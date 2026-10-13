#!/usr/bin/env python3
"""Enforce signed commits on an incoming change range.

For every commit in ``git rev-list BASE..HEAD`` (exactly the newly introduced
commits, never ancestors of BASE), require a cryptographically valid GPG/PGP
signature produced by a trusted signing key:

* ``N`` (no signature)      -> reject
* ``B`` (bad signature)     -> reject
* ``E`` (unverifiable here) -> reject
* ``R``/``X``/``Y``/``D``   -> reject
* ``G`` / ``U``             -> accept only after ``git verify-commit`` exits 0
  against an isolated trusted keyring.  ``U`` (good signature, unknown local
  trust) is accepted on exactly the same cryptographic evidence as ``G``.

Merge commits are ordinary members of the range: a signed merge commit is
verified like any other commit, so ``git merge --no-ff -S`` results are
enforced too.

The trusted keyring is assembled in a throwaway ``GNUPGHOME`` from the
official GitHub web-flow key and the repository maintainer key, and each
downloaded key is pinned by expected fingerprint.
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import urllib.request

TRUSTED_KEYS = (
    (
        "https://github.com/web-flow.gpg",
        "968479A1AFF927E37D1A566BB5690EEEBB952194",
        "GitHub web-flow (commits merged through the GitHub web UI)",
    ),
    (
        "https://github.com/ottojung.gpg",
        "8B9BE8115DCDEEFA3E24D5EDB851B4F4C06C04D6",
        "repository maintainer (signs agent commits via its ed25519 subkey)",
    ),
)

REJECT_STATUSES = {
    "N": "no signature",
    "B": "BAD signature",
    "E": "signature not checkable",
    "R": "revoked signing key",
    "X": "expired signing key",
    "Y": "key with expired validity",
    "D": "signing key expired",
}


class AuditError(Exception):
    pass


def run(cmd: list[str], env: dict | None = None, input_text: str | None = None,
        check: bool = True) -> subprocess.CompletedProcess:
    proc = subprocess.run(cmd, env=env, text=True, input=input_text,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and proc.returncode != 0:
        raise AuditError(
            f"command failed ({proc.returncode}): {' '.join(cmd)}\n"
            f"stdout: {proc.stdout.strip()}\nstderr: {proc.stderr.strip()}")
    return proc


def git(repo: str, *args: str, check: bool = True,
        env: dict | None = None) -> subprocess.CompletedProcess:
    return run(["git", "-C", repo, *args], env=env, check=check)


def import_key(keydir: str, key_path: str, env: dict) -> str:
    """Import one key file; return its primary fingerprint."""
    listing = run(["gpg", "--batch", "--show-keys", "--with-colons",
                   key_path], env=env).stdout
    fps = [line.split(":")[9] for line in listing.splitlines()
           if line.startswith("fpr:")]
    if not fps:
        raise AuditError(f"no fingerprint found in {key_path}")
    run(["gpg", "--batch", "--import", key_path], env=env)
    return fps[0]


def fetch_keyring(keydir: str, extra_keys: list[str] | None = None) -> dict[str, str]:
    """Assemble the trusted keyring in an isolated GNUPGHOME.

    Production keys are downloaded from their official URLs and pinned by
    expected fingerprint.  ``extra_keys`` (selftest hook) are imported as-is.
    """
    env = dict(os.environ, GNUPGHOME=keydir)
    fingerprints: dict[str, str] = {}
    for url, expected_fp, label in TRUSTED_KEYS:
        with urllib.request.urlopen(url, timeout=30) as resp:
            key_data = resp.read()
        if not key_data.startswith(b"-----BEGIN PGP PUBLIC KEY BLOCK-----"):
            raise AuditError(f"unexpected key material from {url}")
        with tempfile.NamedTemporaryFile(suffix=".gpg", delete=False) as fh:
            fh.write(key_data)
            key_path = fh.name
        try:
            import_key(keydir, key_path, env)
        finally:
            os.unlink(key_path)
        listing = run(["gpg", "--batch", "--with-colons", "--list-keys",
                       "--fingerprint"], env=env).stdout
        actual_fps = [line.split(":")[9] for line in listing.splitlines()
                      if line.startswith("fpr:")]
        match = [fp for fp in actual_fps if fp.replace(" ", "").endswith(expected_fp)]
        if not match:
            raise AuditError(
                f"key from {url} does not match expected fingerprint "
                f"{expected_fp}; got {actual_fps}")
        fingerprints[label] = match[0]
    for key_path in extra_keys or []:
        fp = import_key(keydir, key_path, env)
        fingerprints[f"extra key {os.path.basename(key_path)}"] = fp
    return fingerprints


def commit_status(repo: str, commit: str,
                  env: dict | None = None) -> tuple[str, str, str, int]:
    """Return (status, author, subject, parent_count) for one commit.

    The status is computed with the caller's keyring, so a signature that is
    only verifiable against the trusted keyring is not misreported as E.
    """
    proc = git(repo, "log", "-1", "--format=%G?%x1f%an%x1f%s%x1f%P", commit,
               check=False, env=env)
    if proc.returncode != 0:
        raise AuditError(f"cannot read commit {commit}: {proc.stderr.strip()}")
    parts = proc.stdout.rstrip("\n").split("\x1f")
    status = parts[0] if parts and parts[0] else "N"
    author = parts[1] if len(parts) > 1 else "?"
    subject = parts[2] if len(parts) > 2 else "?"
    parents = parts[3].split() if len(parts) > 3 and parts[3] else []
    return status, author, subject, len(parents)


def verify_range(repo: str, base: str, head: str, keydir: str) -> int:
    env = dict(os.environ, GNUPGHOME=keydir)
    merge_base = git(repo, "merge-base", base, head).stdout.strip()
    if not merge_base:
        raise AuditError(f"no merge-base between {base} and {head}")

    range_commits = git(repo, "rev-list", f"{merge_base}..{head}").stdout.split()
    if not range_commits:
        print("no new commits in range; nothing to enforce")
        return 0

    merges = git(repo, "rev-list", "--min-parents=2",
                 f"{merge_base}..{head}").stdout.split()

    print(f"signed-commit gate: {len(range_commits)} new commit(s) "
          f"({len(merges)} merge commit(s)) in {merge_base[:12]}..{head[:12]}")

    failures = []
    for commit in range_commits:
        status, author, subject, nparents = commit_status(repo, commit, env=env)
        short = commit[:12]
        tag = "merge" if nparents >= 2 else "commit"
        if status in REJECT_STATUSES:
            reason = REJECT_STATUSES[status]
        elif status not in ("G", "U"):
            reason = f"unexpected status {status}"
        else:
            proc = git(repo, "verify-commit", commit, env=env, check=False)
            if proc.returncode != 0:
                reason = ("git verify-commit failed: " +
                          (proc.stderr.strip() or "unknown error"))
            else:
                print(f"  accept [{tag}] {short} status={status} "
                      f"{subject[:60]}")
                continue
        failures.append((short, tag, status, reason))
        print(f"  REJECT [{tag}] {short} status={status} ({reason}) "
              f"{subject[:60]}")

    if failures:
        print(f"\nsigned-commit gate FAILED: {len(failures)} of "
              f"{len(range_commits)} commit(s) rejected")
        for short, tag, status, reason in failures:
            print(f"  - {short} [{tag}] ({status}) {reason}")
        return 1
    print(f"\nsigned-commit gate PASSED: all {len(range_commits)} commit(s) "
          f"cryptographically verified")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", default=".", help="path to the git repository")
    ap.add_argument("--base", required=True,
                    help="base ref; only merge-base(base, head)..head is checked")
    ap.add_argument("--head", required=True, help="head ref to verify")
    ap.add_argument("--extra-key", action="append", default=[], metavar="FILE",
                    help="additional trusted public key file (selftest hook)")
    args = ap.parse_args()

    keydir = tempfile.mkdtemp(prefix="signed-commits-keyring.")
    try:
        fingerprints = fetch_keyring(keydir, extra_keys=args.extra_key)
        for label, fp in fingerprints.items():
            print(f"trusted key: {label} {fp}")
        return verify_range(args.repo, args.base, args.head, keydir)
    finally:
        shutil.rmtree(keydir, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
