# Signed commit enforcement

Status: **deployed** (CI gate active on every push/PR to `main`).

## Policy

Every commit newly introduced to `main` — including merge commits — must carry
a cryptographically valid signature from a trusted signing key. The gate
verifies **each commit in the incoming range**, not merely the merge head:

* `N` (no signature) → **rejected**
* `B` (bad signature), `E` (not checkable), `R`/`X`/`Y`/`D` (revoked/expired) → **rejected**
* `G` (good signature, trusted) / `U` (good signature, unknown local trust) →
  **accepted only after `git verify-commit` exits 0** against the isolated
  trusted keyring. `U` and `G` are accepted on identical cryptographic
  evidence; the trust distinction is a local keyring property, not a signature
  property.

A signed merge commit (e.g. `git merge --no-ff -S`) is verified like any
other commit, so the side-branch commits it introduces are all covered.

## Enforcement

* Script: [`scripts/verify_signed_commits.py`](../scripts/verify_signed_commits.py)
* CI: [`.github/workflows/signed-commits.yml`](../.github/workflows/signed-commits.yml)
  runs on every `push` and `pull_request` targeting `main`.
* Range: the gate checks exactly `git rev-list merge-base(base, head)..head` —
  only newly introduced commits, never ancestors of the base.
* Selftest: [`scripts/test_signed_commits.sh`](../scripts/test_signed_commits.sh)
  covers the unsigned-branch rejection, the `U` (unknown-local-trust) case, a
  signed two-parent merge commit, and range isolation, all under a throwaway
  `GNUPGHOME`.

## Trusted keys

Assembled in a throwaway `GNUPGHOME` at gate runtime and pinned by fingerprint:

| Key | Fingerprint | Source |
|-----|-------------|--------|
| GitHub web-flow | `968479A1AFF927E37D1A566BB5690EEEBB952194` | <https://github.com/web-flow.gpg> |
| Maintainer (Otto Jung) | `8B9BE8115DCDEEFA3E24D5EDB851B4F4C06C04D6` | <https://github.com/ottojung.gpg> |

Agent signing keys are subkeys of the maintainer key, so agent-signed commits
verify against the same trusted primary.

## History report (audit of `origin/main`)

Audit performed with the trusted keyring; `E` does not occur because the
signing keys are present and pinned.

| Range | Total | `N` (unsigned) | `U`/`G` (signed, verified) |
|-------|-------|----------------|-----------------------------|
| All of `main` | 679 | 435 | 244 |
| Since 2026-10-09 | 160 | 8 | 152 |

**Affected unsigned range:** from `1cce2a6` *Initialize assemblyp1 research
repository* (2026-09-17) through `2b3011e` *#258: realize all four admissible
spectra by explicit circular genomes* (2026-10-11, merged via PR #159 as
`080b1b3`). The unsigned history predates PR #159 and includes kernel #256
(`737cc9d`). The four PR #159 proof commits named in the issue are
`2b3011e`, `bd4ae52`, `d68dc6c`, `84daf85`.

The 8 unsigned commits since 2026-10-09:

```
2b3011e  #258: realize all four admissible spectra by explicit circular genomes
bd4ae52  #258: derive exact arbitrary-sample chamber iff from the genuine circulation census
d68dc6c  #258: prove global unique, tie and loss spectra for three fixed read samples
84daf85  #258: repair Lean coverage adapter dependent indices and sum proof
737cc9d  256: kernel-check the exact robust same-length ML iff
c8d228a  247e: refute AAABBABB->AAAABABB variable-overlap §6.2 walk (additive)
11ac95c  Merge remote-tracking branch 'origin/main' into agent/board-211-8d5103
76bafba  Integrate ACGT witness and clarify scope of Section 6.2 uniqueness
```

## Historical exception (documented, no rewrite)

The 435 unsigned commits already on `main` are **grandfathered**: the gate
applies only to commits newly introduced by a push or PR range, so existing
history is not re-checked and `main` is never rewritten. Force-pushing or
rewriting public `main` to retroactively sign history would invalidate every
existing clone, PR, and citation; per project policy that requires separate
explicit authorization and an impact analysis and was **not** performed. The
discrepancy is instead recorded here and in the issue tracker.

New work that descends from an unsigned ancestor is unaffected: the gate
checks only `merge-base(base, head)..head`, so a PR whose new commits are all
signed passes even though its base history contains unsigned commits.

## Satisfying the gate

Sign every commit, including merges:

```sh
git config commit.gpgsign true        # sign commits
git merge --no-ff -S ...               # sign merge commits
```

Rebase and re-sign any unsigned commit before pushing. The gate rejects the
push until every commit in the range verifies.
