# Signed commit enforcement

Status: **CI gate active on branch; branch-protection ruleset NOT enabled (admin step required).**

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
other commit. A signed merge does **not** legalize unsigned commits on the
side branches it introduces — every commit in the range is checked
independently.

## Enforcement

* Script: [`scripts/verify_signed_commits.py`](../scripts/verify_signed_commits.py)
* CI: [`.github/workflows/signed-commits.yml`](../.github/workflows/signed-commits.yml)
  runs on every `push` and `pull_request` targeting `main`.
* Range: the gate checks exactly `git rev-list merge-base(base, head)..head` —
  only newly introduced commits, never ancestors of the base.
* Selftest: [`scripts/test_signed_commits.sh`](../scripts/test_signed_commits.sh)
  covers the unsigned-branch rejection, the `U` (unknown-local-trust) case, a
  signed two-parent merge commit, a signed merge with an **unsigned** side
  branch (must fail), and range isolation, all under a throwaway `GNUPGHOME`.

## Branch protection (admin step required)

The CI gate enforces signatures on every push/PR, but a workflow alone is
**advisory** — it can be bypassed by force-push or disabled by an admin.
GitHub's native **Require signed commits** ruleset is also **not enabled**,
and enabling it as the sole gate is **problematic**: agent commits are signed
with GPG subkeys of the maintainer key that GitHub's REST API does not
recognize (`verification.verified=false, reason=no_user`), so native
verification would reject valid agent signatures.

To make enforcement **mandatory**, a repository admin must:

1. Go to **Settings → Branches → Add branch protection rule** for `main`.
2. Enable **Require status checks to pass** and add the `Signed commits` CI
   job — this makes the cryptographic gate non-bypassable.
3. Enable **Do not allow bypassing the above settings** and **Restrict who
   can push** to prevent force-push and direct-push circumvention.
4. Optionally enable **Require signed commits** as defense-in-depth, but be
   aware it may reject agent GPG signatures that GitHub does not recognize.

Until that admin step is completed, enforcement relies on the CI gate alone
and should be considered **advisory, not mandatory**.

## Trusted keys

Assembled OFFLINE from checked-in PUBLIC key files into a throwaway GPG home at gate runtime. Each file must contain exactly one primary public key matching the pinned fingerprint; extra primary keys fail closed:

| Key | Fingerprint | Source |
|-----|-------------|--------|
| GitHub web-flow | `968479A1AFF927E37D1A566BB5690EEEBB952194` | `scripts/trusted-keys/github-web-flow.asc` (originally <https://github.com/web-flow.gpg>) |
| Maintainer (Otto Jung) | `8B9BE8115DCDEEFA3E24D5EDB851B4F4C06C04D6` | `scripts/trusted-keys/maintainer-ottojung.asc` (originally <https://github.com/ottojung.gpg>) |

The key files are public material, downloaded from the official GitHub profile
URLs in October 2026, then exported by FULL primary fingerprint to retain
exactly one explicitly authorized primary per file. GitHub currently offers
multiple primary keys in its public web-flow download; the unapproved primary
must NOT be silently imported. The gate requires no GitHub/keyserver HTTP
requests on each run. To rotate or add a signing key, use a separately
reviewed, signed PR that updates the pinned fingerprint and the public key
file together. Never commit secret key material.

Agent signing keys are subkeys of the maintainer key, so agent-signed commits
verify against the same trusted primary.

## History report (audit of `origin/main`)

Audit performed with the trusted keyring; `E` does not occur because the
signing keys are present and pinned.

| Range | Total | `N` (unsigned) | `U`/`G` (signed, verified) |
|-------|-------|----------------|-----------------------------|
| All of `main` | 737 | 455 | 282 |
| Since 2026-10-09 | 172 | 25 | 147 |

**Affected unsigned range:** from `1cce2a6` *Initialize assemblyp1 research
repository* (2026-09-17) through `abbe728` *paper: list proof-level
reproduction anchors in main theorem inventory* (2026-10-13, merged via PR
#189 as `9ca5c8`). The unsigned history predates PR #159 and includes kernel
#256 (`737cc9d`). The four PR #159 proof commits named in the issue are
`2b3011e`, `bd4ae52`, `d68dc6c`, `84daf85`.

The 25 unsigned commits since 2026-10-09:

```
abbe728  paper: list proof-level reproduction anchors in main theorem inventory   [PR #189]
dd117d3  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
c1f3fdb  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
09da875  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
9d8617c  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
28e34a3  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
08d685f  paper: recognize Graver rigidity and all-count likelihood certificates   [PR #189]
332841c  paper: foreground the distinct structural, sampling, and spelling proofs [PR #189]
4558957  paper: foreground the distinct structural, sampling, and spelling proofs [PR #189]
b4ab037  paper: foreground the distinct structural, sampling, and spelling proofs [PR #189]
1a2c7a5  paper: foreground the distinct structural, sampling, and spelling proofs [PR #189]
5ce17cf  paper: frame ML optimality as motivation for assembly-specific results  [PR #189]
1a11669  paper: frame ML optimality as motivation for assembly-specific results  [PR #189]
ebbf36c  paper: frame ML optimality as motivation for assembly-specific results  [PR #189]
fd64253  Prevent isolated single-dollar display math from silently compiling       [PR #177]
be3d2f5  Correct display math markers to double-dollar KaTeX syntax              [PR #177]
402ee90  Correct display math markers to double-dollar KaTeX syntax              [PR #177]
a72d603  Reject both unsupported delimiters and math hidden in raw HTML           [PR #177]
eb45c7c  Render biologists' equations in Markdown, outside raw HTML blocks       [PR #177]
f082f20  Render programmers' equations in Markdown, outside raw HTML blocks      [PR #177]
2b3011e  #258: realize all four admissible spectra by explicit circular genomes  [PR #159]
bd4ae52  #258: derive exact arbitrary-sample chamber iff from the genuine circulation census [PR #159]
d68dc6c  #258: prove global unique, tie and loss spectra for three fixed read samples       [PR #159]
84daf85  #258: repair Lean coverage adapter dependent indices and sum proof     [PR #159]
737cc9d  256: kernel-check the exact robust same-length ML iff                  [kernel #256]
```

## Historical exception (documented, no rewrite)

The 455 unsigned commits already on `main` are **grandfathered**: the gate
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
