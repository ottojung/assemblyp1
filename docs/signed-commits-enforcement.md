# Signed commit enforcement

Status: **CI gate active and green on `main`; mandatory branch ruleset ACTIVE — `ruleset1` (id `23626350`) is `enforcement=active` on `~DEFAULT_BRANCH` since 2026-10-15T12:01:31Z.**
Audit date: 2026-10-14. Audited revision: `origin/main` @ `b424c987edbde6282bc65ccdb71f65e6abcbe427`.

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

## The merge-commit gap, and why it is closed

Checking only a PR head or only the final merge-commit signature is
insufficient. PR #189 merged to `main` as `9ca5c8fde36466650a2f0ff6a2182bf9cfb2baa0`
with **two parents** `39386230` and `abbe7284`. GitHub reports the merge commit
itself `verified=true, reason=valid`, but the PR branch introduced **14 unsigned
commits** reachable from `main` only through the second parent `abbe7284`.

The gate closes this gap because it verifies `git rev-list merge-base(base, head)..head`,
which enumerates **every commit reachable through any parent** of the incoming
range, merge commits included. Running the gate over the exact range that PR
#189 introduced rejects it:

```
$ python3 scripts/verify_signed_commits.py \
    --base 393862304a656cbdbb1bdb309d1b189629e52a43 \
    --head 9ca5c8fde36466650a2f0ff6a2182bf9cfb2baa0
signed-commit gate: 15 new commit(s) (1 merge commit(s)) in 393862304a65..9ca5c8fde364
  REJECT [commit] abbe728454d8 status=N (no signature) paper: list proof-level reproduction anchors ...
  ... (14 unsigned commits total)
signed-commit gate FAILED: 14 of 15 commit(s) rejected
```

This is captured as an automated regression in `scripts/test_signed_commits.sh`
(test 6) so the property cannot silently regress.

## Exact gate identity

Branch protection and rulesets match a status check by its **check-run name**,
not by the workflow's display name. For this gate they differ:

| Field | Value |
|-------|-------|
| Workflow display name | `Signed commits` |
| Workflow file | `.github/workflows/signed-commits.yml` |
| Workflow id | `383736431` |
| **Required status check context** | **`signed-commits`** |

A required status check must therefore be configured with the job id
`Signed commits` / `signed-commits`; the value that actually matches is the job
id **`signed-commits`**.

## Enforcement

* Script: [`scripts/verify_signed_commits.py`](../scripts/verify_signed_commits.py)
* CI: [`.github/workflows/signed-commits.yml`](../.github/workflows/signed-commits.yml)
  runs on every `push` and `pull_request` targeting `main`. It is currently
  active and green on `main` (observed on `b424c987ed`, `b0a6e9ff11`, and
  current `main` `c581d1196` as of 2026-10-16).
* Range: the gate checks exactly `git rev-list merge-base(base, head)..head` —
  only newly introduced commits, never ancestors of the base.
* Selftest: [`scripts/test_signed_commits.sh`](../scripts/test_signed_commits.sh)
  covers the unsigned-branch rejection, the `U` (unknown-local-trust) case, a
  signed two-parent merge commit, a signed merge with an **unsigned** side
  branch (must fail), range isolation, pinned-key/extra-primary rejection, the
  known-good signed PR #160/#161 ranges, and the real PR #189 merge topology
  (must fail), all under a throwaway `GNUPGHOME`. Current result: **9 passed,
  0 failed**.
* Operator check: [`scripts/check_ruleset_enforcement.py`](../scripts/check_ruleset_enforcement.py)
  reads the public GitHub rulesets API and reports whether the gate is
  actually mandatory (exit 0 = enforced, 1 = advisory, 2 = undetermined). It is
  deliberately not part of CI. Current result: **exit 0, `ENFORCED`** (live
  check 2026-10-16).

## Branch protection (active)

The CI gate verifies signatures on every push/PR, and the repository ruleset
**`ruleset1` (id `23626350`) is `enforcement=active`** on `~DEFAULT_BRANCH`
(activated 2026-10-15T12:01:31Z; ruleset history version `53324683` reports
`2026-10-15T05:01:31.882-07:00`, i.e. `12:01:31Z`), so enforcement is **mandatory**, not
advisory. Observed live (2026-10-16) ruleset rules:

* `required_status_checks` — exact context **`signed-commits`**, with
  `strict_required_status_checks_policy=true`: the gate is required for merge.
* `non_fast_forward` and `deletion` — force-pushes and branch deletion are
  blocked, so the gate cannot be sidestepped by rewriting history.
* `pull_request` — changes arrive via PR.
* `bypass_actors=[]` and `current_user_can_bypass=never` — no bypass path.

The ruleset contains **no native `signed_commits` rule** — deliberately, see
the next section. This is observable without an admin token:

```sh
curl -sS https://api.github.com/repos/ottojung/assemblyp1/rulesets/23626350
python3 scripts/check_ruleset_enforcement.py            # exit 0, prints ENFORCED
python3 scripts/check_ruleset_enforcement.py --selftest # offline fixture checks
```

No repository-admin step remains: a push or PR range containing any commit
that fails the gate cannot merge.

### GitHub-native "Require signed commits" is not a safe substitute

GitHub's own signature verification disagrees with a correct local
cryptographic check on these agent commits, so the native rule must not be
turned on as the primary gate. Live evidence (REST `verification` 2026-10-14;
re-measured 2026-10-16 via API signature states, which return the same
values):

| Commit | Local gate (`%G?`) | GitHub `verification` |
|--------|--------------------|------------------------|
| `7aba5d0` (agent slide commit, PR #254) | `U`, `verify-commit` exit 0 | `verified=false`, reason `bad_email` |
| `5e1659f` (agent CI commit, PR #194) | `U`, `verify-commit` exit 0 | `verified=false`, reason `bad_email` |
| `21fa90b` (agent docs commit, PR #191) | `U`, `verify-commit` exit 0 | `verified=false`, reason `bad_email` |
| `332915c` (agent audit commit, PR #191) | `U`, `verify-commit` exit 0 | `verified=false`, reason `bad_email` |
| `157ad34` (agent merge, #267) | `U`, `verify-commit` exit 0 | `verified=false`, reason `no_user` |
| `9ca5c8f` (PR #189 merge, web-flow) | `U` | `verified=true`, reason `valid` |
| `abbe728` (second parent of #189) | `N`, `verify-commit` fails | `verified=false`, reason `unsigned` |
| `080b1b3` (PR #159 merge, web-flow) | `U` | `verified=true`, reason `valid` |

`bad_email` means the committer email is not among the signing key's identities
— it is **not** an invalid signature — and `no_user` means GitHub has no user
bound to the key. Measured distinction (2026-10-16): agent commits whose
committer email is the maintainer's GitHub noreply address (`7aba5d0`,
`5e1659f`, `21fa90b`, `332915c` — the signing key is bound to a GitHub user
but the committer email is not in the key's identities) return `bad_email`;
agent commits whose committer email is agent-local (`157ad34`, committed as
`agent-7723b8c4b1c0@opencode.local` — no GitHub user bound to the key)
return `no_user`. Both are properties of GitHub's verifier, not of the
signature. Enabling native **Require signed commits** would therefore reject
cryptographically valid agent commits. The `080b1b3`/`9ca5c8f` rows also show
that a GitHub-verified merge head does **not** imply signed ancestry.

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

## History report (audit of `origin/main` @ `b424c98`, 2026-10-14)

Audit performed with the trusted keyring assembled from the pinned public keys;
`E` does not occur because the signing keys are present.

| Range | Total | `N` (unsigned) | `U`/`G` (signed, verified) |
|-------|-------|----------------|-----------------------------|
| All of `main` | 772 | 455 | 317 |
| Since 2026-10-10 (committer date) | 165 | 24 | 141 |
| `abbe728..origin/main` | 42 | **0** | 42 |

**Affected unsigned range:** from `1cce2a6` *Initialize assemblyp1 research
repository* (2026-09-17) through `abbe728` *paper: list proof-level
reproduction anchors in main theorem inventory* (2026-10-13, merged via PR
#189 as `9ca5c8f`). The newest unsigned commit on `main` is `abbe728`; every
commit after it (42 commits, including the signed merges of PR #191 `d4406bc`,
PR #194, and later PRs) is signed and passes the gate. The unsigned history
predates PR #159 and includes kernel #256 (`737cc9d`). The four PR #159 proof
commits named in the issue are `2b3011e`, `bd4ae52`, `d68dc6c`, `84daf85`.

The 24 unsigned commits since 2026-10-10 (PR #189 ×14, PR #177 ×6, PR #159 ×4):

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
```

## Historical exception (documented, no rewrite)

The 455 unsigned commits already on `main` are **grandfathered**: the gate
applies only to commits newly introduced by a push or PR range, so existing
history is not re-checked and `main` is never rewritten. Force-pushing or
rewriting public `main` to retroactively sign history would invalidate every
existing clone, PR, and citation; per project policy that requires separate
explicit authorization and an impact analysis and was **not** performed. The
discrepancy is instead recorded here and in the issue tracker. No
force-push or history rewrite of `main` was performed by this change.

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
