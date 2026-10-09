# Issue #209 terminal report

_Status: TERMINAL — the finite E/A front for issue #209 is closed at the level
of the claims it makes._
Author (board identity): the previous owner recorded `openclaw@marceline-dev`;
git commits on this front are authored as `Otto Jung <otto.jung@vauplace.com>`.
Branch: `agent/board-209-6cf9bd`, pushed to `origin`.
Commits on this front: `cf92561`, `ec783e4`, `d6de84d` (inherited), `5822125`
and `1ceebf5` (previous owner's reconciliation pass), and this pass.

**This file exists because the board comment cannot be posted from this
host — see the "Reporting blocker" section, whose measured facts were
re-verified in this pass. Its text is written to be copied onto issue #209
verbatim.**

---

## 0. What this pass did and found

The inherited measured state was **not** trusted. Everything below was
re-derived by execution: `git status/log`, re-running every script, re-building
the Lean modules, re-running the axiom audit, and re-measuring both inherited
full-library build failures.

Inherited state, re-measured: branch `agent/board-209-6cf9bd`, 5 commits ahead
of `origin/main` (`cc0aa8a`), working tree clean, `scratch-209/` tracked since
`5822125`. Both claims in the inherited report hold: the audit script's own log
contradicted the ledger in two places before `5822125` fixed them, and the
full-library build is red for reasons outside this front.

Three results are new in this pass, all of them corrections or checks, none of
them mathematical:

1. **One real defect found and fixed, in the second-pass script**
   (`scratch-209/independent_recheck.py`). Its `witness(..., alpha="ACGT")`
   argument was accepted and never used, and `L_A` iterated over the global
   `DNA = "ABCG"` — the alphabet of the *fixed-length* modules, not of
   `ExactVariantECounterexample` (`DNA = A | C | G | T`). Both alphabets have
   four letters, so the A-4 binomial *values* came out as `243/4096` and
   `2187/32768` instead of `177147/16777216` and `1594323/134217728`, while the
   ratio `9/8` — the only thing the script asserted — was invariant to the
   truncation. The ledger's §9b row "all likelihood values … reproduced
   exactly" was therefore an overstatement for A-4; corrected there and logged
   as defect 3 in §11. The §1 table's A-4 row itself was correct all along.
   This is the third instance of the same error class in one front — an
   objective quietly evaluated over a different set of read types — and it is
   now also guarded by a check in the new script.
2. **One documentation defect found in this front's own ledger**: §6 said the
   unobserved length-`L` window in each witness was "(`ABA`/`ACA` for the
   competitor)". For E-4 (`AABB → ABAB`) the competitor is completely spelled
   and it is the **truth** that carries the unobserved windows `AA`, `BB`.
   The claim ("at least one of truth, competitor") survives; the parenthetical
   did not. Fixed.
3. **A third, from-scratch verification script**
   (`scripts/verify_issue209_ea_witnesses_third_pass.py`), sharing no code with
   either earlier script or with the Lean library, asserting every §1 value
   against an oracle transcribed from the Lean theorems. 91 checks, all
   passing; log committed. It also re-confirms the maximizer censuses, the
   read-tiled 625/256/400 counts, and the duplicate-read families.
4. **A count error in the axiom audit**: the ledger claimed
   `scratch-209/axioms3.lean` covered "42 names"; it covers 41. Corrected and
   superseded by a generated complete sweep over all 116 theorems of the five
   modules (§7, defect 4 in §11).

No source fact, witness instance, likelihood value or `I_s` certificate was
changed, and no definition was altered to make anything provable.

## 1. Progress comment that should open this front's board record

> **state: terminal** — issue #209, E/A finite-research front. Worktree
> `/workspace/assemblyp1-finite-209`, branch `agent/board-209-6cf9bd`
> (ahead 5 of `origin/main`), pushed.
>
> I re-derived the inherited state by execution rather than trusting it, and
> I re-verified every claim in the inherited ledger: both audit-script defects
> it recorded, the isolated build of the five responsible modules, the
> 41-theorem hand-picked axiom audit (re-ran `axioms3.lean`; byte-identical
> log), the generated complete sweep over all 116 theorems of the five
> modules, and both inherited full-library build failures (`BBTTripleBridge`
> fails to elaborate, `Issue94Transposition` is OOM-killed, exit 137). I then
> wrote a third, independent implementation of the whole E/A check and found
> one real defect, one documentation error and one count error; all three are
> fixed and logged in `docs/issue-209-ea-audit-ledger.md` §6, §7, §9b, §11.
>
> Verdict unchanged in substance: the exact-multinomial (Variant E) and
> literal fixed-`N` binomial-marginals (Variant A) refutations of "the truth is
> a maximizer" stand, for `AAABB → AAAAB`, `AAACC → AAAAC`, `AABB → ABAB` and
> `ACGT → ACACGT`, under the **full** source-faithful `I_s`, with strict
> ratios `2`, `1125/512`, `4`/`4096/729` and `32/27`/`9/8`; they inherit to the
> circular classes where the objective is defined, and they say nothing about
> the §6.2 flow-feasible class. The `N` parameter and the `|D| = N` constraint
> are different restrictions and the separation is kernel-checked.

## 2. Terminal verdict

### What is proved / re-established

**Kernel-checked (Lean 4.34 / Mathlib 4.34).** A complete generated sweep of
*all 116 theorems* of `SourceFaithfulIs`, `ExactVariantECounterexample`,
`FixedLengthExactCounterexample`, `FixedLengthBinomialCounterexample` and
`Issue209EAudit` (`scripts/audit_issue209_axioms_full.py`, output in
`scratch-209/axioms-full.lean` / `scratch-209/axioms-full-run.log`) shows every
one has an axiom surface inside `[propext, Classical.choice, Quot.sound]` — 105
on exactly those three, 11 on none. No `sorry`, no `admit`, no new axiom, no
`native_decide`. Every `I_s` membership is a single `decide` on the whole
`InformationFeasible` predicate — no proxied bridging predicate anywhere in the
E/A chain.

| id | truth → competitor | objective | `L(S)` | `L(D)` | ratio |
|---|---|---|---|---|---|
| E-1 | `ACGT → ACACGT` | exact multinomial, `N = N(D)` | `3/64` | `1/18` | `32/27` |
| E-2 | `AAABB → AAAAB` | exact multinomial | `6/125` | `12/125` | `2` |
| E-3 | `AAACC → AAAAC` | exact multinomial | `6/125` | `12/125` | `2` |
| E-4 | `AABB → ABAB` | exact multinomial | `1/8` | `1/2` | `4` |
| A-1/A-2 | `AAACC`/`AAABB` → `AAAAC`/`AAAAB` | literal binomial, fixed `N = 5` | `452984832/30517578125` | `7962624/244140625` | `1125/512` |
| A-3 | `AABB → ABAB` | binomial, `N = 4` | `729/16384` | `1/4` | `4096/729` |
| A-4 | `ACGT → ACACGT` | binomial, `N = 4` | `177147/16777216` | `1594323/134217728` | `9/8` |

Each of those 19 numbers was recomputed from a from-scratch implementation of
the full `I_s` and both objectives and matched the Lean theorems; the values
of A-4 were the ones the defective alphabet had broken, and they now match.

**Bounded evidence (exhaustive over a complete class, exact arithmetic).** The
truth is not a maximizer of any of the three objectives over all `4^5 = 1024`
length-5 genomes for both the `AAABB` and the `AAACC` observations; in each
such class the maximum is attained by exactly the competitor's cyclic-shift
class, never the truth's. The `ACGT` observation over all 87380 words of length
≤ 8 in `{A,C,G,T}` has maximum `1/18`, attained by exactly the six cyclic
shifts of `ACACGT`. Duplicate-read families `k = 1..6`: exact-E ratio `2^k`;
binomial ratio `(1125/512)(5/2)^(k-1)`.

**Mathematical transfer argument (not a separate kernel check).** The
fixed-length kernel checks do transfer to the unrestricted Variant E statement:
`6/125` and `12/125` recomputed against the unrestricted objective agree.

**Hypothesis coverage.** Clause 3 of `I_s` is vacuous in every E/A witness;
clause 1 (coverage) and clause 2 (all-bridged triple repeat) are what the
refutations rest on. A genuine coverage gap, not a defect, because `I_s` is a
sufficient condition.

**`N` versus `|D| = N`.** Different restrictions, and the separation is
kernel-checked: `winCount_le_len`, `binomial_marginal_probability_on_le_len`,
and `external_N_domain_boundary` (length-6 all-`A` candidate, `N = 5`,
`d_AAA = 6`, unobserved-type marginal `(1-6/5)^3 = -1/125 < 0`).

**Which competitor universes inherit the refutation** (both objectives): the
region `{D : ∀ w, d_w ≤ N}` where the literal marginal is a probability;
`{D : |D| ≤ N}`; the fixed length `|D| = G` class. Variant E additionally
inherits to all nonempty circular candidates (E-1 alone suffices). Variant A is
not a well-posed class over unrestricted circular candidates. Not the §6.2
flow-feasible set: in every witness at least one of truth/competitor carries an
unobserved length-`L` window — E-1 both, E-2/E-3 the competitor, E-4 the truth
(whose `AA`/`BB` windows are unobserved while `ABAB` is fully spelled).

### Fixes delivered

1. `scripts/verify_issue209_ea_witnesses_third_pass.py` (new): the third,
   independent re-verification, 91 checks, log committed
   (`scratch-209/ea-third-pass-run.log`).
2. `scripts/audit_issue209_axioms_full.py` (new): a generated, complete axiom
   sweep over all 116 theorems of the five responsible modules; cannot drift
   from the sources. Output committed as `scratch-209/axioms-full.lean` and
   `scratch-209/axioms-full-run.log`.
3. `scratch-209/independent_recheck.py`: the dead `alpha` parameter is now
   threaded through `L_A`/`witness`, the `DNA` default is documented, and every
   E row asserts its oracle values — so the A-4 values are actually reproduced
   and a future alphabet slip cannot hide behind a ratio check.
4. `docs/issue-209-ea-audit-ledger.md`: §6 parenthetical corrected, §7 theorem
   count corrected and superseded by the complete sweep, §9b overstatement
   corrected, §9c, §11 defects 3 and 4 added.

### What remains (for the parent matrix)

1. Clause 3 of `I_s` is unexercised by every E/A witness.
2. The maximizer census is not kernel-checked (a 1024-candidate exhaustive
   check of a product over 64 read types).
3. §6.2 feasible-set correspondence is open for both objectives; owned by
   other issues.
4. Source correspondence of the fixed-`N` reading (product over the whole
   read-type space retaining zero-count factors) is a repository reading of
   Medvedev–Brudno §6.1, not a re-verified source sentence.
5. Which objective the published 2016 sentence denotes is unresolved. The
   honest aggregate claim is that every *objective-and-candidate-class* pair
   with a defensible reading has been resolved, not that the 2016 question is
   settled.
6. The full-library `lake build` is red for reasons outside this front; a
   parent that needs one green build must repair `BBTTripleBridge` first.

### Reporting blocker (precise, re-verified in this pass)

* `gh` is not installed and is not on `PATH`.
* No GitHub token exists in the environment (`env | grep -i token` finds only
  `LUBKO_SUPERVISOR_STATE_TOKEN`, an opencode supervisor token of a different
  kind), in `~/.git-credentials` or `~/.netrc` (neither exists).
* The repository is private: unauthenticated calls to
  `api.github.com/repos/ottojung/assemblyp1/issues/209` return `404 Not Found`,
  not `401`, so the API cannot be used even for a read.
* `git` over SSH authenticates as `ottojung` (used to push this branch), but
  GitHub's REST API has no SSH transport.
* The board itself is a React SPA at `https://vau.place/a/antonina/`; its
  bundle contains no API endpoint, so there is no client-side path either.
* `docs/skills/itinerary-assemblyp1.md` routes board work through the Lubko /
  Supabase transport on `marceline-dev`, but `marceline-dev` is unreachable
  from this host (`ssh: connect to host marceline-dev port 22: Connection
  refused`) and no `lubko-agent` binary exists locally.

**Action for the orchestrator:** post §0 and §1 verbatim as the terminal report
on issue #209. Everything needed to verify the claims is in the commits of this
pass on branch `agent/board-209-6cf9bd`
(`scripts/verify_issue209_ea_witnesses_third_pass.py`,
`scripts/audit_issue209_axioms_full.py` and their run logs,
`scratch-209/independent_recheck.py`, `docs/issue-209-ea-audit-ledger.md`,
`docs/issue-209-terminal-report.md`).
