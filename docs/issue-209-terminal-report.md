# Issue #209 terminal report

_Status: TERMINAL — bounded-turn reconciliation pass complete._
Author (board identity): `openclaw@marceline-dev`.
Branch: `agent/board-209-6cf9bd`, pushed to `origin`.
Commits on this front: `d6de84d`, `ec783e4`, `cf92561` (inherited from the
previous owner) and `5822125` (this pass).

**This file exists because the board comment could not be posted from this
host — see the "Reporting blocker" section. Its text is written to be copied
onto issue #209 verbatim.**

---

## 1. Progress comment that should open this front's board record

> **state: working** — issue #209, owner `openclaw@marceline-dev`, worktree
> `/workspace/assemblyp1-finite-209`, branch `agent/board-209-6cf9bd` (ahead 4
> of `origin/main`).
>
> I did **not** trust the inherited measured state; I re-derived it by
> execution. Measured starting scope, which is the scope I actually ran:
>
> * Branch `agent/board-209-6cf9bd` at `d6de84d` ("Add an independent
>   re-verification script for the E/A witnesses"), 3 commits ahead of
>   `origin/main`, with untracked `scratch-209/` containing a build log, two
>   axiom-audit files and one run log. No uncommitted edits to tracked files.
> * Re-ran `scripts/verify_issue209_ea_witnesses.py`: its own log already
>   contradicted `docs/issue-209-ea-audit-ledger.md` §10.4 in section F (0
>   ratio-27 observations) and reported an `N = 4` census row evaluated at
>   `N = 5` in section G. Both are real defects in the committed script.
> * Full `lake build` is red: `AssemblyP1/BBTTripleBridge.lean` fails to
>   elaborate (17 errors, first at line 81) and
>   `AssemblyP1/Issue94Transposition.lean` is OOM-killed (`exit 137`). Neither
>   file is in this front's diff, so both are inherited from `origin/main`.
> * The five E/A modules build in isolation and their axiom surfaces are clean,
>   so the red is not an E/A blocker.
>
> Scope I am executing, no expansion: independently recheck the exact
> multinomial (Variant E) and fixed-`N` binomial (Variant A) negative results
> under the full source-faithful `I_s` (not a proxy briding predicate), over
> unrestricted and fixed-length `AAABB/AAAAB` and `AAACC/AAAAC` witnesses,
> binomial zero-count factors, the `d_i/N` domain, duplicate reads and strict
> ratios; check Lean theorems, axiom surfaces and source correspondence;
> confirm which competitor universes inherit the refutation; distinguish the
> external `N` parameter from the `|D| = N` constraint. Deliver a proof/witness
> ledger plus the fixes above. I am not re-running Section 6.2 research.

---

## 2. Terminal verdict

### What I proved / re-established

**Kernel-checked (Lean 4.34 / Mathlib 4.34; all 42 headline theorems of the
five responsible modules depend only on `[propext, Classical.choice,
Quot.sound]`).** No `sorry`, no `admit`, no new axiom, no `native_decide`.

| id | truth → competitor | objective | `L(S)` | `L(D)` | ratio |
|---|---|---|---|---|---|
| E-1 | `ACGT → ACACGT` | exact multinomial, `N = N(D)` | `3/64` | `1/18` | `32/27` |
| E-2 | `AAABB → AAAAB` | exact multinomial | `6/125` | `12/125` | `2` |
| E-3 | `AAACC → AAAAC` | exact multinomial | `6/125` | `12/125` | `2` |
| A-1/A-2 | `AAACC`/`AAABB` → `AAAAC`/`AAAAB` | literal binomial, fixed `N = 5` | `452984832/30517578125` | `7962624/244140625` | `1125/512` |

Every value above was recomputed by me in exact rational arithmetic against a
from-scratch implementation of the full `I_s` predicate, and agrees with the
Lean theorems. A-2 (`AAABB → AAAAB` under the binomial objective) was the new
kernel-checked theorem added by the previous owner; I verified it
independently, including that the objective really is invariant under the
`B ↔ C` relabelling, so A-1 and A-2 share one ratio.

**Bounded evidence (exhaustive over a complete class, exact arithmetic).**

* The truth is not a maximizer of any of the three objectives over all
  `4^5 = 1024` length-5 genomes for both the `AAABB` and `AAACC` observations.
* In each such class the maximum is attained by exactly the competitor's
  cyclic-shift class, never the truth's — stronger than "not a maximizer".
* `ACGT` observation over all 87380 circular candidates of length ≤ 8 in
  `{A,C,G,T}`: the maximum is `1/18`, attained by exactly the six cyclic shifts
  of `ACACGT`.
* Duplicate-read families, `k = 1..6`: exact-E ratio `2^k`; binomial ratio
  `(1125/512)(5/2)^(k-1)`. All strict for every `k ≥ 1`.

**Mathematical transfer argument (not a separate kernel check).** The
fixed-length kernel checks do transfer to the unrestricted Variant E statement:
I recomputed `6/125` and `12/125` against the *unrestricted* objective
(candidate-intrinsic `N(D)`) and they agree, so the subclass-to-superclass
argument of `same-length-witnesses-candidate-set-inclusion.md` §3 is verified
numerically.

**Hypothesis coverage.** Clause 3 of `I_s` (bridged interleaved repeat pairs)
is vacuous in every E/A witness — clause 1 (coverage) and clause 2 (all-bridged
triple repeats) are what the refutations rest on. This is a genuine coverage
gap, not a defect, because `I_s` is a sufficient condition.

**`N` versus `|D| = N`.** These are different restrictions and the separation
is now kernel-checked: `winCount_le_len` gives `d_w ≤ N(D)` for any candidate;
`binomial_marginal_probability_on_le_len` gives `d_w/N ≤ 1` whenever
`|D| ≤ N`; `external_N_domain_boundary` exhibits the length-6 all-`A`
candidate with `N = 5` and `d_AAA = 6`, whose unobserved-type marginal is
`(1-6/5)^3 = -1/125 < 0`. So an external fixed `N` is not a mere parameter
change: on `|D| ≤ N` the objective is automatically a product of
probabilities; on the unrestricted circular class it is not; the intermediate
region `{D : ∀ w, d_w ≤ N}` is nonempty (e.g. `ACACGT` with `N = 4`), where it
happens to be well-defined. The `AAABB`/`AAACC` witnesses are same-length and
land inside all three regions, so they are robust to this choice.

**Which competitor universes inherit the refutation** (both objectives):
all nonempty circular candidates (Variant E only; Variant A is not well posed
there); `{D : ∀ w, d_w ≤ N}`; `{D : |D| ≤ N}`; the fixed length `|D| = G`
class. Not the Section 6.2 flow-feasible set.

### Fixes delivered (commit `5822125`)

Two defects in `scripts/verify_issue209_ea_witnesses.py`, both fixed:

1. Section F inherited a read length of `2` from section E2(b), so it counted
   length-`3` read types among a candidate's length-`2` windows; all
   multiplicities became `0`, all likelihoods `0`, and the section printed
   "observations with ratio 27: 0" — contradicting the ledger's own §10.4
   reconstruction. With `set_read_length(3)` restored it prints 625 ratio-27
   observations, 256 of them fully `I_s`-feasible, including exactly the family
   the ledger describes.
2. Section G's row labelled `binomial A (N=4), AB/BA obs` was evaluated at
   `N = 5` by a hard-coded objective lambda, so it reported `16384/390625` and
   `144/625` under an `N = 4` label. It now takes `N` explicitly; at `N = 4`
   the truth is `729/16384` and the maximum `1/4` at `ABAB`/`BABA`, matching
   the ledger's A-3 entry. The qualitative conclusion was unaffected.

A third defect is recorded as a warning rather than a repo fix: my own
independent script initially scored the binomial objective over the
candidate's own symbol set instead of the model's read-type space, which
silently drops observed types absent from the candidate and inflates relabelled
candidates (`AAAAC` scored the `AAABB` observation at `14155776/244140625`
instead of `0`). Corrected to `Fin 3 → Base`; the same class of error as defect
2 above.

Documentation updated: `docs/issue-209-ea-audit-ledger.md` gains §9b (second
pass results), §10.4 resolved, §10.7 (unrelated pre-existing build breakage)
and §11 (the defect log); `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`
now records the parameters of the previously unparameterized read-tiled row.
No source fact, witness instance, likelihood value or `I_s` certificate was
changed, and no definition was altered to make anything provable.

### What remains

1. **Clause 3 of `I_s` is unexercised** by every E/A witness. A witness in
   which a maximal interleaved repeat pair is genuinely bridged would close it.
2. **The maximizer census is not kernel-checked.** Formalising
   `∀ c : Fin 5 → Base, likelihood c ≤ likelihood AAAAB` is a 1024-candidate
   exhaustive check of a product over 64 read types; not attempted.
3. **§6.2 feasible-set correspondence** is open for both objectives; owned by
   other issues. In every E/A witness at least one of truth/competitor carries
   an unobserved length-`L` window, so no E/A witness places both objects in
   the §6.2 set.
4. **Source correspondence of the fixed-`N` reading** (that the approximation
   is a product over the whole read-type space retaining zero-count factors)
   is a repository reading of Medvedev–Brudno §6.1, not a re-verified source
   sentence. Needs a fresh primary-source read to upgrade.
5. **Which objective the published 2016 sentence denotes** is unresolved. The
   honest aggregate claim is that every *objective-and-candidate-class* pair
   with a defensible reading has been resolved, not that the 2016 question is
   settled.
6. **The read-tiled row is parameterized and feasible but still not
   kernel-checked** in Lean, and still says nothing about §6.2.

### Reporting blocker (precise)

I could not post the board comments on issue #209. Measured facts:

* `gh` is not installed and is not on `PATH`.
* No GitHub token exists in the environment (`env | grep -i token` finds only
  `LUBKO_SUPERVISOR_STATE_TOKEN`, an opencode supervisor token of a different
  kind), in `~/.git-credentials`, in `~/.netrc`, or via
  `git credential fill` (which prompts and fails).
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

**Action for the orchestrator:** post the two texts in §1 verbatim as the
`openclaw@marceline-dev` comments on issue #209. Everything needed to verify
the claims is in commit `5822125` on branch `agent/board-209-6cf9bd`
(`scratch-209/independent_recheck.py`, `scratch-209/axioms3.lean`,
`scratch-209/independent-recheck.log`, `scratch-209/axioms3-run.log`,
`scratch-209/ea-audit-run.log`, `scratch-209/build.log`).
