# Issue #217: preserved follow-up material from the five protected worktrees

_Status: read-only collection record, 2026-10-09, front #217._

The five worktrees registered under issue #217

| worktree | branch | purpose (as recorded locally) |
|---|---|---|
| `/workspace/assemblyp1-94-axiomaudit` | `agent/94-primitive-p2pop-connect` | executable axiom audit and mutation scratch under `audit94/` |
| `/workspace/assemblyp1-94-altroute` | `front94-altroute` | alternative route for the step-2 bridge |
| `/workspace/assemblyp1-94-replacement` | `agent/issue94-p2triple-maxext` | §94 descent / case-1 landing / transposition route; large untracked scratch |
| `/workspace/assemblyp1-94-endpointcheck` | `agent/issue89-ladder-vertexcycle` | §94 endpoint statement inside the lake target |
| `/workspace/assemblyp1-94-census-recheck` | *not a git repository* | independent from-definition re-derivation of the case-1 census |

were consulted read-only. `git status --porcelain` (and `--untracked-files=all`)
was inspected in each before anything was read, so that no material was
disturbed. **Nothing was cherry-picked, merged, moved, or deleted; no worktree
was written to.** All untracked material remains in place.

## 1. What each worktree holds, and whether `main` already has it

| worktree | relevant notes on `main` | extra material not on `main` | verdict |
|---|---|---|---|
| `94-axiomaudit` | same set as `main` | `docs/front-94-p2population-endpoint.md` (a §94 doc); untracked `AssemblyP1/ScratchNameCheck.lean`, `scratch94/Audit94a401.lean`, `scratch94/Mutations94a401.lean`, `audit94/*.{log,exit}` build logs | nothing to collect for #217 || `94-altroute` | same set as `main` | one modified tracked file `AssemblyP1/Issue94AltRoute.lean` (uncommitted) | nothing to collect; the modification is left for its owner |
| `94-replacement` | same set as `main` | 13 §94-specific notes (`admissible-obstruction-94.md`, `backward-extension-common-back-step-94.md`, `bad-selected-interleaving-witness-94.md`, `bbt-replacement-invariant-host-constraint.md`, `bbt-support-invariant-89.md`, `board94-endgame-statement-94.md`, `case1-landing-94.md`, `half-period-no-bad-theta-94.md`, `interleaved-admissible-94a09.md`, `rematching-invariant-94.md`, `selected-interleaving-crux-94.md`, `two-transposition-criterion-94.md`) and ~40 untracked `scratch/*.lean` + `scratch/*.py` files | nothing for #217; all preserved |
| `94-endpointcheck` | same set as `main` | untracked `scratch/` (8 Lean probes + 2 search scripts + `BOARD94-ENDPOINT-REPAIR-1717.md`) | nothing to collect; preserved |
| `94-census-recheck` | — (not a git repo) | `recheck.py` (independent case-1 census re-derivation, `GMAX_CAP = 13`, `CONFIGS_CAP = 4·10⁶`), `verify_cex.py` (exhaustive from-definition check of the `G=5, L=3, S=00101` configuration), `witnesses.py`, `xval.py`, `landing.py`, `landing2.py`, `pred/`, `pred_regime.out` | nothing for #217; see §3 |

`docs/exact-same-length-spectrum-fibre-count.md` is present in `94-replacement`
and `94-endpointcheck` in an **older** form than the one on `main`: the `main`
copy carries two additional blocks that the worktree copies lack — the
board-attribution block (the decomposition is a board construction, not imported
from Pevzner 1995 or BBT) and the correction block striking the wrong BBT
citation (“Algorithmica 13:1–19, 2006”) and recording that BBT’s arXiv appendix
contains a complete proof of its Theorem 3 while the imported
`Lemma [Pevzner] l:Pev95` “is stated but proved nowhere in the chain”. So on
that file `main` is strictly ahead and there is no rollback to perform.

## 2. Consequence for the interpretation matrix

None of the five worktrees contains material that changes a matrix row. All
five concern the transposition/BBT/Eulerian chain of issues #94 and #89, not the
finite maximum-likelihood interpretation question of #217. The one indirect
connection is that `94-census-recheck/recheck.py` and `verify_cex.py` are
**independent re-derivations from the Lean definitions** — including
`AssemblyP1/SourceFaithfulIs.lean` — which is the module that formalizes
Shomorony's bridging predicate `I_s`. Their agreement with the library is
therefore corroboration of the *bridging-rule* column of the matrix, but it is
corroboration by re-implementation, not a new theorem.

## 3. One recorded finding worth carrying forward (not actioned here)

`94-census-recheck/verify_cex.py`, run read-only from its own directory,
reports for `S = 00101`, `L = 3`:

* `backAgreeSet(c,d) = [0,1,2]`, `max' = 2`, landing pair
  `prevPos^2 (c,d) = (0,2)`, and **`LANDING HOLDS: False`**;
* the predecessor's convention gives `p = 1` and `p_prev == u == w: True`;
* `LONGOBSTRUCTION: False` for the same configuration (both clauses fail).

`pred_regime.out` records the regime tally over case-1 configurations up to
`G = 13`: 49 764 configurations, 132 periodic, and the buckets
`FREE B: 13202`, `obst A: 6972`, `obst B: 26354`,
`obst C:OPEN-between: 1738`, `obst D: 676`, `obst E:OPEN-above: 690`,
with “FREE genomes with p != u or p != w: 0”.

This is a §94/#89 fibre-pair-convention question (which `p` the case-1 landing
rule uses) and is **outside** the scope of front #217. It is recorded here so
that the owning front can find it without re-running the census; it is not
merged, not cherry-picked, and not used as evidence for any matrix row.

## 4. Epistemic status

| claim | status |
|---|---|
| The five worktrees were consulted read-only; nothing was modified, moved, or deleted | repository fact |
| None of them contains material that changes an interpretation-matrix row | verified by directory and file comparison against `main` |
| `main`'s `exact-same-length-spectrum-fibre-count.md` is newer than the copies in `94-replacement` and `94-endpointcheck` | verified by `diff` |
| The census-recheck scripts re-derive the bridging predicate from `AssemblyP1/SourceFaithfulIs.lean` | repository fact (their docstrings) |
| The landing/LongObstruction findings in §3 | **verified by running the scripts read-only in their own directory**; owned by #94/#89, not by #217 |

## 5. The leaf-#212 harvest, which *did* change a matrix row

Section 2 above records that the five protected #94 worktrees hold nothing that
changes a matrix row. Section 5 records the opposite outcome for the **one
live leaf** consulted in the second half of this round.

Leaf `#212` (agent `cedd79adfeae`, registered worktree
`/workspace/assemblyp1-finite-212`, branch `agent/board-212-37b45b`, based on
`cc0aa8a`) was also consulted **read-only**: it was never written to, its working
directory was never reused as a `cwd`, and no cherry-pick, merge, or deletion was
performed on it either. It held two artifacts that resolve row **R13**, the only
determinate row open on `main`:

| artifact | state in #212 | how it was taken |
|---|---|---|
| `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean` | **untracked** (kernel-checked; built there, no `sorry`/`axiom`/`admit`/`native_decide`) | copied by path into this worktree, then rebuilt, kernel-replayed, axiom-checked and re-run **here** |
| `scripts/verify_peroccurrence_dna_samelength_212.py` | committed in #212 as `6aeb95e` | copied by path, re-run here |

Taking a leaf artifact by copy is not the same as trusting it. Two guards were
applied before any matrix row changed.

1. **No predicate drift.** #212's `AssemblyP1/SourceFaithfulIs.lean` and
   `AssemblyP1/Section62BidirectedFlow.lean` — the two modules the harvested file
   imports besides Mathlib — are **byte-identical** to this worktree's copies
   (`diff -q`). The certificate therefore checks the same `InformationFeasible`
   and the same `SpelledFeasible62` here as it did there.
2. **Re-execution, not inheritance.** The module was rebuilt in this worktree
   (**Build completed successfully, 8926 jobs**), replayed through the kernel one
   module per process (**exit 0**, with a control
   `leanchecker AssemblyP1.NoSuchModuleXYZ` **exit 1** proving the pass is not a
   silent no-op), re-axiom-checked (`[propext, Classical.choice, Quot.sound]` on
   both endpoints and on the `Prop`), and its script re-run (**ALL CHECKS PASS**,
   46 assertions). In addition, front #217 independently re-derived the
   observation, both spectra, the support and per-occurrence conditions, and both
   exact ratios (`3/2`, `9/5`) from the two strings alone.

The result is row R13 resolved to **FALSE** by `ATATACAC → ATACACAC`
(`G=8`, `L=3`, `n=6 < N=8`, both candidates literal §6.2 bidirected circuits,
both per-occurrence feasible). The full record, including the bounded census and
its explicit non-claim of completeness, is
[`peroccurrence-samelength-dna-counterexample-212.md`](peroccurrence-samelength-dna-counterexample-212.md).

## 6. Epistemic status
