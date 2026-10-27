# Issue #261: reduction/occurrence bridge — candidate universe and transfer boundary (2026-10-27)

**Status:** checkable increment. Exact bounded witness plus explicit OPEN axes.
No maximality theorem claimed. Keep #261 and parent #255 OPEN.

## 1. Repository and source identity

- Repository: `https://github.com/ottojung/assemblyp1` (verified `origin`), base
  `main` @ `3decc39`, this branch `agent-B05bI5V30Eruk-issue261-bridge`.
- Primary sources: Medvedev–Brudno (2009, MB09) §6.2 (transitive reduction,
  Observation 7) and Myers (2005) §2 (idealized transitive edge as a two-hop
  path spelling the same sequence). Noisy/FUZZ practical details are out of scope.
- Repository model: equal-length (`L`), error-free reads; idealized same-spelling
  relation `TwoHopSameSpelling` and spelling law `l₁ + l₂ = L + e.len`
  (`AssemblyP1/Section62MyersIdealTransitivity.lean`,
  `AssemblyP1/Section62SimultaneousReduction.lean`,
  `docs/section62-simultaneous-reduction-284.md` for #284).

## 2. Candidate universe taxonomy (what "candidate" means here)

Without fixing this, maximality statements are ill-typed. This note uses:

- **(F)** bidirected flows on the overlap graph (integer flows; vertex lower
  bound 1 where stated; half-integral relaxation as a separate class);
- **(C)** spelled circuits (closed bidirected walks with spelled words);
- **(G)** circular genomes (strings; RC/orientation quotient applied or not —
  must be stated per claim).

Reductions act on graphs, likelihoods act on genomes/flows through observations.
Transfer across reduction requires proving candidate-set inclusion/equality
**and** objective-value preservation — language preservation alone does not
suffice (§4).

## 3. What is proved elsewhere and reused (not re-proved here)

- `reducible_iff_ideal_two_hop`: one-step spelling reduction ≡ idealized Myers
  same-spelling relation (equal-length model).
- `reduction_preserves_language` / `exists_irreducible_expansion`: every
  complete-graph edge expands to a finite chain of surviving (irreducible)
  edges spelling the same word; extension length `L − overlap` strictly
  decreases, so cascades terminate. This resolves the #284 simultaneous-removal
  gap for the idealized model. It is a **graph-language** statement.

## 4. Exact bounded witness: language ≠ occurrence correspondence

`scripts/verify_261_reduction_occurrence_gap.py` kernel-checks (by `decide`-free
exact asserts, no search) the instance `L = 5`:

- `sx = 01234`, `m₂ = 12341`, `m₁ = 23412`, `sy = 41200`.
- Direct edge `sx → sy`, overlap 1; detour `sx → m₁ → sy`, overlaps 3, 3,
  `3 + 3 = 5 + 1`. First leg reducible via `m₂`, overlaps 4, 4, `4 + 4 = 5 + 3`.
- Terminal chain `sx → m₂ → m₁ → sy` spells exactly `012341200`, the direct
  word. Length-5 windows: `01234, 12341, 23412, 34120, 41200`.
- `34120` is a physical window of the spelled word but is **not** in the
  observed vertex set `{sx, m₂, m₁, sy}`.

Hence neither spelled-string equality nor its physical-window multiset implies
equality of graph-vertex visits with physical occurrence counts. Any ML transfer
whose objective depends on vertex throughput needs an independent walk/flow ↔
observation correspondence proof; it cannot be inferred from language
preservation. This is not a counterexample to MB09 Observation 7 under its
intended walk/occurrence definitions, which remain to be reconciled
proposition-by-proposition.

## 5. Relation to neighboring issues (no forks)

- **#284 (spelling-reduction candidate):** this note consumes, without
  redefining, `isReducibleSpellingB` and the simultaneous-reduction theorems.
  The cascade instance above instantiates (not refutes) that machinery.
- **#259 (binomial/maximality classifications):** likelihood axis (exact vs
  fixed-`N` binomial), fixed-support flow pairs, and extreme-sample criteria
  stay in #259's ownership; this note adds no likelihood theorem.
- **#255 (parent ML maximality):** truth admission, length universe
  (fixed vs variable), RC/orientation quotient, and integer vs half-integral
  flow classes stay open here and in #255; positive full-overlap transfers to
  arbitrary `o_min ≤ L − 1` require proved candidate-set inclusion and are not
  made here.

## 6. Explicit OPEN subclaims

1. Reconcile MB09 Observation 7 walk/occurrence definitions against the
   repository's `Chain`/`spellChain`/flow notions (exact statement or
   counterexample).
2. Necessary-and-sufficient maximality conditions per class
   (F)/(C)/(G) × {integer, half-integral} × {exact, fixed-`N`} × length
   universe × RC quotient × truth admission.
3. Vertex lower bound 1 and orientation/RC-class effects on each cell.
4. Integer-vs-half-integral gaps that survive reduction (cite #259 cells,
   do not duplicate them).

## Evidence

- New: `scripts/verify_261_reduction_occurrence_gap.py` (PASS, see §4).
- Reused: `AssemblyP1/Section62MyersIdealTransitivity.lean`,
  `AssemblyP1/Section62SimultaneousReduction.lean`,
  `docs/section62-simultaneous-reduction-284.md`.
- Validations: `python3 scripts/verify_261_reduction_occurrence_gap.py`,
  `python3 scripts/check-research-docs.py`, `git diff --check`. No Lean
  change/build in this increment.
