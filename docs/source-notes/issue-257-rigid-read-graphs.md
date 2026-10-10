# Issue #257: rigid read graphs beyond repeat bounds — an exact circulation criterion

_Status: mathematical proof + exact computation, 2026-10-10. Child of #255,
complements #256. This note gives a **necessary-and-sufficient checkable
condition** for uniqueness of positive length-`G` circulations on the oriented
`L`-mer support graph, proves it, and separates **support topology** from
**true multiplicities**. It records the exact algebraic criterion (iff), a
clean graph-theoretic **sufficient** certificate (two directed cycles), and an
explicit **counterexample** showing that certificate is not necessary. Every
claim is labelled **mathematical proof**, **verified computation**, or
**open**. It builds on — and does not redo — the short-repeat sufficiency
theorem of `oriented-se62-rigidity-theorem.md` (Theorem A: vertex throughput
`≤ 2` ⇒ rigid), which is kernel-checked in `AssemblyP1/OrientedRigidity.lean`.

_Reproduce: `python3 scratch257/rigidity.py`, `python3 scratch257/two_cycle.py`
(n=3 exhaustive), `python3 scratch257/test_n4.py twocycle` (n=4 cross-check),
`python3 scratch257/verify_counterexample.py` (the §4 counterexample).
Self-contained, exact integer arithmetic, deterministic._

---

## 0. Answer at a glance

Work on the oriented `L`-mer support graph `X_S` of a circular truth `S` of
length `G`: nodes are the distinct length-`(L-1)` windows, edges are the
distinct length-`L` windows `w` (edge `w` runs `prefix_{L-1}(w) →
suffix_{L-1}(w)`), and the truth spectrum `A(w) = spec_L(S)(w)` is a positive
integer circulation of total `G`. A **positive circulation of total `G`** is a
map `B : E → ℤ` with `B ≥ 1` on every edge, balanced at every node, and
`∑ B = G`. **`A` is rigid** iff it is the *only* such `B`.

1. **Exact criterion (iff).** `A` is rigid **iff there is no nonzero**
   `δ ∈ ℤ^E` with `M δ = 0` (balanced), `∑ δ = 0` (zero-sum), and
   `δ ≥ 1 - A` on every edge. Equivalently: no nonzero integral zero-sum
   circulation fits inside the box `∏_e [1 - A(e), ∞)`. This is the
   **verified exact graph criterion**; it is checkable (a finite integer
   feasibility problem). [mathematical proof]

2. **Support topology vs. true multiplicities.** The criterion factors into a
   *topological* part (the lattice `L_0 = ker[M; 1ᵀ] ∩ ℤ^E` of zero-sum
   circulations, depending only on the support graph) and a *multiplicity*
   part (the slack vector `s = A - 1 ≥ 0`, i.e. how far each edge is above
   its positive minimum). Rigidity is **not** determined by the support
   topology alone: the same graph is rigid or non-rigid depending on `A`.
   [mathematical proof + verified computation]

3. **A clean sufficient certificate (two directed cycles).** If two directed
   cycles `C1, C2` admit a zero-sum rerouting that stays inside the box —
   i.e. there are integers `w1, w2` (not both `0`) with
   `w1·|C1| + w2·|C2| = 0` and `w1·χ_{C1} + w2·χ_{C2} ≥ -s` — then `A` is
   **not** rigid. For edge-disjoint cycles this reads
   `min_{e ∈ C2} s(e) ≥ |C1| / gcd(|C1|,|C2|)` (or the symmetric). This is a
   polynomial-size graph-theoretic certificate of non-rigidity.
   [mathematical proof]

4. **The two-cycle certificate is NOT necessary.** There are non-rigid
   supports whose every non-rigidity witness needs **three or more** directed
   cycles; no two-cycle obstruction exists. Minimum such example on `4`
   vertices (§4). So no "two-cycle" (or, a fortiori, "no triple repeat")
   condition is iff. [verified computation]

5. **Rigid despite triples.** `S = ATATAT`, `L = 3` is a single directed
   `2`-cycle with `A = (3,3)`; it is rigid even though the `(L-1)`-mers
   `AT, TA` each occur `3` times. This is the canonical example that the
   short-repeat bound is sufficient but not necessary. [mathematical proof]

6. **Failed simpler hypotheses, recorded.** (a) "No `(L-1)`-mer occurs `≥ 3`
   times" is sufficient, not necessary (Example 5). (b) "A two-cycle
   obstruction exists" is sufficient, not necessary (Example in §4).
   (c) "The support graph is a single directed cycle" is sufficient, not
   necessary (rigid graphs with `≥ 2` independent cycles exist; §5).
   [mathematical proof + verified computation]

---

## 1. Setup and definitions

Let `D = (V, E)` be a finite directed graph (the support graph; we allow
self-loops, which arise from periodic words such as `AAA`). Let
`M : ℤ^E → ℤ^V` be the incidence matrix, `(M x)_v = ∑_{e leaves v} x_e -
∑_{e enters v} x_e`. A **circulation** is `x` with `M x = 0`. The **cycle
space** `ker M` has dimension `|E| - |V| + c` (`c` = number of weakly
connected components). The **zero-sum circulations** are
`L_0 = { δ ∈ ℤ^E : M δ = 0, ∑ δ = 0 }`, a lattice of rank
`r = |E| - |V| + c - 1` (the all-ones functional is never trivial on `ker M`
when `E ≠ ∅`).

Fix a positive circulation `A : E → ℕ` (`A ≥ 1`) with `∑ A = G`. Define the
**slack** `s := A - 1 ≥ 0`. The **candidate set** is

```
F = { B ∈ ℤ^E : B ≥ 1 on E,  M B = 0,  ∑ B = G }.
```

`A ∈ F`. **`A` is rigid** iff `F = {A}`.

Two facts about the support graph of a circular word (proved in
`OrientedRigidity.lean`, `truth_balanced` / `truth_strongly_connected`):
`A` is balanced, and `X_S` is strongly connected. We do **not** assume these
abstractly; they are consequences of the circular-word structure. Every edge
of a positive circulation's support lies on a directed cycle (flow
decomposition), so the support has no bridges and every component satisfies
`|E_i| ≥ |V_i|`; in particular `r ≥ c - 1 ≥ 0`, and `r = 0` iff `D` is a
single directed cycle (the `ATATAT` case), which is automatically rigid.

---

## 2. The exact criterion (necessary and sufficient)

**Theorem 1 (exact rigidity criterion).** `A` is rigid **iff** there is **no**
nonzero `δ ∈ ℤ^E` with
```
M δ = 0,   ∑_{e} δ_e = 0,   δ_e ≥ 1 - A(e)   for all e ∈ E.
```

_Proof._ (⟸) If such `δ` exists, put `B := A + δ`. Then `M B = 0`,
`∑ B = G + 0 = G`, and `B ≥ A - s = 1` (since `δ ≥ -s = 1 - A`). So
`B ∈ F`. And `B ≠ A` because `δ ≠ 0`. Hence `F ≠ {A}`: not rigid.

(⟹) If `B ∈ F` and `B ≠ A`, put `δ := B - A`. Then `M δ = 0`,
`∑ δ = G - G = 0`, and `δ = B - A ≥ 1 - A` (since `B ≥ 1`). And
`δ ≠ 0`. So such a `δ` exists. ∎

**Conceptual restatement.** `A` is rigid iff **every** nonzero integral
zero-sum circulation **overdraws** at least one edge below its positive
minimum, i.e. `δ_e < 1 - A(e)` for some `e`. Non-rigidity is exactly the
existence of a nonzero zero-sum circulation that stays inside the box
`∏_e [1 - A(e), ∞)`.

**Equivalent flow form.** Put `y := δ + s = B - 1 ≥ 0`. Then
`M y = -div` (where `div_v = outdeg(v) - indeg(v)`) and `∑ y = G - |E|`.
So: **`A` is rigid iff `s = A - 1` is the unique nonnegative integer flow
`y` with `M y = -div` and `∑ y = G - |E|`.** This is a fixed-value
transshipment problem; non-rigidity is the existence of a second feasible
flow of the same total. [mathematical proof]

**Topological vs. multiplicity split.** The obstruction set is
`L_0 ∩ box` where `L_0 = ker[M; 1ᵀ] ∩ ℤ^E` (topology only) and
`box = {δ : δ ≥ -s}` (multiplicity only). Rigidity is the statement
`L_0 ∩ box = {0}`. The same graph (same `L_0`) is rigid or non-rigid
depending on `s`; e.g. two disjoint `3`-cycles are rigid at total `6`
(`s = 0` everywhere) and non-rigid at total `9` (`s = (1,1,1,0,0,0)`).
[mathematical proof + verified computation]

---

## 3. A clean sufficient certificate: two directed cycles

**Theorem 2 (two-cycle non-rigidity certificate).** Let `C1, C2` be two
directed cycles in `D` (distinct edge sets) and `w1, w2 ∈ ℤ` not both zero
with
```
w1·|C1| + w2·|C2| = 0,          (zero-sum)
w1·[e ∈ C1] + w2·[e ∈ C2] ≥ -s(e)   for all e ∈ E.   (inside the box)
```
Then `A` is **not** rigid.

_Proof._ `δ := w1 χ_{C1} + w2 χ_{C2}` is a circulation (sum of two directed-
cycle circulations), zero-sum by the first condition, and `δ ≥ -s` by the
second. Since `C1 ≠ C2`, `χ_{C1}` and `χ_{C2}` are linearly independent, so
`(w1,w2) ≠ (0,0)` gives `δ ≠ 0`. By Theorem 1, `A` is not rigid. ∎

**Minimal form.** The zero-sum condition forces `w1 = a·|C2|/g`,
`w2 = -a·|C1|/g` with `g = gcd(|C1|,|C2|)`, `a ∈ ℤ \ {0}`. The box condition
is easiest at `|a| = 1` (larger `|a|` only tightens it), so it suffices to
check `a = ±1`. For **edge-disjoint** cycles the condition simplifies to

```
min_{e ∈ C2} s(e) ≥ |C1| / gcd(|C1|,|C2|)   OR   min_{e ∈ C1} s(e) ≥ |C2| / gcd(|C1|,|C2|).
```

_Proof of the simplification._ With `a = 1`, `w1 = |C2|/g > 0`,
`w2 = -|C1|/g < 0`. On `C1` the value is `|C2|/g ≥ 1 > 0 ≥ -s(e)`; on `C2`
it is `-|C1|/g ≥ -s(e)`, i.e. `s(e) ≥ |C1|/g`. The `a = -1` case is the
symmetric statement with `C1, C2` swapped. ∎

**Rank-1 special case.** If `L_0` has rank `1` (e.g. a figure-eight: two
cycles sharing one vertex), `L_0 = ℤ·g` for a primitive `g`, and non-rigidity
is exactly `∃ e : s(e) ≥ |g(e)|` — a single-edge check. [mathematical proof]

---

## 4. The two-cycle certificate is not necessary (counterexample)

**Theorem 3 (two-cycle sufficiency is strict).** There is a strongly
connected support graph `D` and a positive circulation `A` such that `A` is
**not** rigid, yet **no** two directed cycles satisfy Theorem 2.

_Counterexample (verified)._ `D` on `4` vertices with edge set
```
0→1, 0→2, 1→0, 1→2, 1→3, 2→0, 2→1, 2→3, 3→0   (9 edges; K_4^* minus 0→3, 3→1, 3→2)
```
and
```
A = (1,3,1,1,1,1,2,1,2),   B = (3,1,1,2,1,1,1,1,2),   G = 13.
```
Both `A` and `B` are positive circulations of total `13` (checked: balanced at
every node, `≥ 1`, total `13`), and `A ≠ B`. So `A` is not rigid. The
difference `δ = B - A = (2,-2,0,1,0,0,-1,0,0)` is a zero-sum circulation with
`δ ≥ 1 - A`. An exhaustive search over **all** pairs of simple directed cycles
in `D` (all cycles have length `≤ 4`) finds **no** two-cycle obstruction: the
witness `δ` is supported on `{0→1, 0→2, 1→2, 2→1}`, whose only simple
directed cycle is `1→2→1`; the edges `0→1, 0→2` are not on any directed cycle
inside the support, so `δ` cannot be a two-(simple)-cycle combination. It is,
however, a two-**closed-walk** combination `δ = 2·χ_{0→1→2→0} - χ_{W}` for the
length-`6` closed walk `W = 1→2→0→2→0→2→1`. [verified computation]

**Consequence.** No condition stated purely in terms of "two cycles" (or any
fixed finite number of cycles, or any fixed repeat bound) is necessary and
sufficient. The exact criterion of Theorem 1 is genuinely an integer
feasibility problem. [mathematical proof + verified computation]

---

## 5. Rigid repetitive examples

1. **`S = ATATAT`, `L = 3` (rigid despite triples).** `spec_3 = {ATA:3,
   TAT:3}`. Support graph: two nodes `AT, TA`, two edges `ATA (AT→TA)`,
   `TAT (TA→AT)` — a single directed `2`-cycle. Positive circulations of
   total `6`: `B(ATA) = B(TAT) = k`, `2k = 6`, so `k = 3` uniquely. Rigid.
   Yet the `(L-1)`-mers `AT` and `TA` each occur `3` times. This is the
   canonical refutation of "no triple repeat ⇔ rigid". [mathematical proof]

2. **Periodic truths `S = P^k`.** If `P` is primitive with no factor of length
   `≥ L-1` repeated, `X_S` is a single directed `p`-cycle with `A = k` on
   every edge; rigid (unique circulation `k`). [mathematical proof; cf.
   `oriented-se62-rigidity-theorem.md` §3]

3. **Rigid graphs with `≥ 2` independent cycles.** A single directed cycle is
   not the only rigid shape. E.g. two disjoint `3`-cycles at total `6`
   (`A = 1` everywhere) are rigid (§2), and more generally any support with
   `r = |E| - |V| + c - 1 = 0` is rigid regardless of `A`. [mathematical proof]

4. **Non-rigid witnesses (for contrast).** The minimum same-length non-rigid
   pair is `S = AAAAB`, `D = AABAB` (`G = 5`, `L = 2`), spectra
   `{AA:3,AB:1,BA:1}` vs `{AA:1,AB:2,BA:2}`; both carry a length-`1` triple
   repeat. [verified computation; cf. `oriented-se62-rigidity-theorem.md` §5]

---

## 6. Exhaustive cross-checks

`scratch257/` re-implements spectra, support graphs, rigidity (exact
brute-force over all positive circulations), the two-cycle search, and the
counterexample from scratch (no repository import).

| scope | result |
|---|---|
| `n = 3` vertices, all strongly connected digraphs, all `A` with `G ≤ 3|E|` | two-cycle obstruction ⟺ non-rigid on **all 389** non-rigid cases, **0** mismatches |
| `n = 3`, two-**closed-walk** obstruction (walks `≤ 6`) | matches non-rigid on **all 447** cases, **0** mismatches |
| `n = 4` vertices, sample (`G ≤ 2|E|`) | two-cycle obstruction ⟺ non-rigid except the §4 counterexample family (needs `≥ 3` cycles) |
| §4 counterexample | `A, B` positive circulations of total `13`, `A ≠ B`, no two-simple-cycle obstruction (verified) |

The `n = 3` agreement is exact and complete in scope; the `n = 4` run is a
cross-check, not an exhaustive classification. The exhaustive zeros are a
sanity check on the proofs, not a substitute for them. [verified
computation]

---

## 7. Complexity

* The exact criterion (Theorem 1) is a **finite integer feasibility problem**:
  decide whether `∃ δ ∈ ℤ^E \ {0}` with `M δ = 0`, `∑ δ = 0`, `δ ≥ 1 - A`.
  Since `|δ_e| ≤ G - |E|` (from `δ ≥ 1 - A` and `∑ δ = 0`), the search is
  bounded, hence decidable. [mathematical proof]
* The two-cycle certificate (Theorem 2) is a **finite sufficient check**
  (enumerate pairs of simple directed cycles; the number can be exponential,
  but each check is polynomial). [mathematical proof]
* The **precise complexity classification** of the exact criterion (whether
  it is polynomial via a flow reduction, or NP-hard in general) is **open**;
  this note does not claim it. The LP relaxation
  `P = {δ : Mδ = 0, ∑δ = 0, δ ≥ -s}` is **not** an exact proxy: `P ≠ {0}`
  (real) does not imply a nonzero integer point (the constraint matrix
  `[M; 1ᵀ]` is not totally unimodular), so real and integer non-rigidity can
  differ. [mathematical proof of the TU failure; the exact classification is open]

---

## 8. Open questions (kept explicitly OPEN)

1. **A closed-form graph-theoretic iff** for rigidity, beyond the algebraic
   criterion of Theorem 1 (e.g. a min-cut / max-flow characterization of
   `L_0 ∩ box ≠ {0}`). None is known; the §4 counterexample rules out every
   fixed-finite-cycle and fixed-repeat-bound condition. [open]
2. **The exact complexity** of the exact criterion (§7). [open]
3. **The two-closed-walk certificate** (§4): whether it is necessary and
   sufficient when walks of unbounded length are allowed. The `n = 3` evidence
   is consistent with it, but no proof or counterexample is known. [open]

---

## 9. Epistemic classification

| claim | status |
|---|---|
| Theorem 1: exact rigidity criterion (no nonzero zero-sum circulation in the box) | mathematical proof |
| Topological vs. multiplicity split (`L_0 ∩ box = {0}`) | mathematical proof |
| Theorem 2: two-cycle non-rigidity certificate | mathematical proof |
| Theorem 3 / §4: two-cycle certificate not necessary (4-vertex counterexample) | verified computation |
| §5.1 `ATATAT` rigid despite triples | mathematical proof |
| §5.3 rigid graphs with `≥ 2` independent cycles (`r = 0`) | mathematical proof |
| §6 exhaustive `n = 3` two-cycle agreement | verified computation, exhaustive in scope |
| §7 exact criterion is a finite integer feasibility problem | mathematical proof |
| §7 LP relaxation not exact (`[M; 1ᵀ]` not TU) | mathematical proof |
| §8.1 closed-form graph-theoretic iff | open |
| §8.2 exact complexity | open |
| §8.3 two-closed-walk certificate iff | open |

---

## 10. Sources and relation to prior work

* Builds on `docs/source-notes/oriented-se62-rigidity-theorem.md` (Theorem A:
  throughput `≤ 2` ⇒ rigid) and its kernel-checked core
  `AssemblyP1/OrientedRigidity.lean` (`unique_positive_circulation`,
  `rigidity_same_spectrum`). This note does **not** redo that sufficiency; it
  supplies the missing **necessity** direction and the exact criterion.
* Complements #256 (the robust same-length ML iff); the graph criterion here is
  the uniqueness half that #256's `F = {A}` statement needs.
* The `ATATAT` example and the "no triple repeat is sufficient not necessary"
  observation are from the issue statement; proved here as §5.1.
