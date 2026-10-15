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
`python3 scratch257/verify_counterexample.py` (the §4 counterexample),
`python3 scratch257/finite_decider.py` (§11 finite-decider cross-check),
`python3 scripts/verify_257_two_walk_iff.py` (§12 two-closed-walk cross-check,
constructive n=3/4 and exhaustive search n=3),
`python3 scripts/verify_257_bouquet.py` (§13 bouquet Diophantine criterion
cross-check, exhaustive small scope).
Self-contained, exact integer arithmetic, deterministic._

_Blocking-review repair (2026-10-10, branch `research/257-graver-lean-repair`):
§2's false "primitive = Graver basis" equivalence is corrected (Graver =
conformally indecomposable in `ker_ℤ[M; 1ᵀ]`; `(1,1) ∈ ℤ²` is gcd-one but
decomposable), the salvaged Graver criterion is proved via conformal
decomposition, and the §9 status row no longer claims Graver enumeration is
verified. The Lean criterion is restated on the support domain (equality and
nonzero-`δ` restricted to `edges`), fixing the off-support equality gap;
`nonrigid_iff_exists_delta` is re-kernel-checked._

_Lean: the exact criterion (Theorem 1) is kernel-checked as
`AssemblyP1/ExactRigidityCriterion.lean` (`nonrigid_iff_exists_delta`), with
only the standard axioms `[propext, Classical.choice, Quot.sound]`. Build with
`lake build AssemblyP1.ExactRigidityCriterion`; audit with
`lake env lean AxiomAudit257.lean`._

_Lean (finite decider, 2026-10-14): the checkable decision procedure of §11 is
kernel-checked as `AssemblyP1/FiniteRigidityDecider.lean`
(`rigid_iff_forall_admissible`, `rigid_iff_decider`), with the same standard
axioms. It imports — and does not duplicate — `GraverRigidity.lean`; the
Graver criterion is `rigid_iff_forall_graver_not_feasible` there. Build with
`lake build AssemblyP1.FiniteRigidityDecider`._

_Lean (two-closed-walk criterion, 2026-10-15): §12's Theorem 5 is kernel-checked
as `AssemblyP1/TwoWalkRigidity.lean` (`rigid_iff_no_two_nonneg_circ`,
`nonrigid_of_two_nonneg_circ`, `exists_two_nonneg_circ_of_nonrigid`) with the
same standard axioms, resolving §8.3. Build with
`lake build AssemblyP1.TwoWalkRigidity`; audit with
`lake env lean AxiomAudit257.lean`._

_Lean (bouquet criterion, §8.1 progress, 2026-10-15): the bouquet reduction of
§13 is kernel-checked as `AssemblyP1/RigidityBouquet.lean`
(`bouquet_nonrigid_iff`, plus the rigid-repetitive instance
`len24_mult21_rigid`, the non-rigidity witness `len23_mult41_nonrigid`, and the
real/integer gap `len233_mult211_real_integer_gap`), with the same standard
axioms. Build with `lake build AssemblyP1.RigidityBouquet`; audit with
`lake env lean AxiomAudit257.lean`. This is a partial advance on §8.1: an exact,
checkable graph-theoretic criterion for the whole bouquet family and a
kernel-checked proof that the LP/fractional relaxation is **not** sufficient; a
polynomial min-cut/max-flow form for general supports (or a proof that none
exists) remains **OPEN**._

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
   vertices (§4). So the "two-cycle obstruction" condition is not iff.
   This counterexample does **not** rule out conditions allowing a fixed
   finite number `k > 2` of cycles, nor any fixed repeat bound (see §8.4 and
   §5.1); the non-necessity of "no triple repeat" is established separately
   by the `ATATAT` example (§5.1), not by this counterexample. [verified
   computation]

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

7. **The exact repeat-structural iff (two closed walks).** `A` is not rigid
   **iff** two **closed walks** `W₁, W₂` (of unbounded length, `w₁=1, w₂=-1`,
   equal length) satisfy `χ_{W₁} - χ_{W₂} ≥ -s` and `χ_{W₁} ≠ χ_{W₂}`. This is
   necessary **and** sufficient for strongly connected supports, resolving open
   item §8.3; it strictly extends the two-**cycle** certificate of item 3/4
   (which is only sufficient). [mathematical proof + kernel-checked, §12]

8. **Bouquet family: exact Diophantine criterion, and no fractional closed
   form.** For a **bouquet** (k directed cycles through one common vertex —
   the multi-cycle generalization of the figure-eight, and a genuine L-mer
   support), the exact criterion collapses to a bounded linear Diophantine
   condition: non-rigidity iff there is a nonzero integer `x` with
   `∑ len_i x_i = 0` and `x_i ≥ 1 - mult_i` (§13). This is a sharp, checkable,
   graph-theoretic criterion for the whole family, and a kernel-checked
   **real/integer gap** shows the rational (LP) relaxation is *not* sufficient,
   so no purely fractional min-cut/max-flow condition can decide rigidity.
   [mathematical proof + kernel-checked, §13]

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
`|E_i| ≥ |V_i|`; in particular `r ≥ c - 1 ≥ 0`, and `r = 0` iff every weak
component of `D` is a single directed cycle — for the strongly connected
support graphs of circular truths (§1), `r = 0` iff `D` is a single directed
cycle (the `ATATAT` case), which is automatically rigid.

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
depending on `s`; e.g. the figure-eight `0→1→0`, `0→2→0` is rigid at
`A = (1,1,1,1)` (`s = 0` everywhere) and non-rigid at `A = (2,2,1,1)`
(`s = (1,1,0,0)`; witness `δ = (-1,-1,1,1) = χ_{C2} - χ_{C1}`, giving the
alternative circulation `B = (1,1,2,2)`; note `δ = χ_{C1} - χ_{C2}` is *not*
in the box here, since it would force `B = (3,3,0,0) ≱ 1`).
[mathematical proof + verified computation]

**Graver primitive-trade reformulation (conformal certificate form).** A
nonzero `δ ∈ L_0 ∩ box` exists iff a **primitive** one does: if `δ = k·δ'`
with `δ' ∈ L_0` and `k ≥ 1`, then `δ' = δ/k ≥ -s/k ≥ -s`, so `δ' ∈ box`.
For `L_0 = ker[M; 1ᵀ] ∩ ℤ^E`, primitive ⟺ the coordinates of `δ` have
gcd `1` (if `g = gcd(δ) ≥ 2` then `δ/g ∈ L_0`; conversely `k | δ` for all
`k | gcd`).

**Graver ≠ primitive (blocking-review correction, 2026-10-10).** The
**Graver basis** `Gr(M)` of `L_0 = ker_ℤ[M; 1ᵀ]` is the set of
**conformally indecomposable** nonzero elements of the lattice: `g ∈ Gr(M)`
iff `g ≠ 0` and whenever `g = g1 + g2` with `g1, g2 ∈ L_0` sign-compatible
with `g` (`g1⁻ ≤ g⁻` and `g1⁺ ≤ g⁺` coordinatewise, likewise for `g2`),
then `g1 = 0` or `g2 = 0`. Every Graver element is primitive, but **not
conversely**: in `ker_ℤ(0) = ℤ²`, the vector `(1,1)` has gcd `1` yet
decomposes sign-compatibly as `(1,0) + (0,1)`, so it is primitive but not
Graver. The earlier claim "the primitive elements of a lattice are exactly
its Graver basis" is **false** and is removed. (The `n = 3` exhaustive check
that every non-rigid instance admits a **primitive** (`gcd`-`1`) element of
`L_0` inside the box — 389/389, 0 failures — remains valid **as a statement
about primitive elements**; it is **not** a verification of Graver
enumeration, which ranges over a strictly smaller set.)

**Correct Graver criterion (salvaged form).** `A` is rigid iff **no Graver
element** `g ∈ Gr(M)` satisfies `g ≥ 1 - A` coordinatewise (equivalently
`g⁻ ≤ s`).

_Proof._ (⟸) A Graver `g` with `g ≥ 1 - A` is itself a nonzero feasible `δ`,
so Theorem 1 gives non-rigidity. (⟹) By the Graver conformal-decomposition
theorem — every `δ ∈ ker_ℤ M` is a sign-compatible sum `δ = Σ_i g_i` of
Graver elements (Springer 2026, Def. 4 + Prop. 3; De Loera–Hemmecke–Onn,
Lemma 2.3) — a nonzero feasible `δ` has a Graver summand `g_i` with
`g_i⁻ ≤ δ⁻ ≤ s`, i.e. `g_i ≥ 1 - A`; so a Graver obstruction exists. ∎

`Gr(M)` is **finite** for any fixed integer matrix `M` (Dickson's lemma:
Graver elements are the ≼-minimal elements of `L_0 ∩ ℤ^E ∖ {0}` under the
conformal order, and minimal elements of a subset of `ℕ^E × ℕ^E` are
finite), **not** merely "of fixed rank"; its size can be exponential in
`|E|`, and no polynomial bound is claimed here.

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

**Rank-1 special case.** If `L_0` has rank `1` (e.g. a figure-eight: two cycles sharing one vertex), `L_0 = ℤ·g` for a primitive `g`, and `δ = k·g` fits the box iff `k·g(e) ≥ -s(e)` for all `e`. For `k > 0` the edges with `g(e) ≥ 0` are automatic and the edges with `g(e) < 0` need `k ≤ s(e)/|g(e)|`; so non-rigidity is exactly

```
min_{e : g(e) < 0} floor(s(e)/|g(e)|) ≥ 1   OR   min_{e : g(e) > 0} floor(s(e)/g(e)) ≥ 1
```

(equivalently, after replacing `g` by `-g` if needed: `s(e) ≥ |g(e)|` for **every** edge of one sign class — an all-edges check on one side of `g`, not a single-edge check). [mathematical proof; verified computation: exact on all 93 rank-1 instances of the `n = 3` scope]

**Failed simpler hypothesis (rank-1).** "`∃ e : s(e) ≥ |g(e)|`" (a single-edge check) is **not even sufficient**: the figure-eight `0→1→0`, `0→2→0` with `A = (2,1,1,1)` is rigid (verified: `L_0 = ℤ·(1,1,-1,-1)`; `k = 1` needs `s ≥ 1` on both `C_2` edges, `k = -1` needs `s ≥ 1` on both `C_1` edges), yet `s(0→1) = 1 ≥ |g(0→1)|`. [verified computation]

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

**Consequence.** The example rules out every condition stated purely in terms of **two** simple directed cycles. It does **not** rule out a condition allowing an arbitrary but fixed finite number `k` of cycles, nor any fixed repeat bound: whether, for every `k`, there is a non-rigid instance whose every witness needs `≥ k` simple cycles is **open** (no such family is known), and the non-necessity of repeat bounds such as "no triple repeat" is a separate matter established by the `ATATAT` example (§5.1), not by this counterexample. The exact criterion of Theorem 1 is genuinely an integer feasibility problem — real and integer non-rigidity provably differ (§7 witness). [mathematical proof + verified computation; the finite-k question is open]

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
   not the only rigid shape. E.g. the complete digraph `K_3^*` (all `6` arcs on
   `3` vertices, cycle rank `4`) at total `6` (`A = 1` everywhere) is rigid: the
   balance equations plus `∑ B = 6` with `B ≥ 1` on `6` edges force `B = 1`
   everywhere (verified by brute force). More generally, any support with
   `r = |E| - |V| + c - 1 = 0` is rigid regardless of `A` — for the strongly
   connected supports of circular truths `r = 0` iff the support is a single
   directed cycle, so every genuinely multi-cycle rigid example needs slack
   coordination, not just topology. (Abstract-graph caveat: disconnected
   supports such as two disjoint `3`-cycles are rigid at total `6` but are
   **not** valid circular-word read-support graphs, which are strongly
   connected; they are omitted here as genome examples.) [mathematical proof +
   verified computation]

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
| `n = 3` vertices, all strongly connected digraphs, all `A` with `G ≤ 3|E|` | two-cycle obstruction ⟺ non-rigid on **all 389** non-rigid cases (**447** pairs tested: 58 rigid + 389 non-rigid), **0** mismatches |
| `n = 3`, two-**closed-walk** obstruction (walks `≤ 6`) | agrees with brute-force rigidity on **all 447** pairs (389 non-rigid all detected, 58 rigid all clear), **0** mismatches |
| `n = 4` vertices, exhaustive in scope: all 1606 strongly connected digraphs, all `A` with `G ≤ 2|E|` (83532 pairs) | two-cycle obstruction ⟺ non-rigid except **96** instances forming **4 isomorphism families** (24 labelings each), one of which is the §4 counterexample; every exception needs `≥ 3` simple cycles |
| §4 counterexample | `A, B` positive circulations of total `13`, `A ≠ B`, no two-simple-cycle obstruction (verified) |

The `n = 3` agreement is exact and complete in scope; the `n = 4` run is
exhaustive in its own scope (every strongly connected `4`-vertex digraph, every
`A` with `G ≤ 2|E|`), not an exhaustive classification of all supports. The
exhaustive zeros are a sanity check on the proofs, not a substitute for them.
[verified computation]

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
  this note does not claim it.
* The LP relaxation `P = {δ : Mδ = 0, ∑δ = 0, δ ≥ -s}` is **not** an exact proxy:
  `P ≠ {0}` (real) does not imply a nonzero integer point, so real and integer
  non-rigidity can differ. **Justification (the non-TU remark alone is not
  enough):** it is true that `[M; 1ᵀ]` is not totally unimodular (the `2`-cycle
  submatrix `[[1,-1],[1,1]]` has determinant `2`), but non-TU of the constraint
  matrix does not by itself establish a real-vs-integer gap for this fiber; the
  gap is instead witnessed concretely. Smallest witness: on the `4`-arc graph
  `0→1, 0→2, 1→2, 2→0` with `A = (1,2,1,3)`, `P` contains the real point
  `(1/3, -1/2, 1/3, -1/6)` (take `δ = t·(1, -3/2, 1, -1/2)`, `0 ≤ t ≤ 2/3`)
  but `P ∩ ℤ^E = {0}` (integrality forces `δ_1 = 0`), so the instance is rigid
  while its LP relaxation reports non-rigidity. `36` such real-vs-integer gaps
  occur in the `n = 3` scope alone (all verified by exact vertex enumeration of
  `P`). [mathematical proof + verified computation; the exact classification
  is open]
* **Genome witness (the gap occurs for actual circular DNA).** `S = ACACAGT`,
  `L = 2`, `G = 7`: spectrum `AC:2, CA:2, AG:1, GT:1, TA:1`. Positive
  circulations of total `7` satisfy `2·B(AC) + 3·B(AG) = 7` with `B ≥ 1`;
  the only positive **integer** solution is `(2,1)`, so `S` is rigid. But over
  the reals `B(AC) = 3/2, B(AG) = 4/3` works (e.g. the positive real
  circulation `(3/2, 3/2, 4/3, 4/3, 4/3)` of total `7`): the LP relaxation
  reports non-rigidity for a rigid genome. [verified computation]

---

## 8. Open questions (kept explicitly OPEN)

1. **A closed-form graph-theoretic iff** for rigidity, beyond the algebraic
   criterion of Theorem 1 (e.g. a *polynomial-time* min-cut / max-flow
   characterization of `L_0 ∩ box ≠ {0}`). None is known; the §4 counterexample
   rules out the two-cycle condition specifically, and the two-**closed-walk**
   iff proved in §12 is repeat-structural rather than a min-cut form (it still
   searches over closed walks). **Partial progress (§13, 2026-10-15):** for the
   bouquet family the exact criterion is the bounded linear Diophantine
   condition `∃ x ≠ 0, ∑ len_i x_i = 0, x_i ≥ 1 - mult_i`, kernel-checked as
   `bouquet_nonrigid_iff`; a kernel-checked **real/integer gap**
   (`len233_mult211_real_integer_gap`) proves the rational/LP relaxation is
   **not** sufficient, so no fractional min-cut relaxation can be exact. The
   bouquet family already encodes bounded linear Diophantine feasibility (a
   numerical-semigroup / coin problem), so a *polynomial* general closed form is
   unlikely; the general case remains **OPEN**. [open; bouquet case reduced, §13]
2. **The exact complexity** of the exact criterion (§7). [open]
3. ~~**The two-closed-walk certificate** (§4)~~ **RESOLVED (2026-10-15).** The
   two-closed-walk certificate is necessary **and** sufficient for strongly
   connected supports; see Theorem 5 in §12. The earlier `n = 3` evidence was
   correct. [proved, §12]
4. **The finite-`k` cycle question** (§4): whether for every fixed `k` there is
   a non-rigid instance whose every witness needs `≥ k` simple cycles. The
   §4 example gives `k = 3`; no family for general `k` is known. [open]

---

## 9. Epistemic classification

| claim | status |
|---|---|
| Theorem 1: exact rigidity criterion (no nonzero zero-sum circulation in the box) | mathematical proof |
| Theorem 1 Lean kernel-check (`nonrigid_iff_exists_delta`, `ExactRigidityCriterion.lean`) | kernel-checked (axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Graver primitive-trade reformulation (no Graver basis element of `L_0` in the box) | mathematical proof (corrected statement; Graver enumeration **not** verified — independent audit pending) |
| Topological vs. multiplicity split (`L_0 ∩ box = {0}`) | mathematical proof |
| Theorem 2: two-cycle non-rigidity certificate | mathematical proof |
| Theorem 3 / §4: two-cycle certificate not necessary (4-vertex counterexample) | verified computation |
| §5.1 `ATATAT` rigid despite triples | mathematical proof |
| §5.3 rigid graphs with `≥ 2` independent cycles (`r = 0`) | mathematical proof |
| §6 exhaustive `n = 3` two-cycle agreement | verified computation, exhaustive in scope |
| §7 exact criterion is a finite integer feasibility problem | mathematical proof |
| §7 LP relaxation not exact (real/integer gap witnessed, §7) | mathematical proof + verified computation |
| §8.1 closed-form graph-theoretic iff (polynomial / min-cut form) | open |
| §8.2 exact complexity | open |
| §8.3 two-closed-walk certificate iff | mathematical proof + kernel-checked (`TwoWalkRigidity.rigid_iff_no_two_nonneg_circ`, §12) |
| §8.4 finite-`k` cycle question | open |
| §12 Theorem 5: two-closed-walk iff (general `w₁,w₂` and equal-length `w=1` forms) | mathematical proof + kernel-checked |
| §12 `ATATAT` has no two-closed-walk certificate | kernel-checked (`TwoWalkRigidity.atatat_no_two_nonneg_circ`) |
| §12 figure-eight two-closed-walk witness (`f=(0,0,1,1)`, `g=(1,1,0,0)`) | kernel-checked (`by decide`) |
| §12 exhaustive two-walk cross-check (constructive n=3: 389; n=4: 80864; search n=3: 389; 0 mismatches) | verified computation, exhaustive in scope |
| §11 finite decider: `Rigid ↔ ∀ B : E→Fin(G+1), Admissible B → B = A` | mathematical proof + kernel-checked (`FiniteRigidityDecider.rigid_iff_forall_admissible`) |
| §11 Boolean decider `decider` correctness | kernel-checked (`FiniteRigidityDecider.rigid_iff_decider`) |
| §11 worked instances (`ATATAT` rigid, `AAAAB` non-rigid, figure-eight rigid/non-rigid) | kernel-checked (`by decide`) |
| §11 finite-decider cross-check vs brute force (n=3: 255; n=4: 312; 0 mismatches) | verified computation, exhaustive in scope |
| §13 bouquet exact criterion (`bouquet_nonrigid_iff`: non-rigid iff `∃ x ≠ 0, ∑ len_i x_i = 0, x_i ≥ 1 - mult_i`) | mathematical proof + kernel-checked (`AssemblyP1/RigidityBouquet.lean`) |
| §13 bouquet rigid-repetitive instance `len24_mult21_rigid` | kernel-checked |
| §13 bouquet non-rigidity witness `len23_mult41_nonrigid` (`x = (-3, 2)`) | kernel-checked |
| §13 bouquet real/integer gap `len233_mult211_real_integer_gap` (rational `(-1, 0, 2/3)`, no integer solution) | mathematical proof + kernel-checked |
| §13 bouquet cross-check vs brute force (`scripts/verify_257_bouquet.py`: 3133 bouquets, 0 mismatches) | verified computation, exhaustive in scope |

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

---

## 11. The finite decider (checkable criterion; kernel-checked)

Theorem 1 is a *logical* iff; §11 turns it into a genuine terminating
**decision procedure**. The unblock is the coordinate bound.

**Proposition (coordinate bound).** If `B : E → ℤ` is a positive balanced
circulation of total `G` (`B ≥ 1`, `M B = 0`, `∑ B = G`), then for every edge
`e`,

```
1 ≤ B(e) ≤ G          (indeed B(e) ≤ G - (|E| - 1)).
```

_Proof._ `1 ≤ B(e)` is positivity. For the upper bound, every other coordinate
is `≥ 1 > 0`, so `B(e) ≤ ∑_{e'} B(e') = G`. ∎

Hence **every candidate `B` is already a function `E → Fin(G+1)`**, and the
candidate set `F` is exactly the image of the admissible part of the finite type
`E → Fin(G+1)`. This gives:

**Theorem 4 (finite criterion, `FiniteRigidityDecider.rigid_iff_forall_admissible`).**

```
A rigid  ⟺  ∀ B : E → Fin(G+1),
              (B ≥ 1) ∧ (M B = 0) ∧ (∑ B = G)  ⟹  ∀ e, B(e) = A(e).
```

Both directions are constructive. (⟸) encodes an arbitrary feasible integer
circulation into `Fin(G+1)` using the coordinate bound; (⟹) is immediate.

**Boolean decider (`decider`, `rigid_iff_decider`).** `decider A G` is the
`Bool` obtained by `decide` of the finite universal statement; `rigid_iff_decider`
proves `Rigid A G ↔ decider A G = true`. The search space has exactly
`(G+1)^{|E|}` elements (`card_candidates`), so the decider is a **finite
exhaustive exponential search**: for each *fixed* support size `|E|` it is
polynomial in the numeric magnitude `G` (with degree depending on `|E|`), but it
is exponential in the support size. It is **not** a general
pseudopolynomial-time algorithm (and not polynomial in the bit length of `G` or
in `|E|`). This resolves the "checkable, not merely a logical iff" gap without
needing a sharp Graver-basis cardinality bound (§8.2 remains open for a
polynomial classification).

**Kernel-checked worked instances.** The module contains `by decide` proofs of:

| instance | result |
|---|---|
| `S = ATATAT`, `L = 3` (`A = (3,3)`, `G = 6`) | rigid, though `AT`, `TA` each occur `3` times |
| `S = AAAAB`, `L = 2` (`A = (3,1,1)`, `G = 5`) | non-rigid (`B = (1,2,2)`) |
| figure-eight `0→1→0, 0→2→0`, `A = (1,1,1,1)`, `G = 4` | rigid |
| same figure-eight, `A = (2,2,1,1)`, `G = 6` | non-rigid (`B = (1,1,2,2)`) |

These are the exact witnesses of the failed simpler hypotheses recorded in §0.6
and §5–§6: the first is rigid *despite* a triple `(L-1)`-mer repeat, so "no
triple repeat" is not necessary; the third is rigid with two independent cycles,
so "single directed cycle" is not necessary; the third and fourth share the same
support but differ in rigidity, so topology alone does not determine `A`.

**Independent cross-check (`scratch257/finite_decider.py`).** A from-scratch
re-implementation of the decider (full `itertools.product(range(G+1), repeat=m)`
sweep with zero-coordinate rejection, no pruning) is compared against the
backtracking brute force `rigidity.is_rigid` on exhaustive small cases:

| scope | tested | rigid | non-rigid | skipped (`(G+1)^m` too large) | mismatches |
|---|---|---|---|---|---|
| `n = 3`, all strongly connected supports, `m ≤ 6`, `G ≤ 3m` | 255 | 58 | 197 | 8 | **0** |
| `n = 4`, all strongly connected supports, `m ≤ 5`, `G ≤ 2m` | 312 | 240 | 72 | 0 | **0** |

The four worked instances are also re-derived by the script. This confirms the
coordinate bound and the enumerated criterion on every instance in scope; it is
evidence for, not a replacement for, the kernel proofs.

**Epistemic status.** The decider theorems and the four worked instances are
kernel-checked with only `[propext, Classical.choice, Quot.sound]` (see
`AxiomAudit257.lean`); the cross-check is verified computation, exhaustive in
the stated scope. The broader closed-form/complexity questions (§8.1, §8.2)
remain **open**.

---

## 12. The two-closed-walk criterion is necessary and sufficient (resolves §8.3)

The **two-cycle** certificate of §3–§4 (two *simple* directed cycles) is
sufficient but **not** necessary. The natural weakening — allow the two
obstructions to be **closed walks** of unbounded length — *is* an iff. This
settles open item §8.3.

### 12.1 Statement

Let `D` be a strongly connected support graph (every edge on a directed cycle),
`A : E → ℕ` a positive circulation of total `G`, and `s := A - 1 ≥ 0` the
slack. A **closed walk** is a walk `W = e_1 ⋯ e_k` with `head(e_i) =
tail(e_{i+1})` and `head(e_k) = tail(e_1)`; its **count vector** is
`χ_W ∈ ℕ^E`, `χ_W(e) = #{i : e_i = e}`, and its **length** is
`|W| = ∑_e χ_W(e) = k`. A count vector of a closed walk is exactly a
**nonnegative integer circulation** whose support is connected; a nonnegative
integer circulation is a finite sum of such, and a single one whenever its
support is connected (Eulerian circuit in the multigraph with `f_e` parallel
copies of `e`).

**Theorem 5 (two-closed-walk criterion).** `A` is **not** rigid **iff** there
exist two closed walks `W₁, W₂` and integers `w₁, w₂`, not both zero, with

```
(i)   w₁·|W₁| + w₂·|W₂| = 0,                          (zero-sum)
(ii)  w₁·χ_{W₁} + w₂·χ_{W₂} ≥ -s   coordinatewise,     (inside the box)
(iii) w₁·χ_{W₁} + w₂·χ_{W₂} ≠ 0.                       (nonzero)
```

Moreover the certificate can always be taken with `w₁ = 1`, `w₂ = -1` and
`|W₁| = |W₂|`:

**Corollary 5′ (equal-length form).** `A` is not rigid iff there are two closed
walks `W₁, W₂` of **equal length** with `χ_{W₁} - χ_{W₂} ≥ -s` and
`χ_{W₁} ≠ χ_{W₂}`.

### 12.2 Proof

**(⟸) of Theorem 5.** Put `δ := w₁·χ_{W₁} + w₂·χ_{W₂}`. Each `χ_{Wᵢ}` is a
circulation (`M χ_{Wᵢ} = 0`) of total `|Wᵢ| = 1ᵀχ_{Wᵢ}`, so `M δ = 0` and
`1ᵀδ = w₁|W₁| + w₂|W₂| = 0` by (i). Condition (ii) is the box condition and
(iii) makes `δ` nonzero on the support. Theorem 1 gives that `A` is not rigid.
∎

**(⟹) of Theorem 5.** By Theorem 1 there is a nonzero `δ ∈ L₀` with
`δ ≥ -s`. Write `δ = δ⁺ - δ⁻` with `δ⁺, δ⁻ ≥ 0` (coordinatewise positive and
negative parts). Since `Mδ = 0`, the two parts have **equal divergence**
`D := Mδ⁺ = Mδ⁻` (each is the divergence contributed to a node by the
positive and the negative coordinates separately). The vector `D` has total
`1ᵀD = 0`. Because `D` is strongly connected, every integer divergence of
total `0` is realisable by a **nonnegative integer flow**: route each unit of
supply `D(v)⁺` from `v` to a vertex of demand `D(w)⁻` along a directed path
(strong connectivity supplies the path), accumulating an integer flow `h₀ ≥ 0`
with `Mh₀ = -D`. Choose also a nonnegative integer circulation `γ` whose
support is connected and spans all vertices (a closed walk visiting every
vertex; exists because `D` is strongly connected). Set

```
h := h₀ + γ ≥ 0,    f := δ⁺ + h,    g := δ⁻ + h.
```

Then:

* `Mf = Mδ⁺ + Mh = D - D = 0` and `Mg = Mδ⁻ + Mh = 0`: both are
  circulations, and `f, g ≥ 0`;
* `f - g = δ⁺ - δ⁻ = δ`, so `f - g ≥ -s` and `f ≠ g` (as `δ ≠ 0`);
* `1ᵀf - 1ᵀg = 1ᵀδ = 0`, so `|W_f| = |W_g|`;
* `supp(f) = supp(δ⁺) ∪ supp(h) ⊇ supp(γ)` is connected (every edge of `δ⁺`
  is incident to a vertex of the connected spanning support of `γ`), and
  likewise `supp(g)`.

Hence `f` and `g` are nonnegative integer circulations with connected support,
i.e. count vectors of closed walks `W_f`, `W_g` with `χ_{W_f} = f`,
`χ_{W_g} = g`. Taking `w₁ = 1`, `w₂ = -1` gives `δ = χ_{W_f} - χ_{W_g}`,
`|W_f| = |W_g|`, and (i)–(iii) hold. This proves both Theorem 5 and Corollary
5′. ∎

### 12.3 Relation to the two-cycle certificate

The two-cycle certificate of §3 is the special case in which `W₁, W₂` are
simple directed cycles (with the normalisation `w₁ = a|C₂|/g`,
`w₂ = -a|C₁|/g`). Theorem 3 / §4 exhibits a non-rigid instance where **no**
such pair exists, while its witness `δ = 2·χ_{0→1→2→0} - χ_W` is already a
two-**closed-walk** combination (the second walk `W` has length `6`). So the
closed-walk criterion is strictly more powerful than the two-cycle one, and by
Theorem 5 it is exact. The distinction is exactly the distinction between
*support topology* (simple cycles: not enough, §4) and *true multiplicities*
(repeated use of edges: enough, Theorem 5).

### 12.4 Worked instances

* **`S = ATATAT`, `L = 3` (rigid, no certificate).** `A = (3,3)`, `G = 6`,
  support a single directed `2`-cycle. Every nonnegative circulation is
  `(k,k)`; two of them with equal total have equal `k`, hence are equal. So the
  distinct equal-total pair required by Theorem 5 does not exist — consistent
  with rigidity, and with the triple `(L-1)`-mer repeats. [mathematical proof +
  kernel-checked `TwoWalkRigidity.atatat_no_two_nonneg_circ`]
* **Figure-eight `0→1→0, 0→2→0` at `A = (2,2,1,1)`, `G = 6` (non-rigid).** The
  two `2`-cycles `f = (0,0,1,1)`, `g = (1,1,0,0)` are nonnegative circulations
  of equal total `2`, distinct, with `f - g = (-1,-1,1,1) ≥ 1 - A`; they are
  the two closed walks. The *same support* at `A = (1,1,1,1)` has no such pair
  (slack `0`), so rigidity is a multiplicity, not a topology, property.
  [kernel-checked `TwoWalkRigidity.figureEight_two_walk_witness`]

### 12.5 Exhaustive cross-check (`scripts/verify_257_two_walk_iff.py`)

The script has two independent halves and exits non-zero on any failure.

| check | scope | result |
|---|---|---|
| constructive (proof's construction: complete `δ⁺`, `δ⁻` to connected circulations, extract Eulerian circuits, verify two equal-length walks in the box) | `n = 3`, all strongly connected supports, `G ≤ 3m`: 389 non-rigid of 447 | **0** failures |
| constructive | `n = 4`, all strongly connected supports, `G ≤ 2m`: 80864 non-rigid of 83532 | **0** failures |
| exhaustive search (enumerate closed walks up to length `10`, all `(w₁,w₂)` normalisations, compare with brute-force rigidity) | `n = 3`, `G ≤ 3m`: 447 | **0** mismatches |

The constructive half validates the *forward* direction of Theorem 5 on every
non-rigid instance in scope; the search half validates the criterion as a
predicate. Both are exhaustive in their stated scope. [verified computation]

### 12.6 Lean kernel check

`AssemblyP1/TwoWalkRigidity.lean` formalizes Theorem 5 in the equivalent
"two nonnegative circulations" form (the count vectors of the two closed
walks; see the module docstring for why the connected-support/Eulerian
refinement is a packaging step). The single graph-theoretic input is the
**routing property** `Routable` (`∀ p ≥ 0, ∃ h ≥ 0, p + h` is a circulation),
which is exactly the transshipment-routing consequence of strong connectivity
used in the proof; it is stated as a hypothesis rather than reproved from
connectivity.

* `isCirc_iff_balancedZ`: the explicit `IsCirc` predicate is `BalancedZ` on all
  vertices.
* `nonrigid_of_two_nonneg_circ`: the easy direction (no routing needed).
* `exists_two_nonneg_circ_of_nonrigid`: the constructive direction, via
  `δ⁺ + h`, `δ⁻ + h`.
* `rigid_iff_no_two_nonneg_circ`: `Rigid A G ↔ ¬ ∃ f g, TwoNonnegCirc A f g`,
  assuming `Routable`.
* Worked instances: `atatat_no_two_nonneg_circ` (no certificate) and
  `figureEight_two_walk_witness` (the two `2`-cycles), both kernel-checked with
  only `[propext, Classical.choice, Quot.sound]` (`TwoWalkRigidityAudit.lean`,
  `AxiomAudit257.lean`); no `sorry`, no `native_decide`.

**Complexity.** The criterion is *checkable* but not (via this form)
*polynomial*: enumerating closed walks is exponential, so §8.1 (a min-cut /
max-flow polynomial form) and §8.2 (exact complexity) remain **open**. The
contribution of §12 is an exact **repeat-structural** iff, not a complexity
improvement over the finite decider of §11.

**Epistemic status.** Theorem 5 and Corollary 5′ are [mathematical proof]; the
kernel-checked Lean form is [kernel-checked, standard axioms]; the exhaustive
cross-checks are [verified computation, exhaustive in scope]. §8.1, §8.2, §8.4
remain **open**.

---

## 13. The bouquet family: an exact Diophantine criterion (§8.1 progress)

This section advances open item §8.1 by giving an exact, checkable
graph-theoretic criterion for the **bouquet** family, and a kernel-checked proof
that the fractional (LP) relaxation is *not* exact.

### 13.1 Definition

A **bouquet** is a strongly connected support consisting of `k` directed cycles
`C_1, …, C_k` through one common vertex `v` (so the cycles are otherwise
vertex-disjoint). It is the multi-cycle generalization of the figure-eight
(§5.3), and it is a genuine `L`-mer support: a circular word that traverses each
loop is realizable (e.g. `ATATAC`, `L = 2`, is the figure-eight at vertex `A`).
Write `len_i ≥ 1` for the length of `C_i` and let the truth circulation `A` be
constant on each cycle, `A = mult_i ≥ 1` on every edge of `C_i` (the slack is
`s_i = mult_i - 1`). This is the spectrum of a circular word that traverses
`C_i` exactly `mult_i` times.

### 13.2 Every circulation is constant on each cycle

At an internal vertex of `C_i` there is exactly one in-edge and one out-edge
(the two consecutive edges of `C_i`), so balance forces their values equal; by
induction all `len_i` edges of `C_i` carry the same value `x_i`. Balance at the
common vertex is then automatic (`∑_i x_i = ∑_i x_i`). Conversely every vector
`x : ℤ^k` gives a circulation. Hence the circulation space is `ℤ^k`, and the
total mass is `1ᵀδ = ∑_i len_i x_i`.

### 13.3 Exact criterion

**Theorem 6 (bouquet criterion).** `A` is **not** rigid **iff** there is a
nonzero integer vector `x ∈ ℤ^k` with

```
∑_i len_i x_i = 0        (zero-sum)
x_i ≥ 1 - mult_i         (box)         for every i.
```

_Proof._ Immediate from Theorem 1 together with §13.2: a nonzero
`δ ∈ L_0 ∩ box` corresponds bijectively to a nonzero integer `x` with
`∑ len_i x_i = 0` and `x_i ≥ 1 - mult_i`. ∎

This specializes to the rank-one (`k = 2`) form of §3 and to the figure-eight,
and is kernel-checked as `AssemblyP1.RigidityBouquet.bouquet_nonrigid_iff`.
For `k ≥ 3` it is a genuinely two-dimensional lattice condition (e.g.
`len = (2, 3, 3)`, `mult = (2, 1, 1)`), not reducible to the two-cycle check.

### 13.4 No fractional closed form: the real/integer gap

The rational relaxation of the criterion (replace `ℤ` by `ℚ`) is the LP
relaxation `L_0 ∩ box ≠ {0}` over the reals (§7). The bouquet family exhibits a
gap: for `len = (2, 3, 3)`, `mult = (2, 1, 1)` the rational vector
`x = (-1, 0, 2/3)` satisfies `∑ len_i x_i = 2(-1) + 3·0 + 3·(2/3) = 0`,
`x_1 = -1 ≥ -1`, `x_2 = 0 ≥ 0`, `x_3 = 2/3 ≥ 0` and is nonzero, while no
*integer* `x` satisfies the constraints (the integer condition forces
`x_1 + x_2 = 0`, hence `x = 0`). So the instance is **rigid**, yet its LP
relaxation reports non-rigidity. This is kernel-checked as
`AssemblyP1.RigidityBouquet.len233_mult211_real_integer_gap` and rules out any
purely fractional min-cut/max-flow characterization of rigidity.

### 13.5 Relation to hardness and to §8.1

The bouquet criterion is exactly the feasibility of a bounded linear Diophantine
system `∑_i len_i x_i = 0`, `x_i ≥ 1 - mult_i`. This contains the
**numerical-semigroup / coin problem** (choose a cycle of length `t` with slack
`1`, and lengths `a_i` with slack `0`: non-rigidity then asks whether `t` is a
nonnegative combination of the `a_i`), which is the classical NP-complete
*coin problem* of Lueker (1975) in the relevant (binary) encoding. Hence the
general rigidity problem inherits a Diophantine core, and a *polynomial*
min-cut/max-flow closed form for general supports is unlikely (and remains
**OPEN**, §8.1/§8.2). The contribution here is a sharp, exact, checkable
criterion for the whole bouquet family, together with the kernel-checked proof
that no fractional relaxation can be exact.

### 13.6 Kernel-checked instances and cross-check

* `len24_mult21_rigid`: the bouquet `len = (2, 4)`, `mult = (2, 1)` — the
  `2`-cycle is traversed **twice**, yet the instance is rigid (`x_1 ≥ -1`,
  `x_2 ≥ 0`, `2x_1 + 4x_2 = 0` force `x = 0`). A rigid repetitive example.
* `len23_mult41_nonrigid`: the bouquet `len = (2, 3)`, `mult = (4, 1)` — the
  explicit witness `x = (-3, 2)` (`2·(-3) + 3·2 = 0`, `-3 ≥ -3`, `2 ≥ 0`).
* `len233_mult211_real_integer_gap`: the real/integer gap of §13.4.
* `scripts/verify_257_bouquet.py`: a self-contained, exact, deterministic
  cross-check. It recomputes rigidity from scratch by enumerating **all**
  positive integer circulations of total `G` on the actual support graph
  (balance-guided backtracking) and compares with the Diophantine criterion over
  an exhaustive small scope (`k ≤ 4`, cycle lengths `≤ 4`, multiplicities
  `≤ 3`, `G ≤ 12`: **3133** bouquets, **0** mismatches), and re-derives the gap
  and the worked instances. [verified computation, exhaustive in scope]

### 13.7 Epistemic status

Theorem 6 and the three worked instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityBouquetAudit`); no `sorry`/`admit`/`axiom`/`native_decide`.
The residual — a *polynomial* min-cut/max-flow closed form for general supports,
or a proof that none exists — remains **OPEN** (§8.1/§8.2).
