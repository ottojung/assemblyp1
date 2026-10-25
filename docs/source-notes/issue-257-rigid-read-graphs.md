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
cross-check, exhaustive small scope),
`python3 scripts/verify_257_bridge.py` (§14 antiparallel-bridge four-variable
criterion cross-check, exhaustive small scope),
`python3 scripts/verify_257_target_cycle.py` (§15 target-cycle coin reduction
and Apéry-set polynomial cross-check),
`python3 scripts/verify_257_length3_bridge.py` (§17 length-3 antiparallel-bridge
four-variable criterion and classification cross-check, exhaustive small scope),
`python3 scripts/verify_257_general_bridge.py` (§18 general `p,q` long-bridge
four-variable criterion cross-check, exhaustive small scope),
`python3 scripts/verify_257_double_theta.py` (§19 double-theta four-variable
coupled criterion, rigid repetitive instance and coupling refutation cross-check,
exhaustive small scope),
`python3 scripts/verify_257_multi_hub.py` (§20 multi-hub two-equation criterion,
polynomial DP decision, rigid repetitive instance and coupling refutation
cross-check, exhaustive small scopes),
`python3 scripts/verify_257_tri_hub.py` (§21 triangular multi-hub three-equation
criterion, polynomial DP decision, rigid repetitive instance, non-rigidity
witness and coupling refutation, mutation-red control, exhaustive small scopes).
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
kernel-checked proof that the direct LP/fractional relaxation is **not** sufficient; a
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

8. **Bouquet family: exact Diophantine criterion; direct LP relaxation fails.**
   For an abstract directed bouquet (k cycles through one common vertex),
   non-rigidity is equivalent to a nonzero integer vector x satisfying
   sum_i len_i x_i = 0 and x_i >= 1 - mult_i. The kernel-checked real/integer
   gap proves only that this direct rational relaxation is insufficient,
   not that all exact LP/extended formulations or min-cut algorithms fail.
   A genuine circular DNA read-spectrum realization of the (2,3,3) bouquet
   is Lean-checked in RigidityBouquetGenomeWitness.lean.
   [mathematical proof + kernel-checked, section 13]

9. **Antiparallel bridge: a genuinely coupled criterion beyond the bouquet.**
   A single extra arc on a figure-eight cannot be positive (balance forces it to
   0), so the minimal positive cross-connection is an antiparallel arc pair.
   The resulting *bridge graph* has a 4-parameter circulation space with coupled
   box constraints; non-rigidity is exactly
   `∃ (a,c,p,q) ≠ 0, 2a+2c+p+q = 0, a ≥ 1-m1, a+q-p ≥ 1-m1, c ≥ 1-m2,
   c+p-q ≥ 1-m2, p ≥ 1-f, q ≥ 1-f`, kernel-checked as `bridge_nonrigid_iff`.
   Classification: the bridge is rigid **iff** all multiplicities are `1`
   (`bridgeA_rigid_iff_trivial`); otherwise explicit witnesses. The bridge is an
   abstract support (this exact shape is not a de Bruijn read-support).
   [mathematical proof + kernel-checked, section 14]

10. **Target-cycle bouquet: exact coin reduction; bouquet rigidity is in P.**
    The bouquet with `n` coin cycles (lengths `a_i`, traversed once) and one
    target cycle (length `t`, traversed twice) is not rigid **iff** `t` is a
    nonnegative integer combination of the `a_i` (kernel-checked
    `targetCycle_nonrigid_iff_coin`). This is exactly the unbounded coin /
    numerical-semigroup problem. Because an *explicit* support graph encodes the
    coin lengths in **unary**, representability — hence bouquet rigidity — is
    decidable in polynomial time by the Apéry-set / residue-graph shortest-path
    algorithm (`O(m·n)` ops). This is a genuine §8.2 **upper bound** and it
    **refutes** the tempting "the bouquet encodes an NP-hard problem" reading
    for explicit supports; the uniform-in-support complexity remains **OPEN**.
    [mathematical proof + kernel-checked + verified computation, section 15]

11. **Length-3 bridge: the bridge classification does not generalise.** Replacing
    each `2`-cycle of the antiparallel bridge by a `3`-cycle gives a new topology
    whose circulation is `δ = φ(a,c,u,w)`, zero mass `3a+3c+u+w=0`, and a coupled
    box (kernel-checked `length3Bridge_nonrigid_iff`). Its exact classification is
    rigid **iff** `m₁ = 1 ∧ m₂ = 1 ∧ f ≤ 2` (`length3Bridge_rigid_iff`). In
    particular `(m₁, m₂, f) = (1, 1, 2)` is a **rigid repetitive** support
    (`length3Bridge_rigid_repetitive`), so the merged bridge rule "rigid iff all
    multiplicities `1`" is **false** for longer cycles. This is a committed
    counterexample to that tempting generalisation. [mathematical proof +
    kernel-checked, section 17]

12. **Coupling begins at cycle rank 3; the double theta is minimal among
    realizable supports.** Every strongly connected support of cycle rank `≤ 2`
    is a single cycle, a figure-eight (the `k = 2` bouquet) or a theta graph,
    whose shared path carries the *sum* of the two private path values, so the
    shared box is redundant and the exact criterion is the **bouquet criterion**
    (no coupling). The smallest genuinely coupled support **that is realizable as
    a de Bruijn read-support** is the **double-theta graph** (rank `3`): two hubs
    joined by one arc and one length-`2` path in each direction. (Category
    distinction: among *abstract* supports the `3`-vertex `K3`-minus-an-arc is
    also rank `3` and coupled but is **not** realizable; see §19.6.) Its exact
    criterion is a four-variable integer system coupled by an **extra
    hub-balance equation** (`doubleTheta_nonrigid_iff`); the instance
    `(m₁,m₂,n₁,n₂) = (2,1,2,1)` is a **rigid repetitive** support, and dropping
    the coupling equation is **not sound** (`relaxed_not_sound`). [mathematical
    proof + kernel-checked, section 19]

13. **The multi-hub family: an unbounded-cycle-rank family with a polynomial
    criterion (§8.1/§8.2 progress).** The *multi-hub* family joins two hubs by
    `k` `u → v` paths and `l` `v → u` paths of **arbitrary lengths**; its cycle
    rank is `k + l - 1`, which is **unbounded**, so it strictly exceeds the
    bounded-cycle-rank families (bouquet / bridge / double theta are the cases
    `k + l ≤ 4`). Every circulation is constant on each path, and the exact
    criterion is a **two-equation** integer system — hub balance
    `∑_{u→v} α = ∑_{v→u} α`, zero total mass `∑ length·α = 0`, and the boxes
    `α ≥ 1 - m` (kernel-checked `multiHub_nonrigid_iff`). The instance
    `(lengths (1,3), multiplicities (2,1))` is a **rigid repetitive** support,
    and dropping the hub-balance coupling is **not sound**
    (`multiHub_relaxed_not_sound`), so no independent-per-path / single-cut
    criterion decides the family. Because the path lengths are unary, the
    two-equation system is a nonnegative-integer **uniqueness** problem
    decidable by a polynomial DP (counting solutions up to `2`), giving a §8.2
    **upper bound for this unbounded-rank family**; the *general*-support case
    (arbitrary topology) and any min-cut/max-flow closed form for it remain
    **OPEN**. [mathematical proof + kernel-checked + verified computation,
    section 20]

14. **The triangular multi-hub family: a genuinely three-hub unbounded-rank
    family (§8.1/§8.2 progress).** The *triangular multi-hub* family joins three
    hubs `u, v, w` in a directed cycle: `a` `u → v` paths, `b` `v → w` paths and
    `c` `w → u` paths of **arbitrary lengths**; its cycle rank is `a + b + c - 2`,
    **unbounded**. It is a genuinely *three-hub* topology — the merged two-hub
    multi-hub (§20) is the degenerate two-hub case — and adds a **second
    independent hub-balance equation**, so every circulation is constant on each
    path and the exact criterion is a **three-equation** integer system:
    `∑_{u→v} α = ∑_{v→w} β = ∑_{w→u} γ` (two hub balances), zero total mass
    `∑ length·α + ∑ length·β + ∑ length·γ = 0`, and the boxes `α ≥ 1 - m`
    (kernel-checked `triHub_nonrigid_iff`). The instance
    `(lengths (1,3), multiplicities (2,1))` in each direction is a **rigid
    repetitive** support, and dropping the hub-balance coupling is **not sound**
    (`triHub_relaxed_not_sound`), so no independent-per-path / single-cut
    criterion decides the family. Because the path lengths are unary, the
    three-equation system is a nonnegative-integer **uniqueness** problem
    decidable by a polynomial DP (counting solutions up to `2`), a §8.2 upper
    bound for this unbounded-rank family. [mathematical proof + kernel-checked +
    verified computation, section 21]

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
   **not** sufficient for that direct integer system. This does not rule out
   other exact LP/extended formulations or polynomial graph algorithms.
   **Further partial progress (§14, 2026-10-15):** the antiparallel-bridge family
   (a positively-realizable cross-connection of two cycles) has a genuinely
   *coupled* four-variable criterion (`bridge_nonrigid_iff`) that is **not** of
   the bouquet form, and is rigid **iff** all multiplicities are `1`
   (`bridgeA_rigid_iff_trivial`); so the bridge topology yields no new rigid
   repetitive supports. The general complexity and graph-theoretic
   characterization remain **OPEN**. **Further partial progress (§15,
   2026-10-16):** the bouquet family is *exactly* the unbounded coin /
   numerical-semigroup problem (`targetCycle_nonrigid_iff_coin`), and because
   explicit support graphs give **unary** lengths the family is decidable in
   **polynomial time** via the Apéry-set algorithm. This is a positive §8.2
   upper bound and refutes the naive NP-hardness reading; the uniform-in-support
   complexity and any general polynomial min-cut form remain **OPEN**.
   **Further partial progress (§17, 2026-10-17):** the length-3 antiparallel
   bridge has an exact four-variable criterion and classification, and it
   *refutes* the bridge pattern (rigid **iff** all multiplicities `1`): the
   instance `(m₁, m₂, f) = (1, 1, 2)` is a rigid repetitive support.
   **Further partial progress (§18, 2026-10-17):** the *general* `p,q`
   long-bridge criterion (arbitrary cycle lengths `p, q ≥ 2`) is proved and
    kernel-checked; it is genuinely `p,q`-dependent — `(p,q,m₁,m₂,f) = (3,4,2,1,1)`
    is a rigid repetitive instance, so `m₁ ≥ 2` alone does not force
     non-rigidity. **Further partial progress (§19, 2026-10-18):** coupling begins
     at cycle rank `3`; every rank-`≤ 2` support satisfies the bouquet criterion,
     and the **double-theta graph** (rank `3`) is the minimal genuinely coupled
     support **among realizable supports** (the abstract `3`-vertex
     `K3`-minus-an-arc is smaller and coupled but not realizable), with an exact
     four-variable criterion coupled by an extra
     hub-balance equation, a rigid repetitive instance `(2,1,2,1)`, and a
     kernel-checked refutation of the coupling-dropped relaxation.
     **Further partial progress (§20, 2026-10-20):** the **multi-hub family**
     (`k` `u → v` paths and `l` `v → u` paths of arbitrary lengths) has
     **unbounded cycle rank** `k + l - 1` and an exact **two-equation** criterion
     (`multiHub_nonrigid_iff`); because the path lengths are unary, deciding it is
     a nonnegative-integer **uniqueness** problem solvable by a polynomial DP,
     giving a §8.2 upper bound for this unbounded-rank family. It has a rigid
     repetitive instance and its coupling-dropped relaxation is not sound. The
      *general* support topology and a min-cut/max-flow closed form for it remain
      **OPEN** — no criterion of a single-cut / independent-per-path form can be
      exact (the committed counterexample `multiHub_relaxed_not_sound`).
      **Further partial progress (§21, 2026-10-21):** the **triangular multi-hub
      family** (three hubs in a directed cycle, `a + b + c - 2` paths, unbounded
      cycle rank) is a genuinely *three-hub* topology with a **three-equation**
      criterion (`triHub_nonrigid_iff`); it too is decidable by a polynomial DP
      (unary lengths), has a rigid repetitive instance, and its coupling-dropped
      relaxation is not sound (`triHub_relaxed_not_sound`). The general support
      topology and a min-cut/max-flow closed form for it remain **OPEN**.
    [open; bouquet case reduced and shown poly-time, §13/§15;
    bridge case classified, §14; length-3 bridge classified and bridge pattern
     refuted, §17; general `p,q` long bridge classified, §18; coupling begins at
     rank `3`, double theta minimal among realizable supports, §19; multi-hub
     unbounded-rank family with a two-equation polynomial criterion, §20;
     triangular three-hub unbounded-rank family with a three-equation polynomial
     criterion, §21]
2. **The exact complexity** of the exact criterion (§7). **Partial (§15,
    2026-10-16):** the bouquet family (hence the target-cycle family) is in `P`
    via the Apéry-set / residue-graph shortest-path algorithm. **Partial (§20,
    2026-10-20):** the multi-hub family (unbounded cycle rank) is in `P` via a
     two-equation nonnegative-integer-uniqueness DP (unary path lengths); the
     uniform-in-support case (arbitrary topology) is **OPEN**. **Partial (§21,
     2026-10-21):** the triangular three-hub family (unbounded cycle rank) is in
     `P` via a three-equation nonnegative-integer-uniqueness DP (unary path
     lengths); the uniform-in-support case remains **OPEN**. [open]
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
| §14 bridge exact criterion (`bridge_nonrigid_iff`: `∃ (a,c,p,q) ≠ 0, 2a+2c+p+q = 0` + coupled box) | mathematical proof + kernel-checked (`AssemblyP1/RigidityBridge.lean`) |
| §14 bridge classification (`bridgeA_rigid_iff_trivial`: rigid iff `m1 = m2 = f = 1`) | mathematical proof + kernel-checked |
| §14 bridge non-rigidity witnesses (`dM1`, `dM2`, `dF`) | kernel-checked |
| §14 bridge cross-check vs brute force (`scripts/verify_257_bridge.py`: 880 bridges, 0 mismatches) | verified computation, exhaustive in scope |
| §15 target-cycle coin reduction (`targetCycle_nonrigid_iff_coin`: non-rigid iff `∃ y ≥ 0, ∑ a_i y_i = t`) | mathematical proof + kernel-checked (`AssemblyP1/RigidityTargetCycle.lean`) |
| §15 rigid dual (`targetCycle_rigid_iff_not_coin`) | mathematical proof + kernel-checked |
| §15 target-cycle worked instances (`coin_nonrigid_23_5`, `coin_rigid_23_1`, `coin_rigid_33_2`) | kernel-checked |
| §15 Apéry-set polynomial representability algorithm (bouquet rigidity ∈ P; explicit/unary lengths) | mathematical proof + verified computation (`scripts/verify_257_target_cycle.py`) |
| §15 target-cycle cross-check vs brute force (`scripts/verify_257_target_cycle.py`: 435 bouquets, 10320 Apéry cases, 0 mismatches) | verified computation, exhaustive in scope |
| §17 length-3 bridge exact criterion (`length3Bridge_nonrigid_iff`: `∃ (a,c,u,w) ≠ 0, 3a+3c+u+w = 0` + coupled box) | mathematical proof + kernel-checked (`AssemblyP1/RigidityLength3Bridge.lean`) |
| §17 length-3 bridge classification (`length3Bridge_rigid_iff`: rigid iff `m₁ = 1 ∧ m₂ = 1 ∧ f ≤ 2`) | mathematical proof + kernel-checked |
| §17 length-3 bridge rigid repetitive instance `length3Bridge_rigid_repetitive` (`f = 2`) — refutes "bridge rigid iff all mult `1`" | kernel-checked |
| §17 length-3 bridge non-rigidity witnesses (`length3Bridge_nonrigid_m1/m2/f`) | kernel-checked |
| §17 length-3 bridge cross-check vs brute force (`scripts/verify_257_length3_bridge.py`: 255 bridges, 0 mismatches) | verified computation, exhaustive in scope |
| §18 general `p,q` long-bridge criterion (`generalBridge_nonrigid_iff`: `∃ (a,c,u,w) ≠ 0, p·a+q·c+(q-p+1)·u+(p-q+1)·w = 0` + six coupled boxes) | mathematical proof + kernel-checked (`AssemblyP1/RigidityGeneralBridge.lean`) |
| §18 general `p,q` non-rigidity witnesses (`generalBridge_nonrigid_m2_large` `(q,-p,0,0)`, `generalBridge_nonrigid_m1_large` `(-q,p,0,0)`, `generalBridge_nonrigid_eq_m1/m2`, `generalBridge_nonrigid_q3_f` `(1,0,-1,-2)`) | kernel-checked |
| §18 `p,q`-dependent rigid repetitive instance `generalBridge_rigid_repetitive` (`(p,q,m₁,m₂,f) = (3,4,2,1,1)`) — `m₁ ≥ 2` does not force non-rigidity | kernel-checked |
| §18 general `p,q` long-bridge cross-check vs brute force (`scripts/verify_257_general_bridge.py`: 448 bridges, 0 mismatches) | verified computation, exhaustive in scope |
| §19 rank `≤ 2` supports satisfy the bouquet criterion (shared path value is a sum; shared box redundant) | mathematical proof |
| §19 double-theta exact criterion (`doubleTheta_nonrigid_iff`: `∃ (α₁,α₂,β₁,β₂) ≠ 0, α₁+α₂ = β₁+β₂, α₁+2α₂+β₁+2β₂ = 0` + four boxes) | mathematical proof + kernel-checked (`AssemblyP1/RigidityDoubleTheta.lean`) |
| §19 double-theta non-rigidity witness `doubleTheta_nonrigid_witness` (`(1,2,1,2)`, `(2,-1,2,-1)`) | kernel-checked |
| §19 double-theta rigid repetitive instance `doubleTheta_rigid_repetitive` (`(2,1,2,1)`) | kernel-checked |
| §19 coupling-dropped relaxation not sound `relaxed_not_sound` (`(2,1,2,1)` relaxed-satisfied yet rigid) | kernel-checked |
| §19 double-theta cross-check vs brute force (`scripts/verify_257_double_theta.py`: 33 double thetas, 0 mismatches) | verified computation, exhaustive in scope |
| §20 multi-hub exact criterion (`multiHub_nonrigid_iff`: `∃ α ≠ 0`, `∑_{u→v} α = ∑_{v→u} α`, `∑ length·α = 0`, `α ≥ 1-m`) for arbitrary `k, l` and lengths — unbounded cycle rank | mathematical proof + kernel-checked (`AssemblyP1/RigidityMultiHub.lean`) |
| §20 multi-hub path constancy (`phi_of_balanced` / `balanced_of_phi`) | kernel-checked |
| §20 all multiplicities `1` is rigid (`multiHub_rigid_all_one`) | kernel-checked |
| §20 rigid repetitive instance `multiHub_rigid_repetitive_2` (`p2`/`m2`: lengths `(1,3)`, multiplicities `(2,1)`) | kernel-checked |
| §20 coupling-dropped relaxation not sound `multiHub_relaxed_not_sound` (`p2`/`m2` relaxed-satisfied yet rigid) | kernel-checked |
| §20 multi-hub cross-check vs brute force + polynomial DP (`scripts/verify_257_multi_hub.py`: 78 multi-hub supports, 0 mismatches) | verified computation, exhaustive in scope |
| §21 triangular multi-hub exact criterion (`triHub_nonrigid_iff`: `∃ (α,β,γ) ≠ 0`, `∑_{u→v} α = ∑_{v→w} β = ∑_{w→u} γ`, zero weighted mass, boxes) for arbitrary `a, b, c` and lengths — three-hub, unbounded cycle rank | mathematical proof + kernel-checked (`AssemblyP1/RigidityTriHub.lean`) |
| §21 triangular path constancy (`phi_of_balanced` / `balanced_of_phi`) | kernel-checked |
| §21 all multiplicities `1` is rigid (`triHub_rigid_all_one`) | kernel-checked |
| §21 rigid repetitive instance `triHub_rigid_repetitive` (lengths `(1,3)`, multiplicities `(2,1)` each direction) | kernel-checked |
| §21 coupling-dropped relaxation not sound `triHub_relaxed_not_sound` | kernel-checked |
| §21 triangular cross-check vs brute force + polynomial DP + mutation-red (`scripts/verify_257_tri_hub.py`: 153 triangular supports, 0 mismatches) | verified computation, exhaustive in scope |
| §22 directed-2-cycle sufficiency, parametric (`cycle2_rigid`, `cycle2_balanced_const`) | mathematical proof + kernel-checked (`AssemblyP1/RigiditySimpleCycle.lean`) |
| §22 `ATATAT` parametric rigidity (`atatat_of_cycle2`: rigid at every uniform `k`) | kernel-checked |
| §22 AATT boundary rigid non-cycle (`aatt_rigid`, `aatt_search_space`) | kernel-checked (`by decide`) |
| §22 cross-check vs brute force + mutation-red (`scripts/verify_257_simple_cycle.py`: 20 directed cycles + AATT rigid/mutated, 0 mismatches) | verified computation, exhaustive in scope |

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
that this direct fractional (LP) relaxation is *not* exact.

### 13.1 Definition

A **bouquet** is an abstract strongly connected directed graph consisting of
k cycles C_i through one common vertex, otherwise vertex-disjoint.
It generalizes the figure-eight. Not every choice of cycle lengths and
alphabet is automatically realizable as a de Bruijn/read-support graph;
the concrete DNA realization in section 13.5 is checked separately.

Let len_i >= 1 be the cycle lengths, and let a positive circulation A
be constant on each cycle with multiplicity mult_i >= 1, giving slack
s_i = mult_i - 1. When such a bouquet is realizable as a read-support
graph, the circulation represents a circular walk traversing C_i
exactly mult_i times. The algebraic criterion applies to abstract
bouquets without a realizability assumption.

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

### 13.4 Direct rational relaxation is not exact

Replacing the integer vector in the bouquet criterion by a rational vector
produces a direct linear relaxation. For cycle lengths (2,3,3) and
multiplicities (2,1,1), the rational vector (-1,0,2/3) is nonzero,
has weighted sum zero, and respects all lower bounds.

The integer system, however, has only x=0: its equation is
2*x1 + 3*(x2+x3) = 0, with x1 >= -1 and x2,x3 >= 0.
If x1=0, both other coordinates vanish; if x1=-1, the equation
would require 3*(x2+x3)=2, impossible over the integers.
Positive x1 cannot cancel nonnegative x2,x3. This proves a rigid
integer instance whose *direct* rational relaxation reports a witness,
kernel-checked by len233_mult211_real_integer_gap.

This example does not exclude other exact LP/extended formulations,
integral network-flow formulations, or polynomial-time graph algorithms.

### 13.5 Complexity and realizability caveats

The bouquet criterion is a bounded linear Diophantine feasibility
problem. With lengths encoded in binary it resembles numerical-semigroup
membership: one cycle of length t with slack 1 and other cycles of
length a_i with zero slack admits a nonzero integer perturbation exactly
when t is a nonnegative combination of the a_i. But an *explicit*
bouquet graph has size proportional to the sum of cycle lengths, not
their binary bit lengths. Therefore this observation by itself is **not**
an NP-hardness proof for rigidity on explicitly represented read graphs,
nor does it rule out a polynomial min-cut/max-flow characterization.
Those complexity questions remain OPEN.

Abstract bouquets also need not be realizable as de Bruijn read-support
graphs over a fixed alphabet. One concrete realization is checked in
AssemblyP1/RigidityBouquetGenomeWitness.lean: the circular DNA genome
ACACGACTAC with L=3 has the three cycles (2,3,3), multiplicities
(2,1,1), at shared (L-1)-mer AC. The Lean regression checks all cyclic
reads, their multiplicities, and the source/target 2-mers; the abstract
integer rigidity theorem is a separate kernel-checked result.

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

---

## 14. The antiparallel bridge: a coupled criterion beyond the bouquet (§8.1 progress)

This section advances open item §8.1 past the **bouquet** family of §13, with a
topology whose circulation space is genuinely *coupled* rather than
constant-on-cycles.

### 14.1 Why a single extra arc is not enough

Suppose the figure-eight (two cycles `C1, C2` through a hub `v`) is given one
extra arc from an interior vertex `u1` of `C1` to an interior vertex `u2` of
`C2`. At `u1` there is exactly one incoming `C1`-edge, one outgoing `C1`-edge,
and the new arc. If `A` is a *positive* circulation (every support edge carries
`≥ 1`), balance at `u1` is `A(C1 in) + A(arc in) = A(C1 out) + A(arc out)`; with
`A(C1 in) = A(C1 out)` this forces the arc value to `0`, contradicting
positivity. The same holds for any single arc incident to the interior of a
cycle, and for an arc between two interior vertices. Hence the **minimal
positively-realizable cross-connection between two cycles is an antiparallel arc
pair**.

### 14.2 The bridge graph

Take the hub `v`, the two `2`-cycles `v → x → v` and `v → y → v`, and the
antiparallel pair `x → y`, `y → x`. This is the *bridge graph*; it is an abstract
oriented support graph (a switch `x`, `y` of in-degree and out-degree `2`). Its
six arcs are

```
0: v→x   1: x→v   2: v→y   3: y→v   4: x→y   5: y→x
```

with multiplicities `A = (m1, m1, m2, m2, f, f)`, `m1, m2, f ≥ 1`, total mass
`G = 2(m1 + m2 + f)`.

Unlike a bouquet, a circulation is **not** constant on the cycles: the bridge
couples the two cycle values. Balance at `x` and `y` gives the two independent
equations

```
δ1 + δ4 = δ0 + δ5 ,      δ3 + δ5 = δ2 + δ4
```

(the hub balance `δ0 + δ2 = δ1 + δ3` is a consequence), so every circulation is

```
δ = φ(a, c, p, q) = ![a, a + q - p, c, c + p - q, p, q]
```

for `a = δ0`, `c = δ2`, `p = δ4`, `q = δ5`, with total mass
`∑ δ = 2a + 2c + p + q`. This parameterization is kernel-checked
(`AssemblyP1.RigidityBridge.phi_of_balanced`, `phi_balancedB`, `phi_sum`).

### 14.3 Exact criterion

**Theorem 7 (bridge criterion).** `A` is **not** rigid **iff** there are
integers `a, c, p, q`, not all zero, with

```
2a + 2c + p + q = 0                        (zero total mass)
a ≥ 1 - m1 ,   a + q - p ≥ 1 - m1          (x-cycle box)
c ≥ 1 - m2 ,   c + p - q ≥ 1 - m2          (y-cycle box)
p ≥ 1 - f ,    q ≥ 1 - f                   (bridge box)
```

_Proof._ Immediate from Theorem 1 together with the parameterization §14.2: the
box `δ ≥ 1 - A` becomes the six inequalities above, and `δ ≠ 0` becomes
`(a, c, p, q) ≠ 0`. ∎

This is kernel-checked as `AssemblyP1.RigidityBridge.bridge_nonrigid_iff`. It is
genuinely *coupled*: the box on arc `1 = x→v` involves `a + q - p`, and the box
on arc `3 = y→v` involves `c + p - q`, so it is **not** a bouquet criterion
(which has independent per-cycle bounds). The bouquet criterion of §13 is
recovered only in the degenerate shared-cycle limit, not here.

### 14.4 Rigidity classification: the bridge is rigid only when trivial

**Corollary (bridge is rigid iff all multiplicities are 1).**
`bridgeA_rigid_iff_trivial`: for `m1, m2, f ≥ 1`, `A` is rigid **iff**
`m1 = m2 = f = 1`. In every other case an explicit non-rigidity witness is
kernel-checked:

* `m1 ≥ 2`: `δ = (-1, -1, 0, 0, 1, 1)` (`dM1`);
* `m2 ≥ 2`: `δ = (0, 0, -1, -1, 1, 1)` (`dM2`);
* `f ≥ 2`:  `δ = (0, 0, 1, 1, -1, -1)` (`dF`).

For `m1 = m2 = f = 1` every box constraint is `δ_e ≥ 0`, and zero total mass
forces `δ = 0`, so the instance is rigid (trivially). Thus the **minimal positive
cross-connection between two cycles destroys rigidity except in the all-ones
degenerate case** — a no-go for the tempting hypothesis that adding a bridge
yields new *rigid* repetitive supports.

### 14.5 Cross-check

`scripts/verify_257_bridge.py` recomputes rigidity from scratch by enumerating
**all** positive integer circulations of total `G` on the bridge graph and
compares with the four-variable criterion of §14.3 and with the classification
of §14.4, over an exhaustive scope (`1 ≤ m1, m2, f ≤ 10`, `G = 2(m1+m2+f) ≤ 44`:
**880** bridges, **0** mismatches), and re-derives the three witnesses.
[verified computation, exhaustive in scope]

### 14.6 Epistemic status

Theorem 7, the classification, and the three witnesses are kernel-checked with
only `[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityBridgeAudit`); no `sorry`/`admit`/`axiom`/`native_decide`.
The bridge is an **abstract** support graph; realizability of this exact shape as
a de Bruijn read-support is **not** claimed (two distinct `2`-cycles through one
hub cannot coexist in an order-`(L-1)` de Bruijn graph). The residual — a
*polynomial* min-cut/max-flow closed form for general supports, or a proof that
none exists — remains **OPEN** (§8.1/§8.2).

---

## 15. The target-cycle bouquet: an exact coin / numerical-semigroup reduction and a §8.2 polynomial upper bound

This section advances open items **§8.1** and **§8.2** by isolating the exact
sub-problem encoded by the bouquet family and by giving a genuine
polynomial-time decision procedure for it. It builds on — and does not redo —
the merged bouquet criterion `bouquet_nonrigid_iff` of §13.

### 15.1 Definition: the target-cycle bouquet

Fix coin cycle lengths `a 0, …, a (n-1) ≥ 1` and a **target** cycle length
`t ≥ 1`. The *target-cycle bouquet* is the bouquet of §13 with `n + 1` cycles
through a common vertex:

* the `n` **coin** cycles, each traversed **once** (`mult_i = 1`);
* the **target** cycle, traversed **twice** (`mult_last = 2`).

Its circulation space is `ℤ^{n+1}` and the exact criterion §13.3 reads: `A` is
not rigid iff there is a nonzero integer vector `x` with
`∑_i len_i x_i = 0` and `x_i ≥ 1 - mult_i`. For the target-cycle bouquet the box
is `x_i ≥ 0` on each coin cycle and `x_last ≥ -1` on the target, and the
zero-sum equation is `∑_i a_i x_i + t·x_last = 0`.

### 15.2 The reduction

**Theorem 8 (target-cycle / coin reduction).** The target-cycle bouquet is
**not** rigid **iff** `t` is a nonnegative integer combination of the coin
lengths `a_i`:

```
not rigid  ⟺  ∃ y : ℕ^n,  ∑_i a_i y_i = t.
```

Equivalently, the bouquet is **rigid** iff `t ∉ ⟨a_0, …, a_{n-1}⟩`, the
numerical semigroup generated by the coin lengths.

_Proof._ Let `x` be a witness of the bouquet criterion. Since `a_i > 0` and
`x_i ≥ 0`, the coin part `S := ∑_i a_i x_i` is `≥ 0`. The zero-sum equation is
`S + t·x_last = 0`, so `t·x_last = -S ≤ 0`; with `t > 0` this gives
`x_last ≤ 0`, and the target box `x_last ≥ -1` then gives `x_last ∈ {-1, 0}`.
If `x_last = 0`, then `S = 0` and every term `a_i x_i ≥ 0` vanishes, so
`x_i = 0` for all `i` (as `a_i ≠ 0`) and `x = 0`, contradicting `x ≠ 0`. Hence
`x_last = -1`, and then `S = t` with all `x_i ≥ 0`: `y_i := x_i` is the required
nonnegative combination. Conversely, given `y ≥ 0` with `∑ a_i y_i = t`, set
`x_i := y_i` on the coins and `x_last := -1`; then `∑ len_i x_i = t - t = 0`,
`x_i ≥ 0 = 1 - 1`, `x_last = -1 = 1 - 2`, and `x ≠ 0`, so the criterion yields
non-rigidity. ∎

This is kernel-checked as
`AssemblyP1.RigidityTargetCycle.targetCycle_nonrigid_iff_coin` (and its rigid
dual `targetCycle_rigid_iff_not_coin`). The whole "target + coins" family is
therefore *precisely* the **unbounded coin / change-making problem**. Worked
instances are kernel-checked: `coin_nonrigid_23_5` (coins `(2,3)`, target `5`
representable), `coin_rigid_23_1` (target `1` not representable), and
`coin_rigid_33_2` (coins `(3,3)`, target `2`, the length-`(2,3,3)`
multiplicity-`(2,1,1)` real/integer-gap bouquet of §13 re-read with the
length-`2` cycle as the target; that bouquet is genome-realizable, see
`AssemblyP1/RigidityBouquetGenomeWitness.lean`).

### 15.3 §8.2: the target-cycle bouquet is decidable in polynomial time

The coin problem with **binary** denominations is NP-complete (Lueker 1975,
"Two NP-complete problems in nonnegative integer programming"). It is tempting
to read §13.5 and Theorem 8 as an NP-hardness proof for rigidity. **That reading
is wrong for explicit support graphs**, and recording the exact reason is the
content of this subsection.

An *explicit* support graph has one edge per unit of cycle length: a cycle of
length `a` is `a` distinct edges. Hence the coin lengths `a_i` are encoded in
**unary** (`a_i ≤ M`, the edge bound, is part of the graph size), while the
multiplicities (and the target total) may be binary. For unary denominations,
representability is decidable in polynomial time by the **Apéry set** /
**residue-graph shortest-path** algorithm:

> Let `m := min_i a_i`. In the directed graph on the residue classes
> `ℤ / m`, put an edge `r → (r + a_i) mod m` of weight `a_i` for every coin
> `a_i`. Compute the shortest distance `dist(r)` from `0`. Then `dist(r)` is the
> smallest representable number `≡ r (mod m)`, and
> ```
> t  is representable  ⟺  t ≥ dist(t mod m).
> ```

_Proof._ (`⇐`) `t = dist(t mod m) + k·m` with `k = (t - dist(t mod m))/m ≥ 0`,
and both `dist(t mod m)` (a path sum of denominations) and `m` are representable,
so `t` is. (`⇒`) A representation `t = ∑ a_i y_i` reduces mod `m` to a walk
`0 → t mod m` of total weight `t`, so `dist(t mod m) ≤ t`. ∎

The algorithm costs `O(m · n)` arithmetic operations (`m ≤ M`, `n ≤ |E|`), with
numbers of `O(log t)` bits: **polynomial in the explicit graph size and the bit
length of the multiplicities**. Therefore the target-cycle bouquet — and, by the
same argument, the entire bouquet family — is decidable in polynomial time, and
the naive "the bouquet encodes an NP-hard problem" reading is **refuted**. This
is a genuine §8.2 *upper* bound for a nontrivial family (a positive complexity
result), and it explains why the earlier §13.5 caution was right.

**What this does *not* settle.** The uniform-in-support complexity of the exact
criterion (Theorem 1) for arbitrary support graphs remains **OPEN** (§8.2): the
reduction covers bouquets, not general supports, and the general circulation
lattice `L_0 = ker[M; 1ᵀ]` is not a single equation. The existence of a
polynomial min-cut / max-flow closed form (§8.1) is likewise **OPEN**; §15 shows
only that the bouquet obstruction is *not* the reason it would fail.

**Remark (general supports, fixed cycle rank).** For a *fixed* cycle rank
`r = |E| - |V| + c - 1 = rank L_0`, rigidity **is** decidable in polynomial time
in the explicit graph size and `log G`. Choose a lattice basis `b_1, …, b_r` of
`L_0` (its entries are bounded by the largest subdeterminant of `[M; 1ᵀ]`, which
is `≤ |E|` because `M` is totally unimodular and the single all-ones row expands
into `≤ |E|` unit minors). Then non-rigidity is the integer feasibility of the
system `∑_j z_j b_j ≥ -s` in `r` integer variables; by Lenstra's theorem
(integer programming in fixed dimension is polynomial), this is decidable in
polynomial time for each fixed `r`. So the hardness, if any, is concentrated in
the *uniform-in-`r`* regime, which stays **OPEN**. This is an external cited
result (Lenstra 1983); it is not kernel-checked here and is recorded only to
sharpen §8.2.

### 15.4 Cross-check

`scripts/verify_257_target_cycle.py` is a self-contained, exact, deterministic
cross-check with four parts, exiting non-zero on any failure:

* `bruteforce`: for every target-cycle bouquet in an exhaustive scope
  (`k ≤ 3` coin cycles, lengths `≤ 4`, target `≤ 8`, total support `≤ 12` edges,
  `G ≤ 20`: **435** bouquets), compute rigidity from scratch by enumerating
  **all** positive integer circulations of total `G` on the actual support graph
  and compare with coin representability — **0** mismatches;
* `apery`: the Apéry-set algorithm agrees with a bounded brute-force
  representability oracle on **10320** small cases (**0** mismatches) and is
  exercised on binary-sized targets (`10^9`, `10^9 + 1`, `12345678901234567890`)
  and on the `(6,9,20)` Frobenius instance (Frobenius number `43`);
* `instances`: re-derives `coin_nonrigid_23_5`, `coin_rigid_23_1`,
  `coin_rigid_33_2`;
* `gap`: re-derives the §13 `(2,3,3)`/`(2,1,1)` real/integer-gap bouquet and
  its target-cycle re-reading.

[verified computation, exhaustive in scope]

### 15.5 Epistemic status

Theorem 8 and its three worked instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityTargetCycleAudit`); no `sorry`/`admit`/`axiom`/
`native_decide`. The polynomial Apéry-set algorithm (§15.3) is a standard
numerical-semigroup result, proved above and re-verified by
`scripts/verify_257_target_cycle.py`; the NP-completeness of the *binary* coin
problem is an external cited result (Lueker 1975), used only to explain why the
unary/explicit distinction matters. The uniform-in-support complexity (§8.2) and
the general min-cut/max-flow closed form (§8.1) remain **OPEN**.


---

## 16. Why the direct rational/LP relaxation is insufficient

The added kernel-checked module `AssemblyP1/RigidityNoGo.lean` proves
`coin_bouquet_real_nonrigid`: for **every** coin bouquet with at least one
coin cycle, the direct rational relaxation of the bouquet's integer-kernel
criterion admits a nonzero witness, namely `x₀ = -1` at the target cycle,
`x₁ = t / a₁` at the first coin cycle, and zero elsewhere.
For example, the coin system `{2,3}` with target `1` is rigid over integer
circulations (the target is not a nonnegative combination of the coins) yet
its direct rational relaxation accepts the witness. Thus **feasibility of that
specific LP relaxation cannot characterize rigidity**, even on the coin-bouquet
family. This says **nothing against** more powerful polynomial procedures
such as the Apéry algorithm of §15; general-support complexity remains open.

The module also independently kernel-checks the §15 coin-membership iff in an
opposite indexing convention (`coin_bouquet_nonrigid_iff`) and two concrete
instances. The independent exact-arithmetic
`scripts/verify_257_coin_no_go.py` checks 786 small bouquets, finding no
integer-criterion mismatches and confirming the LP witness in all cases,
including 135 rigid examples. The `RigidityNoGoAudit` and `AxiomAudit257`
files audit the proof's standard-axiom dependencies. This is deliberately a
**bounded direct-LP no-go**, not a binary-input NP-hardness or general
non-existence-of-polynomial-algorithm theorem.

---

## 17. The length-3 antiparallel bridge: the bridge classification does not generalise (§8.1 progress)

This section advances open item **§8.1** past both the *bouquet* family (§13)
and the *antiparallel bridge* (§14), by replacing each `2`-cycle of the bridge
by a `3`-cycle. It builds on — and does not redo — the merged bridge criterion
`bridge_nonrigid_iff` and classification `bridgeA_rigid_iff_trivial` of §14.

### 17.1 The topology

The merged bridge (§14) is the complete digraph `K₃*`: two `2`-cycles through a
hub `v`, joined by an antiparallel arc pair between their interior vertices. Its
classification says it is rigid **iff** every edge has multiplicity `1`; every
repetitive bridge is non-rigid. The *length-3 antiparallel bridge* keeps the
same shape but lengthens each cycle:

```
C1 : v → x → a₂ → v          C2 : v → y → b₂ → v
bridge : x → y , y → x
```

on five vertices `v, x, a₂, y, b₂` and eight arcs. It has the same cycle rank
`4` as the merged bridge but is a genuinely different topology, and it is **not**
covered by the merged `2`-cycle classification.

### 17.2 The four-variable exact criterion

At the interior vertices `a₂`, `b₂` balance forces the two consecutive `C1` (resp.
`C2`) arcs to be equal; the balance at `x` and `y` then couples the two cycle
values with the bridge values. Every circulation is determined by four integers
`(a, c, u, w)` — the values of `v → x`, `v → y`, `x → y`, `y → x` — and equals

```
δ = φ(a, c, u, w) = ![a, a-u+w, a-u+w, c, c-w+u, c-w+u, u, w].
```

The total mass is `∑ δ = 3a + 3c + u + w` (the coefficients are `3, 3, 1, 1`,
not the bridge's `2, 2, 1, 1`). **Theorem 9 (length-3 bridge criterion).** With
multiplicities `m₁, m₂, f ≥ 1` (`m₁` on the `C1` arcs, `m₂` on the `C2` arcs,
`f` on the bridge arcs), the base circulation `A` is **not** rigid **iff** there
are integers `a, c, u, w`, not all zero, with

```
3a + 3c + u + w = 0,                       (zero total mass)
a ≥ 1 - m₁,   a - u + w ≥ 1 - m₁,          (C1 box)
c ≥ 1 - m₂,   c - w + u ≥ 1 - m₂,          (C2 box)
u ≥ 1 - f,    w ≥ 1 - f.                   (bridge box)
```

_Proof._ Immediate from Theorem 1 together with the parameterisation above: the
box `δ ≥ 1 - A` becomes the six inequalities, and `δ ≠ 0` becomes
`(a, c, u, w) ≠ 0`. ∎ This is kernel-checked as
`AssemblyP1.RigidityLength3Bridge.length3Bridge_nonrigid_iff`. The box
genuinely couples `a` with `w - u` and `c` with `u - w`.

### 17.3 Classification and the refutation of the bridge pattern

**Theorem 10 (length-3 bridge classification).** For `m₁, m₂, f ≥ 1`, the base
circulation is rigid **iff** `m₁ = 1 ∧ m₂ = 1 ∧ f ≤ 2`; kernel-checked as
`length3Bridge_rigid_iff`. The non-rigidity witnesses are explicit:

* `m₁ ≥ 2`: `(a, c, u, w) = (-1, 1, 0, 0)`, i.e. `δ = (-1,-1,-1,1,1,1,0,0)`
  (`length3Bridge_nonrigid_m1`);
* `m₂ ≥ 2`: `(a, c, u, w) = (1, -1, 0, 0)`, i.e. `δ = (1,1,1,-1,-1,-1,0,0)`
  (`length3Bridge_nonrigid_m2`);
* `m₁ = m₂ = 1, f ≥ 3`: `(a, c, u, w) = (1, 0, -1, -2)`, i.e.
  `δ = (1,0,0,0,1,1,-1,-2)` (`length3Bridge_nonrigid_f`).

The two remaining cases are rigid: `m₁ = m₂ = f = 1` (every box is `δ ≥ 0`, so
zero total mass forces `δ = 0`), and — the point of this section —
`m₁ = m₂ = 1, f = 2`, kernel-checked as `length3Bridge_rigid_repetitive`.

**Consequence (failed simpler hypothesis, committed witness).** The natural
generalisation of the merged bridge classification — *"an antiparallel bridge is
rigid iff all multiplicities are `1`"* — is **FALSE**. The length-3 bridge with
`(m₁, m₂, f) = (1, 1, 2)` traverses both bridge arcs **twice** and is
nevertheless **rigid**. So "rigid iff all multiplicities `1`" is specific to the
`2`-cycle bridge; longer cycles can absorb repetitions without losing rigidity.
This is a rigid *repetitive* support beyond the bouquet (`len24_mult21_rigid`)
and bridge families.

### 17.4 Cross-check

`scripts/verify_257_length3_bridge.py` is self-contained, exact, and
deterministic. It recomputes rigidity from scratch by enumerating **all**
positive integer circulations of total `G` on the eight-arc graph and compares
with (i) the four-variable criterion and (ii) the classification
`m₁ = 1 ∧ m₂ = 1 ∧ f ≤ 2`, over an exhaustive scope (`1 ≤ m₁, m₂ ≤ 6`,
`1 ≤ f ≤ 8`, `G ≤ 40`: **255** length-3 bridges, **0** mismatches), and
re-derives all four worked instances. [verified computation, exhaustive in
scope]

### 17.5 Epistemic status

Theorems 9–10 and the four instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityLength3BridgeAudit`, and `AxiomAudit257.lean`); no
`sorry`/`admit`/`axiom`/`native_decide`. The topology is an *abstract* oriented
support graph, as for the merged bridge; realizability as a de Bruijn
read-support is not claimed. The residual — a *polynomial* min-cut/max-flow
closed form for general supports, or a proof that none exists — remains
**OPEN** (§8.1/§8.2). The general `p, q` long-bridge criterion (arbitrary cycle
lengths) is **resolved** in §18 below (kernel-checked `generalBridge_nonrigid_iff`).


## 18. The general `p, q` long bridge: an exact criterion beyond the length-3 case (§8.1 progress)

This section advances open item **§8.1** past the length-3 antiparallel bridge
(§17) by allowing the two cycles to have arbitrary lengths `p, q ≥ 2`. It builds
on — and does not redo — the merged `2`-cycle bridge criterion
`bridge_nonrigid_iff` (§14) and the length-3 criterion `length3Bridge_nonrigid_iff`
(§17); both are special cases. [mathematical proof + kernel-checked]

### 18.1 The topology

The *general `p,q` long bridge* is the hub `v` with a `p`-cycle and a `q`-cycle
through it, joined by an antiparallel arc pair between their interior vertices:

```
C1 : v → x → a₂ → … → a_{p-1} → v      (p arcs)
C2 : v → y → b₂ → … → b_{q-1} → v      (q arcs)
bridge : x → y , y → x                 (antiparallel arc pair)
```

on `1 + (p-1) + (q-1)` vertices and `p + q + 2` arcs. The base circulation `A`
has multiplicity `m₁` on every `C1` arc, `m₂` on every `C2` arc, and `f` on each
bridge arc; its total mass is `G = p·m₁ + q·m₂ + 2·f`. At `p = q = 2` this is
the merged bridge; at `p = q = 3` the length-3 bridge.

### 18.2 The four-variable exact criterion

Balance at the interior vertices `a₂, …, a_{p-1}` (resp. `b₂, …, b_{q-1}`)
forces the consecutive `C1` (resp. `C2`) arc values to be constant; the balance
at `x` and `y` couples the two cycle values with the bridge values. Hence every
integral circulation is determined by four integers `(a, c, u, w)` — the values
of `v → x`, `v → y`, `x → y`, `y → x` — and equals

```
φ(a, c, u, w) = ( a, (a-u+w)^{× (p-1)}, c, (c-w+u)^{× (q-1)}, u, w )
```

(kernel-checked as `AssemblyP1.RigidityGeneralBridge.phi_of_balanced`). Its total
mass is

```
Σ φ(a, c, u, w) = p·a + q·c + (q-p+1)·u + (p-q+1)·w
```

(kernel-checked `phi_sum`). The coefficients `(p, q, q-p+1, p-q+1)` specialise to
`(2,2,1,1)` at `p = q = 2` and `(3,3,1,1)` at `p = q = 3`, recovering the merged
criteria.

**Theorem 11 (general `p,q` long-bridge criterion).** For `p, q ≥ 2` and
`m₁, m₂, f ≥ 1`, the base circulation `A` is non-rigid **iff** there are integers
`a, c, u, w`, not all zero, with

```
p·a + q·c + (q-p+1)·u + (p-q+1)·w = 0            (zero total mass)
a ≥ 1-m₁,  a-u+w ≥ 1-m₁,                          (C1 box)
c ≥ 1-m₂,  c-w+u ≥ 1-m₂,                          (C2 box)
u ≥ 1-f,   w ≥ 1-f.                               (bridge box)
```

This is kernel-checked as
`AssemblyP1.RigidityGeneralBridge.generalBridge_nonrigid_iff`, obtained from
Theorem 1 (`nonrigid_iff_exists_delta`) exactly as the merged criteria were.

### 18.3 Non-rigidity witnesses and a `p,q`-dependent rigid repetitive instance

The criterion is non-vacuous in several explicit families
(`AssemblyP1/RigidityGeneralBridge.lean`):

* `generalBridge_nonrigid_m2_large` (`m₂ ≥ p+1`): witness `(a,c,u,w) = (q, -p, 0, 0)`
  — the relation `q·C1 - p·C2` has zero total mass;
* `generalBridge_nonrigid_m1_large` (`m₁ ≥ q+1`): witness `(-q, p, 0, 0)`;
* `generalBridge_nonrigid_eq_m1` (`p = q`, `m₁ ≥ 2`): witness `(-1, 1, 0, 0)`;
* `generalBridge_nonrigid_eq_m2` (`p = q`, `m₂ ≥ 2`): witness `(1, -1, 0, 0)`;
* `generalBridge_nonrigid_q3_f` (`q = 3`, `m₁ = m₂ = 1`, `f ≥ 3`): witness
  `(1, 0, -1, -2)`, generalising `length3Bridge_nonrigid_f` to arbitrary `p`.

Unlike the merged `2`-cycle bridge, the general classification is genuinely
`p,q`-dependent. The kernel-checked instance `generalBridge_rigid_repetitive`
shows that `(p,q,m₁,m₂,f) = (3,4,2,1,1)` is **rigid** even though the first
cycle is traversed twice (`m₁ = 2`). Hence *no* hypothesis of the form
"`m₁ ≥ 2`" alone forces non-rigidity: the relevant quantity is the
`p,q`-weighted Diophantine feasibility of Theorem 11.

### 18.4 Cross-check (`scripts/verify_257_general_bridge.py`)

The script `scripts/verify_257_general_bridge.py` is self-contained, exact, and
deterministic. It recomputes rigidity from scratch by enumerating **all**
positive integer circulations of total `G` on the `p+q+2` arcs and compares with
the four-variable criterion over an exhaustive scope (`2 ≤ p, q ≤ 4`,
`1 ≤ m₁, m₂ ≤ 4`, `1 ≤ f ≤ 5`, `G ≤ 22`: **448** general bridges, **0**
mismatches), and re-derives all eight worked witnesses plus the rigid repetitive
instance. [verified computation, exhaustive in scope]

### 18.5 Epistemic status

Theorems and instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityGeneralBridgeAudit`, and `AxiomAudit257.lean`); no
`sorry`/`admit`/`axiom`/`native_decide`. The topology is an *abstract* oriented
support graph, as for the merged bridge; realizability as a de Bruijn
read-support is not claimed. The residual — a *polynomial* min-cut/max-flow
closed form for general supports, or a proof that none exists — remains
**OPEN** (§8.1/§8.2).


## 19. The double theta: coupling begins at cycle rank 3 (§8.1 progress)

This section advances open item **§8.1** by isolating the *smallest realizable*
support on which the exact criterion is genuinely **coupled**, and by explaining why no
smaller realizable support can be. It builds on — and does not redo — the bouquet (§13), the
antiparallel bridge (§14), the length-3 bridge (§17) and the general `p,q` long
bridge (§18). [mathematical proof + kernel-checked]

### 19.1 Rank `≤ 2` is not coupled: the shared path is a sum

Recall the cycle rank `r = |E| - |V| + c` (so `L₀` has rank `r - 1`). A strongly
connected support of rank `r ≤ 2` is either a single directed cycle (`r = 1`), a
**figure-eight** (two cycles sharing one vertex, i.e. the `k = 2` bouquet), or a
**theta graph** (`r = 2`): two cycles sharing a directed path of length `≥ 1`.
For a theta graph the shared path `P` carries the **sum** of the two private
return-path values: at the shared endpoints `u, v` the balance equation forces
`value(P) = value(Q₁) + value(Q₂)`. For the base circulation `A` (positive,
multiplicity `m_P` on `P`, `m₁`, `m₂` on the private paths) this reads
`m_P = m₁ + m₂`, so the shared box `x + y ≥ 1 - m_P` is *implied* by the private
boxes `x ≥ 1 - m₁`, `y ≥ 1 - m₂`; a figure-eight has no shared edge and is
already a bouquet. Hence in both cases the exact criterion collapses to the
**bouquet criterion** of §13 on the cycles `C₁` (length `L₁`) and `C₂` (length
`L₂`):

```
not rigid  ⟺  ∃ (x,y) ≠ 0,  L₁·x + L₂·y = 0,  x ≥ 1-m₁,  y ≥ 1-m₂.
```

This is the same "shared value is a sum" mechanism that makes a *book* of cycles
collapse to a bouquet: balance at a shared vertex/path turns the shared box into
a redundant inequality. Consequently **no support of cycle rank `≤ 2` exhibits
box coupling**, and the naive "independent per-cycle" (bouquet) relaxation is
*exact* on all of them. [mathematical proof; exhaustive cross-check: every
theta graph on `≤ 3` vertices per path with `G ≤ 12` agrees with the bouquet
criterion — see the `[rank2]` part of `scripts/verify_257_double_theta.py`,
§19.5]

### 19.2 The double theta: the minimal coupled support among realizable supports

Coupling requires **two** independent hub balance equations. The smallest such
support **that is realizable as a de Bruijn read-support** is the
**double-theta graph** (rank `3`): two hubs `u, v`, joined in each
direction by one arc and by one length-`2` path,

```
P1 : u → v            (1 arc)        P2 : u → w → v   (2 arcs)
Q1 : v → u            (1 arc)        Q2 : v → z → u   (2 arcs)
```

on four vertices `u, v, w, z` and six arcs. Its degree-`2` vertices force each
path to carry a **constant** value, and the two hubs give the single independent
coupling equation

```
α₁ + α₂ = β₁ + β₂        (total flow out of u equals total flow into u),
```

where `α₁, α₂` are the values on `P1, P2` and `β₁, β₂` on `Q1, Q2`. Thus every
circulation is `δ = (α₁, α₂, α₂, β₁, β₂, β₂)`, of total mass
`α₁ + 2·α₂ + β₁ + 2·β₂`. Note the contrast with the bridge (§14): there the
coupling sits in the *box* (`a` with `q - p`); here it sits in an **extra
balance equation** between the four free parameters.

### 19.3 The exact criterion and a rigid repetitive instance

**Theorem 12 (double-theta criterion).** For multiplicities `m₁, m₂, n₁, n₂ ≥ 1`
with `m₁ + m₂ = n₁ + n₂`, the base circulation `A` is non-rigid **iff** there are
integers `α₁, α₂, β₁, β₂`, not all zero, with

```
α₁ + α₂ = β₁ + β₂                       (hub balance — the coupling)
α₁ + 2·α₂ + β₁ + 2·β₂ = 0               (zero total mass)
α₁ ≥ 1-m₁,  α₂ ≥ 1-m₂,                  (P1, P2 boxes)
β₁ ≥ 1-n₁,  β₂ ≥ 1-n₂.                  (Q1, Q2 boxes)
```

This is kernel-checked as
`AssemblyP1.RigidityDoubleTheta.doubleTheta_nonrigid_iff` (obtained from
Theorem 1, `nonrigid_iff_exists_delta`, exactly as the merged criteria were).

* **Non-rigidity witness** (`doubleTheta_nonrigid_witness`): at
  `(m₁,m₂,n₁,n₂) = (1,2,1,2)` the parameters `(2,-1,2,-1)` give
  `δ = (2,-1,-1,2,-1,-1)`, which is balanced, zero-sum and inside the box.
* **Rigid repetitive instance** (`doubleTheta_rigid_repetitive`): at
  `(m₁,m₂,n₁,n₂) = (2,1,2,1)` the `P1` and `Q1` arcs are each traversed **twice**,
  yet the instance is **rigid** — the hub-balance coupling forces every
  admissible perturbation to be zero.

### 19.4 The coupling equation is essential (failed simpler hypothesis)

The *relaxed* predicate obtained by **dropping** the hub-balance equation
`α₁ + α₂ = β₁ + β₂` — i.e. the naive independent-per-path / bouquet-style
relaxation that treats the four path values as free — is **not sound**:

> At `(m₁,m₂,n₁,n₂) = (2,1,2,1)` the relaxed predicate is satisfied (witness
> `(α₁,α₂,β₁,β₂) = (-1,1,-1,0)`, `δ = (-1,1,1,-1,0,0)`), while the instance is
> **rigid**.

This is kernel-checked as `AssemblyP1.RigidityDoubleTheta.relaxed_not_sound`, a
committed counterexample to the tempting generalisation "the four path values
may be treated independently". So the double-theta criterion is *genuinely*
coupled and is **not** reducible to the bouquet criterion; this is the first
exact coupled criterion below the bridge's cycle rank `4`.

### 19.5 Cross-check (`scripts/verify_257_double_theta.py`)

The script `scripts/verify_257_double_theta.py` is self-contained, exact, and
deterministic. It recomputes rigidity from scratch by enumerating **all** positive
integer circulations of total `G` on the six arcs and compares with the
four-variable criterion over an exhaustive scope
(`1 ≤ m₁,m₂,n₁,n₂ ≤ 5`, `m₁+m₂ = n₁+n₂`, `G ≤ 16`: **33** double thetas, **0**
mismatches); it re-derives the kernel witness, two explicit non-rigidity families
and the rigid repetitive instance, and confirms that the relaxed predicate is
satisfied at the rigid instance `(2,1,2,1)`. Its `[rank2]` part additionally
checks that **81** rank-`2` theta graphs agree with the bouquet criterion
(`0` mismatches), substantiating §19.1. [verified computation, exhaustive in
scope]

### 19.6 Epistemic status

Theorem 12 and the instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigidityDoubleThetaAudit`, and `AxiomAudit257.lean`); no
`sorry`/`admit`/`axiom`/`native_decide`. The double-theta **is** realizable as a
de Bruijn read-support (two hubs of degree `4`, two vertices of degree `2`): at
`L = 3` take `u = AB`, `v = BA`, `w = BB`, `z = AA`, so the six arcs are the
distinct length-`3` words `ABA, ABB, BBA, BAB, BAA, AAB`; the circular genome
`ABABBA` has exactly this read spectrum (each arc once), and `AABABABB` realizes
the multiplicity tuple `(2,1,2,1)`. (This corrects an earlier note that claimed
the double-theta was non-realizable: the stated reason — a de Bruijn graph has at
most one arc between any ordered pair — does not apply, since the six arcs are
six distinct ordered pairs.) The genuinely **non-realizable** coupled support is
instead the smaller `3`-vertex `K3`-minus-an-arc (rank `3`), whose de Bruijn
overlap constraints are unsatisfiable. The residual — a *polynomial*
min-cut/max-flow closed form for general supports, or a proof that none exists —
remains **OPEN** (§8.1/§8.2).

---

## 20. The multi-hub family: unbounded cycle rank with a polynomial criterion (§8.1/§8.2 progress)

This section advances open items **§8.1** (a polynomial closed-form criterion
beyond bounded cycle rank) and **§8.2** (the exact complexity) by isolating a
genuinely **unbounded-cycle-rank** family with an exact, polynomial-time
decidable criterion. It builds on — and does not redo — the bouquet (§13), the
antiparallel bridge (§14), the length-3 bridge (§17), the general `p,q` bridge
(§18) and the double theta (§19). [mathematical proof + kernel-checked + verified
computation]

### 20.1 The topology

The *multi-hub* family `MH(k, l; L, M)` joins two hubs `u, v` by `k` internally
vertex-disjoint `u → v` paths of lengths `L₁, …, L_k ≥ 1` and `l` internally
vertex-disjoint `v → u` paths of lengths `M₁, …, M_l ≥ 1`:

```
u → … → v      (k paths, arbitrary lengths)      v → … → u      (l paths)
```

on `2 + Σ(L_i − 1) + Σ(M_j − 1)` vertices and `Σ L_i + Σ M_j` arcs, of cycle
rank `k + l − 1`. Unlike the bouquet (rank `k`, but all cycles through one
vertex), the double theta / general two-hub (rank `3`) and the bridges (rank
`4`), here `k` and `l` are **arbitrary**, so the cycle rank is **unbounded**. The
bouquet is `k = l = 1`; the double theta is `k = l = 2` with lengths `(1,2)`.

Every internal vertex has in- and out-degree `1`, so balance forces each path to
carry a **constant** value; writing `α` for the value on each path, the only
independent balance equation is the **hub balance**
`∑_{u→v} α = ∑_{v→u} α`, and the total mass is `∑ length · α`. This is
kernel-checked as `phi_of_balanced` / `balanced_of_phi`.

### 20.2 The exact two-equation criterion

**Theorem 13 (multi-hub criterion).** For lengths `L, M ≥ 1` and multiplicities
`m ≥ 1` with `∑_{u→v} m = ∑_{v→u} m`, the base circulation `A` is non-rigid
**iff** there is a nonzero integer path-perturbation `α` with

```
∑_{u→v} α = ∑_{v→u} α              (hub balance — the coupling)
∑_s length_s · α_s = 0             (zero total mass)
α_s ≥ 1 − m_s                       (boxes)
```

This is kernel-checked as
`AssemblyP1.RigidityMultiHub.multiHub_nonrigid_iff`, obtained from Theorem 1
(`nonrigid_iff_exists_delta`) exactly as the merged criteria were. It
specialises to the bouquet criterion (`k = l = 1`) and to
`doubleTheta_nonrigid_iff` (`k = l = 2`, lengths `(1,2)`).

The contrast with the bouquet is the **hub-balance coupling**: the two hubs
impose one equation linking the two directions, which is *not* implied by the
boxes.

### 20.3 Instances: a rigid repetitive support and the coupling refutation

* **Rigid repetitive instance** (`multiHub_rigid_repetitive_2`): the instance
  `p2`/`m2` — lengths `(1,3)` each way, multiplicities `(2,1)` — is **rigid**,
  even though the length-`1` path of each direction is traversed **twice**. So
  no `m ≥ 2` repeat bound forces non-rigidity in this family.
* **All multiplicities `1` is rigid** (`multiHub_rigid_all_one`): with unit
  slack the boxes force `α ≥ 0`, and positive lengths force `α = 0`.
* **The coupling equation is essential (failed simpler hypothesis)**
  (`multiHub_relaxed_not_sound`): the *relaxed* predicate obtained by dropping
  the hub-balance equation — the naive independent-per-path / bouquet-style /
  single-cut relaxation — is **satisfied** at the rigid instance `p2`/`m2`
  (witness `α = (-1, 0, 1, 0)`). Hence **no** criterion of the independent-per-
  path or single-cut form can decide the multi-hub family: the coupling is a
  genuine balance equation, not a cut condition. This is a committed
  counterexample to the tempting "min-cut / per-cycle" hypothesis for §8.1.

### 20.4 §8.2: a polynomial criterion for the unbounded-rank family

Shifting to nonnegative variables `u_s = α_s + m_s − 1 ≥ 0`, the criterion
becomes the existence of a **second** nonnegative integer solution to the
**two-equation** system

```
∑_{u→v} u − ∑_{v→u} v = l − k
∑_s length_s · u_s (on u→v) + ∑_s length_s · v_s (on v→u) = G − |E|
```

with the base solution `(m_s − 1)` always present. Since the path lengths are
encoded in **unary** (an explicit support), this is a nonnegative-integer
**uniqueness** problem decidable by a dynamic program over `(count, mass)` pairs
that counts solutions up to `2`; its running time is polynomial in the input
size (`O((k + l) · C²)` with `C = G − |E|`). This is a §8.2 **upper bound for a
family of unbounded cycle rank** and complements the bouquet Apéry-set bound
(§15). It is implemented and cross-checked from scratch in
`scripts/verify_257_multi_hub.py`. The **uniform-in-support** complexity
(arbitrary topology) remains **OPEN**.

### 20.5 Cross-check (`scripts/verify_257_multi_hub.py`)

The script `scripts/verify_257_multi_hub.py` is self-contained, exact and
deterministic. It recomputes rigidity from scratch by enumerating **all**
positive integer circulations of total `G` on the multi-hub graph and compares
with the two-equation criterion over exhaustive scopes — `(k,l) ∈ {(1,1),(2,2),
(3,3),(3,2),(2,3),(4,4)}` with small lengths, multiplicities `≤ 4` and `G ≤ 16`
(**78** multi-hub supports, **0** mismatches) — re-derives the rigid repetitive
instance `p2`/`m2`, the relaxed counterexample and the all-ones rigidity, and
cross-checks the polynomial DP against the criterion. [verified computation,
exhaustive in scope]

### 20.6 Epistemic status

Theorems and instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]` (`AssemblyP1/RigidityMultiHubAudit`,
and `AxiomAudit257.lean`); no `sorry`/`admit`/`axiom`/`native_decide`. The
topology is an *abstract* oriented support graph, as for the merged general
bridge (§18); the double-theta specialisation is de-Bruijn-realizable (§19.6).
The residual — a *polynomial* min-cut/max-flow closed form for **arbitrary**
supports (general topology), or a proof that none exists — remains **OPEN**
(§8.1/§8.2); §20 shows that such a criterion cannot be of a single-cut /
independent-per-path form, and gives a polynomial criterion for the
unbounded-rank multi-hub subfamily.

---

## 21. The triangular multi-hub family: a three-hub unbounded-rank criterion (§8.1/§8.2 progress)

This section advances open items **§8.1** (a polynomial closed-form criterion
beyond bounded cycle rank) and **§8.2** (the exact complexity) by isolating a
genuinely **three-hub** family — distinct from the two-hub multi-hub of §20 —
with an exact, polynomial-time decidable criterion. It builds on — and does not
redo — the bouquet (§13), the bridges (§14/§17/§18), the double theta (§19) and
the two-hub multi-hub (§20). [mathematical proof + kernel-checked + verified
computation]

### 21.1 The topology

The *triangular multi-hub* family `TH(a, b, c; L, M, N)` joins three hubs
`u, v, w` in a directed cycle by `a` internally vertex-disjoint `u → v` paths,
`b` `v → w` paths and `c` `w → u` paths, of lengths `L₁, …, L_a`, `M₁, …, M_b`,
`N₁, …, N_c ≥ 1`:

```
u → … → v      (a paths)      v → … → w      (b paths)      w → … → u      (c paths)
```

on `3 + Σ(L_i − 1) + Σ(M_j − 1) + Σ(N_k − 1)` vertices and
`Σ L_i + Σ M_j + Σ N_k` arcs, of cycle rank `a + b + c − 2`. Unlike the two-hub
multi-hub (§20), which has *two* hubs and a *single* independent hub-balance
equation, here the third hub adds a **second independent hub-balance equation**;
the cycle rank is again **unbounded**. The two-hub multi-hub is the degenerate
case `c = 0`; the directed triangle of single arcs is `a = b = c = 1`.

Every internal vertex has in- and out-degree `1`, so balance forces each path to
carry a **constant** value; writing `α, β, γ` for the values in the three
directions, the hubs give the two independent balance equations
`∑_{u→v} α = ∑_{v→w} β` and `∑_{v→w} β = ∑_{w→u} γ`, and the total mass is
`∑ L_i α_i + ∑ M_j β_j + ∑ N_k γ_k`. This is kernel-checked as
`phi_of_balanced` / `balanced_of_phi`.

### 21.2 The exact three-equation criterion

**Theorem 14 (triangular multi-hub criterion).** For lengths `L, M, N ≥ 1` and
multiplicities `m ≥ 1` with `∑ m(u→v) = ∑ m(v→w) = ∑ m(w→u)`, the base
circulation `A` is non-rigid **iff** there is a nonzero integer path-perturbation
`(α, β, γ)` with

```
∑_{u→v} α = ∑_{v→w} β = ∑_{w→u} γ        (two hub balances — the coupling)
∑_s length_s · α_s + ∑_s length_s · β_s + ∑_s length_s · γ_s = 0   (zero mass)
α_s, β_s, γ_s ≥ 1 − m_s                    (boxes)
```

This is kernel-checked as `AssemblyP1.RigidityTriHub.triHub_nonrigid_iff`,
obtained from Theorem 1 (`nonrigid_iff_exists_delta`) exactly as the merged
criteria were. The contrast with the two-hub multi-hub is the **second**
hub-balance equation: the three-hub coupling is strictly stronger, and the
criterion is a **three-equation** system rather than a two-equation one.

### 21.3 Instances: a rigid repetitive support, a witness, and the coupling refutation

* **Rigid repetitive instance** (`triHub_rigid_repetitive`): the instance
  `p3`/`m3` — lengths `(1,3)` each direction, multiplicities `(2,1)` each
  direction — is **rigid**, even though the length-`1` path of each direction is
  traversed **twice**. So no `m ≥ 2` repeat bound forces non-rigidity here.
* **Non-rigidity witness** (`scripts/verify_257_tri_hub.py`): at lengths `(1,1)`
  each direction and multiplicities `(2,2)` each direction, the perturbation
  `(α, β, γ) = ((-1,1), (-1,1), (-1,1))` (or `((-1,1),(0,0,0),(0,0))`) is a
  valid non-rigidity witness.
* **All multiplicities `1` is rigid** (`triHub_rigid_all_one`): with unit slack
  the boxes force the perturbation to be nonnegative, and positive lengths force
  it to be zero.
* **The coupling equations are essential (failed simpler hypothesis)**
  (`triHub_relaxed_not_sound`): the *relaxed* predicate obtained by dropping the
  two hub-balance equations — the naive independent-per-path / bouquet-style /
  single-cut relaxation — is **satisfied** at the rigid instance `p3`/`m3`.
  Hence **no** criterion of the independent-per-path or single-cut form can
  decide the triangular multi-hub family.

### 21.4 §8.2: a polynomial criterion for the unbounded-rank family

Shifting to nonnegative variables `u_i = α_i + m_i − 1 ≥ 0` (etc.), the criterion
becomes the existence of a **second** nonnegative integer solution of a
**three-equation** system (two balance differences and the weighted mass) whose
base solution is `(m_s − 1)`. Since the path lengths are encoded in **unary** (an
explicit support), this is a nonnegative-integer **uniqueness** problem decidable
by a dynamic program over `(Δ_ab, Δ_bc, mass)` counting solutions up to `2`; its
running time is polynomial in the input size. This is a §8.2 **upper bound for a
three-hub family of unbounded cycle rank** and complements the bouquet Apéry-set
bound (§15) and the two-hub DP (§20). It is implemented and cross-checked from
scratch in `scripts/verify_257_tri_hub.py`. The **uniform-in-support** complexity
(arbitrary topology) remains **OPEN**.

### 21.5 Cross-check (`scripts/verify_257_tri_hub.py`)

The script is self-contained, exact and deterministic. It recomputes rigidity
from scratch by enumerating **all** positive integer circulations of total `G` on
the triangular multi-hub graph and compares with the criterion and the DP over
exhaustive scopes — `(a,b,c) ∈ {(1,1,1), (2,2,2), (3,3,3), (2,3,2), (3,2,3),
(2,2,3)}` with small lengths, multiplicities `≤ 4` and `G ≤ 16` (**153**
triangular supports, **0** mismatches) — re-derives the rigid repetitive
instance `p3`/`m3`, the non-rigidity witness, the relaxed counterexample and the
all-ones rigidity, and includes a **mutation-red control** (the coupling-dropped
relaxation disagrees with the brute force, so the harness has real discriminating
power). [verified computation, exhaustive in scope]

### 21.6 Epistemic status

Theorems and instances are kernel-checked with only
`[propext, Classical.choice, Quot.sound]` (`AssemblyP1/RigidityTriHubAudit`,
and `AxiomAudit257.lean`); no `sorry`/`admit`/`axiom`/`native_decide`. The
topology is an *abstract* oriented support graph, as for the merged general
bridge (§18) and the two-hub multi-hub (§20). The residual — a *polynomial*
min-cut/max-flow closed form for **arbitrary** supports (general topology), or a
proof that none exists — remains **OPEN** (§8.1/§8.2); §21 shows that such a
criterion cannot be of a single-cut / independent-per-path form for the
 triangular family either, and gives a polynomial criterion for that
 unbounded-rank three-hub subfamily.

---

## 22. Directed-cycle sufficiency (parametric) and the AATT boundary

This section proves a new small Lean-checked rigidity lemma for a restricted
family (§8.1 progress on a bounded-topology front): uniform directed cycles
are rigid at *every* multiplicity, and records a kernel-checked rigid
repetitive boundary example showing "single directed cycle" is sufficient
but **not necessary**. It builds on — and does not redo — the finite decider
(§11), which is used only as the checking engine for the boundary instance.
[mathematical proof + kernel-checked + verified computation]

### 22.1 Parametric directed-2-cycle rigidity

**Theorem 15 (directed-2-cycle sufficiency).** The directed `2`-cycle support
(`0 → 1 → 0`) with uniform multiplicity `k` and total `G = 2 * k` is rigid,
for every `k : ℕ`.

_Proof._ Balance at vertex `0` (out-edge `{0}`, in-edge `{1}`) forces
`B 0 = B 1`; the total `B 0 + B 1 = 2 * k` then forces `B 0 = B 1 = k. ∎

This is kernel-checked as
`AssemblyP1.RigiditySimpleCycle.cycle2_rigid`, with the constancy step as
`cycle2_balanced_const`. The `ATATAT`/`L = 3` read graph *is* this `2`-cycle
(`cycle2_is_atatat_tail/head`), so the canonical "rigid despite triple
`(L-1)`-mer repeats" example now follows parametrically
(`atatat_of_cycle2`: rigid at every uniform `k`, total `2 * k`), rather than
from a single `k = 3` computation. The general `n`-cycle case is strictly
analogous (balance forces constancy on any directed cycle) and remains open
in Lean.

### 22.2 The AATT boundary: rigid but not a single directed cycle

The circular genome `S = AATT` at `L = 2` has spectrum
`{AA:1, AT:1, TT:1, TA:1}` (verified in
`scripts/verify_257_simple_cycle.py`): two vertices `A, T` and four edges
`AA : A → A`, `AT : A → T`, `TT : T → T`, `TA : T → A`, of cycle rank
`|E| - |V| + c = 3` (zero-sum rank `r = 2`). It is **not** a single directed
cycle, yet it is **rigid** at `A = (1,1,1,1)`, `G = 4`: balance at `A` forces
`B(AT) = B(TA)`, and `B(AA) + B(TT) + 2 * B(AT) = 4` with `B ≥ 1` forces
`B = 1` everywhere. Kernel-checked as
`AssemblyP1.RigiditySimpleCycle.aatt_rigid` (`by decide`, search space
`5^4 = 625`, recorded as `aatt_search_space`).

**Failed simpler hypothesis (committed).** "The support is a single directed
cycle ⟺ rigid" is **false** as an iff: `AATT` is a rigid read-support with
four edges. The forward direction for `2`-cycles is Theorem 15; the reverse
direction fails already at this smallest genome boundary.

**Finite separator for cycle-rank-only classifiers.** Two circular `L = 3`,
`G = 7` genomes have the same support summary `(|V|, |E|, cycle-rank) =
(3,4,2)` but opposite rigidity status:

* `S = AABABAB` has support edges `AAB, ABA, BAB, BAA`, with multiplicities
  `(1,3,2,1)` in that order. It is **rigid**: the exact enumeration finds only
  that positive balanced circulation of total `7`.
* `T = AAAAAAB` has support edges `AAA, AAB, ABA, BAA`, with multiplicities
  `(4,1,1,1)`. It is **non-rigid**: `(1,2,2,2)` is a distinct positive
  balanced circulation of total `7` on its support.

The supports are different (the repeated edge is `BAB` versus `AAA`), but their
vertex/edge counts, first Betti number, read length, and genome length coincide.
Therefore those scalar graph/genome summaries cannot decide rigidity; the
actual labeled incidence structure and multiplicities matter. This finite
counterexample refutes only classifiers determined by these summaries, not
every graph-theoretic condition. [mathematical witness + verified computation]

### 22.3 Cross-check (`scripts/verify_257_simple_cycle.py`)

The script is self-contained, exact and deterministic. It recomputes rigidity
from scratch by enumerating **all** positive integer circulations of total
`G`:

* directed `n`-cycles, `n = 2..6`, uniform `k = 1..4` — **20** cases, all
  rigid, **0** mismatches;
* `AATT` at `(1,1,1,1)` — rigid, unique witness;
* **mutation-red control**: the same `AATT` support at `(2,1,1,1)`, `G = 5`
  is non-rigid (witnesses `(1,1,2,1)`, `(2,1,1,1)`), so the harness has real
  discriminating power;
* complexity record: `(G+1)^|E|` tabulated against `r` (e.g. `AATT`: 625
  candidates at `r = 2`; 6-cycle `k = 4`: 244140625 at `r = 0`);
* genome realizations: circular `AATT`/`L = 2` and `ATATAT`/`L = 3` spectra;
* **cycle-rank separator**: `AABABAB` and `AAAAAAB` share `L=3`, `G=7`,
  `|V|=3`, `|E|=4`, and cycle rank `2`, while exact enumeration reports rigid
  versus non-rigid.
  [verified computation, exhaustive in scope]

### 22.4 Second rigid rank-2 cell (`scripts/verify_257_aabaabb.py`)

Circular `S = AABAABB`, `L = 3` has spectrum
`{AAB:2, ABA:1, BAA:2, ABB:1, BBA:1}` (`G = 7`) on vertices
`AA, AB, BA, BB` (`|V| = 4`, `|E| = 5`, cycle rank `2`). It is **not** a
single directed cycle, yet exact enumeration finds exactly **one** positive
balanced circulation of total `7`: `(2,1,2,1,1)` in spectrum order. The
neighbouring totals `G = 6` and `G = 8` admit **zero** positive balanced
circulations on this support, so the rigid point is isolated rather than
vacuous. The `(L-1)`-mers `AA`/`AB`/`BA` each occur twice in `S`, giving
another rigid repetitive genome beyond `ATATAT`/`AABABAB`, and the shape
`(|V|,|E|) = (4,5)` differs from the `(3,4)` separator pair at the same
cycle rank `2`: rigidity is not a function of cycle rank alone. Lean
formalization of this cell is **not** attempted here (python-only verified
computation; no `sorry` introduced).
  [verified computation, exhaustive in scope]

### 22.5 Epistemic status

`cycle2_rigid`, `cycle2_balanced_const`, `atatat_of_cycle2`, `aatt_rigid`
and `aatt_search_space` are kernel-checked with only
`[propext, Classical.choice, Quot.sound]`
(`AssemblyP1/RigiditySimpleCycleAudit`, and `AxiomAudit257.lean`); no
`sorry`/`admit`/`axiom`/`native_decide`. The uniform-in-support polynomial
criterion (§8.1/§8.2) remains **OPEN**.
