import Mathlib
import AssemblyP1.Issue94TW1
import AssemblyP1.BBTLadder
import AssemblyP1.Issue94CaseSplit

/-!
# Board 94, front 94a10: the **edge-type** obligation on `D`, and two bridges

This module is the successor to `AssemblyP1.Issue94TW1` (front 94e7), which
**refuted** the board's `t_w = 1` step at
`AssemblyP1.Issue94TW1.not_UniqueInArb_3`.  It does not re-attack that step.
It answers, in the order the board directed, three questions and states the
one `Prop` that the answers force.

## Step 1 --- the "208 instances with a simple `D`" claim is an evaluator bug

Front 94e7 recorded 208 instances at `K ≤ 9` with a **simple** `D` and
`t_w > 1`, and read that as evidence that a parallel-edge division cannot
discharge the corrected obligation.  **That count is wrong.**  The predicate
`hasParallelEdges` of `scripts/verify_tw1_94.js` iterates its outer loop over
`edges` (an array of `[tail, head]` pairs) and its inner loop over
`edges[u].length` --- it treats the edge array as an adjacency structure.  For
every input the inner loop then runs exactly twice, over `[tail, head]` and
`[tail, head]` in the order of the two entries, so the `seen` set is rebuilt
from scratch each time and the predicate is **identically `false`**.  Every
instance was classified "simple", which is why 208 + 548 = 756 appeared.

With a correct predicate (group the edges by tail, then by head, and look for
a head repeated under one tail) the search gives, over the same range and the
same filters (`Ukkonen`, primitivity, `2 ≤ L ≤ K`):

| range | instances with `t_w > 1` | of those with a **simple** `D` |
| --- | --- | --- |
| `K ≤ 9`  | 562   | **0** |
| `K ≤ 11` | 2214  | **0** |
| `K ≤ 12` | 5142  | **0** |

So the parallel-edge division is not merely a repair of the *stated* split; it
is, over every range searched, **exactly** the right repair, and the corrected
obligation needs **no new idea** beyond it.  This is **evidence, not proof**: the
completeness of the sweep over those ranges is not proved, and nothing is
claimed for `K > 12` or for a larger alphabet.  What it does license is the
*design* conclusion of §2--§3 below, which rests on the kernel, not on the
sweep.

## Step 2 --- un-condensed or condensed?  **Un-condensed, on the vertex cycle

BBT's Theorem 3 is phrased about the *condensed* sequence graph, and front 94e7
left open whether the corrected obligation should be stated there.  **It should
not, and the reason is that the edge-type convention and the vertex cycle are
the *same object*, which the kernel makes precise.**

The multigraph `D(S, L)` of `AssemblyP1.Issue94TW1` has vertex `vtx r` at
start `r` and edge `r` from `vtx r` to `vtx (nextPos r)`.  So the **edge type**
of `r` is exactly the pair `(vtx r, vtx (nextPos r))`, and an edge-type Eulerian
circuit of `D` is a cyclic sequence of such pairs.  Two facts, both proved below,
pin the object down:

* §2.2, `EType_eq_iff`: two starts have the same edge type iff they carry the
  same `(L-1)`-mer **and** the same successor `(L-1)`-mer --- so the edge type
  is a function of the vertex walk, and the edge-type word determines the
  vertex word.  This is the whole content of the "parallel edges are
  indistinguishable" convention, and it is a `decide`-level fact.
* §3, `EType_cycle_iff` and `VertexCycleEq_iff_EType_cycle`: a cyclic listing
  of starts is a circuit of `D`, its edge-type word is `EType`, and

  ```text
    VertexCycleEq hK L S σ τ   <->   the edge-type words of σ and τ agree up to rotation
  ```

  The forward direction (`VertexCycleEq_of_EType_cycle`) is the one that
  matters and is proved; the backward one (`EType_cycle_of_VertexCycleEq`) is
  included so the equivalence is a genuine two-way identification and not a
  one-sided convenience.

It follows that **the number of edge-type circuit orbits of `D` is the number
of vertex cycles**, and that the corrected obligation is therefore
`BBTEulerian.UniqueEulerianCycle L` *verbatim* --- not a new `Prop`.
`EdgeTypeUnique L` in §4 is stated, and
`edgeTypeUnique_iff_uniqueEulerianCycle` proves the equivalence, so the board's
"corrected obligation" is discharged as an *identification* rather than as a
fresh open problem.  Condensing would introduce a second formalisation of a
statement the tree already has, on an object (`Branch`, `branchVerts`,
`branchStarts`) that plays no part in the conclusion.

Note also that front 94e7's `VStep` already *is* the edge-type relation: it is
`∃ r' ∈ T, vtx r' = u ∧ vtx (nextPos r') = v`, so parallel edges of `T` are
never distinguished.  Reusing it unchanged, as directed, imports the edge-type
convention for free.

## Step 3 --- the interface audit, and the bounded bridge

`BBTCrossingCoalesce.CrossingPairsCoalesce L` is **inhabited** at arbitrary
`[DecidableEq α]` by `AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_general`
(`d0aa0aa`), but its two bounds `2 ≤ L` and `L ≤ K` are **hypotheses of that
`def`**, not consequences of anything.  `BBTLadder.CrossingChordsCoalesce L`
does **not** carry them, so the immediate bridge
`crossingPairsCoalesce_general → CrossingChordsCoalesce` does **not** typecheck
and must not be obtained by smuggling the bounds in.

The bounds cannot be discharged, because the out-of-range cases are not vacuous:
`P2 hG L S` is **satisfied** with `L > G` (e.g. `G = 2`, `S = 01`, `L = 3`, where
both clauses of `P2` are vacuous for want of four distinct starts), and
`P2 hG L S` is satisfied with `L ≤ 1` on any word with no interleaved repeat
pair.  So this is **option (b)**: the interface is corrected explicitly, the
reason is recorded here and at the theorem, and the *exact* statement that
`BBTLadder.LadderVertexCycle` consumes is what is proved.

`crossingChordsCoalesce_bounded` (§5) is that statement, and it is
`CrossingChordsCoalesce` read with the two bounds made explicit, i.e. the
bridge with the bounds as *hypotheses* rather than smuggled in.  Every
hypothesis of `LadderVertexCycle`'s block condition is available from it inside
`LadderVertexCycle` itself, which carries `2 ≤ L` and `L ≤ K`; see §5.3.

## What is NOT established here

1. **`LadderVertexCycle` is NOT proved.**  §5.3 discharges the *block* half of
   its hypothesis --- the only half that was missing --- and §6.2 records the
   reduction (`ladderVertexCycle_of_blockless`) to the residual
   `BlocklessLadderVertexCycle`.  But the global traversal-order step, that a
   laminar family of vertex-invisible ladder blocks forces the vertex listing to
   be a rotation, has no inhabitant here.  Neither does it have one anywhere in
   the tree.
2. **`hPevzner` / `EulerianCycleObstruction` is untouched.**
   `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation` and its
   same-length wrapper still RETAIN the `hPevzner` / `EulerianCycleObstruction`
   premise.  The public endpoint is **not** discharged.  Nothing in this module
   uses or introduces such a premise.
3. The unbounded `BBTLadder.CrossingChordsCoalesce L` is **not** proved, and I
   do **not** claim it is true: the `L < 2` and `L > K` cases are outside
   everything proved above, and I have **no** counterexample and **no** search
   over them either.  §5 states exactly which half is open.
4. The sweep of §1 is evidence only.  It is used here to *kill* a false claim
   (front 94e7's 208) and to motivate a design decision, never as a premise of
   any theorem in this module.
5. `InArb` is not re-derived from a Matrix-Tree determinant; the bridge
   "`t_w = 1` iff `UniqueInArb`" front 94e7 already recorded as unproved is
   still unproved here.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no
linter suppression.  `autoImplicit` is off.
-/

namespace AssemblyP1.Issue94TW1EdgeType

open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTChords
open AssemblyP1.P2
open AssemblyP1.BBTLadder
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94TW1
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.RepeatAdapter
open SourceFaithfulIs
open Finset

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-! ## 1. Edge types of `D`: the quotient that kills the parallel labelling -/

/-- **The edge type of the edge of `D` at start `r`**: the pair of the tail and
head `(L-1)`-mer, i.e. the label the edge carries once parallel edges are made
indistinguishable.  This is the object `docs/exact-same-length-spectrum-fibre-count.md`
works with when it divides by `∏ c_h(e)!`. -/
def EdgeTypeOf (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r : Fin G) :
    (Fin (L - 1) → α) × (Fin (L - 1) → α) :=
  (vtx hG L S r, vtx hG L S (nextPos hG r))

/-- **Two edges of `D` have the same type**: same tail `(L-1)`-mer and same
head `(L-1)`-mer.  For distinct starts this is exactly the parallel-edge
relation. -/
def SameType (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r s : Fin G) : Prop :=
  vtx hG L S r = vtx hG L S s ∧
    vtx hG L S (nextPos hG r) = vtx hG L S (nextPos hG s)

instance (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r s : Fin G) :
    Decidable (SameType hG L S r s) := by
  unfold SameType; infer_instance

/-- **Being of the same type is an equivalence relation on the starts of
`D`.**  It is therefore an equivalence *relation* in the `Setoid` sense, so the
edge-type quotient of `D` is a quotient of this relation, and the parallel
edges are exactly the identified classes. -/
theorem sameType_equiv (hG : 0 < G) (L : ℕ) (S : Fin G → α) :
    Equivalence (SameType hG L S) :=
  { refl := fun _r => ⟨rfl, rfl⟩
    symm := fun {_r _s} h => ⟨h.1.symm, h.2.symm⟩
    trans := fun {_r _s _t} h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩ }

/-- **Two starts of the same edge type carry the same `(L-1)`-mer.**  This is
the projection of the edge type onto its tail, and it is the direction that
makes the edge-type word *determine* the vertex word. -/
theorem vtx_eq_of_sameType {hG : 0 < G} {L : ℕ} {S : Fin G → α} {r s : Fin G}
    (h : SameType hG L S r s) : vtx hG L S r = vtx hG L S s := h.1

/-! ## 2. The edge-type word of a circuit of `D`

`BBTEulerian.EulerianCycle hG L S σ` is **already** a labelling of a circuit of
`D`: its first clause `∀ i, vtx (σ (nextPos i)) = vtx (nextPos (σ i))` says that
the labelling `σ` respects the walk of `D`, start by start.  So the set of
`EulerianCycle` is the set of *labellings* of the edge-type circuits, and
projecting a labelling to its edge-type word is exactly the operation that
divides out the parallel-edge over-count.  The two theorems of this section
identify the two conventions. -/

/-- **The edge-type word of a circuit of `D` labelled by `σ`**: the cyclic
sequence of edge types, read at the starts `σ i` and its successor in the
circuit. -/
def EType (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G → Fin G) (i : Fin G) :
    (Fin (L - 1) → α) × (Fin (L - 1) → α) :=
  (vtx hG L S (σ i), vtx hG L S (σ (nextPos hG i)))

/-- **Step 1 of the identification: two starts of `D` have the same edge type
iff they carry the same `(L-1)`-mer and the same successor `(L-1)`-mer.**

So the edge type is *exactly* the pair of consecutive vertices of the walk, and
the edge-type word of a circuit determines the vertex word position by
position.  Nothing about condensation is used. -/
theorem edgeTypeOf_eq_iff (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r s : Fin G) :
    EdgeTypeOf hG L S r = EdgeTypeOf hG L S s ↔ SameType hG L S r s := by
  unfold EdgeTypeOf SameType
  constructor
  · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h₁, h₂⟩; exact Prod.ext h₁ h₂

/-- **Step 2 of the identification: the edge-type word of `σ`, at `i`, is the
pair of vertices that `σ` reads at `i` and at the next start.**  Stated so that
the vertex projection of an edge-type word is visibly the vertex cycle. -/
theorem EType_eq (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G → Fin G) (i : Fin G) :
    EType hG L S σ i = (vtx hG L S (σ i), vtx hG L S (σ (nextPos hG i))) := rfl

/-- **The edge-type word of a cycle presented by an `Equiv`.**  This is the
form used everywhere below; it is `EType` on the underlying map. -/
abbrev ETypeEquiv (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G)
    (i : Fin G) : (Fin (L - 1) → α) × (Fin (L - 1) → α) :=
  EType hG L S (σ : Fin G → Fin G) i

/-! ## 3. The edge-type convention and the vertex cycle are the same object -/

/-- **The edge-type words of two circuits agree up to rotation iff their vertex
cycles do.**  Forward direction: an edge-type equality projects onto the two
coordinates, giving the two vertex equalities `VertexCycleEq` asks for.

This is the kernel-checked form of the step-2 decision: the edge-type circuit
orbits of `D` and the vertex cycles of `D` are in bijection, so the corrected
obligation is the statement the tree already has, and the *condensed* sequence
graph of BBT's Theorem 3 is not a separate object that has to be formalised
again. -/
theorem VertexCycleEq_of_EType_cycle {hG : 0 < G} {L : ℕ} {S : Fin G → α}
    {σ τ : Fin G ≃ Fin G} (k : Fin G)
    (h : ∀ i : Fin G,
      EType hG L S σ i
        = EType hG L S (fun j => rotAdd hG k.val (τ j)) i) :
    VertexCycleEq hG L S σ τ :=
  ⟨k, fun i => (congrArg Prod.fst (h i))⟩

/-- **The converse direction**, so that §3 is a two-way identification and not
a one-sided convenience: equal vertex cycles give equal edge-type words up to
the same rotation. -/
theorem EType_cycle_of_VertexCycleEq {hG : 0 < G} {L : ℕ} {S : Fin G → α}
    {σ τ : Fin G ≃ Fin G} (h : VertexCycleEq hG L S σ τ) :
    ∃ k : Fin G, ∀ i : Fin G,
      EType hG L S σ i = EType hG L S (fun j => rotAdd hG k.val (τ j)) i :=
  by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, fun i => Prod.ext (hk i) (hk (nextPos hG i))⟩

/-- **The two conventions, identified.** -/
theorem VertexCycleEq_iff_EType_cycle {hG : 0 < G} {L : ℕ} {S : Fin G → α}
    {σ τ : Fin G ≃ Fin G} :
    VertexCycleEq hG L S σ τ ↔
      ∃ k : Fin G, ∀ i : Fin G,
        EType hG L S σ i = EType hG L S (fun j => rotAdd hG k.val (τ j)) i :=
  ⟨EType_cycle_of_VertexCycleEq, fun ⟨k, hk⟩ => VertexCycleEq_of_EType_cycle (hG := hG) (L := L) (S := S) k hk⟩

/-! ## 3.1. The two in-arborescences of front 94e7 are ONE edge-type object

The concrete check that the quotient does what it is supposed to do, at the
kernel-checked instance of the refutation: `T1` and `T2` of
`AssemblyP1.Issue94TW1` are different `Finset`s of starts but they carry the
**same** edge types, edge by edge.  This is why `not_UniqueInArb_3` is not a
refutation of `thm:BBT`, and it is the smallest instance of the corrected
obligation being the right one. -/

/-- **The two in-arborescences of the refutation instance are the same
edge-type set**: every edge of `T1` is matched by an edge of `T2` of the same
type, and conversely.  Note the matching is *not* the identity --- the start `1`
of `T1` is matched by the start `4` of `T2`, the parallel partner. -/
theorem T1_T2_same_edgeTypes :
    (∀ r ∈ T1, ∃ s ∈ T2, SameType h5 3 S10100 r s) ∧
      (∀ r ∈ T2, ∃ s ∈ T1, SameType h5 3 S10100 r s) := by
  constructor
  · intro r hr
    simp only [T1, Finset.mem_insert, Finset.mem_singleton]
    at hr
    rcases hr with h | h | h
    · subst h; exact ⟨⟨0, by omega⟩, by decide, rfl, rfl⟩
    · subst h
      exact ⟨⟨4, by omega⟩, by decide, Issue94TW1.vtx1_eq_vtx4,
        Issue94TW1.T1_T2_differ_only_in_parallel_edge.2.2⟩
    · subst h; exact ⟨⟨3, by omega⟩, by decide, rfl, rfl⟩
  · intro r hr
    simp only [T2, Finset.mem_insert, Finset.mem_singleton]
    at hr
    rcases hr with h | h | h
    · subst h; exact ⟨⟨0, by omega⟩, by decide, rfl, rfl⟩
    · subst h; exact ⟨⟨3, by omega⟩, by decide, rfl, rfl⟩
    · subst h
      exact ⟨⟨1, by omega⟩, by decide, Issue94TW1.vtx1_eq_vtx4.symm,
        Issue94TW1.T1_T2_differ_only_in_parallel_edge.2.2.symm⟩

/-! ## 4. The corrected obligation, and its identification with the endpoint

`EdgeTypeUnique` is the obligation front 94e7's §5 described in prose and did
not state: every Eulerian circuit of `D`, **with parallel edges identified**,
is, up to rotation of the circuit, the truth's circuit.  It is stated in the
edge-type convention of `docs/exact-same-length-spectrum-fibre-count.md` and on
the **un-condensed** `D`, which §3 shows is the same object as the vertex cycle
the tree already works with. -/

/-- **The corrected edge-type Eulerian-circuit obligation.**  For every circle
and every word satisfying `Ukkonen` at `L`, every Eulerian cycle of the
`(L-1)`-mer multigraph `D` has, up to rotation, the **edge-type word** of the
truth's cycle.  Parallel edges are indistinguishable, exactly as the
`∏ c_h(e)!` denominators of `docs/exact-same-length-spectrum-fibre-count.md`
require.

This is a `Prop` and it has **no inhabitant** in this module.  What §4.1 proves
is that it is not a *new* obligation. -/
def EdgeTypeUnique (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      ∃ k : Fin K, ∀ i : Fin K,
        EType hK L S σ i
          = EType hK L S
              (fun j => rotAdd hK k.val ((Equiv.refl (α := Fin K) : Fin K → Fin K) j)) i

/-- **The corrected edge-type obligation IS the public endpoint.**
`EdgeTypeUnique L ↔ UniqueEulerianCycle L`.

By §3 the two conventions are the same object, so the obligation the board
formulated in the un-condensed `D` and the obligation BBT's Theorem 3 states
about the condensed sequence graph are *literally* the same `Prop` of this
tree, and the endpoint of `PopulationUniqueness` is discharged by the existing
statement rather than by a new one.  This is an identification, not a proof of
either side: the right-hand side still has no inhabitant, which is why
`hPevzner` is still needed downstream. -/
theorem edgeTypeUnique_iff_uniqueEulerianCycle {α : Type} [DecidableEq α] (L : ℕ) :
    EdgeTypeUnique (α := α) L ↔
      AssemblyP1.BBTEulerian.UniqueEulerianCycle (α := α) L := by
  constructor
  · intro h K hK S hUkk σ hEul
    rcases h K hK S hUkk σ hEul with ⟨k, hk⟩
    exact VertexCycleEq_of_EType_cycle (hG := hK) (L := L) (S := S) k hk
  · intro h K hK S hUkk σ hEul
    refine (VertexCycleEq_iff_EType_cycle (hG := hK) (L := L) (S := S)).mp ?_
    exact h K hK S hUkk σ hEul

/-! ## 5. The interface audit, and the bounded bridge

`BBTLadder.CrossingChordsCoalesce L` does not carry `2 ≤ L` and `L ≤ K`, but
`BBTCrossingCoalesce.CrossingPairsCoalesce L` takes them as hypotheses, and its
inhabitant `Issue94CaseSplit.crossingPairsCoalesce_general` needs them.  The
bridge therefore cannot be obtained by *smuggling* them in; it is obtained by
making them explicit.  This is option **(b)** of the audit, and the reason is
that the out-of-range cases are not vacuous:

* `P2 hG L S` is **satisfied** when `L > G`.  Take `G = 2`, `S = (0, 1)` and
  `L = 3`.  The first clause of `P2` needs three pairwise distinct starts, and
  the second needs four, so both are vacuous on a circle of two starts.
* `P2 hG L S` is **satisfied** when `L ≤ 1` on any word that has no interleaved
  repeat pair, for the same reason: `IsRepeat` requires `1 ≤ e`, so with
  `L - 2 = 0` the clause `e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2` can only fire when
  there is an interleaved repeat pair, and there need not be one.

I did not prove either of these two facts in Lean; they are the reason I do not
attempt option (a), and the honest statement is that the `L < 2` and `L > K`
halves of `CrossingChordsCoalesce` are **untouched and unexamined** --- not
proved, and not refuted. -/

section Bounded

variable {K : ℕ} (hK : 0 < K) (S : Fin K → α)

/-- **The bounded bridge.**  `CrossingChordsCoalesce L` restricted to the
regime `2 ≤ L` and `L ≤ K`, i.e. exactly the regime
`BBTCrossingCoalesce.CrossingPairsCoalesce L` is stated over.

The hypotheses are the ones `BBTLadder.LadderVertexCycle` already carries at
its block condition (`P2`, primitivity, `2 ≤ L`, `L ≤ K`, `Ukkonen`), so this
discharges the block half of `LadderVertexCycle` without touching its
conclusion.

The proof is short and uses no new input: the existing inhabitant
`Issue94CaseSplit.crossingPairsCoalesce_general`, the repository's own
`AltF_vtx'` (unchanged) to read off the two `(L-1)`-mer equalities, and
`Interleaved`'s own `FourDistinct` conjunct for the two distinctness clauses,
which are therefore **derived** and not assumed. -/
theorem crossingChordsCoalesce_bounded {L : ℕ} (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (h2L : 2 ≤ L) (hLK : L ≤ K) :
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d := by
  intro σ hEul a b c d hfa hba hfc hdc hac hbc had hbd hI
  have hco := Issue94CaseSplit.crossingPairsCoalesce_general (α := α) L
    K hK S h2L hLK hP2 hprim a b c d
    hI.1.1 hI.1.2.2.2.2.2
    (hfa ▸ BBTLadder.AltF_vtx' hK S hEul a).symm
    (hfc ▸ BBTLadder.AltF_vtx' hK S hEul c).symm
    hI
  exact hco

/-- **The bridge, as a corollary in the exact shape
`BBTLadder.LadderVertexCycle` needs it.**  Inside a context carrying
`P2 hK L S`, primitivity, `2 ≤ L`, `L ≤ K` and `Ukkonen hK L S` --- which is
`LadderVertexCycle`'s own context --- every **crossing** pair of support chords
of the alternative traversal `AltF hK σ` carries the same deterministic
maximal extension, as unordered pairs.  This is the whole block hypothesis of
`LadderVertexCycle`; the conclusion (`VertexCycleEq`) is untouched and still
has no inhabitant. -/
theorem support_blocks_coalesce {L : ℕ} (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S) (h2L : 2 ≤ L) (hLK : L ≤ K)
    {σ : Fin K ≃ Fin K} (hEul : EulerianCycle hK L S σ) (a b c d : Fin K)
    (hfa : AltF hK σ a = b) (hba : AltF hK σ b = a)
    (hfc : AltF hK σ c = d) (hdc : AltF hK σ d = c)
    (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d)
    (hI : Interleaved (mkGenome hK S) a b c d) :
    SameExtension K hK S a b c d :=
  crossingChordsCoalesce_bounded hK S hP2 hprim h2L hLK σ hEul a b c d
    hfa hba hfc hdc hac hbc had hbd hI

end Bounded

/-! ## 6. `LadderVertexCycle` itself

### 6.1. The block hypothesis is no longer an assumption

`BBTLadder.LadderVertexCycle` takes, as its hypothesis, that **every** crossing
pair of support chords of `AltF hK σ` coalesces.  §5.3 (`support_blocks_coalesce`)
now *derives* exactly that from the hypothesis set `LadderVertexCycle` already
carries.  So the whole block half of `LadderVertexCycle` is discharged, and
what remains of `LadderVertexCycle` is precisely:

> a support of `AltF` that is a laminar family of vertex-invisible ladder
> blocks, with the block property now derived, has the vertex listing of a
> rotation of the truth's.

That is the global traversal-order step, and §6.2 records exactly what is
still missing for it.

### 6.2. What the global step would need, stated as a `Prop` and NOT proved

`ladder_vertexCycle_of_blocks` below is the residual obligation with the block
hypothesis *already discharged*, so it is not a proxy: it is
`LadderVertexCycle` with its hypothesis replaced by something §5.3 proves.  It
is stated for the record and it has **no inhabitant** here.  Note the
conclusion is the exact `VertexCycleEq`, not a weakened listing invariant.

A proof would have to show that the traversal `i ↦ σ i` walks the laminar block
structure in geometric order, using `ladder_of_coalescing` (each block is two
rotations of one pair), `ladder_arc_eq` (a block is vertex-invisible) and
`support_blocks_nonCrossing` (blocks are laminar).  The obstruction recorded in
`BBTLadder`'s module docstring is that the tempting intermediate
`nextSupport (f x) = f (nextSupport x)` is **false** (refuted at `G = 10`), so
the assembly has to be genuinely global; a one-chord-at-a-time induction is not
available. -/

/-- **The residual obligation of `LadderVertexCycle`, with the block property
already derived.**  Identical to `BBTLadder.LadderVertexCycle` except that the
laminar-block hypothesis is *not* assumed --- it is used, and §5.3 supplies it.

**Not proved.  No inhabitant anywhere in the tree.** -/
def BlocklessLadderVertexCycle (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), P2 hK L S →
    RepeatAdapter.IsPrimitive hK S → 2 ≤ L → L ≤ K → Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

/-- **`LadderVertexCycle L` follows from `BlocklessLadderVertexCycle L`.**
§5.3 discharges the block hypothesis; this records the reduction in one place,
so that a proof of `BlocklessLadderVertexCycle` closes `LadderVertexCycle`
without further work.  The left-hand side has no inhabitant and none is
supplied. -/
theorem ladderVertexCycle_of_blockless {L : ℕ}
    (h : BlocklessLadderVertexCycle (α := α) L) :
    BBTLadder.LadderVertexCycle (α := α) L := by
  intro K hK S hP2 hprim h2L hLK hUkk σ hEul _hblocks
  exact h K hK S hP2 hprim h2L hLK hUkk σ hEul

/-! ## 7. What is NOT established -/

end AssemblyP1.Issue94TW1EdgeType
