import AssemblyP1.BBTLadder
import AssemblyP1.Issue94TransposePreserve
import AssemblyP1.Issue94Reconstruct

/-!
# Board 94, front `94fibres`: doubled `(L-1)`-mer fibres are pairwise disjoint,
# and the candidate re-pairing is a product over them

This module settles the **fibre-uniqueness** half of the
`docs/cohn-lempel-component-route-94.md` plan.  It answers one precise
question, in the form that plan's step "vertex-cycle invisibility" needs:

> **Two rung pairs that share a start are the same unordered pair.**

Under `P2` and primitivity every `(L-1)`-mer is spelled **at most twice**
(`P2.imp_nodeCount_le_two`, i.e. `R1` / `Lemma 1`), so a fibre
`nodeStartsOf hK S k` has cardinality `≤ 2`.  Two *ladder rung pairs* --- the
unordered pairs of starts of one maximal-repeat ladder --- each carry a
**common `vtx`** (`BBTLadder.DoubledPair`, whose whole content is
`vtx p = vtx q`).  So if they share a start, that start, its mate in the first
pair and its mate in the second pair are **three distinct starts of one fibre**
unless the two mates coincide --- a contradiction, and the contradiction is
exactly the multiplicity cap.

The consequence is the object this module is named for: the doubled fibres of
the truth are a **partition into two-element blocks**, so the "product over
unique doubled-fibre swaps" is a well-defined, canonical permutation of the
starts, and it does **not** matter that the character-repeat arcs of two
different doubled fibres overlap.  Overlap is a statement about the
*maximal-repeat geometry*; disjointness of the swaps is a statement about the
*fibres*, and §2 proves the latter from `nodeCount ≤ 2` alone.  The
`S = AABAB` instance of §4 is the certificate: there the two doubled fibres
`01` and `10` give the chords `{1, 3}` and `{2, 4}`, which **interleave** --- the
two character-repeat arcs overlap --- and the two transpositions are
nonetheless disjoint, commute, and their product is label preserving.

## What is proved here

* **§1** (`fibre_card_le_two`, `three_fibre_eq`) the multiplicity cap in fibre
  language, and the counting step: **three distinct starts never spell one
  `(L-1)`-mer**.  The counting is done on `nodeStartsOf` and closed by
  `nodeCount_le_two`, i.e. by `P2.imp_nodeCount_le_two`.
* **§2** (`doubledPair_ne`, `doubledPair_comm`, `doubledPair_shared`,
  `shared_of_mem`, `pair_disjoint_or_equal`, `doubledPair_disjoint`,
  `doubledPair_unique`) **the headline lemma**: two `DoubledPair`s are *either
  the same unordered pair or disjoint*, and in particular two **distinct
  doubled fibres** give **disjoint** swaps.  Everything is phrased with
  `DoubledPair` (so "rung pair" means what the ladder packet means by it) and
  proved through `nodeStartsOf` and the cap of §1.  `doubledPair_unique` is
  the other half: the pair attached to a label is a function of the label, so
  the construction of §3 needs no choice.
* **§3** (`labelPreserving_swap`, `labelPreserving_doubledPair`,
  `labelPreserving_comp`, `doubledSwaps`, `doubledSwaps_cons`,
  `doubledSwaps_bijective`, `doubledSwaps_labelPreserving`,
  `swap_trans_comm_of_disjoint`, `doubledSwapsOn`,
  `vertexCycleEq_doubledSwapsOn`, `exists_eulerianCycle_of_doubledSwaps`)
  **the product**.  §3.1 shows the product of *any* list of doubled-pair swaps
  is a **bijection preserving the `(L-1)`-mer at every start**; §3.2 shows
  transpositions attached to **disjoint** pairs **commute**, so the product over
  the *set* of doubled fibres does not depend on the order in which the fibres
  are enumerated, and deleting a subcollection --- the Cohn--Lempel component
  deletion of `docs/cohn-lempel-component-route-94.md` --- is well defined;
  §3.3 feeds the product to the reconstruction adapter of
  `AssemblyP1.Issue94Reconstruct`.
* **§4** the `S = AABAB` (`= 00101`), `L = 3` instance: two doubled pairs whose
  chords **interleave** and whose transpositions are **disjoint**, and a product
  that is a nonidentity involution.  This is the anti-vacuity check on the whole
  packet, and it is exactly the configuration
  `BBTChords.raw_node_crossing_not_maximal` exhibits.

## The recipe for the candidate `h`, and what is left of it

Let `D` be the set of doubled `(L-1)`-mers of the truth,

```text
  D = { k | (nodeStartsOf hK S k).card = 2 },
```

and for `k ∈ D` let `τ k` be the transposition exchanging the two starts of that
fibre.  Then the candidate re-pairing is

```text
  h = ∏_{k ∈ D} τ k ,
```

and this module says exactly how much of that is already formal.

1. **`τ k` is a function of `k`, not a choice.**
   `doubledPair_unique`: if `(a, b)` and `(a', b')` are both `DoubledPair`s with
   `vtx a = vtx a'`, then `{a, b} = {a', b'}`.  So enumerating the fibres and
   picking a representative start in each is not a choice that can be made
   inconsistently: the pair is forced by the label.  (The construction can
   therefore also be written *pointwise*, `h x =` the other member of
   `nodeStartsOf (vtx x)`, with no global enumeration at all; that variant is
   not formalized here.)
2. **Distinct fibres give disjoint swaps.**  `doubledPair_disjoint`: if
   `vtx a ≠ vtx a'` then `Disjoint {a, b} {a', b'}`.  So the product is a
   product of **pairwise disjoint** transpositions --- which is exactly the
   hypothesis of the Cohn--Lempel / Beck cycle-decomposition theorem that
   `docs/cohn-lempel-component-route-94.md` wants to apply.
3. **The order does not matter.**  `swap_trans_comm_of_disjoint`: transpositions
   attached to disjoint pairs commute.  Order-independence of the *whole*
   product follows by induction along the pairwise disjointness of the blocks
   and is **not** formalized here; what is formalized is the commutation step and
   the disjointness hypothesis it consumes.
4. **The product is a label-preserving bijection.**
   `doubledSwaps_bijective`, `doubledSwaps_labelPreserving`.  This is the input
   of `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`.
   Note that **disjointness is not used here**: each factor is label preserving
   on its own (`labelPreserving_doubledPair`) and label preservation composes.
   Disjointness buys the *Cohn--Lempel shape* (disjoint transpositions), not
   label preservation.
5. **The one remaining input is the single-circuit clause.**
   `exists_eulerianCycle_of_doubledSwaps` concludes `∃ σ, EulerianCycle hK L S σ`
   from the *single* hypothesis `VisitsAll (jump hK h) (origin hK)`.  **That
   hypothesis is the entire unproved content of this route**: it is the
   one-cycle condition, which is what Cohn--Lempel (1972) / Beck (1977) supply
   for a product of disjoint transpositions, via nonsingularity of the binary
   link matrix.  Nothing in this module proves it, and nothing here needs any
   genome theory to state it.
6. **Vertex-cycle invisibility is already formal and needs no disjointness.**
   `vertexCycleEq_doubledSwapsOn` (via
   `BBTTranspose.vertexCycleEq_transpositionList`): composing a
   `VertexCycleEq` listing with *any* list of transpositions at
   equal-`(L-1)`-mer starts keeps `VertexCycleEq`, with the same rotation
   witness.  Note what this does **not** say: it does not say the repair
   *removes* a component, and it does not say `h = id`.

## Relation to the neighbouring statements

* `BBTCrossingCoalesce.three_starts_ne` / `collision_forces_pair` are the same
  counting step at the level of two pairs of *equal-`vtx`* starts, with no
  `DoubledPair` hypothesis.  §1--§2 re-derive the counting against
  `nodeStartsOf`/`DoubledPair` and deliberately do **not** import
  `BBTCrossingCoalesce`, whose §5 carries two uninhabited `Prop`s;
  `doubledPair_shared` is `collision_forces_pair` read at two rung pairs, and is
  recorded here because the ladder packet's `DoubledPair` vocabulary is what §3
  consumes.
* `BBTLadder.DoubledPair` is *used*, not restated: it is the branch object of
  the condensed multigraph together with its two realisations.  §2 routes
  through the **counting** (fibres, cap, cardinality) rather than through
  `DoubledPair`'s own "only two starts" clause, so that the conclusion holds for
  the weaker hypothesis "two pairs of equal-`vtx` distinct starts" --- which is
  what a rung of a ladder is before one knows the pair is a branch object ---
  and so that the disjointness is a statement about *fibres*, usable for labels
  not yet known to be branch objects.

## Compile status

**This module has not been compiled.**  In the checkout it was written in,
`.lake/packages/mathlib` is empty and there are no build artefacts, so no
`lake build` --- not even of a single file --- is possible.  It is therefore
**not** registered in `AssemblyP1.lean`, and the registered set stays green;
registration is a required follow-up as soon as a toolchain is available.  The
kernel claims made here are claims about the Lean text, not about a checked
build; the only kernel-checked inputs are the ones it quotes.

No `sorry`, no `admit`, no new `axiom`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94DoubledFibres

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTLadder
open AssemblyP1.BBTTranspose
open AssemblyP1.Issue94Reconstruct

variable {α : Type} [DecidableEq α] {K L : ℕ} (hK : 0 < K) (S : Fin K → α)

/-- A finset containing three distinct members has cardinality `≥ 3`.  (The same
two `Finset` lemmas as the private copy in `AssemblyP1.BBTLadder`; duplicated
here so that §2 depends on nothing else from that module.) -/
private theorem card_ge_three {s : Finset (Fin K)} {a b c : Fin K}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset (Fin K)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h
    · exact h ▸ ha
    · exact h ▸ hb
    · exact h ▸ hc
  have hcard : (({a, b, c} : Finset (Fin K))).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  exact le_trans hcard.ge (Finset.card_le_card hsub)

/-- Two-element `Finset`s do not see the order of their members. -/
private theorem two_set_comm {K : ℕ} (u v : Fin K) :
    ({u, v} : Finset (Fin K)) = {v, u} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

/-! ## 1. The multiplicity cap, in fibre language -/

/-- **The multiplicity cap, read on the fibre itself.**  Under `P2` and
primitivity the fibre `nodeStartsOf hK S k` --- the set of starts spelling the
`(L-1)`-mer `k` --- has at most two members.

`P2.imp_nodeCount_le_two` (`R1` / `Lemma 1` of `docs/bbt-unique-eulerian-89.md`
§4) is stated about `nodeCount`, and `card_nodeStartsOf` identifies that count
with the cardinality of the fibre; this is the form every counting step below
uses, because what has to be bounded is the size of a *set of starts*. -/
theorem fibre_card_le_two (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (k : Fin (L - 1) → α) : (nodeStartsOf hK S k).card ≤ 2 := by
  rw [card_nodeStartsOf]
  exact P2.imp_nodeCount_le_two hK hL hLG S hprim hP2 k

/-- **A start lies in the fibre of its own label.**  `vtx` is literally
`nodeWindow`, so this is reflexivity under the filter. -/
private theorem mem_own_fibre (x : Fin K) : x ∈ nodeStartsOf hK S (vtx hK L S x) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

/-- **Three pairwise distinct starts cannot spell one `(L-1)`-mer.**  This is
the counting step, and it is the whole of the content of the multiplicity cap:
the three starts lie in the fibre of `vtx a` (`mem_own_fibre`), so the fibre has
`≥ 3` members, which `fibre_card_le_two` forbids.

Equivalently: a fibre has exactly two members whenever it has two distinct
members, so **any two doubled pairs meeting at one start are forced to
coincide** (§2). -/
theorem three_fibre_eq (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c : Fin K} (hne : a ≠ b) (hne' : a ≠ c)
    (hab : vtx hK L S a = vtx hK L S b) (hac : vtx hK L S a = vtx hK L S c) : b = c := by
  by_contra hcon
  have hbc : b ≠ c := by omega
  have hthree : 3 ≤ (nodeStartsOf hK S (vtx hK L S a)).card :=
    card_ge_three (mem_own_fibre hK S a)
      (by rw [← hab]; exact mem_own_fibre hK S b)
      (by rw [← hac]; exact mem_own_fibre hK S c)
      hne hne' hbc
  have hcap := fibre_card_le_two hK S hL hLG hprim hP2 (vtx hK L S a)
  exact absurd hthree (by omega)

/-! ## 2. Rung pairs are disjoint or equal -/

/-- **The two starts of a `DoubledPair` are distinct.**  `DoubledPair` is
`nodeCount (vtx a) = 2` together with "every start spelling `vtx a` is `a` or
`b`", so if `a = b` the fibre of `vtx a` would be `{a}`, contradicting the
multiplicity cap.  This is what makes a `DoubledPair` a genuine *pair* rather
than a one-element block. -/
theorem doubledPair_ne {a b : Fin K} (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (hd : DoubledPair (L := L) hK S a b) : a ≠ b := by
  intro hab
  have hsub : nodeStartsOf hK S (vtx hK L S a) ⊆ ({a} : Finset (Fin K)) := by
    intro z hz
    simp only [Finset.mem_singleton]
    rcases hd.2.1 z hz with hza | hzb
    · exact hza
    · exact hzb.trans hab.symm
  have hle : (nodeStartsOf hK S (vtx hK L S a)).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hcard : (nodeStartsOf hK S (vtx hK L S a)).card = 2 := by
    rw [card_nodeStartsOf, hd.1]
  omega

/-- **`DoubledPair` is symmetric in its two members.** -/
theorem doubledPair_comm {a b : Fin K} (hd : DoubledPair (L := L) hK S a b) :
    DoubledPair (L := L) hK S b a := by
  refine ⟨?_, ?_, hd.2.2.symm⟩
  · rw [hd.2.2]
  · intro x hx
    rcases hd.2.1 x (by rw [hx, hd.2.2]) with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- **A collision forces the two rung pairs to coincide.**  `DoubledPair`s
`a, b` and `c, d` with `a = c` force `b = d`.  This is the requested lemma in
its operational form: two ladder rungs that meet at a start are the *same*
unordered pair, because otherwise `a`, `b` and `d` would be three distinct
starts of the fibre of `vtx a`.

The count is done on `nodeStartsOf` and closed by `fibre_card_le_two`, i.e. by
the multiplicity cap --- not by the "only two starts" clause of `DoubledPair`;
see the module docstring for why. -/
theorem doubledPair_shared (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c d : Fin K} (h1 : DoubledPair (L := L) hK S a b)
    (h2 : DoubledPair (L := L) hK S c d) (hcoll : a = c) : b = d := by
  have hab : a ≠ b := doubledPair_ne hK S hL hLG hprim hP2 h1
  have had : a ≠ d := by rw [← hcoll]; exact doubledPair_ne hK S hL hLG hprim hP2 h2
  have hcad : vtx hK L S a = vtx hK L S d := (hcoll ▸ h2.2.2).symm
  by_cases hbd : b = d
  · exact hbd
  · have hthree : 3 ≤ (nodeStartsOf hK S (vtx hK L S a)).card :=
      card_ge_three (mem_own_fibre hK S a)
        (by rw [← h1.2.2]; exact mem_own_fibre hK S b)
        (by rw [← hcad]; exact mem_own_fibre hK S d)
        hab had hbd
    have hcap := fibre_card_le_two hK S hL hLG hprim hP2 (vtx hK L S a)
    exact absurd hthree (by omega)

/-- **A shared start forces the two unordered pairs to be equal.**  The
four-orientation form of `doubledPair_shared`: whichever way round the shared
start `x` appears in the two pairs, the pairs coincide as two-element sets. -/
theorem shared_of_mem (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c d : Fin K} (h1 : DoubledPair (L := L) hK S a b)
    (h2 : DoubledPair (L := L) hK S c d) {x : Fin K}
    (hx1 : x ∈ ({a, b} : Finset (Fin K))) (hx2 : x ∈ ({c, d} : Finset (Fin K))) :
    ({a, b} : Finset (Fin K)) = ({c, d} : Finset (Fin K)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with hxa | hxb <;> rcases hx2 with hxc | hxd
  · have hbd : b = d := doubledPair_shared hK S hL hLG hprim hP2 h1 h2 (hxa.trans hxc.symm)
    rw [hxa.trans hxc.symm, hbd]
  · have hbc : b = c := doubledPair_shared hK S hL hLG hprim hP2 h1
      (doubledPair_comm hK S h2) (hxa.trans hxd.symm)
    rw [hxa.trans hxd.symm, hbc, two_set_comm d c]
  · have had : a = d := doubledPair_shared hK S hL hLG hprim hP2
      (doubledPair_comm hK S h1) h2 (hxb.trans hxc.symm)
    rw [had, hxb.trans hxc.symm, two_set_comm d c]
  · have hac : a = c := doubledPair_shared hK S hL hLG hprim hP2 h1
      (doubledPair_comm hK S h2) (hxb.trans hxd.symm)
    rw [hxb.trans hxd.symm, hac]

/-- **The headline lemma: two rung pairs are either the same unordered pair or
they share no start at all.**

Stated at the level of the two-element blocks, which is the form the product of
§3 consumes: the doubled pairs are the blocks of a partition of `Fin K`, so
they are pairwise either identical or disjoint. -/
theorem pair_disjoint_or_equal (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c d : Fin K} (h1 : DoubledPair (L := L) hK S a b)
    (h2 : DoubledPair (L := L) hK S c d) :
    ({a, b} : Finset (Fin K)) = ({c, d} : Finset (Fin K)) ∨
      Disjoint ({a, b} : Finset (Fin K)) ({c, d} : Finset (Fin K)) := by
  by_cases heq : ({a, b} : Finset (Fin K)) = ({c, d} : Finset (Fin K))
  · exact Or.inl heq
  · refine Or.inr ?_
    intro x hx1 hx2
    exact heq (shared_of_mem hK S hL hLG hprim hP2 h1 h2 hx1 hx2)

/-- **Two *distinct* doubled fibres give disjoint swaps.**  Same conclusion as
`pair_disjoint_or_equal`, with the disjunction resolved: if the two pairs were
equal as two-element sets then they would carry the same `vtx`, hence be the
same fibre.  This is the lemma the product over the doubled fibres is built on:
the factor attached to a fibre is a transposition, and the factors attached to
different fibres have disjoint supports. -/
theorem doubledPair_disjoint (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c d : Fin K} (h1 : DoubledPair (L := L) hK S a b)
    (h2 : DoubledPair (L := L) hK S c d) (hne : vtx hK L S a ≠ vtx hK L S c) :
    Disjoint ({a, b} : Finset (Fin K)) ({c, d} : Finset (Fin K)) := by
  rcases pair_disjoint_or_equal hK S hL hLG hprim hP2 h1 h2 with heq | hdis
  · have ha : a ∈ ({c, d} : Finset (Fin K)) :=
      heq ▸ Finset.mem_insert_self a (Finset.singleton b)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with hac | had
    · exact hne (by rw [hac])
    · exact hne (by rw [had, h2.2.2])
  · exact hdis

/-- **The pair attached to a doubled fibre is a function of the fibre.**  Two
`DoubledPair`s with equal `vtx` at their first members determine the *same*
unordered pair.  Equivalently: the fibre *is* the pair, so no choice of
representative is involved in the construction of §3.

(The one step that does not go through the cap is the membership `a ∈ {a', b'}`,
which is read off `DoubledPair a' b'`'s own clause --- that clause *is* the
statement that the fibre has exactly those two members.  Everything in §2 that
compares **two** pairs, and in particular the requested
`pair_disjoint_or_equal`, is proved by counting.) -/
theorem doubledPair_unique (hL : 2 ≤ L) (hLG : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b a' b' : Fin K} (h1 : DoubledPair (L := L) hK S a b)
    (h2 : DoubledPair (L := L) hK S a' b') (h : vtx hK L S a = vtx hK L S a') :
    ({a, b} : Finset (Fin K)) = ({a', b'} : Finset (Fin K)) := by
  have hmem : a ∈ nodeStartsOf hK S (vtx hK L S a') := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact h
  refine shared_of_mem hK S hL hLG hprim hP2 h1 h2
    (Finset.mem_insert_self a (Finset.singleton b)) ?_
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact h2.2.1 a hmem

/-! ## 3. The product over the doubled-fibre swaps -/

/-! ### 3.1 Each factor is label preserving, so the product is -/

/-- **Swapping two starts that spell the same `(L-1)`-mer changes no vertex.**
This is the *pointwise* form of the hypothesis of
`BBTTranspose.vertexCycleEq_transposition`: at a start spelling the same
`(L-1)`-mer as `a`, the swap is invisible.  Note it says nothing about
interlacement, ordering, or `AltF`. -/
theorem labelPreserving_swap {a b : Fin K} (hvb : vtx hK L S a = vtx hK L S b)
    (x : Fin K) : vtx hK L S ((Equiv.swap a b : Fin K ≃ Fin K) x) = vtx hK L S x := by
  by_cases hxa : x = a
  · rw [hxa, Equiv.swap_apply_left, hvb.symm]
  by_cases hxb : x = b
  · rw [hxb, Equiv.swap_apply_right, hvb]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- **The same, for the two occurrences of one branch object**: a
`DoubledPair`'s transposition is label preserving at every start.  This is the
input of `Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single`. -/
theorem labelPreserving_doubledPair {a b : Fin K} (hd : DoubledPair (L := L) hK S a b)
    (x : Fin K) : vtx hK L S ((Equiv.swap a b : Fin K ≃ Fin K) x) = vtx hK L S x :=
  labelPreserving_swap hK S hd.2.2.symm x

/-- **Label preservation composes.**  Used to run the induction of
`doubledSwaps_labelPreserving` without any bookkeeping about the shape of the
partial product. -/
theorem labelPreserving_comp {μ ν : Fin K ≃ Fin K}
    (hμ : ∀ x : Fin K, vtx hK L S (μ x) = vtx hK L S x)
    (hν : ∀ x : Fin K, vtx hK L S (ν x) = vtx hK L S x) (x : Fin K) :
    vtx hK L S ((ν.trans μ) x) = vtx hK L S x :=
  (hμ (ν x)).trans (hν x)

/-- **The candidate re-pairing: the product of the transpositions attached to a
list of doubled pairs.**  With `ps` enumerating the doubled fibres of the truth
(this module does not build that list; §2 says any two enumerations give the
same product, up to order), `doubledSwaps ps` is the permutation that swaps the
two realisations of *every* branch vertex, simultaneously.

Right-nested, so that `doubledSwaps (p :: ps)` reduces to
`(Equiv.swap p.1 p.2).trans (doubledSwaps ps)` definitionally. -/
def doubledSwaps : List (Fin K × Fin K) → Fin K ≃ Fin K
  | [] => Equiv.refl
  | p :: ps => (Equiv.swap p.1 p.2).trans (doubledSwaps ps)

/-- **The equation of `doubledSwaps` at a cons**, in the pointwise form the
induction below uses. -/
theorem doubledSwaps_cons (p : Fin K × Fin K) (ps : List (Fin K × Fin K)) (x : Fin K) :
    doubledSwaps (p :: ps) x = doubledSwaps ps ((Equiv.swap p.1 p.2 : Fin K ≃ Fin K) x) := rfl

/-- **The product is a bijection** --- no hypothesis needed, being a product of
equivalences.  This is why disjointness is *not* needed for bijectivity; see
§3.2 for what disjointness does buy. -/
theorem doubledSwaps_bijective :
    ∀ (ps : List (Fin K × Fin K)), Function.Bijective (doubledSwaps ps) :=
  fun ps => Equiv.bijective (doubledSwaps ps)

/-- **The product preserves the `(L-1)`-mer at every start**, i.e. it is a
label-preserving permutation of the starts of the truth.  This is the `hLP`
clause of the reconstruction adapter, and it is exactly what the `traverses`
clause of `EulerianCycle` reads.

No disjointness is used: each factor is label preserving on its own
(`labelPreserving_doubledPair`) and label preservation composes
(`labelPreserving_comp`). -/
theorem doubledSwaps_labelPreserving {ps : List (Fin K × Fin K)}
    (hps : ∀ p ∈ ps, DoubledPair (L := L) hK S p.1 p.2) (x : Fin K) :
    vtx hK L S (doubledSwaps ps x) = vtx hK L S x := by
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
      have hp : DoubledPair (L := L) hK S p.1 p.2 := hps p List.mem_cons_self
      have hps' : ∀ q ∈ ps, DoubledPair (L := L) hK S q.1 q.2 := by
        intro q hq
        exact hps q (List.mem_cons_of_mem p hq)
      rw [doubledSwaps_cons p ps x]
      exact ((labelPreserving_comp hK S
        (ih (hps := hps') (x := (Equiv.swap p.1 p.2 : Fin K ≃ Fin K) x))
        (labelPreserving_doubledPair hK S hp))
        ((Equiv.swap p.1 p.2 : Fin K ≃ Fin K) x)).trans
        (labelPreserving_doubledPair hK S hp x)

/-! ### 3.2 Disjoint pairs commute: the product does not depend on the order in
which the fibres are enumerated -/

/-- **A swap is the identity off its own pair.** -/
private theorem swap_fixes_notin {a b x : Fin K} (hx : x ∉ ({a, b} : Finset (Fin K))) :
    (Equiv.swap a b : Fin K ≃ Fin K) x = x := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  have hxa : x ≠ a := fun e => hx.1 e
  have hxb : x ≠ b := fun e => hx.2 e
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- **A swap preserves its own pair.** -/
private theorem swap_maps_pair {a b x : Fin K} (hx : x ∈ ({a, b} : Finset (Fin K))) :
    (Equiv.swap a b : Fin K ≃ Fin K) x ∈ ({a, b} : Finset (Fin K)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  by_cases hxa : x = a
  · rw [hxa, Equiv.swap_apply_left]
    exact Finset.mem_insert_self _ _
  by_cases hxb : x = b
  · rw [hxb, Equiv.swap_apply_right]
    exact Finset.mem_insert_self _ _
  exact absurd hx (by simp [hxa, hxb])

/-- **Transpositions attached to disjoint pairs commute.**  Pure `Finset`
bookkeeping plus the three `Equiv.swap` equations: no word, no `P2`, no
traversal.

This is what makes the product over the *set* of doubled fibres a well-defined
object rather than a product over an arbitrary enumeration: §2 supplies the
disjointness of the blocks, this lemma supplies commutation, and together they
give order-independence --- which is what the component-deletion step of
`docs/cohn-lempel-component-route-94.md` needs in order to delete a subfamily of
the factors and still be left with a product of disjoint transpositions. -/
theorem swap_trans_comm_of_disjoint {a b c d : Fin K}
    (h : Disjoint ({a, b} : Finset (Fin K)) ({c, d} : Finset (Fin K))) :
    (Equiv.swap a b).trans (Equiv.swap c d) = (Equiv.swap c d).trans (Equiv.swap a b) := by
  ext x
  simp only [Equiv.trans_apply]
  by_cases hx : x ∈ ({a, b} : Finset (Fin K))
  · have hx2 : x ∉ ({c, d} : Finset (Fin K)) := fun hh => h hx hh
    have hfix1 : (Equiv.swap c d : Fin K ≃ Fin K) x = x := swap_fixes_notin hx2
    have hmap : (Equiv.swap a b : Fin K ≃ Fin K) x ∈ ({a, b} : Finset (Fin K)) :=
      swap_maps_pair hx
    have hfix2 : (Equiv.swap c d : Fin K ≃ Fin K) ((Equiv.swap a b : Fin K ≃ Fin K) x)
        = (Equiv.swap a b : Fin K ≃ Fin K) x := swap_fixes_notin (fun hh => h hmap hh)
    calc (Equiv.swap a b : Fin K ≃ Fin K) ((Equiv.swap c d : Fin K ≃ Fin K) x)
        = (Equiv.swap a b : Fin K ≃ Fin K) x := congrArg _ hfix1
      _ = (Equiv.swap c d : Fin K ≃ Fin K) ((Equiv.swap a b : Fin K ≃ Fin K) x) := hfix2.symm
  · by_cases hx2 : x ∈ ({c, d} : Finset (Fin K))
    · have e1 : (Equiv.swap a b : Fin K ≃ Fin K) x = x := swap_fixes_notin hx
      have hmap : (Equiv.swap c d : Fin K ≃ Fin K) x ∈ ({c, d} : Finset (Fin K)) :=
        swap_maps_pair hx2
      have e2 : (Equiv.swap a b : Fin K ≃ Fin K) ((Equiv.swap c d : Fin K ≃ Fin K) x)
          = (Equiv.swap c d : Fin K ≃ Fin K) x :=
        swap_fixes_notin (fun hh => h hh hmap)
      calc (Equiv.swap a b : Fin K ≃ Fin K) ((Equiv.swap c d : Fin K ≃ Fin K) x)
          = (Equiv.swap c d : Fin K ≃ Fin K) x := e2
        _ = (Equiv.swap c d : Fin K ≃ Fin K) ((Equiv.swap a b : Fin K ≃ Fin K) x) := by rw [e1]
    · have e1 : (Equiv.swap a b : Fin K ≃ Fin K) x = x := swap_fixes_notin hx
      have e2 : (Equiv.swap c d : Fin K ≃ Fin K) x = x := swap_fixes_notin hx2
      calc (Equiv.swap a b : Fin K ≃ Fin K) ((Equiv.swap c d : Fin K ≃ Fin K) x)
          = (Equiv.swap a b : Fin K ≃ Fin K) x := congrArg _ e2
        _ = x := e1
        _ = (Equiv.swap c d : Fin K ≃ Fin K) ((Equiv.swap a b : Fin K ≃ Fin K) x) := by rw [e1, e2]

/-! ### 3.3 The product composed into a listing, and the reconstruction adapter -/

/-- **The same product, composed into a listing.**  Left-nested, in the order
`BBTTranspose.vertexCycleEq_transpositionList` consumes. -/
def doubledSwapsOn {K : ℕ} (σ : Fin K ≃ Fin K) (ps : List (Fin K × Fin K)) :
    Fin K ≃ Fin K :=
  ps.foldl (fun τ p => τ.trans (Equiv.swap p.1 p.2)) σ

/-- **Vertex-cycle invisibility of the whole product: no disjointness
needed.**  Composing a `VertexCycleEq` listing with any list of transpositions
at equal-`(L-1)`-mer starts preserves `VertexCycleEq` with the *same* rotation
witness.  This is the formal statement of "re-pairing inside branch vertices is
invisible at the level of the vertex cycle", and it is what licenses carrying a
`VertexCycleEq` witness across the repair. -/
theorem vertexCycleEq_doubledSwapsOn {σ : Fin K ≃ Fin K} {ps : List (Fin K × Fin K)}
    (hps : ∀ p ∈ ps, DoubledPair (L := L) hK S p.1 p.2)
    (hv : VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))) :
    VertexCycleEq hK L S (doubledSwapsOn σ ps) (Equiv.refl (α := Fin K)) :=
  vertexCycleEq_transpositionList hK L S (fun p hmem => (hps p hmem).2.2.symm) hv

/-- **The product of the doubled-fibre swaps, fed to the reconstruction
adapter.**  A label-preserving bijection of the starts whose successor
`jump hK h` is a single circuit is *presented* by an `EulerianCycle`.

The single hypothesis is the whole of the remaining content of this route: it
is the one-cycle condition, which is what Cohn--Lempel / Beck supply for a
product of **disjoint** transpositions, and §2 together with
`swap_trans_comm_of_disjoint` is what makes the product here such a product.
Nothing in this module proves `hV`, and nothing in it needs genome theory to
state it. -/
theorem exists_eulerianCycle_of_doubledSwaps {ps : List (Fin K × Fin K)}
    (hps : ∀ p ∈ ps, DoubledPair (L := L) hK S p.1 p.2)
    (hV : VisitsAll (Issue94Reconstruct.jump hK (doubledSwaps ps : Fin K → Fin K))
      (origin hK)) :
    ∃ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ :=
  Issue94Reconstruct.exists_eulerianCycle_of_labelPreserving_single hK L S
    (doubledSwaps ps) (Equiv.bijective (doubledSwaps ps))
    (fun x => doubledSwaps_labelPreserving hK S hps x) hV

/-! ## 4. Anti-vacuity: `S = AABAB`, two interleaved doubled pairs -/

/-- `0 < 5`, the length of the witness of §4. -/
theorem five : 0 < 5 := by norm_num

/-- **On `S = AABAB` read at `L = 3`, the `2`-mer `01` is a doubled pair at
starts `1` and `3`.**  `decide`, i.e. kernel-checked: `nodeCount (vtx 1) = 2`,
the only starts spelling `vtx 1` are `1` and `3`, and `vtx 3 = vtx 1`. -/
theorem cex_doubledPair_13 :
    DoubledPair (L := 3) five P2RepeatResidual.cexWord (1 : Fin 5) 3 := by
  decide

/-- **... and `10` is a doubled pair at starts `2` and `4`.** -/
theorem cex_doubledPair_24 :
    DoubledPair (L := 3) five P2RepeatResidual.cexWord (2 : Fin 5) 4 := by
  decide

/-- **... and the two chords interleave.**  The *character-repeat arcs* of the
two doubled fibres overlap.  This is the configuration that
`BBTChords.raw_node_crossing_not_maximal` exhibits, and the reason a "the
doubled-pair arcs are disjoint" reading is unavailable.

The word is a primitive `P2` truth (`P2RepeatResidual.cex_is_shiftPrimitive`,
`P2RepeatResidual.cex_is_p2`), so every hypothesis of §2 holds. -/
theorem cex_chords_interleave : InterleavedStarts (hG := five)
    (1 : Fin 5) 3 2 4 := by
  decide

/-- **... yet the two transpositions are disjoint.**  The two fibre swaps of §3
have **disjoint supports** although their arcs **interleave**.  This is the
content of the module in one line: the arcs may overlap, the supports cannot.

This is `doubledPair_disjoint` at the repository's own primitive `P2` witness,
with `hne` discharged by `decide`. -/
theorem cex_pairs_disjoint :
    Disjoint ({1, 3} : Finset (Fin 5)) ({2, 4} : Finset (Fin 5)) :=
  doubledPair_disjoint (K := 5) (L := 3) five P2RepeatResidual.cexWord
    (by norm_num) (by norm_num) P2RepeatResidual.cex_is_shiftPrimitive
    P2RepeatResidual.cex_is_p2 cex_doubledPair_13 cex_doubledPair_24 (by decide)

/-- **... and the two transpositions commute**, which is what makes the product
over the *set* of doubled fibres independent of the enumeration order. -/
theorem cex_pairs_commute :
    (Equiv.swap (1 : Fin 5) 3).trans (Equiv.swap 2 4)
      = (Equiv.swap 2 4).trans (Equiv.swap 1 3) :=
  swap_trans_comm_of_disjoint cex_pairs_disjoint

/-- **The product of the two fibre swaps is not the identity**: on this witness
the candidate re-pairing genuinely re-pairs. -/
theorem cex_doubledSwaps_ne :
    doubledSwaps [((1 : Fin 5), 3), (2, 4)] ≠ Equiv.refl (α := Fin 5) := by
  decide

/-! ## 5. Axiom audit -/

#print axioms AssemblyP1.Issue94DoubledFibres.fibre_card_le_two
#print axioms AssemblyP1.Issue94DoubledFibres.three_fibre_eq
#print axioms AssemblyP1.Issue94DoubledFibres.doubledPair_ne
#print axioms AssemblyP1.Issue94DoubledFibres.doubledPair_comm
#print axioms AssemblyP1.Issue94DoubledFibres.doubledPair_shared
#print axioms AssemblyP1.Issue94DoubledFibres.shared_of_mem
#print axioms AssemblyP1.Issue94DoubledFibres.pair_disjoint_or_equal
#print axioms AssemblyP1.Issue94DoubledFibres.doubledPair_disjoint
#print axioms AssemblyP1.Issue94DoubledFibres.doubledPair_unique
#print axioms AssemblyP1.Issue94DoubledFibres.labelPreserving_swap
#print axioms AssemblyP1.Issue94DoubledFibres.labelPreserving_doubledPair
#print axioms AssemblyP1.Issue94DoubledFibres.labelPreserving_comp
#print axioms AssemblyP1.Issue94DoubledFibres.doubledSwaps_cons
#print axioms AssemblyP1.Issue94DoubledFibres.doubledSwaps_bijective
#print axioms AssemblyP1.Issue94DoubledFibres.doubledSwaps_labelPreserving
#print axioms AssemblyP1.Issue94DoubledFibres.swap_trans_comm_of_disjoint
#print axioms AssemblyP1.Issue94DoubledFibres.doubledSwapsOn
#print axioms AssemblyP1.Issue94DoubledFibres.vertexCycleEq_doubledSwapsOn
#print axioms AssemblyP1.Issue94DoubledFibres.exists_eulerianCycle_of_doubledSwaps
#print axioms AssemblyP1.Issue94DoubledFibres.cex_doubledPair_13
#print axioms AssemblyP1.Issue94DoubledFibres.cex_doubledPair_24
#print axioms AssemblyP1.Issue94DoubledFibres.cex_chords_interleave
#print axioms AssemblyP1.Issue94DoubledFibres.cex_pairs_disjoint
#print axioms AssemblyP1.Issue94DoubledFibres.cex_pairs_commute
#print axioms AssemblyP1.Issue94DoubledFibres.cex_doubledSwaps_ne

end AssemblyP1.Issue94DoubledFibres
