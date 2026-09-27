import AssemblyP1.P2
import AssemblyP1.RepeatAdapter
import AssemblyP1.PopulationReduction
import AssemblyP1.BBTChords

/-!
# The condensed `(L-1)`-mer graph of `thm:BBT` (issue #89), and the #89
# traversal-choice lemma on it

`paper/sections/05-population.tex`, `thm:BBT`, states the external
uniqueness input as follows (Bresler--Bresler--Tse 2013, *Optimal assembly
for high throughput shotgun sequencing*, Theorem 3):

> Construct the `K`-mer graph from the complete `(K+1)`-spectrum of a
> circular genome. If the genome satisfies Ukkonen's condition --- no triple
> repeat and no interleaved repeat pair of length at least `K` --- then the
> graph has a unique Eulerian cycle, which spells the genome up to cyclic
> rotation.

Theorem 3 is a statement about the **condensed sequence graph**: the
`(K+1)`-mer multigraph is built from the spectrum, *unambiguous paths are
contracted*, and what is left is a graph whose vertices are the branch
objects (nodes of multiplicity `≥ 2`) together with the maximal
unambiguous segments joining them; the theorem then asserts a *unique
Eulerian cycle* of that condensed graph.  The uniqueness is therefore
localized at the branch objects, and the `#89` route (chords / local
rematching of truth boundary occurrences) is an attempt to reproduce the
unique-Eulerian-cycle step on the un-condensed word layer.

This module encodes the source's architecture **directly on the de Bruijn
multigraph of the word**, rather than introducing a bespoke block concept:

* §1 is the multigraph layer: the vertex of start `r` is its `(L-1)`-mer
  (`vtx hG L S r`), its out-degree is the `(L-1)`-mer multiplicity
  (`deg hG L S v` = `nodeCount`), and the in-degree equals the out-degree
  (`inDeg_eq_deg`).  `Branch hG L S v` is the source's condensed-vertex
  predicate --- a vertex of multiplicity `≥ 2` --- `branchStarts hG L S` its
  occurrences, `branchVerts hG L S` the condensed vertex set, and
  `branchStarts_eq_biUnion` the disjoint-union bookkeeping of the occurrences
  over that set.  Sums over *all* vertices are deliberately avoided: the vertex
  type `Fin (L-1) → α` is not a `Fintype` for an arbitrary symbol type `α`, so
  a "total degree" sum is not even expressible;
  `card_branchStarts_le_two_mul_branchVerts` bounds the branch occurrences by
  twice the number of condensed vertices under the multiplicity cap.
* §2 is "no choice at an unambiguous vertex", at the strength actually
  needed: an occurrence of a vertex of degree `≤ 1` is uniquely determined
  by the vertex, hence by the word.  `P1` of `def:P1P2` is named here.
* §3 is the **traversal-choice dichotomy** for an alternative Eulerian
  traversal, i.e. the `#89` rematching, in the source's terms.  A
  `BBTChords.Matching` between the truth and a candidate is the pull-back of
  the candidate's cyclic order to the truth's starts; §3 proves that both
  traversals enter the *same vertex* at every start (`match_next_vtx`),
  that there is therefore **no choice at an unambiguous vertex**
  (`forced_at_unambiguous`), and conversely that any place where the
  alternative traversal *departs* from the truth is an occurrence of a
  **branch object** (`choices_only_at_branch`), with the departures
  counted by `card_choices_le_branchStarts` and, under a multiplicity cap,
  `card_choices_le_two_mul_branchVerts`.  This is the sense in which alternate
  Eulerian choices occur only at condensed branch objects.
* §4 closes the whole `thm:BBT` conclusion for the branch-free stratum of
  words --- `P1`, the project's stronger admissibility condition, in which
  no length-`L-1` word occurs more than once:
  `spectrum_unique_of_P1` is the complete-spectrum uniqueness theorem,
  kernel-checked, in that stratum.  The key ingredient is
  `isRotation_of_step`: a map of the circle that advances by one position
  at a time is a rotation.
* §5 is a kernel-checked sanity instance, `condense_sanity_00101`,
  recording why the notions of "condensed object" and "maximal repeat"
  must not be collapsed into one another: for `S = 00101` at `L = 3` the
  branch objects are the two repeated length-`2` mers, the segment leaving
  a branch occurrence is *degenerate* (the next vertex is a branch vertex
  again, so no contraction is available), and simultaneously the word has
  a maximal repeat of length `3` that is **not** a branch object.  So the
  `S = 00101` counterexample of
  `AssemblyP1.BBTChords.raw_node_crossing_not_maximal` is not an artifact
  of a wrong object choice: branch objects and maximal repeats are
  different objects, and §3 uses only the first.

The abstract chord lemma of `AssemblyP1.BBTChords` and the
equal-spectrum matching adapter (`exists_matching`,
`matching_rotation_imp`) are reused unchanged.

## What this module does not do

§4 proves `thm:BBT`'s conclusion only for words with no branch object at
all (the `P1` stratum).  For a word that *has* branch objects, §3 confines
the alternative traversals to the branch occurrences and bounds how many
there are, but the uniqueness of the Eulerian cycle of the condensed graph
is *not* proved.  Following Bresler's dissertation (Appendix B), the
remaining input is Pevzner 1995, Lemma 9 --- the **known-multiplicity**
direction, which is exactly the setting here, since the complete spectrum
supplies all edge multiplicities:

```text
remaining: a non-rotational, read-type-preserving permutation of the
           starts (the pull-back of an equal-spectrum matching) that is
           not the pull-back of a rotation either interleaves two maximal
           repeats of length ≥ L-1, or forces a maximal triple repeat of
           length ≥ L-1.
```

P2 forbids both, so that single statement would close `BBTUniqueAt` in the
`2 ≤ L`, `3 ≤ G` regime.  It is *not* proved here, and the chord lemma of
`AssemblyP1.BBTChords` does not by itself supply it: that lemma needs an
*involution*, and the pull-back of a matching is only known to be a
permutation.  Note also that all statements above are about permutations
(`Equiv`/bijections) that preserve read types; a version for arbitrary start
maps is false, and a sibling audit produced the counterexample `S = 0001`,
`G = 4`, `L = 3` (primitive and `P2`, yet admitting a constant start map).
No `sorry`, no `admit`, no new axiom.
-/

namespace AssemblyP1.BBTSequenceGraph

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords

/-! ## 1. The `(L-1)`-mer multigraph and its condensation data

The `K`-mer graph of `thm:BBT` at `K = L-1`, on the truth's starts: vertex
`v : Fin (L-1) → α` is the `(L-1)`-mer, and the *occurrences* of `v` are
the starts realising it.  Occurrence count is the throughput, and
`BBTChords.nodeStartsOf` / `nodeCount` are already the repository's
definition of it; nothing new about words is introduced here.

Every parameter is explicit, because `L` and the word `S` do not occur in
the *types* of these objects and would otherwise be unsolvable implicit
metavariables. -/

section Condense

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- Two members of a finset of cardinality at most one are equal: the
elementary step behind "a vertex of multiplicity `≤ 1` has a unique
occurrence". -/
theorem card_le_one_unique {α' : Type} (s : Finset α') (h : s.card ≤ 1)
    {a b : α'} (ha : a ∈ s) (hb : b ∈ s) : a = b :=
  Finset.card_le_one.mp h a ha b hb

/-- A finset of cardinality at least two contains two distinct members. -/
theorem two_of_card_ge_two {α' : Type} [DecidableEq α'] {s : Finset α'}
    (h : 2 ≤ s.card) : ∃ a b : α', a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  by_cases hex : ∃ a b : α', a ∈ s ∧ b ∈ s ∧ a ≠ b
  · exact hex
  · have h1 : ∀ a b : α', a ∈ s → b ∈ s → a = b := by
      intro a b ha hb
      by_cases hne : a = b
      · exact hne
      · exact absurd (hex ⟨a, b, ha, hb, hne⟩) (by simp)
    have h2 : s.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => h1 a b ha hb)
    omega

omit [DecidableEq α] in
/-- Cyclic access ignores whole turns of the circle. -/
theorem cycl_add_mul (W : Fin G → α) (i n : ℕ) : cyc hG W (i + G * n) = cyc hG W i := by
  simp only [cyc]
  congr 1
  apply Fin.ext
  exact Nat.add_mul_mod_self_left i G n

omit [DecidableEq α] in
/-- **Sliding a window by one position.**  The `j`-th symbol of the
length-`L` window at `r` is the `(j+1)`-st symbol of the window at
`nextPos r`; the overlap identity used throughout §3. -/
theorem window_next (hG : 0 < G) {L : ℕ} (W : Fin G → α) (r : Fin G) {j : ℕ}
    (hj : j + 1 < L) :
    window (L := L) hG W r ⟨j + 1, by omega⟩
      = window (L := L) hG W (nextPos hG r) ⟨j, by omega⟩ := by
  simp only [window, nextPos, rotAdd, Fin.val_mk]
  have hdiv := Nat.mod_add_div (r.val + 1) G
  have e : r.val + (j + 1) = ((r.val + 1) % G + j) + G * ((r.val + 1) / G) := by omega
  rw [e, cycl_add_mul hG W]

/-- The vertex of the `(L-1)`-mer graph at start `r`: the `(L-1)`-mer
spelled at `r`.  This is `BBTChords.nodeWindow` verbatim, i.e. the index
of `BBTChords.nodeStartsOf`. -/
def vtx (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r : Fin G) : Fin (L - 1) → α :=
  nodeWindow (L := L) hG S r

/-- The out-degree of the vertex `v`: the number of occurrences of the
`(L-1)`-mer `v`, i.e. the number of edges of the multigraph leaving `v`
(= `BBTChords.nodeCount`, the throughput). -/
def deg (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v : Fin (L - 1) → α) : ℕ :=
  nodeCount (L := L) hG S v

/-- The in-degree of the vertex `v`: the number of occurrences of `v` at
which an edge *ends*, i.e. at a start whose preceding vertex is `v`.
Balanced with `deg` by `inDeg_eq_deg`. -/
def inDeg (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v : Fin (L - 1) → α) : ℕ :=
  (Finset.univ.filter (fun r : Fin G => vtx hG L S (prevPos hG r) = v)).card

/-- `v` is a **branch object** of the condensation: a vertex of
multiplicity `≥ 2`, i.e. a place where an Eulerian traversal of the
multigraph has a genuine choice of continuation.  The unambiguous vertices
(`deg v ≤ 1`) are the ones the condensation contracts away. -/
def Branch (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v : Fin (L - 1) → α) : Prop :=
  2 ≤ deg hG L S v

/-- The starts realising the vertex `v`; the fibre of `deg`. -/
def fibre (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v : Fin (L-1) → α) : Finset (Fin G) :=
  nodeStartsOf hG S v

theorem card_fibre (v : Fin (L-1) → α) : (fibre hG L S v).card = deg hG L S v :=
  card_nodeStartsOf hG S v

theorem mem_fibre {v : Fin (L-1) → α} {r : Fin G} :
    r ∈ fibre hG L S v ↔ vtx hG L S r = v := by
  simp [fibre, nodeStartsOf, vtx]

instance (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v : Fin (L-1) → α) :
    Decidable (Branch hG L S v) := by
  unfold Branch deg
  infer_instance

/-- The occurrences of branch objects: the condensed vertices of `thm:BBT`
as *positions*, i.e. the starts at which the traversal of the multigraph
can branch. -/
def branchStarts (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => Branch hG L S (vtx hG L S r))

/-- **The one-step rotation of the circle is injective.** -/
theorem nextPos_inj : Function.Injective (nextPos hG : Fin G → Fin G) := by
  intro a b heq
  have h : (a.val + 1) % G = (b.val + 1) % G := by
    simpa only [nextPos, rotAdd, Fin.val_mk] using congrArg Fin.val heq
  have ha1 : a.val + 1 ≤ G := by omega
  rcases ha1.lt_or_eq with ha | ha
  · rw [Nat.mod_eq_of_lt ha] at h
    by_cases hb : b.val + 1 < G
    · rw [Nat.mod_eq_of_lt hb] at h
      exact Fin.ext (by omega)
    · have hb' : b.val + 1 = G := by omega
      rw [hb', Nat.mod_self] at h
      omega
  · rw [ha, Nat.mod_self] at h
    by_cases hb : b.val + 1 < G
    · rw [Nat.mod_eq_of_lt hb] at h
      omega
    · have hb' : b.val + 1 = G := by omega
      exact Fin.ext (by omega)

/-- **The one-step rotation of the circle is a bijection**: stepping
forward then backward returns to the same start. -/
theorem nextPrev_val (x : Fin G) : ((x.val + G - 1) % G + 1) % G = x.val := by
  by_cases hx : x.val = 0
  · rw [hx]
    show ((0 + G - 1) % G + 1) % G = 0
    rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : G - 1 < G),
      Nat.sub_add_cancel (by omega : 1 ≤ G), Nat.mod_self]
  · have h2 : x.val + G - 1 = (x.val - 1) + G * 1 := by omega
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_add_mod,
      show x.val - 1 + 1 = x.val by omega, Nat.mod_eq_of_lt x.isLt]

theorem nextPrev (x : Fin G) : nextPos hG (prevPos hG x) = x := by
  apply Fin.ext
  simp only [nextPos, prevPos, rotAdd, Fin.val_mk]
  exact nextPrev_val x

theorem prevNext_val (x : Fin G) : ((x.val + 1) % G + G - 1) % G = x.val := by
  by_cases hlt : x.val + 1 < G
  · rw [Nat.mod_eq_of_lt hlt]
    have h2 : x.val + 1 + G - 1 = x.val + G := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
  · have hge : x.val + 1 = G := by omega
    rw [hge, Nat.mod_self, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega : G - 1 < G)]
    omega

theorem prevNext (x : Fin G) : prevPos hG (nextPos hG x) = x := by
  apply Fin.ext
  simp only [nextPos, prevPos, rotAdd, Fin.val_mk]
  exact prevNext_val x

/-- **Balance of the multigraph.**  The in-degree of a vertex equals its
out-degree: the vertices entered at the starts `r` and the vertices
entered at the starts `prevPos r` are the same family, reindexed by the
rotation of the circle.  This is the balance observation used in the proof
sketch of `lem:scaling` in `paper/sections/05-population.tex`, as a
statement about the truth. -/
theorem inDeg_eq_deg (v : Fin (L-1) → α) : inDeg hG L S v = deg hG L S v := by
  unfold inDeg
  calc (Finset.univ.filter (fun r : Fin G => vtx hG L S (prevPos hG r) = v)).card
      = (Finset.univ.filter (fun r : Fin G => vtx hG L S r = v)).card := by
        refine Finset.card_bij (fun r _ => prevPos hG r) ?_ ?_ ?_
        · intro a ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp ha).2⟩
        · intro a₁ ha₁ a₂ ha₂ heq
          have h2 := congrArg (nextPos hG) heq
          simpa only [nextPrev] using h2
        · intro b hb
          refine ⟨nextPos hG b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [prevNext hG b]
            exact (Finset.mem_filter.mp hb).2
          · exact prevNext hG b
    _ = deg hG L S v := by
        have heq : (Finset.univ.filter (fun r : Fin G => vtx hG L S r = v))
            = fibre hG L S v := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (mem_fibre hG L S).symm
        rw [heq, card_fibre]

/-- In particular no vertex has degree larger than the circle. -/
theorem deg_le (v : Fin (L-1) → α) : deg hG L S v ≤ G := by
  have h1 : (fibre hG L S v).card ≤ (Finset.univ : Finset (Fin G)).card :=
    Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin G)).card = G := by simp
  rw [← card_fibre]
  omega

/-- **Every branch object is a repeated `(L-1)`-mer**: `Branch v` gives two
distinct starts spelling the same length-`K` word.  (Maximality is *not*
claimed: a maximal repeat is a different object, see §5.) -/
theorem branch_has_two_occurrences (v : Fin (L-1) → α) (h : Branch hG L S v) :
    ∃ a b : Fin G, a ≠ b ∧ vtx hG L S a = v ∧ vtx hG L S b = v := by
  have h2 : 2 ≤ (fibre hG L S v).card := by rw [card_fibre]; exact h
  obtain ⟨a, b, ha, hb, hab⟩ := two_of_card_ge_two (s := fibre hG L S v) h2
  exact ⟨a, b, hab, (mem_fibre hG L S).mp ha, (mem_fibre hG L S).mp hb⟩

/-- ... in particular a branch object is realised at some start. -/
theorem occ_of_branch (v : Fin (L-1) → α) (h : Branch hG L S v) :
    ∃ r : Fin G, vtx hG L S r = v := by
  obtain ⟨a, b, hab, ha, hb⟩ := branch_has_two_occurrences hG L S v h
  exact ⟨b, hb⟩

/-- **The condensed vertex set of `thm:BBT`**: the distinct branch
vertices, i.e. the vertices of the condensed graph.  It is the *image* of
the branch occurrences, so it is a finset of vertices even though the
vertex type `Fin (L-1) → α` is not a `Fintype` (the symbol type `α` is
arbitrary). -/
def branchVerts (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Finset (Fin (L - 1) → α) :=
  (branchStarts hG L S).image (vtx hG L S)

theorem mem_branchVerts_iff {v : Fin (L-1) → α} :
    v ∈ branchVerts hG L S ↔ Branch hG L S v := by
  simp only [branchVerts, branchStarts, Finset.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact Finset.mem_filter.mp hr |>.2
  · intro hv
    obtain ⟨r, hr⟩ := occ_of_branch hG L S v hv
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, by rw [hr]; exact hv⟩, hr⟩

/-- A branch object is a condensed vertex. -/
theorem mem_branchVerts {v : Fin (L-1) → α} (h : Branch hG L S v) :
    v ∈ branchVerts hG L S :=
  (mem_branchVerts_iff hG L S (v := v)).mpr h

/-- ... and conversely. -/
theorem isBranch_of_mem_branchVerts {v : Fin (L-1) → α}
    (h : v ∈ branchVerts hG L S) : Branch hG L S v :=
  (mem_branchVerts_iff hG L S (v := v)).mp h

/-- **The branch occurrences are the disjoint union of the fibres of the
condensed vertices**: `branchStarts = ⨆ v ∈ branchVerts, fibre v`.  This is
the bookkeeping that makes "choices happen only at branch objects"
quantitative, and it is stated over the condensed vertex set rather than
over all vertices (the vertex type is not a `Fintype`). -/
theorem branchStarts_eq_biUnion :
    branchStarts hG L S
      = (branchVerts hG L S).biUnion (fun v => fibre hG L S v) := by
  ext r
  constructor
  · intro hr
    refine Finset.mem_biUnion.mpr ⟨vtx hG L S r, ?_, ?_⟩
    · rw [mem_branchVerts_iff hG L S (v := vtx hG L S r)]
      exact (Finset.mem_filter.mp hr).2
    · exact (mem_fibre hG L S).mpr rfl
  · intro hr
    obtain ⟨v, hv, hvr⟩ := Finset.mem_biUnion.mp hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ r, ?_⟩
    rw [(mem_fibre hG L S).mp hvr]
    exact isBranch_of_mem_branchVerts hG L S hv

/-- **Multiplicity bound for the condensation.**  Under the multiplicity cap
of P2's triple-repeat clause (`∀ v, deg v ≤ 2`) the branch occurrences are
at most twice the number of condensed vertices. -/
theorem card_branchStarts_le_two_mul_branchVerts
    (hcap : ∀ v : Fin (L-1) → α, deg hG L S v ≤ 2) :
    (branchStarts hG L S).card ≤ 2 * (branchVerts hG L S).card := by
  calc (branchStarts hG L S).card
      = ((branchVerts hG L S).biUnion (fun v => fibre hG L S v)).card := by
        rw [branchStarts_eq_biUnion]
    _ = ∑ v ∈ branchVerts hG L S, (fibre hG L S v).card := by
        apply Finset.card_biUnion
        intro u _ w _ hne
        refine Finset.disjoint_left.mpr (fun r hr1 hr2 => ?_)
        simp only [mem_fibre hG L S] at hr1 hr2
        exact absurd (hr1.symm.trans hr2) hne
    _ ≤ ∑ _v ∈ branchVerts hG L S, 2 := by
        apply Finset.sum_le_sum
        intro v hv
        rw [card_fibre]
        exact hcap v
    _ = 2 * (branchVerts hG L S).card := by
        simp [Finset.sum_const, Nat.mul_comm]

end Condense

/-! ## 2. No choice at an unambiguous vertex -/

section Unambiguous

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **An unambiguous vertex has a unique occurrence.**  If two starts spell
the same vertex of degree `≤ 1`, they are the same start.  In the source's
terms: at a vertex of multiplicity one the `K`-mer multigraph offers no
choice of continuation, so the next vertex of the traversal is determined
by the word. -/
theorem occ_unique (v : Fin (L-1) → α) (hdeg : deg hG L S v ≤ 1)
    {a b : Fin G} (ha : vtx hG L S a = v) (hb : vtx hG L S b = v) :
    a = b := by
  have hcard : (fibre hG L S v).card ≤ 1 := by
    rw [card_fibre]
    exact hdeg
  exact card_le_one_unique (fibre hG L S v) hcard
    ((mem_fibre hG L S).mpr ha) ((mem_fibre hG L S).mpr hb)

/-- The contrapositive, in the form the traversal dichotomy consumes: two
*distinct* occurrences of a vertex force it to be a branch object. -/
theorem deg_two_of_occ_ne (v : Fin (L-1) → α) {a b : Fin G} (hab : a ≠ b)
    (ha : vtx hG L S a = v) (hb : vtx hG L S b = v) :
    Branch hG L S v := by
  by_contra hn
  have hdeg : deg hG L S v ≤ 1 := by
    unfold Branch deg at hn
    unfold deg
    omega
  exact hab (occ_unique hG L S v hdeg ha hb)

/-- **`P1` of `def:P1P2`, in the multigraph language:** no length-`L-1`
word of the word occurs more than once, i.e. the `(L-1)`-mer multigraph
has no branch object at all, and every vertex is contractible. -/
def P1 (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ v : Fin (L - 1) → α, BBTSequenceGraph.deg hG L S v ≤ 1

end Unambiguous

set_option maxHeartbeats 800000

/-! ## 3. The alternative Eulerian traversal: choices live at branch objects

A `BBTChords.Matching` between the truth and a candidate is exactly the
pull-back of the candidate's cyclic order to the truth's starts: the
candidate's read at start `r` is the truth's read at start `σ r`, so the
candidate's *successor* of `r` is compared with the truth's successor of
`σ r`.  Both are starts of the truth, and `match_next_vtx` shows both spell
the same vertex of the `(L-1)`-mer graph; the only question is whether they
are the same start. -/

section Traversal

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S E : Fin G → α)

/-- **The candidate-to-truth map of the matching.**  A
`BBTChords.Matching` `σ` matches the truth's read at `r` with the
candidate's read at `σ r`; `pullback` is the converse bijection, which sends
a candidate start to the truth start carrying the same read. -/
noncomputable def pullback (_hG : 0 < G) (_L : ℕ) (_S _E : Fin G → α)
    {σ : Fin G → Fin G} (hσ : Function.Bijective σ) : Fin G ≃ Fin G :=
  (Equiv.ofBijective σ hσ).symm

theorem pullback_window {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (s : Fin G) :
    window (L := L) hG S (pullback hG L S E hm.1 s) = window (L := L) hG E s := by
  have hp := hm.2 (pullback hG L S E hm.1 s)
  have hsp : σ (pullback hG L S E hm.1 s) = s :=
    Equiv.apply_symm_apply (Equiv.ofBijective σ hm.1) s
  rw [hsp] at hp
  exact hp

theorem pullback_bij {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ) :
    Function.Bijective (pullback hG L S E hm.1) :=
  (Equiv.ofBijective σ hm.1).symm.bijective

/-- **The pull-back is a genuine permutation of the circle.**  It is an
`Equiv`, hence injective, so none of the degenerate start maps (a constant
map, for instance) can occur here: the #89 traversal-choice argument is
about permutations that preserve read types, and the pull-back is exactly
such a permutation.  This is the point at which the equal-spectrum
`Matching` --- which is a bijection --- is used, and it is why no
"arbitrary start map" version of the argument is even meaningful. -/
theorem pullback_isEquiv {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ) :
    Nonempty (Fin G ≃ Fin G) :=
  ⟨pullback hG L S E hm.1⟩

/-- ... and injectivity alone rules out a constant map, which is the
degenerate shape the sibling audit exhibited for `S = 0001`, `G = 4`,
`L = 3`.  No fixed-point assumption is used or needed. -/
theorem not_const_of_injective {f : Fin G → Fin G} (hG2 : 2 ≤ G)
    (hf : Function.Injective f) :
    ¬ ∃ c : Fin G, ∀ x, f x = c := by
  rintro ⟨c, hc⟩
  have h1 : 1 < G := by omega
  have hne : (⟨0, by omega⟩ : Fin G) ≠ (⟨1, h1⟩ : Fin G) := by
    intro he
    have hz : (0 : ℕ) = 1 := congrArg Fin.val he
    omega
  exact hne (hf ((hc (⟨0, by omega⟩)).trans (hc (⟨1, h1⟩)).symm))

/-- **The truth's start of the candidate's read at `s`. -/
noncomputable def truthStart (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ) (s : Fin G) : Fin G :=
  pullback hG L S E hm.1 s

/-- **The truth's start of the candidate's *next* read at `s`. -/
noncomputable def altStart (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ) (s : Fin G) : Fin G :=
  pullback hG L S E hm.1 (nextPos hG s)

/-- **Both traversals enter the same vertex.**  The vertex entered by the
candidate's traversal at `s` is the vertex entered by the truth's traversal
at the truth start carrying the candidate's read at `s`.  This is the
multigraph restatement of "the two traversals of the same `K`-mer
multigraph agree on the vertices", and it is the #89 "the induced
permutation preserves the `(L-1)`-mer" statement. -/
theorem match_next_vtx {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (s : Fin G) :
    vtx hG L S (altStart hG L S E hm s) = vtx hG L S (nextPos hG (truthStart hG L S E hm s)) := by
  funext d
  have hdL : d.val + 1 < L := by
    have := d.isLt
    omega
  have hdI : d.val < L := by omega
  have hA := congrFun (pullback_window hG L S E hm (nextPos hG s)) ⟨d.val, hdI⟩
  have hBfull := window_next hG (L := L) E s hdL
  have hC := congrFun (pullback_window hG L S E hm s) ⟨d.val + 1, hdL⟩
  have hDfull := window_next hG (L := L) S (truthStart hG L S E hm s) hdL
  simp only [vtx, nodeWindow, window, altStart, truthStart] at hA hBfull hC hDfull ⊢
  exact hA.trans (hBfull.symm.trans (hC.symm.trans hDfull))

/-- **No choice at an unambiguous vertex.**  If the vertex entered by the
truth's traversal is not a branch object, the two traversals are forced to
agree there: the truth start of the candidate's next read *is* the truth's
next start. -/
theorem forced_at_unambiguous {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (s : Fin G)
    (hdeg : deg hG L S (vtx hG L S (nextPos hG (truthStart hG L S E hm s))) ≤ 1) :
    altStart hG L S E hm s = nextPos hG (truthStart hG L S E hm s) := by
  have hcard : (fibre hG L S (vtx hG L S (nextPos hG (truthStart hG L S E hm s)))).card
      ≤ 1 := by
    rw [card_fibre]
    exact hdeg
  refine card_le_one_unique
    (fibre hG L S (vtx hG L S (nextPos hG (truthStart hG L S E hm s)))) hcard ?_ ?_
  · exact (mem_fibre hG L S).mpr (match_next_vtx hG L S E hm s)
  · exact (mem_fibre hG L S).mpr rfl

/-- **Traversals differ only at branch objects.**  If the alternative
Eulerian traversal departs from the truth at `s`, then the vertex entered
by the truth's traversal there is a branch object: this is the #89
"rematching happens only at the condensed branch objects" statement, in
the exact form the word layer supports. -/
theorem choices_only_at_branch {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    {s : Fin G} (hdiff : altStart hG L S E hm s ≠ nextPos hG (truthStart hG L S E hm s)) :
    Branch hG L S (vtx hG L S (nextPos hG (truthStart hG L S E hm s))) := by
  by_contra hn
  have hdeg : deg hG L S (vtx hG L S (nextPos hG (truthStart hG L S E hm s))) ≤ 1 := by
    unfold Branch deg at hn
    unfold deg
    omega
  exact hdiff (forced_at_unambiguous hG L S E hm s hdeg)

/-- The starts at which the alternative traversal departs from the truth. -/
noncomputable def choiceSet (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ) : Finset (Fin G) :=
  Finset.univ.filter (fun s : Fin G =>
    altStart hG L S E hm s ≠ nextPos hG (truthStart hG L S E hm s))

/-- **The departures inject into the branch occurrences.**  Hence an
alternative traversal has at most as many choice points as the condensed
graph has branch vertices. -/
theorem card_choices_le_branchStarts {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) :
    (choiceSet hG L S E hm).card ≤ (branchStarts hG L S).card := by
  have hinj : Function.Injective
      (fun s : Fin G => nextPos hG (truthStart hG L S E hm s)) := by
    intro a b heq
    exact (pullback_bij hG L S E hm).1 (nextPos_inj hG heq)
  have hsub : (choiceSet hG L S E hm).image
      (fun s : Fin G => nextPos hG (truthStart hG L S E hm s))
      ⊆ branchStarts hG L S := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      choices_only_at_branch hG L S E hm (Finset.mem_filter.mp hs).2⟩
  calc (choiceSet hG L S E hm).card
      = ((choiceSet hG L S E hm).image
          (fun s : Fin G => nextPos hG (truthStart hG L S E hm s))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (branchStarts hG L S).card := Finset.card_le_card hsub

/-- **Total count bound.**  The number of alternative-traversal choice
points is at most the number of branch occurrences, hence at most `G`. -/
theorem card_choices_le_card {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) :
    (choiceSet hG L S E hm).card ≤ G := by
  calc (choiceSet hG L S E hm).card ≤ (branchStarts hG L S).card :=
        card_choices_le_branchStarts hG L S E hm
    _ ≤ (Finset.univ : Finset (Fin G)).card := Finset.card_le_univ _
    _ = G := by simp

/-- **The choice points are charged to the condensed vertices.**  With the
multiplicity cap of P2's triple-repeat clause (`∀ v, deg v ≤ 2`), the
number of alternative-traversal choice points is at most twice the number
of condensed vertices of `thm:BBT`.  This is the quantitative form of
"alternate Eulerian choices occur only at condensed branch objects": the
whole freedom of the alternative traversal is bounded by the size of the
condensed graph. -/
theorem card_choices_le_two_mul_branchVerts {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ)
    (hcap : ∀ v : Fin (L-1) → α, deg hG L S v ≤ 2) :
    (choiceSet hG L S E hm).card ≤ 2 * (branchVerts hG L S).card := by
  calc (choiceSet hG L S E hm).card ≤ (branchStarts hG L S).card :=
        card_choices_le_branchStarts hG L S E hm
    _ ≤ 2 * (branchVerts hG L S).card :=
        card_branchStarts_le_two_mul_branchVerts hG L S hcap

end Traversal

/-! ## 4. The closed branch-free stratum: complete-spectrum uniqueness

If the truth has no branch object at all, §3 says there is no choice
point anywhere, and the matching is forced to advance by one position at a
time, i.e. to be a rotation of the circle.  The adapter of
`AssemblyP1.BBTChords` then turns the rotation into `RotEquiv`.  This is
`thm:BBT`'s conclusion in the branch-free stratum, fully kernel-checked. -/

section BranchFree

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S E : Fin G → α)

/-- The start of the circle at position `n`, read as an element of
`Fin G`. -/
def pos (hG : 0 < G) (n : ℕ) : Fin G := ⟨n % G, Nat.mod_lt _ hG⟩

/-- **A step-by-step successor map on a circle is a rotation.**  If `σ`
satisfies `σ (nextPos r) = nextPos (σ r)` at every `r`, then `σ` is the
forward rotation by `(σ 0).val` steps. -/
theorem isRotation_of_step {σ : Fin G → Fin G}
    (hstep : ∀ r : Fin G, σ (nextPos hG r) = nextPos hG (σ r)) :
    IsRotation hG σ := by
  have kG : (σ (⟨0, hG⟩ : Fin G)).val < G := (σ (⟨0, hG⟩ : Fin G)).isLt
  have key : ∀ n : ℕ, (σ (pos hG n)).val
      = (n + (σ (⟨0, hG⟩ : Fin G)).val) % G := by
    intro n
    induction n with
    | zero =>
        have hp : pos hG 0 = (⟨0, hG⟩ : Fin G) := Fin.ext (Nat.zero_mod _)
        rw [hp]
        show (σ (⟨0, hG⟩ : Fin G)).val
          = ((0 : ℕ) + (σ (⟨0, hG⟩ : Fin G)).val) % G
        rw [Nat.zero_add, Nat.mod_eq_of_lt kG]
    | succ n ih =>
        have h1 := hstep (pos hG n)
        have hval : (σ (nextPos hG (pos hG n))).val
            = ((σ (pos hG n)).val + 1) % G := by
          have hh := congrArg Fin.val h1
          simpa only [nextPos, rotAdd, Fin.val_mk] using hh
        have hpos : pos hG (n + 1) = nextPos hG (pos hG n) := by
          apply Fin.ext
          show (n + 1) % G = (n % G + 1) % G
          exact (Nat.mod_add_mod n G 1).symm
        have hsum : n + 1 + (σ (⟨0, hG⟩ : Fin G)).val
            = n + (σ (⟨0, hG⟩ : Fin G)).val + 1 := by omega
        rw [hpos, hval, ih, Nat.mod_add_mod, hsum]
  refine ⟨(σ (⟨0, hG⟩ : Fin G)).val, ?_⟩
  intro r
  have hrot : (rotAdd hG (σ (⟨0, hG⟩ : Fin G)).val r).val
      = (r.val + (σ (⟨0, hG⟩ : Fin G)).val) % G := by
    unfold rotAdd
    exact rfl
  have hpos : pos hG r.val = r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have hk := key r.val
  rw [hpos] at hk
  exact Fin.ext (by
    rw [hk]
    exact hrot.symm)

/-- **A branch-free truth admits no alternative Eulerian traversal.**  If
every `(L-1)`-mer of the truth occurs at most once, then the pull-back of
any `Matching` between the truth and a candidate advances one position at a
time, i.e. it is a rotation of the circle (§3, `forced_at_unambiguous`).
This is the `#89` argument *without* chords. -/
theorem pullback_isRotation {σ : Fin G → Fin G} (hm : Matching (L := L) hG S E σ)
    (hfree : P1 hG L S) :
    IsRotation hG (pullback hG L S E hm.1 : Fin G → Fin G) := by
  apply isRotation_of_step hG
  intro s
  exact forced_at_unambiguous hG L S E hm s (hfree _)

/-- **Shifting forward by `k` and then by `G - k` is the identity.** -/
theorem rotAdd_neg_cancel (_hG : 0 < G) (k r : ℕ) (hr : r < G) (hk : k < G) :
    ((r + (G - k)) % G + k) % G = r := by
  have h1 : ((r + (G - k)) % G + k) % G = (r + (G - k) + k) % G :=
    Nat.mod_add_mod _ _ _
  have h2 : r + (G - k) + k = r + G := by omega
  rw [h1, h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-- **A rotational pull-back is a rotation of the words.**  If the
pull-back of the matching --- the truth start carrying the candidate's read
at each start --- is a rotation of the circle, then the candidate is a
rotation of the truth. -/
theorem pullback_rotation_RotEquiv {σ : Fin G → Fin G}
    (hm : Matching (L := L) hG S E σ) (hL : 1 ≤ L)
    (hrot : IsRotation hG (pullback hG L S E hm.1)) :
    RotEquiv hG E S := by
  obtain ⟨k, hk⟩ := hrot
  have hk' : ∀ r : Fin G, pullback hG L S E hm.1 r = rotAdd hG (k % G) r := by
    intro r
    rw [hk r, rotAdd_mod]
  refine ⟨G - k % G, ?_⟩
  intro i
  have hval : (pullback hG L S E hm.1
        ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩).val
      = (((i.val + (G - k % G)) % G) + k % G) % G := by
    have hky := hk' ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩
    rw [hky, rotAdd]
  have hmod : (((i.val + (G - k % G)) % G) + k % G) % G = i.val :=
    rotAdd_neg_cancel hG (k % G) i.val i.isLt (Nat.mod_lt _ hG)
  have hcyc : ∀ x : Fin G, E x = cyc hG E x.val := by
    intro x
    refine congrArg E (Fin.ext (Nat.mod_eq_of_lt x.isLt).symm)
  calc E ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩
      = cyc hG E ((⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩ : Fin G).val) :=
        hcyc _
    _ = window (L := L) hG E ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩
        ⟨0, by omega⟩ := rfl
    _ = window (L := L) hG S (pullback hG L S E hm.1
        ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩) ⟨0, by omega⟩ := by
        have hh := congrFun
          (pullback_window hG L S E hm
            ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩).symm
          (⟨0, by omega⟩ : Fin L)
        exact hh
    _ = cyc hG S (pullback hG L S E hm.1
        ⟨(i.val + (G - k % G)) % G, Nat.mod_lt _ hG⟩).val := rfl
    _ = cyc hG S i.val := by rw [hval, hmod]
    _ = S i := by
        unfold cyc
        congr 1
        apply Fin.ext
        exact Nat.mod_eq_of_lt i.isLt

/-- **`thm:BBT` in the branch-free stratum.**  A circular word all of whose
`(L-1)`-mers are unique is determined up to cyclic rotation by its
complete `L`-spectrum. -/
theorem bbt_of_unambiguous (hfree : P1 hG L S) (hL : 2 ≤ L)
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S := by
  obtain ⟨σ, hm⟩ := exists_matching hG S E hspec
  have hL1 : 1 ≤ L := by omega
  exact pullback_rotation_RotEquiv hG L S E hm hL1
    (pullback_isRotation hG L S E hm hfree)

/-- The same statement with `P1` of `def:P1P2` named.  `P1` --- no
length-`L-1` word occurs more than once --- is a *sufficient* condition for
the complete-spectrum uniqueness theorem, and it is the project's stronger
of the two admissibility conditions.  No change to
`def:BBTCompleteSpectrumUniqueness` is claimed or needed. -/
theorem spectrum_unique_of_P1 (hP1 : P1 hG L S) (hL : 2 ≤ L)
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    RotEquiv hG E S :=
  bbt_of_unambiguous hG L S E hP1 hL hspec

end BranchFree

/-! ## 5. Sanity: branch objects and maximal repeats are different objects

The kernel-checked instance below is the `S = 00101` example of
`AssemblyP1.BBTChords.raw_node_crossing_not_maximal`, re-read in the
condensation language:

* the branch objects are exactly the two repeated length-`2` mers `01` and
  `10`, both of degree `2`, and their occurrences are the four starts
  `1, 2, 3, 4` (`card_branchStarts_eq_sum` gives `2 + 2 = 4`);
* the maximal unambiguous segment leaving a branch occurrence is
  *degenerate*: the vertex entered at the next start is a branch vertex
  again, so no contraction is available there;
* and simultaneously the word has a **maximal repeat of length `3`** at
  starts `1` and `3`, which is *not* a branch object (a branch object is a
  repeat of length exactly `K = L-1`).

So the condensation objects of `thm:BBT` and the maximal repeats ranged
over by P2's interleaved clause are genuinely different, and both `#89`
inferences that failed are explained: raw repeated nodes are not maximal
repeats (the maximal repeat is longer), and maximal repeats are not the
condensed vertices (they are one `K`-mer long). -/

section Sanity

/-- `S = 00101` as a length-5 word. -/
def S5 : Fin 5 → Fin 2 := ![0, 0, 1, 0, 1]

theorem hG5 : 0 < 5 := by decide

/-- The same word as a source-faithful genome. -/
def D5 : Genome (Fin 2) := Genome.mk 5 hG5 S5

/-- The instance, kernel-checked (`decide` throughout).  The branch objects
of `00101` at `L = 3` are exactly the two repeated length-`2` mers `01` and
`10`, each of degree `2`; their occurrences are the four starts `1, 2, 3, 4`
(`card_branchStarts_eq_sum` gives `2 + 2 = 4`); and the segment leaving a
branch occurrence is *degenerate*, because the vertex entered at the next
start is a branch vertex again.  The word also has a maximal repeat of
length `3` --- recorded in
`AssemblyP1.BBTChords.raw_node_crossing_not_maximal` and
`docs/bbt-chord-rematch-89.md` §3, where the `S = 00101` counterexample is
discharged --- which is *not* a branch object, since a branch object is a
repeat of length exactly `K = L-1`. -/
theorem condense_sanity_00101 :
    (vtx hG5 3 S5 (1 : Fin 5) = ![0, 1] ∧
      vtx hG5 3 S5 (3 : Fin 5) = ![0, 1] ∧
      deg hG5 3 S5 ![0, 1] = 2 ∧
      deg hG5 3 S5 ![1, 0] = 2 ∧
      deg hG5 3 S5 ![0, 0] = 1 ∧
      (branchStarts hG5 3 S5).card = 4 ∧
      Branch hG5 3 S5 (vtx hG5 3 S5 (2 : Fin 5))) := by
  decide

end Sanity

end AssemblyP1.BBTSequenceGraph
