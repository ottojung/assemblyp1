import AssemblyP1.BidirectedEulerian

/-!
# Layer A, step 2: splicing closed bidirected trails (toward `EulerianSufficient`)

This module continues `AssemblyP1/BidirectedEulerian.lean` (issue #261 Layer A).
It supplies the list-manipulation lemmas the remaining assembly step needs and
does **not** restate any source-specific spelling or likelihood claim.

* `adjacentValid_iff_isChain` — `AdjacentValid` is the relation chain of
  `ValidStep`s (`List.IsChain`), which exposes Mathlib's append/rotation API.
* `adjacentValid_append` — the general `AdjacentValid` append lemma.
* `usedEdges_append` — the physical-edge set of a concatenation is the union.
* `isClosedTrail_rotate` — a cyclic rotation of a closed trail is a closed trail.
* `isClosedTrail_append` — splicing two closed trails with disjoint physical
  edges whose two junction transitions are valid yields a closed trail.

The connected-extension induction that assembles these into
`EulerianSufficient` (splicing `exists_closed_circuit` circuits across the
connected support) is the next step and is not claimed here.
-/

set_option linter.unusedSectionVars false

namespace AssemblyP1.BidirectedEulerian

variable {V E : Type*}

namespace SignedBiGraph

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : SignedBiGraph V E)

/-- `AdjacentValid` is exactly the relation chain of valid steps. -/
theorem adjacentValid_iff_isChain (hs : List (Half E)) :
    G.AdjacentValid hs ↔ hs.IsChain G.ValidStep := by
  induction hs with
  | nil => simp [AdjacentValid]
  | cons a t ih =>
    cases t with
    | nil => simp [AdjacentValid]
    | cons b rest =>
      simp only [AdjacentValid] at ih
      rw [AdjacentValid, adjacentValidB_cons_cons, Bool.and_eq_true, decide_eq_true_eq, ih,
        List.isChain_cons_cons]

/-- The general append lemma for `AdjacentValid`. -/
theorem adjacentValid_append (l₁ l₂ : List (Half E)) :
    G.AdjacentValid (l₁ ++ l₂) ↔
      G.AdjacentValid l₁ ∧ G.AdjacentValid l₂ ∧
        (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, G.ValidStep x y) := by
  rw [adjacentValid_iff_isChain, adjacentValid_iff_isChain, adjacentValid_iff_isChain]
  exact List.isChain_append

/-- The physical edges of a concatenation are the union of the parts. -/
theorem usedEdges_append (l₁ l₂ : List (Half E)) :
    usedEdges (l₁ ++ l₂) = usedEdges l₁ ∪ usedEdges l₂ := by
  ext e
  simp [usedEdges, List.map_append, List.mem_toFinset]

/-- A closed trail is a chain of valid steps. -/
theorem isClosedTrail_chain {hs : List (Half E)} (h : G.IsClosedTrail hs) :
    hs.IsChain G.ValidStep :=
  (G.adjacentValid_iff_isChain hs).mp h.2.2.1

/-- The wrap-around transition of a closed trail. -/
theorem isClosedTrail_wrap {hs : List (Half E)} (h : G.IsClosedTrail hs) (hne : hs ≠ []) :
    G.ValidStep (hs.getLast hne) (hs.head hne) :=
  h.2.2.2 _ _ (List.head?_eq_some_head hne) (List.getLast?_eq_some_getLast hne)

/-- **Rotation.**  A cyclic rotation of a closed trail is a closed trail with the
same physical edges. -/
theorem isClosedTrail_rotate {hs : List (Half E)} (h : G.IsClosedTrail hs)
    {l₁ l₂ : List (Half E)} (hl : hs = l₁ ++ l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    G.IsClosedTrail (l₂ ++ l₁) := by
  obtain ⟨hne, hnd, hch, hwrap⟩ := h
  subst hl
  have hne12 : l₁ ++ l₂ ≠ [] := by simp [h₁]
  have hwrap' : G.ValidStep ((l₁ ++ l₂).getLast hne12) ((l₁ ++ l₂).head hne12) :=
    hwrap _ _ (List.head?_eq_some_head hne12) (List.getLast?_eq_some_getLast hne12)
  rw [G.adjacentValid_iff_isChain] at hch
  rw [List.isChain_append] at hch
  obtain ⟨hc1, hc2, hjun⟩ := hch
  refine ⟨by simp [h₂], ?_, ?_, ?_⟩
  · rw [List.map_append] at hnd ⊢
    exact List.nodup_append_comm.mp hnd
  · rw [G.adjacentValid_iff_isChain, List.isChain_append]
    refine ⟨hc2, hc1, ?_⟩
    intro x hx y hy
    have hy' : y ∈ (l₁ ++ l₂).head? := by
      rw [List.head?_append_of_ne_nil l₁ h₁]; exact hy
    have hx' : x ∈ (l₁ ++ l₂).getLast? := by
      rw [List.getLast?_append_of_ne_nil l₁ h₂]; exact hx
    exact hwrap y x (Option.mem_def.mp hy') (Option.mem_def.mp hx')
  · intro h0 hl' hh hg
    have hh' : h0 ∈ l₂.head? := by
      rw [List.head?_append_of_ne_nil l₂ h₂] at hh
      exact Option.mem_def.mpr hh
    have hg' : hl' ∈ l₁.getLast? := by
      rw [List.getLast?_append_of_ne_nil l₂ h₁] at hg
      exact Option.mem_def.mpr hg
    exact hjun hl' hg' h0 hh'

/-- **Splice.**  Two closed trails with disjoint physical edges splice into one
closed trail when the wrap transition of the first meets the head of the second
and the wrap transition of the second meets the head of the first. -/
theorem isClosedTrail_append {C C' : List (Half E)} (hCne : C ≠ []) (hC'ne : C' ≠ [])
    (hC : G.IsClosedTrail C) (hC' : G.IsClosedTrail C')
    (hdisj : Disjoint (usedEdges C) (usedEdges C'))
    (hj1 : G.ValidStep (C.getLast hCne) (C'.head hC'ne))
    (hj2 : G.ValidStep (C'.getLast hC'ne) (C.head hCne)) :
    G.IsClosedTrail (C ++ C') := by
  obtain ⟨-, hCnd, hCch, -⟩ := hC
  obtain ⟨-, hC'nd, hC'ch, -⟩ := hC'
  have hdisjL : List.Disjoint (C.map Prod.fst) (C'.map Prod.fst) := by
    rw [List.disjoint_left]
    intro x hx hx'
    exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr hx')
  refine ⟨by simp [hCne], ?_, ?_, ?_⟩
  · rw [List.map_append]
    exact List.nodup_append'.mpr ⟨hCnd, hC'nd, hdisjL⟩
  · rw [G.adjacentValid_iff_isChain, List.isChain_append]
    refine ⟨(G.adjacentValid_iff_isChain C).mp hCch,
      (G.adjacentValid_iff_isChain C').mp hC'ch, ?_⟩
    intro x hx y hy
    have hx' : C.getLast hCne = x := by
      rw [List.getLast?_eq_getLast_of_ne_nil hCne] at hx
      simpa using hx
    have hy' : C'.head hC'ne = y := by
      rw [List.head?_eq_some_head hC'ne] at hy
      simpa using hy
    subst hx'; subst hy'
    exact hj1
  · intro h0 hl' hh hg
    have hh' : h0 ∈ C.head? := by
      rw [List.head?_append_of_ne_nil C hCne] at hh
      exact Option.mem_def.mpr hh
    have hg' : hl' ∈ C'.getLast? := by
      rw [List.getLast?_append_of_ne_nil C hC'ne] at hg
      exact Option.mem_def.mpr hg
    have hh'' : C.head hCne = h0 := by
      rw [List.head?_eq_some_head hCne] at hh'
      simpa using hh'
    have hg'' : C'.getLast hC'ne = hl' := by
      rw [List.getLast?_eq_getLast_of_ne_nil hC'ne] at hg'
      simpa using hg'
    subst hh''; subst hg''
    exact hj2

end SignedBiGraph

end AssemblyP1.BidirectedEulerian
