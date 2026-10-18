import AssemblyP1.BidirectedEulerian

/-!
# Layer A, step 2: the bidirected Euler sufficiency theorem (`EulerianSufficient`)

This module continues `AssemblyP1/BidirectedEulerian.lean` (issue #261 Layer A)
and **closes its remaining target**: it proves `EulerianSufficient`, i.e. MB09
§3.4 Observation 1's sufficiency direction for finite signed bidirected
multigraphs (nonempty + balanced + support-connected ⇒ a single Euler tour on
all edges).  It does **not** restate any source-specific spelling or likelihood
claim: no §4.1 spelling theorem and no §6.2 flow-to-genome statement.

Building blocks:

* `adjacentValid_iff_isChain` — `AdjacentValid` is the relation chain of
  `ValidStep`s (`List.IsChain`), which exposes Mathlib's append/rotation API.
* `adjacentValid_append` — the general `AdjacentValid` append lemma.
* `usedEdges_append` — the physical-edge set of a concatenation is the union.
* `isClosedTrail_rotate` / `exists_head_rotate` — rotating a closed trail.
* `isClosedTrail_append` — splicing two closed trails with disjoint physical
  edges whose two junction transitions are valid yields a closed trail.
* `support_usedEdges_iff`, `support_mono`, `support_meets` — support algebra;
  a proper closed sub-trail of a support-connected set meets the residual at a
  vertex.
* `exists_incidence_sign` — in a balanced set, a supported vertex has an
  incidence of each sign (the counting lemma that makes the splice signs match).
* `exists_transition` — every supported vertex of a closed trail is the
  departure of some valid transition.
* `exists_longer` — a closed trail that misses an edge of a balanced,
  support-connected set can be spliced strictly longer.
* `exists_eulerTrailOn_of_closed` — well-founded recursion on
  `U.card - (usedEdges C).card` turning any contained closed trail into an Euler
  trail on `U`.
* `eulerianSufficient` — the assembled theorem.

Every endpoint is kernel-checked with no `sorry`/`admit`/`axiom`/`native_decide`
and axioms within `{propext, Classical.choice, Quot.sound}`.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

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

/-- The physical-edge set of a concatenation is a union (restated for the support). -/
theorem support_usedEdges_iff (l : List (Half E)) (v : V) :
    v ∈ G.support (usedEdges l) ↔
      ∃ h ∈ l, G.halfVtx h = v ∨ G.halfVtx (flip h) = v := by
  constructor
  · intro hv
    rw [support] at hv
    obtain ⟨e, he, hinc⟩ := hv
    rw [usedEdges] at he
    obtain ⟨h, hh, hhe⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    refine ⟨h, hh, ?_⟩
    rw [← hhe] at hinc
    rcases h with ⟨e', b⟩
    simp only [Incident, halfVtx, flip_mk] at hinc ⊢
    rcases b with _ | _ <;> tauto
  · rintro ⟨h, hh, hvv⟩
    rw [support]
    refine ⟨h.1, ?_, ?_⟩
    · rw [usedEdges]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨h, hh, rfl⟩)
    · rw [Incident]
      rcases h with ⟨e, b⟩
      simp only [halfVtx, flip_mk] at hvv
      rcases b with _ | _ <;> tauto

/-- Removing a balanced subset from a balanced set leaves a balanced set. -/
theorem balanced_sdiff {U V : Finset E} (hbalU : G.Balanced U) (hbalV : G.Balanced V)
    (hVsub : V ⊆ U) : G.Balanced (U \ V) := by
  intro v
  have hsum := Finset.sum_sdiff (f := fun e => G.edgeImb e v) hVsub
  have hu := hbalU v
  have hv := hbalV v
  simp only [setImb] at hu hv ⊢
  linarith

/-- The cyclic successor of a half-edge of a closed trail is a valid next step. -/
theorem isClosedTrail_validStep_next {l : List (Half E)} (h : G.IsClosedTrail l)
    (x : Half E) (hx : x ∈ l) : G.ValidStep x (l.next x hx) := by
  have hne := List.ne_nil_of_mem hx
  have hchain := G.isClosedTrail_chain h
  by_cases hmem : x ∈ l.dropLast
  · have hinf : [x, l.next x hx] <:+: l := by
      have := List.nextOr_infix_of_mem_dropLast (l := l) (a := x) hmem
        (l.get ⟨0, List.length_pos_of_mem hx⟩)
      simpa only [List.next] using this
    exact List.isChain_pair.mp (hchain.infix hinf)
  · have hxlast : x = l.getLast hne := by
      have hdl := List.dropLast_append_getLast hne
      rw [← hdl] at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact absurd hx hmem
      · simpa using hx
    have hnotmem : l.getLast hne ∉ l.dropLast := by
      intro hc; rw [← hxlast] at hc; exact hmem hc
    subst hxlast
    rw [List.next_getLast_eq_head_of_notMem_dropLast hne hnotmem]
    exact G.isClosedTrail_wrap h hne

/-- The cyclic predecessor of a half-edge of a closed trail is a valid previous step. -/
theorem isClosedTrail_validStep_prev {l : List (Half E)} (h : G.IsClosedTrail l)
    (x : Half E) (hx : x ∈ l) : G.ValidStep (l.prev x hx) x := by
  have hne := List.ne_nil_of_mem hx
  have hchain := G.isClosedTrail_chain h
  by_cases hhead : x = l.head hne
  · subst hhead
    rw [List.prev_head_eq_getLast l hne]
    exact G.isClosedTrail_wrap h hne
  · exact List.isChain_pair.mp (hchain.infix (List.prev_infix_of_mem_tail hx hhead))

/-- Decompose a list around a member. -/
theorem mem_iff_append' {l : List (Half E)} {x : Half E} (hx : x ∈ l) :
    ∃ l₁ l₂ : List (Half E), l = l₁ ++ x :: l₂ := by
  induction l with
  | nil => exact absurd hx (by simp)
  | cons a t ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨[], t, rfl⟩
    · obtain ⟨l₁, l₂, hl⟩ := ih hx
      exact ⟨a :: l₁, l₂, by rw [hl]; rfl⟩

/-- Rotate a closed trail to start at any chosen half-edge. -/
theorem exists_head_rotate (l : List (Half E)) (h : G.IsClosedTrail l)
    {b : Half E} (hb : b ∈ l) :
    ∃ l', G.IsClosedTrail l' ∧ l'.head? = some b ∧ usedEdges l' = usedEdges l := by
  obtain ⟨l₁, l₂, hl⟩ := mem_iff_append' hb
  rw [hl] at h ⊢
  rcases eq_or_ne l₁ [] with rfl | h₁
  · refine ⟨b :: l₂, ?_, rfl, by simp⟩
    simpa using h
  · have hrot := G.isClosedTrail_rotate h (l₁ := l₁) (l₂ := b :: l₂) rfl h₁ (by simp)
    refine ⟨(b :: l₂) ++ l₁, hrot, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil (b :: l₂) (by simp)]
      rfl
    · rw [usedEdges_append, usedEdges_append, Finset.union_comm]

/-- Support is monotone in the edge set. -/
theorem support_mono {V U : Finset E} (h : V ⊆ U) : G.support V ⊆ G.support U := by
  intro v hv
  rw [support] at hv ⊢
  obtain ⟨e, he, hinc⟩ := hv
  exact ⟨e, h he, hinc⟩

/-- If `U` is support-connected, a nonempty closed trail `C` with `usedEdges C ⊊ U`
meets `U \ usedEdges C` at a vertex. -/
theorem support_meets (U : Finset E) (hconn : G.SupportConnected U)
    {C : List (Half E)} (hCsub : usedEdges C ⊆ U) (hCne : C ≠ [])
    (hne : usedEdges C ≠ U) :
    (G.support (usedEdges C) ∩ G.support (U \ usedEdges C)).Nonempty := by
  have hAne : (G.support (usedEdges C)).Nonempty := by
    cases C with
    | nil => exact absurd rfl hCne
    | cons h t =>
      exact ⟨G.halfVtx h, (G.support_usedEdges_iff (h :: t) _).mpr ⟨h, by simp, Or.inl rfl⟩⟩
  have hRne : (U \ usedEdges C).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hUC
    exact hne (Finset.Subset.antisymm hCsub hUC)
  have hBne : (G.support (U \ usedEdges C)).Nonempty := by
    obtain ⟨e, he⟩ := hRne
    exact ⟨G.endVtx e false, by rw [support]; exact ⟨e, he, Or.inl rfl⟩⟩
  by_contra hdisj
  have hdj : Disjoint (G.support (usedEdges C)) (G.support (U \ usedEdges C)) :=
    Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hdisj)
  have hstep : ∀ x y, x ∈ G.support (usedEdges C) → G.Adj U x y →
      y ∈ G.support (usedEdges C) := by
    intro x y hx hadj
    rw [Adj] at hadj
    obtain ⟨e, he, hends⟩ := hadj
    by_cases heC : e ∈ usedEdges C
    · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h2]; rw [support]; exact ⟨e, heC, Or.inr rfl⟩
      · rw [← h2]; rw [support]; exact ⟨e, heC, Or.inl rfl⟩
    · exfalso
      have heR : e ∈ U \ usedEdges C := Finset.mem_sdiff.mpr ⟨he, heC⟩
      have hxB : x ∈ G.support (U \ usedEdges C) := by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1]; rw [support]; exact ⟨e, heR, Or.inl rfl⟩
        · rw [← h1]; rw [support]; exact ⟨e, heR, Or.inr rfl⟩
      exact Set.disjoint_left.mp hdj hx hxB
  obtain ⟨u, hu⟩ := hAne
  obtain ⟨w, hw⟩ := hBne
  have huU : u ∈ G.support U := G.support_mono hCsub hu
  have hwU : w ∈ G.support U := G.support_mono (Finset.sdiff_subset) hw
  have hconn' := hconn u huU w hwU
  have hinv : ∀ x y, Relation.ReflTransGen (G.Adj U) x y →
      x ∈ G.support (usedEdges C) → y ∈ G.support (usedEdges C) := by
    intro x y hrt
    induction hrt with
    | refl => exact id
    | tail hab hbc ih => exact fun hx => hstep _ _ (ih hx) hbc
  have hwA : w ∈ G.support (usedEdges C) := hinv u w hconn' hu
  exact Set.disjoint_left.mp hdj hwA hw

/-- In a balanced set, a vertex that is incident to some edge has an incidence of
each sign. -/
theorem exists_incidence_sign (R : Finset E) (hbal : G.Balanced R) (v : V)
    (hv : v ∈ G.support R) (s : Bool) :
    ∃ h : Half E, h.1 ∈ R ∧ G.halfVtx h = v ∧ G.halfSgn h = s := by
  by_contra hcon
  have hno : ∀ e ∈ R, ∀ b : Bool, G.halfVtx (e, b) = v → G.halfSgn (e, b) ≠ s := by
    intro e he b hvw hsg
    exact hcon ⟨(e, b), he, hvw, hsg⟩
  set t : ℤ := if s then 1 else -1 with ht
  have ht2 : t * t = 1 := by rw [ht]; split <;> norm_num
  have hsign : ∀ e ∈ R, ∀ b : Bool, G.halfVtx (e, b) = v →
      t * G.signIndic (e, b) v = -1 := by
    intro e he b hvw
    have hsg : G.halfSgn (e, b) ≠ s := hno e he b hvw
    rw [G.signIndic_eq_of_vtx hvw, ht]
    cases hs : s <;> cases hb : G.halfSgn (e, b) <;> simp_all
  have hterm : ∀ e ∈ R, t * G.edgeImb e v ≤ 0 := by
    intro e he
    have hb : ∀ b : Bool, t * G.signIndic (e, b) v ≤ 0 := by
      intro b
      by_cases hvw : G.halfVtx (e, b) = v
      · rw [hsign e he b hvw]; norm_num
      · rw [G.signIndic_eq_zero hvw, mul_zero]
    rw [edgeImb, mul_add]
    linarith [hb false, hb true]
  have hzero : t * G.setImb R v = 0 := by rw [hbal v, mul_zero]
  have hsum : t * G.setImb R v = ∑ e ∈ R, t * G.edgeImb e v := by
    rw [setImb, Finset.mul_sum]
  rw [hsum] at hzero
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hzero
  rw [support] at hv
  obtain ⟨e, he, hinc⟩ := hv
  rw [Incident] at hinc
  obtain ⟨b, hb⟩ : ∃ b : Bool, G.halfVtx (e, b) = v := by
    rcases hinc with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have h1 : t * G.signIndic (e, b) v = -1 := hsign e he b hb
  have h2 : t * G.signIndic (e, !b) v ≤ 0 := by
    by_cases hw : G.halfVtx (e, !b) = v
    · rw [hsign e he (!b) hw]; norm_num
    · rw [G.signIndic_eq_zero hw, mul_zero]
  have heq : t * G.edgeImb e v =
      t * G.signIndic (e, b) v + t * G.signIndic (e, !b) v := by
    rw [edgeImb, mul_add]
    rcases b <;> simp only [Bool.not_false, Bool.not_true] <;> ring
  have := hall e he
  rw [heq, h1] at this
  linarith

/-- In a closed trail, any vertex of its support occurs as the departure of some
valid transition. -/
theorem exists_transition {l : List (Half E)} (h : G.IsClosedTrail l)
    (v : V) (hv : v ∈ G.support (usedEdges l)) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ G.ValidStep a b ∧ G.halfVtx b = v := by
  obtain ⟨h0, hh0, hcase⟩ := (G.support_usedEdges_iff l v).mp hv
  rcases hcase with hcase | hcase
  · exact ⟨l.prev h0 hh0, h0, List.prev_mem l h0 hh0, hh0,
      G.isClosedTrail_validStep_prev h h0 hh0, hcase⟩
  · exact ⟨h0, l.next h0 hh0, hh0, List.next_mem l h0 hh0,
      G.isClosedTrail_validStep_next h h0 hh0,
      (G.isClosedTrail_validStep_next h h0 hh0).1.trans hcase⟩

/-- In a balanced, support-connected set, a closed trail that does not use every
edge can be spliced with another circuit into a strictly longer closed trail. -/
theorem exists_longer (U : Finset E) (hbal : G.Balanced U) (hconn : G.SupportConnected U)
    {C : List (Half E)} (hC : G.IsClosedTrail C) (hCsub : usedEdges C ⊆ U) (hCne : C ≠ [])
    (hne : usedEdges C ≠ U) :
    ∃ C', G.IsClosedTrail C' ∧ usedEdges C ⊆ usedEdges C' ∧ usedEdges C' ⊆ U ∧
      (usedEdges C).card < (usedEdges C').card := by
  classical
  set R := U \ usedEdges C with hR
  have hCbal : G.Balanced (usedEdges C) := by
    intro v
    rw [G.setImb_usedEdges C hC.2.1 v, G.trailImb_eq_zero_of_closed hC v]
  have hRbal : G.Balanced R := G.balanced_sdiff hbal hCbal hCsub
  obtain ⟨v, hv⟩ := G.support_meets U hconn hCsub hCne hne
  have hvC : v ∈ G.support (usedEdges C) := hv.1
  have hvR : v ∈ G.support R := hv.2
  obtain ⟨_, b, _, hb, _, hbv⟩ := G.exists_transition hC v hvC
  obtain ⟨Cb, hCb, hCbhead, hCbeq⟩ := G.exists_head_rotate C hC hb
  have hCbne : Cb ≠ [] := by rintro h; rw [h] at hCbhead; simp at hCbhead
  have hCbhead' : Cb.head hCbne = b := by
    rw [List.head?_eq_some_head hCbne] at hCbhead
    exact Option.some.inj hCbhead
  obtain ⟨h0', hh0'R, hh0'v, hh0'sgn⟩ := G.exists_incidence_sign R hRbal v hvR (G.halfSgn b)
  obtain ⟨C', hC'closed, hC'sub, hC'head⟩ := G.exists_closed_circuit R hRbal h0' hh0'R
  have hC'ne : C' ≠ [] := by rintro h; rw [h] at hC'head; simp at hC'head
  have hC'head' : C'.head hC'ne = h0' := by
    rw [List.head?_eq_some_head hC'ne] at hC'head
    exact Option.some.inj hC'head
  have hdisj : Disjoint (usedEdges Cb) (usedEdges C') := by
    rw [hCbeq, Finset.disjoint_left]
    intro e heC heC'
    exact (Finset.mem_sdiff.mp (hC'sub heC')).2 heC
  have hj1 : G.ValidStep (Cb.getLast hCbne) (C'.head hC'ne) := by
    have hw := G.isClosedTrail_wrap hCb hCbne
    rw [hCbhead'] at hw
    rw [hC'head']
    exact ⟨by rw [hh0'v, ← hbv]; exact hw.1, by rw [hh0'sgn]; exact hw.2⟩
  have hj2 : G.ValidStep (C'.getLast hC'ne) (Cb.head hCbne) := by
    have hw := G.isClosedTrail_wrap hC'closed hC'ne
    rw [hC'head'] at hw
    rw [hCbhead']
    exact ⟨by rw [hbv, ← hh0'v]; exact hw.1, by rw [← hh0'sgn]; exact hw.2⟩
  refine ⟨Cb ++ C', G.isClosedTrail_append hCbne hC'ne hCb hC'closed hdisj hj1 hj2,
    ?_, ?_, ?_⟩
  · rw [usedEdges_append, hCbeq]; exact Finset.subset_union_left
  · rw [usedEdges_append, hCbeq, Finset.union_subset_iff]
    refine ⟨hCsub, ?_⟩
    rw [hR] at hC'sub
    exact Finset.Subset.trans hC'sub Finset.sdiff_subset
  · rw [usedEdges_append, hCbeq]
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩)
    intro hEq
    obtain ⟨e, heC'⟩ : (usedEdges C').Nonempty := by
      cases C' with
      | nil => exact absurd rfl hC'ne
      | cons h t => exact ⟨h.1, List.mem_toFinset.mpr (List.mem_map.mpr ⟨h, by simp, rfl⟩)⟩
    have heU : e ∈ usedEdges C ∪ usedEdges C' := Finset.mem_union_right _ heC'
    rw [← hEq] at heU
    exact (Finset.mem_sdiff.mp (hC'sub heC')).2 heU

/-- Every balanced, support-connected finite edge set admits a single Euler trail,
grown from any closed trail already contained in it by repeated splicing. -/
theorem exists_eulerTrailOn_of_closed (U : Finset E) (hbal : G.Balanced U)
    (hconn : G.SupportConnected U) :
    ∀ (C : List (Half E)), G.IsClosedTrail C → usedEdges C ⊆ U → C ≠ [] →
      ∃ hs, G.IsEulerTrailOn U hs := by
  classical
  let P : ℕ → Prop := fun m => ∀ (C : List (Half E)), G.IsClosedTrail C →
      usedEdges C ⊆ U → C ≠ [] → U.card - (usedEdges C).card = m →
      ∃ hs, G.IsEulerTrailOn U hs
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro C hC hCsub hCne hm
      by_cases hfull : usedEdges C = U
      · exact ⟨C, hC, hfull⟩
      · obtain ⟨C', hC'closed, hCsub', hC'subU, hcard⟩ :=
          G.exists_longer U hbal hconn hC hCsub hCne hfull
        have hC'ne : C' ≠ [] := by
          intro h; rw [h] at hcard; simp [usedEdges] at hcard
        have hle : (usedEdges C').card ≤ U.card := Finset.card_le_card hC'subU
        exact ih (U.card - (usedEdges C').card) (by omega) C' hC'closed hC'subU hC'ne rfl
  intro C hC hCsub hCne
  exact hP _ C hC hCsub hCne rfl

end SignedBiGraph

open SignedBiGraph

/-- **Layer A sufficiency (MB09 §3.4 Observation 1).**  Every nonempty balanced,
support-connected finite signed bidirected multigraph has a single Euler tour on
all of its edges. -/
theorem eulerianSufficient : EulerianSufficient := by
  intro V E _ _ _ _ G hcard hbal hconn
  classical
  have hcard' : 0 < (Finset.univ : Finset E).card := by rwa [Finset.card_univ]
  obtain ⟨e0, -⟩ := Finset.card_pos.mp hcard'
  obtain ⟨C, hCclosed, hCsub, hChead⟩ :=
    G.exists_closed_circuit (Finset.univ) hbal (e0, false) (Finset.mem_univ _)
  have hCne : C ≠ [] := by rintro h; rw [h] at hChead; simp at hChead
  exact G.exists_eulerTrailOn_of_closed (Finset.univ) hbal hconn C hCclosed hCsub hCne

end AssemblyP1.BidirectedEulerian
