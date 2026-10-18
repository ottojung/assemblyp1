import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Layer A: the bidirected Euler-circuit theorem (MB09 §3.4, Observation 1)

Primary source: A. Medvedev and M. Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. **16**(8) (2009) 1101–1116, §3.4 Observation 1:

> A bidirected graph contains an Eulerian circuit iff it is connected and
> balanced.

and §4.1, which constructs a physical bidirected de Bruijn edge per `k`-molecule
and proves that a bidirected tour spells circular DNA.

This module formalizes the **topological** half of that statement only, for a
finite signed bidirected *multigraph* presented by **physical edge IDs**, which is
what MB09 §3.2 needs (parallel overlaps and self-loops with two endpoint
occurrences must stay distinct).  It is deliberately independent of the §6.2
read-overlap flow model and of any likelihood statement: it says that a balanced
connected physical edge multigraph has one alternately signed cyclic tour using
every physical edge exactly once.

## The model

`SignedBiGraph V E` assigns to each physical edge ID `e : E` and each of its two
endpoint occurrences `b : Bool` a vertex `endVtx e b` and a sign `endSgn e b`.
The two occurrences of one edge are the *half-edges* `(e, false)` and
`(e, true)`; `flip` swaps them and is fixed-point-free.  A loop is an edge whose
two occurrences share a vertex; the occurrences are still distinct, so both of
its incidences are counted.

* `Balanced U` — at every vertex the number of positive incidences equals the
  number of negative incidences among the half-edges of the edges in `U`.
* `SupportConnected U` — the vertices incident to `U` form one connected class
  under the edge relation.
* `ValidStep a b` — a bidirected transition: `b` departs the vertex at which `a`
  arrives, with the opposite sign (MB09 §3.2).
* `IsClosedTrail hs` — `hs` is a nonempty cyclic list of half-edges, with distinct
  physical edges, consecutive `ValidStep`s including the wrap-around.
* `IsEulerTrailOn U hs` — a closed trail whose physical edges are exactly `U`,
  each once.

## What is proved (kernel-checked)

* `balanced_of_isEulerTrailOn` — the **necessary** direction: an Euler trail on
  `U` makes `U` balanced, because each visit enters and leaves with opposite
  signs (the telescoping identity `trailImb_telescope` plus `setImb_usedEdges`).
* `exists_extension` — the **no-dead-end** lemma, the counting heart of
  Observation 1: in a balanced edge set, a valid open trail with distinct edges
  that is not yet closed can always be extended by an unused edge.
* `exists_closed_circuit` — a nonempty balanced edge set admits a closed
  alternating circuit through any prescribed incidence, obtained as a maximal
  valid trail.  This is the connected-component-free core of Observation 1.

The assembly of `exists_closed_circuit` over a connected support into a *single*
Euler tour on all of `U` (splicing the circuits of `U` at shared vertices, using
that connectivity forces distinct circuits to meet) is the remaining step; it is
not claimed here.  `EulerianSufficient` records that target.

## What is *not* claimed

This is a statement about an abstract finite signed bidirected multigraph.  It
does **not** prove that any particular §6.2 flow is a single circular genome, nor
that the abstract model is MB09's physical read-overlap graph, nor any
spelling/Observation-7 correspondence.  Those are separate layers.
-/

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace AssemblyP1.BidirectedEulerian

variable {V E : Type*}

/-- The two endpoint occurrences (half-edges) of a physical edge ID. -/
abbrev Half (E : Type*) := E × Bool

/-- The edge involution: it swaps the two endpoint occurrences of a physical
edge and is fixed-point-free. -/
def flip : Half E ≃ Half E where
  toFun h := (h.1, !h.2)
  invFun h := (h.1, !h.2)
  left_inv h := by rcases h with ⟨e, b⟩; cases b <;> rfl
  right_inv h := by rcases h with ⟨e, b⟩; cases b <;> rfl

@[simp] theorem flip_mk (e : E) (b : Bool) : flip (E := E) (e, b) = (e, !b) := rfl

@[simp] theorem flip_flip (h : Half E) : flip (E := E) (flip h) = h := by
  rcases h with ⟨e, b⟩; cases b <;> rfl

theorem flip_ne (h : Half E) : flip (E := E) h ≠ h := by
  rcases h with ⟨e, b⟩; cases b <;> simp

/-- A finite signed bidirected multigraph, presented by physical edge IDs.  Each
physical edge has two endpoint occurrences (`Bool`), each with its own vertex and
its own incidence sign.  Parallel edge IDs and self-loops are kept distinct. -/
structure SignedBiGraph (V E : Type*) where
  /-- The vertex of the endpoint occurrence `(e, b)`. -/
  endVtx : E → Bool → V
  /-- The incidence sign of the endpoint occurrence `(e, b)` (`true` is `+1`). -/
  endSgn : E → Bool → Bool

namespace SignedBiGraph

/-- The physical edges traversed by a list of half-edges. -/
def usedEdges [DecidableEq E] (hs : List (Half E)) : Finset E := (hs.map Prod.fst).toFinset

/-- All endpoint occurrences of the edges of `U`. -/
def incidences (U : Finset E) : Finset (Half E) := U.product Finset.univ

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : SignedBiGraph V E)

/-- The vertex of a half-edge. -/
def halfVtx (h : Half E) : V := G.endVtx h.1 h.2

/-- The incidence sign of a half-edge (`true` is `+1`). -/
def halfSgn (h : Half E) : Bool := G.endSgn h.1 h.2

/-- MB09 §3.2: a bidirected transition.  `b` departs from the vertex at which
`a` arrives (`halfVtx (flip a)`) and its sign is opposite to the arriving
sign. -/
def ValidStep (a b : Half E) : Prop :=
  G.halfVtx b = G.halfVtx (flip a) ∧ G.halfSgn b = !G.halfSgn (flip a)

instance (a b : Half E) : Decidable (G.ValidStep a b) := by
  unfold ValidStep; infer_instance

/-- Consecutive validity of a list of half-edges (ignoring the wrap-around). -/
def adjacentValidB : List (Half E) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (G.ValidStep a b) && adjacentValidB (b :: rest)

/-- Consecutive validity of a list of half-edges (ignoring the wrap-around). -/
def AdjacentValid (hs : List (Half E)) : Prop := G.adjacentValidB hs = true

instance (hs : List (Half E)) : Decidable (G.AdjacentValid hs) :=
  inferInstanceAs (Decidable (G.adjacentValidB hs = true))

@[simp] theorem adjacentValidB_nil : G.adjacentValidB [] = true := rfl
@[simp] theorem adjacentValidB_singleton (a : Half E) : G.adjacentValidB [a] = true := rfl
theorem adjacentValidB_cons_cons (a b : Half E) (rest : List (Half E)) :
    G.adjacentValidB (a :: b :: rest) =
      (decide (G.ValidStep a b) && G.adjacentValidB (b :: rest)) := rfl

/-- A closed bidirected trail: a nonempty cyclic list of half-edges, distinct
physical edges, consecutive transitions valid, and the wrap-around transition
also valid. -/
def IsClosedTrail (hs : List (Half E)) : Prop :=
  hs ≠ [] ∧ (hs.map Prod.fst).Nodup ∧ G.AdjacentValid hs ∧
    (∀ (h0 hl : Half E), hs.head? = some h0 → hs.getLast? = some hl → G.ValidStep hl h0)

/-- An Euler trail on the edge set `U`: a closed trail using exactly the physical
edges of `U`, each once. -/
def IsEulerTrailOn (U : Finset E) (hs : List (Half E)) : Prop :=
  G.IsClosedTrail hs ∧ usedEdges hs = U

/-- The signed incidence contribution of one half-edge at the vertex `v`. -/
def signIndic (h : Half E) (v : V) : ℤ :=
  if G.halfVtx h = v then (if G.halfSgn h then (1 : ℤ) else -1) else 0

/-- The signed incidence contribution of one physical edge at `v`: the sum of
the two endpoint occurrences, counted separately even for a loop. -/
def edgeImb (e : E) (v : V) : ℤ := G.signIndic (e, false) v + G.signIndic (e, true) v

/-- MB09 §3.4's signed imbalance `pos(f)(v) − neg(f)(v)` for the multiplicity
vector that is `1` on `U` and `0` elsewhere. -/
def setImb (U : Finset E) (v : V) : ℤ := U.sum (fun e => G.edgeImb e v)

/-- MB09 §3.4: `pos(f)(v) = neg(f)(v)` at every vertex, written as the signed
imbalance being zero. -/
def Balanced (U : Finset E) : Prop := ∀ v, G.setImb U v = 0

/-- The signed imbalance of a list of half-edges at `v`: the departure signs plus
the arrival signs. -/
def trailImb (hs : List (Half E)) (v : V) : ℤ :=
  (hs.map (fun h => G.signIndic h v)).sum +
    (hs.map (fun h => G.signIndic (flip h) v)).sum

/-- `v` is incident to the edge `e`. -/
def Incident (e : E) (v : V) : Prop := G.endVtx e false = v ∨ G.endVtx e true = v

/-- The vertex support of `U`. -/
def support (U : Finset E) : Set V := {v | ∃ e ∈ U, G.Incident e v}

/-- Two vertices are joined by an edge of `U`. -/
def Adj (U : Finset E) (u v : V) : Prop :=
  ∃ e ∈ U, (G.endVtx e false = u ∧ G.endVtx e true = v) ∨
    (G.endVtx e true = u ∧ G.endVtx e false = v)

/-- The vertex support of `U` is connected under `Adj`. -/
def SupportConnected (U : Finset E) : Prop :=
  ∀ u ∈ G.support U, ∀ v ∈ G.support U, Relation.ReflTransGen (G.Adj U) u v

/-! ## Counting lemmas -/

/-- A half-edge's signed contribution at a vertex it is not incident to is zero. -/
@[simp] theorem signIndic_eq_zero {h : Half E} {v : V} (hv : G.halfVtx h ≠ v) :
    G.signIndic h v = 0 := by simp [signIndic, hv]

/-- At its own vertex, a half-edge's signed contribution is its sign. -/
theorem signIndic_eq_of_vtx {h : Half E} {v : V} (hv : G.halfVtx h = v) :
    G.signIndic h v = (if G.halfSgn h then (1 : ℤ) else -1) := by
  simp [signIndic, hv]

/-- The two endpoint occurrences of an edge contribute `edgeImb`. -/
theorem edgeImb_fst (h : Half E) (v : V) :
    G.edgeImb h.1 v = G.signIndic h v + G.signIndic (flip h) v := by
  rcases h with ⟨e, b⟩
  cases b <;>
    simp only [edgeImb, flip_mk, Bool.not_false, Bool.not_true] <;> ring

/-- Sum of a pointwise sum of integer-valued maps on a list. -/
private theorem list_sum_map_add (l : List (Half E)) (f g : Half E → ℤ) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih => rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons, List.sum_cons, ih]; ring

/-- A `Finset` sum over the `toFinset` of a nodup list is the list sum. -/
theorem list_sum_toFinset {α : Type*} [DecidableEq α] (l : List α) (f : α → ℤ)
    (h : l.Nodup) : l.toFinset.sum f = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at h
    rw [List.toFinset_cons, Finset.sum_insert, List.map_cons, List.sum_cons, ih h.2]
    exact fun ha => h.1 (List.mem_toFinset.mp ha)

/-- A valid transition cancels the arrival sign of one step against the departure
sign of the next. -/
theorem signIndic_cancel {a b : Half E} (h : G.ValidStep a b) (v : V) :
    G.signIndic (flip a) v + G.signIndic b v = 0 := by
  obtain ⟨hv, hsg⟩ := h
  simp only [signIndic]
  rw [hv]
  by_cases hc : G.halfVtx (flip a) = v
  · simp only [hc, ite_true]
    cases hfa : G.halfSgn (flip a) <;> simp_all
  · simp only [hc, ite_false, zero_add]

/-- A valid adjacent pair decomposes into the step and the tail's validity. -/
theorem validStep_of_adjacentValid_cons {a b : Half E} {rest : List (Half E)}
    (h : G.AdjacentValid (a :: b :: rest)) :
    G.ValidStep a b ∧ G.AdjacentValid (b :: rest) := by
  rw [AdjacentValid] at h
  simp only [adjacentValidB_cons_cons, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, by rw [AdjacentValid]; exact h.2⟩

/-- **Telescoping.**  The signed imbalance of a valid open trail is the departure
sign of its first step plus the arrival sign of its last step. -/
theorem trailImb_telescope (hs : List (Half E)) (hne : hs ≠ [])
    (hch : G.AdjacentValid hs) (v : V) :
    G.trailImb hs v =
      G.signIndic (hs.head hne) v + G.signIndic (flip (hs.getLast hne)) v := by
  induction hs with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [trailImb, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [List.head_cons, List.getLast_singleton]
      ring
    | cons b rest =>
      obtain ⟨hvs, hch'⟩ := G.validStep_of_adjacentValid_cons hch
      have ih' := ih (by simp) hch'
      rw [trailImb]
      simp only [List.map_cons, List.sum_cons]
      rw [List.head_cons, List.getLast_cons_cons]
      simp only [trailImb, List.map_cons, List.sum_cons] at ih'
      rw [List.head_cons] at ih'
      linarith [ih', G.signIndic_cancel hvs v]

/-- The edge set of a trail is exactly the image of its physical edge IDs. -/
theorem setImb_usedEdges (hs : List (Half E)) (hnd : (hs.map Prod.fst).Nodup) (v : V) :
    G.setImb (usedEdges hs) v = G.trailImb hs v := by
  rw [setImb, usedEdges,
    list_sum_toFinset (hs.map Prod.fst) (fun e => G.edgeImb e v) hnd]
  rw [trailImb, List.map_map, ← list_sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro h _
  exact G.edgeImb_fst h v

/-- The edge set of a closed trail is balanced. -/
theorem trailImb_eq_zero_of_closed {hs : List (Half E)} (h : G.IsClosedTrail hs) (v : V) :
    G.trailImb hs v = 0 := by
  obtain ⟨hne, hnd, hch, hwrap⟩ := h
  rw [G.trailImb_telescope hs hne hch v]
  have hh : hs.head? = some (hs.head hne) := List.head?_eq_some_head hne
  have hl : hs.getLast? = some (hs.getLast hne) := List.getLast?_eq_some_getLast hne
  have hw := hwrap _ _ hh hl
  have hc := G.signIndic_cancel hw v
  linarith

/-- **The necessary direction.**  An Euler trail on `U` exhibits `U` as balanced:
each visit enters and leaves with opposite signs. -/
theorem balanced_of_isEulerTrailOn (U : Finset E) (hs : List (Half E))
    (h : G.IsEulerTrailOn U hs) : G.Balanced U := by
  intro v
  rw [← h.2]
  rw [G.setImb_usedEdges hs h.1.2.1 v]
  exact G.trailImb_eq_zero_of_closed h.1 v

/-! ## The greedy extension step -/

private theorem eq_not_of_ne_bool {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

/-- **No dead end.**  In a balanced edge set `U`, a valid open trail with
distinct edges drawn from `U` that is not yet closed can always be extended by an
unused edge of `U`.  This is the counting heart of Observation 1: balance forces
the unused residual to have an incidence of the required opposite sign at the
current vertex. -/
theorem exists_extension (U : Finset E) (hbal : G.Balanced U)
    (hs : List (Half E)) (hne : hs ≠ []) (hch : G.AdjacentValid hs)
    (hnd : (hs.map Prod.fst).Nodup) (hsub : usedEdges hs ⊆ U)
    (hopen : ¬ G.ValidStep (hs.getLast hne) (hs.head hne)) :
    ∃ h' : Half E, h'.1 ∈ U ∧ h'.1 ∉ usedEdges hs ∧ G.ValidStep (hs.getLast hne) h' := by
  classical
  set w := G.halfVtx (flip (hs.getLast hne)) with hw
  set t : ℤ := G.signIndic (flip (hs.getLast hne)) w with ht
  have htval : t = (if G.halfSgn (flip (hs.getLast hne)) then (1 : ℤ) else -1) := by
    rw [ht]; exact G.signIndic_eq_of_vtx rfl
  have ht2 : t * t = 1 := by rw [htval]; split <;> norm_num
  -- telescoping: the trail's imbalance at `w` is `t` or `2 * t`
  have htrail : G.trailImb hs w = t ∨ G.trailImb hs w = 2 * t := by
    rw [G.trailImb_telescope hs hne hch w, ← ht]
    have hsign : G.signIndic (hs.head hne) w = 0 ∨ G.signIndic (hs.head hne) w = t := by
      by_cases hvw : G.halfVtx (hs.head hne) = w
      · right
        have hsg : G.halfSgn (hs.head hne) = G.halfSgn (flip (hs.getLast hne)) := by
          by_contra hc
          exact hopen ⟨by rw [hvw, hw], eq_not_of_ne_bool hc⟩
        rw [G.signIndic_eq_of_vtx hvw, hsg, htval]
      · left; exact G.signIndic_eq_zero hvw
    rcases hsign with h | h
    · left; rw [h]; ring
    · right; rw [h]; ring
  -- the unused residual imbalance is `-trailImb`
  have hsdiff : G.setImb (U \ usedEdges hs) w = -G.trailImb hs w := by
    have hsum := Finset.sum_sdiff (f := fun e => G.edgeImb e w) hsub
    have hb := hbal w
    have hu := G.setImb_usedEdges hs hnd w
    simp only [setImb] at hsum hb hu ⊢
    linarith
  by_contra hcon
  have hno : ∀ e ∈ U \ usedEdges hs, ∀ b : Bool,
      ¬ (G.halfVtx (e, b) = w ∧
        G.halfSgn (e, b) = !G.halfSgn (flip (hs.getLast hne))) := by
    intro e he b hb
    apply hcon
    refine ⟨(e, b), (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2, ?_⟩
    rw [ValidStep]
    exact ⟨by rw [hb.1, hw], hb.2⟩
  have hnonneg : 0 ≤ t * G.setImb (U \ usedEdges hs) w := by
    rw [setImb, Finset.mul_sum]
    apply Finset.sum_nonneg
    intro e he
    have hb : ∀ b : Bool, 0 ≤ t * G.signIndic (e, b) w := by
      intro b
      by_cases hvw : G.halfVtx (e, b) = w
      · have hsg : G.halfSgn (e, b) = G.halfSgn (flip (hs.getLast hne)) := by
          by_contra hc
          exact hno e he b ⟨hvw, eq_not_of_ne_bool hc⟩
        rw [G.signIndic_eq_of_vtx hvw, hsg, ← htval, ht2]
        norm_num
      · rw [G.signIndic_eq_zero hvw, mul_zero]
    rw [edgeImb, mul_add]
    linarith [hb false, hb true]
  have hneg : t * G.setImb (U \ usedEdges hs) w < 0 := by
    rw [hsdiff]
    rcases htrail with h | h <;> rw [h] <;> nlinarith [ht2]
  linarith [hnonneg, hneg]

/-! ## The greedy circuit through a vertex -/

/-- The edges traversed by a list of half-edges lie in `U` when every half-edge
does. -/
theorem usedEdges_subset {U : Finset E} {hs : List (Half E)}
    (h : ∀ x ∈ hs, x.1 ∈ U) : usedEdges hs ⊆ U := by
  intro e he
  rw [usedEdges] at he
  obtain ⟨x, hx, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  rw [← heq]
  exact h x hx

/-- Consecutive validity after appending one step tests exactly the appended
transition. -/
theorem adjacentValidB_append_singleton (l : List (Half E)) (a : Half E) :
    G.adjacentValidB (l ++ [a]) =
      (G.adjacentValidB l && (match l.getLast? with
        | some b => decide (G.ValidStep b a) | none => true)) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    cases t with
    | nil => simp [adjacentValidB]
    | cons y t' =>
      simp only [List.cons_append, adjacentValidB_cons_cons, List.getLast?_cons_cons]
      rw [← List.cons_append, ih, Bool.and_assoc]

/-- **A closed alternating circuit through a given incidence.**  In a balanced
edge set `U`, starting from any half-edge whose edge is in `U`, a maximal valid
trail closes up and uses only edges of `U`.  This is the connected-component-free
core of Observation 1. -/
theorem exists_closed_circuit (U : Finset E) (hbal : G.Balanced U)
    (h0 : Half E) (hh0 : h0.1 ∈ U) :
    ∃ hs : List (Half E), G.IsClosedTrail hs ∧ usedEdges hs ⊆ U ∧ hs.head? = some h0 := by
  classical
  let C : Finset {l : List (Half E) // l.Nodup} := Finset.univ.filter (fun l =>
    l.1.head? = some h0 ∧ (l.1.map Prod.fst).Nodup ∧ G.AdjacentValid l.1 ∧
      ∀ h ∈ l.1, h.1 ∈ U)
  have hCne : C.Nonempty := by
    refine ⟨⟨[h0], by simp⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rfl, by simp, by rw [AdjacentValid]; rfl, ?_⟩
    intro h hh; rw [List.mem_singleton] at hh; rw [hh]; exact hh0
  obtain ⟨l, hmem, hmax⟩ := Finset.exists_max_image C (fun l => l.1.length) hCne
  rw [Finset.mem_filter] at hmem
  obtain ⟨-, hhead, hnd, hch, hsub⟩ := hmem
  have hnodup : l.1.Nodup := l.2
  have hne : l.1 ≠ [] := by intro hnil; rw [hnil] at hhead; simp at hhead
  refine ⟨l.1, ⟨hne, hnd, hch, ?_⟩, usedEdges_subset hsub, hhead⟩
  intro h0' hl hh0' hhl
  have hh0'eq : h0' = h0 := by rw [hhead] at hh0'; exact (Option.some.inj hh0').symm
  have hhleq : hl = l.1.getLast hne := by
    rw [List.getLast?_eq_some_getLast hne] at hhl
    exact (Option.some.inj hhl).symm
  have hheadval : l.1.head hne = h0 := by
    have hh := List.head?_eq_some_head hne
    rw [hhead] at hh
    exact (Option.some.inj hh).symm
  by_contra hvs
  rw [hh0'eq, hhleq, ← hheadval] at hvs
  obtain ⟨h', hU, hnotD, hvstep⟩ :=
    G.exists_extension U hbal l.1 hne hch hnd (usedEdges_subset hsub) hvs
  have hnotmem : h' ∉ l.1 := by
    intro hh
    exact hnotD (List.mem_toFinset.mpr (List.mem_map.mpr ⟨h', hh, rfl⟩))
  have hnodup' : (l.1 ++ [h']).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnodup, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    intro he
    rw [hb] at he
    rw [he] at ha
    exact hnotmem ha
  have hhead' : (l.1 ++ [h']).head? = some h0 := by
    rw [List.head?_append, hhead]; rfl
  have hnd' : ((l.1 ++ [h']).map Prod.fst).Nodup := by
    rw [List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨hnd, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    intro he
    rw [hb] at he
    rw [he] at ha
    exact hnotD (List.mem_toFinset.mpr ha)
  have hch' : G.AdjacentValid (l.1 ++ [h']) := by
    rw [AdjacentValid, G.adjacentValidB_append_singleton, hch, Bool.true_and,
      List.getLast?_eq_some_getLast hne]
    exact decide_eq_true hvstep
  have hsub' : ∀ h ∈ l.1 ++ [h'], h.1 ∈ U := by
    intro h hh
    rw [List.mem_append] at hh
    rcases hh with hh | hh
    · exact hsub h hh
    · rw [List.mem_singleton] at hh; rw [hh]; exact hU
  have hmem' : (⟨l.1 ++ [h'], hnodup'⟩ : {l : List (Half E) // l.Nodup}) ∈ C := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hhead', hnd', hch', hsub'⟩
  have hle := hmax ⟨l.1 ++ [h'], hnodup'⟩ hmem'
  simp only [List.length_append, List.length_cons, List.length_nil] at hle
  omega

end SignedBiGraph

/-- **The full Observation 1 sufficiency target.**  Every nonempty, balanced,
support-connected finite signed bidirected multigraph has a single Euler tour on
all of its edges.

The module proves the necessary direction (`SignedBiGraph.balanced_of_isEulerTrailOn`)
and the closed-circuit core (`SignedBiGraph.exists_closed_circuit`); this `Prop`
names the remaining assembly (splicing circuits at shared vertices across the
connected support) so it is not silently claimed as done. -/
def EulerianSufficient : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : SignedBiGraph V E),
    0 < Fintype.card E → G.Balanced Finset.univ → G.SupportConnected Finset.univ →
      ∃ hs : List (Half E), G.IsEulerTrailOn Finset.univ hs

end AssemblyP1.BidirectedEulerian
