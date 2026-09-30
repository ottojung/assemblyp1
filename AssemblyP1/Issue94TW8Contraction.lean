import AssemblyP1.BBTUniqueEulerian
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94TW8Contraction

open SourceFaithfulIs
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1

/- `open AssemblyP1.Issue94TW6Lemma1` was removed together with the import: no
identifier of that module was used here, so the module's independence from tw6
is now structural rather than incidental.  The relationship between `NoTriple`
and tw6's degree fact is provenance only, and is described in the docstring
below. -/

/- `NOTE (shadowing).`  `outDeg`/`inDeg` below are *this* module's names; `inDeg`
also exists at `AssemblyP1.BBTSequenceGraph` (`BBTCondense.lean:213`), which
`open AssemblyP1.BBTSequenceGraph` above brings into scope, and `deg`/`vtx` are
brought in by `open AssemblyP1`.  A bare `inDeg` in this file means the one
defined below. -/

variable {α : Type} [DecidableEq α]

theorem length_drop_le' (l : List α) (n : ℕ) : (l.drop n).length ≤ l.length := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih => cases n with
    | zero => simp
    | succ n => show (t.drop n).length ≤ (a :: t).length
                have h := ih n; simp only [List.length_cons] at h ⊢; omega

/-- The source's merged node `u_1^end v_{o+1}^end` with the overlap `o`
made **explicit**: `u` concatenated with the tail of `v` past its first `o`
symbols.  In `Defn. d:condensed` the parameter is `olap(u,v)`, a datum of the
*edge* `e = (u,v)`, not of the nodes. -/
def MergeWith (o : ℕ) (u v : List α) : List α := u ++ v.drop o

/-- **The merged node used by this module**: `Merge` is `MergeWith (u.length - 1)`,
i.e. the source's `w = u_1^end v_{olap(u,v)+1}^end` **specialized to
`olap(u,v) = u.length - 1`**, the maximal self-overlap.  It is NOT the source's
formula for an arbitrary edge, and this docstring says so.

*Why the specialisation is the right one in the intended application.*  In the
`(L-1)`-mer multigraph of a word (BBT's `G_0`, the object `BBTSequenceGraph`
enumerates by `nextPos`), two nodes joined by an edge are *consecutive*
`(L-1)`-mers: they share their first `L-2` symbols, so `olap(u,v) = (L-1)-1 =
|u| - 1`.  For that application `Merge u v` is the source's `w`.

*Where it is not sound.*  For any edge of a general `SeqGraph`, or of a graph
whose nodes are `k`-mers with `k < L-1`, or any graph carrying per-edge labels,
the overlap may be smaller than `|u| - 1` and `Merge u v` is then the wrong
node.  `merge_narrowing_witness` below is a kernel-checked witness that the
specialisation is a genuine narrowing and not an identity, and
`mergeWith_eq_merge` is the exact statement of the condition under which it
*is* the source's `w`.

*What is still missing.*  Nothing in this repository states the sentence "for
consecutive `(L-1)`-mers the overlap is `|u| - 1`" in a form that could be
instantiated here: the `K`-mer multigraph of a word does not exist yet (see
the "not established" list, item 2).  So the specialisation is justified by
prose above, not by a Lean hypothesis. -/
def Merge (u v : List α) : List α := MergeWith (u.length - 1) u v

/-- **`Merge` is the source's `w` exactly when the edge's overlap is
`|u| - 1`.**  This is the condition the source's `olap(u,v)` has to meet; the
module fixes it rather than assuming it. -/
theorem mergeWith_eq_merge {u v : List α} {o : ℕ} (h : o = u.length - 1) :
    MergeWith o u v = Merge u v := by
  rw [h, Merge]

/-- **The specialisation is a genuine narrowing, not a coincidence:** an edge
with a strictly smaller overlap gets a different node.  Decided by the kernel
on concrete lists. -/
theorem merge_narrowing_witness :
    MergeWith 0 [0, 1] [1, 1, 1] ≠ Merge [0, 1] [1, 1, 1] := by
  decide

/-- A **sequence graph**: a finite set of labelled nodes together with a
finite set of edges, an edge being an ordered pair of nodes. -/
structure SeqGraph (α : Type) where
  nodes : Finset (List α)
  edges : Finset (List α × List α)
  deriving DecidableEq

/-- Every edge of a well-formed sequence graph joins two of its nodes. -/
def WellFormed (G : SeqGraph α) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ G.nodes ∧ e.2 ∈ G.nodes

/-- The edges leaving `u`: the support of `d⁺(u)`. -/
def outEdges (G : SeqGraph α) (u : List α) : Finset (List α × List α) :=
  G.edges.filter (fun e => e.1 = u)

/-- The edges entering `u`: the support of `d⁻(u)`. -/
def inEdges (G : SeqGraph α) (u : List α) : Finset (List α × List α) :=
  G.edges.filter (fun e => e.2 = u)

/-- **`d⁺(u)`**, the out-degree of `Defn. d:condensed`. -/
def outDeg (G : SeqGraph α) (u : List α) : ℕ := (outEdges G u).card

/-- **`d⁻(u)`**, the in-degree of `Defn. d:condensed`. -/
def inDeg (G : SeqGraph α) (u : List α) : ℕ := (inEdges G u).card

theorem mem_outEdges {G : SeqGraph α} {u v : List α} :
    (u, v) ∈ outEdges G u ↔ (u, v) ∈ G.edges := by
  simp [outEdges]

theorem mem_inEdges {G : SeqGraph α} {u v : List α} :
    (u, v) ∈ inEdges G v ↔ (u, v) ∈ G.edges := by
  simp [inEdges]

/-- **`Defn. d:condensed`, first half.**  The source says:

> For an edge `e = (u,v)` with overlap `olap(u,v)`, *contracting* `e`
> entails two steps: first, merging `u` and `v` along `e` to form a new
> node `w = u_1^end v_{olap(u,v)+1}^end`, and, second, edges to `u` are
> replaced with edges to `w`, and edges from `v` are replaced by edges
> from `w`. **We will only contract edges `(u,v)` with `d⁺(u) = d⁻(v) = 1`.**

`Contractible` is that last sentence, verbatim. -/
def Contractible (G : SeqGraph α) (u v : List α) : Prop :=
  (u, v) ∈ G.edges ∧ outDeg G u = 1 ∧ inDeg G v = 1

/-- The node set after contracting `(u, v)`: the source's `u` and `v` are erased
and the merged node `w` is added.  This **is** the source's first step. -/
def contractNodes (G : SeqGraph α) (u v : List α) : Finset (List α) :=
  (G.nodes.erase u).erase v ∪ {Merge u v}

/-- **The edges that survive contracting `(u, v)`.**  This is the *erasure* half
only: the contracted edge itself, every edge out of `u` and every edge into `v`
are dropped.

The source's second step --- "edges to `u` are replaced with edges to `w`, and
edges from `v` are replaced by edges from `w`" --- is **NOT implemented here**
and `contractEdges` does not do it: the contracted graph produced below has *no*
edge incident to `w` at all.  The step is not implemented because in the source
it is a step on a *labelled multigraph*: the replacement edges carry the
overlap `olap(u,v)` of the edge they came from, and their multiplicities
(`m_C`) are inherited, and this module's `SeqGraph.edges` is an unlabelled
`Finset` with the multiplicity held in a separate function `Mult G`.  Doing the
replacement properly therefore needs (a) the labelled edge multiset of the
`K`-mer graph, which does not exist in this repository yet, and (b) the push
forward of the multiplicity function, which is exactly the quantitative
inheritance the "not established" list, item 5, records as unproved.  A finset
replacement `{(p, w)} ∪ {(w, s)}` alone would be a further narrowing of the
source, and it would falsify `edges_contract_subset` below, which is the
*forward* half of the reconstruction claim and does hold for what is computed
here. -/
def contractEdges (G : SeqGraph α) (u v : List α) : Finset (List α × List α) :=
  G.edges.filter (fun e => e.1 ≠ u ∧ e.2 ≠ v)

/-- **A node-and-edge REDUCTION of `G` along `(u, v)` --- NOT the source's
one-step contraction.**

`Contract G u v` erases the nodes `u` and `v`, inserts the merged node
`Merge u v`, and drops every edge out of `u` or into `v` (including `(u,v)`
itself).  The source's second step, the *replacement* of edges to `u` by edges
to `w` and of edges from `v` by edges from `w`, is **missing**: the result has
no edge incident to `w`, and is therefore not the source's condensed graph.
This definition is deliberately named for what it is; it is not offered as a
transcription of `Defn. d:condensed`, and the earlier claim that it was has
been withdrawn.  `Contractible` is not needed for the construction --- it is the
*permission* to perform the source's contraction, and nothing in this file
performs that contraction. -/
def Contract (G : SeqGraph α) (u v : List α) : SeqGraph α where
  nodes := contractNodes G u v
  edges := contractEdges G u v

@[simp] theorem mem_contractNodes_merge (G : SeqGraph α) (u v : List α) :
    Merge u v ∈ contractNodes G u v :=
  Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self _))

theorem mem_contractNodes_of_mem {G : SeqGraph α} {u v x : List α}
    (hx : x ∈ G.nodes) (hxu : x ≠ u) (hxv : x ≠ v) : x ∈ contractNodes G u v :=
  Finset.mem_union.mpr
    (Or.inl (Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hx⟩⟩))

/-- **The edges of the reduced graph are edges of the original graph.**
Correct for the reduction `Contract` actually is; the source's second step
would create edges `(p, w)` and `(w, s)` that are generally *not* in `G`, so
this lemma must not be read as a statement about the source's condensation. -/
theorem edges_contract_subset (G : SeqGraph α) (u v : List α) :
    (Contract G u v).edges ⊆ G.edges :=
  fun _ h => (Finset.mem_filter.mp h).1

/-- **A surviving edge survives the reduction, unchanged.** -/
theorem mem_contractEdges_of_ne {G : SeqGraph α} {u v : List α} {e : List α × List α}
    (he : e ∈ G.edges) (h1 : e.1 ≠ u) (h2 : e.2 ≠ v) : e ∈ contractEdges G u v :=
  Finset.mem_filter.mpr ⟨he, h1, h2⟩

/-- The merged node is not one of the two erased nodes, provided it is not
already a node of `G`.  The freshness hypothesis `hw` has **no counterpart in
the source**: there `w` is a new node by fiat.  In this module `w` is inserted
into a `Finset` of existing labels, so it can coincide with a node of `G`, and
the side condition is genuine.  It is a hypothesis, not an assumption away; in
the intended application it is discharged by `u ≠ v` together with the fact that
a `(L-1)`-mer `w` of the `K`-mer graph is new whenever its two halves come from
a contractible edge --- a fact this repository does not yet state. -/
theorem merge_not_mem_erase (G : SeqGraph α) (u v : List α) (hw : Merge u v ∉ G.nodes) :
    Merge u v ∉ (G.nodes.erase u).erase v := by
  intro hmem
  have h' : Merge u v ∈ G.nodes.erase u := (Finset.mem_erase.mp hmem).2
  have h'' : Merge u v ∈ G.nodes := (Finset.mem_erase.mp h').2
  exact hw h''

/-- **The measure strictly decreases.**  This is the well-foundedness half of
the fixpoint clause of `Defn. d:condensed`, measured on the *node* set of the
reduction `Contract` (see its docstring: the source's second, replacement step
is not implemented).  The node step --- merge and erase --- *is* the source's
first step, and it is this one that the measure counts.  Both side conditions
(`u ≠ v` and freshness of the merged node, the latter not a source hypothesis)
are explicit binders, not hidden. -/
theorem card_contractNodes_lt (G : SeqGraph α) (u v : List α)
    (hu : u ∈ G.nodes) (hv : v ∈ G.nodes) (hne : u ≠ v)
    (hw : Merge u v ∉ G.nodes) : (contractNodes G u v).card < G.nodes.card := by
  have hdisj : Disjoint ((G.nodes.erase u).erase v) ({Merge u v} : Finset (List α)) := by
    refine Finset.disjoint_left.2 (fun {a : List α} h1 h2 => ?_)
    exact merge_not_mem_erase G u v hw (Finset.mem_singleton.mp h2 ▸ h1)
  have hA : (contractNodes G u v).card = ((G.nodes.erase u).erase v).card + 1 := by
    rw [contractNodes, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  have h1 : ((G.nodes.erase u).erase v).card = (G.nodes.erase u).card - 1 :=
    Finset.card_erase_of_mem (s := G.nodes.erase u) (a := v) (by
      show v ∈ G.nodes.erase u
      exact Finset.mem_erase.mpr ⟨hne.symm, hv⟩)
  have h2 : (G.nodes.erase u).card = G.nodes.card - 1 :=
    Finset.card_erase_of_mem (s := G.nodes) (a := u) (by show u ∈ G.nodes; exact hu)
  have hpos : 0 < G.nodes.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hge : 1 ≤ (G.nodes.erase u).card := by
    have hsub := Finset.card_le_card
      (Finset.singleton_subset_iff.mpr (Finset.mem_erase.mpr ⟨hne.symm, hv⟩))
    simpa using hsub
  have hA' : (contractNodes G u v).card = G.nodes.card - 1 := by
    calc (contractNodes G u v).card = ((G.nodes.erase u).erase v).card + 1 := hA
      _ = (G.nodes.erase u).card - 1 + 1 := by rw [h1]
      _ = (G.nodes.erase u).card := Nat.sub_add_cancel hge
      _ = G.nodes.card - 1 := h2
  rw [hA']
  exact Nat.sub_lt hpos (show (0 : ℕ) < 1 by decide)

/-- **The measure never exceeds the original**, provided the tail `u` is a
node at all (which it is whenever `(u, v)` is an edge). -/
theorem card_contractNodes_le (G : SeqGraph α) (u v : List α) (hu : u ∈ G.nodes) :
    (contractNodes G u v).card ≤ G.nodes.card := by
  have h1 : ((G.nodes.erase u).erase v).card ≤ (G.nodes.erase u).card :=
    Finset.card_le_card (Finset.erase_subset _ _)
  have h2 : (G.nodes.erase u).card + 1 = G.nodes.card := by
    have := Finset.card_erase_of_mem (s := G.nodes) (a := u) hu
    have hpos : 0 < G.nodes.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  calc (contractNodes G u v).card ≤ ((G.nodes.erase u).erase v).card + 1 := by
          rw [contractNodes]; exact Finset.card_union_le _ _
        _ ≤ (G.nodes.erase u).card + 1 := Nat.add_le_add_right h1 1
        _ = G.nodes.card := h2
        _ ≤ G.nodes.card := Nat.le_refl _

/-- A **traversal** of `G`, given by a multiplicity function on the edges:
`m e` is the number of times the traversal uses `e`.  This is `m_C(e)`.

`NOTE (vacuous parameter).`  `G` is **ignored**: `Mult G` is literally the type
`(List α × List α) → ℕ`, so `Mult GA` and `Mult GB` are the same type and `mA`,
`mB` are interchangeable.  Harmless for every statement in this file, but a
trap for the bridge of the "not established" list, where the multiplicity is a
function of `(hG, L, S)`.  The parameter is kept only to keep the statements
readable. -/
def Mult (G : SeqGraph α) : Type := (List α × List α) → ℕ

/-- **The number of traversals of the node `u`**, i.e. `m_C(u)`. -/
def nodeMult (G : SeqGraph α) (m : Mult G) (u : List α) : ℕ :=
  ∑ e ∈ outEdges G u, m e

/-- The same count on the in-edges. -/
def inMult (G : SeqGraph α) (m : Mult G) (u : List α) : ℕ :=
  ∑ e ∈ inEdges G u, m e

/-- **The walk is balanced**: at every node the number of exits equals the
number of entries --- the conservation law of a closed walk. -/
def Balanced (G : SeqGraph α) (m : Mult G) : Prop :=
  ∀ u ∈ G.nodes, inMult G m u = nodeMult G m u

theorem nodeMult_ge_of_mem {G : SeqGraph α} (m : Mult G) {u v : List α}
    (he : (u, v) ∈ G.edges) : m (u, v) ≤ nodeMult G m u :=
  Finset.single_le_sum (f := m) (fun b _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨he, rfl⟩)

theorem inMult_ge_of_mem {G : SeqGraph α} (m : Mult G) {u v : List α}
    (he : (u, v) ∈ G.edges) : m (u, v) ≤ inMult G m v :=
  Finset.single_le_sum (f := m) (fun b _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨he, rfl⟩)

/-- **Two distinct out-edges of one node are both counted.** -/
theorem nodeMult_ge_add {G : SeqGraph α} (m : Mult G) {u : List α}
    {e₁ e₂ : List α × List α}
    (h₁ : e₁ ∈ outEdges G u) (h₂ : e₂ ∈ outEdges G u) (hne : e₁ ≠ e₂) :
    m e₁ + m e₂ ≤ nodeMult G m u := by
  have h2' : e₂ ∈ (outEdges G u).erase e₁ := Finset.mem_erase.mpr ⟨Ne.symm hne, h₂⟩
  calc m e₁ + m e₂ ≤ m e₁ + ∑ x ∈ (outEdges G u).erase e₁, m x :=
        Nat.add_le_add_left (Finset.single_le_sum (f := m) (fun b _ => Nat.zero_le _) h2') _
    _ = ∑ x ∈ outEdges G u, m x :=
      ((Finset.sum_erase_add (f := m) _ h₁).symm.trans (Nat.add_comm _ _)).symm

theorem inMult_ge_add {G : SeqGraph α} (m : Mult G) {u : List α}
    {e₁ e₂ : List α × List α}
    (h₁ : e₁ ∈ inEdges G u) (h₂ : e₂ ∈ inEdges G u) (hne : e₁ ≠ e₂) :
    m e₁ + m e₂ ≤ inMult G m u := by
  have h2' : e₂ ∈ (inEdges G u).erase e₁ := Finset.mem_erase.mpr ⟨Ne.symm hne, h₂⟩
  calc m e₁ + m e₂ ≤ m e₁ + ∑ x ∈ (inEdges G u).erase e₁, m x :=
        Nat.add_le_add_left (Finset.single_le_sum (f := m) (fun b _ => Nat.zero_le _) h2') _
    _ = ∑ x ∈ inEdges G u, m x :=
      ((Finset.sum_erase_add (f := m) _ h₁).symm.trans (Nat.add_comm _ _)).symm

/-- **`l:condensed` (3), the "at least once" half.** -/
def EdgeSurj {G : SeqGraph α} (m : Mult G) : Prop :=
  ∀ e ∈ G.edges, 1 ≤ m e

/-- **"the cycle `C_0` does not traverse any node three times in `G_0`"** ---
the degree fact of the appendix's proof, in this module's vocabulary. -/
def NoTriple {G : SeqGraph α} (m : Mult G) : Prop :=
  ∀ u ∈ G.nodes, nodeMult G m u ≤ 2

/-- **THE CONTRACTION RULE, out-degree half.** -/
theorem twiceTraversed_outDeg_eq_one {G : SeqGraph α} (hwf : WellFormed G)
    (m : Mult G) (hSurj : EdgeSurj m) (hCap : NoTriple m) {u v : List α}
    (he : (u, v) ∈ G.edges) (h2 : 2 ≤ m (u, v)) : outDeg G u = 1 := by
  by_contra hcon
  have hne0 : (0 : ℕ) < outDeg G u := by
    refine Finset.card_pos.mpr ?_
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  have hcard : 2 ≤ (outEdges G u).card := by
    simp only [outDeg] at hcon hne0 ⊢
    omega
  have hmem : (u, v) ∈ outEdges G u := Finset.mem_filter.mpr ⟨he, rfl⟩
  have herase : 0 < ((outEdges G u).erase (u, v)).card := by
    have hc := Finset.card_erase_of_mem hmem
    omega
  obtain ⟨e₂, h₂⟩ := Finset.card_pos.mp herase
  have hne : e₂ ≠ (u, v) := (Finset.mem_erase.mp h₂).1
  have h₂' : e₂ ∈ outEdges G u := (Finset.mem_erase.mp h₂).2
  have hb : m (u, v) + m e₂ ≤ nodeMult G m u := nodeMult_ge_add m hmem h₂' (Ne.symm hne)
  have h3 : 3 ≤ nodeMult G m u := by
    have hle := Nat.add_le_add h2 (hSurj e₂ (Finset.mem_filter.mp h₂').1)
    omega
  exact absurd (hCap u (hwf (u, v) he).1) (by omega)

/-- **THE CONTRACTION RULE, in-degree half.** -/
theorem twiceTraversed_inDeg_eq_one {G : SeqGraph α} (hwf : WellFormed G)
    (m : Mult G) (hBal : Balanced G m) (hSurj : EdgeSurj m) (hCap : NoTriple m)
    {u v : List α} (he : (u, v) ∈ G.edges) (h2 : 2 ≤ m (u, v)) : inDeg G v = 1 := by
  by_contra hcon
  have hne0 : (0 : ℕ) < inDeg G v := by
    refine Finset.card_pos.mpr ?_
    exact ⟨(u, v), Finset.mem_filter.mpr ⟨he, rfl⟩⟩
  have hcard : 2 ≤ (inEdges G v).card := by
    simp only [inDeg] at hcon hne0 ⊢
    omega
  have hmem : (u, v) ∈ inEdges G v := Finset.mem_filter.mpr ⟨he, rfl⟩
  have herase : 0 < ((inEdges G v).erase (u, v)).card := by
    have hc := Finset.card_erase_of_mem hmem
    omega
  obtain ⟨e₂, h₂⟩ := Finset.card_pos.mp herase
  have hne : e₂ ≠ (u, v) := (Finset.mem_erase.mp h₂).1
  have h₂' : e₂ ∈ inEdges G v := (Finset.mem_erase.mp h₂).2
  have hb : m (u, v) + m e₂ ≤ inMult G m v := inMult_ge_add m hmem h₂' (Ne.symm hne)
  have h3in : 3 ≤ inMult G m v := by
    have hle := Nat.add_le_add h2 (hSurj e₂ (Finset.mem_filter.mp h₂').1)
    omega
  have h3 : 3 ≤ nodeMult G m v := by
    rw [← hBal v (hwf (u, v) he).2]
    exact h3in
  exact absurd (hCap v (hwf (u, v) he).2) (by omega)

/-- **THE CONTRACTION RULE.**  Exactly the two sentences of the appendix's
proof, as a rule about the graph: an edge traversed twice is *contractible*,
i.e. `d⁺(u) = d⁻(v) = 1`, and `Defn. d:condensed` contracts it. -/
theorem twiceTraversed_contractible {G : SeqGraph α} (hwf : WellFormed G)
    (m : Mult G) (hBal : Balanced G m) (hSurj : EdgeSurj m) (hCap : NoTriple m)
    {u v : List α} (he : (u, v) ∈ G.edges) (h2 : 2 ≤ m (u, v)) :
    Contractible G u v :=
  ⟨he, twiceTraversed_outDeg_eq_one hwf m hSurj hCap he h2,
    twiceTraversed_inDeg_eq_one hwf m hBal hSurj hCap he h2⟩

/-- **The contrapositive the induction consumes: in a graph with no
contractible edge, no edge is traversed twice.** -/
theorem not_twiceTraversed_of_not_contractible {G : SeqGraph α} (hwf : WellFormed G)
    (m : Mult G) (hBal : Balanced G m) (hSurj : EdgeSurj m) (hCap : NoTriple m)
    (hfix : ∀ u v, ¬ Contractible G u v) {e : List α × List α} (he : e ∈ G.edges) :
    m e ≤ 1 := by
  rcases Nat.lt_or_ge (m e) 2 with h | h
  · omega
  · exact absurd (hfix e.1 e.2
      (twiceTraversed_contractible hwf m hBal hSurj hCap he h)) (by simp)



/-!
# `Defn. d:condensed`: the contraction rule of BBT Theorem 3 (board 94, front tw8)

**Obligation.**  The condensation step named by tw6 §8 point 8 item (c): the
step that takes a graph admitting a unique Eulerian cycle down to a
strictly smaller condensed graph, and the rule that reconstructs a cycle
from the condensed one.  Disjoint from sibling front 94e8, which is
attacking the `AltF = id` step.

## The source, verbatim

Retrieved from `https://arxiv.org/e-print/1301.0068v3` (HTTP 200,
1 357 427 bytes, unpacked into `/tmp/opencode/`), file `appendix_short.tex`.
**The line numbers below were re-derived from the tarball by the repair front
(board 94, front tw8-repair) and supersede the ones originally cited here,
which were off by one to three lines:** the operations paragraph is line
**131**, the definition environment is lines **138--140** (its text line 139),
and the theorem-3 quotation is line **167** (confirmed).  The `.tex` is
hard-wrapped differently from the quotation below; the *text* is identical
except that line 139's trailing commented-out clause
`%, yielding the \emph{condensed sequence graph}.` is omitted here:

```latex
We will perform two basic operations on the sequence graph. For an edge
$e=(\bu,\bv)$ with overlap $\olap\bu\bv$, \emph{merging} $\bu$ and $\bv$
along $e$ produces the concatenation $\bu_1^\text{end}
\bv_{\olap\bu\bv+1}^\text{end}$. \emph{Contracting} an edge $e=(\bu,\bv)$
entails two steps (c.f. Fig.~\ref{fig:condensing}): first, merging $\bu$
and $\bv$ along $e$ to form a new node $\bw=\bu_1^\text{end}
\bv_{\olap\bu\bv+1}^\text{end}$, and, second, edges to $\bu$ are replaced
with edges to $\bw$, and edges from $\bv$ are replaced by edges from $\bw$.
We will only contract edges $(\bu,\bv)$ with $\dout(\bu)=\din(\bv)=1$.

The condensed sequence graph is defined next.
\begin{definition}[Condensed sequence graph] \label{d:condensed}
The \emph{condensed sequence graph} replaces unambiguous paths by single
nodes. Concretely, any edge $e=(u,v)$ with $\dout(u)=\din(v)=1$ is
contracted, and this is repeated until no candidate edges remain.%
\end{definition}
```

`Defn.~\ref{d:condensed}` is therefore exactly two statements:

1. **the one-step rule**: contract `e = (u,v)` when `d⁺(u) = d⁻(v) = 1`,
   merging `u` and `v` into `w = u_1^end v_{olap(u,v)+1}^end` and moving
   the edges accordingly (line 131);
2. **the fixpoint clause**: "this is repeated until no candidate edges
   remain" (line 139).

And the *only* thing the proof of BBT's Theorem 3 uses of it is the
following, `appendix_short.tex:167`, quoted unabridged:

> We argue that every edge $(\bu,\bv)$ traversed twice by $\CC_0$ in the
> $K$-mer graph $\G_0$ has been contracted in the condensed graph $\G$ and
> hence in $\CC$. Note that the cycle $\CC_0$ does not traverse any node
> three times in $\G_0$, for this would imply the existence of a triple
> repeat of length $K$, violating the hypothesis of the Lemma.  It
> follows that the node $\bu$ cannot have two outgoing edges in $\G_0$ as
> $\bu$ would then be traversed three times; similarly, $\bv$ cannot have
> two incoming edges.  Thus $\dout(\bu)=\din(\bv)=1$ and, as prescribed
> in Defn.~\ref{d:condensed}, the edge $(\bu,\bv)$ has been contracted.

## What this module proves

* `MergeWith o u v` is the source's merged node with the overlap made explicit,
  and `Merge u v` is `MergeWith (u.length - 1) u v` --- the source's `w`
  **specialized** to `olap(u,v) = |u| - 1` (see `Merge`'s docstring for where
  that is and is not the source's `w`; `mergeWith_eq_merge` is the exact
  condition, and `merge_narrowing_witness` is the kernel-checked witness that
  the specialisation really does narrow the rule).
* `contractNodes G u v` is the source's **first** step of contraction (merge
  `u, v` into `w`, erase `u` and `v`).  `Contract G u v` is a **node-and-edge
  reduction**, NOT the source's one-step contraction: the source's **second**
  step --- edges to `u` replaced by edges to `w`, edges from `v` replaced by
  edges from `w` --- is **not implemented**,   and `Contract`'s docstring says so
  and gives the reason (labelled multigraph + multiplicity push-forward).
  The gap is not merely asserted: `no_w_edge_after_contract` and
  `source_replacement_edges_absent` in §6 check by `decide` that after
  contracting the contractible edge `a → b` of `GA` the reduced graph has no
  edge incident to `w` at all, and that the two edges the source's second step
  would have rewritten are missing from it.
  An earlier version of this docstring called `Contract` a transcription of
  `Defn. d:condensed`; that claim was wrong and has been withdrawn.
* `card_contractNodes_lt`: the **induction measure**, and nothing more.  For a
  *single* step satisfying its four stated side conditions (`u ∈ G.nodes`,
  `v ∈ G.nodes`, `u ≠ v`, and `Merge u v ∉ G.nodes`), the node count strictly
  decreases.  This does **not** establish the well-foundedness of "repeated
  until no candidate edges remain": nothing here shows that those side
  conditions persist along a *sequence* of contractions.  In particular
  `hw : Merge u v ∉ G.nodes` is not implied by `Contractible` (which is only
  `(u,v) ∈ G.edges ∧ outDeg G u = 1 ∧ inDeg G v = 1`), and in a genuine
  condensation the merged node `w` may already be a node of `G`, in which case
  the count does not strictly drop and this measure is not available as a
  decreasing measure along the iteration.  The measure-persistence gap is
  separate from item 3 below (which concerns order-independence) and is
  **not** discharged here.  Whether `Merge`-freshness is expected to be
  satisfiable along a genuine condensation, or whether `card` is the wrong
  measure, is a question about the source's condensation that this module does
  not answer.
* `twiceTraversed_contractible`: **the contraction rule**, i.e. the two
  sentences "the node `u` cannot have two outgoing edges ... thus
  `d⁺(u) = d⁻(v) = 1` and the edge `(u,v)` has been contracted", as a
  theorem about a graph and a traversal of it.  It concludes `Contractible`,
  the *permission* to contract; the contraction itself is not performed here.
* `not_twiceTraversed_of_not_contractible`: the contrapositive in the
  shape the induction consumes --- in a graph with no contractible edge
  no edge is traversed twice.

### Why the `SeqGraph` layer is load-bearing

Not because of node *lengths*: `BBTSequenceGraph`'s node type is
`Fin (L-1) → α`, and a merged node of length `K+1` (this is `Merge u v` at
`|u| = |v| = K`, **not** `2K-1`, which would be the length at overlap `1`)
would fit that type perfectly well --- `Fin (K+1) → α` is exactly as available
as `Fin (L-1) → α`.  An earlier version of this docstring gave the length
reason; it was arithmetically false and is withdrawn.  The real reason:

* `BBTSequenceGraph` is a **namespace of functions** (`vtx`, `deg`, `inDeg`,
  `fibre`, `Branch`, `branchStarts`).  There is **no node finset, no edge
  finset, no multiplicity function and no contraction operation** anywhere in
  the repository, so a graph-level statement about `d⁺`, `d⁻` and "the nodes
  strictly decrease" is simply not expressible there.
* `NOTE (a conversion lemma will be needed):` this module's nodes are
  `List α`, while the repository speaks `Fin (L-1) → α`.  Any bridge to a word
  (`G_0`) must convert, and that conversion is part of the missing bridge below.

## Where the primitivity hypothesis enters --- nowhere; it is a hypothesis

`twiceTraversed_contractible` has four hypotheses, and the derivation
uses them as follows.

| hypothesis | source | what it does in the proof |
| --- | --- | --- |
| `hSurj : EdgeSurj m` --- every edge is traversed at least once | `l:condensed` (3), "As noted in Lemma~\ref{l:condensed}, `C` traverses each edge at least once" | supplies `1 ≤ m e₂` for the *second* out-edge `e₂` of the tail.  Without it the count `m (u,v) + m e₂ ≥ 2 + 1 = 3` collapses to `≥ 2`. |
| `hCap : NoTriple m` --- no node is traversed three times | "Note that the cycle `C_0` does not traverse any node three times in `G_0`, for this would imply the existence of a triple repeat of length `K`" | **This is the only place where the word would enter.**  It is the degree fact.  **Nothing from `Issue94TW6Lemma1` is used at the Lean level**: this module does not import it, and no identifier from it occurs here.  The relationship is a *provenance* one: `hCap` is the hypothesis that the bridge of item 2 below would discharge from `Issue94TW6Lemma1.prim_deg_le_two` (or `deg_fact_of_primitive`, or `no_three_of_P2`) once that bridge exists.  It is **not** "tw6's theorem, relayed": `NoTriple` bounds `nodeMult` on an abstract `SeqGraph`, `prim_deg_le_two` bounds `BBTSequenceGraph.deg` on a `(L-1)`-mer multigraph of a circular word, and no theorem in this repository identifies the two predicates --- that identification *is* the missing lemma (items 2 and 9 of the board report).  A `P2` word satisfies the word-level form and `P2` includes primitivity.  The form of the degree fact needing no condition on the word, **at length `K`**, is FALSE: tw6's kernel-checked counterexample at `S = 012012012`, `G = 9`, `K = 3` gives `¬ (mkGenome hG9 S9).IsTripleRepeat e 0 3 6` for `e = 3`, `4` and `8`.  That is **one** triple of starts at **three** lengths; the lengths `5, 6, 7` and all other triples of starts are not checked, so the `≥ K` reading of the degree fact is **left open** by that counterexample and is not refuted here either. |
| `hBal : Balanced G m` --- the walk is closed | a closed walk | transfers the cap from the out-count to the in-count, which is what makes the in-degree half (`d⁻(v) = 1`) follow. |
| `hwf : WellFormed G` | --- | only to know that `u` and `v` are nodes, so that the cap applies to them. |

**No primitivity, no `Ukkonen`, no `P2` and no word appears anywhere else
in the module.**  §1-§3 and the degree lemmas are pure graph theory; the
`NoTriple` hypothesis is a *hypothesis of the theorem*, not a consequence
proved here.  §6 exhibits, at concrete kernel-checked values, a graph `GB`
and a traversal `mB` satisfying `WellFormed`, `EdgeSurj` and `2 ≤ mB (a,b)`
for which `NoTriple` **fails** and the conclusion `d⁺(a) = 1` of the
out-degree half is **false** --- so `hCap` is load-bearing for that half.
**Scope of that claim, stated precisely:** `GB` is *not* a refutation of the
whole rule `twiceTraversed_contractible` with `NoTriple` dropped, because that
theorem also needs `Balanced`, and `Balanced GB mB` is **false**
(`not_balanced_GB`: at `a`, `nodeMult = 4` while `inMult = 1`).  See §6.

## What is NOT established (read this before the rest)

1. **`hPevzner` (`BBTEulerian.EulerianCycleObstruction` at
   `AssemblyP1/PopulationUniqueness.lean` lines 164, 217, 247) is NOT
   discharged and is not touched by this module.**  It remains the issue's
   public endpoint and an explicit hypothesis.
2. **The bridge from the word to the `K`-mer multigraph is NOT proved.**
   This module's `SeqGraph` is an abstract finite directed multigraph.
   The missing statement is that, for the `K = L-1` `K`-mer multigraph of
   a word `S` with the truth's cycle as its traversal, (a) the traversal is
   edge-surjective, (b) it is balanced, (c) `nodeMult G m v = deg hG L S v`
   for every node `v`, and (d) hence `NoTriple` follows from
   `Issue94TW6Lemma1.prim_deg_le_two`.  This is exactly the place where
   `prim_deg_le_two` would be consumed.  **It is a genuine missing lemma,
   not a formality**, and it is stated in the board report.  Part (c) also
   needs the `List α` → `Fin (L-1) → α` conversion noted above, and it must be
   stated at *this* module's node type, not at `BBTSequenceGraph`'s.
3. **Order-independence (`l:condensed` (1), "Edges in `G_0` can be
   contracted in any order, resulting in the same graph") is NOT proved.**
   The precise missing statement is in the board report.  Consequently the
   *fixpoint* clause of `Defn. d:condensed` is not proved either: what is
   proved is the **measure** (`card_contractNodes_lt`), which is the
   well-foundedness half of the fixpoint argument, not the
   order-independence half.
4. **The replacement half of the contraction is NOT proved, and the
   label/overlap half is NOT proved either.**  `Contract` implements only
   merge-and-erase (the source's first step); the source's second step ---
   "edges to `u` are replaced with edges to `w`, and edges from `v` are
   replaced by edges from `w`" --- is absent from this module, and so is the
   statement that a replaced edge keeps the *same* overlap `o` (a
   `List.take`/`List.drop` lemma about `MergeWith`).  The node side is
   additionally specialized to `olap(u,v) = |u| - 1`; see `Merge`'s docstring
   and the kernel-checked `merge_narrowing_witness`.  So of the source's
   one-step rule this module formalizes the *degree* half of the permission
   (`Contractible`), the *first* (merge/erase) step, and the measure; it does
   **not** formalize the *second* (replacement) step.
5. **"the cycle is reconstructed from the condensed one" is only half
   done.**  The *forward* half is `edges_contract_subset` and
   `mem_contractEdges_of_ne` (a surviving edge survives unchanged, so
   a cycle of the reduced graph reads the same edges) --- correct for the
   reduction actually computed here, and to be read with the caveat on those
   two lemmas.  The *quantitative* half --- that a balanced, edge-surjective
   traversal of `G` pushes forward to a balanced, edge-surjective traversal of
   `Contract G u v`, i.e. `l:condensed` (3) inherited through the contraction
   --- is **not proved**, and its precise statement is in the report.  It is
   also not fully *statable* yet: a push-forward along a reduction that keeps
   no edge incident to `w` is not the source's statement (item 4).
6. Nothing was proved about the "at most once" conclusion *in the condensed
   graph*, i.e. that every edge of the fixpoint is traversed exactly once.
   That needs items 3, 4 and 5 plus the uniqueness argument, and it is the
   remaining content of BBT Theorem 3.

No `sorry`, no `admit`, no `native_decide`, no new axiom, no `set_option`
weakening (the three `set_option`s above are *linter* suppressions only).  Every
numerical statement in §6 is plain `by decide` --- **not** `decide +kernel`:
`+kernel` changes only the printed form of a closed term, so asserting it would
describe a check that was not performed.  Plain `decide` reduces through the
kernel and cannot reach `native_decide`.  `AssemblyP1.lean` carries
`#print axioms` lines for the 34 declarations this module had when it was first
merged; the declarations added since are audited in the repair report, not in
that list. -/

/-! ## 6. Instances: the rule is applicable, and its out-degree hypothesis is
load-bearing.

Two kernel-checked finite instances, both with symbol type `Fin 2` and both
`decide`-checked.  These are *correctness* checks of the rule, not
object-count / storage checks: the first exhibits a traversal satisfying the
hypotheses for which the conclusion is a specific, checkable value; the second
exhibits a traversal satisfying the *out-degree* half's remaining hypotheses
for which that half's conclusion is **false**.

Every numeric statement below is decided by plain `decide` (kernel-checked,
not `decide +kernel`); the universally quantified hypotheses (`WellFormed`,
`Balanced`, `EdgeSurj`, `NoTriple`) are discharged by hand from those same
decided values, because `decide` cannot synthesise a `DecidablePred` for a `∀`
over the non-`Fintype` node type in this pin (the defect tw6 §6.12 recorded). -/

section Instances

/-- `a = 00`. -/
def na : List (Fin 2) := [0, 0]
/-- `b = 01`. -/
def nb : List (Fin 2) := [0, 1]
/-- `c = 11`. -/
def nc : List (Fin 2) := [1, 1]

/-- **The positive instance.**  Three nodes `a, b, c` in a cycle, with the
single edge `a → b` traversed **twice** --- and likewise for the other two
edges, so that the traversal really is a balanced closed walk.  Here
`d⁺(a) = 1` and `d⁻(b) = 1`, so `(a, b)` is contractible and the rule
applies. -/
def GA : SeqGraph (Fin 2) where
  nodes := {na, nb, nc}
  edges := {(na, nb), (nb, nc), (nc, na)}

/-- The traversal: every edge of `GA` used twice.  Balanced, edge-surjective,
and every node traversed exactly twice --- so `NoTriple` holds *exactly at
its bound*, which is what makes the instance a test rather than a triviality. -/
def mA : Mult GA := fun _ => 2

theorem GA_nodes : GA.nodes = {na, nb, nc} := rfl
theorem wellFormed_GA : WellFormed GA := by
  intro e he
  simp only [GA, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h
  · subst h; simp [GA, Finset.mem_insert, Finset.mem_singleton]
  · subst h; simp [GA, Finset.mem_insert, Finset.mem_singleton]
  · subst h; simp [GA, Finset.mem_insert, Finset.mem_singleton]

theorem balanced_GA : Balanced GA mA := by
  intro u hu
  simp only [GA, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h
  · subst h; decide
  · subst h; decide
  · subst h; decide

theorem edgeSurj_GA : EdgeSurj mA := by
  intro e he
  simp only [GA, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h <;> subst h <;> decide

theorem noTriple_GA : NoTriple mA := by
  intro u hu
  simp only [GA, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with h | h | h <;> subst h <;> decide

/-- The edge `a → b` is traversed **twice**: the hypothesis of the rule. -/
theorem mA_ab : mA (na, nb) = 2 := by decide

/-- **`d⁺(a) = 1` and `d⁻(b) = 1`**: the source's conclusion
`d⁺(u) = d⁻(v) = 1`, decided. -/
theorem outDeg_GA_a : outDeg GA na = 1 := by decide
theorem inDeg_GA_b : inDeg GA nb = 1 := by decide

/-- **The rule applies to `GA` and yields exactly the source's conclusion.** -/
theorem GA_ab_contractible : Contractible GA na nb :=
  twiceTraversed_contractible wellFormed_GA mA balanced_GA edgeSurj_GA noTriple_GA
    (by decide) (by decide)

/-- The merged node of the contractible edge `a → b` of `GA`. -/
theorem merge_na_nb : Merge na nb = [0, 0, 1] := by decide

/-- **The source's second step really is absent --- kernel-checked, not
asserted.**  Contracting the contractible edge `a → b` of `GA` leaves exactly
the two edges that touch neither `a` nor `b`, i.e. `c → a` and `b → c`; the
source would in addition have produced `c → w` and `w → c`. -/
theorem contractEdges_GA_na_nb : (Contract GA na nb).edges = {(nc, na), (nb, nc)} := by
  decide

/-- **No edge of the reduced graph is incident to the merged node `w`.**  This
is `Contract`'s defining gap, made machine-checked. -/
theorem no_w_edge_after_contract :
    ∀ e ∈ (Contract GA na nb).edges, e.1 ≠ Merge na nb ∧ e.2 ≠ Merge na nb := by
  decide

/-- **The source's replacement edges are absent.**  The edges that the source's
second step would have rewritten, `c → a` and `b → c`, are present in `GA` and
missing from the reduction. -/
theorem source_replacement_edges_absent :
    (nc, na) ∈ GA.edges ∧ (nb, nc) ∈ GA.edges
      ∧ (nc, Merge na nb) ∉ (Contract GA na nb).edges
      ∧ (Merge na nb, nc) ∉ (Contract GA na nb).edges := by
  decide

/-- **THE NON-VACUITY CHECK.**  Every hypothesis of the contraction rule is
satisfiable on a concrete graph, and the conclusion `d⁺(u) = d⁻(v) = 1` holds
there --- while it is *false* for a traversal violating the cap (`GB` below),
so the theorem is not an artefact of an empty hypothesis class.  (This is
non-vacuity of the *hypothesis class*, i.e. satisfiability; it is not a
mutation test.  The mutation test is `GB`, and its scope is stated there.) -/
theorem GA_nodes_three : GA.nodes.card = 3 := by decide

/-- **The negative instance.**  `GB` is `a → b` (used **three** times)
together with `a → c` (used once), and `b → a`.  Then `a` is traversed four
times, `d⁺(a) = 2`, and the out-degree half's conclusion `d⁺(a) = 1` is
**false**.  `wellFormed_GB`, `edgeSurj_GB` and `mB_ab` below show that every
*other* hypothesis of `twiceTraversed_outDeg_eq_one` is satisfied here, so that
theorem with `NoTriple` removed is refuted at these concrete values.

**What this instance does NOT show.**  It does not refute
`twiceTraversed_contractible` with `NoTriple` removed: that theorem also
requires `Balanced`, and `Balanced GB mB` is false, as `not_balanced_GB` below
proves.  Any claim that dropping `NoTriple` refutes "the rule" as a whole
would be unsupported. -/
def GB : SeqGraph (Fin 2) where
  nodes := {na, nb, nc}
  edges := {(na, nb), (na, nc), (nb, na)}

def mB : Mult GB := fun e => if e = (na, nb) then 3 else 1

theorem outDeg_GB_a : outDeg GB na = 2 := by decide
theorem mB_ab : mB (na, nb) = 3 := by decide
theorem nodeMult_GB_a : nodeMult GB mB na = 4 := by decide

theorem wellFormed_GB : WellFormed GB := by
  intro e he
  simp only [GB, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h
  · subst h; simp [GB, Finset.mem_insert, Finset.mem_singleton]
  · subst h; simp [GB, Finset.mem_insert, Finset.mem_singleton]
  · subst h; simp [GB, Finset.mem_insert, Finset.mem_singleton]

theorem edgeSurj_GB : EdgeSurj mB := by
  intro e he
  simp only [GB, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h <;> subst h <;> decide

/-- **The refutation of the out-degree half, on concrete values.**  `GB`,
`mB` satisfy `WellFormed`, `EdgeSurj` and `2 ≤ mB (a,b)`, and the conclusion
`d⁺(a) = 1` of `twiceTraversed_outDeg_eq_one` is false there.  So `NoTriple`
is load-bearing for that theorem.  The `NoTriple` hypothesis it violates is
witnessed by `not_noTriple_GB` below. -/
theorem not_outDeg_GB_a : outDeg GB na ≠ 1 := by decide

theorem inMult_GB_a : inMult GB mB na = 1 := by decide

/-- **`GB` is not balanced**, so it is *not* a counterexample to the whole
rule.  Stated so that the scope of `not_outDeg_GB_a` cannot be overread. -/
theorem not_balanced_GB : ¬ Balanced GB mB := by
  intro h
  have hna := h na (by decide)
  rw [inMult_GB_a, nodeMult_GB_a] at hna
  omega

/-- The traversal cap fails exactly where the theorem says it must. -/
theorem not_noTriple_GB : ¬ NoTriple mB := by
  intro h
  have hc : nodeMult GB mB na ≤ 2 := h na (by decide)
  have h4le : (4 : ℕ) ≤ nodeMult GB mB na := Nat.le_of_eq nodeMult_GB_a.symm
  exact absurd (h4le.trans hc) (by decide)

end Instances
end AssemblyP1.Issue94TW8Contraction
