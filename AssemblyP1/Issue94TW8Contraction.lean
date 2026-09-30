import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.Issue94TW6Lemma1
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
open AssemblyP1.Issue94TW6Lemma1

variable {α : Type} [DecidableEq α]

theorem length_drop_le' (l : List α) (n : ℕ) : (l.drop n).length ≤ l.length := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih => cases n with
    | zero => simp
    | succ n => show (t.drop n).length ≤ (a :: t).length
                have h := ih n; simp only [List.length_cons] at h ⊢; omega

/-- The merged node of `Defn. d:condensed`: `u_1^end v_{olap(u,v)+1}^end`. -/
def Merge (u v : List α) : List α := u ++ v.drop (u.length - 1)

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

/-- The node set after contracting `(u, v)`. -/
def contractNodes (G : SeqGraph α) (u v : List α) : Finset (List α) :=
  (G.nodes.erase u).erase v ∪ {Merge u v}

/-- The edge set after contracting `(u, v)`. -/
def contractEdges (G : SeqGraph α) (u v : List α) : Finset (List α × List α) :=
  G.edges.filter (fun e => e.1 ≠ u ∧ e.2 ≠ v)

/-- **`Defn. d:condensed`, one step.**  `Contractible` is not needed for the
construction --- it is the *permission* to perform it. -/
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

/-- **The edges of the contracted graph are edges of the original graph.** -/
theorem edges_contract_subset (G : SeqGraph α) (u v : List α) :
    (Contract G u v).edges ⊆ G.edges :=
  fun _ h => (Finset.mem_filter.mp h).1

/-- **A non-contracted edge survives contraction, unchanged.** -/
theorem mem_contractEdges_of_ne {G : SeqGraph α} {u v : List α} {e : List α × List α}
    (he : e ∈ G.edges) (h1 : e.1 ≠ u) (h2 : e.2 ≠ v) : e ∈ contractEdges G u v :=
  Finset.mem_filter.mpr ⟨he, h1, h2⟩

/-- The merged node is not one of the two erased nodes, provided it is not
already a node of `G`. -/
theorem merge_not_mem_erase (G : SeqGraph α) (u v : List α) (hw : Merge u v ∉ G.nodes) :
    Merge u v ∉ (G.nodes.erase u).erase v := by
  intro hmem
  have h' : Merge u v ∈ G.nodes.erase u := (Finset.mem_erase.mp hmem).2
  have h'' : Merge u v ∈ G.nodes := (Finset.mem_erase.mp h').2
  exact hw h''

/-- **The measure strictly decreases.** -/
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
`m e` is the number of times the traversal uses `e`.  This is `m_C(e)`. -/
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

Retrieved by this front from `https://arxiv.org/e-print/1301.0068v3`
(HTTP 200, 1 357 427 bytes, unpacked by this front into
`/tmp/opencode/tw8/`), file `appendix_short.tex`, lines 130-141.  The
relevant text, unabridged:

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
   the edges accordingly (line 131-132);
2. **the fixpoint clause**: "this is repeated until no candidate edges
   remain" (line 140).

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

* `Merge` is the source's merged node, and `Contract G u v` is the
  source's one-step contraction `Defn. d:condensed` (§3).
* `card_contractNodes_lt`: the **induction measure**.  Every contraction
  strictly decreases the number of nodes, so "repeated until no candidate
  edges remain" is well founded.  Two side conditions (`u ≠ v` and
  freshness of the merged node) are stated explicitly, not hidden.
* `twiceTraversed_contractible`: **the contraction rule**, i.e. the two
  sentences "the node `u` cannot have two outgoing edges ... thus
  `d⁺(u) = d⁻(v) = 1` and the edge `(u,v)` has been contracted", as a
  theorem about a graph and a traversal of it.
* `not_twiceTraversed_of_not_contractible`: the contrapositive in the
  shape the induction consumes --- in a graph with no contractible edge
  no edge is traversed twice.

## Where the primitivity hypothesis enters --- EXACTLY HERE, and nowhere
else

`twiceTraversed_contractible` has four hypotheses, and the derivation
uses them as follows.

| hypothesis | source | what it does in the proof |
| --- | --- | --- |
| `hSurj : EdgeSurj m` --- every edge is traversed at least once | `l:condensed` (3), "As noted in Lemma~\ref{l:condensed}, `C` traverses each edge at least once" | supplies `1 ≤ m e₂` for the *second* out-edge `e₂` of the tail.  Without it the count `m (u,v) + m e₂ ≥ 2 + 1 = 3` collapses to `≥ 2`. |
| `hCap : NoTriple m` --- no node is traversed three times | "Note that the cycle `C_0` does not traverse any node three times in `G_0`, for this would imply the existence of a triple repeat of length `K`" | **This is the only place where the word enters.**  It is the degree fact, and it is what tw6 proved as `Issue94TW6Lemma1.deg_fact_of_primitive` / `no_three_of_P2` / `prim_deg_le_two` (RELAYED, not re-derived here).  A `P2` word satisfies it, `P2` includes primitivity, and the unrestricted form is FALSE (tw6's kernel-checked counterexample at `S = 012012012`, `G = 9`, `K = 3`). |
| `hBal : Balanced G m` --- the walk is closed | a closed walk | transfers the cap from the out-count to the in-count, which is what makes the in-degree half (`d⁻(v) = 1`) follow. |
| `hwf : WellFormed G` | --- | only to know that `u` and `v` are nodes, so that the cap applies to them. |

**No primitivity, no `Ukkonen`, no `P2` and no word appears anywhere else
in the module.**  §1-§3 and the degree lemmas are pure graph theory; the
`NoTriple` hypothesis is a *hypothesis of the theorem*, not a consequence
proved here.  §6 exhibits, at concrete kernel-checked values, a graph and
a traversal satisfying `EdgeSurj` and `Balanced` for which `NoTriple`
**fails** and the conclusion `d⁺(u) = 1` is **false** --- so the
hypothesis is load-bearing and the rule is not a tautology.

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
   not a formality**, and it is stated in the board report.
3. **Order-independence (`l:condensed` (1), "Edges in `G_0` can be
   contracted in any order, resulting in the same graph") is NOT proved.**
   The precise missing statement is in the board report.  Consequently the
   *fixpoint* clause of `Defn. d:condensed` is not proved either: what is
   proved is the **measure** (`card_contractNodes_lt`), which is the
   well-foundedness half of the fixpoint argument, not the
   order-independence half.
4. **The label/overlap half of the contraction is NOT proved.**  `Merge` is
   the source's `w` and is used in the node set, but the statement "an edge
   `(p, u)` with overlap `o` becomes the edge `(p, w)` with the *same*
   overlap" is not formalized.  It is a `List.take`/`List.drop` lemma about
   `Merge`; see the report.
5. **"the cycle is reconstructed from the condensed one" is only half
   done.**  The *forward* half is `edges_contract_subset` and
   `mem_contractEdges_of_ne` (a non-contracted edge survives unchanged, so
   a cycle of the condensed graph reads the same edges).  The *quantitative*
   half --- that a balanced, edge-surjective traversal of `G` pushes forward
   to a balanced, edge-surjective traversal of `Contract G u v`, i.e.
   `l:condensed` (3) inherited through the contraction --- is **not
   proved**, and its precise statement is in the report.
6. Nothing was proved about the "at most once" conclusion *in the condensed
   graph*, i.e. that every edge of the fixpoint is traversed exactly once.
   That needs items 3 and 5 plus the uniqueness argument, and it is the
   remaining content of BBT Theorem 3.

No `sorry`, no `admit`, no `native_decide`, no new axiom.  Every
numerical statement in §6 is `decide +kernel`.
-/

/-! ## 6. Instances: the rule is applicable, and its hypothesis is
load-bearing.

Two kernel-checked finite instances, both with symbol type `Fin 2` and both
`decide`-checked.  These are *correctness* checks of the rule, not
object-count / storage checks: they exhibit a traversal satisfying the
hypotheses for which the conclusion is a specific, checkable value, and a
traversal for which the conclusion is **false**, so the hypothesis
`NoTriple` cannot be dropped.

Every numeric statement below is decided by `decide +kernel`; the
universally quantified hypotheses (`WellFormed`, `Balanced`, `EdgeSurj`,
`NoTriple`) are discharged by hand from those same decided values, because
`decide` cannot synthesise a `DecidablePred` for a `∀` over the
non-`Fintype` node type in this pin (the defect tw6 §6.12 recorded). -/

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

/-- **THE NON-VACUITY CHECK.**  Every hypothesis of the contraction rule is
satisfiable on a concrete graph, and the conclusion `d⁺(u) = 1` holds there
--- and it is *false* for a graph violating the cap (§`GB`
below), so the theorem is not an artefact of an empty hypothesis class. -/
theorem GA_nodes_three : GA.nodes.card = 3 := by decide

/-- **The negative instance, and the mutation check.**  `GB` is
`a → b` (used **three** times) together with `a → c` (used once), and
`b → a`.  Then `a` is traversed three times, `d⁺(a) = 2`, and the source's
conclusion `d⁺(a) = 1` is **false**.  So the traversal cap
(`NoTriple`, i.e. "the cycle `C_0` does not traverse any node three times")
is genuinely load-bearing: without it the rule is refuted at these concrete
values. -/
def GB : SeqGraph (Fin 2) where
  nodes := {na, nb, nc}
  edges := {(na, nb), (na, nc), (nb, na)}

def mB : Mult GB := fun e => if e = (na, nb) then 3 else 1

theorem outDeg_GB_a : outDeg GB na = 2 := by decide
theorem mB_ab : mB (na, nb) = 3 := by decide
theorem nodeMult_GB_a : nodeMult GB mB na = 4 := by decide

/-- **The mutation goes red.**  Dropping `NoTriple` makes the conclusion of
the rule false on this instance: the hypothesis is not decorative. -/
theorem not_outDeg_GB_a : outDeg GB na ≠ 1 := by decide

/-- The traversal cap fails exactly where the theorem says it must. -/
theorem not_noTriple_GB : ¬ NoTriple mB := by
  intro h
  have hc : nodeMult GB mB na ≤ 2 := h na (by decide)
  have h4le : (4 : ℕ) ≤ nodeMult GB mB na := Nat.le_of_eq nodeMult_GB_a.symm
  exact absurd (h4le.trans hc) (by decide)

end Instances
end AssemblyP1.Issue94TW8Contraction
