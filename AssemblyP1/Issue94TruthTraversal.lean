import AssemblyP1.BBTEulerian

/-!
# Board 94, front `hpevroute`: the word-to-multigraph bridge, and a refutation
# of the obstruction map's proposed §5b statement

**EVERY DECLARATION IN THIS FILE IS UNCOMPILED.**  This front held no Lean
process; the host's compilation window was held by another live front on this
issue.  Every signature this file invokes is quoted, with `file:line`, in
`/workspace/BOARD94-HPEV-ROUTE.md`, so that a reader can check the draft
without a compiler.  There is no `sorry`, no `admit`, no `axiom`, no
`native_decide`, and no `set_option` that removes an obligation.

## Placement

`/workspace/BOARD94-HPEV-MAP.md` §5b asks for this to be a new section of
`AssemblyP1/BBTEulerian.lean` between §3 (the obstruction section, which ends
at `AssemblyP1/BBTEulerian.lean:520`) and §4 (the `Objects` section, at
`:524`).  That is the right place and the code below is written to be pasted
there **unchanged**: `BBTEulerian.lean` already carries
`open OrientedRigidity` (`:158`), `open AssemblyP1.BBTChords` (`:160`),
`open AssemblyP1.BBTSequenceGraph` (`:161`) and
`variable {α : Type} [DecidableEq α]` (`:164`), and imports
`AssemblyP1.BBTCondense` (`:2`), which transitively imports `Mathlib`.  It is
kept in a separate file here only so that no *shared* file of the tree is left
carrying uncompiled text.

## §1. THE PROPOSED STATEMENT IS FALSE.  The hypothesis is on a vertex, not
## on an edge.

`BOARD94-HPEV-MAP.md` §5b proposes

```lean
theorem truth_traversal_edgeSurj {G : ℕ} (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) :
    ∀ (v w : Fin (L - 1) → α), (G ≤ nodeCount (L := L) hG S v) →
      ∃ (r : Fin G), vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w
```

This is **refutable**, and the refutation is forced, not incidental.
`BBTSequenceGraph.deg_le` (`AssemblyP1/BBTCondense.lean:352`) is
`deg hG L S v ≤ G`, and `deg` is *definitionally* `nodeCount`
(`AssemblyP1/BBTCondense.lean:230`).  Hence the hypothesis `G ≤ nodeCount v`
forces `nodeCount v = G`, i.e. **every** start spells `v`; then
`vtx (nextPos hG r) = v` for every `r`, so the conclusion holds only for
`w = v`.  Taking `w ≠ v` refutes it.  §2 below states this as a general lemma
(`nodeCount_eq_G_imp`) and then instantiates it.

The hypothesis is a statement about a *vertex*: it says the whole circle spells
one `(L-1)`-mer.  Edge-surjectivity is a statement about *edges*, i.e. about
the pair `(v, w)`.  §3 therefore replaces `nodeCount v` by the edge count
`edgeCount v w`, and §4 identifies that edge count with the multiplicity of
the corresponding `L`-mer in the complete spectrum.  That identification is the
substance of the word-to-multigraph bridge.

`hLG : L ≤ G` is not needed anywhere in the corrected development; the
corrected statements hold for every `G > 0` and every `L ≥ 2`.

## §2. The `Decidable` / `Finset` question, resolved concretely

The map warns that "this becomes fiddly fast if `DecidableEq α` is not in the
ambient `variable` block".  It **is** in the ambient block
(`AssemblyP1/BBTEulerian.lean:164`), and it is enough:

* `OrientedRigidity.nodeCount` (`AssemblyP1/OrientedRigidity.lean:644`) takes
  `{α : Type} [DecidableEq α]`, satisfied by the ambient instance.
* The new predicate `vtx hG L S r = v` lives in the type
  `Fin (L - 1) → α`, whose `DecidableEq` comes from
  `Mathlib.Data.Fintype.Defs.decidablePiFintype`
  (`Mathlib/Data/Fintype/Defs.lean:204`), which needs only
  `[Fintype (Fin (L - 1))]` (an instance for every `n`) and `[DecidableEq α]`.
  **No `classical` is required anywhere in this file**, and none is used.
* The direction "cardinality `> 0` gives an existential" is
  `Finset.card_pos : 0 < #s ↔ s.Nonempty`
  (`Mathlib/Data/Finset/Card.lean:78`) followed by
  `Finset.Nonempty.exists_mem : s.Nonempty → ∃ x, x ∈ s`
  (`Mathlib/Data/Finset/Empty.lean:67`).  That is the whole of the "hardest
  step" the map predicts, and it is two lines.  The genuinely hard step is the
  one the map did not name: the pointwise equivalence of the *predicates*
  `vtx r = v ∧ vtx (nextPos r) = w` and `window r = <the glued L-mer>`, which
  is §4.

## §3. What this file does and does not give

It gives, at the node type `Fin (L - 1) → α`:

* §3.1 edge-surjectivity of the truth's own traversal onto the multigraph whose
  edge set is the image of `r ↦ (vtx r, vtx (nextPos r))` — this is the
  corrected `truth_traversal_edgeSurj`;
* §4.1 the identification `edgeCount v w = specCount (glue v w)`, i.e. the
  number of times the truth traverses the directed edge `(v, w)` is exactly the
  multiplicity of the corresponding `L`-mer in the complete spectrum.  This is
  the part that connects the multigraph to `specCount`, and hence to the
  endpoint's spectrum hypothesis;
* §5 node multiplicity: the number of traversals of node `v` by the truth's
  own cycle is exactly `BBTSequenceGraph.deg hG L S v`;
* balance is **already in the tree** and is not reproved here:
  `BBTSequenceGraph.inDeg_eq_deg` (`AssemblyP1/BBTCondense.lean:327`) is
  precisely "the number of starts entering `v` equals the number leaving `v`",
  the `Balanced` clause of `Issue94TW8Contraction`
  (`AssemblyP1/Issue94TW8Contraction.lean:284`).

It does **not** give the `Issue94TW8Contraction.SeqGraph` instance, because
`SeqGraph.nodes` and `SeqGraph.edges` are `Finset (List α)` and
`Finset (List α × List α)` (`AssemblyP1/Issue94TW8Contraction.lean:88`), not
`Finset (Fin (L-1) → α)`.  The conversion is a real, separate, unproved step
and it is what `AssemblyP1/Issue94TW8Contraction.lean:551` item 2 says.  See
`/workspace/BOARD94-HPEV-ROUTE.md`, "WHICH FLOATING RESULTS BECOME USABLE".

It does **not** produce the dichotomy and does **not** discharge `hPevzner`.
-/

namespace AssemblyP1.Issue94TruthTraversal

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian

set_option linter.unusedSectionVars false

section TruthTraversal

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. A concrete instance, for the refutation

`S = 00` at `G = 2`, `L = 2`, so the node type is `Fin (2 - 1) → Fin 2`, i.e.
single symbols.  `nodeCount ![0] = 2 = G`, and every vertex entered by the
truth is `![0]`. -/

/-- `S = 00`, at `G = 2`, `L = 2`. -/
def S2 : Fin 2 → Fin 2 := ![0, 0]

theorem hG2 : 0 < 2 := by decide

/-- Every start of `S2` spells the single symbol `0`. -/
theorem vtx_S2 (r : Fin 2) : vtx hG2 2 S2 r = ![0] := by
  funext j
  rfl

/-- Hence `G ≤ nodeCount v` holds for the vertex `![0]` at `G = 2`, `L = 2`. -/
theorem nodeCount_S2_zero : nodeCount (L := 2) hG2 S2 ![0] = 2 := by
  have hset : ((Finset.univ : Finset (Fin 2)).filter
      (fun r : Fin 2 => nodeWindow (L := 2) hG2 S2 r = ![0])
      : Finset (Fin 2)) = Finset.univ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext j
    rfl
  show ((Finset.univ : Finset (Fin 2)).filter
      (fun r : Fin 2 => nodeWindow (L := 2) hG2 S2 r = ![0])).card = 2
  rw [hset, Finset.card_univ, Fintype.card_fin]

/-! ## 2. The general form of the refutation: `G ≤ nodeCount v` pins `v`

`BBTSequenceGraph.card_fibre` (`AssemblyP1/BBTCondense.lean:250`) is
`(fibre hG L S v).card = deg hG L S v`;
`BBTSequenceGraph.mem_fibre` (`AssemblyP1/BBTCondense.lean:253`) is
`r ∈ fibre hG L S v ↔ vtx hG L S r = v`;
`BBTSequenceGraph.deg_le` (`AssemblyP1/BBTCondense.lean:352`) is
`deg hG L S v ≤ G`; and `Finset.eq_of_subset_of_card_le`
(`Mathlib/Data/Finset/Card.lean:285`) is `(s ⊆ t) → #t ≤ #s → s = t`. -/

theorem nodeCount_eq_G_imp (v : Fin (L - 1) → α) (h : G ≤ nodeCount (L := L) hG S v)
    (r : Fin G) : vtx hG L S r = v := by
  have hle : nodeCount (L := L) hG S v ≤ G := deg_le hG L S v
  have hcard : (fibre hG L S v).card = G := by
    have h2 : (fibre hG L S v).card = nodeCount (L := L) hG S v := card_fibre
    omega
  have hsub : fibre hG L S v ⊆ (Finset.univ : Finset (Fin G)) := Finset.subset_univ _
  have heq : fibre hG L S v = (Finset.univ : Finset (Fin G)) :=
    Finset.eq_of_subset_of_card_le hsub (by simp)
  refine (mem_fibre hG L S).mp ?_
  rw [heq]
  exact Finset.mem_univ r

/-- **The proposed statement of `BOARD94-HPEV-MAP.md` §5b is false**, and
this is the refutation, as a single self-contained `¬`-theorem. -/
theorem not_edgeSurj_S2 :
    ¬ ((2 ≤ nodeCount (L := 2) hG2 S2 ![0]) →
        ∃ r : Fin 2, vtx hG2 2 S2 r = ![0] ∧
          vtx hG2 2 S2 (nextPos hG2 r) = ![1]) := by
  intro h
  have hnn : nodeCount (L := 2) hG2 S2 ![0] = 2 := nodeCount_S2_zero
  obtain ⟨r, hr1, hr2⟩ := h hnn
  have hz := nodeCount_eq_G_imp hG2 2 S2 ![0] hnn (nextPos hG2 r)
  have hcontra : ![0] = ![1] := hz.symm.trans hr2
  exact absurd hcontra (by decide)

/-! ## 3. The corrected edge-surjectivity -/

/-- **The edge of the `(L-1)`-mer multigraph traversed at start `r`.**  This
is the successor relation of the truth's own cycle, by definition: the truth's
traversal *is* `nextPos`. -/
def truthEdge (hG : 0 < G) (L : ℕ) (S : Fin G → α) (r : Fin G) :
    (Fin (L - 1) → α) × (Fin (L - 1) → α) :=
  (vtx hG L S r, vtx hG L S (nextPos hG r))

/-- **The starts at which the truth traverses the directed edge `(v, w)`.**
This is the `Finset` that the map's `nodeCount` should have been. -/
def edgeStarts (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v w : Fin (L - 1) → α) :
    Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w)

/-- **The edge multiplicity: how many times the truth traverses `(v, w)`.** -/
def edgeCount (hG : 0 < G) (L : ℕ) (S : Fin G → α) (v w : Fin (L - 1) → α) : ℕ :=
  (edgeStarts hG L S v w).card

theorem mem_edgeStarts_iff {v w : Fin (L - 1) → α} {r : Fin G} :
    r ∈ edgeStarts hG L S v w ↔ vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w :=
  Iff.rfl

/-- The edge set of the `(L-1)`-mer multigraph of `S`, as a `Finset` of
pairs.  (Stated this way because the vertex type `Fin (L-1) → α` is not a
`Fintype`, so no sum over all vertices is expressible --- the reason recorded
in the module docstring of `AssemblyP1/BBTCondense.lean`.) -/
def edgeSet (hG : 0 < G) (L : ℕ) (S : Fin G → α) :
    Finset ((Fin (L - 1) → α) × (Fin (L - 1) → α)) :=
  Finset.univ.image (truthEdge hG L S)

/-- **THE CORRECTED EDGE-SURJECTIVITY, in the direction the map asked for.**
A positive *edge* count gives a start.  `Finset.card_pos`
(`Mathlib/Data/Finset/Card.lean:78`) and `Finset.Nonempty.exists_mem`
(`Mathlib/Data/Finset/Empty.lean:67`). -/
theorem truth_traversal_edgeSurj (v w : Fin (L - 1) → α)
    (h : 0 < edgeCount hG L S v w) :
    ∃ r : Fin G, vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w := by
  obtain ⟨r, hr⟩ := (Finset.card_pos.mp h).exists_mem
  exact ⟨r, (mem_edgeStarts_iff hG L S).mp hr⟩

/-- **Every edge of the multigraph is traversed, in the `EdgeSurj` shape of
`AssemblyP1/Issue94TW8Contraction.lean:317`.** -/
theorem truth_edgeSurj (e : (Fin (L - 1) → α) × (Fin (L - 1) → α))
    (he : e ∈ edgeSet hG L S) : 1 ≤ edgeCount hG L S e.1 e.2 := by
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp he
  show 1 ≤ (Finset.univ.filter (fun r : Fin G =>
      vtx hG L S r = vtx hG L S r ∧
        vtx hG L S (nextPos hG r) = vtx hG L S (nextPos hG r))).card
  exact (Finset.card_pos.mpr
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, rfl⟩⟩).le

/-! ## 4. The substance: the edge count IS the spectrum multiplicity

`OrientedRigidity.window` (`AssemblyP1/OrientedRigidity.lean:617`) is the
length-`L` window, `OrientedRigidity.nodeWindow`
(`AssemblyP1/OrientedRigidity.lean:621`) the length-`L-1` one, and the two have
*literally the same body*, so `vtx hG L S r` is the length-`L` window
restricted to `Fin (L - 1)`.  Consequently the length-`L` window at `r` is
determined by the *pair* `(vtx r, vtx (nextPos r))`, and that is the de Bruijn
edge/vertex dictionary.

Two lemmas of `AssemblyP1/OrientedRigidity.lean` say exactly this ---
`winPrefix_window` (`:702`) and `winSuffix_window` (`:709`) --- but **both are
`private`**, so they are not reachable from any other module and are
re-derived here.  The re-derivation of the second one is routed through the
*public* `BBTSequenceGraph.window_next`
(`AssemblyP1/BBTCondense.lean:212`) rather than through the modular arithmetic
of the original. -/

/-- **Re-derivation of the `private` `winPrefix_window`.** -/
theorem winPrefix_window' (r : Fin G) :
    winPrefix (window (L := L) hG S r : Fin L → α) = vtx hG L S r := by
  funext d
  rfl

/-- **Re-derivation of the `private` `winSuffix_window`.**  No hypothesis on
`L` is needed: `d : Fin (L - 1)` gives `d.val + 1 < L`. -/
theorem winSuffix_window' (r : Fin G) :
    winSuffix (window (L := L) hG S r : Fin L → α) = vtx hG L S (nextPos hG r) := by
  funext d
  show window (L := L) hG S r ⟨d.val + 1, by have := d.isLt; omega⟩
      = window (L := L) hG S (nextPos hG r) ⟨d.val, by have := d.isLt; omega⟩
  exact window_next hG (L := L) S r (j := d.val) (by have := d.isLt; omega)

/-- **The glued `L`-mer of a directed edge.**  `hL : 2 ≤ L` is what makes the
split exhaustive with both halves inhabited: at `d.val = L - 1` the index
`d.val - 1` is a legal element of `Fin (L - 1)`. -/
def glue {L : ℕ} (hL : 2 ≤ L) (v w : Fin (L - 1) → α) : Fin L → α :=
  fun d => if h : d.val < L - 1 then v ⟨d.val, h⟩ else w ⟨d.val - 1, by omega⟩

theorem glue_winPrefix (v w : Fin (L - 1) → α) : winPrefix (glue hL v w) = v := by
  funext d
  simp [glue]

theorem glue_winSuffix (v w : Fin (L - 1) → α) : winSuffix (glue hL v w) = w := by
  funext d
  simp [glue, Nat.add_sub_cancel]

/-- **The length-`L` window at `r` is the glued `L`-mer of the two vertices
the truth enters at `r` and at `nextPos r`.**  This is the edge/vertex
dictionary, and it is the only genuinely new combinatorial content in this
file. -/
theorem window_eq_glue (hL : 2 ≤ L) (r : Fin G) :
    window (L := L) hG S r = glue hL (vtx hG L S r) (vtx hG L S (nextPos hG r)) := by
  funext d
  by_cases hd : d.val < L - 1
  · simp only [glue, dif_pos hd]
    rfl
  · have hd' : d.val = L - 1 := by omega
    subst hd'
    simp only [glue, dif_neg (by omega)]
    -- `window_next` is stated at `⟨j + 1, _⟩`, and `Fin` does not remember
    -- proofs, so `(L - 2) + 1 = L - 1` is enough for `exact`.
    show window (L := L) hG S r ⟨L - 1, by omega⟩
        = window (L := L) hG S (nextPos hG r) ⟨L - 2, by omega⟩
    exact window_next hG (L := L) S r (j := L - 2) (by omega)

theorem window_eq_pair_iff (hL : 2 ≤ L) {r : Fin G} {v w : Fin (L - 1) → α} :
    (vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w) ↔
      window (L := L) hG S r = glue hL v w := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [window_eq_glue hL r, (glue_winPrefix hL v w).symm,
      (glue_winSuffix hL v w).symm]
  · intro h
    rw [window_eq_glue hL r] at h
    exact ⟨by rw [← glue_winPrefix hL v w, h], by rw [← glue_winSuffix hL v w, h]⟩

/-- **THE BRIDGE LEMMA.  The number of times the truth traverses the directed
edge `(v, w)` is exactly the multiplicity, in the complete `L`-spectrum, of
the `L`-mer formed by overlapping `v` and `w`.**  This is what identifies the
`(L-1)`-mer multigraph of the word with the de Bruijn graph of the spectrum,
and it is the step that makes `specCount` --- the object the endpoint's
hypothesis is about --- the multiplicity function of the multigraph.

Proof: the two `Finset`s being counted have the same membership predicate, by
`window_eq_pair_iff`; `Finset.filter_congr`
(`Mathlib/Data/Finset/Filter.lean:176`) makes them equal, and the right-hand
side is `specCount` by its own definition
(`AssemblyP1/OrientedRigidity.lean:626`). -/
theorem card_edgeCount_eq_specCount (hL : 2 ≤ L) (v w : Fin (L - 1) → α) :
    edgeCount hG L S v w = specCount (L := L) hG S (glue hL v w) := by
  have hcongr : ((Finset.univ : Finset (Fin G)).filter
        (fun r : Fin G => vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w))
      = (Finset.univ : Finset (Fin G)).filter
        (fun r : Fin G => window (L := L) hG S r = glue hL v w) :=
    Finset.filter_congr (fun r _ => window_eq_pair_iff hL)
  show ((Finset.univ : Finset (Fin G)).filter
      (fun r : Fin G => vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w)).card
      = ((Finset.univ : Finset (Fin G)).filter
        (fun r : Fin G => window (L := L) hG S r = glue hL v w)).card
  rw [hcongr]

/-! ## 5. Node multiplicity: the truth's cycle visits `v` exactly `deg v` times

This is item 2(c) of `AssemblyP1/Issue94TW8Contraction.lean:551`, at the
`Fin (L - 1) → α` node type.  It is stated as a sum over **starts** rather
than a sum over vertices, because the vertex type is not a `Fintype`.  Each
start of the fibre of `v` contributes exactly one traversal of the unique
edge it uses out of `v`; `Finset.card_eq_one`
(`Mathlib/Data/Finset/Card.lean:694`) is `#s = 1 ↔ ∃ a, s = {a}` and
`Finset.card_eq_sum_ones`
(`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:966`) is
`#s = ∑ _ ∈ s, 1`. -/

theorem nodeMult_eq_deg (v : Fin (L - 1) → α) :
    ∑ r ∈ (fibre hG L S v), edgeCount hG L S v (vtx hG L S (nextPos hG r))
      = deg hG L S v := by
  have hone : ∀ r ∈ fibre hG L S v,
      edgeCount hG L S v (vtx hG L S (nextPos hG r)) = 1 := by
    intro r hr
    have hmem : r ∈ edgeStarts hG L S v (vtx hG L S (nextPos hG r)) :=
      (mem_edgeStarts_iff hG L S).mpr ⟨(mem_fibre hG L S).mp hr, rfl⟩
    have hcard : (edgeStarts hG L S v (vtx hG L S (nextPos hG r))).card = 1 :=
      Finset.card_eq_one.mpr ⟨r, hmem⟩
    exact hcard
  show (∑ r ∈ (fibre hG L S v), (edgeStarts hG L S v (vtx hG L S (nextPos hG r))).card)
      = (fibre hG L S v).card
  rw [Finset.sum_congr rfl hone, Finset.card_eq_sum_ones, card_fibre]

/-! ## 6. What already exists and is NOT reproved here

* `BBTSequenceGraph.inDeg_eq_deg` (`AssemblyP1/BBTCondense.lean:327`): the
  `Balanced` clause.  It is already proved, on exactly the `nextPos` /
  `prevPos` relation used here.
* `BBTSequenceGraph.branchStarts_eq_biUnion`
  (`AssemblyP1/BBTCondense.lean:407`): the vertex-side disjoint-union
  bookkeeping.  It is already proved; it is *not* re-proved here and it is not
  needed by §3--§5.
* `OrientedRigidity.mem_nodes_of_mem_support`
  (`AssemblyP1/OrientedRigidity.lean:723`): the well-formedness clause, already
  proved, at the `Fin (L-1) → α` node type.
* `OrientedRigidity.truth_pos_on_support`
  (`AssemblyP1/OrientedRigidity.lean:737`) and `OrientedRigidity.truth_total`
  (`AssemblyP1/OrientedRigidity.lean:751`): the `EdgeSurj` and total-mass facts
  at the *spectrum* level, already proved.  §4.1 is the missing translation
  between the two levels.

## 7. The residual

The corrected development stops at the node type `Fin (L - 1) → α`.
`AssemblyP1/Issue94TW8Contraction.SeqGraph` (`:88`) is indexed by `List α`, so

* the instantiation of `WellFormed` (`Issue94TW8Contraction.lean:94`),
  `Balanced` (`:284`), `EdgeSurj` (`:317`) and `NoTriple` (`:322`) for the
  word's own multigraph is **not** supplied by this file, and
* `Issue94TW6Lemma1.prim_deg_le_two` (`AssemblyP1/Issue94TW6Lemma1.lean:579`)
  is already a statement at the `Fin (L-1) → α` node type --- it concludes
  `deg hG L S v ≤ 2` --- so the *content* of `NoTriple` is available and only
  the re-indexing is missing, not the mathematics.

That is the whole of what is left on this line, and it is a re-indexing
problem, not a combinatorial one.  It still does not touch `hPevzner`. -/

end TruthTraversal

end AssemblyP1.Issue94TruthTraversal
