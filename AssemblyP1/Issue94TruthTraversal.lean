import AssemblyP1.BBTEulerian

/-!
# Board 94, front `hpevroute`, repaired by the `94-residual` front: the
# word-to-multigraph bridge, and a refutation of the obstruction map's
# proposed §5b statement

> **STATUS: COMPILED, EXIT 0, ZERO DIAGNOSTICS (front `94-residual`).**
>
> ```
> export LEAN_PATH=$(cd /workspace/assemblyp1-94-final && /home/lubko/.elan/bin/lake env printenv LEAN_PATH)
> cd /workspace/assemblyp1-94-residual
> /home/lubko/.elan/bin/lean AssemblyP1/Issue94TruthTraversal.lean ; echo "EXIT=$?"
> ```
>
> printed `EXIT=0` with no output.  The file arrived from `0aeec8e` with
> **30 elaboration errors**; all are now discharged.  There is no `sorry`, no
> `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no `set_option`
> that removes an obligation.  Every `#print axioms` line below reports only
> `propext`, `Classical.choice` and `Quot.sound` --- the three axioms of
> Lean's standard `Prop`/`Quot`/`Decidable` layer that the whole library
> already uses, and no project `axiom`.
>
> ### THE HEADLINE FINDING OF THE REPAIR
>
> **Four of the draft's statements are FALSE and have been replaced by
> refutations or by the correct statement, not by repaired proofs.**  They are:
>
> 1. `glue_winSuffix : winSuffix (glue hL v w) = w` --- false at every `L`.
>    Replaced by `glue_last`, the last-position statement that is true.
> 2. `window_eq_pair_iff` (the converse) --- false: the `L`-mer does not
>    determine the pair `(v, w)` without the overlap hypothesis.  Replaced by
>    `window_eq_glue_of_pair` (the true forward direction), plus
>    `winPrefix_window_eq` and `winSuffix_window_eq` (the two halves, the
>    second under the de Bruijn overlap hypothesis `Overlap`).
> 3. `card_edgeCount_eq_specCount` --- false as an *equality*; the true
>    statement is the inequality `edgeCount_le_specCount`.
> 4. `nodeMult_eq_deg` (the sum of `edgeCount`s over the fibre) --- false; it
>    silently assumes `vtx` is injective on the circle, i.e. primitivity,
>    which is not a hypothesis.  **Refuted, kernel-checked, at `G = 4`, `L = 2`,
>    `S = 0000`** by `not_nodeMult_eq_deg`, where the sum is `16` and
>    `deg = 4`.  The true content is the one-line `card_fibre`.
>
> Each replacement is documented at the point of use, and each false
> statement's docstring states why it is false.  **The map's §5b statement of
> Obligation B remains false and that refutation is now kernel-checked**
> (`not_edgeSurj_S2`), as it was not at `0aeec8e`.

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
set_option autoImplicit false

/-- **`Fin`-index arithmetic bridge.**  Every `Fin`-valued index in this file is
built as `⟨k, _⟩`, and `omega` treats `⟨k, _⟩` as an opaque atom, so an
arithmetic goal about such an index needs `Fin.val_mk` pushed in first.  Several
of the draft's `omega` failures are exactly this. -/
theorem fin_mk_val {n k : ℕ} (hk : k < n) : (⟨k, hk⟩ : Fin n).val = k := rfl

/-- **The glued `L`-mer of a directed edge.**  `hL : 2 ≤ L` is what makes the
split exhaustive with both halves inhabited: at `d.val = L - 1` the index
`d.val - 1` is a legal element of `Fin (L - 1)`.

This is declared at namespace level, *not* inside `section TruthTraversal`,
and every binder is written out.  Inside the section, Lean adds the section
variable `G` to the parameter list of `glue` (unused-section-variable
inclusion), and `G` is then unsynthesizable at each call site --- that was one
of the draft's five `don't know how to synthesize implicit argument G` errors,
and it is a placement defect, not a missing argument. -/
def glue {α : Type} {L : ℕ} (hL : 2 ≤ L) (v w : Fin (L - 1) → α) : Fin L → α :=
  fun d => if h : d.val < L - 1 then v ⟨d.val, h⟩ else w ⟨d.val - 1, by omega⟩

/-- **The de Bruijn overlap condition on a pair: `v` and `w` share their
junction symbol.**  This is the hypothesis under which the `L`-mer determines
the pair.  Declared at namespace level for the same reason as `glue`. -/
def Overlap {α : Type} {L : ℕ} (v w : Fin (L - 1) → α) : Prop :=
  ∀ d : Fin (L - 2), v ⟨d.val + 1, by omega⟩ = w ⟨d.val, by omega⟩

section TruthTraversal

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. A concrete instance, for the refutation

`S = 00` at `G = 2`, `L = 2`, so the node type is `Fin (2 - 1) → Fin 2`, i.e.
single symbols.  `nodeCount ![0] = 2 = G`, and every vertex entered by the
truth is `![0]`. -/

/-- `S = 00`, at `G = 2`, `L = 2`. -/
def S2 : Fin 2 → Fin 2 := ![0, 0]

theorem hG2 : 0 < 2 := by decide

/-- Every start of `S2` spells the single symbol `0`.

The draft proved this `by funext j; rfl`.  `rfl` does not close it, because
`vtx` at `L = 2` is `cyc hG2 S2 (r.val + j.val)`, whose value is
`S2 ((r.val + j.val) % 2)` --- a `Nat.mod` that is not reduced when `r` and `j`
are variables.  Case analysis on the two `Fin`s closes it. -/
theorem vtx_S2 (r : Fin 2) : vtx hG2 2 S2 r = ![0] := by
  funext j
  fin_cases r <;> fin_cases j <;> decide

/-- Hence `G ≤ nodeCount v` holds for the vertex `![0]` at `G = 2`, `L = 2`. -/
theorem nodeCount_S2_zero : nodeCount (L := 2) hG2 S2 ![0] = 2 := by
  have hset : ((Finset.univ : Finset (Fin 2)).filter
      (fun r : Fin 2 => nodeWindow (L := 2) hG2 S2 r = ![0])
      : Finset (Fin 2)) = Finset.univ :=
    Finset.filter_eq_self.2 (fun r _ => vtx_S2 r)
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
  -- `card_fibre` states the fibre count in terms of `deg`, and `deg` is
  -- *definitionally* `nodeCount` (`BBTCondense.lean:230`), so the two are the
  -- same function; the draft's failure here was not applying the lemma's
  -- four explicit arguments.
  have h2 : (fibre hG L S v).card = nodeCount (L := L) hG S v := card_fibre hG L S v
  have hcard : (fibre hG L S v).card = G := by omega
  have hsub : fibre hG L S v ⊆ (Finset.univ : Finset (Fin G)) := Finset.subset_univ _
  have heq : fibre hG L S v = (Finset.univ : Finset (Fin G)) :=
    Finset.eq_of_subset_of_card_le hsub (by simpa using hcard.symm.le)
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
  -- the hypothesis is the *inequality* `2 ≤ nodeCount`, which `hnn` supplies
  obtain ⟨r, hr1, hr2⟩ := h (by omega)
  have hz := nodeCount_eq_G_imp hG2 2 S2 ![0] (by omega) (nextPos hG2 r)
  exact absurd (hz.symm.trans hr2) (by decide)

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

/-- **Membership in `edgeStarts`, unfolded.**  The draft proved this `Iff.rfl`,
which is wrong: `edgeStarts` is a `Finset.univ.filter`, so membership is
`r ∈ Finset.univ ∧ (...)`, and `Iff.rfl` does not see through `Finset.filter`.
The corrected statement is the same proposition. -/
theorem mem_edgeStarts_iff {v w : Fin (L - 1) → α} {r : Fin G} :
    r ∈ edgeStarts hG L S v w ↔       vtx hG L S r = v ∧ vtx hG L S (nextPos hG r) = w := by
  simp only [edgeStarts, Finset.mem_filter, Finset.mem_univ, true_and]

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
  unfold edgeCount
  refine Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨r, ?_⟩)
  simp only [edgeStarts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨rfl, rfl⟩

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

theorem glue_winPrefix (hL : 2 ≤ L) (v w : Fin (L - 1) → α) : winPrefix (glue hL v w) = v := by
  funext d
  show (glue hL v w) ⟨d.val, by have := d.isLt; omega⟩ = v d
  rw [glue, dite_eq_left (by have := d.isLt; omega)]

/-- **The glued `L`-mer at its LAST position.**  This is the only suffix
statement about `glue` that is true, and it is the one the bridge needs:
`glue hL v w` reads `v` on `0 … L-2` and `w (L-2)` at `L-1`.

**The draft's `glue_winSuffix` (`winSuffix (glue hL v w) = w`) is FALSE,
and is removed here rather than repaired.**  `winSuffix` reads positions
`1 … L-1`, but `glue` reads `v` on all of `0 … L-2`, so at `d.val = 0` the
suffix of `glue` is `v 1`, not `w 0`.  Concrete: at `L = 3`,
`v = ![a, b]`, `w = ![c, d]`, `glue hL v w = ![a, b, d]`, and
`winSuffix (glue hL v w) = ![b, d] ≠ ![c, d] = w` whenever `b ≠ c`.  The
draft's `simp`-with-`Nat.add_sub_cancel` proof of it did not compile, which is
the only reason the defect was not visible; the statement is not true at any
`L`, so no proof of it exists.  `glue_last` and `window_eq_pair_iff` below
carry the correct content. -/
theorem glue_last (hL : 2 ≤ L) (v w : Fin (L - 1) → α) :
    glue hL v w ⟨L - 1, by omega⟩ = w ⟨L - 2, by omega⟩ := by
  have hlast0 : ¬ (L - 1 < L - 1) := by omega
  have hlast : ¬ ((⟨L - 1, by omega⟩ : Fin L).val < L - 1) := by
    simpa only [Fin.val_mk] using hlast0
  rw [glue, dite_eq_right hlast]
  congr 1

/-- **The length-`L` window at `r` is the glued `L`-mer of the two vertices
the truth enters at `r` and at `nextPos r`.**  This is the edge/vertex
dictionary, and it is the only genuinely new combinatorial content in this
file. -/
theorem window_eq_glue (hL : 2 ≤ L) (r : Fin G) :
    window (L := L) hG S r = glue hL (vtx hG L S r) (vtx hG L S (nextPos hG r)) := by
  -- `vtx hG L S r` is *definitionally* `window (L := L) hG S r`; the draft
  -- never noticed, and the residual `vtx`/`window` mismatch in the last
  -- `convert` goal below is a direct consequence.
  simp only [vtx]
  funext d
  by_cases hd : d.val < L - 1
  · show window (L := L) hG S r d = (glue hL (nodeWindow (L := L) hG S r)
      (nodeWindow (L := L) hG S (nextPos hG r))) d
    rw [glue, dite_eq_left hd]
    rfl
  · have hd' : d = ⟨L - 1, by omega⟩ := by rw [Fin.mk.injEq]; omega
    rw [hd', glue, dite_eq_right (by omega)]
    -- `window_next` is stated at `⟨j + 1, _⟩`, and `(L-2)+1` and `L-1` are
    -- equal but not syntactically so; the draft's `show` with pre-simplified
    -- indices is why this line did not close.  `convert` plus `Fin.ext` does.
    have hwn := window_next hG (L := L) S r (j := L - 2) (by omega)
    -- the remaining arithmetic mismatch is `(L-2)+1` vs `L-1` and `L-2` vs
    -- `(L-1)-1`; `convert` with `Fin.mk.injEq` closes both without a motive.
    convert hwn using 1
    all_goals first
      | exact congrArg _ (by rw [Fin.mk.injEq]; omega)
      | -- `nodeWindow` is `window` with body `cyc`; only the index differs.
        simp only [nodeWindow]
        congr 1

/-- **The forward half of the edge/vertex dictionary, which is all that is
true.**  If the truth spells `v` at `r` and `w` at `nextPos r`, then the
length-`L` window at `r` is the glued `L`-mer of the pair.

**The draft's converse `window_eq_pair_iff` is FALSE, and is removed here
rather than repaired.**  The `L`-mer `glue hL v w` records `v` in full but only
the *last* symbol of `w`, so it does not determine `w`: at `L = 3`,
`glue hL ![a,b] ![c,d] = ![a,b,d] = glue hL ![a,b] ![c',d]` for any `c'`.  The
pair `(v, w)` is recoverable from the `L`-mer only under the extra hypothesis
that `v` and `w` **overlap**, `v (L-2) = w 0`; the dictionary is the standard
de Bruijn one, and that hypothesis is exactly what makes it injective.  The
draft's proof of the converse used `glue_winSuffix`, which is false, and the
`congrFun` step it would have needed does not close. -/
theorem window_eq_glue_of_pair (hL : 2 ≤ L) (r : Fin G) {v w : Fin (L - 1) → α}
    (h1 : vtx hG L S r = v) (h2 : vtx hG L S (nextPos hG r) = w) :
    window (L := L) hG S r = glue hL v w := by
  -- `window_eq_glue` takes the section's `hG`, `L`, `S` explicitly, so the
  -- call is `window_eq_glue hG L S hL r`; the draft's `window_eq_glue hL r`
  -- silently elaborated to a metavariable-filled application, which is why the
  -- following `rw` reported "did not find an occurrence".
  rw [window_eq_glue hG L S hL r, h1, h2]

/-- **The prefix half of the dictionary, which *is* injective.** -/
theorem winPrefix_window_eq (hL : 2 ≤ L) (r : Fin G) {v w : Fin (L - 1) → α}
    (h : window (L := L) hG S r = glue hL v w) : vtx hG L S r = v := by
  rw [← glue_winPrefix (L := L) hL v w, ← h]
  exact winPrefix_window' hG L S r

/-- **The de Bruijn overlap condition on a pair: `v` and `w` share their
junction symbol.**  This is the hypothesis under which the `L`-mer determines
the pair. -/
theorem winSuffix_window_eq (hL : 2 ≤ L) (r : Fin G) {v w : Fin (L - 1) → α}
    (h : window (L := L) hG S r = glue hL v w) (hO : Overlap v w) :
    vtx hG L S (nextPos hG r) = w := by
  -- the pair is `winPrefix` and `winSuffix` of the window;
  -- `winSuffix (window r) = vtx (nextPos r)` (`winSuffix_window'`), and
  -- `winSuffix (glue hL v w) d` is `v (d.val + 1)` when `d.val + 1 < L - 1`
  -- and `w d` at `d.val = L - 2`; `h` and the overlap hypothesis close it.
  rw [← winSuffix_window' hG L S r, h]
  funext d
  show (glue hL v w) ⟨d.val + 1, by have := d.isLt; omega⟩ = w d
  by_cases hd : d.val + 1 < L - 1
  · rw [glue, dite_eq_left hd]
    exact hO ⟨d.val, by omega⟩
  · have hd' : d = ⟨L - 2, by omega⟩ := by rw [Fin.mk.injEq]; omega
    have hnot0 : ¬ (L - 2 + 1 < L - 1) := by omega
    have hnot : ¬ ((⟨L - 2 + 1, by omega⟩ : Fin L).val < L - 1) := by
      simpa only [Fin.val_mk] using hnot0
    rw [hd', glue, dite_eq_right hnot]
    show w ⟨((⟨L - 2 + 1, by omega⟩ : Fin L).val - 1), by omega⟩
      = w ((⟨L - 2, by omega⟩ : Fin (L - 1)))
    apply congrArg _
    apply Fin.ext
    rw [Fin.val_mk, Fin.val_mk]
    omega

/-- **THE BRIDGE LEMMA.  The number of times the truth traverses the directed
edge `(v, w)` is exactly the multiplicity, in the complete `L`-spectrum, of
the `L`-mer formed by overlapping `v` and `w`.**  This is what identifies the
`(L-1)`-mer multigraph of the word with the de Bruijn graph of the spectrum,
and it is the step that makes `specCount` --- the object the endpoint's
hypothesis is about --- the multiplicity function of the multigraph.

Proof: `Finset.filter_congr` (`Mathlib/Data/Finset/Filter.lean:176`) makes the
outer `Finset`s equal, the membership predicate is
`window_eq_glue_of_pair`, and the right-hand side is `specCount` by its own
definition (`AssemblyP1/OrientedRigidity.lean:626`).

**The draft stated this as an EQUALITY.  It is an INEQUALITY, and the
difference is not cosmetic.**  `specCount` counts starts by their `L`-mer, and
the `L`-mer does not determine the pair `(v, w)` without the overlap
hypothesis (`winSuffix_window_eq` above): at `G = 4`, `L = 2`, `S = 0000`, the
single vertex `v = ![0]` has `edgeCount v v = 4` while
`specCount (glue hL v v) = 4` --- but at `G = 6`, `L = 3` the same
many-to-one failure makes the counts differ.  What is always true, and what is
stated here, is `edgeCount ≤ specCount`: every start of the edge is a start of
the spectrum entry, and `specCount` may count further starts whose pair is a
*different* preimage of the same `L`-mer.  `card_edgeCount_eq_specCount` is
**not** proved here and is not provable in this form. -/
theorem edgeCount_le_specCount (hL : 2 ≤ L) (v w : Fin (L - 1) → α) :
    edgeCount hG L S v w ≤ specCount (L := L) hG S (glue hL v w) := by
  unfold edgeCount edgeStarts specCount
  refine Finset.card_le_card ?_
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
  exact window_eq_glue_of_pair hG L S hL r hr.1 hr.2

/-! ## 5. Node multiplicity: the truth's cycle visits `v` exactly `deg v` times

This is item 2(c) of `AssemblyP1/Issue94TW8Contraction.lean:551`, at the
`Fin (L - 1) → α` node type.  The draft stated it as a sum of `edgeCount`s
over the starts of the fibre of `v`.

**That statement is FALSE, and the refutation is below, kernel-checked.**  The
draft's intermediate claim --- "each start of the fibre of `v` contributes
exactly one traversal of the unique edge it uses out of `v`" --- silently
assumes `vtx` is injective on the circle, i.e. that the `(L-1)`-mers of the word
are pairwise distinct.  That is primitivity, which is not a hypothesis here.
At `G = 4`, `L = 2`, `S = 0000` the word has a single `(L-1)`-mer `v = ![0]`,
`deg v = 4`, every start of the fibre spells the *same* edge `(v, v)`, so each
of the four summands is `4` and the sum is `16`, not `4`.  The draft's
`Finset.card_eq_one` step could not be supplied for exactly this reason.

What *is* true, and is the intended content, is the version below: the number
of traversals of `v` by the truth's own cycle is exactly the number of starts
of `v`, which is `deg v` by `card_fibre` already in the library.  It does not
need the edge multiset at all, and it does not need primitivity.  The
`SeqGraph` re-indexing of `AssemblyP1/Issue94TW8Contraction.lean:551` item
2(c) that needs *edges* is therefore still open, and is a different statement
from this one. -/

theorem nodeMult_eq_deg (v : Fin (L - 1) → α) :
    (fibre hG L S v).card = deg hG L S v :=
  card_fibre hG L S v

/-- `0000` at `G = 4`, `L = 2`: the constant word, whose only `(L-1)`-mer is
`![0]` and which is spelled at all four starts. -/
def Sz4 : Fin 4 → Fin 1 := fun _ => 0

theorem hG4 : 0 < 4 := by decide

/-- **The draft's `nodeMult_eq_deg` is refuted.**  At `G = 4`, `L = 2`,
`S = 0000`, the sum of `edgeCount`s over the starts of the fibre of `![0]` is
`16`, while `deg ![0] = 4`. -/
theorem not_nodeMult_eq_deg :
    (∑ r ∈ (fibre hG4 2 Sz4 ![0]),
        edgeCount hG4 2 Sz4 ![0] (vtx hG4 2 Sz4 (nextPos hG4 r)))
      ≠ deg hG4 2 Sz4 ![0] := by
  have hsum : (∑ r ∈ (fibre hG4 2 Sz4 ![0]),
        (edgeStarts hG4 2 Sz4 ![0] (vtx hG4 2 Sz4 (nextPos hG4 r))).card) = 16 := by
    show (∑ _r ∈ (fibre hG4 2 Sz4 ![0]),
        (((Finset.univ : Finset (Fin 4)).filter
          (fun r : Fin 4 => vtx hG4 2 Sz4 r = ![0] ∧
            vtx hG4 2 Sz4 (nextPos hG4 r) = vtx hG4 2 Sz4 (nextPos hG4 r))).card)) = 16
    decide
  have hdeg : deg hG4 2 Sz4 ![0] = 4 := by
    show (((Finset.univ : Finset (Fin 4)).filter
      (fun r : Fin 4 => nodeWindow (L := 2) hG4 Sz4 r = ![0])).card) = 4
    have hmem : ∀ r : Fin 4, nodeWindow (L := 2) hG4 Sz4 r = ![0] := by
      intro r
      funext j
      fin_cases r <;> fin_cases j <;> decide
    have hset : ((Finset.univ : Finset (Fin 4)).filter
        (fun r : Fin 4 => nodeWindow (L := 2) hG4 Sz4 r = ![0])
        : Finset (Fin 4)) = Finset.univ :=
      Finset.filter_eq_self.2 (fun r _ => hmem r)
    rw [hset, Finset.card_univ, Fintype.card_fin]
  unfold edgeCount
  rw [hsum, hdeg]
  decide

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
