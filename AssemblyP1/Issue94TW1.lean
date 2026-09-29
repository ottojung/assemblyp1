import AssemblyP1.BBTCondense

/-!
# Board 94, front 94e7: the `t_w = 1` obligation is **REFUTED**

**Headline result of this module, kernel-checked:**

> `Ukkonen` at read length `L`, together with rotation-primitivity, does **not**
> give a unique spanning in-arborescence of the `(L-1)`-mer multigraph `D`.
> The board's own `t_w = 1` step --- the second half of its own
> BEST-theorem decomposition, the half this front was asked to advance --- is
> **false as stated**, on a primitive binary word of length `5` at read
> length `3`.

The instance is `S = 10100` on the circle of `5` positions, read at `L = 3`.
`Ukkonen h5 3 S10100` holds (`S10100_ukkonen`) and
`RepeatAdapter.IsPrimitive h5 S10100` holds (`S10100_primitive`), yet the
multigraph `D` of `S` at `L = 3` carries **two distinct spanning
in-arborescences rooted at the start-`0` vertex**: `S10100_arb1` and
`S10100_arb2`.  Hence `S10100_two_arbs` and `not_UniqueInArb_3`.

## What this does and does not refute

**It refutes** `UniqueInArb L` as defined in §3 below: the claim that
`Ukkonen` plus primitivity makes the in-arborescence of `D` rooted at each
vertex unique.  That is precisely the "`t_w = 1`" step of the board's own
conditional BEST-theorem reduction.

**It does not refute `thm:BBT`**, and that distinction is the point of this
module.  `t_w > 1` and "more than one *edge-type* Eulerian circuit" are
different statements.  At `S = 10100`, `L = 3` the two in-arborescences differ
**only** in which of the two parallel `01 -> 10` edges they use, and the two
resulting labelled Eulerian circuits are the **same edge-type word**.
`docs/exact-same-length-spectrum-fibre-count.md` works throughout with edge
*types*, copies of one type being indistinguishable, and BBT's Theorem 3 is a
statement about the **condensed** sequence graph, which is the same coarser
object.  The parallel-edge labelling is exactly the over-count that the
`prod_e c_h(e)!` denominators of that note remove.  So the refutation kills
the *stated* form of the split; it does not kill the theorem the split was
aiming at, and it is **not** evidence against `Ukkonen` uniqueness.

## What survives, and is the next obligation

The count that must be `1` is the number of *edge-type* circuit orbits, and a
correct reduction must divide out the parallel-edge labellings rather than
demand `t_w = 1`.  That corrected obligation is **not** stated as proved here
and is not proved here; §5 records it.

## Attribution (board 94, front 94e7; `docs/best-tw1-attribution-94.md`)

The `t_w = 1` split, the conditional BEST-theorem reduction behind it, and the
identification of out-degree as the critical parameter are **the board's own
constructions**.  They are **not** results imported from Pevzner 1995
(Algorithmica 13:77--105) or from Bresler--Bresler--Tse (Algorithmica
13:1--19, 2006): the first contains no counting statement of any kind, and the
second contains no arborescence and no proof of its own Theorem 3, its
Theorem 3 importing the step from the first, so the citation chain is broken
and terminates in nothing.  The BEST theorem is cited from van
Aardenne-Ehrenfest and de Bruijn, *Indag. Math.* (1951), or Tutte, LMS Lect.
Notes 83 (1975).  This module uses **no counting input at all**: it exhibits
two spanning in-arborescences by hand, so no BEST theorem, no Matrix-Tree
determinant and no arborescence-counting theory is invoked.

## Computational provenance, and its limits

The bounded search behind this module is `scripts/verify_tw1_94.js`.  Over
every binary circular word of length `K <= 12` that is primitive and satisfies
`Ukkonen` at some `2 <= L <= K` --- 52210 `(S, L)` instances, of which the
edge-type circuit count was computed for all `K <= 9` (4312 instances) --- it
reported:

* `t_w != 1` in **5704** instances, with `t_w` as large as `16`;
* **zero** instances with more than one edge-type circuit orbit, i.e. zero
  candidates for a refutation of `Ukkonen` uniqueness itself.

That search is **evidence, not proof**: its completeness over those ranges is
not proved, and nothing is claimed here for `K > 12`.  This module proves only
the single kernel-checked refutation above; the search is cited as motivation
and as a record of what was looked for, and for nothing more.

Three independent checks are built into the evaluator, and two earlier versions
of it were **wrong** and were caught by them: a fraction-free Bareiss variant
missing the division by the previous pivot, and a cross-multiplied fraction
variant dividing by zero.  Both produced root-dependent `t_w` values, which is
impossible for an Eulerian `D`; both were fixed before any output above was
read.  The evaluator now computes `t_w` by the directed Matrix-Tree theorem,
cross-checks it against a brute-force enumeration of in-arborescences, checks
that `t_w` agrees across roots, and checks the BEST product against a
**direct** enumeration of Eulerian circuits using neither BEST nor any
determinant.

## Why no new model is introduced

Everything is phrased on the repository's own objects: `vtx` (the `(L-1)`-mer
at a start) and `nextPos` (one-step rotation) are the vertices and edges of
`D`, and a "set of edges" is a `Finset (Fin K)` of starts.  The shape is forced
by a real obstruction recorded in `BBTCondense.lean`'s module docstring: the
vertex type `Fin (L-1) -> α` is not a `Fintype` for arbitrary `α`, so a
multigraph object with a `Fintype` vertex type --- and hence a Matrix-Tree
determinant --- is not available without new infrastructure.  Phrasing
`t_w = 1` as *uniqueness of the in-arborescence expressed as a subset of edge
positions* sidesteps that, keeps the statement faithful, and --- since the
refutation needs only **two** in-arborescences --- needs no counting machinery
at all.

## What is NOT established here

Stated plainly, so nothing above is over-read.  This module does **not**
prove, and does not claim:

1. that `Ukkonen` uniqueness (BBT's Theorem 3) is true --- it is neither proved
   nor refuted here, and the search found no refutation candidate;
2. that `t_w > 1` *always* arises from parallel edges.  **CORRECTION (board
   94, front 94a10; see `docs/edge-type-obligation-94.md`):** this module's
   original item 2 said the search found 208 instances at `K <= 9` with a
   **simple** `D` and `t_w > 1`, so that sufficient condition is false.  **That
   count was wrong.**  `scripts/verify_tw1_94.js`'s `hasParallelEdges` iterated
   its outer loop over the edge *array* and its inner loop over
   `edges[u].length`, so it was **identically `false`** and every instance was
   classified simple (548 + 208 = 756 = all of them).  With the predicate
   corrected there are **zero** simple-`D`, `t_w > 1` instances at `K <= 12`
   (5142 instances have `t_w > 1`, all with a parallel edge).  So this module
   neither proves that sufficient condition nor refutes it; the corrected
   obligation of §5 needs no new idea beyond the parallel-edge division.  That
   is **evidence**, not proof;
3. anything about `K > 12`, or about alphabets larger than binary;
4. the corrected edge-type obligation of §5.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no `unsafe`, no
linter suppression.  `autoImplicit` is off.
-/

namespace AssemblyP1.Issue94TW1

open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.P2
open AssemblyP1.PopulationReduction
open AssemblyP1.RepeatAdapter
open SourceFaithfulIs
open Finset

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α]
variable {K L : ℕ}

/-! ## 1. `D` in the repository's own coordinates

The multigraph `D(S, L)` of the `(L-1)`-mer spectrum: **vertices** are the
distinct `(L-1)`-mers, **edges** are indexed by the starts `r`, the edge `r`
running from `vtx r` to `vtx (nextPos r)`.  The out-degree of a vertex is the
number of its occurrences, i.e. `BBTCondense.deg`.  So a "set of edges" is a
`Finset (Fin K)` of starts, and a *choice of one out-edge at a vertex* is a
single start `r` with `vtx r` that vertex. -/

/-- The set of edges of `D` leaving the vertex carried by the start `r`: those
starts `r'` in `T` whose `(L-1)`-mer is the one read at `r`.  With `T = univ`
this is the whole out-edge set of that vertex. -/
def OutEdges (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (T : Finset (Fin K)) (r : Fin K) : Finset (Fin K) :=
  T.filter fun r' => vtx hK L S r' = vtx hK L S r

/-- **One out-edge at every non-root vertex.**  Every vertex other than the
root's has exactly one out-edge in `T`.  Quantified over *starts* `r` rather
than over vertices, which is sound because the vertices of `D` are exactly the
`(L-1)`-mers that occur, i.e. exactly the `vtx r`. -/
def OneOutEdge (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (w : Fin K) (T : Finset (Fin K)) : Prop :=
  ∀ r : Fin K, vtx hK L S r ≠ vtx hK L S w → (OutEdges hK L S T r).card = 1

/-- One step of `D` restricted to the edge set `T`, from the vertex `u` to the
vertex `v`: there is an edge of `T` leaving `u` and landing on `v`.  Parallel
edges are **not** distinguished, which is the edge-type convention of
`docs/exact-same-length-spectrum-fibre-count.md`.

The `u = v` disjunct is a notational convenience only.  A vertex of `D` is
carried by several starts, so a statement "every vertex reaches the root" has
to be phrased with one start per vertex, and without the disjunct two starts of
one vertex would be distinct *terms* that `ReflTransGen.refl` cannot identify.
Adding `u = v` lets the proof change representative freely.  It does not
change which vertices are reachable, because `u = v` only ever adds a
zero-length move from a vertex to itself. -/
def VStep (hK : 0 < K) (L : ℕ) (S : Fin K → α) (T : Finset (Fin K))
    (u v : Fin (L - 1) → α) : Prop :=
  u = v ∨ ∃ r' ∈ T, vtx hK L S r' = u ∧ vtx hK L S (nextPos hK r') = v

instance instVStep (hK : 0 < K) (L : ℕ) (S : Fin K → α) (T : Finset (Fin K))
    (u v : Fin (L - 1) → α) : Decidable (VStep hK L S T u v) := by
  unfold VStep; infer_instance

/-- **`T` is a spanning in-arborescence of `D` rooted at `w`:** one out-edge at
every non-root vertex, and every vertex reaches the root's vertex along `T`.

This is the object whose number is `t_w` at a vertex `w` of `D`.  It is stated
directly rather than via a determinant, because the module docstring explains
why that is both faithful and sufficient for this front. -/
def InArb (hK : 0 < K) (L : ℕ) (S : Fin K → α)
    (w : Fin K) (T : Finset (Fin K)) : Prop :=
  OneOutEdge hK L S w T ∧
    ∀ r : Fin K,
      Relation.ReflTransGen (VStep hK L S T) (vtx hK L S r) (vtx hK L S w)

/-! ## 2. The instance: `S = 10100` on `K = 5`, read at `L = 3`

The `(L-1)`-mers read at the five starts, with `L = 3` so `L - 1 = 2`:

| start `r` | 0    | 1    | 2    | 3    | 4    |
| --- | --- | --- | --- | --- | --- |
| `vtx r` | `10` | `01` | `10` | `00` | `01` |

So `D` has three vertices `10`, `01`, `00` and five edges

```text
r = 0 :  10 -> 01
r = 1 :  01 -> 10
r = 2 :  10 -> 00
r = 3 :  00 -> 01
r = 4 :  01 -> 10          <-- parallel to r = 1
```

The root is the start-`0` vertex, `10`.  Two spanning in-arborescences:

* `T₁ = {0, 1, 3}`: at `01` take edge `1`, at `00` take edge `3`.  So
  `00 -> 01 -> 10` and `01 -> 10`.
* `T₂ = {0, 3, 4}`: at `01` take edge `4`, at `00` take edge `3`.  So
  `00 -> 01 -> 10` and `01 -> 10`.

They differ in exactly one edge, and that edge is one of the two parallel
`01 -> 10` edges.  Both are in-arborescences; hence `t_w ≥ 2` at `w = 0`. -/

/-- `0 < 5`, the circle length of the instance. -/
theorem h5 : 0 < 5 := by omega

/-- The counterexample word `S = 1, 0, 1, 0, 0` on the circle of `5`
positions.  It is primitive, and it satisfies `Ukkonen` at `L = 3`. -/
def S10100 : Fin 5 → Bin
  | ⟨0, _⟩ => Bin.B | ⟨1, _⟩ => Bin.A | ⟨2, _⟩ => Bin.B
  | ⟨3, _⟩ => Bin.A | ⟨_, _⟩ => Bin.A

/-- The instance is **rotation-primitive**: no shift in `1, 2, 3, 4` preserves
`S10100`. -/
theorem S10100_primitive : RepeatAdapter.IsPrimitive h5 S10100 := by
  intro s hs hlt hsi
  interval_cases s
  · exact absurd (hsi 0) (by decide)
  · exact absurd (hsi 2) (by decide)
  · exact absurd (hsi 0) (by decide)
  · exact absurd (hsi 0) (by decide)

/-- **The load-bearing hypothesis: `S10100` satisfies `Ukkonen` at `L = 3`.**
Without it the instance would show only that *some* word has two
in-arborescences, which nobody claims.  Proved by `decide` against the
library's own `Ukkonen`, whose clauses use the library's own `IsTripleRepeat`
and `IsRepeat`, maximality clauses included.

At the threshold `L - 1 = 2` the only maximal repeat pair of length at least
`2` is `{1, 4}` at length `3`, and it does **not** interleave with anything:
the interleaving clause needs four pairwise distinct starts, and the only
other maximal repeat pair is `{3, 4}` at length `1 < 2`, so the
`Or.inr` disjunct is discharged.  Every maximal triple repeat is at length
`1 < 2`.  So `Ukkonen` holds while `D` has out-degree `2` at the vertex `01`
and two in-arborescences: **`Ukkonen`'s clauses do not see this
configuration.** -/
theorem S10100_ukkonen : Ukkonen h5 3 S10100 := by
  unfold Ukkonen mkGenome
  decide

/-- `T₁ = {0, 1, 3}`: at the vertex `01` take edge `1`, at `00` take edge
`3`. -/
def T1 : Finset (Fin 5) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩}

/-- `T₂ = {0, 3, 4}`: at the vertex `01` take edge `4`, at `00` take edge
`3`.  `T₂` differs from `T₁` in exactly the choice between the two parallel
`01 -> 10` edges. -/
def T2 : Finset (Fin 5) := {⟨0, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩}

theorem T1_ne_T2 : T1 ≠ T2 := by
  have h1not : (⟨1, by omega⟩ : Fin 5) ∉ T2 := by decide
  intro h
  rw [← h] at h1not
  exact h1not (by simp [T1])

/-! ## 3. The two in-arborescences, and the refutation -/

/-- **The three vertices of `D` at this instance, read off the starts.** -/
theorem vtx0_10100 : vtx h5 3 S10100 (⟨0, by omega⟩ : Fin 5) = ![Bin.B, Bin.A] := by decide
theorem vtx1_10100 : vtx h5 3 S10100 (⟨1, by omega⟩ : Fin 5) = ![Bin.A, Bin.B] := by decide
theorem vtx2_10100 : vtx h5 3 S10100 (⟨2, by omega⟩ : Fin 5) = ![Bin.B, Bin.A] := by decide
theorem vtx3_10100 : vtx h5 3 S10100 (⟨3, by omega⟩ : Fin 5) = ![Bin.A, Bin.A] := by decide
theorem vtx4_10100 : vtx h5 3 S10100 (⟨4, by omega⟩ : Fin 5) = ![Bin.A, Bin.B] := by decide

/-- Starts `0` and `2` carry the same vertex: the vertex `10`. -/
theorem vtx0_eq_vtx2 :
    vtx h5 3 S10100 (⟨0, by omega⟩ : Fin 5) = vtx h5 3 S10100 (⟨2, by omega⟩ : Fin 5) := by decide

/-- Starts `1` and `4` carry the same vertex: the vertex `01`. -/
theorem vtx1_eq_vtx4 :
    vtx h5 3 S10100 (⟨1, by omega⟩ : Fin 5) = vtx h5 3 S10100 (⟨4, by omega⟩ : Fin 5) := by decide

/-- **`T₁` is a spanning in-arborescence of `D` rooted at the start-`0`
vertex.**  The one-out-edge half is a finite computation over the five starts;
the reachability half is the explicit chain `00 -> 01 -> 10` together with
`01 -> 10`, with the root itself needing only reflexivity. -/
theorem S10100_arb1 :
    InArb h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T1 := by
  have hone : OneOutEdge h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T1 := by
    intro r hr
    fin_cases r <;>
      first
        | exact absurd hr (by decide)
        | decide
  have hstep1 : VStep h5 3 S10100 T1 (vtx h5 3 S10100 ⟨1, by omega⟩)
      (vtx h5 3 S10100 ⟨0, by omega⟩) := Or.inr ⟨⟨1, by omega⟩, by decide, by decide⟩
  have hstep3 : VStep h5 3 S10100 T1 (vtx h5 3 S10100 ⟨3, by omega⟩)
      (vtx h5 3 S10100 ⟨1, by omega⟩) := Or.inr ⟨⟨3, by omega⟩, by decide, by decide⟩
  have hstep1' : VStep h5 3 S10100 T1 (vtx h5 3 S10100 ⟨4, by omega⟩)
      (vtx h5 3 S10100 ⟨0, by omega⟩) := Or.inr ⟨⟨1, by omega⟩, by decide, by decide⟩
  refine ⟨hone, ?_⟩
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep1
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Or.inl vtx0_eq_vtx2.symm)
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep3) hstep1
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep1'

/-- **`T₂` is a spanning in-arborescence of the same `D`, same root.**  The
chain is the same `00 -> 01 -> 10`; only the `01 -> 10` edge is `4` instead of
`1`. -/
theorem S10100_arb2 :
    InArb h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T2 := by
  have hone : OneOutEdge h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T2 := by
    intro r hr
    fin_cases r <;>
      first
        | exact absurd hr (by decide)
        | decide
  have hstep4 : VStep h5 3 S10100 T2 (vtx h5 3 S10100 ⟨1, by omega⟩)
      (vtx h5 3 S10100 ⟨0, by omega⟩) := Or.inr ⟨⟨4, by omega⟩, by decide, by decide⟩
  have hstep3 : VStep h5 3 S10100 T2 (vtx h5 3 S10100 ⟨3, by omega⟩)
      (vtx h5 3 S10100 ⟨1, by omega⟩) := Or.inr ⟨⟨3, by omega⟩, by decide, by decide⟩
  have hstep4' : VStep h5 3 S10100 T2 (vtx h5 3 S10100 ⟨4, by omega⟩)
      (vtx h5 3 S10100 ⟨0, by omega⟩) := Or.inr ⟨⟨4, by omega⟩, by decide, by decide⟩
  refine ⟨hone, ?_⟩
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep4
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl (Or.inl vtx0_eq_vtx2.symm)
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep3) hstep4
  · exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hstep4'

/-- **The refutation in the form the board needs it:** `D` has **two
distinct** spanning in-arborescences rooted at the start-`0` vertex of a
**primitive** word satisfying **`Ukkonen` at `L = 3`**.  Hence `t_w ≥ 2` there,
so `t_w = 1` does not follow from `Ukkonen`. -/
theorem S10100_two_arbs :
    InArb h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T1 ∧
      InArb h5 3 S10100 (⟨0, by omega⟩ : Fin 5) T2 ∧ T1 ≠ T2 :=
  ⟨S10100_arb1, S10100_arb2, T1_ne_T2⟩

/-- **The board's `t_w = 1` obligation, as a `Prop`.**  For every circle, every
word satisfying `Ukkonen` at `L`, and every vertex `w` of `D`, the spanning
in-arborescence of `D` rooted at `w` is unique.  Uniqueness of the
in-arborescence *is* the statement `t_w = 1`.

This is a **board construction**, not a source claim; see the module docstring
and `docs/best-tw1-attribution-94.md`. -/
def UniqueInArb (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → Bin), Ukkonen hK L S →
    RepeatAdapter.IsPrimitive hK S →
    ∀ w : Fin K, ∃! T : Finset (Fin K), InArb hK L S w T

/-- **The `t_w = 1` obligation is refuted at `L = 3`, on a primitive `Ukkonen`
word of length `5`.**  This is the front's public result. -/
theorem not_UniqueInArb_3 : ¬ UniqueInArb 3 := by
  intro h
  obtain ⟨T, hT, huniq⟩ :=
    h 5 h5 S10100 S10100_ukkonen S10100_primitive ⟨0, by omega⟩
  have h1 : T1 = T := huniq T1 S10100_arb1
  have h2 : T2 = T := huniq T2 S10100_arb2
  exact T1_ne_T2 ((h2.trans h1.symm).symm)

/-! ## 4. Why this is not a refutation of `Ukkonen` uniqueness, in the kernel

The two in-arborescences of §3 differ only in which of the two parallel
`01 -> 10` edges is used.  That is recorded here as a theorem rather than left
as prose, because it is the whole reason the refutation does not bite.

* `T₁` contains the start `1` and `T₂` does not, and those are exactly the
  two starts carrying the vertex `01` whose successor vertex is `10`;
* every other member of `T₁` and `T₂` is shared. -/

/-- The two in-arborescences differ in exactly one edge, and that edge is one
of the two parallel `01 -> 10` edges: the starts `1` and `4` both carry the
vertex `01` and both have successor vertex `10`. -/
theorem T1_T2_differ_only_in_parallel_edge :
    ((⟨1, by omega⟩ : Fin 5) ∈ T1 ∧ (⟨1, by omega⟩ : Fin 5) ∉ T2) ∧
    vtx h5 3 S10100 (⟨1, by omega⟩ : Fin 5) = vtx h5 3 S10100 ⟨4, by omega⟩ ∧
    vtx h5 3 S10100 (nextPos h5 ⟨1, by omega⟩)
      = vtx h5 3 S10100 (nextPos h5 ⟨4, by omega⟩) := by
  refine ⟨⟨by decide, by decide⟩, by decide, by decide⟩

end AssemblyP1.Issue94TW1
