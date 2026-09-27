import AssemblyP1.BBTEulerian

/-!
# A kernel-checked exhaustive verification of the exact #89 statement on a
# finite class (issue #89)

`AssemblyP1/BBTEulerian.lean` isolates the one open mathematical input of the
exported population theorems:

```text
EulerianCycleObstruction L :=
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
      ∀ σ : Fin K ≃ Fin K, EulerianCycle hK L S σ →
        VertexCycleEq hK L S σ id ∨ LongObstruction hK L S
```

i.e. the contrapositive of Theorem 3 of Bresler--Bresler--Tse 2013 (*Optimal
assembly for high throughput shotgun sequencing*): a circular genome
satisfying Ukkonen's condition at `K = L - 1` has a unique Eulerian cycle in
its condensed `K`-mer graph, in the sense that every alternative Eulerian
cycle spells the same cyclic sequence of `K`-mers.

This module does **not** prove that statement.  What it does is check it,
by the kernel, on a finite but non-trivial class: **every binary circular
genome of length at most `maxG`, at every read length `2 ≤ L ≤ maxL`**.  The
check is exhaustive in the three quantifiers of the theorem (genome length,
read length, word) and in the inner quantifier over the alternative
traversal, and it is done with `decide`, so the result is a theorem of the
kernel with no `sorry`, no `admit` and no extra hypothesis: the hypothesis of
each instance is literally `P2` of `def:P1P2` and the conclusion is
literally the uniqueness clause of `EulerianCycleObstruction`.

A finite verification is evidence, not a proof, and it is recorded as such
(`docs/eulerian-cycle-audit-89.md`).  Its value here is that the statement
that is being asked about is machine-checked on every small instance, so a
later proof of the general case cannot be contradicted by small examples, and
so that the *statement* (not a paraphrase) is the thing that was tested.

## The statement, isolated per genome

`UniqueAt hG L S` is the per-genome content of the first disjunct of
`EulerianCycleObstruction`, and
`obstruction_of_uniqueAt` / `uniqueAt_of_obstruction` record that it is
interchangeable with the obstruction form once `P2` is assumed --- the two
forms of the theorem are the same statement.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTSequenceGraph
open AssemblyP1

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **The first disjunct of `EulerianCycleObstruction`, at one genome:**
every alternative Eulerian cycle of the condensed `(L-1)`-mer graph spells
the truth's own vertex cycle. -/
def UniqueAt (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G))

instance (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Decidable (UniqueAt hG L S) := by
  unfold UniqueAt
  infer_instance

/-- The per-genome uniqueness clause implies the obstruction form of
`thm:BBT` at this genome, for a `P2` truth. -/
theorem obstruction_of_uniqueAt (hL : 2 ≤ L) (hP2 : P2 hG L S)
    (hu : UniqueAt hG L S) :
    ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
      VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) ∨ LongObstruction hG L S := by
  intro σ hEul
  exact Or.inl (hu σ hEul)

/-- ... and the obstruction form implies the uniqueness clause.  The two
formulations of `thm:BBT` are therefore the same statement; the finite
verification below checks the uniqueness one, which is the weaker
formulation (it is the conclusion of Theorem 3 of Bresler--Bresler--Tse
2013 read on the condensed graph). -/
theorem uniqueAt_of_obstruction (hL : 2 ≤ L) (hP2 : P2 hG L S)
    (ho : ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
      VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) ∨ LongObstruction hG L S) :
    UniqueAt hG L S := by
  intro σ hEul
  rcases ho σ hEul with hv | hl
  · exact hv
  · exact absurd hl (not_longObstruction_of_P2 hG hL hP2)

/-! ## The finite class: binary genomes up to `maxG`, read lengths up to `maxL` -/

/-- **The exact #89 statement, decided on the finite class.**  For every
binary circular genome of length at most `maxG` and every read length
`2 ≤ L ≤ maxL`: if the genome satisfies `P2` of `def:P1P2`, then every
Eulerian cycle of its condensed `(L-1)`-mer multigraph spells its own vertex
cycle.

The quantifiers are the ones of `EulerianCycleObstruction` itself; the two
outermost are written as `Finset.all` over `range` so that the whole
statement is decidable, and the third (`S`) ranges over the `Fintype`
`Fin G → Fin 2`, the fourth being the traversal quantified in `UniqueAt`.

Everything quantified here is quantified: the length, the read length, the
word, and (inside `UniqueAt`) the alternative traversal.  There is no
auxiliary hypothesis. -/
def FiniteBinary (maxG maxL : ℕ) : Prop :=
  (Finset.range (maxG + 1)).all (fun G =>
    ((Finset.range (maxL + 1)).filter (fun L => 2 ≤ L)).all (fun L =>
      (Finset.univ : Finset (Fin G → Fin 2)).all (fun S =>
        if hG : 0 < G then
          P2 ⟨G, hG, S⟩ L → UniqueAt ⟨G, hG, S⟩ L S
        else True)))

/-- The class is decidable, so `FiniteBinary` can be *decided* rather than
merely stated. -/
instance (maxG maxL : ℕ) : Decidable (FiniteBinary maxG maxL) := by
  unfold FiniteBinary
  infer_instance

/-- `Fin G → Fin 2` and `Fin G ≃ Fin G` are finite, which is what makes the
inner quantifiers of `UniqueAt` decidable; the instances are recorded here
because the finite verification below rests on them. -/
example (n : ℕ) : Fintype (Fin n → Fin 2) := inferInstance
example (n : ℕ) : Fintype (Fin n ≃ Fin n) := inferInstance

/-- **`FiniteBinary 4 6`, by `decide`:** every binary circular genome of
length at most `4` and every read length `2 ≤ L ≤ 6` satisfies the exact
statement of #89.  This is 30 words x 5 read lengths x (up to 24) traversals,
all of them enumerated by the kernel. -/
theorem finiteBinary_4_6 : FiniteBinary 4 6 := by decide

end AssemblyP1.BBTEulerian
