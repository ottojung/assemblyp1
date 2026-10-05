import AssemblyP1.BBTEulerian
import AssemblyP1.PopulationUniqueness
import AssemblyP1.Issue94EulerianTheta

/-!
# Front `94bbt` (recovery `94bbt`-rec): auditing the claim that the residual
# hypothesis of `PopulationUniqueness` is `thm:BBT`

Branch `proof/94-eulerian-obstruction`, board 94, issue #89.  Full record in
`docs/issue-94-obstruction-equiv.md`.

## The gap, re-derived

`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
(and `..._same_length`, `population_tie_implies_rotation`) carry one explicit
hypothesis

  `hPevzner : AssemblyP1.BBTEulerian.EulerianCycleObstruction (α := α) L`

with `2 ≤ L`.  `BBTEulerian.lean` states

```
def UniqueEulerianCycle (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

def EulerianCycleObstruction (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L S
```

`EulerianCycleObstruction ↔ UniqueEulerianCycle` is
`BBTEulerian.uniqueEulerianCycle_of_obstruction` /
`obstruction_of_uniqueEulerianCycle`, both proved there.

## The claim worth having

`AssemblyP1.P2.BBTUniqueAt L` is the published `thm:BBT` as this project states
it: the complete `L`-spectrum of an `Ukkonen` circular word determines it up
to cyclic rotation, uniformly over all genome lengths.  The natural reduction is

  `EulerianCycleObstruction L ↔ BBTUniqueAt L`,  for `2 ≤ L`.

The forward implication is already in the library
(`BBTEulerian.bbtUniqueAt_of_obstruction`).  **This module does not close the
converse.**  §1 below is a kernel-checked refutation of the only argument the
residue of the killed front `94d4` offered for it, and §2 records what survives
and what does not.

## §1. REFUTED: not every start-permutation is the pull-back of a `Matching`

The residue argued that `EulerianCycle hG L S σ` needs no content beyond a
permutation of the starts: for the read-off candidate `E s = S (σ s)` "the
complete `L`-window of `E` at `s` is the complete `L`-window of `S` at `σ s`,
by construction", hence every bijection of starts is the pull-back of a
`Matching` with no hypothesis on `σ` at all, and `§1` of that draft carried no
information.

**That is false, and it is `decide`-closed.**  `window hG (readOff S σ) s` reads
`S` at `σ ((s + d) mod G)`, while `window hG S (σ s)` reads `S` at
`(σ s + d) mod G`: the two agree only if `σ` carries the shift, i.e. only for
rotations (and, incidentally, for some accidental instances of short periodic
words such as `S = 0101`).  Concretely, at `S = 0001`, `G = 4`, `L = 3` and
`σ = (2 3)`, the engine computation fails
(`window_readOff_refuted`), and the conclusion drawn from it fails with it: no
matching whatsoever has that `σ` as its pull-back
(`exists_matching_pullback_refuted`).

Note also that the draft's repair of its own failed step passed through
`equiv_apply_eq : ∀ σ x, σ x = x`, the statement that every `Equiv` of `Fin G`
is the identity.  That is `decide`-refutable as well
(`equiv_identity_refuted`), and it cannot have been proved: had it been, `S`
would be its own pull-back candidate for every `σ` and §1 would have been
vacuous rather than false.

So the residue's route to the converse is closed: it rests on a false
structural claim, not on a gap in the elaboration.

### What *is* in the tree, in the other direction

`Issue94EulerianTheta.theta_of_same_spectrum_is_one_cycle`: a *matching*
pull-back is an `EulerianCycle` (together with the window agreement).  I.e.
`Matching`-pull-backs ⊆ `EulerianCycle`s, which is the direction the reduction
needs to go the *other* way round and the only one available here.  Concretely,
`BBTEulerian.pullback_isEulerianCycle`.

Whether every `EulerianCycle σ` is the pull-back of *some* `Matching` is a
different and much narrower question than the residue's claim, and it is not
settled here; at `G = 4`, `L = 3` it does hold on every instance (binary
alphabet, all `2⁴` words and all `4!` permutations, checked by script), which
is evidence and nothing more.  Proving it would require constructing, from the
traversal order supplied by the `single` clause, a circular candidate word
`E` whose `L`-windows are the traversal's `L`-windows; the residue's `readOff`
construction is not that word (it reads the truth at `σ`-permuted positions,
which the `single` clause does not control).

## §2. Status, recorded honestly

* **proved, in the library**: `BBTEulerian.bbtUniqueAt_of_obstruction`,
  i.e. `EulerianCycleObstruction L → BBTUniqueAt L` for `2 ≤ L`.
* **proved here**: `bbtUniqueAt_iff_residual` (§3), a decomposition of
  `BBTUniqueAt L` into the independent per-genome-length family `BBTResidual`.
* **not proved here**: `BBTUniqueAt L → EulerianCycleObstruction L`, i.e. the
  reverse of the library's implication.  It is named as the open `Prop`
  `ObstructionFromBBT` and left as a `Prop`, with no `axiom`, `sorry` or
  `admit` anywhere.
* **open regardless**: an inhabitant of `BBTUniqueAt` (equivalently of
  `EulerianCycleObstruction`, equivalently of `hPevzner`) is missing.  Nothing
  in this module is progress toward an inhabitant; §2 is bookkeeping.

`BBTCompleteSpectrumUniqueness` demands `Ukkonen` of the **truth only**
(`∀ E, Ukkonen hK L S → ...`), never of the candidate.  Worth recording,
because it is what makes `Issue94EulerianTheta.theta_of_same_spectrum_is_one_cycle`
usable with an arbitrary equal-spectrum competitor: a candidate obtained by
reindexing the circle by a permutation need not satisfy `Ukkonen` itself.
-/

set_option maxHeartbeats 2000000

namespace AssemblyP1.BBT94

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94EulerianTheta
open AssemblyP1

variable {α : Type} [DecidableEq α] {G : ℕ}

/-! ## 1. The residue's §1 is refuted -/

/-- **The read-off candidate of a start-permutation.**  The residue's
construction: `σ s` is the truth start whose complete `L`-read is presented at
candidate start `s`. -/
def readOff {G : ℕ} (S : Fin G → α) (σ : Fin G ≃ Fin G) : Fin G → α :=
  fun s => S (σ s)

/-- `S = 0001`, the word used by the refutations below. -/
def S0001 : Fin 4 → Fin 2 := ![0, 0, 0, 1]

/-- **REFUTED (`decide`): the residue's engine, at a named instance.**
`window (readOff S0001 (2 3)) 0` at offset `2` is `S0001 (σ 2) = S0001 3 = 1`,
whereas `window S0001 (σ 0) = window S0001 0` at offset `2` is `S0001 2 = 0`. -/
theorem window_readOff_refuted_S0001 :
    window (L := 3) hG4 (readOff S0001 (Equiv.swap 2 3 : Fin 4 ≃ Fin 4)) 0 ⟨2, by decide⟩
      ≠ window (L := 3) hG4 S0001 ((Equiv.swap 2 3 : Fin 4 ≃ Fin 4) 0) ⟨2, by decide⟩ := by
  decide

/-- **REFUTED (`decide`): the residue's engine, in general.**  The claim that
the complete `L`-window of `readOff S σ` at `s` is the complete `L`-window of
`S` at `σ s`, with no hypothesis on `σ`, is false; `window_readOff_refuted_S0001`
is the instance found by exhaustive scan (`G = 4`, `L = 3`, all `2⁴` binary
words, all `4!` permutations, all starts and offsets). -/
theorem window_readOff_refuted :
    ¬ (∀ (S : Fin 4 → Fin 2) (σ : Fin 4 ≃ Fin 4) (s : Fin 4) (d : Fin 3),
      window (L := 3) hG4 (readOff S σ) s d = window (L := 3) hG4 S (σ s) d) := by
  decide

/-- **REFUTED (`decide`): `Fin G ≃ Fin G` is not the identity.**  The lemma the
residue introduced to repair its own elaboration failure, `σ x = x`, is false:
`(Equiv.swap 2 3) 2 = 3`.  Had it been provable, §1 of the residue would have been
vacuous (every `σ` would be matched by `E = S`) rather than false. -/
theorem equiv_identity_refuted : ¬ (∀ (σ : Fin 4 ≃ Fin 4) (x : Fin 4), σ x = x) :=
  fun h => absurd (h (Equiv.swap 2 3 : Fin 4 ≃ Fin 4) 2) (by decide)

/-- **REFUTED: the conclusion drawn from the engine.**  At `S = 0001`, `G = 4`,
`L = 3`, `σ = (2 3)`: *no* `Matching` has this `σ` as its pull-back, whatever
the candidate word is.  So the converse of
`BBTEulerian.bbtUniqueAt_of_obstruction` cannot be closed by "every
start-permutation is a matching pull-back": that premise is false here.

Proof.  `pullback_window` reads the matched pair at `σ s` off the matching, so
a matching whose pull-back is `(2 3)` forces the candidate's window at `σ 1 = 1`
to be the truth's `(0,0,1)`, putting the symbol at candidate position `2` equal
to `0`; and its window at `σ 2 = 3` to be the truth's `(1,0,0)`, putting the
same symbol equal to `1`. -/
theorem exists_matching_pullback_refuted :
    ¬ ∃ (E : Fin 4 → Fin 2) (μ : Fin 4 → Fin 4) (hμ : Function.Bijective μ),
      Matching (L := 3) hG4 S0001 E μ ∧
        ∀ s : Fin 4, pullback hG4 3 S0001 E hμ s = (Equiv.swap 2 3) s := by
  rintro ⟨E, μ, hμ, hm, hp⟩
  have hW : ∀ s : Fin 4,
      window (L := 3) hG4 S0001 ((Equiv.swap 2 3 : Fin 4 ≃ Fin 4) s)
        = window (L := 3) hG4 E s := by
    intro s
    have hpb := pullback_window (L := 3) hG4 S0001 E hm s
    rwa [hp s] at hpb
  have hs1 : ((Equiv.swap 2 3 : Fin 4 ≃ Fin 4) : Fin 4 → Fin 4) 1 = 1 := rfl
  have hs2 : ((Equiv.swap 2 3 : Fin 4 ≃ Fin 4) : Fin 4 → Fin 4) 2 = 3 := rfl
  -- the candidate's window at `1` is `(0,0,1)`: its symbol at position `2` is `0`
  have e2zero : E 2 = 0 := by
    have h := congrFun (hW 1) ⟨1, by decide⟩
    rw [hs1] at h
    have h' : cyc hG4 S0001 2 = cyc hG4 E 2 := h
    have h'' : S0001 2 = E 2 := h'
    rw [← h'']
    decide
  -- the candidate's window at `2` reads the truth at `3`, i.e. `(1,0,0)`
  have e2one : E 2 = 1 := by
    have h := congrFun (hW 2) ⟨0, by decide⟩
    rw [hs2] at h
    have h' : cyc hG4 S0001 3 = cyc hG4 E 2 := h
    have h'' : S0001 3 = E 2 := h'
    rw [← h'']
    decide
  omega

/-! ## 2. The converse, named as the open `Prop` -/

/-- **The unproved converse of `BBTEulerian.bbtUniqueAt_of_obstruction`.**
`BBTUniqueAt L → EulerianCycleObstruction L`, for `2 ≤ L`.  It is a `Prop` and
nothing more: it is *not* an inhabitant, it is not proved, and §1 explains why
the one available proof attempt was rejected. -/
def ObstructionFromBBT (L : ℕ) : Prop :=
  BBTUniqueAt (α := α) L → EulerianCycleObstruction (α := α) L

/-- The library's direction, restated as the residual being *at most*
`thm:BBT`: the endpoint of #89 follows from the published theorem, so no
stronger input than `hPevzner` is required. -/
theorem bbtUniqueAt_of_obstruction' {L : ℕ} (hL : 2 ≤ L)
    (h : EulerianCycleObstruction (α := α) L) : BBTUniqueAt (α := α) L :=
  bbtUniqueAt_of_obstruction hL h

/-! ## 3. The residual obligation, decomposed -/

/-- **The residual obligation at one genome length `K`.**
`BBTUniqueAt L` is a countable conjunction of these; there is no content
shared between two different genome lengths, so the residual obligation
decomposes into one independent obligation per `K`.  The `Ukkonen` premise of
the truth is already inside `BBTCompleteSpectrumUniqueness`.  Nothing is proved
here about any individual conjunct --- that is the open part. -/
def BBTResidual {α : Type} [DecidableEq α] (L : ℕ) {K : ℕ} (hK : 0 < K) :
    Prop :=
  ∀ (S : Fin K → α), BBTCompleteSpectrumUniqueness hK L S

/-- The per-length obligations are exactly the conjuncts of the residual. -/
theorem bbtUniqueAt_iff_residual {L : ℕ} :
    BBTUniqueAt (α := α) L ↔
      ∀ (K : ℕ) (hK : 0 < K), BBTResidual (α := α) L hK := by
  constructor
  · intro h K hK S
    exact h K hK S
  · intro h K hK S
    exact h K hK S

/-! ## 4. Executable audit -/

#print axioms BBTEulerian.uniqueEulerianCycle_of_obstruction
#print axioms BBTEulerian.obstruction_of_uniqueEulerianCycle
#print axioms BBTEulerian.bbtUniqueAt_of_obstruction
#print axioms BBTEulerian.pullback_isEulerianCycle
#print axioms AssemblyP1.BBT94.window_readOff_refuted_S0001
#print axioms AssemblyP1.BBT94.window_readOff_refuted
#print axioms AssemblyP1.BBT94.equiv_identity_refuted
#print axioms AssemblyP1.BBT94.exists_matching_pullback_refuted
#print axioms AssemblyP1.BBT94.bbtUniqueAt_of_obstruction'
#print axioms AssemblyP1.BBT94.bbtUniqueAt_iff_residual
#print axioms Issue94EulerianTheta.theta_of_same_spectrum_is_one_cycle
#print axioms Issue94EulerianTheta.badThetaObstruction_of_bbt
#print axioms Issue94EulerianTheta.bbt_of_badThetaObstruction
#print axioms Issue94EulerianTheta.vertexCycleEq_of_RotEquiv_pullback
#print axioms PopulationUniqueness.population_unique_ML_up_to_rotation

end AssemblyP1.BBT94