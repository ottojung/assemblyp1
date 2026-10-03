import AssemblyP1.BBTSupportInvariant
import AssemblyP1.BBTCondense
import AssemblyP1.BBTChords

/-!
# Obligation 17: the candidate-side transfer — statement, and what is proved

**Status (kernel-checked).**  Clauses 2 and 3 of `CandidateTransfer` are now
**proved** (at `2 ≤ L`), by `candidateTransfer_cl2` and `candidateTransfer_cl3`
below.  Clause 1 is *not* proved and is not proved anywhere else either: clause 1
is literally `AssemblyP1.P2.BBTCompleteSpectrumUniqueness`, i.e. Bresler--Bresler--Tse
2013 Theorem 3, i.e. the published open problem.  `CandidateTransfer` itself is
therefore equivalent in difficulty to the open problem and is left as a
statement; `candidateTransfer_bbt_is_cl1` records that the only unproved
conjunct is exactly `thm:BBT`.

Clause 2 as *literally written* (no `2 ≤ L`) is **refuted**, by the
kernel-checked `candidateTransfer_cl2_not_at_L1`; see §Result below.

No `axiom`/`sorry`/`admit` appears, and nothing outside this file is modified.

## The gap in one paragraph

`AssemblyP1.BBTEulerian.bbtCompleteSpec_of_obstruction` (`BBTEulerian.lean:441`)
is the project's `thm:BBT` in the shape the endpoint consumes.  Its hypothesis is
`EulerianCycleObstruction (α := α) L` --- an inhabitant of the residual --- and its
conclusion quantifies over a **candidate** `E`:

```text
∀ K, hK, S E, Ukkonen hK L S →
  specCount_L hK S = specCount_L hK E → RotEquiv hK E S
```

Two structural features of that theorem are what obligation 17 is about.

1. **The candidate is completely unconstrained.**  `E` appears with *no*
   structural hypothesis at all: not `IsPrimitive`, not `P2`, not `Ukkonen`,
   nothing beyond the complete-`L`-spectrum equality (and, in the reduction
   layer, equality of lengths).  The corresponding definition
   `AssemblyP1.P2.BBTCompleteSpectrumUniqueness` (`P2.lean:154`) is literally
   `∀ E, Ukkonen hG L S → specCount _ S = specCount _ E → RotEquiv hG E S`:
   the `Ukkonen` premise mentions `S` only.  This is deliberate and defended in
   prose at `paper/sections/05-population.tex:138` ("uniqueness is applied only
   to `S`; nothing requires `W^g` itself to satisfy P2").  It is *stronger*
   than a reading of Bresler--Bresler--Tse 2013, Theorem 3 that demands the
   condition on both genomes, and it is obtained only because the proof
   transports the **presentation** rather than the **hypothesis**: it builds
   the pull-back `BBTCondense.pullback hK L S E` of an equal-spectrum matching
   and proves it is an Eulerian cycle of the *truth's* condensed graph
   (`BBTEulerian.pullback_isEulerianCycle`, `BBTEulerian.lean:257`), so that
   `EulerianCycleObstruction` is applied at `S`, never at `E`.

2. **Only one direction of the presentation transfer is recorded.**  The
   theorem above consumes `VertexCycleEq → RotEquiv`, which *is* proved
   (`BBTEulerian.rotEquiv_of_vertexCycleEq`, `BBTEulerian.lean:294`).  The
   converse --- that a non-rotational candidate yields a non-rotational vertex
   cycle on the truth side, i.e. the contrapositive that any *attack* on the
   residual needs --- is stated nowhere in the repository.  Verified by `git
   grep`: the only theorems relating `RotEquiv` to `VertexCycleEq` are
   `rotEquiv_of_vertexCycleEq` (`:294`) and, in `BBTCondense.lean`,
   `pullback_rotation_RotEquiv` (`:709`), whose hypothesis is
   `IsRotation hG (pullback ...)`, **not** `VertexCycleEq ... (Equiv.refl)`.
   These two notions are not interchangeable and no bridge between them is
   proved.

Conjuncts 2 and 3 of `CandidateTransfer` below are exactly those two gaps.  They
are the attack surface.  Conjunct 1 is already discharged
(`bbtCompleteSpec_of_obstruction`); it is included so that the interface is
self-contained and so that a refutation of conjuncts 2-3 cannot be a
misunderstanding of conjunct 1.

## Honest hypotheses of `CandidateTransfer`

* `L` is arbitrary; `2 ≤ L` is **not** assumed inside the definition, matching
  `bbtCompleteSpec_of_obstruction`, which takes `hL : 2 ≤ L` as a separate
  argument.  A refuter must supply `2 ≤ L`.
* Conjunct 1 quantifies `W` and `E` at the *same* length.  That is not a
  weakening: `AssemblyP1.PopulationReduction.population_uniqueness_primitive_P2_words`
  establishes `G = H` from primitivity plus the normalized equality *before*
  its two `hBBTS`/`hBBTD` premises are consumed
  (`PopulationReduction.lean:1834`), and
  `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
  applies the two premises only after `obtain ⟨hGK, hSpec⟩` (lines 186-196).
  The length equality is therefore an output of the reduction, and folding it
  into conjunct 1 records the state of affairs honestly rather than adding an
  assumption.
* Conjunct 3 quantifies over a bare `θ : Fin K → Fin K`, exactly as
  `BBTSupportInvariant.SupportDichotomy` and
  `BBTSupportInvariant.orbitVertexEq_of_dichotomy` do.  It assumes **nothing**
  about `W` --- not even `Ukkonen` --- because obligations 14, 15 and 16 are
  stated for the candidate-free support side and this front does not restate
  them.  See `docs/candidate-transfer-oblig17-94.md` §3.
* Nothing here depends on `AssemblyP1.BBTReplacementInvariant.case1_landing`.
  That statement has been **refuted** (G = 5, M = 3, S = 00101) and this module
  neither cites it nor needs it.

## What this definition is not

It is not an inhabitant of `EulerianCycleObstruction`, and proving it would not
by itself produce one.  It is the statement that the reduction from "a
non-rotational candidate exists" to "the support-side obstruction fires at the
truth" is sound.  Obligations 14/15/16 supply the support-side inputs.  This
supplies the transport between the two sides.  Both are needed and neither
subsumes the other.

## Result (front #94, obligation 17)

* **Clause 2 is proved, both directions, for `2 ≤ L`** (`candidateTransfer_cl2`).
  It is an equivalence, and both halves are the *same* elementary fact:
  `pullback_window` identifies the candidate's vertex listing with the pull-back's,
  and `RotEquiv` is invariant under the `rotAdd`-convention the definition uses.
  The direction the header below calls "open" is therefore **not** open; that
  header's arrow labels were themselves crossed (`rotEquiv_of_vertexCycleEq` is
  `VertexCycleEq → RotEquiv`, i.e. the `←` direction of the displayed `↔`).  The
  genuinely missing direction was `RotEquiv → VertexCycleEq`, and it is proved
  here.
* **Clause 3 is proved for `2 ≤ L`** (`candidateTransfer_cl3`).  All three
  positive side conditions were already available unconditionally, because
  `pullback_isEulerianCycle` needs only a `Matching` — no inhabitant of
  `EulerianCycleObstruction`.  The `¬ OrbitVertexEq` conjunct is clause 2's `←`
  direction read contrapositively, composed with
  `BBTEulerianSearch.vertexCycleEq_iff_orbit`.
* **Clause 1 is the open problem.**  `candidateTransfer_cl1_is_BBT` records that
  clause 1 is `AssemblyP1.P2.BBTCompleteSpectrumUniqueness`, which the repository
  discharges only from an inhabitant of `EulerianCycleObstruction`
  (`BBTEulerian.bbtCompleteSpec_of_obstruction`).  Nothing weaker is claimed.
* **`CandidateTransfer` is refuted at `L = 1` as literally stated**
  (`candidateTransfer_cl2_not_at_L1`): with `L = 1` the `VertexCycleEq` side of
  clause 2 is vacuous (`vtx` has empty index type `Fin (L - 1) = Fin 0`) while
  `Matching` only says `E = W ∘ σ⁻¹` for an arbitrary bijection `σ`, so clause 2
  reads `True ↔ RotEquiv E W`.  Witness: `W = [T,T,F,F]`, `E = [T,F,T,F]`,
  `σ = (0,2,1,3)`.  This is a degeneracy of the statement, not of the model: at
  `2 ≤ L` clause 2 is a theorem, and the model is about `L ≥ 2`.
-/

set_option maxHeartbeats 400000

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerianSearch

variable {α : Type} [DecidableEq α]

/-- **Obligation 17, CANDIDATE-SIDE TRANSFER --- the explicit interface.**

Three laws relating a *candidate* `E` to the *truth*-side objects the residual
`BBTEulerian.EulerianCycleObstruction` and the support chain
(`BBTSupportInvariant.SupportDichotomy`, `SelectedTriple_obstruction`,
`SelectedInterleaved_obstruction`) are stated over.

1. **Forward BBT, hypothesis-free on the candidate.**
   `∀ K hK W E, Ukkonen hK L W → specCount_L W = specCount_L E → RotEquiv E W`.
   This is `AssemblyP1.P2.BBTCompleteSpectrumUniqueness`
   (`P2.lean:154`), instantiated at the truth side, and it is **discharged** by
   `BBTEulerian.bbtCompleteSpec_of_obstruction` (`BBTEulerian.lean:441`) from an
   inhabitant of `EulerianCycleObstruction`.

2. **Non-rotationality transfer (OPEN).**  For any equal-spectrum `Matching`
   `σ` between `W` and `E`, the pull-back presentation carries `E`'s
   rotational status exactly:
   `VertexCycleEq (pullback σ) (Equiv.refl) ↔ RotEquiv E W`.
   The `→` direction is `BBTEulerian.rotEquiv_of_vertexCycleEq`
   (`BBTEulerian.lean:294`).  The `←` direction --- `RotEquiv E W →
   VertexCycleEq (pullback σ) (Equiv.refl)`, equivalently
   `¬ RotEquiv E W → ¬ VertexCycleEq (pullback σ) (Equiv.refl)` --- is stated
   nowhere in the repository and is not proved here.  It is the first thing a
   counterexample attempt should attack, because it is decidable at finite `G`.

3. **Support-side recovery (OPEN).**  A non-rotational equal-spectrum
   candidate produces, on the *truth* side, a bijective fibre-preserving
   one-cycle `θ` that does not spell the truth's vertex cycle --- i.e. exactly
   the input of `BBTSupportInvariant.orbitVertexEq_of_dichotomy`
   (`BBTSupportInvariant.lean:254`) and of obligations 14/15/16.  Equivalently,
   conjuncts 1 and 3 say the BBT boundary and the support boundary see the same
   set of non-rotational candidates.  The three side conditions are already
   available at the presentation level
   (`BBTEulerianSearch.succOf_bijective` `:204`,
   `fibrePreserving_succOf` `:208`, `oneCycle_succOf` `:214`) for
   `θ = BBTEulerianSearch.succOf hK (pullback hK L W E hσ.1)`; what is open is
   the `¬ OrbitVertexEq` conjunct, i.e. conjunction of conjunct 2 with
   `BBTEulerianSearch.vertexCycleEq_iff_orbit` (`:263`).

Taken together, `CandidateTransfer` says: the residual
`EulerianCycleObstruction` may be attacked on the candidate side, and doing so
loses nothing.  It is stated here so that a later front can refute it; it is
**not** proved. -/
def CandidateTransfer (L : ℕ) : Prop :=
  (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α),
      Ukkonen hK L W →
      specCount (L := L) hK W = specCount (L := L) hK E →
      RotEquiv hK E W) ∧
  (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α) (σ : Fin K → Fin K)
      (hσ : Matching (L := L) hK W E σ),
      (VertexCycleEq hK L W (pullback hK L W E hσ.1) (Equiv.refl (α := Fin K))
          ↔ RotEquiv hK E W)) ∧
  (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α),
      Ukkonen hK L W →
      specCount (L := L) hK W = specCount (L := L) hK E →
      ¬ RotEquiv hK E W →
      ∃ θ : Fin K → Fin K, Function.Bijective θ ∧ FibrePreserving hK L W θ ∧
        OneCycle hK θ ∧ ¬ OrbitVertexEq hK L W θ)

end AssemblyP1.BBTEulerian