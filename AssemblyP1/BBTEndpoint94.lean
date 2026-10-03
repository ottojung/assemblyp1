import AssemblyP1.PopulationUniqueness
import AssemblyP1.BBTAdmissibleObstruction
import AssemblyP1.BBTInterleavedAdmissible
import AssemblyP1.BBTSupportInvariant
import AssemblyP1.BBTEulerianSearch

/-!
# Board 94, front `94b15` (ENDPOINT): the SINGLE final theorem for #89

This module writes down, once, in the project's own terms, the theorem that
closes board issue #94 / issue #89, states it **without weakening it**, and
isolates the exact residual obligations as `Prop`s so that a later pass does not
have to re-derive them from board comments.

Read `docs/population-uniqueness-end-to-end-89.md` (the #89 endpoint note) and
`docs/board94-endgame-statement-94.md` (this branch's statement front) first.

## 1. The endpoint is ONE exported theorem

`thm:population` of Bresler–Bresler–Tse 2013, in the published model, is

```
Endpoint L  :=  ∀ {G} (hG : 0 < G) (hL : 1 < L) (S : Fin G → α),
    IsPrimitive S → P2 hG L S →
      (a) ∀ K hK W, AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)
    ∧ (b) ∀ K hK W, AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
            ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S
```

clause (a) being "the truth is a population maximizer" and clause (b) being
"every population tie is a cyclic shift of the truth", i.e. uniqueness up to
cyclic rotation of the genome — the strict reading of "the maximum-likelihood
sequence is the true sequence" recorded in `docs/ml-formalization-contract.md`
and the tie-semantics section of `docs/population-uniqueness-end-to-end-89.md`.
It is
**not** weakened here: no `PopTie`, no `PopMaximizer`, no caller-supplied bridge
parameter survives, and the candidate class is the actual `P2` of `def:P1P2`
together with actual primitivity.

`Endpoint L` is **already a theorem of this repository**,
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`, on the
single non-kernel hypothesis `BBTEulerian.EulerianCycleObstruction L`.
`endpoint_of_obstruction` below is that fact, re-derived in one line so the
gap is visible in one place.

## 2. The SINGLE remaining obligation

`BBTEulerian.EulerianCycleObstruction (α := α) L` (Pevzner 1995 Lemma 9 /
`thm:BBT`, read in the Eulerian-cycle form of Bresler–Bresler–Tse 2013,
Theorem 3): the condensed `(L-1)`-mer graph of a Ukkonen-satisfying genome has
a unique Eulerian cycle up to choice of starting point.  Its exact text is
`BBTEulerian.lean:400`:

```
∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
  ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
    VertexCycleEq hK L S σ (Equiv.refl _) ∨ LongObstruction hK L S
```

Everything else in the chain — the Gibbs/KL layer, `P2.imp_Ukkonen`, the
gcd-one reduction, the proportional-cancellation lemma, `BBTUniqueAt` and its
derivation from the obstruction — is kernel-checked in this repository.

`Residual L` below is that obligation as a `Prop`.  It is stated, not proved.

## 3. STANDING RULE: `AdmissibleObstruction` is a CONCLUSION

`BBTAdmissible.AdmissibleObstruction` is the endgame's replacement for the
refuted `LongObstruction`: two interleaved right-maximal repeats of length
`≥ L - 1`, at least one preceding-blocked.  Because
`BBTAdmissible.P2_and_admissible_00101` is kernel-checked — `P2` and
`AdmissibleObstruction` hold **together** at `S = 00101`, `L = 3` — the
statement `P2 ∧ AdmissibleObstruction → False` is **false by construction**.

**No statement of that shape occurs anywhere in this file, and no future front
may write one.**  `AdmissibleObstruction` may only ever appear as a *conclusion*
(of the descent step) or as a *target to be refuted from another side*; the
discharger must produce `False` from `P2` plus `Bad`-ness alone.

`DescentObligation` / `DischargerObligation` below are stated in the only
admissible shapes: the descent obligation *concludes* `AdmissibleObstruction`
from descent hypotheses; the discharger obligation concludes `False` from `P2`
and badness and **never mentions** `AdmissibleObstruction`.

## 4. Non-axioms

No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, or linter suppression
occurs in this file.  Everything is kernel-checked by `lake env lean`.
-/

namespace AssemblyP1.BBTEndpoint94

open AssemblyP1
open AssemblyP1.P2
open AssemblyP1.BBTEulerian
open AssemblyP1.PopulationUniqueness
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTAdmissible
open AssemblyP1.BBTReplacement
open AssemblyP1.BBTSupport
open AssemblyP1.BBTEulerianSearch

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ}

/-! ## 1. The single final theorem for #89 -/

/-- **THE SINGLE FINAL THEOREM FOR #89 (`thm:population`).**  Among primitive
`P2`-admissible oriented circular candidates, the truth maximizes the published
population log-likelihood, and every population tie is a cyclic shift of the
truth.  Quantified here as a `Prop` so that the single hypothesis it needs is
visible; `endpoint_of_obstruction` shows it is already a theorem of the library
under `Residual`. -/
def Endpoint (L : ℕ) : Prop :=
  ∀ (hG : 0 < G) (_hL : 1 < L) (S : Fin G → α),
    PopulationReduction.IsPrimitive S → P2 hG L S →
      ( (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))
        ∧
        (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
            ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) )

/-! ## 2. The single remaining obligation: `thm:BBT` in Eulerian-cycle form -/

/-- **THE SINGLE REMAINING MATHEMATICAL OBLIGATION.**  Uniqueness of the
Eulerian cycle of the condensed `(L-1)`-mer graph, in the obstruction form of
`BBTEulerian.EulerianCycleObstruction` (`BBTEulerian.lean:400`).  This is a
`def`, not an `axiom`; it is the only hypothesis of `Endpoint` that is not
kernel-checked in this repository. -/
def Residual (L : ℕ) : Prop := BBTEulerian.EulerianCycleObstruction (α := α) L

/-- **The endpoint follows from the single residual obligation.**  Kernel-checked;
this is the whole of the gap. -/
theorem endpoint_of_obstruction (L : ℕ) (h : Residual (α := α) L) :
    Endpoint (α := α) (G := G) L := by
  intro hG _hL S hPrimS hP2S
  exact population_unique_ML_up_to_rotation L hG _hL S hPrimS hP2S h

/-! ## 3. The descent obligations, in the only admissible shapes

`BBTAdmissible.AdmissibleObstruction` is a CONCLUSION.  The two obligations
below are what board 94 has left to prove inside the descent; both are stated
as `Prop`s with no proof, and both are discharged *upward* into `Endpoint` only
if `Residual` is proved.  Note they are obligations about the *descent*, not the
whole of `Residual`; the gap between them and `Residual` is documented in
`docs/population-uniqueness-end-to-end-89.md` ("the one residual formalization
boundary") and quantified in `docs/admissible-obstruction-94.md` §5. -/

/-- **Descent obligation (step 4 of `docs/admissible-obstruction-94.md` §5).**
A selected interleaving of a *primitive* genome yields the admissible
obstruction.  `AdmissibleObstruction` occurs here as a **conclusion**, never as a
hypothesis.

Kernel-checked on this branch at general `G`, general `L`, under primitivity:
`BBTInterleaved.selectedInterleaved_admissible_of_P2` (commit `078d2b7`).  This
`Prop` is the *full* form demanded by `docs/admissible-obstruction-94.md` §5,
i.e. without the `P2` hypothesis the front could not state. -/
def DescentObligation : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (θ : Fin K → Fin K), 2 ≤ M →
    PopulationReduction.IsPrimitive S → P2 hK M S →
      Function.Bijective θ → FibrePreserving (hG := hK) (L := M) S θ →
        OneCycle hK θ → ¬ OrbitVertexEq (hG := hK) (L := M) S θ →
          ¬ SelectedTriple (hG := hK) (L := M) S θ →
            SelectedInterleaved (hG := hK) (L := M) S θ →
              BBTAdmissible.AdmissibleObstruction hK M S

/-- The `SelectedInterleaved ⟹ AdmissibleObstruction` step, extracted from the
obligation above in the shape the descent actually uses. -/
theorem selectedInterleaved_concludes_admissible
    (hD : DescentObligation) (K M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K)
    (θ : Fin K → Fin K) (hM : 2 ≤ M)
    (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hK M S)
    (hbi : Function.Bijective θ) (hfp : FibrePreserving (hG := hK) (L := M) S θ)
    (hoc : OneCycle hK θ) (hgood : ¬ OrbitVertexEq (hG := hK) (L := M) S θ)
    (hnT : ¬ SelectedTriple (hG := hK) (L := M) S θ)
    (hSel : SelectedInterleaved (hG := hK) (L := M) S θ) :
    BBTAdmissible.AdmissibleObstruction hK M S :=
  hD K M S hK θ hM hPrim hP2 hbi hfp hoc hgood hnT hSel

/-- **Discharger obligation.**  From `P2` alone (plus the descent facts), derive
`False`.

This is stated so that it **cannot** be read as `P2 ∧ AdmissibleObstruction →
False`: `AdmissibleObstruction` does not occur in it, and must not.  The
instance `P2_and_admissible_00101` (kernel-checked, commit `b0de723`) shows any
statement that puts the two together as hypotheses and concludes `False` is
false at `S = 00101`, `L = 3`. -/
def DischargerObligation : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (θ : Fin K → Fin K), 2 ≤ M →
    PopulationReduction.IsPrimitive S → P2 hK M S →
      Function.Bijective θ → FibrePreserving (hG := hK) (L := M) S θ →
        OneCycle hK θ → ¬ OrbitVertexEq (hG := hK) (L := M) S θ →
          ¬ SelectedTriple (hG := hK) (L := M) S θ →
            SelectedInterleaved (hG := hK) (L := M) S θ → False

/-! ## 4. The refuted shapes, recorded so no future front re-proposes them -/

/-- **`P2 → LongObstruction` is refuted by construction** (`BBTAdmissible`,
commit `b0de723`): under `2 ≤ L`, `P2` is the conjunction of the negations of
exactly the two clauses of `LongObstruction`.  No discharger obligation may have
`LongObstruction` as its conclusion. -/
theorem P2_refutes_LongObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (hL : 2 ≤ L) (hP2 : P2 hG L S) : ¬ LongObstruction hG L S :=
  BBTAdmissible.P2_not_LongObstruction hG L S hL hP2

/-- **`P2` and the admissible obstruction are jointly inhabited** (`00101`,
`L = 3`), so the admissible obstruction is a real conclusion and not a
refutation of `P2`. -/
theorem admissible_not_refuted_by_P2 :
    P2 BBTChords.hG5 3 BBTReplacement.S5b ∧
      BBTAdmissible.AdmissibleObstruction (hG := BBTChords.hG5) (L := 3)
        BBTReplacement.S5b :=
  BBTAdmissible.P2_and_admissible_00101

end AssemblyP1.BBTEndpoint94
