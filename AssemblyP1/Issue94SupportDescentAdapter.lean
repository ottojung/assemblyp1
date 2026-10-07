import AssemblyP1.Issue94P2PrimInterface
import AssemblyP1.Issue94SupportDescent

/-!
# Board 94 / issue #89, front `94descend`: the support-descent route's adapter
# to the endpoint's exact long uniqueness hypothesis

This module is the plug-in point for the support-descent route of #89. It
converts the route's single named input — a **concrete support-descent step**,
i.e. an inhabitant of the hypothesis of
`AssemblyP1.Issue94SupportDescent.long_eulerian_unique_of_support_descent` —
into `P2LongUnique L`, the *exact* long uniqueness hypothesis that
`AssemblyP1.Issue94Interface.population_unique_ML_of_long_unique` consumes, and
then into `thm:population` itself with the short range parameterized.

## 1. The input

`SupportDescentStep L` is the descent-step hypothesis of
`Issue94SupportDescent.long_eulerian_unique_of_support_descent`, abstracted
from one truth to the whole long window: for every genome length `K ≥ L` and
every circular word `W` of that length, a step which from any
`EulerianCycle σ` of positive `supportMeasure` produces a strictly smaller
`EulerianCycle τ` that is pointwise vertex-equal to `σ`.  No `P2`, no
primitivity and no `Ukkonen` is demanded of `W`: the step is a property of the
truth's own traversal, and the interface's `P2`-and-primitive restrictions on
the truth are discharged by the caller, not used here.

`SupportDescentStep L` is a `Prop` and is **not** an inhabitant, here or
anywhere in the tree.

## 2. The adapter, kernel-checked

The conversion is the standard four-step route of
`Issue94LongWindowSplit.bbtCompleteSpec_of_short_window`, with the short-window
theorem replaced by the support-descent endpoint:

1. `BBTChords.exists_matching` — equal complete `L`-spectra give a `Matching`;
2. `BBTEulerian.pullback_isEulerianCycle` — its pull-back is an
   `EulerianCycle` of the truth;
3. `Issue94SupportDescent.long_eulerian_unique_of_support_descent` — the
   descent step makes its vertex cycle the truth's own;
4. `BBTEulerian.rotEquiv_of_vertexCycleEq` — a rotational vertex cycle is a
   rotation of the word.

`bbtCompleteSpec_of_supportDescent` is the single-instance form (one truth,
one step at that truth); `p2LongUnique_of_supportDescentStep` is the adapter
to the exact hypothesis of the endpoint: it returns `P2LongUnique L` verbatim,
with the `P2` and primitivity premises of the interface discarded, because the
descent step is assumed of every long-range truth.

## 3. The endpoint, with the short case parameterized

`population_unique_ML_of_supportDescent` is
`Issue94Interface.population_unique_ML_of_long_unique` with `P2LongUnique L`
supplied by §2 and the short half `ShortRangeUnique L` taken as an explicit
parameter — the support-descent step says nothing about genome lengths
`K < L`, so the short range is not proved here and is passed in. Its
conclusion is `thm:population`'s conclusion verbatim.

## 4. What this does not do

* **No inhabitant of `SupportDescentStep L`**, at any `L`. Issue #89 is not
  settled; the descent step is the route's own input and is exactly the
  hypothesis of the already-merged `Issue94SupportDescent` endpoint.
* **No inhabitant of `P2LongUnique L`** is claimed: §2 produces it *from* a
  descent step, and without one it remains a `Prop`.
* The short range is **not** re-proved. `ShortRangeUnique L` is a parameter of
  the endpoint theorem, discharged elsewhere in the tree by
  `Issue94KShort.vertexCycleEq_short_window_general` (see
  `AssemblyP1/Issue94LongWindowSplit.lean`, not imported here).
* No definition is changed. `EulerianCycle`, `VertexCycleEq`, `Matching`,
  `pullback`, `specCount`, `RotEquiv`, `P2`, `IsPrimitive`, `AdmClass`,
  `PopLogLik`, `popSpectrum`, `supportMeasure` and `PointwiseVtxEq` are used
  exactly as their own modules state them.
* No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter
  suppression. §5 is the `#print axioms` audit and reports only `propext`,
  `Classical.choice`, `Quot_sound`.

Source fidelity: the support-descent step is
`Issue94SupportDescent.long_eulerian_unique_of_support_descent`'s hypothesis
verbatim (its `supportMeasure` is `|Support (AltF hG σ)|`, the finite support
of the traversal difference, so the descent is a finite termination argument);
the spectrum, rotation and population vocabulary is `P2.lean`,
`BBTChords.lean`, `BBTCondense.lean`, `BBTEulerian.lean` and
`PopulationUniqueness.lean`'s own.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94SupportDescentAdapter

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94Interface
open AssemblyP1.P2
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationUniqueness
open AssemblyP1.Issue94SupportDescent

variable {α : Type} [DecidableEq α] [Fintype α] {G H L : ℕ}

/-! ## 1. The input: a concrete support-descent step -/

/-- **A concrete support-descent step, in the long window.**  For every genome
length `K ≥ L` and every circular word `W : Fin K → α`, the hypothesis of
`Issue94SupportDescent.long_eulerian_unique_of_support_descent` at the truth
`(K, L, W)`: from any `EulerianCycle σ` of positive `supportMeasure` one can
step to a strictly smaller `EulerianCycle τ` that agrees with `σ` on every
vertex.  This is the support-descent route's single named input, abstracted
from one truth to the whole long window.

No `P2`, no primitivity and no `Ukkonen` is demanded of `W`.  This is a `Prop`
and is **not** an inhabitant. -/
def SupportDescentStep (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), L ≤ K →
    ∀ σ : Fin K ≃ Fin K,
      EulerianCycle hK L W σ →
      0 < supportMeasure hK σ →
      ∃ τ : Fin K ≃ Fin K,
        EulerianCycle hK L W τ ∧
        supportMeasure hK τ < supportMeasure hK σ ∧
        PointwiseVtxEq hK L W σ τ

/-! ## 2. The adapter, kernel-checked -/

/-- **The single-instance bridge.**  At `2 ≤ L`, a truth `W` of length `K ≥ L`
with a concrete support-descent step at `(K, L, W)` has its complete
`L`-spectrum determine it up to cyclic rotation: any competitor `E` with the
same spectrum is a rotation of `W`.

Proof: equal spectra give a `Matching` (`BBTChords.exists_matching`); its
pull-back is an `EulerianCycle` (`BBTEulerian.pullback_isEulerianCycle`); the
descent step makes its vertex cycle the truth's own
(`Issue94SupportDescent.long_eulerian_unique_of_support_descent`); and a
rotational vertex cycle is a rotation of the word
(`BBTEulerian.rotEquiv_of_vertexCycleEq`).  The `P2`, primitivity and
`Ukkonen` hypotheses of `thm:BBT` are not used: the descent step is assumed of
the truth directly. -/
theorem bbtCompleteSpec_of_supportDescent (hL : 2 ≤ L) {K : ℕ} (hK : 0 < K)
    (_hLK : L ≤ K) (W E : Fin K → α)
    (hspec : specCount (L := L) hK W = specCount (L := L) hK E)
    (hstep :
      ∀ σ : Fin K ≃ Fin K,
        EulerianCycle hK L W σ →
        0 < supportMeasure hK σ →
        ∃ τ : Fin K ≃ Fin K,
          EulerianCycle hK L W τ ∧
          supportMeasure hK τ < supportMeasure hK σ ∧
          PointwiseVtxEq hK L W σ τ) :
    RotEquiv hK E W := by
  obtain ⟨σ, hm⟩ := exists_matching hK W E hspec
  have hEul : EulerianCycle hK L W (pullback hK L W E hm.1) :=
    pullback_isEulerianCycle hK L W hm
  have hVertex : VertexCycleEq hK L W (pullback hK L W E hm.1)
      (Equiv.refl (α := Fin K)) :=
    long_eulerian_unique_of_support_descent hK L W hstep _ hEul
  exact rotEquiv_of_vertexCycleEq hK L W (pullback hK L W E hm.1) hL hVertex
    (fun s => (pullback_window hK L W E hm s).symm)

/-- **THE ADAPTER.**  A concrete support-descent step in the long window yields
`P2LongUnique L` — the exact long uniqueness hypothesis that
`Issue94Interface.population_unique_ML_of_long_unique` consumes, at every
genome length `K ≥ L`, with the competitor unconstrained.

The `P2` and primitivity premises of `P2LongUnique` are discarded, not used:
the descent step is assumed of every long-range truth, so the bridge of §2
applies at every `P2`-and-primitive truth the interface quantifies over. -/
theorem p2LongUnique_of_supportDescentStep (hL : 2 ≤ L)
    (hstep : SupportDescentStep (α := α) L) : P2LongUnique (α := α) L := by
  intro K hK W hLK _hP2 _hprim E hspec
  exact bbtCompleteSpec_of_supportDescent hL hK hLK W E hspec (hstep K hK W hLK)

/-! ## 3. The endpoint, with the short case parameterized -/

/-- **`thm:population` from a concrete support-descent step, plus the short
range.**  The conclusion is
`Issue94Interface.population_unique_ML_of_long_unique`'s conclusion verbatim —
the same two conjuncts, the same `PopLogLik`, the same `AdmClass`, the same
`popSpectrum` — with `P2LongUnique L` supplied by §2 and the short half
`ShortRangeUnique L` taken as an explicit parameter.

The short range is parameterized, not proved: a support-descent step is a
statement about a truth's own Eulerian cycles and says nothing about genome
lengths `K < L`.  `hShort` is discharged elsewhere in the tree by
`Issue94KShort.vertexCycleEq_short_window_general` (see
`AssemblyP1/Issue94LongWindowSplit.lean`, which is not imported here). -/
theorem population_unique_ML_of_supportDescentStep
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hstep : SupportDescentStep (α := α) L)
    (hShort : ShortRangeUnique (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) :=
  population_unique_ML_of_long_unique L hG hL S hPrimS hP2S
    (p2LongUnique_of_supportDescentStep (by omega) hstep) hShort

/-! ## 5. Executable audit -/

#print axioms AssemblyP1.Issue94SupportDescentAdapter.SupportDescentStep
#print axioms AssemblyP1.Issue94SupportDescentAdapter.bbtCompleteSpec_of_supportDescent
#print axioms AssemblyP1.Issue94SupportDescentAdapter.p2LongUnique_of_supportDescentStep
#print axioms AssemblyP1.Issue94SupportDescentAdapter.population_unique_ML_of_supportDescentStep
#print axioms AssemblyP1.Issue94SupportDescent.long_eulerian_unique_of_support_descent
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_long_unique

end AssemblyP1.Issue94SupportDescentAdapter
