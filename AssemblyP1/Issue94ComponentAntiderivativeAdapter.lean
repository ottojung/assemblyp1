import AssemblyP1.Issue94ComponentAlgebra
import AssemblyP1.Issue94ComponentResidual

/-!
# Board 94: antiderivative adapter for the component-deletion path

This module is the tiny adapter connecting the canonical
`componentSwitch`/`componentResidual` of `Issue94ComponentResidual` to the
pure deletion algebra of `Issue94ComponentAlgebra`.  It instantiates
`delete_component` with the concrete switch and residual, so that the
antiderivative construction (which supplies `g` satisfying the coboundary
equation and commuting with the residual) yields the exact statement:

```
AltF (sigma.trans g) = componentResidual ...
```

i.e. postcomposing the listing by the antiderivative `g` deletes exactly the
interlace component from `AltF`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94ComponentAntiderivativeAdapter

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94ComponentAlgebra
open AssemblyP1.Issue94ComponentResidual

variable {α : Type} [DecidableEq α] {K L : ℕ}

/-- **THE ANTIDERIVATIVE ADAPTER.**  Given a listing `sigma`, a chord `c`, and
a permutation `g` of the starts satisfying:

* the **coboundary equation**
  `componentSwitch ... x = g⁻¹ (nextPos (g (prevPos x)))`, and
* **commutation with the residual**
  `g (componentResidual ... x) = componentResidual ... (g x)`,

postcomposing the listing by `g` deletes exactly the interlace component from
`AltF`:

```
AltF (sigma.trans g) = componentResidual ...
```

This is `Issue94ComponentAlgebra.delete_component` instantiated with the
canonical component switch and residual. -/
theorem altF_trans_of_antiderivative
    (hK : 0 < K) (S : Fin K → α) (sigma : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L S sigma) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    (c : AltFChord hK sigma)
    (g : Fin K ≃ Fin K)
    (hcob : ∀ x : Fin K,
      componentSwitch hK S sigma hEul hL hLK hprim hP2 c x
        = g.symm (nextPos hK (g (prevPos hK x))))
    (hcomm : ∀ x : Fin K,
      g (componentResidual hK S sigma hEul hL hLK hprim hP2 c x)
        = componentResidual hK S sigma hEul hL hLK hprim hP2 c (g x)) :
    ∀ q : Fin K,
      AltF hK (sigma.trans g) q
        = componentResidual hK S sigma hEul hL hLK hprim hP2 c q :=
  delete_component hK sigma g
    (componentSwitch hK S sigma hEul hL hLK hprim hP2 c)
    (componentResidual hK S sigma hEul hL hLK hprim hP2 c)
    (fun x => altF_eq_switch_residual hK S sigma hEul hL hLK hprim hP2 c x)
    (fun x => switch_residual_commute hK S sigma hEul hL hLK hprim hP2 c x)
    hcomm hcob

#print axioms AssemblyP1.Issue94ComponentAntiderivativeAdapter.altF_trans_of_antiderivative

end AssemblyP1.Issue94ComponentAntiderivativeAdapter
