import AssemblyP1.Issue94P2SupportDescent
import AssemblyP1.Issue94SupportDescentAdapter
import AssemblyP1.Issue94P2PrimInterface
import AssemblyP1.P2RepeatResidual

/-!
# Board 94 / issue #89, front `94final`: the final witness adapter

This module is the last plug-in point of the support-descent route.  It
consumes the route's single named input — the **component antiderivative
witness** `hantider` — and produces the two theorems the endpoint needs:

* `p2PrimSupportDescentStep_of_component_witness` produces
  `P2PrimSupportDescentStep L`, the `P2`/primitive-specific support-descent
  step that `Issue94SupportDescentAdapter.p2LongUnique_of_p2PrimSupportDescentStep`
  consumes;
* `p2LongUnique_of_component_witness` produces `P2LongUnique L`, the exact long
  uniqueness hypothesis that `Issue94Interface.population_unique_ML_of_long_unique`
  consumes.

## The witness

`hantider` packages, for every genome length `K ≥ L`, every `P2` primitive
word `W`, every `EulerianCycle σ`, and every interlace chord `c`, the existence
of a permutation `g` satisfying the three concrete component lemmas:

1. **switch-product equality** — the component switch is the `g`-conjugate
   successor, `componentSwitch … x = g⁻¹ (nextPos (g (prevPos x)))`;
2. **residual commutation** — `g` commutes with the component residual,
   `g (componentResidual … x) = componentResidual … (g x)`;
3. **vtx preservation** — `vtx hK L W (g x) = vtx hK L W x`.

These three are the route's own inputs, proved by the concrete
interval-product antiderivative (`Issue94ComponentSwitchProduct`,
`Issue94ComponentResidualCommute`, `Issue94ComponentAntiderivativeVtx`);
this module does **not** prove them, it consumes them.  The descent step is
the already-proved `Issue94P2SupportDescent.support_descent_step_of_P2Prim`,
and the bridge to `P2LongUnique` is the already-proved
`Issue94SupportDescentAdapter.p2LongUnique_of_p2PrimSupportDescentStep`.

The witness's primitivity is stated in the route's own
`RepeatAdapter.IsPrimitive` sense; the interface's
`PopulationReduction.IsPrimitive` (carried by `P2PrimSupportDescentStep`) is
converted by `IsPrimitive.shiftPrimitive`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`, and no
change to any existing definition.
-/

namespace AssemblyP1.Issue94FinalAdapter

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94SupportDescent
open AssemblyP1.Issue94PhysicalChord
open AssemblyP1.Issue94ComponentResidual
open AssemblyP1.Issue94ComponentDeleteEulerian
open AssemblyP1.Issue94P2SupportDescent
open AssemblyP1.Issue94SupportDescentAdapter
open AssemblyP1.Issue94Interface
open AssemblyP1.P2RepeatResidual

variable {α : Type} [DecidableEq α] [Fintype α] {L : ℕ}

theorem p2PrimSupportDescentStep_of_component_witness (hL : 2 ≤ L)
    (hantider :
      ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α) (hLK : L ≤ K) (hP2 : P2 hK L W)
        (hprim : RepeatAdapter.IsPrimitive hK W) (sigma : Fin K ≃ Fin K)
        (hEul : EulerianCycle hK L W sigma),
        ∀ c : AltFChord hK sigma,
          ∃ g : Fin K ≃ Fin K,
            (∀ x : Fin K,
              componentSwitch hK W sigma hEul hL hLK hprim hP2 c x
                = g.symm (nextPos hK (g (prevPos hK x)))) ∧
            (∀ x : Fin K,
              g (componentResidual hK W sigma hEul hL hLK hprim hP2 c x)
                = componentResidual hK W sigma hEul hL hLK hprim hP2 c (g x)) ∧
            (∀ x : Fin K, vtx hK L W (g x) = vtx hK L W x)) :
    P2PrimSupportDescentStep (α := α) L := by
  intro K hK W hLK hP2 hprim σ hEul hpos
  exact support_descent_step_of_P2Prim hK hL hLK W
    (IsPrimitive.shiftPrimitive hK hprim) hP2 σ hEul hpos
    (fun c => hantider K hK W hLK hP2 (IsPrimitive.shiftPrimitive hK hprim) σ hEul c)

theorem p2LongUnique_of_component_witness (hL : 2 ≤ L)
    (hantider :
      ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α) (hLK : L ≤ K) (hP2 : P2 hK L W)
        (hprim : RepeatAdapter.IsPrimitive hK W) (sigma : Fin K ≃ Fin K)
        (hEul : EulerianCycle hK L W sigma),
        ∀ c : AltFChord hK sigma,
          ∃ g : Fin K ≃ Fin K,
            (∀ x : Fin K,
              componentSwitch hK W sigma hEul hL hLK hprim hP2 c x
                = g.symm (nextPos hK (g (prevPos hK x)))) ∧
            (∀ x : Fin K,
              g (componentResidual hK W sigma hEul hL hLK hprim hP2 c x)
                = componentResidual hK W sigma hEul hL hLK hprim hP2 c (g x)) ∧
            (∀ x : Fin K, vtx hK L W (g x) = vtx hK L W x)) :
    P2LongUnique (α := α) L :=
  p2LongUnique_of_p2PrimSupportDescentStep hL
    (p2PrimSupportDescentStep_of_component_witness hL hantider)

end AssemblyP1.Issue94FinalAdapter
