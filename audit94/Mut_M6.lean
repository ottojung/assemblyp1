import AssemblyP1

set_option maxHeartbeats 1000000

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.RepeatAdapter
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.P2
open AssemblyP1.P2RepeatResidual
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94CaseSplit
open AssemblyP1.Issue94Step5Heads

/-! ## M6. The endpoint, on an INHABITED hypothesis set.

`population_unique_ML_up_to_rotation_same_length` is conditional on
`EulerianCycleObstruction`.  Dropping the `hPevzner` binder must fail: that
would be the published open problem.

The slice is the repository's own primitive `P2` witness `headWord` (`AABAB`)
at `G = 5`, `L = 3`, so the hypothesis set is INHABITED
(`Issue94Step5Heads.headWord_is_p2`, `headWord_primitive`, both proved).  A
successful compile here would not be vacuity: it would be a proof of the
endpoint for a genuine word. -/
theorem M6_drop_hPevzner (hPrim : AssemblyP1.PopulationReduction.IsPrimitive headWord) :
    ∀ E : Fin 5 → AssemblyP1.PopulationReduction.Bin,
        AssemblyP1.PopulationUniqueness.AdmClass 3 (by decide) E →
        AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum 3 (by decide) headWord)
            (AssemblyP1.PopulationUniqueness.popSpectrum 3 (by decide) E)
          = AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum 3 (by decide) headWord)
            (AssemblyP1.PopulationUniqueness.popSpectrum 3 (by decide) headWord) →
        AssemblyP1.PopulationReduction.RotEquiv (by decide) E headWord :=
  AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation_same_length
    3 (by decide) (by norm_num) headWord hPrim headWord_is_p2
