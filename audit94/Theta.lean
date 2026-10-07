import AssemblyP1

/-!
# Board 94 recovery front --- is `Issue94EulerianTheta` proved or admitted?

Every declaration of `AssemblyP1.Issue94EulerianTheta` is listed below.  If any
of them reported a user axiom, the "quarantine lifted" claim of commit a91a01e
would be a lie.  There is deliberately no `axiom`, `sorry`, `admit`,
`native_decide` or linter suppression in this file.
-/

set_option maxHeartbeats 1000000

#print axioms AssemblyP1.Issue94EulerianTheta.theta_of_same_spectrum_is_one_cycle
#print axioms AssemblyP1.Issue94EulerianTheta.window_rotAdd_refuted
#print axioms AssemblyP1.Issue94EulerianTheta.vtx_rotAdd_refuted
#print axioms AssemblyP1.Issue94EulerianTheta.vertexCycleEq_of_isRotation
#print axioms AssemblyP1.Issue94EulerianTheta.vertexCycleEq_of_isRotation_pullback
#print axioms AssemblyP1.Issue94EulerianTheta.badTheta_of_not_RotEquiv
#print axioms AssemblyP1.Issue94EulerianTheta.window_rotEquiv
#print axioms AssemblyP1.Issue94EulerianTheta.vertexCycleEq_of_RotEquiv_pullback
#print axioms AssemblyP1.Issue94EulerianTheta.step2_unrestricted_refuted
#print axioms AssemblyP1.Issue94EulerianTheta.specCount_eq_of_Matching
#print axioms AssemblyP1.Issue94EulerianTheta.bbt_of_badThetaObstruction
#print axioms AssemblyP1.Issue94EulerianTheta.badThetaObstruction_of_bbt

/-! ## The endpoint's real dependency is a *hypothesis*, not an axiom.

`EulerianCycleObstruction` and `UniqueEulerianCycle` are `def`s (Props) with no
inhabitants anywhere in the library.  So the endpoint theorem is a genuine
conditional and the logic is clean --- but the published problem is still
unsettled, because the hypothesis is not discharged.  Below: the two `def`s are
provably equivalent (so they are interchangeable statements of the SAME open
obligation), and neither is provable from what the tree has. -/

open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.P2

/-! ## The two residual `Prop`s are interchangeable, kernel-checked.

`EulerianCycleObstruction` and `UniqueEulerianCycle` are `def`s, not axioms,
and they are the same open statement up to the proved `Ukkonen` exclusion of
the long-obstruction branch.  Renaming the endpoint's hypothesis buys no
mathematics. -/
open AssemblyP1.BBTEulerian

theorem T_ECO_iff_UEC {α : Type} [DecidableEq α] (L : ℕ) :
    (EulerianCycleObstruction (α := α) L → UniqueEulerianCycle (α := α) L) ∧
    (UniqueEulerianCycle (α := α) L → EulerianCycleObstruction (α := α) L) :=
  ⟨uniqueEulerianCycle_of_obstruction, obstruction_of_uniqueEulerianCycle⟩
