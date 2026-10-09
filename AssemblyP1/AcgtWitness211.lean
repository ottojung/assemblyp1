import AssemblyP1.SourceFaithfulIs
import AssemblyP1.SameLength62Maximizer
import AssemblyP1.OrientedSameLengthML
import AssemblyP1.OrientedRigidity

/-!
# Independent review witness for #211: `I_s` does not imply the truth is a genuine §6.2 candidate

Concrete instance (review hypothesis):

* truth `S = ACGT`, `G = 4`, read length `L = 3`;
* realization `rho4`: two reads, at starts `0` and `2`;
* realized start set `R = {0, 2}`.

Kernel-checked findings:

1. `InformationFeasible ⟨4, hG4, S4⟩ 3 (realizedStarts rho4)` holds
   (`acgt4_information_feasible`): coverage holds and there are no repeats at
   every length `1 ≤ e < 4` (all windows of `ACGT` are distinct), so the
   bridging clauses are vacuous.
2. The genomic `3`-mers of the truth are `ACG, CGT, GTA, TAC`, but only `ACG`
   (start `0`) and `GTA` (start `2`) are observed; `CGT` (start `1`) and `TAC`
   (start `3`) are never observed.
3. Consequently the truth's window support is strictly larger than the observed
   read set, so by the proved bridge `SameLength62Maximizer.genuine62_support_eq`
   the truth is **not** a genuine §6.2 candidate for the observed read set
   (`acgt4_not_candidate`): the bridge forces a genuine candidate's window
   support to equal `ObservedTypes verts` exactly, and the necessary condition
   fails at the unobserved `3`-mer `CGT`.

So the `hStruth` hypothesis of the #211 uniqueness/maximizer theorems can fail
even when full source-faithful `I_s` holds: `I_s` (coverage + bridging) does
not force the truth's complete genomic `L`-mer support to be observed.
-/

namespace AssemblyP1.AcgtWitness211

open SourceFaithfulIs
open AssemblyP1.SameLength62Maximizer
open AssemblyP1.OrientedSameLengthML
open AssemblyP1.OrientedRigidity

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-- `G = 4`. -/
private theorem hG4 : 0 < 4 := by norm_num

/-- The truth `ACGT` as a length-`4` circular word over `Fin 4` (`A=0, C=1, G=2, T=3`). -/
def S4 : Fin 4 → Fin 4 := ![0, 1, 2, 3]

/-- The realization: two reads, at starts `0` and `2`. -/
def rho4 : Realization 4 2 := ![0, 2]

/-- The observed read set (the `verts` a realization gives for free). -/
def verts4 : List (Fin 3 → Fin 4) := [![0, 1, 2], ![2, 3, 0]]

/-- **The witness instance is fully information-feasible (`I_s` holds).**
Kernel-checked on the source-faithful `InformationFeasible`. -/
theorem acgt4_information_feasible :
    InformationFeasible ⟨4, hG4, S4⟩ 3 (realizedStarts rho4) := by
  decide

/-- The truth's window at start `1` is the `3`-mer `CGT`, which is never observed. -/
theorem acgt4_window1_cgt :
    (⟨4, hG4, S4⟩ : Genome (Fin 4)).window 3 ⟨1, by norm_num⟩ = ![1, 2, 3] := by
  funext d
  fin_cases d <;> decide

/-- `CGT` is not an observed read type. -/
theorem acgt4_cgt_not_observed :
    ![1, 2, 3] ∉ SameLength62Maximizer.ObservedTypes verts4 := by
  decide

/-- The truth is **not** a genuine §6.2 candidate for the observed read set,
even though the instance is fully `I_s`-feasible.

`SameLength62Maximizer.genuine62_support_eq` (a proved bridge) forces a genuine
candidate's window support to equal `ObservedTypes verts` exactly; here the
truth's support contains the unobserved `3`-mer `CGT`, so the necessary
condition fails at `w = CGT`. -/
theorem acgt4_not_candidate :
    ¬ SameLength62Maximizer.Is62Candidate62 ⟨4, hG4, S4⟩ verts4
      (fun w => List.ofFn w) (fun y => y) (fun y => y) 1 := by
  intro hC
  have hsup := SameLength62Maximizer.genuine62_support_eq (L := 3) hC ![1, 2, 3]
  exact acgt4_cgt_not_observed (hsup.mp ⟨⟨1, by norm_num⟩, acgt4_window1_cgt⟩)

end

end AssemblyP1.AcgtWitness211
