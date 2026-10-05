import AssemblyP1

/-!
# Board 94 recovery front --- mutations proving the `#89` assertions are
load-bearing.

Every declaration in this file is **expected to FAIL**.  Each one restates a
closest-to-final theorem over the same hypotheses with exactly one ingredient
removed, weakened or replaced.  If any compiled, the corresponding library
assertion would be decoration.

Corrections over the dead front 94a401's copy, all forced by execution:
the original never elaborated, so its "red" was partly typos (`cyc` and
`maxPairStart` unqualified, `hI` out of scope, `2 ≤` parsed as a binder) and
proved nothing.  Each mutation below now reddens for a *mathematical* reason
only.  No `sorry`, no `admit`, no `axiom`, no `native_decide`.
-/

set_option maxHeartbeats 1000000

open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.RepeatAdapter
open AssemblyP1.BBTLadder
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.P2
open AssemblyP1.Issue94CaseSplit
open AssemblyP1.Issue94HeadCollision
open AssemblyP1.Issue94NoCollision
open AssemblyP1.P2RepeatResidual

/-! M2. `crossingPairsCoalesce_alpha` with `hI`, the interleaving
hypothesis, dropped.  This is the premise the whole `#89` route rests on. -/
theorem M2_drop_hI {α : Type} [DecidableEq α] {K L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI

