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

/-! ## M5. The `2 ≤ L` side condition of `CrossingChordsCoalesce_ge2` is
load-bearing, exactly as `crossingChordsCoalesce_refuted` says: the same
statement at `L = 1` is refuted over `Fin 2`.  So the strengthened form, with
`2 ≤ L` removed from the *statement*, must fail.  The statement below is copied
verbatim from `AssemblyP1/Issue94CrossingChords.lean:454-462` with `hL`
dropped. -/
theorem M5_weaken_2_le {α : Type} [DecidableEq α] (L : ℕ) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
      (_hprim : RepeatAdapter.IsPrimitive hK S) (_hLG : L ≤ K) (_hUkk : Ukkonen hK L S)
      (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d :=
  AssemblyP1.Issue94CrossingChords.CrossingChordsCoalesce_ge2 (α := α) L (by omega)
