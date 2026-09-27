import AssemblyP1.P2
import AssemblyP1.BridgingBridge
import AssemblyP1.RepeatAdapter

/-!
# P2 to RepeatAdapter bridge for issue #89

This file connects the source-faithful `P2` triple-repeat clause to the older
`RepeatAdapter.HasLongTripleRepeat` interface. The latter is the hypothesis
used by the kernel-checked two-sided three-copy extension theorem
`RepeatAdapter.primitive_nodeCount_le_two`.

No new repeat notion is introduced here: `BridgingBridge.isTripleRepeat_of_maximalTriple`
converts the natural-number-start representation used by `RepeatAdapter` into
the exact `SourceFaithfulIs.Genome.IsTripleRepeat` predicate used by `P2`.
-/

namespace AssemblyP1.P2

open SourceFaithfulIs

/-- **P2 excludes the RepeatAdapter long-triple interface.**

For `L ≥ 2`, any `RepeatAdapter.HasLongTripleRepeat` witness has length
`ℓ ≥ L - 1`. `BridgingBridge.isTripleRepeat_of_maximalTriple` turns that
same witness into a source-faithful maximal triple repeat of `mkGenome hG S`,
while `P2.triple` says every such repeat has length strictly below
`L - 1`. -/
theorem noLongTripleRepeat {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (hL : 2 ≤ L) (S : Fin G → α)
    (hP2 : AssemblyP1.P2 hG L S) :
    ¬ RepeatAdapter.HasLongTripleRepeat hG S L := by
  rintro ⟨a, b, c, ℓ, hlong, hℓG, hab, hbc, hac, hmax⟩
  have h1 : 1 ≤ ℓ := by omega
  rcases hmax with ⟨hag, hpre, hfol⟩
  have ht := BridgingBridge.isTripleRepeat_of_maximalTriple
    (S := mkGenome hG S) h1 hℓG hab hac hbc hag hpre hfol
  have hlt : ℓ < L - 1 := by
    exact AssemblyP1.P2.triple hG hP2 (e := ⟨ℓ, hℓG⟩) ht
  omega

end AssemblyP1.P2
