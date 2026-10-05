import AssemblyP1

/-!
# Board 94 front 94a401 --- independent trust audit of the assembled `#89` work

This file is **audit scaffolding, not library content**.  It is not imported by
`AssemblyP1.lean` and adds no declaration to the library.  Everything below is
either an axiom report, a kernel-checked refutation of a *documentation*
sentence, or a non-vacuity witness.
-/

set_option maxHeartbeats 1000000

open AssemblyP1 AssemblyP1.PopulationReduction AssemblyP1.SourceFaithfulIs
open AssemblyP1.P2RepeatResidual

/-! ## 1. Axiom audit.  The theorems the tree presents as the `#89` results. -/

-- The word-level coalescence theorem: the closest thing to `#89`'s core.
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_general
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_alpha
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_bin
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce
#print axioms AssemblyP1.Issue94CaseSplit.crossingPairsCoalesce_of_noCollision
#print axioms AssemblyP1.Issue94HeadCollision.head_collision_implies_sameExtension
#print axioms AssemblyP1.Issue94NoCollision.no_collision_contradiction
#print axioms AssemblyP1.Issue94NoCollisionAlpha.no_collision_contradiction_alpha

-- The Eulerian-level characterisation of the block hypothesis.
#print axioms AssemblyP1.Issue94CrossingChords.CrossingChordsCoalesce_ge2
#print axioms AssemblyP1.Issue94CrossingChords.crossingChordsCoalesce_sharp_bin
#print axioms AssemblyP1.Issue94CrossingChords.crossingChordsCoalesce_refuted
#print axioms AssemblyP1.Issue94TW4Coalesce.not_crossingChordsCoalesce_one

-- The public endpoint, and the surrogate it still carries.
#print axioms AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation
#print axioms AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation_same_length
#print axioms AssemblyP1.PopulationUniqueness.population_tie_implies_rotation
#print axioms AssemblyP1.BBTEulerian.bbtUniqueAt_of_obstruction

-- The refutations the tree presents as settled.
#print axioms AssemblyP1.Issue89GapMap.SlidePreservesInterleaved_refuted
#print axioms AssemblyP1.Issue89GapMap.ShiftLeftPersistence_refuted
#print axioms AssemblyP1.Issue94Step4Prop.not_Step4_slide_iterates_1
#print axioms AssemblyP1.Issue94Step4Prop.step4_guarded
#print axioms AssemblyP1.Issue94Step2Path.step2_components_are_paths_proved
#print axioms AssemblyP1.Issue94Step5Heads.not_Step5_heads_interleave_3
#print axioms AssemblyP1.Issue94WitnessPair.no_foreign_eulerianCycle_Fin2_K5
#print axioms AssemblyP1.Issue94WitnessPair.cex_no_chord
#print axioms AssemblyP1.Issue94WitnessPair.cex_no_interlaced_pair
#print axioms AssemblyP1.Issue94WitnessPair.cex_not_vertexCycleEq
#print axioms AssemblyP1.Issue94TW7AltF.not_ukk_then_not_altF
#print axioms AssemblyP1.Issue94IterSlide.slide_one
#print axioms AssemblyP1.Issue89GapMap.step3_slides_meet_no_foreign_chord

/-! ## 2. The documentation sentence that is kernel-checkably false.

`AssemblyP1/BBTLadder.lean:622-624` says the word-level theorem
`BBTCrossingCoalesce.CrossingPairsCoalesce` "implies this one [`BBTLadder.
CrossingChordsCoalesce`] outright".  It does not: `CrossingPairsCoalesce` is
phrased under `2 ≤ L`, while the `BBTLadder` `def` carries no bound on `L` at
all, and at `L = 1` the `def` is refuted.  Witness: `CrossingPairsCoalesce 1`
holds (its `2 ≤ L` hypothesis is false, so the `∀` is vacuous --- *that* is why
the sentence cannot be repaired by pointing at a special case) while
`BBTLadder.CrossingChordsCoalesce (α := Fin 2) 1` is refuted. -/

theorem audit_wordLevel_does_not_imply_unbounded :
    BBTCrossingCoalesce.CrossingPairsCoalesce (α := Fin 2) 1 ∧
    ¬ (∀ L : ℕ, BBTLadder.CrossingChordsCoalesce (α := Fin 2) L) :=
  ⟨Issue94CaseSplit.crossingPairsCoalesce_general (α := Fin 2) 1,
   Issue94CrossingChords.crossingChordsCoalesce_refuted⟩

/-! ## 3. Non-vacuity of the closest-to-final theorem.

`crossingPairsCoalesce_general` is a `∀` over genomes; a theorem with no
inhabitant of its hypothesis set would be a claim in name only.  Here is an
explicit inhabitant: the repository's own primitive `P2` witness `AABAB` on
five positions at `L = 3`, with the chords `{1,3}` and `{2,4}`. -/

open AssemblyP1.Issue94Step5Heads

/-- `AABAB` on five positions: the repository's own `cexWord`, quoted
unchanged, is **primitive** --- kernel-checked at
`P2RepeatResidual.cex_is_shiftPrimitive`. -/
theorem auditWord_primitive : RepeatAdapter.IsPrimitive five headWord :=
  headWord_primitive

/-- ... and satisfies genuine `P2` at `L = 3` (`P2RepeatResidual.cex_is_p2`),
so the hypothesis set of the closest-to-final theorem is inhabited by
something the repository already exhibits. -/
theorem auditWord_P2 : P2 five 3 headWord := headWord_is_p2

open AssemblyP1.BBTLadder AssemblyP1.BBTSequenceGraph

/-- The chords `{1,3}` and `{2,4}` really are distinct chords of `AABAB` at
`L = 3` (`vtx` is the `2`-mer), and they interleave.  So the hypothesis set of
`crossingPairsCoalesce_alpha` has a concrete, non-vacuous inhabitant. -/
theorem audit_vtx13 :
    vtx five 3 headWord (1 : Fin 5) = vtx five 3 headWord (3 : Fin 5) := by decide

theorem audit_vtx24 :
    vtx five 3 headWord (2 : Fin 5) = vtx five 3 headWord (4 : Fin 5) := by decide

theorem audit_interleaved :
    Interleaved (mkGenome five headWord) (1 : Fin 5) (3 : Fin 5) (2 : Fin 5) (4 : Fin 5) :=
  by decide

/-- ... and on that concrete instance the theorem delivers the real conclusion,
`SameExtension`, not a vacuous one. -/
theorem audit_hab : ¬ ((1 : Fin 5) = 3) := by decide

theorem audit_hcd : ¬ ((2 : Fin 5) = 4) := by decide

theorem audit_instance_conclusion :
    SameExtension 5 five headWord (1 : Fin 5) (3 : Fin 5) (2 : Fin 5) (4 : Fin 5) :=
  Issue94CaseSplit.crossingPairsCoalesce_alpha five headWord
    (by norm_num) (by norm_num) auditWord_P2 auditWord_primitive
    audit_hab audit_hcd audit_vtx13 audit_vtx24 audit_interleaved

/-- **The collision branch of the case split is genuinely live on this
instance**, not vacuous: the four heads are `1, 3, 1, 3`, so the first
disjunct of `hcoll` holds by `rfl` and
`Issue94HeadCollision.head_collision_implies_sameExtension` really does the
work.  (Values: `Issue94Step5Heads.head_cex_mps13/24/31/42`, all `by decide`
on the computable `pairBackC`.) -/
theorem audit_collision_branch_is_live :
    maxPairStart five headWord (1 : Fin 5) (3 : Fin 5)
        = maxPairStart five headWord (2 : Fin 5) (4 : Fin 5) ∨
    maxPairStart five headWord (1 : Fin 5) (3 : Fin 5)
        = maxPairStart five headWord (4 : Fin 5) (2 : Fin 5) ∨
    maxPairStart five headWord (3 : Fin 5) (1 : Fin 5)
        = maxPairStart five headWord (2 : Fin 5) (4 : Fin 5) ∨
    maxPairStart five headWord (3 : Fin 5) (1 : Fin 5)
        = maxPairStart five headWord (4 : Fin 5) (2 : Fin 5) :=
  Or.inl (head_cex_mps13.trans head_cex_mps24.symm)