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

/-! ## M1. `crossingPairsCoalesce_alpha` with `hP2` dropped.

`P2` supplies the three-occurrences property `P2.imp_ExtCrossing` needs to
forbid the interleaving heads.  Without it the statement is false. -/
theorem M1_drop_hP2 {α : Type} [DecidableEq α] {K L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_alpha hK S h2L hLK hprim hab hcd hvab hvcd hI

/-! ## M2. `crossingPairsCoalesce_alpha` with `hI`, the interleaving
hypothesis, dropped.  This is the premise the whole `#89` route rests on. -/
theorem M2_drop_hI {α : Type} [DecidableEq α] {K L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI

/-! ## M3. `crossingPairsCoalesce_alpha` with `hprim` dropped.  Primitivity
is what makes `maxPairStart` a *maximal* extension at all; without it the
determinism argument has no anchor. -/
theorem M3_drop_hprim {α : Type} [DecidableEq α] {K L : ℕ}
    (hK : 0 < K) (S : Fin K → α) (h2L : 2 ≤ L) (hLK : L ≤ K)
    (hP2 : P2 hK L S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b) (hvcd : vtx hK L S c = vtx hK L S d)
    (hI : Interleaved (mkGenome hK S) a b c d) :
    SameExtension K hK S a b c d :=
  crossingPairsCoalesce_alpha hK S h2L hLK hP2 hprim hab hcd hvab hvcd hI

/-! ## M4. The collision branch with its `hcoll` disjunct *weakened to a
single orientation*.  `head_collision_implies_sameExtension` needs one of four
head collisions; keeping only `maxPairStart a b = maxPairStart c d` must be
insufficient, since the library theorem genuinely uses the four-way split. -/
theorem M4_weaken_hcoll_to_one {K L : ℕ} {α : Type} [DecidableEq α]
    (hK : 0 < K) (S : Fin K → α) (hL : 2 ≤ L) (hLG : L ≤ K)
    (hP2 : P2 hK L S) (hprim : RepeatAdapter.IsPrimitive hK S) {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hagab : ∀ t : Fin (L - 1), cyc hK S (a.val + t.val) = cyc hK S (b.val + t.val))
    (hagcd : ∀ t : Fin (L - 1), cyc hK S (c.val + t.val) = cyc hK S (d.val + t.val))
    (hcoll : maxPairStart hK S a b = maxPairStart hK S c d) :
    SameExtension K hK S a b c d :=
  head_collision_implies_sameExtension hK S hL hLG hP2 hprim hab hcd hagab hagcd
    (Or.inl hcoll)

/-! ## M5. The `2 ≤ L` side condition of `CrossingChordsCoalesce_ge2` is
load-bearing, exactly as `crossingChordsCoalesce_refuted` says: the same
statement at `L = 1` is refuted over `Fin 2`.  So the strengthened form, with
`2 ≤ L` removed from the *statement*, must fail. -/
theorem M5_weaken_2_le {α : Type} [DecidableEq α] (L : ℕ) (hL : 2 ≤ L) :
    ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (P2 hK L S)
      (_hprim : RepeatAdapter.IsPrimitive hK S) (_hUkk : Ukkonen hK L S) (_hLG : L ≤ K)
      (σ : Fin K ≃ Fin K) (EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d :=
  AssemblyP1.Issue94CrossingChords.CrossingChordsCoalesce_ge2 (α := α) L hL

/-! ## M6. The endpoint.  `population_unique_ML_up_to_rotation` is claimed to
be *conditional* on `EulerianCycleObstruction`.  The honest statement is that
the theorem is `EulerianCycleObstruction → (maximizer ∧ uniqueness)`.  Mutating
it to drop the `hPevzner` binder must fail: that would be the published open
problem. -/
theorem M6_drop_hPevzner (L : ℕ) (hG : 0 < 1) (hL : 1 < L)
    (S : Fin 1 → AssemblyP1.PopulationReduction.Bin) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → AssemblyP1.PopulationReduction.Bin),
        AssemblyP1.PopulationUniqueness.AdmClass L hK W →
        AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S)
            (AssemblyP1.PopulationUniqueness.popSpectrum L hK W)
          ≤ AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S)
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → AssemblyP1.PopulationReduction.Bin),
        AssemblyP1.PopulationUniqueness.AdmClass L hK W →
        AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S)
            (AssemblyP1.PopulationUniqueness.popSpectrum L hK W)
          = AssemblyP1.PopulationGibbs.PopLogLik
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S)
            (AssemblyP1.PopulationUniqueness.popSpectrum L hG S) →
        ∃ hGK : 1 = K, AssemblyP1.PopulationReduction.RotEquiv hG (hGK ▸ W) S)) :=
  AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation
    L hG hL S (by decide) (by decide)