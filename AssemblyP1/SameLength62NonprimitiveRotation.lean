import AssemblyP1.SameLength62Maximizer
import AssemblyP1.CycleSpellingRotation
import AssemblyP1.RepeatAdapter
import AssemblyP1.BridgingBridge

/-!
# Board #245: nonprimitive same-length §6.2 rotation uniqueness without `hStruth`

This module proves the **nonprimitive** half of the same-length §6.2 rotation
uniqueness statement **without** the truth's own genuine §6.2 certificate
(`hStruth`). The conditional #211 theorem
(`SameLength62Uniqueness.unique_62_maximizer_up_to_rotation`, PR #124 head
`5b24e5e`, not yet merged) carries `hStruth` as a hypothesis.

## The gap in #211, and how this module closes it

#211's nonprimitive branch obtains `support D = support S` from the §6.2 bridge
`oriented_support_eq_of_genuine62`, which consumes **both** the truth's and the
candidate's genuine certificates. The truth's certificate `hStruth` is a
nontrivial extra hypothesis: it asserts the truth has complete observed
support, which is not automatic from `I_s` alone.

The #243 rotation lemma `isCyclicShift_of_isSimpleCycle_support_subset` only
needs the **one-way** inclusion `support D ⊆ support S`. This module derives
that inclusion from the candidate's certificate plus **provenance** — the fact
that the §6.2 vertex list `verts` was produced by the realization `ρ` on the
truth `S` — with no certificate for the truth:

* `Is62Candidate62 D` gives `support D ⊆ ObservedTypes verts`, the forward
  direction of the §6.2 bridge `genuine62_support_eq` (a candidate's window
  support is exactly the observed read set);
* provenance gives `ObservedTypes verts ⊆ support S`: every vertex was
  actually observed in `ρ` on `S` (`hverts`), hence is a window of `S` by
  `observedOf_mem_support`.

Chaining the two gives `support D ⊆ support S`. The nonprimitive route then
produces `IsSimpleCycle S` from `I_s` and nonprimitivity
(`RepeatAdapter.periodic_factor_distinct` + `RepeatAdapter.periodic_cycle_shape`
fed by `BridgingBridge.informationFeasible_no_long_triple_repeat`), and the #243
lemma concludes `OrientedFinal.IsCyclicShift hG D S`.

## Assumptions, stated accurately

* **Nonprimitive only.** The hypothesis is `¬ RepeatAdapter.IsPrimitive hG S`,
  the shift-invariance form consumed directly by
  `RepeatAdapter.primitive_or_minimal_period`. The primitive branch is **not**
  claimed: it needs spectrum equality (equivalently `hStruth`), exactly as in
  #211. This module does not settle the primitive case and does not claim all
  maximum-likelihood cases are solved.
* **No `L ≤ G`.** The nonprimitive route does not consume the read-length
  bound, so it is not assumed here. (`I_s` itself remains the source-faithful
  hypothesis.)
* The provenance hypothesis `hverts` is a real hypothesis, and it is
  **one-way**: every §6.2 vertex was observed in `ρ` on `S`. It does *not*
  assert that `verts` is exactly the observed read-type set (that would be the
  converse, plus list-level accounting); it is the direction the support
  inclusion consumes. It is the natural "the observed reads came from the
  truth" statement, not a formality.
* **Rotation uniqueness only, not maximum likelihood.** The candidate `D` is
  assumed to be a genuine same-length §6.2 candidate (`Is62Candidate62`), not a
  likelihood maximizer. The theorem concludes only that `D` is a cyclic shift
  of `S`; it makes no claim that `D` maximises the same-length likelihood. The
  maximizer statement is `SameLength62Maximizer.informationFeasible_62_maximizer`,
  and any "the ML maximizer is the truth up to rotation" reading needs the
  maximizer-membership fact supplied separately.
* No `sorry`, no new `axiom`.
-/

namespace AssemblyP1.SameLength62NonprimitiveRotation

open AssemblyP1.OrientedSameLengthML
open AssemblyP1.OrientedRigidity
open AssemblyP1.SourceFaithfulIs

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. The support inclusion from provenance -/

/-- **Provenance gives `support D ⊆ support S`.** The candidate's genuine §6.2
certificate puts its window support inside the observed read set (the forward
direction of `genuine62_support_eq`); provenance — every §6.2 vertex was
actually observed in the realization `ρ` on the truth `S` — puts the observed
read set inside the truth's window support (`observedOf_mem_support`). -/
theorem support_subset_of_provenance {G L n : ℕ} (hG : 0 < G)
    (S : Fin G → α) (ρ : Realization G n)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hverts : ∀ w, w ∈ verts → 0 < observedOf (L := L) hG S ρ w)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    ∀ w : Fin L → α, w ∈ OrientedRigidity.support (L := L) hG D
      → w ∈ OrientedRigidity.support (L := L) hG S := by
  intro w hw
  have hwv : w ∈ SameLength62Maximizer.ObservedTypes verts := by
    refine (SameLength62Maximizer.genuine62_support_eq (L := L) (toList := toList)
      hD w).mp ?_
    obtain ⟨r, _, hrw⟩ := Finset.mem_image.mp hw
    exact ⟨r, hrw⟩
  have hmem : w ∈ verts := List.mem_toFinset.mp hwv
  exact observedOf_mem_support hG S ρ w (hverts w hmem)

/-! ## 2. The nonprimitive rotation theorem -/

/-- **Board #245: a nonprimitive truth's genuine same-length §6.2 candidates are
cyclic shifts of the truth, without `hStruth`.** Let `S` be a nonprimitive
circular word of length `G`, `ρ` a realization of `n` reads on `S`, and `I_s`
hold at the realized starts. Suppose every vertex of the §6.2 vertex list
`verts` was observed in `ρ` on `S` (the one-way provenance `hverts`), and let
`D` be a genuine same-length §6.2 candidate for `verts`. Then `D` is a cyclic
rotation of `S`.

This is a **rotation-uniqueness** statement about genuine §6.2 candidates, not
a maximum-likelihood statement: `hD` gives membership in the §6.2 candidate
class, not likelihood optimality, and the conclusion is only `IsCyclicShift`.
The truth's own certificate `hStruth` is **not** consumed; the one-way support
inclusion `support D ⊆ support S` needed by the #243 rotation lemma comes from
`hD` plus provenance (`support_subset_of_provenance`), and `IsSimpleCycle S`
comes from `I_s` plus nonprimitivity.

The primitive branch is deliberately not claimed here: without `hStruth` the
spectrum equality it needs is unavailable, so this theorem settles only the
nonprimitive case. -/
theorem candidate_isCyclicShift_of_nonprimitive_I_s {G L n : ℕ} (hG : 0 < G)
    (hL2 : 2 ≤ L) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    (hnp : ¬ RepeatAdapter.IsPrimitive hG S)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hverts : ∀ w, w ∈ verts → 0 < observedOf (L := L) hG S ρ w)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    OrientedFinal.IsCyclicShift hG D S := by
  have hsub := support_subset_of_provenance hG S ρ hverts D hD
  have hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L :=
    BridgingBridge.informationFeasible_no_long_triple_repeat hL2 hfeas
  rcases RepeatAdapter.primitive_or_minimal_period hG S with hprim' | ⟨p, hp⟩
  · exact absurd hprim' hnp
  · have hNwin : ∀ i j : ℕ, i < p → j < p →
        (∀ d : ℕ, d < L - 1 → OrientedRigidity.cyc hG S (i + d)
          = OrientedRigidity.cyc hG S (j + d)) → i = j :=
      RepeatAdapter.periodic_factor_distinct hG S p hL2 hp hno
    obtain ⟨hp0, hpG, _hGp, hper, _hsmall⟩ := hp
    have hcyc := RepeatAdapter.periodic_cycle_shape hG S p hp0
      (le_of_lt hpG) hper hNwin
    exact CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_support_subset
      hG hL2 S D hsub hcyc

end

#print axioms support_subset_of_provenance
#print axioms candidate_isCyclicShift_of_nonprimitive_I_s

end AssemblyP1.SameLength62NonprimitiveRotation
