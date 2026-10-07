import AssemblyP1.P2Multiplicity
import AssemblyP1.ScalarPrimitiveSpellings

/-!
# `IsGcdOne` for a primitive `P2` truth: no complete-spectrum uniqueness
# (issue #89, the gcd-one bottleneck)

## The theorem

`gcd_one_of_primitive_P2`:

```text
0 < G          the genome is nonempty
2 ≤ L ≤ G      read length in the admissible range
S : Fin G → α  a circular word
IsPrimitive S  the truth is not an exact nontrivial power
P2 hG L S      the actual P2 of `def:P1P2`
⟹ IsGcdOne (specCount (L := L) hG S)
```

No `hBBT`, no `BBTCompleteSpectrumUniqueness`, no `BBTUniqueAt`, no
opaque `AdmP2`: the only hypotheses are the paper's own primitivity and its
own P2, at `K = L - 1` compatibility (`2 ≤ L ≤ G`).

## The argument

Suppose `g > 1` divides every `L`-mer count.  For `e` in the spectrum
support, `0 < specCount hG S e` and `g ∣ specCount hG S e`, hence
`g ≤ specCount hG S e`, so **every support count is at least `g ≥ 2`**.

The `P2` triple-repeat clause gives the multiplicity cap
`nodeCount (L-1)-mer ≤ 2` (`P2Multiplicity.AssemblyP1.P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive`,
which uses only that clause, through `P2.noLongTripleRepeat`).

Now suppose the spectrum-support graph branches: two distinct support edges
`e₁ ≠ e₂` leave the same node `winPrefix e₁ = winPrefix e₂`.  Their occurrence
sets are disjoint (a start spells one window) and both sit inside the fiber of
that node, so
`nodeCount (winPrefix e₁) ≥ specCount e₁ + specCount e₂ ≥ 2g ≥ 4`, against the
cap `≤ 2`.  So the support is **nonbranching**
(`nonbranching_of_primitive_P2_of_divisible`).

A primitive truth on a nonbranching support has `specCount = 1` on the whole
support, hence gcd one (`ScalarPrimitive.gcdOne_of_nonbranching_primitive`).
`g ∣ 1` forces `g = 1`.

So the two ingredients are both project-side and kernel-checked: the multiplicity
cap (P2 → repeat theory) and the nonbranching-gcd-one consequence
(issue #92's classification).  The complete-spectrum uniqueness of
`thm:BBT` is not used; the fact that makes it unnecessary here is that a
divisible complete spectrum needs multiplicity `≥ 2` on *every* support edge,
which is incompatible with the `≤ 2` per-node cap of a `P2` truth as soon as two
support edges share a node.

## Scope

* The cap needs `2 ≤ L` (read length) and `L ≤ G`, the range in which
  `P2Multiplicity.AssemblyP1.P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive` and the
  admissible-candidate reading of P2 are stated.  `PopulationReduction.gcd_one_of_primitive_P2_words`,
  which replaces this file's theorem by the stronger external route, carries only
  `1 < L`; the new theorem is therefore the honest statement, and
  `population_uniqueness_of_primitive_P2` below re-derives the end-to-end
  population conclusion under the actual `P2` predicate.  Neither this file nor
  the `PopulationReduction.population_uniqueness_of_spectra` it uses mentions
  `AdmP2`, `hBBT`, `BBTUniqueAt` or `BBTCompleteSpectrumUniqueness`.
* Only the *triple-repeat* clause of `P2` is used.  The interleaved-pair clause
  is not needed, and is not claimed to be.
* The regression `PopulationReduction.primitivity_insufficient` still stands:
  primitivity alone does not give gcd one, and it is not contradicted here,
  since it needs P2.
-/

namespace AssemblyP1.P2GcdOne

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.RepeatAdapter
open AssemblyP1.ScalarPrimitive

set_option maxHeartbeats 800000
-- the private occurrence-set helpers genuinely do not need every section instance
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] [Fintype α] {G L : ℕ}

/-! ## Window bookkeeping -/

/-- The length-`(L-1)` prefix of the window read at `r` is the node window at
`r`. -/
theorem winPrefix_window (hG : 0 < G) (S : Fin G → α) (r : Fin G) :
    winPrefix (window (L := L) hG S r : Fin L → α) = nodeWindow (L := L) hG S r := by
  funext d
  rfl

/-- The starts spelling an `L`-mer `w`. -/
private def occL (hG : 0 < G) (S : Fin G → α) (w : Fin L → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => window (L := L) hG S r = w)

/-- The starts spelling an `(L-1)`-mer `k`. -/
private def occN (hG : 0 < G) (S : Fin G → α) (k : Fin (L - 1) → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG S r = k)

private theorem card_occL (hG : 0 < G) (S : Fin G → α) (w : Fin L → α) :
    (occL hG S w).card = specCount (L := L) hG S w := rfl

private theorem card_occN (hG : 0 < G) (S : Fin G → α) (k : Fin (L - 1) → α) :
    (occN hG S k).card = nodeCount (L := L) hG S k := rfl

/-- Every start spelling `w` spells the node `winPrefix w`. -/
private theorem occL_subset_occN (hG : 0 < G) (S : Fin G → α) (w : Fin L → α) :
    occL hG S w ⊆ occN hG S (winPrefix w) := by
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  show nodeWindow (L := L) hG S r = winPrefix w
  rw [← hr'.2, winPrefix_window]

/-- A start spells at most one window, so two distinct windows have disjoint
occurrence sets. -/
private theorem occL_disjoint (hG : 0 < G) (S : Fin G → α) {w₁ w₂ : Fin L → α}
    (hne : w₁ ≠ w₂) : Disjoint (occL hG S w₁) (occL hG S w₂) :=
  Finset.disjoint_left.2 (fun r hr₁ hr₂ => by
    have h₁ : window (L := L) hG S r = w₁ := (Finset.mem_filter.mp hr₁).2
    have h₂ : window (L := L) hG S r = w₂ := (Finset.mem_filter.mp hr₂).2
    exact hne (h₁.symm.trans h₂))

/-- **Two windows out of one node cost two fibers' worth of starts.**  The
multiplicity of a node dominates the sum of the multiplicities of any two
distinct windows whose `L-1`-prefix is that node: their starts are disjoint and
both spell the node. -/
theorem nodeCount_ge_two_specs (hG : 0 < G) (S : Fin G → α) (e₁ e₂ : Fin L → α)
    (hne : e₁ ≠ e₂) (hpre : winPrefix (L := L) e₁ = winPrefix (L := L) e₂) :
    specCount (L := L) hG S e₁ + specCount (L := L) hG S e₂
      ≤ nodeCount (L := L) hG S (winPrefix (L := L) e₁) := by
  have hunion : occL hG S e₁ ∪ occL hG S e₂ ⊆ occN hG S (winPrefix (L := L) e₁) := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact occL_subset_occN hG S e₁ h
    · rw [hpre]; exact occL_subset_occN hG S e₂ h
  have hcard : (occL hG S e₁ ∪ occL hG S e₂).card
      = (occL hG S e₁).card + (occL hG S e₂).card :=
    Finset.card_union_of_disjoint (occL_disjoint hG S hne)
  have hle := Finset.card_le_card hunion
  rw [hcard] at hle
  simpa only [card_occL, card_occN] using hle

/-! ## Divisibility forces a nonbranching support -/

/-- **A primitive `P2` truth whose complete spectrum has a common divisor `> 1`
has a nonbranching support.**  Every support count is then at least `g ≥ 2`,
and two support edges out of one node would spend at least `4` starts in a
fiber that `P2` caps at `2` (`nodeCount_ge_two_specs`). -/
theorem nonbranching_of_primitive_P2_of_divisible (hG : 0 < G) (hL : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hG L S)
    {g : ℕ} (hg1 : g ≠ 1)
    (hg : ∀ w : Fin L → α, g ∣ specCount (L := L) hG S w) :
    NonBranching (genomeNodes (L := L) hG S) (support (L := L) hG S)
      (winPrefix (L := L)) (winSuffix (L := L)) := by
  have hcap : ∀ k : Fin (L - 1) → α, nodeCount (L := L) hG S k ≤ 2 :=
    AssemblyP1.P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive hG hL hLG S hPrim hP2
  -- the common divisor is positive, because a support count is positive
  have hsup := support_ne_nil_of_truth (L := L) (hG := hG) S
  obtain ⟨e₀, he₀⟩ := hsup
  have hpos0 : 0 < specCount (L := L) hG S e₀ := truth_pos_on_support (L := L) hG S e₀ he₀
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with rfl | hp
    · exfalso
      have : specCount (L := L) hG S e₀ = 0 :=
        Nat.eq_zero_of_zero_dvd (hg e₀)
      omega
    · exact hp
  have hlt : 1 < g := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hgpos) (Ne.symm hg1)
  -- every support count is at least `g`
  have hge : ∀ e ∈ support (L := L) hG S, g ≤ specCount (L := L) hG S e := by
    intro e he
    exact Nat.le_of_dvd (truth_pos_on_support (L := L) hG S e he) (hg e)
  intro v e₁ h₁ e₂ h₂ htail htail₂
  by_contra hne
  have hpre : winPrefix (L := L) e₁ = winPrefix (L := L) e₂ :=
    htail.trans htail₂.symm
  have hsum := nodeCount_ge_two_specs hG S e₁ e₂ hne hpre
  have hcapk := hcap (winPrefix (L := L) e₁)
  have h1 := hge e₁ h₁
  have h2 := hge e₂ h₂
  have h4 : 4 ≤ specCount (L := L) hG S e₁ + specCount (L := L) hG S e₂ := by omega
  have : False := by omega
  exact this.elim

/-! ## The gcd-one theorem -/

/-- **Gcd one for a primitive `P2` truth, from actual `P2` and primitivity
alone.**  The complete `L`-spectrum of a primitive `P2` word is gcd one, so the
population reduction's `hGcdS`/`hGcdD` obligations hold with no
complete-spectrum uniqueness premise (`hBBT`), no `BBTUniqueAt` inhabitant and
no opaque `AdmP2`. -/
theorem gcd_one_of_primitive_P2 (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hG L S) :
    IsGcdOne (W := Fin L → α) (specCount (L := L) hG S) := by
  intro g hg
  by_cases hg1 : g = 1
  · exact hg1
  · have hnb := nonbranching_of_primitive_P2_of_divisible hG hL hLG S hPrim hP2 hg1 hg
    exact gcdOne_of_nonbranching_primitive (L := L) (hL := by omega) hPrim hnb g hg

/-! ## The end-to-end population consequence, on the actual `P2` predicate -/

/-- **End-to-end population reduction for primitive `P2` genomes, with no
complete-spectrum uniqueness premise.**  Normalized equality of the complete
`(L-1)`-read distributions forces the two lengths to be equal and the two
complete spectra to be equal, for two primitive `P2` truths of arbitrary
lengths, at `2 ≤ L ≤ min G H`.

This is `PopulationReduction.population_uniqueness_primitive_P2_words` with
`hBBTS`/`hBBTD`/`AdmP2` discharged by `gcd_one_of_primitive_P2` (the `AdmP2`
hypotheses are read off the actual `P2` predicate, which is *stronger*: it
carries both clauses, while the cap uses only the triple-repeat clause). -/
theorem population_uniqueness_of_primitive_P2 {G H : ℕ}
    (hG : 0 < G) (hH : 0 < H) (S : Fin G → α) (D : Fin H → α)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hLH : L ≤ H)
    (hPrimS : PopulationReduction.IsPrimitive S) (hPrimD : PopulationReduction.IsPrimitive D)
    (hP2S : P2 hG L S) (hP2D : P2 hH L D)
    (hNormEq : NormalizedEqual (W := Fin L → α) (specCount (L := L) hG S)
      (specCount (L := L) hH D) G H) :
    G = H ∧ specCount (L := L) hG S = specCount (L := L) hH D :=
  PopulationReduction.population_uniqueness_of_spectra hG hH S D hNormEq
    (gcd_one_of_primitive_P2 hG hL hLG S hPrimS hP2S)
    (gcd_one_of_primitive_P2 hH hL hLH D hPrimD hP2D)

end AssemblyP1.P2GcdOne
