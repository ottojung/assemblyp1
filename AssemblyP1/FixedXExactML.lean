import Mathlib
import AssemblyP1.OrientedSameLengthML
import AssemblyP1.SourceFaithfulIs

/-!
# Fixed-`x` exact ML classification (issue #258)

Child of #255; contrast #256. This module settles the **fixed-`x`** question:
for a *FIXED* observed count vector `x`, when does the truth spectrum `A`
maximize the exact finite-sample multinomial likelihood over the same-length
oriented feasible spectra? The uniform-over-all-samples question (#256) is
different and is not settled here.

Everything is **exact rational arithmetic**: likelihood comparisons are between
positive integers (or rationals `ℚ`), with no floating point. Zero-count edges
are never omitted — they contribute the factor `1` to every product comparison
and still constrain the candidate circulations through balance and positivity
on the whole support.

Scope: oriented single-strand read types, exact multinomial objective
(`docs/ml-formalization-contract.md` Variant E), candidate universe =
same-length oriented feasible spectra. Nothing here is transferred to
reverse-complement molecule flows or to the §6.1 binomial approximation. See
`docs/fixed-x-exact-ml-258.md` for the mathematical note.

## Theorem surface (trust boundary)

* `fixedX_classification_iff`: the iff of deliverable 1 — maximization of the
  exact likelihood factor over feasible spectra is equivalent to the exact
  integer likelihood-product inequality for every feasible spectrum.
* `fixedX_classification_iff_of_realizable`: the directly stated theorem of
  deliverable 5, with explicit quantifiers for sampling realizability
  (`hreal`), historical coverage (`hcov`), the objective (exact multinomial,
  Variant E) and the candidate universe (same-length oriented feasible
  spectra).
* `exactLik_eq_spectrumLikFactor`: the genome-level `exactLik` equals the
  exact rational likelihood factor of the candidate's spectrum, so the
  spectrum-level iff applies to the genome-level objective.
* `FixedXExample`: the concrete instance of deliverable 3 — genome
  `S = AAABBB`, `L = 2`, with four feasible spectra; the truth wins at the
  realizable complete-support sample `x1` and loses at the realizable
  complete-support sample `x2` (exact ratio `4`). All instance facts are
  kernel-checked by `decide`/`norm_num`.

## What is deliberately not proved here

* The Eulerian realization direction (every feasible spectrum is the spectrum
  of some circular genome) is external (Eulerian-circuit existence / BBT); the
  genome-level theorems of `FixedXExample` are proved at the four concrete
  genomes directly.
* The chamber decomposition of deliverable 2 is a real-arrangement statement;
  its decision content is the finite certificate, which is kernel-checked at
  the instance.
* Full `I_s` is not assumed anywhere; the coverage hypothesis is the source's
  `Covers` clause only. The concrete instance does not satisfy full `I_s`
  (bridging a length-`1` triple repeat needs a read of length `≥ 3`), which is
  exactly why its feasible set is not a singleton.
-/

namespace AssemblyP1.FixedXExactML

open Finset BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]

/-! ## The candidate universe and the exact-rational likelihood factor -/

/-- The candidate universe: same-length oriented feasible spectra — positive
integer balanced circulations of total mass `G` on the truth's window support.
These are literally the three hypotheses of
`AssemblyP1.MLEscape.IsMassGPositiveCirculation`, restated at spectrum level so
the fixed-`x` question can be asked without choosing a realizing genome. -/
def IsFeasibleSpectrum {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : (Fin L → α) → ℕ) : Prop :=
  (∀ w : Fin L → α, w ∈ OrientedRigidity.support (L := L) hG S ↔ 0 < B w) ∧
    OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := α) (L := L))
      (OrientedRigidity.winSuffix (α := α) (L := L))
      (OrientedRigidity.genomeNodes (L := L) hG S)
      (OrientedRigidity.support (L := L) hG S) B ∧
    (∑ w ∈ (OrientedRigidity.support (L := L) hG S : Finset (Fin L → α)), B w = G)

/-- The exact integer likelihood product `∏ w ∈ E, (B w)^(x w)`: the exact
multinomial likelihood factor with the candidate-independent denominator
`G ^ n` (and the observation-only multinomial coefficient) divided out. All
comparisons between such products are exact integer comparisons — no floating
point anywhere. -/
def likProduct {L : ℕ} (E : Finset (Fin L → α)) (B : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) : ℕ :=
  ∏ w ∈ E, (B w) ^ (x w)

/-- The exact rational likelihood factor of a candidate spectrum `B` at the
fixed observation `x`: `∏ w ∈ E, (B w / G)^(x w)`. This is the oriented
same-length exact Medvedev–Brudno multinomial objective
(`docs/ml-formalization-contract.md` Variant E) with the observation-only
multinomial coefficient divided out, evaluated at a spectrum. -/
def spectrumLikFactor {G L : ℕ} (hG : 0 < G) (E : Finset (Fin L → α))
    (B : (Fin L → α) → ℕ) (x : (Fin L → α) → ℕ) : ℚ :=
  ∏ w ∈ E, ((B w : ℚ) / (G : ℚ)) ^ (x w)

/-- **The exact rational likelihood factor is the exact integer product divided
by the candidate-independent denominator `G ^ n`** (`n = totalReads x`). The
support hypothesis on `x` is what makes the product over `E` equal the full
likelihood factor: off-support factors are `(·/G)^0 = 1`. -/
theorem spectrumLikFactor_eq_likProduct_div {G L : ℕ} (hG : 0 < G)
    (E : Finset (Fin L → α)) (B : (Fin L → α) → ℕ) (x : (Fin L → α) → ℕ)
    (hx : ∀ w, 0 < x w → w ∈ E) :
    spectrumLikFactor hG E B x
      = (likProduct E B x : ℚ) / (G : ℚ) ^ (OrientedSameLengthML.totalReads x) := by
  unfold spectrumLikFactor likProduct
  simp only [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ w ∈ E, x w = OrientedSameLengthML.totalReads x := by
    have hoff : ∀ w ∈ (Finset.univ : Finset (Fin L → α)), w ∉ E → x w = 0 := by
      intro w _ hw
      by_contra hcon
      exact hw (hx w (Nat.pos_of_ne_zero hcon))
    unfold OrientedSameLengthML.totalReads
    exact Finset.sum_subset (Finset.subset_univ E) hoff
  rw [hsum]
  simp [Rat.cast_pow, Rat.cast_prod]

/-! ## The genome-level objective is the spectrum-level factor -/

/-- A per-factor cast lemma: the `ℝ` factor `((k : ℝ)/(G : ℝ))^n` equals the
`ℚ` factor `((k : ℚ)/(G : ℚ))^n` viewed in `ℝ`. This is `div_pow` plus
`Rat.cast_pow` plus the double-cast `Rat.cast_natCast`. -/
theorem factor_cast {G : ℕ} (k : ℕ) (n : ℕ) :
    ((k : ℝ) / (G : ℝ)) ^ n = (((k : ℚ) / (G : ℚ)) ^ n : ℝ) := by
  simp [div_pow, Rat.cast_pow, Rat.cast_natCast]

/-- **The genome-level `exactLik` equals the exact rational likelihood factor
of the candidate's spectrum** (observation-only multinomial coefficient
divided out in both). Under the support hypothesis on `x`, the off-support
factors of `exactLik` are `1`, so the objective is the product over the
support; `Rat.cast_prod` moves the `ℚ` product past the cast, and
`factor_cast` equates the factors. -/
theorem exactLik_eq_spectrumLikFactor {G L : ℕ} (hG : 0 < G) (S D : Fin G → α)
    (x : (Fin L → α) → ℕ)
    (hx : ∀ w, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S) :
    OrientedSameLengthML.exactLik (L := L) hG D x
      = (spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S)
          (OrientedRigidity.specCount (L := L) hG D) x : ℝ) := by
  have hsub : (Finset.univ : Finset (Fin L → α)) ⊇
      OrientedRigidity.support (L := L) hG S := Finset.subset_univ _
  have hoff : ∀ w ∈ (Finset.univ : Finset (Fin L → α)),
      w ∉ OrientedRigidity.support (L := L) hG S →
        OrientedSameLengthML.exactFactor hG D x w = 1 := by
    intro w _ hw
    have hx0 : x w = 0 := by
      by_contra hcon
      exact hw (hx w (Nat.pos_of_ne_zero hcon))
    unfold OrientedSameLengthML.exactFactor
    simp [hx0]
  unfold OrientedSameLengthML.exactLik
  rw [(Finset.prod_subset hsub hoff).symm]
  unfold OrientedSameLengthML.exactFactor
  unfold spectrumLikFactor
  rw [Rat.cast_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp [Rat.cast_pow, div_pow, Rat.cast_natCast]

/-! ## The fixed-`x` classification iff (deliverable 1) -/

/-- **Per-candidate comparison iff.** For one feasible spectrum `B`, the exact
rational likelihood-factor comparison equals the exact integer likelihood-product
comparison: rewrite both sides to the divided form, cancel the
candidate-independent positive denominator `G ^ n`, and remove the `ℕ → ℚ`
casts. -/
theorem specLik_le_iff_likProduct {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : (Fin L → α) → ℕ) (x : (Fin L → α) → ℕ)
    (hx : ∀ w, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S) :
    spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S) B x
        ≤ spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S)
          (OrientedRigidity.specCount (L := L) hG S) x
      ↔
    likProduct (OrientedRigidity.support (L := L) hG S) B x
        ≤ likProduct (OrientedRigidity.support (L := L) hG S)
          (OrientedRigidity.specCount (L := L) hG S) x := by
  rw [spectrumLikFactor_eq_likProduct_div hG _ B x hx,
    spectrumLikFactor_eq_likProduct_div hG _ _ x hx]
  have hGq : (0 : ℚ) < (G : ℚ) := by exact_mod_cast hG
  have hc : (0 : ℚ) < (G : ℚ) ^ (OrientedSameLengthML.totalReads x) :=
    pow_pos hGq (OrientedSameLengthML.totalReads x)
  rw [div_le_div_iff_of_pos_right hc, Nat.cast_le]

/-- **The fixed-`x` classification iff.** For a fixed observation `x` whose
support lies in the truth's window support, the truth spectrum maximizes the
exact multinomial likelihood factor over the feasible spectra if and only if
the exact integer likelihood product of the truth is at least that of every
feasible spectrum.

Exact rational arithmetic throughout: the candidate-independent positive
denominator `G ^ n` cancels in every comparison. Zero-count edges contribute
the factor `1` to both sides — present, never omitted — and they still
constrain the candidate circulations through balance and positivity on the
whole support `E`. -/
theorem fixedX_classification_iff {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (x : (Fin L → α) → ℕ)
    (hx : ∀ w, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S) :
    (∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S) B x
          ≤ spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x)
      ↔
    (∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        likProduct (OrientedRigidity.support (L := L) hG S) B x
          ≤ likProduct (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x) := by
  constructor
  · intro h B hB
    exact (specLik_le_iff_likProduct hG S B x hx).mp (h B hB)
  · intro h B hB
    exact (specLik_le_iff_likProduct hG S B x hx).mpr (h B hB)

/-- **The directly stated Lean theorem (deliverable 5).** For a fixed
observation `x` that is realizable from the truth (sampling realizability,
`hreal`) by a realization whose starts cover the genome (historical coverage,
`hcov`), the truth spectrum maximizes the exact multinomial likelihood factor
(objective: Variant E, coefficient divided out) over the same-length oriented
feasible spectra (candidate universe) if and only if the exact integer
likelihood product of the truth dominates that of every feasible spectrum.

The realizability hypothesis implies the support hypothesis of
`fixedX_classification_iff` via `observedOf_mem_support`. The coverage
hypothesis is stated for every realization producing `x` (coverage is a
property of the realization, not of the likelihood). -/
theorem fixedX_classification_iff_of_realizable {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (x : (Fin L → α) → ℕ)
    (hreal : ∃ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x)
    (hcov : ∀ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x →
        SourceFaithfulIs.Covers (OrientedSameLengthML.asGenome hG S) L
          (OrientedSameLengthML.realizedStarts ρ)) :
    (∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S) B x
          ≤ spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x)
      ↔
    (∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        likProduct (OrientedRigidity.support (L := L) hG S) B x
          ≤ likProduct (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x) := by
  obtain ⟨ρ, hρ⟩ := hreal
  have hx : ∀ w, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S := by
    intro w hw
    exact OrientedSameLengthML.observedOf_mem_support hG S ρ w (by rw [hρ]; exact hw)
  exact fixedX_classification_iff hG S x hx

end AssemblyP1.FixedXExactML
