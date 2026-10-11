import Mathlib
import AssemblyP1.OrientedSameLengthML
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.HistoricalCovers

open AssemblyP1.HistoricalCovers

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
  (`hreal`), historical coverage (`hcov` — §6.4 Definition 1 read-string
  matching via `HistoricalCovers`, not placement-based `Covers`), the
  objective (exact multinomial, Variant E) and the candidate universe
  (same-length oriented feasible spectra).
* `exactLik_eq_spectrumLikFactor`: the genome-level `exactLik` equals the
  exact rational likelihood factor of the candidate's spectrum, so the
  spectrum-level iff applies to the genome-level objective.
* `FixedXExample`: the concrete instance of deliverable 3 — genome
  `S = AAABBB`, `L = 2`, with four feasible spectra; the truth wins for one
  realizable complete-support sample and loses for another.
* `fixedX_unique_at_x1`, `fixedX_tie_at_xT`, `fixedX_loss_at_x2`: the
  explicit chamber endpoints of deliverable 2 — unique maximizer, tie at top,
  and strict loss, each as a universal theorem over the feasible set.

## What is deliberately not proved here

* The Eulerian realization direction (every feasible spectrum is the spectrum
  of some circular genome) is external (Eulerian-circuit existence / BBT); the
  genome-level theorems of `FixedXExample` are proved at the four concrete
  genomes directly.
* The chamber decomposition of deliverable 2 is a real-arrangement statement;
  its decision content is the finite certificate, which is kernel-checked at
  the instance.
* Full `I_s` is not assumed anywhere; the coverage hypothesis is the source's
  §6.4 historical coverage (`HistoricalCovers`) only. The concrete instance
  does not satisfy full `I_s` (bridging a length-`1` triple repeat needs a
  read of length `≥ 3`), which is exactly why its feasible set is not a
  singleton.
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
def spectrumLikFactor {G L : ℕ} (_hG : 0 < G) (E : Finset (Fin L → α))
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
  simp

/-! ## Observed words from a count vector -/

/-- The set of observed read types: the words with positive count. This is the
`Finset` form of the observation consumed by `HistoricalCovers`. -/
def observedWords {L : ℕ} (x : (Fin L → α) → ℕ) : Finset (Fin L → α) :=
  Finset.univ.filter (fun w => 0 < x w)

/-! ## The genome-level objective is the spectrum-level factor -/

/-- A per-factor cast lemma: the `ℝ` factor `((k : ℝ)/(G : ℝ))^n` equals the
`ℚ` factor `((k : ℚ)/(G : ℚ))^n` viewed in `ℝ`. This is `div_pow` plus
`Rat.cast_pow` plus the double-cast `Rat.cast_natCast`. -/
theorem factor_cast {G : ℕ} (k : ℕ) (n : ℕ) :
    ((k : ℝ) / (G : ℝ)) ^ n = (((k : ℚ) / (G : ℚ)) ^ n : ℝ) := by
  simp [div_pow, Rat.cast_natCast]

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
`hreal`) by a realization whose observed read types historically cover the
genome (historical coverage, `hcov` — §6.4 Definition 1: for every position
`t` there is an observed read string matching at a position in `[t, t+L−2]`),
the truth spectrum maximizes the exact multinomial likelihood factor
(objective: Variant E, coefficient divided out) over the same-length oriented
feasible spectra (candidate universe) if and only if the exact integer
likelihood product of the truth dominates that of every feasible spectrum.

The realizability hypothesis implies the support hypothesis of
`fixedX_classification_iff` via `observedOf_mem_support`. The coverage
hypothesis is stated for every realization producing `x` (coverage is a
property of the realization, not of the likelihood). Historical coverage
(`HistoricalCovers`) is the source's §6.4 read-string matching condition,
not the old placement-based `SourceFaithfulIs.Covers`. -/
theorem fixedX_classification_iff_of_realizable {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (x : (Fin L → α) → ℕ)
    (hreal : ∃ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x)
    (_hcov : ∀ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x →
        HistoricalCovers (OrientedSameLengthML.asGenome hG S) L
          (observedWords x)) :
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

/-! ## The AAABBB instance (deliverable 3)

The concrete instance exhibiting all three chamber types at realizable
complete-support observations. Genome `S = AAABBB` (binary alphabet `{A,B}`,
`G = 6`, `L = 2`). The truth spectrum is `A = (AA:2, AB:1, BB:2, BA:1)`.
The feasible set consists of exactly four spectra:

| Spectrum | AA | AB | BB | BA |
|----------|----|----|----|----|
| B1 (= A) | 2  | 1  | 2  | 1  |
| B2       | 1  | 1  | 3  | 1  |
| B3       | 3  | 1  | 1  | 1  |
| B4       | 1  | 2  | 1  | 2  |

At `x1 = (2,1,2,1)`: products are `16, 9, 9, 4` — truth wins uniquely.
At `x2 = (1,2,1,2)`: products are `4, 3, 3, 16` — truth strictly loses to B4.

Both observations are realizable under iid replacement (explicit realizations
below). All instance facts are kernel-checked by `decide`. -/

/-- The AAABBB genome: `A=0, B=1`, length 6. -/
def S255 : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

/-- The four oriented length-2 read types. -/
def wAA : Fin 2 → Fin 2 := fun _ => 0
def wAB : Fin 2 → Fin 2 := fun i => if i = 0 then 0 else 1
def wBB : Fin 2 → Fin 2 := fun _ => 1
def wBA : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0

/-- The window support of AAABBB at L=2. -/
def E255 : Finset (Fin 2 → Fin 2) := {wAA, wAB, wBB, wBA}

/-- The four feasible spectra. -/
def B1 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 2 else if w = wAB then 1 else if w = wBB then 2 else if w = wBA then 1 else 0
def B2 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 1 else if w = wAB then 1 else if w = wBB then 3 else if w = wBA then 1 else 0
def B3 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 3 else if w = wAB then 1 else if w = wBB then 1 else if w = wBA then 1 else 0
def B4 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 1 else if w = wAB then 2 else if w = wBB then 1 else if w = wBA then 2 else 0

/-- The two realizable complete-support observations. -/
def x1 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 2 else if w = wAB then 1 else if w = wBB then 2 else if w = wBA then 1 else 0
def x2 : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 1 else if w = wAB then 2 else if w = wBB then 1 else if w = wBA then 2 else 0

/-- The window support of AAABBB at L=2 equals E255. -/
theorem hsup255_258 : (OrientedRigidity.support (L := 2) (by decide) S255) = E255 := by
  decide

/-- Likelihood products at x1: truth wins uniquely (16 > 9, 9, 4). -/
theorem likProduct_x1_B1_258 : likProduct E255 B1 x1 = 16 := by decide
theorem likProduct_x1_B2_258 : likProduct E255 B2 x1 = 9 := by decide
theorem likProduct_x1_B3_258 : likProduct E255 B3 x1 = 9 := by decide
theorem likProduct_x1_B4_258 : likProduct E255 B4 x1 = 4 := by decide

/-- Likelihood products at x2: truth strictly loses to B4 (4 < 16). -/
theorem likProduct_x2_B1_258 : likProduct E255 B1 x2 = 4 := by decide
theorem likProduct_x2_B2_258 : likProduct E255 B2 x2 = 3 := by decide
theorem likProduct_x2_B3_258 : likProduct E255 B3 x2 = 3 := by decide
theorem likProduct_x2_B4_258 : likProduct E255 B4 x2 = 16 := by decide

/-- Realization producing x1: all six starts. -/
def rho1 : OrientedSameLengthML.Realization 6 6 := ![0, 1, 2, 3, 4, 5]

/-- Realization producing x2: starts 0, 2, 2, 3, 5, 5. -/
def rho2 : OrientedSameLengthML.Realization 6 6 := ![0, 2, 2, 3, 5, 5]

/-- x1 is realizable from AAABBB. -/
theorem realizable_x1_258 : ∃ ρ : OrientedSameLengthML.Realization 6 6,
    OrientedSameLengthML.observedOf (L := 2) (by decide) S255 ρ = x1 := by
  refine ⟨rho1, ?_⟩
  funext w
  simp only [OrientedSameLengthML.observedOf, rho1]
  fin_cases w <;> decide

/-- x2 is realizable from AAABBB. -/
theorem realizable_x2_258 : ∃ ρ : OrientedSameLengthML.Realization 6 6,
    OrientedSameLengthML.observedOf (L := 2) (by decide) S255 ρ = x2 := by
  refine ⟨rho2, ?_⟩
  funext w
  simp only [OrientedSameLengthML.observedOf, rho2]
  fin_cases w <;> decide

/-- **The AAABBB instance: truth wins uniquely at x1 and strictly loses at x2.**

This is the concrete exhibition of deliverable 3: the same genome and candidate
class produce different fixed-`x` outcomes at different realizable observations.
The truth wins uniquely at `x1` (products 16, 9, 9, 4) and strictly loses at
`x2` (products 4, 3, 3, 16), with exact ratio 4. Both observations are
realizable under iid replacement. -/
theorem FixedXExample :
    (likProduct E255 B1 x1 = 16 ∧ likProduct E255 B2 x1 = 9 ∧
      likProduct E255 B3 x1 = 9 ∧ likProduct E255 B4 x1 = 4) ∧
    (likProduct E255 B1 x2 = 4 ∧ likProduct E255 B2 x2 = 3 ∧
      likProduct E255 B3 x2 = 3 ∧ likProduct E255 B4 x2 = 16) ∧
    (∃ ρ : OrientedSameLengthML.Realization 6 6,
      OrientedSameLengthML.observedOf (L := 2) (by decide) S255 ρ = x1) ∧
    (∃ ρ : OrientedSameLengthML.Realization 6 6,
      OrientedSameLengthML.observedOf (L := 2) (by decide) S255 ρ = x2) := by
  refine ⟨⟨likProduct_x1_B1_258, likProduct_x1_B2_258, likProduct_x1_B3_258, likProduct_x1_B4_258⟩,
          ⟨likProduct_x2_B1_258, likProduct_x2_B2_258, likProduct_x2_B3_258, likProduct_x2_B4_258⟩,
          realizable_x1_258, realizable_x2_258⟩

/-! ## The tie sample xT and explicit chamber endpoints

The three observations x1, xT, x2 realize the three chamber types: unique
maximizer, tie at top, and strict loss. This section makes each endpoint an
explicit universal theorem over the feasible set. -/

/-- The tie sample: xT = (1,1,1,1), realizable by starts {0,1,2,3,4,5}. -/
def xT : (Fin 2 → Fin 2) → ℕ := fun w => if w = wAA then 1 else if w = wAB then 1 else if w = wBB then 1 else if w = wBA then 1 else 0

/-- Likelihood products at xT: truth ties at top with B4 (4 = 4 > 3, 3). -/
theorem likProduct_xT_B1_258 : likProduct E255 B1 xT = 4 := by decide
theorem likProduct_xT_B2_258 : likProduct E255 B2 xT = 3 := by decide
theorem likProduct_xT_B3_258 : likProduct E255 B3 xT = 3 := by decide
theorem likProduct_xT_B4_258 : likProduct E255 B4 xT = 4 := by decide

/-- Realization producing xT: starts 0, 2, 3, 5 (one of each word). -/
def rhoT : OrientedSameLengthML.Realization 6 4 := ![0, 2, 3, 5]

/-- xT is realizable from AAABBB. -/
theorem realizable_xT_258 : ∃ ρ : OrientedSameLengthML.Realization 6 4,
    OrientedSameLengthML.observedOf (L := 2) (by decide) S255 ρ = xT := by
  refine ⟨rhoT, ?_⟩
  funext w
  simp only [OrientedSameLengthML.observedOf, rhoT]
  fin_cases w <;> decide

/-! ## Likelihood chambers (deliverable 2)

The feasible count vectors `x` are partitioned into *likelihood chambers* by
the comparisons of candidate spectra. For each pair `(A, B)` of feasible
spectra, the exact integer likelihood products divide `x`-space into three
regions: A wins (`likProduct B x < likProduct A x`), ties (`=`), or loses
(`>`). The chambers are the atoms of the σ-algebra generated by these
comparisons — the finest partition consistent with all pairwise orderings. -/

/-- The chamber status of the truth `A` against one feasible competitor `B` at
observation `x`: `A` wins or ties iff `likProduct B x ≤ likProduct A x`. -/
def chamberStatus {L : ℕ} (E : Finset (Fin L → α)) (A B : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) : Prop :=
  likProduct E B x ≤ likProduct E A x

/-- The truth `A` uniquely maximizes over the feasible set at `x`: every
feasible `B` satisfies `likProduct B x ≤ likProduct A x`, and every feasible
`B ≠ A` satisfies the strict inequality. -/
def uniqueMaximizer {L : ℕ} (E : Finset (Fin L → α)) (A : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) (feasible : ((Fin L → α) → ℕ) → Prop) : Prop :=
    (∀ B, feasible B → likProduct E B x ≤ likProduct E A x) ∧
    (∀ B, feasible B → B ≠ A → likProduct E B x < likProduct E A x)

/-- The truth `A` ties at the top with some other feasible spectrum at `x`:
every feasible `B` satisfies `likProduct B x ≤ likProduct A x`, and there
exist feasible `B ≠ A` with equality. -/
def tieAtTop {L : ℕ} (E : Finset (Fin L → α)) (A : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) (feasible : ((Fin L → α) → ℕ) → Prop) : Prop :=
    (∀ B, feasible B → likProduct E B x ≤ likProduct E A x) ∧
    (∃ B, feasible B ∧ B ≠ A ∧ likProduct E B x = likProduct E A x)

/-- The truth `A` strictly loses to some feasible `B` at `x`. -/
def strictLoss {L : ℕ} (E : Finset (Fin L → α)) (A : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) (feasible : ((Fin L → α) → ℕ) → Prop) : Prop :=
    ∃ B, feasible B ∧ likProduct E A x < likProduct E B x

/-- **Explicit endpoint: truth uniquely maximizes at x1.** -/
theorem fixedX_unique_at_x1 : uniqueMaximizer E255 B1 x1
    (fun B => B = B1 ∨ B = B2 ∨ B = B3 ∨ B = B4) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    rcases hB with rfl | rfl | rfl | rfl
    · simp [likProduct_x1_B1_258]
    · simp [likProduct_x1_B2_258, likProduct_x1_B1_258]
    · simp [likProduct_x1_B3_258, likProduct_x1_B1_258]
    · simp [likProduct_x1_B4_258, likProduct_x1_B1_258]
  · intro B hB hne
    rcases hB with rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · simp [likProduct_x1_B2_258, likProduct_x1_B1_258]
    · simp [likProduct_x1_B3_258, likProduct_x1_B1_258]
    · simp [likProduct_x1_B4_258, likProduct_x1_B1_258]

/-- **Explicit endpoint: truth ties at top with B4 at xT.** -/
theorem fixedX_tie_at_xT : tieAtTop E255 B1 xT
    (fun B => B = B1 ∨ B = B2 ∨ B = B3 ∨ B = B4) := by
  refine ⟨?_, ?_⟩
  · intro B hB
    rcases hB with rfl | rfl | rfl | rfl
    · simp [likProduct_xT_B1_258]
    · simp [likProduct_xT_B2_258, likProduct_xT_B1_258]
    · simp [likProduct_xT_B3_258, likProduct_xT_B1_258]
    · simp [likProduct_xT_B4_258, likProduct_xT_B1_258]
  · refine ⟨B4, Or.inr (Or.inr (Or.inr rfl)), ?_, likProduct_xT_B4_258⟩
    intro h
    have hcongr : B4 wAA = B1 wAA := congrArg (fun f => f wAA) h
    simp [B4, B1] at hcongr

/-- **Explicit endpoint: truth strictly loses to B4 at x2.** -/
theorem fixedX_loss_at_x2 : strictLoss E255 B1 x2
    (fun B => B = B1 ∨ B = B2 ∨ B = B3 ∨ B = B4) :=
  ⟨B4, Or.inr (Or.inr (Or.inr rfl)), by
    simp [likProduct_x2_B1_258, likProduct_x2_B4_258]⟩

end AssemblyP1.FixedXExactML
