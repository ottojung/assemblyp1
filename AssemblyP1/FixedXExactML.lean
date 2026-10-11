import Mathlib
import AssemblyP1.OrientedSameLengthML
import AssemblyP1.SourceFaithfulIs

/-!
# Fixed-`x` exact ML classification (issue #258) — minimal core

Child of #255; contrast #256. This module isolates the **core structural
content** of the fixed-`x` question: the exact characterization of the
candidate universe (same-length oriented feasible spectra) for the AAABBB
instance, and the classification iff quantified over that universe.

Everything is **exact rational arithmetic**: likelihood comparisons are between
positive integers (or rationals `ℚ`), with no floating point. Zero-count edges
are never omitted.

The key theorem is `feasibleSpectrum_iff_258`: the feasible set of AAABBB at
`L = 2` is exactly `{B1, B2, B3, B4}`, proved via the balance equation
`B wAB = B wBA`, mass `6`, positivity, and `omega`.
-/

namespace AssemblyP1.FixedXExactML

open Finset BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]

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

/-- The exact integer likelihood product `∏ w ∈ E, (B w)^(x w)`. -/
def likProduct {L : ℕ} (E : Finset (Fin L → α)) (B : (Fin L → α) → ℕ)
    (x : (Fin L → α) → ℕ) : ℕ :=
  ∏ w ∈ E, (B w) ^ (x w)

/-- The exact rational likelihood factor of a candidate spectrum `B` at the
fixed observation `x`: `∏ w ∈ E, (B w / G)^(x w)`. -/
def spectrumLikFactor {G L : ℕ} (_hG : 0 < G) (E : Finset (Fin L → α))
    (B : (Fin L → α) → ℕ) (x : (Fin L → α) → ℕ) : ℚ :=
  ∏ w ∈ E, ((B w : ℚ) / (G : ℚ)) ^ (x w)

/-! ## The AAABBB instance

Genome `S = AAABBB` (binary alphabet `{A,B}`, `G = 6`, `L = 2`). The truth
spectrum is `A = (AA:2, AB:1, BB:2, BA:1)`. The feasible set consists of exactly
four spectra. -/

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

/-- The window support of AAABBB at L=2 equals E255. -/
theorem hsup255_258 : (OrientedRigidity.support (L := 2) (by decide) S255) = E255 := by
  decide

/-- The two de Bruijn nodes of AAABBB at `L = 2`: the symbols `A` and `B`. -/
def nodeA258 : Fin 1 → Fin 2 := fun _ => 0
def nodeB258 : Fin 1 → Fin 2 := fun _ => 1

/-- The node set of AAABBB at `L = 2` is exactly `{nodeA258, nodeB258}`. -/
theorem genomeNodes_258 : (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
    = {nodeA258, nodeB258} := by
  decide

theorem mem_nodeA_258 : nodeA258 ∈ OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255 := by
  rw [genomeNodes_258]; simp

theorem mem_nodeB_258 : nodeB258 ∈ OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255 := by
  rw [genomeNodes_258]; simp

/-- The four balance filters of the AAABBB instance, evaluated exactly. -/
theorem filt_outA_258 : (E255.filter
    (fun e => OrientedRigidity.winPrefix (α := Fin 2) (L := 2) e = nodeA258)) = {wAA, wAB} := by
  decide

theorem filt_inA_258 : (E255.filter
    (fun e => OrientedRigidity.winSuffix (α := Fin 2) (L := 2) e = nodeA258)) = {wAA, wBA} := by
  decide

theorem filt_outB_258 : (E255.filter
    (fun e => OrientedRigidity.winPrefix (α := Fin 2) (L := 2) e = nodeB258)) = {wBB, wBA} := by
  decide

theorem filt_inB_258 : (E255.filter
    (fun e => OrientedRigidity.winSuffix (α := Fin 2) (L := 2) e = nodeB258)) = {wAB, wBB} := by
  decide

/-- **The balance equation of the AAABBB instance.** At `L = 2` the two node
balance conditions both say `B wAB = B wBA`. -/
theorem balanceEq_258 (B : (Fin 2 → Fin 2) → ℕ)
    (hbal : OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := Fin 2) (L := 2))
      (OrientedRigidity.winSuffix (α := Fin 2) (L := 2))
      (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
      (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255) B) :
    B wAB = B wBA := by
  unfold OrientedRigidity.Balanced at hbal
  have hA : ∑ e ∈ insert wAA ({wAB} : Finset _), B e
      = ∑ e ∈ insert wAA ({wBA} : Finset _), B e := by
    have hA' : ∑ e ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255).filter
        (fun e => OrientedRigidity.winPrefix (α := Fin 2) (L := 2) e = nodeA258), B e
        = ∑ e ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255).filter
        (fun e => OrientedRigidity.winSuffix (α := Fin 2) (L := 2) e = nodeA258), B e :=
      hbal nodeA258 mem_nodeA_258
    rw [hsup255_258, filt_outA_258, filt_inA_258] at hA'
    exact hA'
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_singleton] at hA
  omega

/-- Every oriented length-2 read type over the binary alphabet is one of the four
words `wAA, wAB, wBB, wBA`. -/
theorem word_cases_258 (w : Fin 2 → Fin 2) : w = wAA ∨ w = wAB ∨ w = wBB ∨ w = wBA := by
  by_cases h0 : (w 0).val = 0
  · by_cases h1 : (w 1).val = 0
    · left; exact funext fun i => by
        fin_cases i
        · exact Fin.ext h0
        · exact Fin.ext h1
    · right; left
      have h1' : (w 1).val = 1 := by have := Fin.isLt (w 1); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.ext h0
        · exact Fin.val_injective h1'
  · by_cases h1 : (w 1).val = 0
    · right; right; right
      have h0' : (w 0).val = 1 := by have := Fin.isLt (w 0); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.val_injective h0'
        · exact Fin.ext h1
    · right; right; left
      have h0' : (w 0).val = 1 := by have := Fin.isLt (w 0); omega
      have h1' : (w 1).val = 1 := by have := Fin.isLt (w 1); omega
      exact funext fun i => by
        fin_cases i
        · exact Fin.val_injective h0'
        · exact Fin.val_injective h1'

/-- The support clause of `IsFeasibleSpectrum` at the instance, for each candidate. -/
theorem support_B1_258 : ∀ w : Fin 2 → Fin 2,
    w ∈ OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255 ↔ 0 < B1 w := by
  intro w
  rw [hsup255_258]
  rcases word_cases_258 w with r | r | r | r <;> subst r <;> decide

theorem support_B2_258 : ∀ w : Fin 2 → Fin 2,
    w ∈ OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255 ↔ 0 < B2 w := by
  intro w
  rw [hsup255_258]
  rcases word_cases_258 w with r | r | r | r <;> subst r <;> decide

theorem support_B3_258 : ∀ w : Fin 2 → Fin 2,
    w ∈ OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255 ↔ 0 < B3 w := by
  intro w
  rw [hsup255_258]
  rcases word_cases_258 w with r | r | r | r <;> subst r <;> decide

theorem support_B4_258 : ∀ w : Fin 2 → Fin 2,
    w ∈ OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255 ↔ 0 < B4 w := by
  intro w
  rw [hsup255_258]
  rcases word_cases_258 w with r | r | r | r <;> subst r <;> decide

/-- The balance clause of `IsFeasibleSpectrum` at the instance, for each candidate. -/
theorem balance_B1_258 : OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := Fin 2) (L := 2))
    (OrientedRigidity.winSuffix (α := Fin 2) (L := 2))
    (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
    (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255) B1 := by
  unfold OrientedRigidity.Balanced
  intro v hv
  rw [genomeNodes_258] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv <;> subst hv <;> decide

theorem balance_B2_258 : OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := Fin 2) (L := 2))
    (OrientedRigidity.winSuffix (α := Fin 2) (L := 2))
    (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
    (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255) B2 := by
  unfold OrientedRigidity.Balanced
  intro v hv
  rw [genomeNodes_258] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv <;> subst hv <;> decide

theorem balance_B3_258 : OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := Fin 2) (L := 2))
    (OrientedRigidity.winSuffix (α := Fin 2) (L := 2))
    (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
    (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255) B3 := by
  unfold OrientedRigidity.Balanced
  intro v hv
  rw [genomeNodes_258] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv <;> subst hv <;> decide

theorem balance_B4_258 : OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := Fin 2) (L := 2))
    (OrientedRigidity.winSuffix (α := Fin 2) (L := 2))
    (OrientedRigidity.genomeNodes (L := 2) (by decide : 0 < 6) S255)
    (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255) B4 := by
  unfold OrientedRigidity.Balanced
  intro v hv
  rw [genomeNodes_258] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv <;> subst hv <;> decide

/-- The mass clause of `IsFeasibleSpectrum` at the instance, for each candidate. -/
theorem mass_B1_258 : ∑ w ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255), B1 w = 6 := by
  rw [hsup255_258]; decide

theorem mass_B2_258 : ∑ w ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255), B2 w = 6 := by
  rw [hsup255_258]; decide

theorem mass_B3_258 : ∑ w ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255), B3 w = 6 := by
  rw [hsup255_258]; decide

theorem mass_B4_258 : ∑ w ∈ (OrientedRigidity.support (L := 2) (by decide : 0 < 6) S255), B4 w = 6 := by
  rw [hsup255_258]; decide

/-- Each of the four exhibited spectra is feasible. -/
theorem feasible_B1_258 : IsFeasibleSpectrum (by decide : 0 < 6) S255 B1 :=
  ⟨support_B1_258, balance_B1_258, mass_B1_258⟩

theorem feasible_B2_258 : IsFeasibleSpectrum (by decide : 0 < 6) S255 B2 :=
  ⟨support_B2_258, balance_B2_258, mass_B2_258⟩

theorem feasible_B3_258 : IsFeasibleSpectrum (by decide : 0 < 6) S255 B3 :=
  ⟨support_B3_258, balance_B3_258, mass_B3_258⟩

theorem feasible_B4_258 : IsFeasibleSpectrum (by decide : 0 < 6) S255 B4 :=
  ⟨support_B4_258, balance_B4_258, mass_B4_258⟩

/-! ## The bridge theorem: `IsFeasibleSpectrum hG S255 B ↔ B=B1 ∨ B=B2 ∨ B=B3 ∨ B=B4`

This is the **core structural content** of issue #258. It proves that the four
spectra exhibited above are ALL the feasible spectra — every feasible spectrum
equals one of them.

**Proof strategy (the "targeted census"):**
1. **Positivity** (support clause): all four values `B wAA, B wAB, B wBB, B wBA` are `> 0`
   (since all four words are in the support `E255`).
2. **Balance** (`balanceEq_258`): `B wAB = B wBA`.
3. **Mass**: `B wAA + B wAB + B wBB + B wBA = 6`.
4. **omega**: the linear system with `AB = BA`, `AA + 2·AB + BB = 6`, all `> 0`
   has exactly the four solutions `(2,1,2,1), (1,1,3,1), (3,1,1,1), (1,2,1,2)`.

Backward: each exhibited spectrum satisfies all three clauses (proved above). -/
theorem feasibleSpectrum_iff_258 (B : (Fin 2 → Fin 2) → ℕ) :
    IsFeasibleSpectrum (by decide : 0 < 6) S255 B ↔ B = B1 ∨ B = B2 ∨ B = B3 ∨ B = B4 := by
  constructor
  · intro hB
    obtain ⟨hsupp, hbal, hsum⟩ := hB
    have hAA : 0 < B wAA := (hsupp wAA).mp (by rw [hsup255_258]; simp [E255])
    have hAB : 0 < B wAB := (hsupp wAB).mp (by rw [hsup255_258]; simp [E255])
    have hBB : 0 < B wBB := (hsupp wBB).mp (by rw [hsup255_258]; simp [E255])
    have hBA : 0 < B wBA := (hsupp wBA).mp (by rw [hsup255_258]; simp [E255])
    have heq : B wAB = B wBA := balanceEq_258 B hbal
    have hsum' : B wAA + B wAB + B wBB + B wBA = 6 := by
      rw [hsup255_258] at hsum
      have hsum'' : ∑ w ∈ insert wAA (insert wAB (insert wBB ({wBA} : Finset _))), B w = 6 := hsum
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton] at hsum''
      omega
    have hvals : (B wAA = 2 ∧ B wAB = 1 ∧ B wBB = 2 ∧ B wBA = 1) ∨
        (B wAA = 1 ∧ B wAB = 1 ∧ B wBB = 3 ∧ B wBA = 1) ∨
        (B wAA = 3 ∧ B wAB = 1 ∧ B wBB = 1 ∧ B wBA = 1) ∨
        (B wAA = 1 ∧ B wAB = 2 ∧ B wBB = 1 ∧ B wBA = 2) := by omega
    rcases hvals with h | h | h | h
    · left; funext w; rcases word_cases_258 w with r | r | r | r <;> subst r
      · rw [h.1]; decide
      · rw [h.2.1]; decide
      · rw [h.2.2.1]; decide
      · rw [h.2.2.2]; decide
    · right; left; funext w; rcases word_cases_258 w with r | r | r | r <;> subst r
      · rw [h.1]; decide
      · rw [h.2.1]; decide
      · rw [h.2.2.1]; decide
      · rw [h.2.2.2]; decide
    · right; right; left; funext w; rcases word_cases_258 w with r | r | r | r <;> subst r
      · rw [h.1]; decide
      · rw [h.2.1]; decide
      · rw [h.2.2.1]; decide
      · rw [h.2.2.2]; decide
    · right; right; right; funext w; rcases word_cases_258 w with r | r | r | r <;> subst r
      · rw [h.1]; decide
      · rw [h.2.1]; decide
      · rw [h.2.2.1]; decide
      · rw [h.2.2.2]; decide
  · intro hB
    rcases hB with h | h | h | h <;> subst h
    · exact feasible_B1_258
    · exact feasible_B2_258
    · exact feasible_B3_258
    · exact feasible_B4_258

/-! ## The fixed-`x` classification iff (deliverable 1)

The truth spectrum maximizes the exact multinomial likelihood factor over the
feasible spectra if and only if the exact integer likelihood product of the
truth is at least that of every feasible spectrum.

Quantified over `IsFeasibleSpectrum` — NOT over specific candidates. -/

/-- **The exact rational likelihood factor is the exact integer product divided
by the candidate-independent denominator `G ^ n`**. -/
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

/-- **Per-candidate comparison iff.** -/
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

Quantified over `IsFeasibleSpectrum` — NOT over specific candidates. -/
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

/-! ## The directly stated Lean theorem (deliverable 5)

With explicit quantifiers for sampling realizability (`hreal`), historical
coverage (`hcov`), the objective (exact multinomial, Variant E) and the
candidate universe (same-length oriented feasible spectra). -/

/-- **Coverage implies observed cover.** Under historical coverage, every genome
position is covered by some observed window. -/
theorem coverage_implies_observed_cover {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (x : (Fin L → α) → ℕ)
    (hreal : ∃ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x)
    (hcov : ∀ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x →
        SourceFaithfulIs.Covers (OrientedSameLengthML.asGenome hG S) L
          (OrientedSameLengthML.realizedStarts ρ)) :
    ∀ p : Fin G, ∃ w ∈ OrientedRigidity.support (L := L) hG S,
      x w > 0 ∧ ∃ d : Fin L, w d = S p := by
  obtain ⟨ρ, hρ⟩ := hreal
  intro p
  have hcov' := hcov ρ hρ
  obtain ⟨r, hr, d, hd⟩ := hcov' p
  refine ⟨OrientedRigidity.window (L := L) hG S r, ?_, ?_, d, ?_⟩
  · exact (OrientedSameLengthML.mem_support_iff_window hG S _).mpr ⟨r, rfl⟩
  · rw [hρ.symm]
    show (∑ j : Fin (OrientedSameLengthML.totalReads x),
      if OrientedRigidity.window (L := L) hG S (ρ j) = OrientedRigidity.window (L := L) hG S r then 1 else 0) > 0
    obtain ⟨i, hi⟩ := (OrientedSameLengthML.mem_realizedStarts ρ r).mp hr
    have hterm : (if OrientedRigidity.window (L := L) hG S (ρ i) = OrientedRigidity.window (L := L) hG S r then 1 else 0) = 1 := by
      rw [hi]
      simp
    have hpos : ∀ j : Fin (OrientedSameLengthML.totalReads x),
        0 ≤ (if OrientedRigidity.window (L := L) hG S (ρ j) = OrientedRigidity.window (L := L) hG S r then 1 else 0) := by
      intro j
      split
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    have hsum : 1 ≤ ∑ j : Fin (OrientedSameLengthML.totalReads x),
        if OrientedRigidity.window (L := L) hG S (ρ j) = OrientedRigidity.window (L := L) hG S r then 1 else 0 := by
      calc 1 = (if OrientedRigidity.window (L := L) hG S (ρ i) = OrientedRigidity.window (L := L) hG S r then 1 else 0) := by rw [hterm]
        _ ≤ ∑ j : Fin (OrientedSameLengthML.totalReads x),
            if OrientedRigidity.window (L := L) hG S (ρ j) = OrientedRigidity.window (L := L) hG S r then 1 else 0 :=
          Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin (OrientedSameLengthML.totalReads x) =>
              if OrientedRigidity.window (L := L) hG S (ρ j) =
                  OrientedRigidity.window (L := L) hG S r then (1 : ℕ) else 0)
            (by intro j _; exact hpos j) (Finset.mem_univ i)
    omega
  · unfold OrientedRigidity.window OrientedRigidity.cyc
    have hmod : (r.val + d.val) % G = p.val := hd.symm
    change S (⟨(r.val + d.val) % G, Nat.mod_lt _ hG⟩ : Fin G) = S p
    exact congrArg S (Fin.ext hmod)

/-- **The directly stated Lean theorem (deliverable 5).** For a fixed
observation `x` that is realizable from the truth (sampling realizability,
`hreal`) by a realization whose starts cover the genome (historical coverage,
`hcov`):

1. **Structural consequence of coverage**: every genome position is covered by
   some observed window.
2. **Classification iff**: the truth spectrum maximizes the exact multinomial
   likelihood factor over the same-length oriented feasible spectra if and only
   if the exact integer likelihood product of the truth dominates that of every
   feasible spectrum.

The coverage hypothesis `hcov` is USED to establish the structural property (1). -/
theorem fixedX_classification_iff_of_realizable {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (x : (Fin L → α) → ℕ)
    (hreal : ∃ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x)
    (hcov : ∀ ρ : OrientedSameLengthML.Realization G (OrientedSameLengthML.totalReads x),
      OrientedSameLengthML.observedOf (L := L) hG S ρ = x →
        SourceFaithfulIs.Covers (OrientedSameLengthML.asGenome hG S) L
          (OrientedSameLengthML.realizedStarts ρ)) :
    (∀ p : Fin G, ∃ w ∈ OrientedRigidity.support (L := L) hG S,
        x w > 0 ∧ ∃ d : Fin L, w d = S p) ∧
    ((∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S) B x
          ≤ spectrumLikFactor hG (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x)
      ↔
     (∀ B : (Fin L → α) → ℕ, IsFeasibleSpectrum hG S B →
        likProduct (OrientedRigidity.support (L := L) hG S) B x
          ≤ likProduct (OrientedRigidity.support (L := L) hG S)
            (OrientedRigidity.specCount (L := L) hG S) x)) := by
  refine ⟨coverage_implies_observed_cover hG S x hreal hcov, ?_⟩
  obtain ⟨ρ, hρ⟩ := hreal
  have hx : ∀ w, 0 < x w → w ∈ OrientedRigidity.support (L := L) hG S := by
    intro w hw
    exact OrientedSameLengthML.observedOf_mem_support hG S ρ w (by rw [hρ]; exact hw)
  exact fixedX_classification_iff hG S x hx


/-! ## Genuine global fixed-sample chambers for the AAABBB instance

These theorems quantify over `IsFeasibleSpectrum`, not a stipulated
four-element candidate list. Exhaustiveness is supplied by
`feasibleSpectrum_iff_258` above. All comparisons are exact integers. -/

def xTie258 : (Fin 2 → Fin 2) → ℕ := fun _ => 1

theorem truth_spec_B1_258 :
    OrientedRigidity.specCount (L := 2) (by decide : 0 < 6) S255 = B1 := by
  funext w
  rcases word_cases_258 w with h | h | h | h <;> subst w <;> decide

/-- Under observation x=B1, the truth strictly beats every distinct
positive balanced same-length spectrum; this is an ALL-candidates theorem. -/
theorem fixedX_unique_at_xWin258 :
    ∀ B : (Fin 2 → Fin 2) → ℕ,
      IsFeasibleSpectrum (by decide : 0 < 6) S255 B →
      B ≠ B1 →
      likProduct E255 B B1 < likProduct E255 B1 B1 := by
  intro B hB hne
  rcases (feasibleSpectrum_iff_258 B).mp hB with h | h | h | h
  · exact False.elim (hne h)
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-- For one read of each of AA, AB, BB, BA, the truth ties B4 at the
global maximum, with all other feasible spectra no better. -/
theorem fixedX_top_tie_at_xTie258 :
    likProduct E255 B1 xTie258 = likProduct E255 B4 xTie258 ∧
    ∀ B : (Fin 2 → Fin 2) → ℕ,
      IsFeasibleSpectrum (by decide : 0 < 6) S255 B →
      likProduct E255 B xTie258 ≤ likProduct E255 B1 xTie258 := by
  constructor
  · decide
  · intro B hB
    rcases (feasibleSpectrum_iff_258 B).mp hB with h | h | h | h
    · rw [h]
    · rw [h]; decide
    · rw [h]; decide
    · rw [h]; decide

/-- At sample x=B4 (still supported entirely on the truth's windows),
B4 strictly beats the true genome's spectrum. -/
theorem fixedX_strict_loss_at_xLose258 :
    likProduct E255 B1 B4 < likProduct E255 B4 B4 := by
  decide

#print axioms fixedX_unique_at_xWin258
#print axioms fixedX_top_tie_at_xTie258
#print axioms fixedX_strict_loss_at_xLose258

end AssemblyP1.FixedXExactML
