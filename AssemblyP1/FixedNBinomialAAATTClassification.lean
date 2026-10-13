import Mathlib

/-!
# Fixed-N product-binomial maximality classification for AAATT (#259)

This module kernel-checks the fixed-`x` maximality classification for the
MB09 §6.1 fixed-external-N product-binomial objective at the concrete
bidirected instance:

* alphabet `{A, T}` with reverse-complement collapse;
* true circular genome `S = AAATT` (`G = 5`);
* read length `L = 3`;
* observed placements: start `0` twice, start `1` once, start `4` once
  (`n = 4` reads);
* molecule-type counts `x = {AAA:2, AAT:1, TAA:1}`;
* external known genome size `N = 5`.

The truth spectrum is `d_S = {AAA:1, AAT:2, TAA:2}`.
The same-length competitor `D = AAAAT` has spectrum
`d_D = {AAA:2, AAT:1, ATA:1, TAA:1}`.

The competitor's bidirected read-overlap graph walk uses the `AAA → AAA`
self-overlap (the length-2 suffix `AA` of `AAA` equals the length-2 prefix
`AA` of `AAA`), enabling two copies of the `AAA` molecule.

**Classification:** At this fixed observation `x`, the truth `S = AAATT` is
**not** an ML maximizer under the product-binomial objective. The competitor
`D = AAAAT` has strictly higher score, with exact ratio `65536/50625 > 1`.

This is a concrete instance of the #259(A) fixed-`x` classification: the
product-binomial's extra `(N - d_i)^{n - x_i}` factors (including zero-count
coordinates) break the coordinatewise-dominance sufficiency that holds for
the exact multinomial (#256).

Scope. This file is about this finite bidirected instance only. It does not
settle the general fixed-`x` classification, the sample-uniform classification
(#259(B)), or the general bidirected flow candidate universe (#260–#261).
-/

namespace AssemblyP1.FixedNBinomialAAATTClassification

/-! ## The bidirected molecule-class framework -/

/-- Two-symbol alphabet; the reverse-complement involution is `A ↔ T`. -/
inductive Base where
  | A
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.T}
  complete := by intro x; cases x <;> simp

/-- DNA reverse complement on the two-symbol alphabet. -/
def comp : Base → Base
  | .A => .T
  | .T => .A

/-- A length-`3` read type / window. -/
abbrev W3 := Fin 3 → Base

/-- Bit encoding of a symbol (`A ↦ 0`, `T ↦ 1`). -/
def bitA : Base → Nat
  | .A => 0
  | .T => 1

/-- Binary code of a length-`3` word, in `[0, 8)`. -/
def code (w : W3) : Nat := bitA (w 0) * 4 + bitA (w 1) * 2 + bitA (w 2)

/-- Reverse complement of a length-`3` word. -/
def rc (w : W3) : W3 := ![comp (w 2), comp (w 1), comp (w 0)]

lemma code_lt (w : W3) : code w < 8 := by
  have h0 : bitA (w 0) ≤ 1 := by cases w 0 <;> decide
  have h1 : bitA (w 1) ≤ 1 := by cases w 1 <;> decide
  have h2 : bitA (w 2) ≤ 1 := by cases w 2 <;> decide
  unfold code
  omega

/-- Molecule class of a word: the smaller of its own code and the code of its
reverse complement.  This is the `Fin 8` label of the reverse-complement pair.
The four molecule classes are at indices `0` (AAA/TTT), `1` (AAT/ATT),
`2` (ATA/TAT), `4` (TAA/TTA). -/
def cls (w : W3) : Fin 8 :=
  ⟨min (code w) (code (rc w)), Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (code_lt w)⟩

/-! ## The genomes -/

/-- The true circular genome `AAATT` of length `5`. -/
def truth : Fin 5 → Base := ![.A, .A, .A, .T, .T]

/-- The same-length competitor `AAAAT` of length `5`. -/
def competitor : Fin 5 → Base := ![.A, .A, .A, .A, .T]

/-- Circular symbol access for a length-`5` genome. -/
def cyc5 (g : Fin 5 → Base) (i : Nat) : Base :=
  g ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Length-`3` circular window at start `r` of a length-`5` genome. -/
def window5 (g : Fin 5 → Base) (r : Fin 5) : W3 :=
  ![cyc5 g r.val, cyc5 g (r.val + 1), cyc5 g (r.val + 2)]

/-- Number of starts of a length-`5` genome whose window has molecule class `c`. -/
def spec5 (g : Fin 5 → Base) (c : Fin 8) : Nat :=
  (Finset.univ.filter (fun r : Fin 5 => cls (window5 g r) = c)).card

/-- Truth-induced spectrum `d_S`. -/
def dS (c : Fin 8) : Nat := spec5 truth c

/-- Competitor spectrum `d_D`. -/
def dD (c : Fin 8) : Nat := spec5 competitor c

/-! ## The observation -/

/-- The realized read multiset: start `0` twice, start `1` once, start `4` once. -/
def reads : List (Fin 5) := [0, 0, 1, 4]

/-- Observed molecule-class counts `x`. -/
def obs (c : Fin 8) : Nat :=
  (reads.filter (fun r => cls (window5 truth r) = c)).length

/-! ## Spectra and observation values -/

theorem dS_eq :
    dS 0 = 1 ∧ dS 1 = 2 ∧ dS 2 = 0 ∧ dS 3 = 0 ∧
      dS 4 = 2 ∧ dS 5 = 0 ∧ dS 6 = 0 ∧ dS 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold dS spec5 window5 cyc5 cls code rc bitA comp truth <;> decide

theorem dD_eq :
    dD 0 = 2 ∧ dD 1 = 1 ∧ dD 2 = 1 ∧ dD 3 = 0 ∧
      dD 4 = 1 ∧ dD 5 = 0 ∧ dD 6 = 0 ∧ dD 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold dD spec5 window5 cyc5 cls code rc bitA comp competitor <;> decide

theorem obs_eq :
    obs 0 = 2 ∧ obs 1 = 1 ∧ obs 2 = 0 ∧ obs 3 = 0 ∧
      obs 4 = 1 ∧ obs 5 = 0 ∧ obs 6 = 0 ∧ obs 7 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    unfold obs reads window5 cyc5 cls code rc bitA comp truth <;> decide

theorem n_total : ∑ c : Fin 8, obs c = 4 := by
  decide

/-! ## The product-binomial numerator -/

/-- The candidate-dependent integer numerator of the product of binomial
marginals, with fixed external `N`.  Zero-count factors are retained:
types with `x_i = 0` contribute `(N - d_i)^n`, and `0^0 = 1` over `Nat`. -/
def binomNumerator (N n : ℕ) (d x : Fin 8 → ℕ) : ℕ :=
  ∏ c : Fin 8, (d c) ^ (x c) * (N - d c) ^ (n - x c)

/-- The normalized product-binomial score (including binomial coefficients),
as an exact rational. -/
def binomLik (N n : ℕ) (d x : Fin 8 → ℕ) : ℚ :=
  (∏ c : Fin 8,
    ((Nat.choose n (x c) : ℚ) *
      ((d c : ℚ) / (N : ℚ)) ^ (x c) *
      (1 - (d c : ℚ) / (N : ℚ)) ^ (n - x c)))

/-! ## The AAA → AAA self-overlap walk certificate -/

/-- The length-`2` prefix of a length-`3` word. -/
def prefix2 (w : W3) : Fin 2 → Base := ![w 0, w 1]

/-- The length-`2` suffix of a length-`3` word. -/
def suffix2 (w : W3) : Fin 2 → Base := ![w 1, w 2]

/-- The molecule-class vertex set for this instance: the four classes with
positive spectrum in either candidate. -/
def vertices : Finset (Fin 8) := {0, 1, 2, 4}

/-- Two molecule classes `u` and `v` are connected by a bidirected overlap
edge if there exists a word `w` in class `u` and a word `w'` in class `v`
such that the length-`(L-1)` suffix of `w` equals the length-`(L-1)` prefix
of `w'`.  This is the MB09 §6.2 non-spelled flow edge relation. -/
def overlapEdge (u v : Fin 8) : Prop :=
  ∃ w w' : W3, cls w = u ∧ cls w' = v ∧ suffix2 w = prefix2 w'

/-- The `AAA → AAA` self-overlap: the length-2 suffix `AA` of `AAA` equals
the length-2 prefix `AA` of `AAA`.  This is the walk mechanism that allows
the competitor `D = AAAAT` to carry two copies of the `AAA` molecule. -/
theorem aaa_self_overlap : overlapEdge 0 0 := by
  refine ⟨![.A, .A, .A], ![.A, .A, .A], ?_, ?_, ?_⟩
  · unfold cls code rc bitA comp; decide
  · unfold cls code rc bitA comp; decide
  · unfold suffix2 prefix2; decide

/-- The competitor's walk: `AAA → AAA → AAT → ATA → TAA → (back to AAA)`.
Each consecutive pair is a valid bidirected overlap edge, and the vertex
throughputs equal `d_D`. -/
def walkD : List (Fin 8) := [0, 0, 1, 2, 4]

/-- The walk is a circuit: it starts and ends at the same vertex. -/
theorem walkD_isCircuit : walkD.head? = walkD.getLast? := by
  unfold walkD; decide

/-- The walk visits each molecule class exactly `d_D` times. -/
theorem walkD_counts : ∀ c : Fin 8, walkD.count c = dD c := by
  intro c
  by_cases hc : c = 0
  · subst hc; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
  · by_cases hc : c = 1
    · subst hc; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
    · by_cases hc : c = 2
      · subst hc; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
      · by_cases hc : c = 4
        · subst hc; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
        · have : c ∉ walkD := by
            unfold walkD; simp [hc]
          by_cases h0 : c = 3
          · subst h0; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
          · by_cases h0 : c = 5
            · subst h0; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
            · by_cases h0 : c = 6
              · subst h0; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide
              · have : c = 7 := by
                  have h1 : c ≠ 0 := hc
                  have h2 : c ≠ 1 := hc
                  have h3 : c ≠ 2 := hc
                  have h4 : c ≠ 4 := hc
                  have h5 : c ≠ 3 := h0
                  have h6 : c ≠ 5 := h0
                  have h7 : c ≠ 6 := h0
                  have : c < 8 := c.isLt
                  fin_cases c <;> simp_all
                subst this; unfold walkD dD spec5 window5 cyc5 cls code rc bitA comp competitor; decide

/-- Every consecutive pair in the walk is a valid bidirected overlap edge. -/
theorem walkD_edges_valid :
    ∀ i : Fin (walkD.length - 1), overlapEdge (walkD.natGet i.val) (walkD.natGet (i.val + 1)) := by
  intro i
  fin_cases i
  · unfold walkD overlapEdge; refine ⟨![.A, .A, .A], ![.A, .A, .A], ?_, ?_, ?_⟩ <;>
      · unfold cls code rc bitA comp; decide
      · unfold cls code rc bitA comp; decide
      · unfold suffix2 prefix2; decide
  · unfold walkD overlapEdge; refine ⟨![.A, .A, .A], ![.A, .A, .T], ?_, ?_, ?_⟩ <;>
      · unfold cls code rc bitA comp; decide
      · unfold cls code rc bitA comp; decide
      · unfold suffix2 prefix2; decide
  · unfold walkD overlapEdge; refine ⟨![.A, .A, .T], ![.A, .T, .A], ?_, ?_, ?_⟩ <;>
      · unfold cls code rc bitA comp; decide
      · unfold cls code rc bitA comp; decide
      · unfold suffix2 prefix2; decide
  · unfold walkD overlapEdge; refine ⟨![.A, .T, .A], ![.T, .A, .A], ?_, ?_, ?_⟩ <;>
      · unfold cls code rc bitA comp; decide
      · unfold cls code rc bitA comp; decide
      · unfold suffix2 prefix2; decide
  · unfold walkD overlapEdge; refine ⟨![.T, .A, .A], ![.A, .A, .A], ?_, ?_, ?_⟩ <;>
      · unfold cls code rc bitA comp; decide
      · unfold cls code rc bitA comp; decide
      · unfold suffix2 prefix2; decide

/-- The `AAA → AAA` self-overlap is used in the competitor's walk. -/
theorem walkD_uses_aaa_self_overlap :
    walkD.natGet 1 = 0 ∧ walkD.natGet 2 = 0 ∧ overlapEdge 0 0 := by
  refine ⟨rfl, rfl, aaa_self_overlap⟩

/-! ## The product-binomial score comparison -/

/-- The product-binomial numerator for the truth at this observation. -/
theorem binomNumerator_truth : binomNumerator 5 4 dS obs = 16 * 54 * 54 * 625 ^ 5 := by
  unfold binomNumerator
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n_total]
  norm_num

/-- The product-binomial numerator for the competitor at this observation. -/
theorem binomNumerator_competitor : binomNumerator 5 4 dD obs = 36 * 64 * 256 * 64 * 625 ^ 4 := by
  unfold binomNumerator
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n_total]
  norm_num

/-- The ratio of competitor to truth product-binomial numerators. -/
theorem binomNumerator_ratio :
    binomNumerator 5 4 dD obs / binomNumerator 5 4 dS obs = 65536 / 50625 := by
  rw [binomNumerator_truth, binomNumerator_competitor]
  norm_num

/-- The competitor's product-binomial numerator is strictly greater. -/
theorem competitor_numerator_strictly_better :
    binomNumerator 5 4 dS obs < binomNumerator 5 4 dD obs := by
  rw [binomNumerator_truth, binomNumerator_competitor]
  norm_num

/-- The full normalized binomial likelihood for the truth. -/
theorem binomLik_truth : binomLik 5 4 dS obs = 46656 / 50625 ^ 4 * 625 ^ 5 * 6 / 64 := by
  unfold binomLik
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dS_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n_total]
  norm_num

/-- The full normalized binomial likelihood for the competitor. -/
theorem binomLik_competitor : binomLik 5 4 dD obs = 36 * 64 * 256 * 64 * 625 ^ 4 / 50625 ^ 4 := by
  unfold binomLik
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := obs_eq
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, g0, g1, g2, g3, g4, g5, g6, g7, n_total]
  norm_num

/-- The binomial-likelihood ratio for competitor over truth. -/
theorem binom_ratio : binomLik 5 4 dD obs / binomLik 5 4 dS obs = 65536 / 50625 := by
  rw [binomLik_truth, binomLik_competitor]
  norm_num

/-- The competitor strictly beats the truth under the product-binomial
objective with external known `N = 5`. -/
theorem competitor_strictly_better_binom :
    binomLik 5 4 dS obs < binomLik 5 4 dD obs := by
  rw [binomLik_truth, binomLik_competitor]
  norm_num

/-! ## The maximality classification -/

/-- **The fixed-`x` maximality classification for AAATT.**

At the fixed observation `x = {AAA:2, AAT:1, TAA:1}` (`n = 4`, `N = 5`),
the truth `S = AAATT` is **not** an ML maximizer under the MB09 §6.1
fixed-external-N product-binomial objective. The same-length competitor
`D = AAAAT` — realized by the bidirected read-overlap graph walk
`AAA → AAA → AAT → ATA → TAA → (back to AAA)` — has strictly higher
product-binomial score, with exact ratio `65536/50625 > 1`.

The mechanism is the `AAA → AAA` self-overlap: the length-2 suffix `AA` of
`AAA` equals the length-2 prefix `AA` of `AAA`, allowing the competitor to
carry two copies of the `AAA` molecule.  This shifts mass from `AAT` and
`TAA` to `AAA`, which is favored because `AAA` has the highest observation
count `x(AAA) = 2`.

The product-binomial's extra `(N - d_i)^{n - x_i}` factors — including the
zero-count coordinate `ATA` in the competitor — break the coordinatewise
dominance that would suffice for the exact multinomial (#256).  Here
`d_D(ATA) = 1 > 0 = d_S(ATA)`, but the factor `(5-1)^4 = 256` for this
zero-observed coordinate contributes positively to the competitor's score. -/
theorem aaatt_not_maximizer_fixed_x :
    ¬ (∀ d : Fin 8 → ℕ, (∀ c, d c ≤ 5) →
        binomLik 5 4 d obs ≤ binomLik 5 4 dS obs) := by
  intro h
  have := h dD (by
    intro c
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
    fin_cases c <;> simp_all)
  rw [binomLik_truth, binomLik_competitor] at this
  norm_num at this

/-- **Classification summary.**  The truth `S = AAATT` is not a fixed-`x`
ML maximizer; the competitor `D = AAAAT` provides a strict improvement with
exact rational ratio `65536/50625`. -/
theorem aaatt_classification :
    (∃ d : Fin 8 → ℕ, (∀ c, d c ≤ 5) ∧
      binomLik 5 4 dS obs < binomLik 5 4 d d obs) := by
  refine ⟨dD, ?_, ?_⟩
  · intro c
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := dD_eq
    fin_cases c <;> simp_all
  · rw [binomLik_truth, binomLik_competitor]
    norm_num

end AssemblyP1.FixedNBinomialAAATTClassification
