import Mathlib
import AssemblyP1.SourceFaithfulIs

/-!
# Issue #209 audit: E/A strict witnesses and the `N`-parameter boundary

This module is the kernel-checked residue of the issue #209 audit
(`docs/issue-209-ea-audit-ledger.md`).  It is deliberately *not* a
re-statement of the modules it audits: every definition below is written
locally, so that agreement with
`AssemblyP1.ExactVariantECounterexample`,
`AssemblyP1.FixedLengthExactCounterexample` and
`AssemblyP1.FixedLengthBinomialCounterexample` is an independent check
rather than a shared symbol.

Three things are proved, one per theorem block.

1. **The `AAABB → AAAAB` witness refutes the fixed-`N` product-of-binomial-
   marginals objective as well as the exact multinomial objective.**
   `docs/fixed-length-exact-counterexample.md` states that the `AAABB`
   witness does not refute the Medvedev–Brudno separable/binomial
   approximation.  Under the *literal* Section 6.1 approximation — the
   product over the whole read-type space, which retains every
   `(1 - d_w/N)^n` factor of an unobserved read type — the same witness has
   the same likelihood ratio `1125/512 > 1` as the `AAACC` witness of
   `FixedLengthBinomialCounterexample`, because the two witnesses differ only
   by a renaming of one unused symbol.  The ratio is recomputed here from a
   locally written objective.

2. **The multiplicity bound `d_w ≤ N(D)`, and the boundary of the external-`N`
   objective.**  For any circular candidate `D` and read type `w`, the
   occurrence multiplicity satisfies `d_w ≤ N(D)`.  The literal binomial
   marginal `Binom(n, x) (d/N)^x (1 - d/N)^(n-x)` is a probability only when
   `d ≤ N`.  Hence an external fixed `N` restricts the admissible candidate
   class to `|D| ≤ N`; it is *not* implied by "the genome length is a known
   constant".  Block 3 exhibits a length-`6` candidate for which the literal
   marginal with `N = 5` is negative, so the objective is not a likelihood
   outside that class.

3. **The `I_s` certificate of block 1 is the full source-faithful predicate**,
   `SourceFaithfulIs.InformationFeasible`, discharged by computation over
   every admissible repeat length and every selection of starts — not a
   hand-listed repeat.

Scope.  Nothing here speaks to the Section 6.2 flow feasible set, to which
candidate class the published 2016 question quantifies, or to the tie
semantics of "the maximum-likelihood sequence".
-/

namespace AssemblyP1.Issue209EAudit

open SourceFaithfulIs

/-- The four-symbol alphabet used by the audited witness modules. -/
inductive Base where
  | A
  | B
  | C
  | G
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.B, Base.C, Base.G}
  complete := by intro x; cases x <;> simp

/-! ## The instances, as shared-layer circular genomes -/

/-- The true circular genome `S = AAABB` (length `5`). -/
abbrev aaabGenome : Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.B, Base.B]

/-- The same-length competitor `D = AAAAB` (length `5`). -/
abbrev aaaabGenome : Genome Base where
  len := 5
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.A, Base.B]

/-- A length-`6` circular genome, used only for the domain check. -/
abbrev aaaaaaGenome : Genome Base where
  len := 6
  len_pos := by norm_num
  sym := ![Base.A, Base.A, Base.A, Base.A, Base.A, Base.A]

/-- Read type `AAA`. -/
def readAAA : Fin 3 → Base := fun _ => Base.A

/-- Read type `AAB`. -/
def readAAB : Fin 3 → Base := ![Base.A, Base.A, Base.B]

/-- Read type `BAA`. -/
def readBAA : Fin 3 → Base := ![Base.B, Base.A, Base.A]

/-- Read type `ABB` (unobserved, multiplicity one in `AAABB`). -/
def readABB : Fin 3 → Base := ![Base.A, Base.B, Base.B]

/-- Read type `BBA` (unobserved, multiplicity one in `AAABB`). -/
def readBBA : Fin 3 → Base := ![Base.B, Base.B, Base.A]

/-- Read type `ABA` (unobserved, multiplicity one in `AAAAB`). -/
def readABA : Fin 3 → Base := ![Base.A, Base.B, Base.A]

/-- Occurrence multiplicity `d_w`: the number of circular starts of `g` whose
length-`L` window is the read type `w`.  This is the `d_i` of Medvedev-Brudno
Section 6.1, computed for a candidate of *any* intrinsic length. -/
def winCount {α : Type} [DecidableEq α] (g : Genome α) (L : ℕ)
    (w : Fin L → α) : ℕ :=
  (Finset.univ.filter (fun r : Fin g.len => g.window L r = w)).card

/-! ## The literal fixed-`N` binomial marginal and the objective -/

/-- The literal Section 6.1 binomial marginal for one read type, with the
*fixed external* genome length `N`, total read count `n`, observed count `x`
and candidate multiplicity `d`:

`Binom(n, x) (d/N)^x (1 - d/N)^(n-x)`.

The `(1 - d/N)^(n-x)` factor is retained when `x = 0`; that is what
distinguishes this from the exact multinomial, and it is the factor the
`AAABB` witness turns on. -/
def binomialMarginal (d N n x : ℕ) : ℚ :=
  (Nat.choose n x : ℚ) * ((d : ℚ) / N) ^ x * (1 - (d : ℚ) / N) ^ (n - x)

/-- Observed read counts for the `AAABB` realization: `AAA, AAB, BAA`, once
each.  Given as a function of the read type so that the objective below is a
product over the *whole* read-type space. -/
def obs (w : Fin 3 → Base) : ℕ :=
  (if w = readAAA then 1 else 0) + (if w = readAAB then 1 else 0) +
    (if w = readBAA then 1 else 0)

/-- The fixed-`N` binomial-approximation objective: the product of the
individual marginals over the entire length-`3` read-type space.  `n = 3`. -/
def likelihood (g : Genome Base) (N : ℕ) : ℚ :=
  ∏ w : Fin 3 → Base, binomialMarginal (winCount g 3 w) N 3 (obs w)

/-- The realized read placements: starts `0, 1, 4`. -/
def readStarts : Finset (Fin 5) := {0, 1, 4}

/-- The placements really produce the observation consumed by `likelihood`. -/
theorem realized_reads :
    aaabGenome.window 3 0 = readAAA ∧ aaabGenome.window 3 1 = readAAB ∧
      aaabGenome.window 3 4 = readBAA :=
  ⟨by decide, by decide, by decide⟩

/-- **Full source-faithful `I_s` membership**, discharged by computation over
every admissible repeat length and every selection of starts. -/
theorem truth_information_feasible :
    SourceFaithfulIs.InformationFeasible aaabGenome 3 readStarts := by
  unfold SourceFaithfulIs.InformationFeasible
  decide

/-! ## Reducing the whole read-type product to the six relevant types -/

/-- The six read types whose marginal is not automatically `1` for either
candidate: the three observed types, plus the three types that have positive
multiplicity in exactly one of `AAABB`, `AAAAB`. -/
def relevant : Finset (Fin 3 → Base) :=
  {readAAA, readAAB, readBAA, readABB, readBBA, readABA}

/-- Unobserved read types have observed count zero. -/
theorem obs_eq_zero_of_not_relevant (w : Fin 3 → Base) (h : w ∉ relevant) :
    obs w = 0 := by
  have h1 : w ≠ readAAA := fun heq => h (heq ▸ by simp [relevant])
  have h2 : w ≠ readAAB := fun heq => h (heq ▸ by simp [relevant])
  have h3 : w ≠ readBAA := fun heq => h (heq ▸ by simp [relevant])
  simp [obs, h1, h2, h3]

/-- Absent read types have multiplicity zero in a candidate whose whole
support lies in `relevant`. -/
theorem winCount_eq_zero_of_not_relevant {g : Genome Base}
    (w : Fin 3 → Base) (h : w ∉ relevant)
    (hsub : ∀ r : Fin g.len, g.window 3 r ∈ relevant) : winCount g 3 w = 0 := by
  rw [winCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _
  exact fun heq => h (heq ▸ hsub r)

/-- A read type that is neither observed nor present contributes factor `1`. -/
theorem marginal_eq_one (d N n : ℕ) (w : Fin 3 → Base) (hd : d = 0)
    (hx : obs w = 0) : binomialMarginal d N n (obs w) = 1 := by
  rw [hx, hd]
  simp [binomialMarginal]

/-- The whole-space product equals the product over the six relevant types. -/
theorem likelihood_eq_relevant_prod (g : Genome Base) (N : ℕ)
    (hsub : ∀ r : Fin g.len, g.window 3 r ∈ relevant) :
    likelihood g N = ∏ w ∈ relevant, binomialMarginal (winCount g 3 w) N 3 (obs w) := by
  unfold likelihood
  exact (Finset.prod_subset (s₁ := relevant) (s₂ := Finset.univ)
    (by intro x _; exact Finset.mem_univ x)
    (by
      intro w _ hw
      exact marginal_eq_one (winCount g 3 w) N 3 w
        (winCount_eq_zero_of_not_relevant w hw hsub)
        (obs_eq_zero_of_not_relevant w hw))).symm

theorem relevant_prod_eq (f : (Fin 3 → Base) → ℚ) :
    ∏ w ∈ relevant, f w =
      f readAAA * (f readAAB * (f readBAA * (f readABB *
        (f readBBA * f readABA)))) := by
  unfold relevant
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]

/-! ## Block 1: the `AAABB` witness under the fixed-`N` objective -/

theorem windows_aaab_mem_relevant :
    ∀ r : Fin 5, aaabGenome.window 3 r ∈ relevant := by decide

theorem windows_aaaab_mem_relevant :
    ∀ r : Fin 5, aaaabGenome.window 3 r ∈ relevant := by decide

theorem obs_readAAA : obs readAAA = 1 := by decide

theorem obs_readAAB : obs readAAB = 1 := by decide

theorem obs_readBAA : obs readBAA = 1 := by decide

theorem obs_zero_count (w : Fin 3 → Base) (h1 : w ≠ readAAA)
    (h2 : w ≠ readAAB) (h3 : w ≠ readBAA) : obs w = 0 := by
  simp [obs, h1, h2, h3]

theorem winCount_aaab_AAA : winCount aaabGenome 3 readAAA = 1 := by decide

theorem winCount_aaab_AAB : winCount aaabGenome 3 readAAB = 1 := by decide

theorem winCount_aaab_BAA : winCount aaabGenome 3 readBAA = 1 := by decide

theorem winCount_aaab_ABB : winCount aaabGenome 3 readABB = 1 := by decide

theorem winCount_aaab_BBA : winCount aaabGenome 3 readBBA = 1 := by decide

theorem winCount_aaab_ABA : winCount aaabGenome 3 readABA = 0 := by decide

theorem winCount_aaaab_AAA : winCount aaaabGenome 3 readAAA = 2 := by decide

theorem winCount_aaaab_AAB : winCount aaaabGenome 3 readAAB = 1 := by decide

theorem winCount_aaaab_BAA : winCount aaaabGenome 3 readBAA = 1 := by decide

theorem winCount_aaaab_ABB : winCount aaaabGenome 3 readABB = 0 := by decide

theorem winCount_aaaab_BBA : winCount aaaabGenome 3 readBBA = 0 := by decide

theorem winCount_aaaab_ABA : winCount aaaabGenome 3 readABA = 1 := by decide

/-- Exact product-of-binomial-marginals likelihood of the observation under
the truth `AAABB`, with the fixed external length `N = 5`. -/
theorem likelihood_aaab : likelihood aaabGenome 5 = 452984832 / 30517578125 := by
  rw [likelihood_eq_relevant_prod aaabGenome 5 windows_aaab_mem_relevant,
    relevant_prod_eq]
  simp only [binomialMarginal]
  rw [obs_readAAA, obs_readAAB, obs_readBAA,
    obs_zero_count readABB (by decide) (by decide) (by decide),
    obs_zero_count readBBA (by decide) (by decide) (by decide),
    obs_zero_count readABA (by decide) (by decide) (by decide),
    winCount_aaab_AAA, winCount_aaab_AAB, winCount_aaab_BAA, winCount_aaab_ABB,
    winCount_aaab_BBA, winCount_aaab_ABA]
  norm_num

/-- Exact likelihood under the competitor `AAAAB`, with `N = 5`. -/
theorem likelihood_aaaab : likelihood aaaabGenome 5 = 7962624 / 244140625 := by
  rw [likelihood_eq_relevant_prod aaaabGenome 5 windows_aaaab_mem_relevant,
    relevant_prod_eq]
  simp only [binomialMarginal]
  rw [obs_readAAA, obs_readAAB, obs_readBAA,
    obs_zero_count readABB (by decide) (by decide) (by decide),
    obs_zero_count readBBA (by decide) (by decide) (by decide),
    obs_zero_count readABA (by decide) (by decide) (by decide),
    winCount_aaaab_AAA, winCount_aaaab_AAB, winCount_aaaab_BAA,
    winCount_aaaab_ABB, winCount_aaaab_BBA, winCount_aaaab_ABA]
  norm_num

/-- The strict ratio under the fixed-`N` objective, recomputed from the local
definitions: `1125/512 > 1`. -/
theorem likelihood_ratio :
    likelihood aaaabGenome 5 / likelihood aaabGenome 5 = 1125 / 512 := by
  rw [likelihood_aaab, likelihood_aaaab]
  norm_num

/-- The competitor is strictly more likely than the truth. -/
theorem competitor_beats_truth :
    likelihood aaabGenome 5 < likelihood aaaabGenome 5 := by
  rw [likelihood_aaab, likelihood_aaaab]
  norm_num

/-- Fixed-length maximum-likelihood predicate for this fixed-`N` objective. -/
def IsMaximumLikelihood (g : Genome Base) : Prop :=
  ∀ candidate : Genome Base, candidate.len = g.len →
    likelihood candidate 5 ≤ likelihood g 5

/-- The truth is not a maximizer, even among candidates of the same length. -/
theorem truth_not_maximum_likelihood : ¬ IsMaximumLikelihood aaabGenome := by
  intro h
  have hcomp := h aaaabGenome rfl
  rw [likelihood_aaab, likelihood_aaaab] at hcomp
  norm_num at hcomp

/-- **Kernel-checked block 1.** The `AAABB -> AAAAB` witness satisfies the full
source-faithful `I_s` and refutes the fixed-`N` product-of-binomial-marginals
objective with the same likelihood ratio as the `AAACC` witness. -/
theorem aaab_refutes_fixed_N_binomial :
    SourceFaithfulIs.InformationFeasible aaabGenome 3 readStarts ∧
      ¬ IsMaximumLikelihood aaabGenome ∧
        likelihood aaaabGenome 5 / likelihood aaabGenome 5 = 1125 / 512 :=
  ⟨truth_information_feasible, truth_not_maximum_likelihood, likelihood_ratio⟩

/-! ## Block 2: `d_w ≤ N(D)`, and the boundary of an external `N` -/

/-- The occurrence multiplicity of any read type in any circular candidate is
bounded by the candidate's own length. -/
theorem winCount_le_len {α : Type} [DecidableEq α] (g : Genome α) (L : ℕ)
    (w : Fin L → α) : winCount g L w ≤ g.len := by
  have hle : (Finset.univ.filter
      (fun r : Fin g.len => g.window L r = w)).card ≤
      (Finset.univ : Finset (Fin g.len)).card := Finset.card_filter_le _ _
  have hcard : (Finset.univ : Finset (Fin g.len)).card = g.len := by simp
  simpa [winCount] using hle.trans (by rw [hcard])

/-- Consequently, on the candidate class `|D| ≤ N` the literal marginal's
`d/N` lies in `[0, 1]`: the binomial marginal is a probability there, without
any further assumption. -/
theorem binomial_marginal_probability_on_le_len {α : Type} [DecidableEq α]
    (g : Genome α) (L : ℕ) (w : Fin L → α) (N : ℕ) (hN : 0 < N) (h : g.len ≤ N) :
    (winCount g L w : ℚ) / N ≤ 1 := by
  have h1 : (winCount g L w : ℚ) ≤ g.len := by exact_mod_cast winCount_le_len g L w
  have h2 : (g.len : ℚ) ≤ N := by exact_mod_cast h
  have hN : (0 : ℚ) < N := by exact_mod_cast hN
  rw [div_le_one hN]
  linarith

/-- **The boundary.**  A length-`6` candidate with `N = 5` external: the
multiplicity of `AAA` is `6 > 5`, so the literal marginal for an *unobserved*
type is `(1 - 6/5)^3 < 0`.  The fixed-`N` objective is therefore not a
product of probabilities outside the class `|D| ≤ N`; the external parameter
`N` is not a license to score candidates of arbitrary length. -/
theorem external_N_domain_boundary :
    winCount aaaaaaGenome 3 readAAA = 6 ∧ binomialMarginal 6 5 3 0 < 0 := by
  refine ⟨by decide, ?_⟩
  simp only [binomialMarginal]
  norm_num

end AssemblyP1.Issue209EAudit
