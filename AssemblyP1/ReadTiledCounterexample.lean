import Mathlib

/-!
# Read-tiled (flow-feasible) fixed-length exact counterexample

This file kernel-checks a finite instance showing that the source-faithful
information-feasible hypothesis `I_s` does **not** force the true sequence to be
an exact maximum-likelihood sequence even after adding the feasibility
constraint that the competitor be *read-tiled*: its length-`L` window multiset
equals the observed read multiset.  Read-tiling is the candidate condition
induced by the per-occurrence reading of the Medvedev–Brudno §6.2 flow (each
observed read occurrence is used by the assembly), and it implies both L-mer
support containment `supp(D) ⊆ supp(x)` and the per-occurrence lower bounds
`d_D(w) ≥ x_w`.  It is therefore a *stronger* candidate restriction than the
fixed-length exact variant checked in `FixedLengthExactCounterexample.lean`.

Instance:

* true circular genome `truth = AAABCBC` (length `G = 7`);
* read length `L = 3`, realized starts `{0, 1, 2, 5, 6}` (with the start `0`
  realized three times, giving `N = 7` reads);
* observed read multiset `{AAA:3, AAB:1, ABC:1, BCA:1, CAA:1}`;
* read-tiled competitor `competitor = AAAAABC`, whose length-`3` windows are
  exactly that multiset.

The truth has a maximal all-bridged length-`1` triple repeat (`A` at positions
`0, 1, 2`), and the realized reads cover the truth, so the kernel-checked
`SourceHypotheses` certificate is genuinely non-vacuous.  The exact
fixed-length multinomial likelihood ratio is `3^3 = 27 > 1`, so the truth is
not a maximizer even among read-tiled (hence flow-feasible, support-contained,
per-occurrence-lower-bounded) same-length candidates.

Scope.  As in the companion module, this is limited to the fixed-length exact
multinomial variant and to one finite instance.  It does not settle the
unrestricted-length objective, the binomial approximation, the source-ambiguous
Shomorony et al. open question, or the exact Medvedev–Brudno §6.2 flow model.
The interleaved-repeat conjunct of `I_s` is vacuous here; that finite check is
recorded in `docs/read-tiled-counterexample.md`.
-/

namespace AssemblyP1.ReadTiledCounterexample

/-- Four-symbol alphabet. -/
inductive Base where
  | A
  | B
  | C
  | G
  deriving DecidableEq, Inhabited, Repr

/-- A circular genome of length `7`. -/
abbrev Genome := Fin 7 → Base

/-- The `i`-th symbol of a circular genome of length `7`. -/
def cyc (g : Genome) (i : Nat) : Base :=
  g ⟨i % 7, Nat.mod_lt _ (by norm_num)⟩

/-- The length-`3` circular window of `g` beginning at start `r`. -/
def window (g : Genome) (r : Fin 7) : Fin 3 → Base :=
  fun d => cyc g (r.val + d.val)

/-- Read type `AAA`. -/
def readAAA : Fin 3 → Base := fun _ => Base.A

/-- Read type `AAB`. -/
def readAAB : Fin 3 → Base := ![Base.A, Base.A, Base.B]

/-- Read type `ABC`. -/
def readABC : Fin 3 → Base := ![Base.A, Base.B, Base.C]

/-- Read type `BCA`. -/
def readBCA : Fin 3 → Base := ![Base.B, Base.C, Base.A]

/-- Read type `CAA`. -/
def readCAA : Fin 3 → Base := ![Base.C, Base.A, Base.A]

/-- Number of circular start positions of `g` whose length-`3` window is `w`. -/
def occ (g : Genome) (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 7 => window g r = w)).card

/-- The true circular genome `S = AAABCBC`. -/
def truth : Genome := ![Base.A, Base.A, Base.A, Base.B, Base.C, Base.B, Base.C]

/-- The read-tiled competitor `D = AAAAABC`. -/
def competitor : Genome := ![Base.A, Base.A, Base.A, Base.A, Base.A, Base.B, Base.C]

/-! ## Exact fixed-length multinomial likelihood -/

/--
Exact Medvedev–Brudno read-count multinomial likelihood of the observed
multiset `{AAA:3, AAB:1, ABC:1, BCA:1, CAA:1}` under a length-`7` circular
candidate.

The observation has `n = 7` reads with type counts `3,1,1,1,1`, so the
observation-only multinomial coefficient is `7! / (3!·1!·1!·1!·1!) = 840`, and
the candidate length is `7` for every candidate in `Genome`.  The factors are
the `(d_i / 7)^{x_i}` contributions of the observed types.
-/
def likelihood (g : Genome) : ℚ :=
  (840 : ℚ) * ((occ g readAAA : ℚ) / 7) ^ 3 * ((occ g readAAB : ℚ) / 7) *
    ((occ g readABC : ℚ) / 7) * ((occ g readBCA : ℚ) / 7) *
    ((occ g readCAA : ℚ) / 7)

theorem occ_truth_AAA : occ truth readAAA = 1 := by decide
theorem occ_truth_AAB : occ truth readAAB = 1 := by decide
theorem occ_truth_ABC : occ truth readABC = 1 := by decide
theorem occ_truth_BCA : occ truth readBCA = 1 := by decide
theorem occ_truth_CAA : occ truth readCAA = 1 := by decide

theorem occ_competitor_AAA : occ competitor readAAA = 3 := by decide
theorem occ_competitor_AAB : occ competitor readAAB = 1 := by decide
theorem occ_competitor_ABC : occ competitor readABC = 1 := by decide
theorem occ_competitor_BCA : occ competitor readBCA = 1 := by decide
theorem occ_competitor_CAA : occ competitor readCAA = 1 := by decide

/-- Exact likelihood of the observed reads under the truth. -/
theorem likelihood_truth : likelihood truth = 840 / 7 ^ 7 := by
  unfold likelihood
  rw [occ_truth_AAA, occ_truth_AAB, occ_truth_ABC, occ_truth_BCA, occ_truth_CAA]
  norm_num

/-- Exact likelihood of the observed reads under the competitor. -/
theorem likelihood_competitor : likelihood competitor = 840 * 27 / 7 ^ 7 := by
  unfold likelihood
  rw [occ_competitor_AAA, occ_competitor_AAB, occ_competitor_ABC,
    occ_competitor_BCA, occ_competitor_CAA]
  norm_num

/-- The exact likelihood ratio is `27 = 3^3`. -/
theorem likelihood_ratio : likelihood competitor / likelihood truth = 27 := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

/-! ## Read-tiling (the source-faithful feasibility constraint) -/

/--
`ReadTiled g` holds when the length-`3` window multiset of `g` is exactly the
observed read multiset `{AAA:3, AAB:1, ABC:1, BCA:1, CAA:1}`.  Because the
counts sum to `7 = |g|`, any genome satisfying these five equations has no
other window type, so `ReadTiled` is precisely the condition `d_g = x`.

This is the strongest candidate restriction considered here: a read-tiled
candidate is flow-feasible in the per-occurrence reading of §6.2, is
support-contained, and obeys the per-occurrence lower bounds `d_g(w) ≥ x_w`.
-/
def ReadTiled (g : Genome) : Prop :=
  occ g readAAA = 3 ∧ occ g readAAB = 1 ∧ occ g readABC = 1 ∧
    occ g readBCA = 1 ∧ occ g readCAA = 1

/-- The competitor is read-tiled. -/
theorem competitor_read_tiled : ReadTiled competitor := by
  unfold ReadTiled
  exact ⟨occ_competitor_AAA, occ_competitor_AAB, occ_competitor_ABC,
    occ_competitor_BCA, occ_competitor_CAA⟩

/-- The truth is not read-tiled: it contains `AAA` only once. -/
theorem truth_not_read_tiled : ¬ ReadTiled truth := by
  intro h
  have hAAA : occ truth readAAA = 3 := h.1
  rw [occ_truth_AAA] at hAAA
  norm_num at hAAA

/-- Maximum-likelihood predicate *among read-tiled candidates only*. -/
def IsMaximumLikelihoodAmongReadTiled (g : Genome) : Prop :=
  ∀ candidate : Genome, ReadTiled candidate → likelihood candidate ≤ likelihood g

/--
The read-tiled competitor strictly beats the truth, so the truth is not an
exact maximum-likelihood maximizer even among read-tiled (hence
flow-feasible, support-contained, per-occurrence-lower-bounded) same-length
candidates.
-/
theorem truth_not_maximum_likelihood_even_read_tiled :
    ¬ IsMaximumLikelihoodAmongReadTiled truth := by
  intro h
  have hcomp := h competitor competitor_read_tiled
  rw [likelihood_truth, likelihood_competitor] at hcomp
  norm_num at hcomp

/-! ## Source-faithful `I_s` certificate for the instance -/

/-- The realized read start positions (as a set; start `0` has multiplicity 3). -/
def readStarts : Finset (Fin 7) := {0, 1, 2, 5, 6}

/-- Coverage: the realized length-`3` reads cover all seven circular positions. -/
def Covers : Prop :=
  ∀ p : Fin 7, ∃ r ∈ readStarts, ∃ d : Fin 3, p.val = (r.val + d.val) % 7

/-- The realized reads cover the truth. -/
theorem truth_covered : Covers := by
  unfold Covers
  decide

/--
Concrete source-faithful triple-repeat certificate: the length-`1` windows at
starts `0, 1, 2` are equal (`A`), the three-copy maximality condition holds
(the preceding symbols `C, A, A` are not all equal and the following symbols
`A, A, B` are not all equal), and every one of the three copies is bridged by a
realized read: the read at `6` bridges copy `0`, the read at `0` bridges copy
`1`, and the read at `1` bridges copy `2`.

Bridging a length-`1` copy at `t` by a length-`3` read starting at `r` means
`t = r + 1` (mod `7`), i.e. the copy is strictly interior to the read, as
required by the strict-extension source convention.
-/
def TripleRepeatAllBridged (g : Genome) : Prop :=
  g 0 = g 1 ∧ g 1 = g 2 ∧
  ¬(g 6 = g 0 ∧ g 0 = g 1) ∧
  ¬(g 1 = g 2 ∧ g 2 = g 3) ∧
  (∀ t : Fin 7, (t.val = 0 ∨ t.val = 1 ∨ t.val = 2) →
    ∃ r ∈ readStarts, (r.val + 1) % 7 = t.val)

/-- The concrete triple-repeat certificate holds for the truth. -/
theorem truth_triple_repeat_all_bridged : TripleRepeatAllBridged truth := by
  unfold TripleRepeatAllBridged
  decide

/--
The instance-specific part of the source-faithful `I_s` hypothesis that is
kernel-checked here: coverage plus the maximal, all-bridged length-`1` triple
repeat.  Absence of interleaved repeat pairs for this instance is recorded in
`docs/read-tiled-counterexample.md`.
-/
def SourceHypotheses (g : Genome) : Prop :=
  Covers ∧ TripleRepeatAllBridged g

/-- The truth satisfies the kernel-checked `I_s` certificate. -/
theorem truth_source_hypotheses : SourceHypotheses truth :=
  ⟨truth_covered, truth_triple_repeat_all_bridged⟩

/-! ## Main finite theorem -/

/--
Kernel-checked finite counterexample to the fixed-length exact-multinomial
variant **with the added read-tiling feasibility constraint**: the concrete
instance satisfies the source-faithful coverage and all-bridged-triple-repeat
certificate, the competitor is read-tiled (hence flow-feasible, support-contained,
and per-occurrence-lower-bounded), yet the true sequence is not a
maximum-likelihood assembly among such candidates.

This theorem is deliberately limited to the fixed-length exact multinomial
variant, to the read-tiling feasibility reading, and to this finite instance.
It does not settle the source-ambiguous Shomorony et al. open question.
-/
theorem read_tiled_counterexample :
    SourceHypotheses truth ∧ ReadTiled competitor ∧
      ¬ IsMaximumLikelihoodAmongReadTiled truth :=
  ⟨truth_source_hypotheses, competitor_read_tiled,
    truth_not_maximum_likelihood_even_read_tiled⟩

end AssemblyP1.ReadTiledCounterexample
