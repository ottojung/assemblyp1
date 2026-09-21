import Mathlib

/-!
# Issue #48: free-length counterexample under candidate-intrinsic admissibility

This file kernel-checks the decisive finite instance refuting the issue-#48
"repaired" finite theorem: with the exact Medvedev–Brudno read-count
multinomial over candidates of **arbitrary length**, the truth need not be
maximum-likelihood even when the competitor is required to be primitive and to
satisfy the strongest candidate-intrinsic repeat condition.

Scope and conventions (exactly those of
`docs/issue48-finite-intrinsic-negative.md`):

* single-strand oriented reads of length `L = 3`, no reverse-complement
  collapse;
* free candidate length: the likelihood uses each candidate's own length
  `N(D) = D.length`, so the length factor `G / N(D)` is present;
* observed read multiset `{AAB, BAA}` (one each), realized on the truth at
  starts `0, 3`;
* truth `S = AABB` (`G = 4`), competitor `D = AAB` (`n = 3`);
* intrinsic condition `Strong D 3`: no length-`(L-1) = 2` window of `D` occurs
  twice;
* `IsPrimitive D`: `D` is not a nontrivial power `w^m`, `m ≥ 2`.

The kernel-checked facts are:

* `Covers truth 3`: the realized reads at starts `0, 3` cover the truth;
* `NoTripleRepeat truth`: the truth has no Bresler triple repeat;
* `Strong truth 3` and `Strong competitor 3`;
* `IsPrimitive truth` and `IsPrimitive competitor`;
* `likelihood truth < likelihood competitor`, with exact rationals `1/16 < 1/9`.

The remaining conjunct of the source `I_s` hypothesis for this instance is the
absence of interleaved repeat pairs. It is vacuous here: the only maximal repeat
pairs of `AABB` are the length-`1` pairs `A@(0,1)` and `B@(2,3)`, whose four
starts `0,1,2,3` carry labels `A,A,B,B` and therefore do not alternate. That
finite check, together with the strict `I_s` check for the non-vacuous witness,
is performed by `scripts/verify_issue48_intrinsic_admissibility.py`; it is not
re-formalized here to avoid introducing general repeat/interleaving
infrastructure, following the precedent of
`AssemblyP1/FixedLengthExactCounterexample.lean`.

This file does **not** settle the source-ambiguous Shomorony et al. open
question. It refutes one explicitly additional free-length repaired formulation.
-/

namespace AssemblyP1.Issue48

/-- Three-symbol alphabet (only `A`, `B` occur in the witness). -/
inductive Base where
  | A
  | B
  | C
  deriving DecidableEq, Repr, Inhabited

open Base

/-- Circular length-`L` window of a candidate `D` beginning at start `t`. -/
def win (D : List Base) (L t : Nat) : List Base :=
  (List.range L).map fun j => D.getD ((t + j) % D.length) Base.A

/-- Number of circular length-`w.length` windows of `D` equal to `w`. -/
def occ (D : List Base) (w : List Base) : Nat :=
  ((List.range D.length).filter fun t => win D w.length t = w).length

/-- Exact Medvedev–Brudno read-count likelihood for the observed multiset
`{AAB, BAA}`, with candidate-intrinsic length `N(D) = D.length`. -/
def likelihood (D : List Base) : ℚ :=
  (occ D [A, A, B] : ℚ) / D.length * ((occ D [B, A, A] : ℚ) / D.length)

/-- The true circular genome `S = AABB` (length `4`). -/
def truth : List Base := [A, A, B, B]

/-- The shorter competitor `D = AAB` (length `3`). -/
def competitor : List Base := [A, A, B]

/-- `D` is a power of a word of length `p`. -/
def IsPower (D : List Base) (p : Nat) : Prop :=
  p ∣ D.length ∧ D = (List.replicate (D.length / p) (D.take p)).flatten

/-- `D` is primitive: not a nontrivial power `w^m`, `m ≥ 2`. -/
def IsPrimitive (D : List Base) : Prop :=
  ∀ p : Fin D.length, p.val ∣ D.length → ¬ IsPower D p.val

/-- No `(L-1)`-window of `D` occurs twice (the `STRONG` intrinsic condition). -/
def Strong (D : List Base) (L : Nat) : Prop :=
  ∀ i j : Fin D.length, i ≠ j → win D (L - 1) i.val ≠ win D (L - 1) j.val

/-- Realized read start positions. -/
def readStarts : List Nat := [0, 3]

/-- The realized reads cover `S`. -/
def Covers (S : List Base) (L : Nat) : Prop :=
  ∀ p : Fin S.length, ∃ i : Fin readStarts.length, ∃ d : Fin L,
    p.val = (readStarts[i.val] + d.val) % S.length

/-- Symbol immediately preceding position `t` on the circle. -/
def prev (D : List Base) (t : Nat) : Base :=
  D.getD ((t + D.length - 1) % D.length) Base.A

/-- Symbol immediately following the length-`ell` window at `t`. -/
def follow (D : List Base) (t ell : Nat) : Base :=
  D.getD ((t + ell) % D.length) Base.A

/-- Bresler triple repeat: three equal length-`ell` windows with the three-copy
maximality condition. -/
def IsTripleRepeat (D : List Base) (ell : Nat) (t1 t2 t3 : Fin D.length) : Prop :=
  t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
  win D ell t1.val = win D ell t2.val ∧ win D ell t2.val = win D ell t3.val ∧
  ¬ (prev D t1.val = prev D t2.val ∧ prev D t2.val = prev D t3.val) ∧
  ¬ (follow D t1.val ell = follow D t2.val ell ∧
     follow D t2.val ell = follow D t3.val ell)

/-- The truth has no triple repeat of any positive length. -/
def NoTripleRepeat (D : List Base) : Prop :=
  ∀ e : Fin D.length, 1 ≤ e.val →
    ∀ t1 t2 t3 : Fin D.length, ¬ IsTripleRepeat D e.val t1 t2 t3

theorem occ_truth_AAB : occ truth [A, A, B] = 1 := by decide

theorem occ_truth_BAA : occ truth [B, A, A] = 1 := by decide

theorem occ_competitor_AAB : occ competitor [A, A, B] = 1 := by decide

theorem occ_competitor_BAA : occ competitor [B, A, A] = 1 := by decide

/-- Exact likelihood of the observed reads under the truth. -/
theorem likelihood_truth : likelihood truth = 1 / 16 := by
  unfold likelihood
  rw [occ_truth_AAB, occ_truth_BAA]
  norm_num [truth]

/-- Exact likelihood of the observed reads under the shorter competitor. -/
theorem likelihood_competitor : likelihood competitor = 1 / 9 := by
  unfold likelihood
  rw [occ_competitor_AAB, occ_competitor_BAA]
  norm_num [competitor]

/-- The free-length exact likelihood strictly prefers the shorter candidate. -/
theorem competitor_strictly_more_likely :
    likelihood truth < likelihood competitor := by
  rw [likelihood_truth, likelihood_competitor]
  norm_num

theorem truth_primitive : IsPrimitive truth := by
  unfold IsPrimitive IsPower
  decide

theorem competitor_primitive : IsPrimitive competitor := by
  unfold IsPrimitive IsPower
  decide

theorem truth_strong : Strong truth 3 := by unfold Strong; decide

theorem competitor_strong : Strong competitor 3 := by unfold Strong; decide

theorem truth_covers : Covers truth 3 := by unfold Covers readStarts; decide

theorem truth_no_triple : NoTripleRepeat truth := by
  unfold NoTripleRepeat IsTripleRepeat prev follow win
  decide

/--
Kernel-checked finite refutation of the issue-#48 free-length repaired theorem
in its strongest intrinsic form: the truth is primitive and `STRONG`, the
competitor is primitive and `STRONG`, and the competitor is strictly more
likely under the exact free-length Medvedev–Brudno multinomial.

The full source `I_s` certificate for this instance is coverage (checked here)
together with the absence of triple repeats (checked here) and interleaved
pairs (vacuous here; see the module docstring and the verification script).
-/
theorem issue48_free_length_counterexample :
    Covers truth 3 ∧ NoTripleRepeat truth ∧
      Strong truth 3 ∧ IsPrimitive truth ∧
      Strong competitor 3 ∧ IsPrimitive competitor ∧
      likelihood truth < likelihood competitor :=
  ⟨truth_covers, truth_no_triple, truth_strong, truth_primitive,
    competitor_strong, competitor_primitive, competitor_strictly_more_likely⟩

end AssemblyP1.Issue48
