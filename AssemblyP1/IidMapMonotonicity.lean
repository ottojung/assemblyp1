import Mathlib
import AssemblyP1.FiniteBayesDecision

/-!
# Exact iid n → n+1 MAP success monotonicity (Antonina #269)

This module instantiates the merged generic decision theorem
`AssemblyP1.FiniteBayesDecision.chooseMAP_success_monotone_under_refinement`
(PR #174) to the concrete finite iid read model, with the (n+1)-read
observation represented exactly as a pair `(x : Fin n → R, r : R)`.

Model.  `Θ` is a finite candidate family with arbitrary real weights
`π : Θ → ℝ` and, for each candidate `θ`, a read score
`p θ : R → ℝ` on the finite read alphabet `R`, with the explicit
normalization condition `∑ r, p θ r = 1`.  Reads `x : Fin n → R` are independent under each
candidate, so the joint mass of candidate `θ` and sample `x` is

    J θ x = π θ * ∏ i : Fin n, p θ (x i).

The (n+1)-read observation is the pair `(x, r)` with joint mass

    K θ x r = J θ x * p θ r.

Because `∑ r, p θ r = 1`, summing the (n+1)-read joint mass over the last
read recovers the n-read joint mass (`iidJointSucc_marginal`, via
`Finset.mul_sum`).  The merged refinement theorem then gives that the
constructed MAP policy's prior-averaged zero-one success is nondecreasing
from n reads to n+1 reads (`iid_map_success_monotone`).

Explicit scope (no silent identifications):

* This is PRIOR-AVERAGED success under the fixed iid observation model.  It
  is not a claim about the success probability for each fixed true candidate,
  and not a global "ML is the best algorithm" claim.
* The proved inequality is actually algebraic for ANY real-valued `π`
  and any `p` whose per-candidate sums equal one; positivity and
  normalization of `π`, and nonnegativity of `p`, are only required
  to interpret these numbers as genuine joint probability masses and
  the sums as success probabilities. For the later genome adapter
  the prior must be defined on rotation/RC orbit classes, not raw
  spellings. This module does not construct that orbit quotient.
* Ties are handled by the constructive `FiniteBayesDecision.chooseMAP`
  (a finite maximizing witness via `Finset.exists_max_image`); every
  maximizer is optimal, and no uniqueness of the maximizer is claimed.
* Nothing here conditions on coverage or any other event.  Event-conditional
  success is a different experiment (Antonina #266) and is not claimed.
* The (n+1)-sample is the pair `(x, r)`; a reindexing adapter to a literal
  `Fin (n+1) → R` sample is separate optional polish, not required for the
  mathematical content.
-/

namespace AssemblyP1.IidMapMonotonicity

open Finset BigOperators

variable {Θ R : Type*} [Fintype Θ] [DecidableEq Θ] [Fintype R] [Nonempty Θ]

/-- Algebraic joint weight of `π` and the iid read score `p` at sample
size `n`: `π θ * ∏ i, p θ (x i)`. -/
def iidJoint (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) : Θ → (Fin n → R) → ℝ :=
  fun θ x => π θ * ∏ i : Fin n, p θ (x i)

/-- Joint mass at the (n+1)-read observation represented as the pair
`(x : Fin n → R, r : R)`: `J θ x * p θ r`. -/
def iidJointSucc (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) :
    Θ → (Fin n → R) → R → ℝ :=
  fun θ x r => iidJoint π p n θ x * p θ r

/-- The n-read joint mass is the marginal of the (n+1)-read joint mass over
the last read, because the read pmf is normalized: `∑ r, p θ r = 1`. -/
theorem iidJointSucc_marginal (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ)
    (hnorm : ∀ θ, ∑ r : R, p θ r = 1) :
    ∀ θ x, (∑ r : R, iidJointSucc π p n θ x r) = iidJoint π p n θ x := by
  intro θ x
  simp only [iidJointSucc]
  rw [← Finset.mul_sum, hnorm θ, mul_one]

/-- Prior-averaged zero-one success of the constructed MAP policy at sample
size `n`. -/
noncomputable def mapSuccess (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) : ℝ :=
  FiniteBayesDecision.success (iidJoint π p n)
    (FiniteBayesDecision.chooseMAP (iidJoint π p n))

/-- Prior-averaged zero-one success of the constructed MAP policy at the
(n+1)-read observation represented as the pair `(x, r)`. -/
noncomputable def mapSuccessSucc (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → R, ∑ r : R,
    iidJointSucc π p n
      (FiniteBayesDecision.chooseMAP
        (fun θ (xr : (Fin n → R) × R) => iidJointSucc π p n θ xr.1 xr.2) (x, r)) x r

/-- **Exact iid n → n+1 MAP success monotonicity.**  For every sample size
`n` (including `n = 0`), the constructed MAP policy's prior-averaged zero-one
success under a genuine finite iid read model does not decrease when one more
read is observed. Interpreting the formula probabilistically requires a
nonnegative normalized prior and nonnegative normalized per-candidate read pmfs;
the algebraic inequality itself uses only per-candidate read-score sums = 1.  This is prior-averaged only; per-candidate success may
drop (see Antonina #269 counterexample packet). -/
theorem iid_map_success_monotone (π : Θ → ℝ) (p : Θ → R → ℝ) (n : ℕ)
    (hnorm : ∀ θ, ∑ r : R, p θ r = 1) :
    mapSuccess π p n ≤ mapSuccessSucc π p n := by
  unfold mapSuccess mapSuccessSucc
  exact FiniteBayesDecision.chooseMAP_success_monotone_under_refinement
    (iidJoint π p n) (iidJointSucc π p n) (iidJointSucc_marginal π p n hnorm)

#print axioms iidJointSucc_marginal
#print axioms iid_map_success_monotone

end AssemblyP1.IidMapMonotonicity
