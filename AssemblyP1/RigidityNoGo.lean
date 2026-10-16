import AssemblyP1.RigidityBouquet

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The coin-problem obstruction to a polynomial rigidity criterion (issue #257, §8.1/§8.2)

This module advances the *genuinely open* residual of
`docs/source-notes/issue-257-rigid-read-graphs.md`: §8.1 (a closed-form
polynomial graph-theoretic criterion for uniqueness of positive length-`G`
circulations on general oriented `L`-mer supports, or a no-go) and §8.2 (exact
complexity). The exact algebraic criterion
(`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta`), the Graver form
(`AssemblyP1.GraverRigidity`), the two-closed-walk form
(`AssemblyP1.TwoWalkRigidity`), the finite decider
(`AssemblyP1.FiniteRigidityDecider`), the bouquet reduction
(`AssemblyP1.RigidityBouquet`) and the antiparallel-bridge reduction
(`AssemblyP1.RigidityBridge`) are already merged and are **not** redone here.

## The obstruction

The bouquet criterion (`bouquet_nonrigid_iff`) says that a bouquet of `k` cycles
is non-rigid iff there is a nonzero integer vector `x` with
`∑ i, len i * x i = 0` and `x i ≥ 1 - mult i`. This module exhibits the
*arithmetic core* of general-support rigidity: it is exactly the **unbounded
coin problem** (numerical-semigroup membership).

Concretely, given coin values `coins : Fin k → ℕ` and a target `t`, build the
**coin bouquet**: one *target* cycle of length `t` with multiplicity `2`
(slack `1`), and `k` further cycles of lengths `coins i` with multiplicity `1`
(slack `0`). Then:

> `coin_bouquet_nonrigid_iff`: the coin bouquet is **not** rigid **iff** `t` is a
> nonnegative integer combination of the `coins i`.

_Proof._ The criterion becomes `t * x 0 + ∑ i, coins i * x (i+1) = 0` with
`x 0 ≥ -1` and `x (i+1) ≥ 0`. Since `t ≥ 1` and `coins i ≥ 1`, the equation
forces `x 0 ∈ {-1, 0}`; `x 0 = 0` forces `x = 0`, so a nonzero witness has
`x 0 = -1` and `∑ i, coins i * x (i+1) = t` with `x (i+1) ≥ 0`. ∎

This is a *reduction*: deciding general-support rigidity is at least as hard as
the unbounded coin problem. The coin problem with binary-encoded coin values is
NP-hard (Lueker 1975, unbounded knapsack), so no polynomial-time closed form is
expected for general supports. See the note §15 for the precise encoding caveat
(an explicitly represented support encodes the cycle lengths in unary).

## The fractional (LP) no-go

`coin_bouquet_real_nonrigid` shows that for the coin bouquet the **direct
rational relaxation is always satisfiable** (take `x 0 = -1`,
`x 1 = t / coins 0`): a nonzero rational point with zero weighted length sum and
the same box always exists whenever `k ≥ 1`. Hence *no* criterion based only on
the fractional relaxation of this integer system can certify rigidity: the
real-valued problem never detects the rigid instances. This generalizes the
single `len233_mult211_real_integer_gap` example of `RigidityBouquet` to the
whole coin family.

## Main results

* `coin_bouquet_nonrigid_iff`: the exact reduction to numerical-semigroup
  membership.
* `coin_bouquet_real_nonrigid`: the direct LP/fractional relaxation always has a
  nonzero witness for `k ≥ 1`.
* `coins23_target1_rigid`: a rigid coin bouquet (`2 x + 3 y = 1` impossible).
* `coins23_target5_nonrigid`: a non-rigid coin bouquet (`5 = 2 + 3`).

## Epistemic status

All theorems are kernel-checked with only `[propext, Classical.choice,
Quot.sound]` (`AssemblyP1/RigidityNoGoAudit`); no `sorry`/`admit`/`axiom`/
`native_decide`. The reduction and the LP no-go are [mathematical proof +
kernel-checked]; the complexity consequence is stated in the note and depends on
the external NP-hardness of the unbounded coin problem. The exact complexity of
rigidity for **explicitly represented** supports remains **OPEN** (§8.2).
-/

namespace AssemblyP1.RigidityNoGo

open Finset BigOperators
open AssemblyP1.RigidityBouquet (btail bhead bnodes bedges bouquetA bouquet_nonrigid_iff
  sum_bedges_const ConstCyc)

variable {k : ℕ}

/-! ## Numerical-semigroup membership (the unbounded coin problem) -/

/-- `SemigroupMember coins t` says that the target `t` is a nonnegative integer
combination of the coin values `coins`. This is exactly numerical-semigroup
membership, the decision problem of the **unbounded coin problem**. -/
def SemigroupMember (coins : Fin k → ℕ) (t : ℕ) : Prop :=
  ∃ x : Fin k → ℕ, t = ∑ i, coins i * x i

/-! ## The coin bouquet -/

/-- Cycle lengths of the coin bouquet: cycle `0` is the *target* `t`-cycle and
cycle `i+1` is the coin `coins i`-cycle. -/
def coinLen (coins : Fin k → ℕ) (t : ℕ) : Fin (k + 1) → ℕ :=
  Fin.cases t coins

/-- Multiplicities of the coin bouquet: the target cycle has multiplicity `2`
(slack `1`), each coin cycle multiplicity `1` (slack `0`). -/
def coinMult : Fin (k + 1) → ℤ :=
  Fin.cases 2 (fun _ => 1)

/-- A length upper bound for the coin bouquet, used to instantiate the merged
bouquet criterion. -/
def coinM (coins : Fin k → ℕ) (t : ℕ) : ℕ :=
  t + ∑ i, coins i

/-- Total mass of the coin bouquet base circulation: the target cycle
contributes `2 t`, each coin cycle `coins i`. -/
def coinG (coins : Fin k → ℕ) (t : ℕ) : ℕ :=
  2 * t + ∑ i, coins i

lemma coin_hlen (coins : Fin k → ℕ) (hc : ∀ i, 1 ≤ coins i) (t : ℕ) (ht : 1 ≤ t) :
    ∀ i, 1 ≤ coinLen coins t i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [coinLen] using ht
  · simpa [coinLen] using hc j

lemma coin_hM (coins : Fin k → ℕ) (t : ℕ) :
    ∀ i, coinLen coins t i ≤ coinM coins t := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coinLen, coinM]
  · have h1 : coins j ≤ ∑ i, coins i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [coinLen, Fin.cases_succ, coinM]
    omega

/-- Total mass identity for the coin bouquet, supplying the `hAtot` hypothesis
of the merged bouquet criterion. -/
lemma coin_total (coins : Fin k → ℕ) (hc : ∀ i, 1 ≤ coins i) (t : ℕ) (ht : 1 ≤ t) :
    ∑ e ∈ bedges (coinLen coins t) (coinM coins t),
        bouquetA (coinLen coins t) (coinM coins t) coinMult e = (coinG coins t : ℤ) := by
  change ∑ e ∈ bedges (coinLen coins t) (coinM coins t), coinMult e.1 = (coinG coins t : ℤ)
  rw [sum_bedges_const (coinLen coins t) (coinM coins t) (coin_hlen coins hc t ht)
      (coin_hM coins t) (fun e => coinMult e.1) coinMult (fun e _ => rfl)]
  rw [Fin.sum_univ_succ]
  simp only [coinLen, coinMult, Fin.cases_zero, Fin.cases_succ, mul_one]
  rw [coinG]
  push_cast
  ring

/-! ## The exact reduction -/

/-- **Coin-problem reduction for general-support rigidity.** The coin bouquet is
non-rigid **iff** the target is a nonnegative integer combination of the coin
values. This is the precise sense in which deciding rigidity of positive
length-`G` circulations on general oriented supports is *at least as hard as* the
unbounded coin problem. -/
theorem coin_bouquet_nonrigid_iff (coins : Fin k → ℕ) (hc : ∀ i, 1 ≤ coins i)
    (t : ℕ) (ht : 1 ≤ t) :
    (¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes (coinLen coins t))
        (bedges (coinLen coins t) (coinM coins t))
        (bouquetA (coinLen coins t) (coinM coins t) coinMult) (coinG coins t)) ↔
      SemigroupMember coins t := by
  rw [bouquet_nonrigid_iff (coinLen coins t) (coinM coins t) (coin_hlen coins hc t ht)
    (coin_hM coins t) coinMult (coinG coins t) (coin_total coins hc t ht)]
  constructor
  · rintro ⟨x, hxne, hxsum, hxbox⟩
    have hxsum' : (t : ℤ) * x 0 + ∑ i : Fin k, (coins i : ℤ) * x i.succ = 0 := by
      have h := hxsum
      rw [Fin.sum_univ_succ] at h
      simpa [coinLen] using h
    have hxsucc_nonneg : ∀ i : Fin k, 0 ≤ x i.succ := by
      intro i
      have h := hxbox i.succ
      simpa [coinMult] using h
    have hS_nonneg : 0 ≤ ∑ i : Fin k, (coins i : ℤ) * x i.succ := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (by exact_mod_cast Nat.zero_le (coins i)) (hxsucc_nonneg i)
    have ht_pos : (0 : ℤ) < (t : ℤ) := by exact_mod_cast ht
    have hx0_le : x 0 ≤ 0 := by nlinarith [hS_nonneg, hxsum', ht_pos]
    have hx0_ge : (-1 : ℤ) ≤ x 0 := by
      have h := hxbox 0
      simpa [coinMult] using h
    have hx0_cases : x 0 = 0 ∨ x 0 = -1 := by omega
    rcases hx0_cases with hx0 | hx0
    · exfalso
      apply hxne
      have hS0 : ∑ i : Fin k, (coins i : ℤ) * x i.succ = 0 := by
        rw [hx0] at hxsum'
        simpa using hxsum'
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)), (coins i : ℤ) * x i.succ = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => mul_nonneg (by exact_mod_cast Nat.zero_le (coins i)) (hxsucc_nonneg i))).mp hS0
      funext i
      refine Fin.cases hx0 (fun j => ?_) i
      exact (mul_eq_zero.mp (hterm j (Finset.mem_univ j))).resolve_left
        (ne_of_gt (by exact_mod_cast hc j))
    · refine ⟨fun i => (x i.succ).toNat, ?_⟩
      have hS : ∑ i : Fin k, (coins i : ℤ) * x i.succ = (t : ℤ) := by
        rw [hx0] at hxsum'
        linarith
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sum]
      have hcongr : ∀ i : Fin k,
          ((coins i * (x i.succ).toNat : ℕ) : ℤ) = (coins i : ℤ) * x i.succ := by
        intro i
        rw [Nat.cast_mul, Int.toNat_of_nonneg (hxsucc_nonneg i)]
      rw [Finset.sum_congr rfl (fun i _ => hcongr i)]
      exact hS.symm
  · rintro ⟨y, hy⟩
    refine ⟨Fin.cases (-1) (fun i => (y i : ℤ)), ?_, ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      rw [Fin.cases_zero] at h0
      exact absurd h0 (by norm_num)
    · have hy' : (t : ℤ) = ∑ i : Fin k, (coins i : ℤ) * (y i : ℤ) := by
        rw [hy]
        push_cast
        ring
      rw [Fin.sum_univ_succ]
      simp only [coinLen, Fin.cases_zero, Fin.cases_succ]
      linarith [hy']
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [coinMult]
      · simp only [coinMult, Fin.cases_succ]
        simp

/-! ## The fractional (LP) no-go -/

/-- The **rational relaxation** of the bouquet criterion: a nonzero rational
vector with zero weighted length sum and the same box. This is the direct
fractional/LP relaxation of the integer system; a criterion that only tests this
predicate cannot distinguish rigid from non-rigid coin bouquets. -/
def RealWitness (len : Fin k → ℕ) (mult : Fin k → ℤ) : Prop :=
  ∃ x : Fin k → ℚ, x ≠ 0 ∧ (∑ i, (len i : ℚ) * x i = 0) ∧
    ∀ i, (1 - (mult i : ℚ)) ≤ x i

/-- **The direct LP/fractional relaxation is always satisfiable for the coin
bouquet** (`k ≥ 1`). The witness is `x 0 = -1`, `x 1 = t / coins 0`, all other
coordinates `0`; it satisfies the box and the zero weighted length sum. Hence no
criterion based only on the direct rational relaxation can certify rigidity on
general supports. -/
theorem coin_bouquet_real_nonrigid (coins : Fin k → ℕ) (hc : ∀ i, 1 ≤ coins i)
    (t : ℕ) (ht : 1 ≤ t) (hk : 0 < k) :
    RealWitness (coinLen coins t) coinMult := by
  let j0 : Fin k := ⟨0, hk⟩
  refine ⟨Fin.cases (-1) (fun j => if j = j0 then (t : ℚ) / (coins j0 : ℚ) else 0),
    ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    rw [Fin.cases_zero] at h0
    exact absurd h0 (by norm_num)
  · have hsingle : ∑ j : Fin k,
        (coins j : ℚ) * (if j = j0 then (t : ℚ) / (coins j0 : ℚ) else 0) = (t : ℚ) := by
      rw [Finset.sum_eq_single j0]
      · have hc0 : (coins j0 : ℚ) ≠ 0 := by
          have : (1 : ℚ) ≤ (coins j0 : ℚ) := by exact_mod_cast hc j0
          linarith
        rw [ite_eq_left rfl, mul_comm]
        exact div_mul_cancel₀ (t : ℚ) hc0
      · intro j _ hj
        rw [ite_eq_right hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j0) h
    rw [Fin.sum_univ_succ]
    simp only [coinLen, Fin.cases_zero, Fin.cases_succ]
    rw [hsingle]
    ring
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · norm_num [coinMult]
    · simp only [coinMult, Fin.cases_succ]
      by_cases hj : j = j0
      · rw [ite_eq_left hj]
        norm_num
        exact div_nonneg (by positivity) (by positivity)
      · rw [ite_eq_right hj]
        norm_num

/-! ## Kernel-checked worked instances -/

/-- The coin values `{2, 3}`. -/
def coins23 : Fin 2 → ℕ := ![2, 3]

lemma coins23_ge (i : Fin 2) : 1 ≤ coins23 i := by fin_cases i <;> decide

/-- **Rigid coin bouquet.** Target `t = 1` is *not* a nonnegative integer
combination of `{2, 3}` (the only equation is `2x + 3y = 1`), so the coin bouquet
is rigid. -/
theorem coins23_target1_rigid :
    AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes (coinLen coins23 1))
      (bedges (coinLen coins23 1) (coinM coins23 1))
      (bouquetA (coinLen coins23 1) (coinM coins23 1) coinMult) (coinG coins23 1) := by
  by_contra h
  rw [coin_bouquet_nonrigid_iff coins23 coins23_ge 1 (by norm_num)] at h
  obtain ⟨y, hy⟩ := h
  have hy' : 1 = 2 * y 0 + 3 * y 1 := by
    simpa [coins23, Fin.sum_univ_two] using hy
  omega

/-- **Non-rigid coin bouquet.** Target `t = 5 = 2 + 3` is a nonnegative integer
combination of `{2, 3}` (witness `y = (1, 1)`), so the coin bouquet is
non-rigid. -/
theorem coins23_target5_nonrigid :
    ¬ AssemblyP1.ExactRigidityCriterion.Rigid btail bhead (bnodes (coinLen coins23 5))
      (bedges (coinLen coins23 5) (coinM coins23 5))
      (bouquetA (coinLen coins23 5) (coinM coins23 5) coinMult) (coinG coins23 5) := by
  rw [coin_bouquet_nonrigid_iff coins23 coins23_ge 5 (by norm_num)]
  refine ⟨![1, 1], ?_⟩
  simp [coins23, Fin.sum_univ_two]

end AssemblyP1.RigidityNoGo
