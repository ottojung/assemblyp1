import AssemblyP1.RepeatAdapter
import AssemblyP1.PopulationReduction

/-!
# The bridge between the two primitivity predicates (issue #89)

The library carries **two** primitivity predicates, and until now nothing in
the tree identified them:

* `AssemblyP1.RepeatAdapter.IsPrimitive hG S` — no nonzero shift `s < G`
  preserves the circular word (`RepeatAdapter.lean:87`);
* `AssemblyP1.PopulationReduction.IsPrimitive S` — not a nontrivial
  whole-genome power, i.e. no divisor `H` of `G` with `G = H * q`, `q > 1`,
  such that `S` is `q` copies of a word of length `H`
  (`PopulationReduction.lean:1719`).

The population endpoint `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
(through `BBTEndpoint94.Endpoint` and `BBTEndpoint94.DescentObligation`) takes
the **second** one, while every BBT/rematch lemma — `P2RepeatResidual`,
`BBTInterleavedAdmissible.selectedInterleaved_admissible`, and
`P2TripleResidual.triple_extension_of_repeated` /
`not_SelectedTriple_of_P2_primitive` — takes the **first** one.  Since the
reduction chain composes those two layers, the predicates must be identified,
not conflated.  This module identifies them, at every alphabet and every
length, in the kernel:

```lean
isPrimitive_repeatAdapter_of_population
    : PopulationReduction.IsPrimitive S → RepeatAdapter.IsPrimitive hG S
isPrimitive_population_of_repeatAdapter
    : RepeatAdapter.IsPrimitive hG S → PopulationReduction.IsPrimitive S
```

Both directions hold without extra hypotheses (no `2 ≤ G`, no binary alphabet,
no `P2`).

## Which direction does the work

* **`RepeatAdapter → Population`** is the cheap one.  A repetition of a word of
  length `H` with `H * q = G`, `q > 1`, forces `H < G`, and the repetition
  makes the word invariant under the shift `H`, which is exactly what
  `RepeatAdapter.IsPrimitive` forbids.  No minimal-period machinery is needed.

* **`Population → RepeatAdapter`** goes through
  `RepeatAdapter.primitive_or_minimal_period` (issue #74).  A shift `s < G`
  that preserves the word is a period, so the non-primitive branch of the
  dichotomy delivers a minimal period `p` with `p ∣ G` and `p < G`; the shift
  then makes `S` a repetition of a word of length `p`, contradicting
  `PopulationReduction.IsPrimitive`.  The one arithmetic step needed is that a
  period `p` makes `cyc` depend on its argument only modulo `p`
  (`cyc_eq_cyc_mod_of_period`).

No `axiom`, `sorry`, `admit`, `native_decide` or `unsafe` occurs in this file.
-/

namespace AssemblyP1.PrimitivityBridge

open AssemblyP1.RepeatAdapter
open AssemblyP1.PopulationReduction

/-- **A period makes `cyc` depend on its index only modulo the period.**
This is the single arithmetic step the `Population → RepeatAdapter` direction
needs: it reads "`S` is `p`-periodic" as "`S` is a repetition of its first `p`
symbols". -/
theorem cyc_eq_cyc_mod_of_period {α : Type} {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    {p : ℕ} (hper : IsPeriod hG S p) (i : ℕ) :
    OrientedRigidity.cyc hG S i = OrientedRigidity.cyc hG S (i % p) := by
  have hstep : ∀ (q j : ℕ), OrientedRigidity.cyc hG S j
      = OrientedRigidity.cyc hG S (j + p * q) := by
    intro q j
    induction q with
    | zero => simp
    | succ n ih =>
        have heq : j + (p * n + p) = (j + p * n) + p := by omega
        rw [Nat.mul_succ, heq]
        exact ih.trans (hper (j + p * n))
  have heq : i % p + p * (i / p) = i := Nat.mod_add_div i p
  refine Eq.trans ?_ ((hstep (i / p) (i % p)).symm)
  rw [heq]

/-- **The cheap direction.**  A nontrivial whole-genome power is invariant
under the shift by its own half-length, so it is not `RepeatAdapter.IsPrimitive`. -/
theorem isPrimitive_population_of_repeatAdapter {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (h : RepeatAdapter.IsPrimitive hG S) :
    PopulationReduction.IsPrimitive S := by
  intro hrep
  obtain ⟨H, hH0, U, q, hq, hlen, hU⟩ := hrep
  have hHG : H * 2 ≤ G := by
    have hle : H * 2 ≤ H * q := Nat.mul_le_mul_left H (by omega : 2 ≤ q)
    rw [hlen] at hle
    exact hle
  have hHlt : H < G := by omega
  have hdvd : H ∣ G := ⟨q, hlen.symm⟩
  have hSI : ShiftInvariant hG S H := by
    intro i
    have hL : OrientedRigidity.cyc hG S i = U ⟨i % H, Nat.mod_lt i hH0⟩ := by
      have h1 := hU ⟨i % G, Nat.mod_lt i hG⟩
      calc OrientedRigidity.cyc hG S i
          = S ⟨i % G, Nat.mod_lt i hG⟩ := rfl
        _ = U ⟨(i % G) % H, Nat.mod_lt (i % G) hH0⟩ := h1
        _ = U ⟨i % H, Nat.mod_lt i hH0⟩ := by
            refine congrArg U (Fin.ext ?_)
            exact Nat.mod_mod_of_dvd i hdvd
    have hR : OrientedRigidity.cyc hG S (i + H)
        = U ⟨i % H, Nat.mod_lt i hH0⟩ := by
      have h1' := hU ⟨(i + H) % G, Nat.mod_lt (i + H) hG⟩
      calc OrientedRigidity.cyc hG S (i + H)
          = S ⟨(i + H) % G, Nat.mod_lt (i + H) hG⟩ := rfl
        _ = U ⟨((i + H) % G) % H, Nat.mod_lt ((i + H) % G) hH0⟩ := h1'
        _ = U ⟨i % H, Nat.mod_lt i hH0⟩ := by
            refine congrArg U (Fin.ext ?_)
            exact (Nat.mod_mod_of_dvd (i + H) hdvd).trans (Nat.add_mod_right i H)
    exact hL.trans hR.symm

  exact h H hH0 hHlt hSI

/-- **The direction that does the work**, through the issue-#74 dichotomy.
A word invariant under a nonzero shift below `G` has a minimal period `p`
dividing `G`, and a period makes the word a repetition of its first `p`
symbols. -/
theorem isPrimitive_repeatAdapter_of_population {α : Type} {G : ℕ} (hG : 0 < G)
    (S : Fin G → α) (h : PopulationReduction.IsPrimitive S) :
    RepeatAdapter.IsPrimitive hG S := by
  intro s hs0 hsG hSI
  rcases primitive_or_minimal_period hG S with hpr | ⟨p, hp0, hpG, hpdiv, hper, _⟩
  · exact absurd hSI (hpr s hs0 hsG)
  apply h
  have hdvd : p ∣ G := Nat.dvd_of_mod_eq_zero hpdiv
  have hc : p * (G / p) = G := Nat.mul_div_cancel' hdvd
  have hq : 1 < G / p := by
    by_contra hc2
    push Not at hc2
    have hd : p * (G / p) ≤ p * 1 := Nat.mul_le_mul_left p hc2
    rw [hc] at hd
    omega
  refine ⟨p, hp0, (fun j : Fin p => S ⟨j.val, by omega⟩), G / p, hq, hc, ?_⟩
  · intro i
    have hltp : i.val % p < G := lt_of_lt_of_le (Nat.mod_lt i.val hp0) hpG.le
    have hci : OrientedRigidity.cyc hG S i.val = S i :=
      congrArg S (Fin.ext (Nat.mod_eq_of_lt i.isLt))
    have hcp : OrientedRigidity.cyc hG S i.val
        = S ⟨i.val % p, hltp⟩ := by
      rw [cyc_eq_cyc_mod_of_period hG S hper i.val]
      have h2 : OrientedRigidity.cyc hG S (i.val % p)
          = S ⟨(i.val % p) % G, Nat.mod_lt (i.val % p) hG⟩ := rfl
      rw [h2]
      exact congrArg S (Fin.ext (Nat.mod_eq_of_lt hltp))
    exact hci.symm.trans hcp
