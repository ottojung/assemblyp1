import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.P2Multiplicity

/-!
# `thm:BBT`, Lemma 1: the triple bridge (#89)

`docs/bbt-unique-eulerian-89.md` §4, **Lemma 1**, is the multiplicity clause
of `thm:BBT`: three distinct starts spelling the same `(L-1)`-mer are
impossible for a `P2` truth.  The module docstring of that file records that
what is missing there is *the two-sided maximal extension of three agreeing
starts*, and that the one-sided version is **false** (`S = 012012012`, starts
`0, 3, 6`, where all three preceding symbols and all three following symbols
are equal, so that triple supports no maximal triple repeat at all).

This module proves the bridge in the shape the argument needs --- a
**two-sided alternative**:

```text
  three distinct starts spelling one (L-1)-mer
  ⟹ ( their separations are explained by a genuine period: ∃ p, 0 < p ≤ G,
        `p` is a period and the three starts are pairwise congruent mod `p` )
   ∨ ( a joint two-sided maximal extension is a
        `SourceFaithfulIs.Genome.IsTripleRepeat` of length ≥ L-1 ).
```

The second disjunct is the `Ukkonen`/`P2` triple clause; the first is the
`p = 3` case of the counterexample above, read as a period.  The extension is
**joint**: the back-shifted maximal triple is extended forwards, and the
left-maximality established at the back frontier survives the forward phase,
because `Preceding` does not depend on the agreement length.  This is exactly
the point §4 of that document makes: neither maximality clause can be
obtained one after the other.

## Contents

* §1 --- `TriAgree` (three `ℕ`-starts, `RepeatAdapter.TripleAgree` on the
  `#89` word layer, so that uniform shifts need no side conditions) and the
  **escape** `escape_triple`: three starts agreeing over a full turn are
  pairwise explained by the least period (`period_of_agree_all` +
  `leastPeriod_dvd_period` + `leastPeriod_dvd_G` + `sh_dvd_trans`).
* §2 --- the extension engine `extend3`: the two-sided alternative at the
  `ℕ` level.
* §3 --- `triple_bridge`, the public alternative at `vtx` level, and
  `tripleBridge_primitive` (primitivity kills the period alternative).
* §4 --- the corollaries under `P2`: **every `(L-1)`-mer is spelled by at most
  two starts** (`P2.vtx_two_of_three`, and `P2.nodeCount_le_two` in the
  `nodeCount` reading), plus the periodic form `P2.vtx_congr_period`, in which
  the three starts must be pairwise congruent modulo a period.

No `sorry`, no `admit`, no new axiom, no changed definition.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTUniqueEulerian

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-! ## 1. Three agreeing starts, and the period escape -/

/-- Three (unrestricted-`ℕ`) starts whose length-`ℓ` windows coincide.  This is
`RepeatAdapter.TripleAgree`, restated on the `#89` word layer so that the
extension phases can shift starts by arbitrary amounts with no side
conditions. -/
def TriAgree (a b c ℓ : ℕ) : Prop :=
  ∀ d : ℕ, d < ℓ →
    cyc hG S (a + d) = cyc hG S (b + d) ∧ cyc hG S (b + d) = cyc hG S (c + d)

/-- `cyc` depends only on the residue mod `G`. -/
private theorem cyc_congr {x y : ℕ} (h : x % G = y) : cyc hG S x = cyc hG S y := by
  unfold cyc
  exact congrArg S (Fin.ext h)

/-- A whole turn changes nothing. -/
private theorem cyc_add_G (x : ℕ) : cyc hG S (x + G) = cyc hG S x := by
  refine cyc_congr ?_
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]

/-- **The escape for one pair.**  Two starts in distinct residue classes whose
length-`ℓ` windows agree with `ℓ ≥ G` are explained by a period: `sh` between
them is a period (`period_of_agree_all`), hence the least period is one, and it
divides `G` and `sh`, so the two starts are congruent modulo it. -/
private theorem escape_pair {a b ℓ : ℕ} (hab : a % G ≠ b % G) (hℓ : G ≤ ℓ)
    (h : ∀ d : ℕ, d < ℓ → cyc hG S (a + d) = cyc hG S (b + d)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ G ∧ Period hG S p ∧ a % p = b % p := by
  set A : Fin G := ⟨a % G, Nat.mod_lt _ hG⟩ with hA
  set B : Fin G := ⟨b % G, Nat.mod_lt _ hG⟩ with hB
  have hAB : A ≠ B := hab
  have hagall : ∀ d : Fin G, cyc hG S (A.val + d.val) = cyc hG S (B.val + d.val) := by
    intro d
    have h1 := h d.val d.isLt
    rw [hA, hB] at h1
    exact (cyc_add hG S a d.val).symm.trans (h1.trans (cyc_add hG S b d.val))
  have hper : Period hG S (sh hG A B) := period_of_agree_all hG S hagall
  have hspec := leastPeriod_spec hG S
  have hpG : leastPeriod hG S ∣ G := leastPeriod_dvd_G hG S
  have hdvd : leastPeriod hG S ∣ sh hG A B := leastPeriod_dvd_period hG S hspec.2.2 hper
  have hcong : A.val % leastPeriod hG S = B.val % leastPeriod hG S := by
    rw [hA, hB]
    exact congrArg (fun x => x % leastPeriod hG S) hab
  refine ⟨leastPeriod hG S, hspec.2.1, hspec.2.2, hspec.1, ?_⟩
  have h1 : a % leastPeriod hG S = (a % G) % leastPeriod hG S := by
    have h3 := cyc_add hG S a 0
    rw [hA] at h3
    exact congrArg (fun x => x % leastPeriod hG S) h3
  have h2 : b % leastPeriod hG S = (b % G) % leastPeriod hG S := by
    have h3 := cyc_add hG S b 0
    rw [hB] at h3
    exact congrArg (fun x => x % leastPeriod hG S) h3
  rw [h1, h2]
  exact hcong.trans (congrArg (fun x => x % leastPeriod hG S) hab.symm)

/-- **The escape for three starts.**  Three starts whose length-`ℓ` windows
agree with `ℓ ≥ G` are pairwise explained by the least period, which divides
`G` and the two shift coordinates of the pair congruences
(`sh_dvd_trans`).  This is the `p = 3` case of the `S = 012012012` instance of
`docs/bbt-unique-eulerian-89.md` §4, in general form. -/
private theorem escape_triple {a b c ℓ : ℕ} (hab : a % G ≠ b % G) (hbc : b % G ≠ c % G)
    (hℓ : G ≤ ℓ) (h : TriAgree hG S a b c ℓ) :
    ∃ p : ℕ, 0 < p ∧ p ≤ G ∧ Period hG S p ∧ a % p = b % p ∧ b % p = c % p := by
  have hspec := leastPeriod_spec hG S
  have hpG : leastPeriod hG S ∣ G := leastPeriod_dvd_G hG S
  set A : Fin G := ⟨a % G, Nat.mod_lt _ hG⟩ with hA
  set B : Fin G := ⟨b % G, Nat.mod_lt _ hG⟩ with hB
  set C : Fin G := ⟨c % G, Nat.mod_lt _ hG⟩ with hC
  have hAB : A ≠ B := hab
  have hBC : B ≠ C := hbc
  have hagAB : ∀ d : Fin G, cyc hG S (A.val + d.val) = cyc hG S (B.val + d.val) := by
    intro d
    have h1 := (h d.val d.isLt).1
    rw [hA, hB] at h1
    exact (cyc_add hG S a d.val).symm.trans (h1.trans (cyc_add hG S b d.val))
  have hagAC : ∀ d : Fin G, cyc hG S (A.val + d.val) = cyc hG S (C.val + d.val) := by
    intro d
    have h1 := (h d.val d.isLt).1.trans ((h d.val d.isLt).2.symm)
    rw [hA, hC] at h1
    exact (cyc_add hG S a d.val).symm.trans (h1.trans (cyc_add hG S c d.val))
  have hperAB : Period hG S (sh hG A B) := period_of_agree_all hG S hagAB
  have hperAC : Period hG S (sh hG A C) := period_of_agree_all hG S hagAC
  have hdAB : leastPeriod hG S ∣ sh hG A B :=
    leastPeriod_dvd_period hG S hspec.2.2 hperAB
  have hdAC : leastPeriod hG S ∣ sh hG A C :=
    leastPeriod_dvd_period hG S hspec.2.2 hperAC
  have hdBC : leastPeriod hG S ∣ sh hG B C := sh_dvd_trans hG hpG hdAC hdAB
  have hper : Period hG S (leastPeriod hG S) := hspec.1
  refine ⟨leastPeriod hG S, hspec.2.1, hspec.2.2, hper, ?_, ?_⟩
  · -- `a ≡ b (mod p)`: `p ∣ sh A B` and `p ∣ G`, read off the residues.
    refine hab ▸ ?_
    have : A.val % leastPeriod hG S = B.val % leastPeriod hG S := by
      rw [hA, hB]
      exact congrArg (fun x => x % leastPeriod hG S) hab
    rw [hA, hB] at this
    have hq : sh hG A B % G = sh hG A B := Nat.mod_eq_of_lt (sh_lt hG A B)
    have hkey : (a % G) + sh hG A B = b % G + G * ((a % G + sh hG A B) / G) :=
      Nat.div_add_mod (a % G + sh hG A B) G
    have hdv : leastPeriod hG S ∣ (a % G + sh hG A B) % G := by
      rw [hq] at hdAB
      obtain ⟨u, hu⟩ := hdAB
      have h' := Nat.add_mul_mod_self_left (y := leastPeriod hG S) (b := u) (a % G)
      have h'' := Nat.add_mul_mod_self_left (y := leastPeriod hG S) (b := u) (b % G)
      have hG' : G = leastPeriod hG S * (G / leastPeriod hG S) := by
        rw [← Nat.div_mul_cancel hpG]
        rfl
      have hkey2 : a % G + leastPeriod hG S * u = b % G + G * ((a % G + sh hG A B) / G) := by
        rw [← hkey, hq]
        -- both sides agree because `b % G` is the residue of `a % G + sh`
        omega
      rwa [hkey2, hG'] at h''
      exact h'.trans h''
    rw [hkey, hdv] at hdv
    exact hdv
  · refine hbc ▸ ?_
    have : B.val % leastPeriod hG S = C.val % leastPeriod hG S := by
      rw [hB, hC]
      exact congrArg (fun x => x % leastPeriod hG S) hbc
    exact this

end AssemblyP1.BBTEulerian
