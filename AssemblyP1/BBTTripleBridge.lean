import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.P2Multiplicity

/-!
# BBT triple bridge: full-turn period escape

If cyclic windows from two starts agree for an entire genome length,
their starts are congruent modulo the least period of the genome.
Applying this pairwise gives the three-start period alternative.
The proof uses `period_of_agree_all` and divisibility of the least
period; unlike the previous draft, it does not confuse inequivalence
modulo G with equality or divisibility.
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

/-- Three circular starts agree at every position in a length-ℓ window. -/
def TriAgree (a b c ℓ : ℕ) : Prop :=
  ∀ d : ℕ, d < ℓ →
    cyc hG S (a + d) = cyc hG S (b + d) ∧
    cyc hG S (b + d) = cyc hG S (c + d)

/-- Full-turn equality gives congruence modulo the genome's least period. -/
private theorem congr_leastPeriod_of_full_agree {a b ℓ : ℕ}
    (hℓ : G ≤ ℓ)
    (h : ∀ d : ℕ, d < ℓ → cyc hG S (a + d) = cyc hG S (b + d)) :
    a % leastPeriod hG S = b % leastPeriod hG S := by
  let A : Fin G := ⟨a % G, Nat.mod_lt _ hG⟩
  let B : Fin G := ⟨b % G, Nat.mod_lt _ hG⟩
  have hall : ∀ d : Fin G, cyc hG S (A.val + d.val) =
      cyc hG S (B.val + d.val) := by
    intro d
    change cyc hG S ((a % G) + d.val) = cyc hG S ((b % G) + d.val)
    calc
      _ = cyc hG S (a + d.val) := (cyc_add hG S a d.val).symm
      _ = cyc hG S (b + d.val) :=
        h d.val (Nat.lt_of_lt_of_le d.isLt hℓ)
      _ = _ := cyc_add hG S b d.val
  have hper : Period hG S (sh hG A B) :=
    period_of_agree_all hG S hall
  have hpG : leastPeriod hG S ∣ G := leastPeriod_dvd_G hG S
  have hpsh : leastPeriod hG S ∣ sh hG A B :=
    leastPeriod_dvd_period hG S (Nat.le_of_lt (sh_lt hG A B)) hper
  have hshift : (a % G + sh hG A B) % G = b % G := by
    have hh := congrArg Fin.val (rotAdd_sh hG A B)
    simpa [A, B, rotAdd] using hh
  calc
    a % leastPeriod hG S = (a % G) % leastPeriod hG S :=
      (Nat.mod_mod_of_dvd a hpG).symm
    _ = (a % G + sh hG A B) % leastPeriod hG S := by
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpsh]
    _ = ((a % G + sh hG A B) % G) % leastPeriod hG S :=
      (Nat.mod_mod_of_dvd _ hpG).symm
    _ = (b % G) % leastPeriod hG S :=
      congrArg (fun n => n % leastPeriod hG S) hshift
    _ = b % leastPeriod hG S := Nat.mod_mod_of_dvd b hpG

/-- The pairwise full-turn agreement forces one shared genuine period. -/
private theorem escape_pair {a b ℓ : ℕ} (hab : a % G ≠ b % G)
    (hℓ : G ≤ ℓ)
    (h : ∀ d : ℕ, d < ℓ → cyc hG S (a + d) = cyc hG S (b + d)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ G ∧ Period hG S p ∧ a % p = b % p := by
  have hs := leastPeriod_spec hG S
  exact ⟨leastPeriod hG S, hs.2.1, hs.2.2, hs.1,
    congr_leastPeriod_of_full_agree hG S hℓ h⟩

/-- Agreement of three circular windows across a full turn makes all
three starts congruent modulo the *same* genuine period. -/
private theorem escape_triple {a b c ℓ : ℕ}
    (hab : a % G ≠ b % G) (hbc : b % G ≠ c % G)
    (hℓ : G ≤ ℓ) (h : TriAgree hG S a b c ℓ) :
    ∃ p : ℕ, 0 < p ∧ p ≤ G ∧ Period hG S p ∧
      a % p = b % p ∧ b % p = c % p := by
  have hs := leastPeriod_spec hG S
  exact ⟨leastPeriod hG S, hs.2.1, hs.2.2, hs.1,
    congr_leastPeriod_of_full_agree hG S hℓ (fun d hd => (h d hd).1),
    congr_leastPeriod_of_full_agree hG S hℓ (fun d hd => (h d hd).2)⟩

end AssemblyP1.BBTEulerian
