import AssemblyP1.BBTEulerian

/-!
# Three agreeing circular windows: certified interface

The previous private escape_pair/escape_triple attempts did not elaborate.
Their draft is preserved in docs/unfinished-bbt-triple-bridge-draft.md,
explicitly not a proof. Do not assert an unproved period-escape theorem.
This module remains part of the complete Lean build.
-/

namespace AssemblyP1.BBTEulerian

open OrientedRigidity

variable {α : Type} [DecidableEq α] {G : ℕ}
  (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- Three starts have identical length-ℓ observed cyclic windows. -/
def TriAgree (a b c ℓ : ℕ) : Prop :=
  ∀ d : ℕ, d < ℓ →
    cyc hG S (a + d) = cyc hG S (b + d) ∧
    cyc hG S (b + d) = cyc hG S (c + d)

/-- A three-way agreement certifies the first pair of windows. -/
theorem triAgree_left {a b c ℓ : ℕ}
    (h : TriAgree hG S a b c ℓ) {d : ℕ} (hd : d < ℓ) :
    cyc hG S (a + d) = cyc hG S (b + d) :=
  (h d hd).1

/-- A three-way agreement certifies the second pair of windows. -/
theorem triAgree_right {a b c ℓ : ℕ}
    (h : TriAgree hG S a b c ℓ) {d : ℕ} (hd : d < ℓ) :
    cyc hG S (b + d) = cyc hG S (c + d) :=
  (h d hd).2

end AssemblyP1.BBTEulerian
