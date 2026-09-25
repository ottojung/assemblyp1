import Mathlib

/-!
# A shared source-faithful circular read / repeat / bridging layer

This module formalizes, once and generically, the hypothesis side of the
AssemblyP1 open problem: the Shomorony et al. (2016) information-feasible set
`I_s`, transcribed with the Bresler et al. (2013) repeat definitions that the
2016 paper explicitly delegates to.

The source correspondence, clause by clause, is recorded in
`docs/bridging-source-semantics.md`.  The essentials, and where each is
implemented below:

| source clause | this module |
| --- | --- |
| circular sequence of length `G` | `Genome` (`len`, `len_pos`, `sym : Fin len → α`) |
| length-`ℓ` substring beginning at a position on the circle | `Genome.window` |
| repeat: two starts, equal length-`ℓ` windows, maximal on both sides | `IsRepeat` |
| triple repeat: three starts, equal windows, three-copy maximality | `IsTripleRepeat` |
| a copy is bridged iff some read covers a base on **both** sides of it | `BridgesCopy` |
| a (triple) repeat is *bridged* iff at least one selected copy is bridged | `BridgesRepeat` |
| a triple repeat is *all-bridged* iff every selected copy is bridged | `IsTripleRepeatAllBridged` |
| interleaved: the four selected starts alternate | `Interleaved` (cyclic alternation) |
| an interleaved pair is bridged iff one repeat of it is bridged | `IsInterleavedPairBridged` |
| `R` covers `s` | `Covers` |
| `I_s`: `1. R covers s; 2. triple repeats all-bridged; 3. interleaved repeats bridged` | `InformationFeasible` |

Three modeling decisions are visible in the code and are deliberate.

* **Lifting is invisible.** Every position, window, and bridging test is
  phrased with `% len`, so a read or copy that crosses the chosen origin is
  treated exactly like one that does not.  This is the "suitable integer lift of
  the circle" normalization recorded in `docs/bridging-source-semantics.md`.
* **Repeat objects select occurrences.** `IsRepeat` and `IsTripleRepeat`
  quantify over *selected starts* and carry the maximality condition; neither is
  defined by the total multiplicity of a word.  A substring occurring four times
  therefore gives rise to several selected repeats, as the source requires.
* **Interleaving is origin-independent.** `Interleaved` is cyclic alternation:
  exactly one of the second repeat's two selected starts lies on the open
  clockwise arc from the first repeat's first to second start.  Cyclic
  alternation is equivalent, for a circular genome, to the two linear orders
  `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃` of Bresler et al. after cutting the
  circle away from the four starts; the source's displayed inequalities are not
  circular notation, so the two are not identified here, only proved equivalent
  in `docs/bridging-source-semantics.md`.

Nothing in this module is witness-specific.  It is deliberately *only* the
hypothesis side: candidate universes and likelihood variants stay in the
counterexample modules, because the source does not fix a candidate class.
-/

namespace AssemblyP1.SourceFaithfulIs

universe u

variable {α : Type u}

/-- A circular genome over `α`: `len` symbols indexed by `Fin len`, read modulo
`len`.  This is the shared substrate for *both* the true sequence `s` and any
circular candidate, so that candidate-intrinsic length `len` is intrinsic to the
object rather than supplied externally. -/
structure Genome (α : Type u) where
  /-- Number of symbols on the circle. -/
  len : ℕ
  /-- The circle is nonempty, so `% len` is total. -/
  len_pos : 0 < len
  /-- The symbols, indexed by position on the circle. -/
  sym : Fin len → α

namespace Genome

/-- The symbol at an arbitrary integer position, read around the circle. -/
def cycl [DecidableEq α] (S : Genome α) (i : Nat) : α :=
  S.sym ⟨i % S.len, Nat.mod_lt _ S.len_pos⟩

/-- The length-`e` circular window of `S` beginning at start `r`, i.e. the
substring of length `e` that a read of length `e` placed at `r` would return. -/
def window [DecidableEq α] (S : Genome α) (e : ℕ) (r : Fin S.len) : Fin e → α :=
  fun d => S.cycl (r.val + d.val)

/-- Two starts carry the same length-`e` substring. -/
def Agree [DecidableEq α] (S : Genome α) (e : ℕ) (r t : Fin S.len) : Prop :=
  ∀ d : Fin e, S.window e r d = S.window e t d

/-- The symbol immediately before the copy at start `t` (the last base outside
the occurrence `[t, t + e)`). -/
def Preceding [DecidableEq α] (S : Genome α) (t : Fin S.len) : α :=
  S.cycl (t.val + S.len - 1)

/-- The symbol immediately after the copy of length `e` at start `t`. -/
def Following [DecidableEq α] (S : Genome α) (e : ℕ) (t : Fin S.len) : α :=
  S.cycl (t.val + e)

/-- A *maximal* length-`e` repeat with the two selected starts `a` and `b`:
equal length-`e` substrings whose preceding symbols differ and whose following
symbols differ.  This is the source repeat, with Bresler's two-sided maximality
requirement; it is emphatically not "some word occurs at least twice". -/
def IsRepeat [DecidableEq α] (S : Genome α) (e : ℕ) (a b : Fin S.len) : Prop :=
  1 ≤ e ∧ e < S.len ∧ a ≠ b ∧ S.Agree e a b ∧
    S.Preceding a ≠ S.Preceding b ∧ S.Following e a ≠ S.Following e b

/-- A *maximal triple repeat* of length `e` with the three pairwise distinct
selected starts `a`, `b`, `c`: the three length-`e` substrings agree and the
preceding (respectively following) symbols are not all equal.

Total multiplicity is deliberately unconstrained: a substring occurring four
times yields several selected triple repeats, which is what the source
prescribes. -/
def IsTripleRepeat [DecidableEq α] (S : Genome α) (e : ℕ) (a b c : Fin S.len)
    : Prop :=
  1 ≤ e ∧ e < S.len ∧
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    S.Agree e a b ∧ S.Agree e a c ∧ S.Agree e b c ∧
    ¬(S.Preceding a = S.Preceding b ∧ S.Preceding b = S.Preceding c) ∧
    ¬(S.Following e a = S.Following e b ∧ S.Following e b = S.Following e c)

end Genome

/-! ## Realized reads and bridging -/

variable {G : ℕ}

/-- A realized read of length `L` starting at `r` covers the positions
`r, r + 1, ..., r + L - 1`, read modulo `S.len`. -/
def ReadCovers (S : Genome α) (L : ℕ) (r : Fin S.len) (p : Nat) : Prop :=
  ∃ d : Fin L, p = (r.val + d.val) % S.len

/-- The realized read placements: the distinct start positions at which reads
were sampled.  Multiplicity of a *read type* is deliberately **not** recorded
here: coverage and bridging are properties of the latent placements, whereas the
likelihood consumes only observed type counts. -/
abbrev ReadPlacements := Finset (Fin _)

/-- Coverage: every position of `S` lies in at least one realized read.  Since
the right-hand side is a residue, ranging `p` over all of `ℕ` also forces
`p < S.len`, so this is exactly "every base of the circular sequence is read". -/
def Covers (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  ∀ p : ℕ, ∃ r ∈ R, ReadCovers S L r p

/-- The selected length-`e` copy at `t` is **bridged** by the realized reads
when some single read covers at least one base strictly before the copy and at
least one base strictly after it, i.e. the positions `t - 1` and `t + e`.

This is the source's strict-extension convention (Bresler et al., Fig. 5 and the
paragraph before Theorem 1; Shomorony et al. §3/Fig. 6).  Containing the
repeated substring is *not* enough: a read starting exactly at the copy, or
ending exactly at its last base, does not bridge it. -/
def BridgesCopy (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (t : Fin S.len) : Prop :=
  ∃ r ∈ R,
    ReadCovers S L r ((t.val + S.len - 1) % S.len) ∧
      ReadCovers S L r ((t.val + e) % S.len)

/-- A repeat (given by its two selected starts) is *bridged* in Bresler's
shorthand: at least one of its selected copies is bridged. -/
def BridgesRepeat (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (a b : Fin S.len) : Prop :=
  BridgesCopy S L R e a ∨ BridgesCopy S L R e b

/-- A triple repeat is *all-bridged*: every selected copy is bridged.  This is
strictly stronger than `BridgesRepeat` on one of its pairs and is the condition
`I_s` actually requires. -/
def IsTripleRepeatAllBridged (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (a b c : Fin S.len) : Prop :=
  BridgesCopy S L R e a ∧ BridgesCopy S L R e b ∧ BridgesCopy S L R e c

/-! ## Interleaving

Two repeats with selected starts `a, b` and `c, d` interleave when the four
starts alternate around the circle.  Represented origin-independently: exactly
one of `c`, `d` lies strictly on the open clockwise arc from `a` to `b`. -/

/-- `p` lies strictly on the open clockwise arc from `a` to `b`, i.e. between
`a` and `b` in the cyclic order, going the short way round. -/
def InOpenArc (S : Genome α) (a b p : Fin S.len) : Prop :=
  0 < (p.val + S.len - a.val) % S.len ∧
    (p.val + S.len - a.val) % S.len < (b.val + S.len - a.val) % S.len

/-- The four selected starts of a pair of repeats are pairwise distinct. -/
def FourDistinct (a b c d : Fin S.len) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Cyclic alternation of the two repeats' selected starts.  Equivalent to
Bresler's `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃` for some linearization of
the circle avoiding the four starts; the alternation condition itself is
invariant under rotating the cut. -/
def Interleaved (S : Genome α) (a b c d : Fin S.len) : Prop :=
  FourDistinct a b c d ∧ ((InOpenArc S a b c) ↔ ¬ InOpenArc S a b d)

/-- An interleaved pair of repeats is *bridged*: at least one of the two
repeats, in Bresler's shorthand, has a bridged selected copy. -/
def IsInterleavedPairBridged (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e₁ e₂ : ℕ) (a b c d : Fin S.len) : Prop :=
  BridgesCopy S L R e₁ a ∨ BridgesCopy S L R e₁ b ∨
    BridgesCopy S L R e₂ c ∨ BridgesCopy S L R e₂ d

/-! ## The information-feasible hypothesis `I_s` -/

/-- The information-feasible set membership `R ∈ I_s` of Shomorony et al. (2016),
Eq. (1), on the true circular sequence `S`:

1. `R` covers `S`;
2. every triple repeat of `S` is all-bridged;
3. every interleaved pair of repeats of `S` is bridged.

Quantification is over all admissible repeat lengths `1 ≤ e < S.len` and over
all selected starts, so the predicate is a genuine statement about the
truth/genome pair and not a certificate about a hand-listed triple. -/
def InformationFeasible (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  Covers S L R ∧
    (∀ (e : ℕ) (a b c : Fin S.len), S.IsTripleRepeat e a b c →
      IsTripleRepeatAllBridged S L R e a b c) ∧
    (∀ (e₁ e₂ : ℕ) (a b c d : Fin S.len),
      S.IsRepeat e₁ a b → S.IsRepeat e₂ c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L R e₁ e₂ a b c d)

/-- Coverage alone. -/
theorem InformationFeasible.covers (h : InformationFeasible S L R) :
    Covers S L R := h.1

/-- The all-bridged-triple-repeat clause. -/
theorem InformationFeasible.triples
    (h : InformationFeasible S L R) {e a b c} (ht : S.IsTripleRepeat e a b c) :
    IsTripleRepeatAllBridged S L R e a b c := h.2.1 e a b c ht

/-- The bridged-interleaved-repeat clause. -/
theorem InformationFeasible.interleaved
    (h : InformationFeasible S L R) {e₁ e₂ a b c d}
    (h₁ : S.IsRepeat e₁ a b) (h₂ : S.IsRepeat e₂ c d) (hi : Interleaved S a b c d) :
    IsInterleavedPairBridged S L R e₁ e₂ a b c d := h.2.2 e₁ e₂ a b c d h₁ h₂ hi

/-! ## Decidability

The whole layer is finite for concrete `S` and `R`, so every witness module can
discharge the certificate by computation. -/

instance (S : Genome α) [DecidableEq α] (L : ℕ) (r : Fin S.len) (p : Nat) :
    Decidable (ReadCovers S L r p) := by
  unfold ReadCovers; infer_instance

instance (S : Genome α) [DecidableEq α] (L : ℕ) (R : Finset (Fin S.len)) :
    Decidable (Covers S L R) := by
  unfold Covers; infer_instance

instance (S : Genome α) [DecidableEq α] (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (t : Fin S.len) : Decidable (BridgesCopy S L R e t) := by
  unfold BridgesCopy; infer_instance

instance (S : Genome α) [DecidableEq α] (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (a b c : Fin S.len) :
    Decidable (IsTripleRepeatAllBridged S L R e a b c) := by
  unfold IsTripleRepeatAllBridged; infer_instance

instance (S : Genome α) [DecidableEq α] (L : ℕ) (R : Finset (Fin S.len))
    (e₁ e₂ : ℕ) (a b c d : Fin S.len) :
    Decidable (IsInterleavedPairBridged S L R e₁ e₂ a b c d) := by
  unfold IsInterleavedPairBridged; infer_instance

instance (S : Genome α) [DecidableEq α] (e : ℕ) (a b : Fin S.len) :
    Decidable (S.IsRepeat e a b) := by
  unfold Genome.IsRepeat Genome.Agree Genome.Preceding Genome.Following
    Genome.window Genome.cycl
  infer_instance

instance (S : Genome α) [DecidableEq α] (e : ℕ) (a b c : Fin S.len) :
    Decidable (S.IsTripleRepeat e a b c) := by
  unfold Genome.IsTripleRepeat Genome.Agree Genome.Preceding Genome.Following
    Genome.window Genome.cycl
  infer_instance

instance (S : Genome α) (a b c d : Fin S.len) :
    Decidable (Interleaved S a b c d) := by
  unfold Interleaved FourDistinct InOpenArc
  infer_instance

instance (S : Genome α) [DecidableEq α] (L : ℕ) (R : Finset (Fin S.len)) :
    Decidable (InformationFeasible S L R) := by
  unfold InformationFeasible; infer_instance

end AssemblyP1.SourceFaithfulIs
