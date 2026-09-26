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
| repeat: two starts, equal length-`ℓ` windows, maximal on both sides | `Genome.IsRepeat` |
| triple repeat: three starts, equal windows, three-copy maximality | `Genome.IsTripleRepeat` |
| a copy is bridged iff some read covers a base on **both** sides of it | `BridgesCopy` |
| a (triple) repeat is *bridged* iff at least one selected copy is bridged | `BridgesRepeat` |
| a triple repeat is *all-bridged* iff every selected copy is bridged | `IsTripleRepeatAllBridged` |
| interleaved: the four selected starts alternate | `Interleaved` (cyclic alternation) |
| an interleaved pair is bridged iff one repeat of it is bridged | `IsInterleavedPairBridged` |
| `R` covers `s` | `Covers` |
| `I_s`: `1. R covers s; 2. triple repeats all-bridged; 3. interleaved repeats bridged` | `InformationFeasible` |

Four modeling decisions are visible in the code and are deliberate.

* **Lifting is invisible.** Every position, window, and bridging test is
  phrased with `% len`, so a read or copy that crosses the chosen origin is
  treated exactly like one that does not.  This is the "suitable integer lift of
  the circle" normalization recorded in `docs/bridging-source-semantics.md`.
* **Repeat objects select occurrences.** `IsRepeat` and `IsTripleRepeat`
  quantify over *selected starts* and carry the maximality condition; neither is
  defined by the total multiplicity of a word.  A substring occurring four times
  therefore gives rise to several selected repeats, as the source requires.
  `Genome.IsTripleRepeat.swap₁/…` record the resulting symmetry in the three
  selected starts, so that a certificate proved at one ordering of the starts
  certifies the same triple repeat at every ordering.
* **Interleaving is origin-independent.** `Interleaved` is cyclic alternation:
  exactly one of the second repeat's two selected starts lies on the open
  clockwise arc from the first repeat's first to second start.  Cyclic
  alternation is equivalent, for a circular genome, to the two linear orders
  `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃` of Bresler et al. after cutting the
  circle away from the four starts; the source's displayed inequalities are not
  circular notation, so the two are not identified here, only proved equivalent
  in `docs/bridging-source-semantics.md`.  `Interleaved.cases`, `left_first`,
  `right_first` and `swap₂` make the alternation explicit in its two cases and
  record its independence from the internal order of the *second* repeat's two
  selected starts.
* **All quantification is over a finite type.** `Covers` ranges over
  `Fin S.len` and `InformationFeasible` ranges the repeat lengths over
  `Fin S.len`, using the `e < S.len` side conditions already built into
  `IsRepeat` and `IsTripleRepeat`.  This is why `InformationFeasible` has a
  `Decidable` instance and can be discharged by computation on a concrete
  instance, while remaining literally the source predicate.

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

/-! ## Selected-occurrence symmetry: a certificate is not order-specific

A repeat or triple repeat is an object about *selected occurrences*.  The
source does not privilege an ordering of the selected starts, and the three-copy
maximality condition of `IsTripleRepeat` is already symmetric in `a, b, c`.  The
following equivalences make that explicit, so that no downstream certificate can
silently depend on the order in which the occurrences happen to be listed. -/

/-- Swapping the first two entries of a `=`-chain, in the negated-conjunction
"not all equal" form.  Stated for an arbitrary equational structure so that it
applies to chains of equality of *values* (e.g. of the symbols preceding or
following selected copies), not merely of propositions. -/
theorem notAllEq_swap₁ {ι : Sort _} {x y z : ι}
    (h : ¬ (x = y ∧ y = z)) : ¬ (y = x ∧ x = z) := by
  rintro ⟨h1, h2⟩
  exact h ⟨h1.symm, h1.trans h2⟩

/-- Swapping the first two entries of a `=`-chain, in the negated-conjunction
"not all equal" form; inverted direction. -/
theorem notAllEq_swap₁' {ι : Sort _} {x y z : ι}
    (h : ¬ (y = x ∧ x = z)) : ¬ (x = y ∧ y = z) := by
  rintro ⟨h1, h2⟩
  exact h ⟨h1.symm, h1.trans h2⟩

/-- Swapping the last two entries of a `=`-chain, in the negated-conjunction
"not all equal" form. -/
theorem notAllEq_swap₂ {ι : Sort _} {x y z : ι}
    (h : ¬ (x = y ∧ y = z)) : ¬ (x = z ∧ z = y) := by
  rintro ⟨h1, h2⟩
  exact h ⟨h1.trans h2, h2.symm⟩

/-- Swapping the last two entries of a `=`-chain, in the negated-conjunction
"not all equal" form; inverted direction. -/
theorem notAllEq_swap₂' {ι : Sort _} {x y z : ι}
    (h : ¬ (x = z ∧ z = y)) : ¬ (x = y ∧ y = z) := by
  rintro ⟨h1, h2⟩
  exact h ⟨h1.trans h2, h2.symm⟩

section Selected
variable [DecidableEq α] (S : Genome α) (e : ℕ) (a b c : Fin S.len)

/-- Agreeing windows is symmetric in the two selected starts. -/
theorem Genome.Agree_comm : S.Agree e a b ↔ S.Agree e b a :=
  Iff.intro (fun h => fun d => (h d).symm) (fun h => fun d => (h d).symm)

/-- A maximal repeat is a symmetric object: swapping the two selected starts
gives the same repeat. -/
theorem Genome.IsRepeat_comm : S.IsRepeat e a b ↔ S.IsRepeat e b a :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ =>
      ⟨h1, h2, h3.symm, (Genome.Agree_comm (S := S) (e := e) (a := a) (b := b)).mp h4, h5.symm, h6.symm⟩,
   fun ⟨h1, h2, h3, h4, h5, h6⟩ =>
      ⟨h1, h2, h3.symm, (Genome.Agree_comm (S := S) (e := e) (a := a) (b := b)).mpr h4, h5.symm, h6.symm⟩⟩

/-- A triple repeat is invariant under exchanging its first two selected
starts.  The three-copy maximality conditions need no extra case analysis: they
are chains of `=` and are handled by `notAllEq_swap₁`. -/
theorem Genome.IsTripleRepeat_swap₁ : S.IsTripleRepeat e a b c ↔
    S.IsTripleRepeat e b a c :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h3.symm, h5, h4, (Genome.Agree_comm (S := S) (e := e) (a := a) (b := b)).mp h6, h8, h7,
        notAllEq_swap₁ h9, notAllEq_swap₁ h10⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h3.symm, h5, h4, (Genome.Agree_comm (S := S) (e := e) (a := a) (b := b)).mpr h6, h8, h7,
        notAllEq_swap₁' h9,
        notAllEq_swap₁' h10⟩⟩

/-- A triple repeat is invariant under exchanging its last two selected
starts. -/
theorem Genome.IsTripleRepeat_swap₂ : S.IsTripleRepeat e a b c ↔
    S.IsTripleRepeat e a c b :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h4, h3, h5.symm, h7, h6, (Genome.Agree_comm (S := S) (e := e) (a := b) (b := c)).mp h8,
        notAllEq_swap₂ h9, notAllEq_swap₂ h10⟩,
   fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
      ⟨h1, h2, h4, h3, h5.symm, h7, h6, (Genome.Agree_comm (S := S) (e := e) (a := b) (b := c)).mpr h8,
        notAllEq_swap₂' h9,
        notAllEq_swap₂' h10⟩⟩

/-- A triple repeat is invariant under cyclically rotating its three selected
starts. -/
theorem Genome.IsTripleRepeat_rotate : S.IsTripleRepeat e a b c ↔
    S.IsTripleRepeat e b c a :=
  (Genome.IsTripleRepeat_swap₁ (S := S) (e := e) (a := a) (b := b) (c := c)).trans
    (Genome.IsTripleRepeat_swap₂ (S := S) (e := e) (a := b) (b := a) (c := c))

end Selected

/-! ## Realized reads and bridging -/

/-- A realized read of length `L` starting at `r` covers the positions
`r, r + 1, ..., r + L - 1`, read modulo `S.len`. -/
def ReadCovers (S : Genome α) (L : ℕ) (r : Fin S.len) (p : Nat) : Prop :=
  ∃ d : Fin L, p = (r.val + d.val) % S.len

/-- Coverage: every position of `S` lies in at least one realized read.

`R` is the set of distinct start positions at which reads were sampled.
Multiplicity of a *read type* is deliberately **not** recorded here: coverage
and bridging are properties of the latent placements, whereas the likelihood
consumes only observed type counts. -/
def Covers (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  ∀ p : Fin S.len, ∃ r ∈ R, ReadCovers S L r p.val

/-- The `Fin`-indexed form of `Covers` read at any integer lift of a position:
because `ReadCovers` is phrased modulo `S.len`, the position `p` and its
representative `p % S.len` are covered by the same realized read.  The
statement is about the *reduced* position, which is the one `Covers` quantifies
over; that is exactly the "suitable integer lift of the circle" normalization,
and it is what makes reads crossing the chosen origin indistinguishable. -/
theorem Covers.ofNat (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (h : Covers S L R) (p : ℕ) : ∃ r ∈ R, ReadCovers S L r (p % S.len) := by
  exact h ⟨p % S.len, Nat.mod_lt _ S.len_pos⟩

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

/-- In Bresler's shorthand, an all-bridged triple repeat is in particular a
*bridged* triple repeat, at every ordering of its three selected starts. -/
theorem IsTripleRepeatAllBridged.bridgesRepeat {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e : ℕ} {a b c : Fin S.len}
    (h : IsTripleRepeatAllBridged S L R e a b c) :
    BridgesRepeat S L R e a b := Or.inl h.1

/-! ## Interleaving

Two repeats with selected starts `a, b` and `c, d` interleave when the four
starts alternate around the circle.  Represented origin-independently: exactly
one of `c`, `d` lies strictly on the open clockwise arc from `a` to `b`. -/

section Interleaving
variable {S : Genome α}

/-- `p` lies strictly on the open clockwise arc from `a` to `b`, i.e. between
`a` and `b` in the cyclic order, going clockwise from `a`. -/
def InOpenArc (S : Genome α) (a b p : Fin S.len) : Prop :=
  0 < (p.val + S.len - a.val) % S.len ∧
    (p.val + S.len - a.val) % S.len < (b.val + S.len - a.val) % S.len

/-- The four selected starts of a pair of repeats are pairwise distinct. -/
def FourDistinct (a b c d : Fin S.len) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Cyclic alternation of the two repeats' selected starts: the four starts
alternate around the circle, so no third start separates `a` from `b`. -/
def Interleaved (S : Genome α) (a b c d : Fin S.len) : Prop :=
  FourDistinct a b c d ∧ ((InOpenArc S a b c) ↔ ¬ InOpenArc S a b d)

/-- **Case 1** of the alternation: `c` lies on the open clockwise arc from `a`
to `b` and `d` does not. -/
theorem Interleaved.left_first {S : Genome α} {a b c d : Fin S.len}
    (h : Interleaved S a b c d) (hc : InOpenArc S a b c) :
    ¬ InOpenArc S a b d := h.2.mp hc

/-- **Case 2** of the alternation: `d` lies on the open clockwise arc from `a`
to `b` and `c` does not. -/
theorem Interleaved.right_first {S : Genome α} {a b c d : Fin S.len}
    (h : Interleaved S a b c d) (hd : InOpenArc S a b d) :
    ¬ InOpenArc S a b c := by
  intro hc
  exact (h.2.mp hc) hd

/-- The two cases above exhaust the definition. -/
theorem Interleaved.cases {S : Genome α} {a b c d : Fin S.len}
    (h : Interleaved S a b c d) :
    InOpenArc S a b c ∧ ¬ InOpenArc S a b d ∨
      InOpenArc S a b d ∧ ¬ InOpenArc S a b c := by
  by_cases hc : InOpenArc S a b c
  · exact Or.inl ⟨hc, h.2.mp hc⟩
  · by_cases hd : InOpenArc S a b d
    · exact Or.inr ⟨hd, fun ic => (h.2.mp ic) hd⟩
    · exact absurd (h.2.mpr hd) hc

/-- Cyclic alternation does not depend on the internal order of the *second*
repeat's two selected starts, so an interleaved *pair of repeats* is an object
about the two repeats, not about a chosen presentation of the second one.

The corresponding symmetry for the *first* repeat (`Interleaved S a b c d ↔
Interleaved S b a c d`) is stated in `docs/bridging-source-semantics.md` and is
**not** formalized here: it needs the arithmetic identity that the clockwise arc
from `a` to `b` is the clockwise arc from `b` to `a` traversed backwards, i.e.
`arcDist a b + arcDist b a = S.len` for `a ≠ b`.  That identity is left to a
follow-up so that no step here depends on an unproved modular-arithmetic
normalization.

The alternation clause `InOpenArc a b c ↔ ¬ InOpenArc a b d` is equivalent, but
not syntactically equal, to `InOpenArc a b d ↔ ¬ InOpenArc a b c`; the latter
direction is the classical double-negation step `Classical.byContradiction`, and
no finiteness or arithmetic fact is used. -/
theorem Interleaved.swap₂ {S : Genome α} {a b c d : Fin S.len}
    (h : Interleaved S a b c d) : Interleaved S a b d c :=
  ⟨(fun ⟨f1, f2, f3, f4, f5, f6⟩ => ⟨f1, f3, f2, f5, f4, f6.symm⟩) h.1,
    Iff.intro (fun hd ic => (h.2.mp ic) hd)
      (fun hnic => Classical.byContradiction fun hnid => hnic (h.2.mpr hnid))⟩

/-- An interleaved pair of repeats is *bridged*: at least one of the four
selected copies is bridged by a realized read, which is the composition of the
source's two "bridged" abbreviations. -/
def IsInterleavedPairBridged (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e₁ e₂ : ℕ) (a b c d : Fin S.len) : Prop :=
  BridgesCopy S L R e₁ a ∨ BridgesCopy S L R e₁ b ∨
    BridgesCopy S L R e₂ c ∨ BridgesCopy S L R e₂ d

end Interleaving

/-! ## The information-feasible hypothesis `I_s` -/

section Membership
variable [DecidableEq α] {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}

/-- The information-feasible set membership `R ∈ I_s` of Shomorony et al. (2016),
Eq. (1), on the true circular sequence `S`:

1. `R` covers `S`;
2. every triple repeat of `S` is all-bridged;
3. every interleaved pair of repeats of `S` is bridged.

Quantification is over all admissible repeat lengths `1 ≤ e < S.len` and over
all selected starts, so the predicate is a genuine statement about the
truth/genome pair and not a certificate about a hand-listed triple.  Repeat
lengths are ranged over `Fin S.len` because `IsRepeat` and `IsTripleRepeat`
already require `e < S.len`; this keeps the whole predicate decidable without
changing which repeats are quantified. -/
def InformationFeasible (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  Covers S L R ∧
    (∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridged S L R e.val a b c) ∧
    (∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridged S L R e₁.val e₂.val a b c d)

/-- Coverage alone. -/
theorem InformationFeasible.covers (h : InformationFeasible S L R) :
    Covers S L R := h.1

/-- The all-bridged-triple-repeat clause, applied to the triple repeat whose
three selected starts are listed in the order `a, b, c`.  Use
`Genome.IsTripleRepeat_swap₁`/`_swap₂` to apply it at another ordering. -/
theorem InformationFeasible.triples
    (h : InformationFeasible S L R) {e a b c} (ht : S.IsTripleRepeat e a b c)
    (he : e < S.len) : IsTripleRepeatAllBridged S L R e a b c :=
  h.2.1 ⟨e, he⟩ a b c ht

/-- The bridged-interleaved-repeat clause. -/
theorem InformationFeasible.interleaved
    (h : InformationFeasible S L R) {e₁ e₂ a b c d}
    (h₁ : S.IsRepeat e₁ a b) (h₂ : S.IsRepeat e₂ c d) (hi : Interleaved S a b c d)
    (he₁ : e₁ < S.len) (he₂ : e₂ < S.len) :
    IsInterleavedPairBridged S L R e₁ e₂ a b c d :=
  h.2.2 ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ a b c d h₁ h₂ hi

end Membership

/-! ## Decidability

The whole layer is finite for concrete `S` and `R`, so every witness module can
discharge the certificate — and hence full `I_s` membership, not a weakened
stand-in — by computation. -/

instance (S : Genome α) (L : ℕ) (r : Fin S.len) (p : Nat) :
    Decidable (ReadCovers S L r p) := by
  unfold ReadCovers; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Decidable (Covers S L R) := by
  unfold Covers; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (t : Fin S.len) : Decidable (BridgesCopy S L R e t) := by
  unfold BridgesCopy; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (a b c : Fin S.len) :
    Decidable (IsTripleRepeatAllBridged S L R e a b c) := by
  unfold IsTripleRepeatAllBridged; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
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
