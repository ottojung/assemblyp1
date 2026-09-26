import AssemblyP1.BridgingBridge
import AssemblyP1.SameLength62Maximizer

/-!
# #88 in the §6.2 same-length setting: the faithful ML predicate and the
# graph-level reduction

This module states the faithful §6.2 maximum-likelihood predicate, proves that
the ML comparison in that class is the spectral comparison, and derives the
§6.2 maximum-likelihood statement from **full `I_s` alone**.

## 0. Status at this head

`AssemblyP1.MLEscape.informationFeasible_62_spelledML`: let `S` be a circular
word of length `G`, let `ρ` be a realization of `n` reads on `S`, suppose the
**realized** reads are `I_s`-feasible at read length `L` (§2), and suppose the
truth is a genuine §6.2 candidate for the observed read set. Then every
**same-length genuine §6.2 candidate** `D` for the same observed read set has
exact same-length Medvedev–Brudno likelihood at most the truth's.

There is **no** long-triple-repeat premise, **no** primitivity or period
premise, and **no** escape, culprit or "spectral rigidity" hypothesis of any
kind. The hypothesis list is exactly the source's: `2 ≤ L ≤ G`, full `I_s`, and
the §6.2 data.

Two things changed at this head, and both are recorded in the git history.

**The source-semantics fix.** Up to the previous commit this module's headline
theorem carried an explicit, unproved combinatorial hypothesis
`EscapeForcesMidRangeRepeat` ("a spectral escape forces a maximal triple repeat
in the band `L - 1 ≤ ℓ < G - L`") plus a `¬ HasLongTripleRepeat` premise, and
`AssemblyP1.WraparoundTripleRepeat` kernel-checked that the latter was not
dischargeable from `I_s`. All of that rested on `SourceFaithfulIs.BridgesCopy`
being read *endpoint-wise* — "some realized read covers `(t-1) % G` and covers
`(t+e) % G`" — which is not the source's condition. Bresler et al. and
Shomorony et al. require one read to strictly straddle the occurrence, i.e. on a
suitable lift `r < t` and `t + e < r + L`; the endpoint-wise reading lets a read
reach a *long* copy's two endpoints around the complementary circular arc
without containing the copy. With the corrected `BridgesCopy`,

* `SourceFaithfulIs.bridgesCopy_length : BridgesCopy → e + 2 ≤ L`, and
* `BridgingBridge.informationFeasible_no_long_triple_repeat : 2 ≤ L → R ∈ I_s →
  ¬ HasLongTripleRepeat`,

so the "wraparound regime" is empty, `informationFeasible_no_escape` below is a
theorem, and the culprit statement is gone. See
`docs/bridging-source-semantics.md` and `docs/issue88-wraparound-contrapositive.md`.

**The exact-range semantics.** `realizedStarts ρ` (§2) is the range of the
realization, and the previous surface took an arbitrary `R` with only
`hR : ∀ i, ρ i ∈ R`. Since every clause of `InformationFeasible` is a
"some `r ∈ R` does …" or a coverage condition, an `R` with spurious starts is a
strictly weaker hypothesis than the source's statement about the reads actually
taken. `informationFeasible_of_exact_subset` shows that a start set which
contains the range **and** has no spurious start *is* the range.

## 1. The band that clause 2 of `I_s` decides

`HasMidRangeTripleRepeat` is the mid-range band `L - 1 ≤ ℓ < G - L`;
`informationFeasible_no_midRangeTriple` is the kernel-checked fact that clause 2
of `I_s` forbids it, and `longTripleFree_no_midRangeTriple` shows
`¬ HasLongTripleRepeat → ¬ HasMidRangeTripleRepeat`. The band survives as a
*description* of what clause 2 rules out; the old `HasWraparoundTripleRepeat`
band and the `G - L` escape route are deleted, because under the corrected
semantics `I_s` rules out the whole range `ℓ ≥ L - 1`.

## 2. A genuinely faithful §6.2 maximum-likelihood predicate

`AssemblyP1.SameLengthExactMLCounterexample.Is62MaximumLikelihood` is a
*dominance* predicate: it has no membership conjunct, so refuting it does not
refute "the truth is a §6.2 candidate and maximises". `Is62SpelledMLMax` is the
maximizer predicate with membership:

* the truth carries a genuine `Section62Flow.SpelledFeasible62` certificate for
  the observed read set (`SameLength62Maximizer.Is62Candidate62`: a `Spelling`
  of `G` positions that *represents* `S`, a literal §6.2 feasibility
  certificate, and the walk's own flow), **and**
* every same-length `Fin G → α` word carrying such a certificate for the same
  observed read set has `exactLik` at most the truth's.

Conventions are those of `docs/ml-formalization-contract.md` Variant E and are
*not* changed here: strict oriented single-strand read types, no
reverse-complement collapse, genome equivalence by rotation only, the exact
Medvedev–Brudno multinomial objective with the candidate-intrinsic `N(D) = G`,
and the observation-only multinomial coefficient divided out (`exactLik_scale`
reinstates it without changing any comparison).

## 3. The likelihood comparison *is* the spectral comparison

`exactLik_le_of_spec_le` is the structural heart of this module, and it is proved
rather than asserted. If `D` has the truth's window support and the observation
is a realization on the truth, then

```
exactLik D x ≤ exactLik S x  ↔  ∀ w, 0 < x w → specCount D w ≤ specCount S w
```

because every factor `(d w / G) ^ (x w)` has base in `(0, 1]` on the support
(the multiplicity is at most `G`) and is `1` off it (nothing is observed
there). So the ML comparison in the §6.2 class is exactly the pointwise
comparison of spectra on the **observed** read types.

Consequently:

* `candidate_escape_iff_ml_failure`: ML failure in the same-length §6.2 class
  is exactly the existence of a single **observed** read type whose
  multiplicity in the candidate strictly exceeds the truth's; and
* `ml_failure_gives_spectral_escape`: ML failure produces, at the graph level,
  a positive balanced circulation of total mass `G` on the truth's support that
  beats the truth's spectrum (the candidate's own spectrum is such a
  circulation, by `candidate_is_massG_positive_circulation`).

The contrapositive `informationFeasible_no_escape` is now a **theorem**: full
`I_s` forbids every such circulation. The question that
`docs/issue88-wraparound-contrapositive.md` records as open — "can a positive
balanced circulation of total mass `G` on the truth's window support strictly
exceed the truth's spectrum?" — is answered negatively, from `I_s`.

## 4. Finite evidence for the mid-range band

`HasMidRangeTripleRepeat` and the `culprit_instance_checked` instance remain as a
*record* of the investigation: at the truth `0000001` and the same-length
candidate `0001001`, `G = 7`, `L = 3`, the read type `100` has multiplicity `1`
in the truth and `2` in the candidate (so the premise is non-vacuous), and the
truth carries a maximal triple repeat at starts `0, 1, 4` of length
`2 ∈ [L - 1, G - L) = [2, 4)`. That genome is *not* `I_s`-feasible, and under
the corrected semantics it is excluded by clause 2 exactly as it should be: the
band `[L - 1, G - L)` is inside the excluded range `[L - 1, G)`.

The non-vacuity companion is deliberate. An earlier harness in this
repository's history was void because the implication it checked had an
unsatisfiable premise (`docs/same-length-exact-ml-88-refutation.md` §4), and a
non-vacuity companion is the direct guard against repeating that.
-/

namespace AssemblyP1.MLEscape

open SourceFaithfulIs
open OrientedRigidity
open BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. The mid-range band -/

/-- **A maximal triple repeat of the truth in the mid-range band
`L - 1 ≤ ℓ < G - L`.**

The band that clause 2 of `I_s` decides. The starts and the length are `Fin G`
indexed rather than `ℕ` indexed so that the predicate is decidable by
`decide`; the residue-distinctness conditions are spelled out because
`RepeatAdapter.HasLongTripleRepeat` carries them separately from
`IsMaximalTriple`. -/
def HasMidRangeTripleRepeat {G : ℕ} (hG : 0 < G) (S : Fin G → α) (L : ℕ) : Prop :=
  ∃ (a b c ℓ : Fin G),
    L - 1 ≤ ℓ.val ∧ ℓ.val < G - L ∧
      a.val % G ≠ b.val % G ∧ b.val % G ≠ c.val % G ∧ a.val % G ≠ c.val % G ∧
      RepeatAdapter.IsMaximalTriple hG S a.val b.val c.val ℓ.val

/-- `HasMidRangeTripleRepeat` is decidable. The instance is stated explicitly
because `RepeatAdapter.TripleAgree` is a plain `def`, which instance search
does not unfold on its own; the finite check in §5 depends on this. -/
instance {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (L : ℕ) : Decidable (HasMidRangeTripleRepeat hG S L) := by
  unfold HasMidRangeTripleRepeat RepeatAdapter.IsMaximalTriple
    RepeatAdapter.TripleAgree
  infer_instance

/-- `RepeatAdapter.IsMaximalTriple` is decidable; the instance is stated
explicitly because `TripleAgree` is a plain `def` that instance search does not
unfold on its own. -/
instance {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (a b c ℓ : ℕ) : Decidable (RepeatAdapter.IsMaximalTriple hG S a b c ℓ) := by
  unfold RepeatAdapter.IsMaximalTriple RepeatAdapter.TripleAgree
  infer_instance

/-- **A mid-range maximal triple repeat is a long maximal triple repeat.** So
`¬ HasLongTripleRepeat` implies `¬ HasMidRangeTripleRepeat`: a theorem stated
with the mid-range premise is strictly stronger than the audited one with
`hno`, and under `I_s` the two premises agree. -/
theorem HasMidRangeTripleRepeat.longTriple {G L : ℕ} (hG : 0 < G) (hLG : L ≤ G)
    {S : Fin G → α} (h : HasMidRangeTripleRepeat hG S L) :
    RepeatAdapter.HasLongTripleRepeat hG S L := by
  obtain ⟨a, b, c, ℓ, hℓ1, hℓ2, hab, hbc, hac, htri⟩ := h
  refine ⟨a.val, b.val, c.val, ℓ.val, hℓ1, ?_, hab, hbc, hac, htri⟩
  omega

/-- **Full `I_s` excludes the mid-range band.** Clause 2 of `I_s`, read through
the sharp bridging dichotomy, rules out every maximal triple repeat of the
truth of length `L - 1 ≤ ℓ < G - L`. -/
theorem informationFeasible_no_midRangeTriple {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (R : Finset (Fin G))
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R) :
    ¬ HasMidRangeTripleRepeat hG S L := by
  rintro ⟨a, b, c, ℓ, hℓ1, hℓ2, hab, hbc, hac, htri⟩
  have h1 : 1 ≤ ℓ.val := by omega
  have hℓG : ℓ.val < G := by omega
  have ht : (⟨G, hG, S⟩ : Genome α).IsTripleRepeat ℓ.val ⟨a.val % G, Nat.mod_lt _ hG⟩
      ⟨b.val % G, Nat.mod_lt _ hG⟩ ⟨c.val % G, Nat.mod_lt _ hG⟩ :=
    BridgingBridge.isTripleRepeat_of_maximalTriple (S := ⟨G, hG, S⟩)
      (a := a.val) (b := b.val) (c := c.val) (ℓ := ℓ.val) h1 hℓG hab hac hbc
      htri.1 (fun h => htri.2.1 h) (fun h => htri.2.2 h)
  have hge : G - L ≤ ℓ.val :=
    BridgingBridge.informationFeasible_tripleRepeat_ge_G_sub_L hL2 hLG hfeas hℓ1 hℓG ht
  omega

/-- The audited premise implies the mid-range premise. -/
theorem longTripleFree_no_midRangeTriple {G L : ℕ} (hG : 0 < G) (hLG : L ≤ G)
    {S : Fin G → α} (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L) :
    ¬ HasMidRangeTripleRepeat hG S L :=
  fun h => hno (HasMidRangeTripleRepeat.longTriple hG hLG h)

/-! ## 2. The realized start set: `I_s` at the *exact* range of `ρ`

Issue #88 states the hypothesis on the reads that were actually taken, so the
start set entering `I_s` must be the range of the realization, not an
over-approximation of it. The previous surface of this module took an arbitrary
`R : Finset (Fin G)` together with `hR : ∀ i, ρ i ∈ R`, which lets `R` carry
*spurious* starts. That is a strictly weaker hypothesis: every clause of
`InformationFeasible` is a "some `r ∈ R` does …" or a coverage condition, so
inflating `R` can only make `I_s` easier to satisfy. This section names the
exact range and proves the transfer, so the final theorems of §5 can be stated
with no `R` at all.

The substantive content is `informationFeasible_of_exact_subset`: subset
containment *together with* the absence of spurious starts recovers
`I_s` at `realizedStarts ρ`. -/

/-- **The set of distinct start positions actually realized by the reads `ρ`.**
This is `range ρ` as a `Finset`; it is the start set the source's `I_s` is
stated over. -/
def realizedStarts {G n : ℕ} (ρ : OrientedSameLengthML.Realization G n) :
    Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => ∃ i : Fin n, ρ i = r)

@[simp] theorem mem_realizedStarts {G n : ℕ} (ρ : OrientedSameLengthML.Realization G n)
    (r : Fin G) : r ∈ realizedStarts ρ ↔ ∃ i : Fin n, ρ i = r := by
  simp [realizedStarts]

/-- Every realized read start lies in `realizedStarts`. -/
theorem mem_realizedStarts_self {G n : ℕ} (ρ : OrientedSameLengthML.Realization G n)
    (i : Fin n) : ρ i ∈ realizedStarts ρ :=
  (mem_realizedStarts ρ _).mpr ⟨i, rfl⟩

/-- **`I_s` at the exact range of `ρ` follows from `I_s` at a start set that is
exactly the range.** A start set `R` containing the range *and* carrying no
spurious start is the range, so the two hypotheses agree; in particular the
`hR : ∀ i, ρ i ∈ R` of the earlier surface is only half of what is needed, and
`hRanti` is the missing half. -/
theorem informationFeasible_of_exact_subset {α : Type} [DecidableEq α] [Fintype α]
    {G L n : ℕ} (hG : 0 < G) (S : Fin G → α) (ρ : OrientedSameLengthML.Realization G n)
    (R : Finset (Fin G)) (hsub : ∀ i : Fin n, ρ i ∈ R)
    (hanti : ∀ r ∈ R, ∃ i : Fin n, ρ i = r)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R) :
    InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ) := by
  have heq : ∀ r : Fin G, r ∈ realizedStarts ρ ↔ r ∈ R := by
    intro r
    rw [mem_realizedStarts]
    constructor
    · rintro ⟨i, hi⟩; simpa only [hi] using hsub i
    · rintro hr; obtain ⟨i, hi⟩ := hanti r hr; exact ⟨i, hi⟩
  have hbc : ∀ (e : ℕ) (t : Fin G), BridgesCopy ⟨G, hG, S⟩ L R e t →
      BridgesCopy ⟨G, hG, S⟩ L (realizedStarts ρ) e t := by
    intro e t ht
    obtain ⟨r, hr, d, hd, hpos⟩ := ht
    obtain ⟨i, hi⟩ := hanti r hr
    exact ⟨ρ i, (heq (ρ i)).mpr (hi ▸ hr), d, hd, hi ▸ hpos⟩
  rcases hfeas with ⟨hcov, htri, hinter⟩
  refine ⟨fun p => ?_, fun e a b c h => ?_, fun e₁ e₂ a b c d h₁ h₂ hi => ?_⟩
  · obtain ⟨r, hr, hcov⟩ := hcov p
    exact ⟨r, (heq r).mpr hr, hcov⟩
  · obtain ⟨e, he⟩ := e
    obtain ⟨ha, hb, hc⟩ := htri ⟨e, he⟩ a b c h
    exact ⟨hbc e a ha, hbc e b hb, hbc e c hc⟩
  · obtain ⟨e₁, he₁⟩ := e₁
    obtain ⟨e₂, he₂⟩ := e₂
    rcases hinter ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ a b c d h₁ h₂ hi with h | h | h | h
    · exact Or.inl (hbc e₁ a h)
    · exact Or.inr (Or.inl (hbc e₁ b h))
    · exact Or.inr (Or.inr (Or.inl (hbc e₂ c h)))
    · exact Or.inr (Or.inr (Or.inr (hbc e₂ d h)))

/-! ## 3. The faithful §6.2 maximum-likelihood predicate -/

/-- **A genuine §6.2 maximum-likelihood sequence, in the literal strict-oriented
§6.2 model.** Both clauses are present:

* *membership* — the truth carries a genuine `SpelledFeasible62` certificate for
  the observed read set, i.e. `SameLength62Maximizer.Is62Candidate62`;
* *dominance* — every same-length `Fin G → α` word carrying such a certificate
  for the same observed read set has exact same-length likelihood at most the
  truth's.

Both genomes are `Fin G → α` at the same length `G`, so "same length" is part
of the type rather than a hypothesis, and the objective is
`AssemblyP1.OrientedSameLengthML.exactLik` with the candidate-intrinsic
`N(D) = G`. -/
def Is62SpelledMLMax {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (x : OrientedSameLengthML.ObservedReads α L) : Prop :=
  SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList (fun y => y)
      (fun y => y) oMin ∧
    ∀ (D : Fin G → α),
      SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList (fun y => y)
        (fun y => y) oMin →
      OrientedSameLengthML.exactLik (L := L) hG D x
        ≤ OrientedSameLengthML.exactLik (L := L) hG S x

/-- **The audited #88 result, in the faithful maximizer predicate.** Full `I_s`,
a realization, a genuine §6.2 truth certificate, a genuine §6.2 candidate
certificate and the residual `hno` premise give the maximizer statement *with
membership*. -/
theorem informationFeasible_62_spelledML_of_no_long_triple {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (R : Finset (Fin G))
    (hR : ∀ i : Fin n, ρ i ∈ R)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  refine ⟨hStruth, fun D hD => ?_⟩
  exact SameLength62Maximizer.informationFeasible_62_maximizer hG hL2 hLG S D ρ R hR
    hfeas hwx hStruth hD

/-! ## 3. The likelihood comparison is the spectral comparison

The two product lemmas below are proved here rather than quoted: in this
Mathlib revision `ℝ` carries no `MulLeftMono` / `IsOrderedCancelMonoid`
instance, so the standard `Finset.prod_le_prod` / `Finset.prod_lt_prod` are not
available for `ℝ`. Both are the usual inductions. -/

/-- Pointwise comparison of nonnegative factors gives a comparison of the
products. -/
private theorem prod_le_prod_of_nonneg {ι : Type} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, f i ≤ g i) (hp : ∀ i ∈ s, 0 ≤ f i) : s.prod f ≤ s.prod g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      have h0 : f a ≤ g a := h a (Finset.mem_insert_self a s)
      have hp0 : 0 ≤ f a := hp a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, f i ≤ g i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hprest : ∀ i ∈ s, 0 ≤ f i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
      exact mul_le_mul h0 (ih hrest hprest) (Finset.prod_nonneg hprest) (hp0.trans h0)

/-- One strictly smaller factor, all others no larger, all factors of both
products positive: the products are strictly comparable. -/
private theorem prod_lt_prod_of_pos {ι : Type} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, f i ≤ g i) (hpf : ∀ i ∈ s, 0 < f i) (hpg : ∀ i ∈ s, 0 < g i)
    (hex : ∃ i ∈ s, f i < g i) : s.prod f < s.prod g := by
  classical
  obtain ⟨a, ha, hfa⟩ := hex
  have hle : (s.erase a).prod f ≤ (s.erase a).prod g :=
    prod_le_prod_of_nonneg (s.erase a) f g
      (fun i hi => h i (Finset.mem_of_mem_erase hi))
      (fun i hi => (hpf i (Finset.mem_of_mem_erase hi)).le)
  have hpf' : 0 < (s.erase a).prod f :=
    Finset.prod_pos (fun i hi => hpf i (Finset.mem_of_mem_erase hi))
  have hlt : f a * (s.erase a).prod f < g a * (s.erase a).prod g :=
    mul_lt_mul hfa hle hpf' (hpg a ha).le
  have hlt' : (s.erase a).prod f * f a < (s.erase a).prod g * g a := by
    simpa only [mul_comm] using hlt
  have hmul : s.prod f = (s.erase a).prod f * f a :=
    (Finset.prod_erase_mul s f ha).symm
  have hmul' : s.prod g = (s.erase a).prod g * g a :=
    (Finset.prod_erase_mul s g ha).symm
  rw [hmul, hmul']
  linarith [mul_le_mul_of_nonneg_right hle (hpg a ha).le, hlt']

/-- Every read type the observation mentions lies in the truth's window
support: the observable consequence of a realization on the truth. -/
theorem observed_mem_support {G L n : ℕ} (hG : 0 < G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (w : Fin L → α)
    (hw : 0 < OrientedSameLengthML.observedOf hG S ρ w) :
    w ∈ OrientedRigidity.support (L := L) hG S :=
  OrientedSameLengthML.observedOf_mem_support hG S ρ w hw

/-- **Every observed read type is a window of the truth, hence in its
`Finset` window support.** -/
theorem observed_mem_support' {G L n : ℕ} (hG : 0 < G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (w : Fin L → α)
    (hw : 0 < OrientedSameLengthML.observedOf hG S ρ w) :
    w ∈ OrientedRigidity.support (L := L) hG S := by
  by_contra hcon
  have hne : ∀ r : Fin G, OrientedRigidity.window (L := L) hG S r ≠ w :=
    fun r hr => hcon ((OrientedSameLengthML.mem_support_iff_window hG S w).mpr ⟨r, hr⟩)
  have hzero : OrientedSameLengthML.observedOf hG S ρ w = 0 := by
    unfold OrientedSameLengthML.observedOf
    exact Finset.sum_eq_zero fun i _ => if_neg (hne (ρ i))
  omega

/-- A read type's multiplicity is at most the genome length, so every factor
base `d w / G` lies in `[0, 1]`. -/
theorem specCount_le {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (w : Fin L → α) :
    OrientedRigidity.specCount (L := L) hG S w ≤ G := by
  unfold OrientedRigidity.specCount
  have hsub : ((Finset.univ : Finset (Fin G)).filter
      (fun r : Fin G => OrientedRigidity.window (L := L) hG S r = w))
      ⊆ (Finset.univ : Finset (Fin G)) := Finset.filter_subset _ _
  simpa using Finset.card_le_card hsub

/-- **Off the support, the objective factor is `1`.** The exponent is `0`
there, because the observation mentions only read types of the truth. -/
theorem factor_eq_one_of_not_mem {G L n : ℕ} (hG : 0 < G) (S D : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (w : Fin L → α)
    (hw : w ∉ OrientedRigidity.support (L := L) hG S) :
    OrientedSameLengthML.exactFactor hG D (OrientedSameLengthML.observedOf hG S ρ) w = 1 := by
  have hx : OrientedSameLengthML.observedOf hG S ρ w = 0 := by
    refine Nat.eq_zero_of_not_pos fun hpos => hw (observed_mem_support hG S ρ w hpos)
  simp [OrientedSameLengthML.exactFactor, hx]

/-- **The objective is the product over the truth's window support.** -/
theorem exactLik_eq_prod_support {G L n : ℕ} (hG : 0 < G) (S D : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) :
    OrientedSameLengthML.exactLik (L := L) hG D (OrientedSameLengthML.observedOf hG S ρ)
      = ∏ w ∈ (OrientedRigidity.support (L := L) hG S : Finset (Fin L → α)),
          OrientedSameLengthML.exactFactor hG D (OrientedSameLengthML.observedOf hG S ρ) w := by
  have hsub : (Finset.univ : Finset (Fin L → α)) ⊇
      OrientedRigidity.support (L := L) hG S := Finset.subset_univ _
  unfold OrientedSameLengthML.exactLik
  exact (Finset.prod_subset hsub
    (fun w _ hw => factor_eq_one_of_not_mem hG S D ρ w hw)).symm

/-- **Pointwise spectral domination on the observed read types gives the
likelihood inequality.**

Every factor is `(d w / G) ^ (x w)`: the base is in `(0, 1]` on the support
(the multiplicity of a read type is at most `G`) and the factor is `1` off it
(nothing is observed there), so the product over the support is monotone in
each multiplicity, and the likelihood comparison follows from the pointwise
comparison of the two spectra on the observed read types.

**Direction, and why only this direction.** This is a *sufficient* condition,
and the converse is **false** in general: two same-support same-length spectra
of equal total mass can differ in both directions at once, and the likelihood
product can then go either way. So the exact content of ML failure is the
weaker statement `observed_spectral_excess_of_ml_failure` below, which is the
contrapositive of this theorem and is all the reduction needs. -/
theorem exactLik_le_of_spec_le {G L n : ℕ} (hG : 0 < G) (S D : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n)
    (hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S)
    (hdom : ∀ w : Fin L → α, 0 < OrientedSameLengthML.observedOf hG S ρ w →
        OrientedRigidity.specCount (L := L) hG D w
          ≤ OrientedRigidity.specCount (L := L) hG S w) :
    OrientedSameLengthML.exactLik (L := L) hG D (OrientedSameLengthML.observedOf hG S ρ)
      ≤ OrientedSameLengthML.exactLik (L := L) hG S (OrientedSameLengthML.observedOf hG S ρ) := by
  have hmemS : ∀ w : Fin L → α,
      w ∈ OrientedRigidity.support (L := L) hG S ↔
        0 < OrientedRigidity.specCount (L := L) hG S w :=
    fun w => (OrientedSameLengthML.specCount_pos_iff hG S w).symm
  have hmemD : ∀ w : Fin L → α,
      w ∈ OrientedRigidity.support (L := L) hG S ↔
        0 < OrientedRigidity.specCount (L := L) hG D w := by
    intro w
    rw [← hsup, (OrientedSameLengthML.specCount_pos_iff hG D w).symm]
  have hfac : ∀ (w : Fin L → α) (hw : w ∈ OrientedRigidity.support (L := L) hG S)
      (hx : 0 < OrientedSameLengthML.observedOf hG S ρ w),
      (OrientedSameLengthML.exactFactor hG D (OrientedSameLengthML.observedOf hG S ρ) w
          ≤ OrientedSameLengthML.exactFactor hG S (OrientedSameLengthML.observedOf hG S ρ) w) := by
    intro w hw hx
    have hG0 : (0 : ℝ) < G := by exact_mod_cast hG
    have hne : (OrientedSameLengthML.observedOf hG S ρ w : ℕ) ≠ 0 := by omega
    have hmono : StrictMonoOn
        (fun x : ℝ => (x / (G : ℝ)) ^ (OrientedSameLengthML.observedOf hG S ρ w))
        {x : ℝ | (0 : ℝ) ≤ x} := by
      intro x hx' y hy hxy
      exact pow_lt_pow_left₀ (div_lt_div_of_pos_right hxy (by exact_mod_cast hG))
        (div_nonneg hx' hG0.le) hne
    have hdpos : 0 < OrientedRigidity.specCount (L := L) hG D w := (hmemD w).mp hw
    have h0 : (0 : ℝ) ≤ (OrientedRigidity.specCount (L := L) hG D w : ℝ) := by positivity
    have h0' : (0 : ℝ) ≤ (OrientedRigidity.specCount (L := L) hG S w : ℝ) := by
      have := (hmemS w).mp hw
      positivity
    rw [OrientedSameLengthML.exactFactor, OrientedSameLengthML.exactFactor]
    exact (hmono.le_iff_le h0 h0').mpr (by exact_mod_cast hdom w hx)
  rw [exactLik_eq_prod_support hG S D ρ, exactLik_eq_prod_support hG S S ρ]
  refine prod_le_prod_of_nonneg
    (OrientedRigidity.support (L := L) hG S)
    (OrientedSameLengthML.exactFactor hG D (OrientedSameLengthML.observedOf hG S ρ))
    (OrientedSameLengthML.exactFactor hG S (OrientedSameLengthML.observedOf hG S ρ))
    ?_ (fun i _ => by rw [OrientedSameLengthML.exactFactor]; positivity)
  intro i hi
  by_cases hxi : OrientedSameLengthML.observedOf hG S ρ i = 0
  · rw [OrientedSameLengthML.exactFactor, OrientedSameLengthML.exactFactor, hxi]
    simp
  · exact hfac i hi (Nat.pos_of_ne_zero hxi)

/-- **ML failure in the same-support class exhibits a strict spectral excess at
an observed read type.** This is the target-shaped contrapositive: the ML
question in the §6.2 same-length class is answered by the pointwise spectral
comparison on the observed read types. -/
theorem observed_spectral_excess_of_ml_failure {G L n : ℕ} (hG : 0 < G)
    (S D : Fin G → α) (ρ : OrientedSameLengthML.Realization G n)
    (hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S)
    (hml : ¬ (OrientedSameLengthML.exactLik (L := L) hG D
        (OrientedSameLengthML.observedOf hG S ρ)
        ≤ OrientedSameLengthML.exactLik (L := L) hG S
          (OrientedSameLengthML.observedOf hG S ρ))) :
    ∃ w : Fin L → α, 0 < OrientedSameLengthML.observedOf hG S ρ w ∧
      OrientedRigidity.specCount (L := L) hG D w
        > OrientedRigidity.specCount (L := L) hG S w := by
  by_contra hcon
  push Not at hcon
  exact hml (exactLik_le_of_spec_le hG S D ρ hsup hcon)

/-! ## 4. The graph-level culprit, and the target theorem

The culprit statement has three steps, and **two of them are proved here**:

* Step 1 (`spectralEscape_gives_longTriple`): a spectral escape forces a long
  maximal triple repeat of the truth, by applying the existing rigidity chain to
  the escaping circulation. This is at the `HasSpectralEscape` level, not only
  at the candidate level, because the chain's proof never uses that the
  circulation is the spectrum of a word.
* Step 2 (`informationFeasible_escape_gives_wraparound`): under full `I_s`,
  that long triple cannot lie in the mid-range band
  (`informationFeasible_no_midRangeTriple`), so by `longTriple_band` it lies in
  the **wraparound band** `max (L - 1) (G - L) ≤ ℓ < G`, named here by
  `HasWraparoundTripleRepeat`. This is the regime the audited `hno` premise
  excluded and `I_s` does not forbid.
* Step 3 (**not** proved) is `EscapeForcesMidRangeRepeat`: an escape that also
  produces a wraparound-bridged long triple repeat produces a *mid-range* one
  as well. That is the whole remaining content, and
  `informationFeasible_62_spelledML_of_escape_crux` takes it as its single
  extra hypothesis. -/

/-- **A positive balanced circulation of total mass `G` on the truth's window
support.** These are literally the three hypotheses
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity` consumes,
with the candidate's spectrum replaced by an arbitrary weighting `B` of the
truth's support. -/
def IsMassGPositiveCirculation {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : (Fin L → α) → ℕ) : Prop :=
  (∀ w : Fin L → α,
      w ∈ OrientedRigidity.support (L := L) hG S ↔ 0 < B w) ∧
    OrientedRigidity.Balanced (OrientedRigidity.winPrefix (α := α) (L := L))
      (OrientedRigidity.winSuffix (α := α) (L := L))
      (OrientedRigidity.genomeNodes (L := L) hG S)
      (OrientedRigidity.support (L := L) hG S) B ∧
    (∑ w ∈ (OrientedRigidity.support (L := L) hG S : Finset (Fin L → α)), B w = G)

/-- `B` strictly exceeds the truth's spectrum at some read type. -/
def BeatsTruthSpectrum {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : (Fin L → α) → ℕ) : Prop :=
  ∃ w : Fin L → α, B w > OrientedRigidity.specCount (L := L) hG S w

/-- **Spectral escape.** Some positive balanced circulation of total mass `G`
on the truth's window support strictly exceeds the truth's spectrum at some
read type. -/
def HasSpectralEscape {G : ℕ} (hG : 0 < G) (S : Fin G → α) (L : ℕ) : Prop :=
  ∃ B : (Fin L → α) → ℕ,
    IsMassGPositiveCirculation hG S B ∧ BeatsTruthSpectrum hG S B


/-- **A same-support same-length candidate's spectrum is a mass-`G` positive
circulation of the truth's support.** This is the graph-level content of the
§6.2 bridge, and it is what promotes a candidate-level likelihood failure to
the circulation statement `HasSpectralEscape`. -/
theorem candidate_is_massG_positive_circulation {G L n : ℕ} (hG : 0 < G)
    (S D : Fin G → α) (ρ : OrientedSameLengthML.Realization G n)
    (hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S) :
    IsMassGPositiveCirculation hG S (OrientedRigidity.specCount (L := L) hG D) := by
  obtain ⟨hsup', hbal, htot⟩ :=
    OrientedSameLengthML.candidate_circulation_hypotheses hG S D
      (OrientedSameLengthML.observedOf hG S ρ)
      ⟨hsup, fun w hw => (OrientedSameLengthML.specCount_pos_iff hG D w).mpr
        (hsup ▸ observed_mem_support' hG S ρ w hw)⟩
  refine ⟨hsup', hbal, htot⟩

/-- **A mass-`G` positive circulation that does not beat the truth is the
truth's own spectrum.** Total mass `G` turns pointwise domination into
equality, so the only mass-`G` positive circulation of the support that fails
to exceed the truth's spectrum anywhere is the truth's spectrum itself. -/
theorem eq_specCount_of_massG_le {G : ℕ} {L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : (Fin L → α) → ℕ) (hB : IsMassGPositiveCirculation hG S B)
    (hle : ∀ w : Fin L → α, B w ≤ OrientedRigidity.specCount (L := L) hG S w) :
    ∀ w : Fin L → α, B w = OrientedRigidity.specCount (L := L) hG S w := by
  intro w
  by_contra hne
  have hwS : w ∈ OrientedRigidity.support (L := L) hG S := by
    by_contra hcon
    have hB0 : B w = 0 := by
      have hiff := hB.1 w
      have hnot : ¬ (0 < B w) := fun hpos => hcon (hiff.mpr hpos)
      omega
    have hS0 : OrientedRigidity.specCount (L := L) hG S w = 0 := by
      have hiff := OrientedSameLengthML.specCount_pos_iff hG S w
      have hnot : ¬ (0 < OrientedRigidity.specCount (L := L) hG S w) :=
        fun hpos => hcon (hiff.mp hpos)
      omega
    exact hne (hB0.trans hS0.symm)
  have hlt : (∑ w ∈ (OrientedRigidity.support (L := L) hG S :
      Finset (Fin L → α)), B w)
      < ∑ w ∈ (OrientedRigidity.support (L := L) hG S :
        Finset (Fin L → α)), OrientedRigidity.specCount (L := L) hG S w := by
    refine Finset.sum_lt_sum (fun i _ => hle i)
      ⟨w, hwS, lt_of_le_of_ne (hle w) (fun hbeq => hne hbeq)⟩
  have htot := hB.2.2
  have htot' : (∑ w ∈ (OrientedRigidity.support (L := L) hG S :
      Finset (Fin L → α)), OrientedRigidity.specCount (L := L) hG S w) = G :=
    OrientedRigidity.truth_total (L := L) hG S
  rw [htot, htot'] at hlt
  omega

/-- `cyc` depends only on the residue mod `G`, so a maximal triple repeat at
starts `a, b, c` is also one at the reduced starts `a % G, b % G, c % G`. This
is the transport from the `ℕ`-indexed `RepeatAdapter.HasLongTripleRepeat` to the
`Fin G`-indexed predicates of this module. -/
theorem isMaximalTriple_of_mod {G : ℕ} (hG : 0 < G) {S : Fin G → α}
    {a b c ℓ a' b' c' : ℕ} (htri : RepeatAdapter.IsMaximalTriple hG S a b c ℓ)
    (ha : a % G = a' % G) (hb : b % G = b' % G) (hc : c % G = c' % G) :
    RepeatAdapter.IsMaximalTriple hG S a' b' c' ℓ := by
  have hcyc : ∀ (x y : ℕ), x % G = y % G →
      OrientedRigidity.cyc hG S x = OrientedRigidity.cyc hG S y := by
    intro x y hxy
    unfold OrientedRigidity.cyc
    exact congrArg S (Fin.ext hxy)
  have hshift : ∀ (x y k : ℕ), x % G = y % G → (x + k) % G = (y + k) % G := by
    intro x y k hxy
    simp only [Nat.add_mod, Nat.mod_mod]
    rw [hxy, Nat.add_mod]
  have hshift : ∀ (x y k : ℕ), x % G = y % G → (x + k) % G = (y + k) % G := by
    intro x y k hxy
    simp only [Nat.add_mod, Nat.mod_mod]
    rw [hxy, Nat.add_mod]
  have hcycp : ∀ (x y k : ℕ), x % G = y % G →
      OrientedRigidity.cyc hG S (x + k) = OrientedRigidity.cyc hG S (y + k) := by
    intro x y k hxy
    exact hcyc (x + k) (y + k) (hshift x y k hxy)
  have hform : ∀ (x : ℕ), x + G - 1 = x + (G - 1) := by
    intro x
    omega
  have hag' : RepeatAdapter.TripleAgree hG S a' b' c' ℓ := by
    intro d hd
    have h1 := (htri.1 d hd).1
    have h2 := (htri.1 d hd).2
    refine ⟨?_, ?_⟩
    · rw [← hcycp a a' d ha, ← hcycp b b' d hb]
      exact h1
    · rw [← hcycp b b' d hb, ← hcycp c c' d hc]
      exact h2
  refine ⟨hag', ?_, ?_⟩
  · intro hccon
    refine htri.2.1 ?_
    have e1 : OrientedRigidity.cyc hG S (a' + (G - 1))
        = OrientedRigidity.cyc hG S (a + (G - 1)) := (hcycp a a' (G - 1) ha).symm
    have e2 : OrientedRigidity.cyc hG S (b' + (G - 1))
        = OrientedRigidity.cyc hG S (b + (G - 1)) := (hcycp b b' (G - 1) hb).symm
    have e3 : OrientedRigidity.cyc hG S (c' + (G - 1))
        = OrientedRigidity.cyc hG S (c + (G - 1)) := (hcycp c c' (G - 1) hc).symm
    rw [hform, hform, hform] at hccon
    rw [e1, e2, e3] at hccon
    rw [hform, hform, hform]
    exact hccon
  · intro hccon
    refine htri.2.2 ?_
    have e1 : OrientedRigidity.cyc hG S (a' + ℓ)
        = OrientedRigidity.cyc hG S (a + ℓ) := (hcycp a a' ℓ ha).symm
    have e2 : OrientedRigidity.cyc hG S (b' + ℓ)
        = OrientedRigidity.cyc hG S (b + ℓ) := (hcycp b b' ℓ hb).symm
    have e3 : OrientedRigidity.cyc hG S (c' + ℓ)
        = OrientedRigidity.cyc hG S (c + ℓ) := (hcycp c c' ℓ hc).symm
    rw [e1, e2, e3] at hccon
    exact hccon

/-- **Step 1 of the culprit statement, kernel-checked at the graph level.** A
spectral escape is incompatible with the absence of a long maximal triple
repeat of the truth: apply the existing rigidity chain to the escaping
circulation, which is one of its permitted inputs (its proof never uses that the
circulation comes from a word, so this step is about `HasSpectralEscape`, not
only about candidates). -/
theorem spectralEscape_contradiction {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hesc : HasSpectralEscape hG S L)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L) : False := by
  obtain ⟨B, hB, hbeats⟩ := hesc
  obtain ⟨w, hgt⟩ := hbeats
  have heq := OrientedFinal.oriented_same_length_spectrum_rigidity hG S hL2 hLG hno
    B hB.1 hB.2.1 hB.2.2
  exact absurd (heq w ▸ hgt) (Nat.lt_irrefl _)

/-- **Step 1, positive form.** A spectral escape forces a long maximal triple
repeat of the truth: if there were none, the rigidity chain applied to the
escaping circulation would make it equal to the truth's spectrum. -/
theorem spectralEscape_gives_longTriple {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hesc : HasSpectralEscape hG S L) :
    RepeatAdapter.HasLongTripleRepeat hG S L := by
  by_cases hp : RepeatAdapter.HasLongTripleRepeat hG S L
  · exact hp
  · exact False.elim (spectralEscape_contradiction hG hL2 hLG S hesc hp)

/-- **ML failure in the §6.2 same-length class produces a spectral escape.**

This is the target-shaped contrapositive. Read left to right: a genuine §6.2
candidate of the same length as the truth, under the §6.2 hypotheses, whose
exact finite likelihood is strictly larger than the truth's, yields at the
graph level a positive balanced circulation of total mass `G` on the truth's
window support that strictly exceeds the truth's spectrum at some read type.

Every ingredient is the repository's own machinery: the support equality comes
from the two `Is62Candidate62` certificates (`oriented_support_eq_of_genuine62`),
the observation-level hypothesis from the realization (`observed_mem_support'`),
the promotion of the observed excess from `observed_spectral_excess_of_ml_failure`,
and the mass-`G` circulation property from `candidate_circulation_hypotheses`. -/
theorem ml_failure_gives_spectral_escape {G L n : ℕ} (hG : 0 < G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin)
    (hml : ¬ (OrientedSameLengthML.exactLik (L := L) hG D
        (OrientedSameLengthML.observedOf hG S ρ)
        ≤ OrientedSameLengthML.exactLik (L := L) hG S
          (OrientedSameLengthML.observedOf hG S ρ))) :
    HasSpectralEscape hG S L := by
  have hsup := SameLength62Maximizer.oriented_support_eq_of_genuine62 (L := L)
    (toList := toList) hStruth hD rfl
  obtain ⟨w, hxw, hgt⟩ :=
    observed_spectral_excess_of_ml_failure hG S D ρ hsup hml
  exact ⟨OrientedRigidity.specCount (L := L) hG D,
    candidate_is_massG_positive_circulation hG S D ρ hsup, ⟨w, hgt⟩⟩

/-- **No spectral escape under full `I_s`.**

If `2 ≤ L`, `L ≤ G` and the realized reads are `I_s`-feasible, then no positive
balanced circulation of total mass `G` on the truth's window support strictly
exceeds the truth's spectrum.

Up to this commit this was the *open* target-shaped statement: it was equivalent
to the culprit statement `EscapeForcesMidRangeRepeat`, which this module carried
as an explicit unproved hypothesis. It is now a theorem, because
`informationFeasible_no_midRangeTriple` and `informationFeasible_no_escape_*`
follow from `BridgingBridge.informationFeasible_no_long_triple_repeat`, i.e.
from `I_s` alone. -/
theorem informationFeasible_no_escape {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : OrientedSameLengthML.Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ)) :
    ¬ HasSpectralEscape hG S L := by
  intro hesc
  exact spectralEscape_contradiction hG hL2 hLG S hesc
    (BridgingBridge.informationFeasible_no_long_triple_repeat hL2 hfeas)

/-- **The §6.2 maximum-likelihood statement in the literal strict-oriented
model, from full `I_s` alone.**

Let the truth `S` be a circular word of length `G`, let `ρ` be a realization of
`n` reads on `S`, and suppose the *realized* reads satisfy **full
source-faithful** `InformationFeasible` at read length `L` — that is, `I_s` is
stated at `realizedStarts ρ`, the range of `ρ` itself, with **no** auxiliary
start set and no slack (see §2). Suppose the truth is a genuine §6.2 candidate
for the observed read set, and let `D` be a **same-length genuine §6.2
candidate** for the same observed read set. Then the exact same-length
Medvedev–Brudno likelihood of `D` is at most the truth's.

**The hypothesis list is exactly the source's:** `2 ≤ L ≤ G`, full `I_s` at the
realized starts, and the §6.2 data (`hwx`, `hStruth`). There is **no**
long-triple-repeat premise, **no** primitivity or period premise, and **no**
escape or culprit hypothesis of any kind: the statement that was open until this
commit is now proved.

The proof route is the reduction of §3–§4 with the culprit step replaced by
`informationFeasible_no_escape`: the candidate's spectrum is a mass-`G` positive
circulation of the truth's support, the absence of an escape makes it pointwise
bounded by the truth's spectrum, total mass `G` turns that into equality, and
the likelihood comparison follows. -/
theorem informationFeasible_62_spelledML {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  have hnoesc : ¬ HasSpectralEscape hG S L :=
    informationFeasible_no_escape hG hL2 hLG S ρ hfeas
  refine ⟨hStruth, fun D hD => ?_⟩
  obtain ⟨hsupD, hbal, htot⟩ :=
    OrientedSameLengthML.candidate_circulation_hypotheses hG S D
      (OrientedSameLengthML.observedOf hG S ρ)
      (SameLength62Maximizer.genuine62_is_spelled_candidate hG S D
        (OrientedSameLengthML.observedOf hG S ρ) hStruth hD hwx)
  have hcir : IsMassGPositiveCirculation hG S
      (OrientedRigidity.specCount (L := L) hG D) :=
    ⟨hsupD, hbal, htot⟩
  have heq : ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w
      = OrientedRigidity.specCount (L := L) hG S w :=
    eq_specCount_of_massG_le (L := L) hG S (OrientedRigidity.specCount (L := L) hG D) hcir
      (fun w => Nat.le_of_not_gt (fun hgt => hnoesc
        ⟨OrientedRigidity.specCount (L := L) hG D, hcir, ⟨w, hgt⟩⟩))
  have hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S := by
    ext w
    exact (OrientedSameLengthML.specCount_pos_iff hG D w).symm.trans
      (hsupD w).symm
  exact exactLik_le_of_spec_le hG S D ρ hsup (fun w _ => Nat.le_of_eq (heq w))

/-- **The audited #88 result in the exact-range semantics, with the residual
`¬ HasLongTripleRepeat` premise made explicit.**

Weaker in its hypotheses than `informationFeasible_62_spelledML` only in that it
also exposes the nondegeneracy fact, which that theorem obtains from `I_s`
itself. It is kept because it is the statement that
`docs/same-length-62-maximizer.md` audits. -/
theorem informationFeasible_62_spelledML_of_no_long_triple_exact {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  refine ⟨hStruth, fun D hD => ?_⟩
  exact SameLength62Maximizer.informationFeasible_62_maximizer hG hL2 hLG S D ρ
    (realizedStarts ρ) (fun i => mem_realizedStarts_self ρ i) hfeas hwx hStruth hD

/-- **The subset-start-set variant of the same statement, retained for
comparison only.** `R` may carry starts that were never realized, which can only
make `I_s` easier to satisfy, so this is *not* the faithful reading of issue #88;
it is the weaker surface of the previous commit, kept so the two are directly
comparable. The faithful statement is `informationFeasible_62_spelledML`. -/
theorem informationFeasible_62_spelledML_of_subset_starts {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (R : Finset (Fin G))
    (hR : ∀ i : Fin n, ρ i ∈ R)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  refine ⟨hStruth, fun D hD => ?_⟩
  exact SameLength62Maximizer.informationFeasible_62_maximizer hG hL2 hLG S D ρ R
    hR hfeas hwx hStruth hD

/-! ## 5. Finite evidence for the culprit statement

`EscapeForcesMidRangeRepeat` is the one statement this module does not prove.
The check below is a complete `decide` computation for **binary** truths and
candidates of length `G = 7` and all read lengths `L` with `2 ≤ L ≤ 7`:
whenever a candidate has the truth's window support and its spectrum strictly
exceeds the truth's on a support read type, the truth carries a maximal triple
repeat of length in the mid-range band `L - 1 ≤ ℓ < 7 - L`.

`cand0_beats_truth0` and `candidate_escape_binary_witness` are included so that
the check is **not vacuous**: the premise of the checked implication is
realized, at the truth `0000001` and the candidate `0001001` with `L = 3`
(read type `100`, whose multiplicity goes from `1` to `2`). The non-vacuity
companion matters: an earlier harness in this repository's history was void for
exactly this reason, and `docs/same-length-exact-ml-88-refutation.md` §4 records
that incident.

This is **evidence, not a completeness proof**: it says nothing about `G > 7`,
about alphabets larger than binary, and it checks the *candidate-level* form of
the culprit statement (a same-support competitor that beats the truth), not the
`HasSpectralEscape` statement over arbitrary weightings `B`. It is recorded as
evidence precisely so that the culprit statement is presented as a conjectured
lemma, not as a proved one. Wider searches with the same definitions
(binary `G ≤ 9`, `3`-letter `G ≤ 7`) are recorded in
`docs/issue88-wraparound-contrapositive.md`; they found no violation of the
culprit statement, and no instance of full `I_s` with a same-support
same-length competitor that beats the truth. -/

/-- `G = 7 > 0`, as a concrete instance. -/
private theorem hG7 : 0 < 7 := by norm_num

/-- The truth `0000001`, over the binary alphabet. -/
def truth0 : Fin 7 → Fin 2 := ![0, 0, 0, 0, 0, 0, 1]

/-- A same-length candidate `0001001`. -/
def cand0 : Fin 7 → Fin 2 := ![0, 0, 0, 1, 0, 0, 1]

/-- The escape premise of the finite check, as a `Prop` with a `Decidable`
instance: the `decide` tactic needs the instance, and instance search does not
unfold `OrientedRigidity.support` / `specCount` on its own. -/
def BinaryCandidateEscape (S D : Fin 7 → Fin 2) (L : ℕ) : Prop :=
  OrientedRigidity.support (L := L) hG7 D = OrientedRigidity.support (L := L) hG7 S ∧
    (∃ w : Fin L → Fin 2, w ∈ OrientedRigidity.support (L := L) hG7 S ∧
      OrientedRigidity.specCount (L := L) hG7 D w
        > OrientedRigidity.specCount (L := L) hG7 S w)

instance (S D : Fin 7 → Fin 2) (L : ℕ) : Decidable (BinaryCandidateEscape S D L) := by
  unfold BinaryCandidateEscape OrientedRigidity.support OrientedRigidity.specCount
  infer_instance

/-- The read type `100`, at which the candidate strictly exceeds the truth. -/
def read100 : Fin 3 → Fin 2 := ![1, 0, 0]

/-- **The premise of the culprit statement is realized at a concrete
instance.** For the truth `0000001` and the same-length candidate `0001001`, at
read length `L = 3`, the read type `100` is in the truth's window support, the
candidate's multiplicity of it is strictly larger, and the two candidates have
the same window support. -/
theorem cand0_beats_truth0 :
    read100 ∈ OrientedRigidity.support (L := 3) hG7 truth0 ∧
      OrientedRigidity.specCount (L := 3) hG7 cand0 read100
        > OrientedRigidity.specCount (L := 3) hG7 truth0 read100 := by
  constructor
  · exact (OrientedSameLengthML.specCount_pos_iff hG7 truth0 read100).mp
      (by decide)
  · decide

/-- The two window supports agree at this instance. -/
theorem cand0_support_eq_truth0 :
    OrientedRigidity.support (L := 3) hG7 cand0
      = OrientedRigidity.support (L := 3) hG7 truth0 := by decide

/-- **The escape premise, in full.** -/
theorem cand0_is_escape :
    OrientedRigidity.support (L := 3) hG7 cand0
      = OrientedRigidity.support (L := 3) hG7 truth0 ∧
      ∃ w : Fin 3 → Fin 2, w ∈ OrientedRigidity.support (L := 3) hG7 truth0 ∧
        OrientedRigidity.specCount (L := 3) hG7 cand0 w
          > OrientedRigidity.specCount (L := 3) hG7 truth0 w :=
  ⟨cand0_support_eq_truth0,
    Exists.intro read100 ⟨cand0_beats_truth0.1, cand0_beats_truth0.2⟩⟩

/-- The concrete maximal triple repeat of the truth `0000001` in the
mid-range band at `L = 3`: the three length-`2` windows at starts `0, 1, 4` are
all `00`, and the copy is maximal on both sides because the symbol before
start `0` is the `1` at position `6` and the symbol after start `4` is the same
`1`. -/
theorem truth0_midrange_witness :
    ∃ (a b c ℓ : Fin 7), 2 ≤ ℓ.val ∧ ℓ.val < 4 ∧
      a.val % 7 ≠ b.val % 7 ∧ b.val % 7 ≠ c.val % 7 ∧ a.val % 7 ≠ c.val % 7 ∧
      RepeatAdapter.IsMaximalTriple hG7 truth0 a.val b.val c.val ℓ.val :=
  ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨4, by norm_num⟩, ⟨2, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide⟩

/-- **The conclusion of the culprit statement holds at that instance.** -/
theorem truth0_has_midrange_triple : HasMidRangeTripleRepeat hG7 truth0 3 :=
  truth0_midrange_witness

/-- **The culprit statement, checked at one concrete non-vacuous instance:**
the escape premise holds and the mid-range conclusion holds. -/
theorem culprit_instance_checked :
    (OrientedRigidity.support (L := 3) hG7 cand0
      = OrientedRigidity.support (L := 3) hG7 truth0 ∧
      ∃ w : Fin 3 → Fin 2, w ∈ OrientedRigidity.support (L := 3) hG7 truth0 ∧
        OrientedRigidity.specCount (L := 3) hG7 cand0 w
          > OrientedRigidity.specCount (L := 3) hG7 truth0 w) ∧
    HasMidRangeTripleRepeat hG7 truth0 3 :=
  ⟨cand0_is_escape, truth0_has_midrange_triple⟩

end

end AssemblyP1.MLEscape
