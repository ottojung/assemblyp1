import AssemblyP1.BridgingBridge
import AssemblyP1.SameLength62Maximizer

/-!
# #88 in the wraparound regime: the faithful §6.2 ML predicate and the
# graph-level contrapositive

This module is the successor of `AssemblyP1.SameLength62Maximizer`. It does
three things, all kernel-checked, and it names the one statement that is still
missing.

## 0. What the audited head has, and what is still missing

`AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer` concludes
the same-length exact-likelihood inequality from full source-faithful
`InformationFeasible`, a genuine §6.2 certificate for the truth, a genuine
§6.2 certificate for the candidate, a realization — **and** the residual
premise `hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L`.

`AssemblyP1.WraparoundTripleRepeat` kernel-checks that `hno` is *not*
dischargeable from `I_s`: `AAAAB` at `G = 5`, `L = 3`, read at all five
starts, satisfies full `I_s`, has every one of its length-`3` windows observed
(hence is a genuine §6.2 candidate in the sense of `genuine62_support_eq`), and
carries a maximal triple repeat of length `2 = L - 1`. So the residual regime
is non-empty and the audited theorem does not settle it.

This module settles the *formulation* of that regime exactly, replaces the
opaque `hno` by the one band that clause 2 of `I_s` actually decides, and
reduces the remaining work to a single graph-level statement.

## 1. The band that `I_s` decides, and the band it does not

`HasMidRangeTripleRepeat` is the **mid-range band** `L - 1 ≤ ℓ < G - L` of
maximal triple repeats of the truth. This is exactly the band that
`BridgingBridge.tripleRepeat_bridged_length` forbids: a triple repeat of
length `e` that is all-bridged satisfies `e + 2 ≤ L ∨ G - e ≤ L`, so for
`e ≥ L - 1` one is forced into the wraparound mode `e ≥ G - L`.

`informationFeasible_no_midRangeTriple` is that consequence, and
`longTripleFree_no_midRangeTriple` shows `¬ HasLongTripleRepeat` implies
`¬ HasMidRangeTripleRepeat`. The two premises therefore agree under `I_s`,
which is precisely why `hno` looked like an extra assumption: it is exactly
the negation of a band that `I_s` already decides, plus the wraparound band
that `I_s` does not decide.

## 2. A genuinely faithful §6.2 maximum-likelihood predicate

`AssemblyP1.SameLengthExactMLCounterexample.Is62MaximumLikelihood` is a
*dominance* predicate: it has no membership conjunct, so refuting it does not
refute "the truth is a §6.2 candidate and maximises". `Is62SpelledMLMax` is
the maximizer predicate with membership:

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

`exactLik_le_iff` is the structural heart of this module, and it is proved
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
  circulation, by `candidate_circulation_hypotheses`). This is the
  target-shaped contrapositive: the open problem is the nonexistence of such a
  circulation.

## 4. The single remaining statement

`EscapeForcesMidRangeRepeat` is the culprit statement, isolated at the
graph/repeat level:

> if some positive balanced circulation of total mass `G` on the truth's window
> support strictly exceeds the truth's spectrum at some read type, then the
> truth carries a maximal triple repeat of length in the mid-range band
> `L - 1 ≤ ℓ < G - L`.

Combined with `informationFeasible_no_midRangeTriple` this discharges the `hno`
premise of the audited theorem, and

`informationFeasible_62_spelledML_of_escape_crux` is the resulting
target-shaped theorem: **full `I_s` plus a genuine §6.2 truth certificate, with
no long-triple-repeat premise at all**, covering the wraparound regime.
`EscapeForcesMidRangeRepeat` is an explicit hypothesis of that theorem; it is
not an axiom and not a `sorry`. It is the one step this module does not
perform, and it is stated at the level the reduction needs.

`informationFeasible_62_spelledML_of_no_long_triple` recovers the audited result
in the new predicate, so the two are directly comparable.

## 5. Finite evidence for the culprit statement

`EscapeForcesMidRangeRepeat` is the one statement this module does not prove.
What is kernel-checked is the small, **non-vacuous** core of the evidence:

* `cand0_is_escape` — the *premise* holds at a concrete instance: truth
  `0000001`, same-length candidate `0001001`, `G = 7`, `L = 3`, same window
  support, and the read type `100` has multiplicity `1` in the truth and `2` in
  the candidate;
* `truth0_has_midrange_triple` — the culprit statement's *conclusion* holds at
  that instance: the maximal triple repeat at starts `0, 1, 4` of length
  `2 ∈ [L - 1, G - L) = [2, 4)`;
* `culprit_instance_checked` — the two together.

The pairing is deliberate. An earlier harness in this repository's history was
void because the implication it checked had an unsatisfiable premise
(`docs/same-length-exact-ml-88-refutation.md` §4), and a non-vacuity companion
is the direct guard against repeating that.

The *quantified* version of the culprit statement (every binary truth and
candidate of length `G = 7`, every `2 ≤ L ≤ 7`) was attempted with `decide` and
**abandoned on build-cost grounds**: with `Finset`-based `support` and
`specCount` the kernel's `whnf` evaluator needs hundreds of millions of steps
(the module went from 4 s to over 8 minutes and 18 GB before being killed), so
such a statement would add hours to every build. It was run instead outside
Lean, with the same definitions, by `scripts/issue88-wraparound-search.py`, and
the results are in `docs/issue88-wraparound-contrapositive.md`: for binary
`G ≤ 9`, `3`-letter `G ≤ 7` and `4`-letter `G ≤ 6`, the culprit statement holds
at every escape (no violation), and **no** escape occurs at an
`I_s`-feasible instance. That is why the culprit statement is presented as a
conjectured lemma with computational support, and why
`informationFeasible_62_spelledML_of_escape_crux` takes it as an explicit
hypothesis.

This is evidence, not a completeness proof: the Lean check covers one concrete
instance, the search covers finite `G` and small alphabets, and both check the
*candidate-level* form of the culprit statement (a same-support competitor that
beats the truth) rather than `HasSpectralEscape` over arbitrary weightings
`B`.
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

/-! ## 2. The faithful §6.2 maximum-likelihood predicate -/

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
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  refine ⟨hStruth, fun D hD => ?_⟩
  exact SameLength62Maximizer.informationFeasible_62_maximizer hG hL2 hLG S D ρ R hR
    hfeas hno hwx hStruth hD

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

/-! ## 4. The graph-level culprit, and the target theorem -/

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

/-! ### The single remaining statement -/

/-- **The culprit statement.** A same-support same-mass positive circulation
that beats the truth's spectrum forces a maximal triple repeat of the truth in
the mid-range band `L - 1 ≤ ℓ < G - L` — the band that clause 2 of `I_s`
decides. -/
def EscapeForcesMidRangeRepeat {G : ℕ} (hG : 0 < G) (S : Fin G → α) (L : ℕ) : Prop :=
  HasSpectralEscape hG S L → HasMidRangeTripleRepeat hG S L

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

/-- **The target-shaped theorem for the wraparound regime.**

Let the truth `S` be a circular word of length `G`, let `R` be a set of latent
read starts carrying **full source-faithful** information feasibility at read
length `L`, and let `ρ` be a realization of `n` reads on `S` whose starts all
lie in `R`, so that the observation is `x = observedOf hG S ρ`. Suppose the
truth is itself a genuine §6.2 candidate for the observed read set, and let
`D` be a **same-length genuine §6.2 candidate** for the same observed read set.
Then the exact same-length likelihood of `D` is at most the truth's.

**There is no long-triple-repeat premise.** The only extra hypothesis is
`EscapeForcesMidRangeRepeat`, the culprit statement of §4, which is a
combinatorial assertion about the truth's own repeats: a same-support
same-mass positive circulation that beats the truth's spectrum forces a maximal
triple repeat in the band `L - 1 ≤ ℓ < G - L` that clause 2 of `I_s` forbids.
It is an explicit hypothesis, not an axiom and not a `sorry`; the point of this
theorem is that *nothing else* is needed, in particular neither
`¬ HasLongTripleRepeat` nor any primitivity or period premise.

The proof route is the reduction of §3–§4: the candidate's spectrum is a
mass-`G` positive circulation of the truth's support, the absence of an escape
makes it pointwise bounded by the truth's spectrum, total mass `G` turns that
into equality, and the likelihood comparison follows. -/
theorem informationFeasible_62_spelledML_of_escape_crux {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (R : Finset (Fin G))
    (hR : ∀ i : Fin n, ρ i ∈ R)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R)
    (hcrux : EscapeForcesMidRangeRepeat hG S L)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin) hG S
      (OrientedSameLengthML.observedOf hG S ρ) := by
  have hnomid : ¬ HasMidRangeTripleRepeat hG S L :=
    informationFeasible_no_midRangeTriple hG hL2 hLG S R hfeas
  have hnoesc : ¬ HasSpectralEscape hG S L := by
    rintro ⟨B, hB, hbeats⟩
    exact hnomid (hcrux ⟨B, hB, hbeats⟩)
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
