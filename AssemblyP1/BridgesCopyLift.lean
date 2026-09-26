import AssemblyP1.MLEscape
import AssemblyP1.WraparoundTripleRepeat
import AssemblyP1.ExactVariantECounterexample
import AssemblyP1.FiniteSamplingCounterexample
import AssemblyP1.FixedLengthBinomialCounterexample
import AssemblyP1.FixedLengthExactCounterexample
import AssemblyP1.SameLengthExactMLCounterexample
import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.Section62BridgingCounterexample

/-!
# Audit of the bridging predicate: the same-lift reading, and what it implies

## The finding

`docs/bridging-source-semantics.md` records the source's bridging condition as
a **single-lift half-open interval** condition: a read `[r, r+L)` bridges a
chosen lifted occurrence `[t, t+ℓ)` exactly when

```
r < t    and    t + ℓ < r + L
```

i.e. the read strictly contains the selected copy, with at least one base on
each side.  In that reading a read can bridge a copy only if `ℓ + 2 ≤ L`.

`SourceFaithfulIs.BridgesCopy`, as merged, is **endpoint-only and modular**:

```
∃ r ∈ R, ReadCovers S L r ((t + G - 1) % G) ∧ ReadCovers S L r ((t + ℓ) % G)
```

It requires the read to touch the base before the copy and the base after it,
but it does **not** require the read to *contain* the copy: when the complement
arc is short (`G - ℓ ≤ L`) a single read reaches both flank bases by travelling
the *other* way round the circle.  That is not a read extending a base on each
side of the occurrence; it is a read sitting on the opposite arc.  The two
readings differ exactly there, and `BridgesCopy` is the weaker one, so
`SourceFaithfulIs.InformationFeasible` is **weaker** than the source formula
records.

`wraparound_witness_bridges_with_complement_arc` below is a kernel-checked
instance of the difference: the truth `AAAAB` at read length `3`, copy of
length `2` at start `0`, read at start `2`.  That read covers positions `4`
(the base before the copy) and `2` (the base after it) — but it covers them
across the complement arc `{2,3,4}`, and `ℓ + 2 = 4 > L = 3`.

## The corrected predicate

`BridgesCopyLift` is the modular form of the lifted interval condition: the
same read covers the base before the copy at offset `d` and the base after it at
offset `d + ℓ + 1`, with the whole span inside the read, i.e. `d + ℓ + 1 < L`.
Equivalently: there is a lift of the read start `r'` and of the copy start `t'`
with `r' < t'` and `t' + ℓ < r' + L`.

Two facts are proved here and are the whole content of the correction:

* `BridgesCopyLift.to_old`: the corrected predicate implies the merged one, so
  it is *strictly* stronger;
* `BridgesCopyLift.length_bound`: the corrected predicate forces `ℓ + 2 ≤ L`.

Together with `¬ (BridgesCopy → BridgesCopyLift)` in general (the witness),
this is a non-equivalence, not a refactorisation.

## What this does to `I_s`

With the corrected predicate, the all-bridged clause of `I_s` cannot be
satisfied by any triple repeat of length `ℓ ≥ L - 1`, because such a copy has
`ℓ + 2 > L` and hence is unbridgeable.  So:

* `informationFeasibleLift_triple_le`: under corrected `I_s`, every triple
  repeat of the truth has length `≤ L - 2`;
* `informationFeasibleLift_no_longTripleRepeat`: corrected `I_s` **excludes**
  long Bresler triple repeats.

The second statement is note §3 "Fact D", which every module in this repository
has recorded as *external / not kernel-checked* precisely because the merged
endpoint-only predicate could not deliver it: with that predicate, bridging is
possible in the wraparound mode `G - ℓ ≤ L`, and
`AssemblyP1.WraparoundTripleRepeat` is a kernel-checked `I_s`-feasible instance
carrying a long triple repeat.  Under the corrected predicate that instance is
**not** `I_s`-feasible (`wraparound_not_informationFeasible_lift` below), so
the "residual regime is non-empty" claim does not survive the correction.

## Consequences for #88

* The ML endpoint becomes unconditional with respect to repeats:
  `informationFeasibleLift_62_spelledML` is
  `informationFeasible_62_spelledML_of_no_long_triple` at
  `hno := informationFeasibleLift_no_longTripleRepeat`, i.e. full corrected
  `I_s` plus a realization plus a genuine §6.2 truth certificate suffice, with
  **no** long-triple-repeat premise and **no** culprit statement.
* The `EscapeForcesMidRangeRepeat` crux of `AssemblyP1.MLEscape` is not needed
  in that regime: it was introduced only because the merged predicate left the
  wraparound band (`ℓ ≥ G - L`) reachable.  Under the corrected predicate that
  band is unreachable, since a triple repeat there has `ℓ + 2 > L` as well.
* The conclusion is **independent of the certificate set `R`**: the derived
  bound `ℓ + 2 ≤ L` never mentions `R`, so corrected `I_s` excludes long triple
  repeats for *every* `R`.  This also settles the separate audit question about
  `R` being the realized start range (`ρ`) rather than a superset of it: under
  the corrected predicate the final theorem is the same statement for
  `R = range ρ`, for any `R ⊇ range ρ`, and in fact for any `R` whatsoever, so
  the subset-only reading is not a weaker hypothesis there.

## Trust surface

Nothing here is assumed: no `axiom`, no `sorry`, no `admit`.  The two
definitions (`BridgesCopyLift`, `InformationFeasibleLift`) are the *only* new
objects; `SourceFaithfulIs.BridgesCopy` and
`SourceFaithfulIs.InformationFeasible` are **left untouched**, so every merged
theorem of this repository continues to hold exactly as stated.  What changes is
the audit verdict recorded in `docs/bridging-lift-audit.md`: two `I_s`
witnesses (this repository's `AAAAB` instance, used twice) are not
source-faithful under the corrected predicate, and the seven counterexample
instances are (kernel-checked below, one per module).
-/

namespace AssemblyP1.LiftAudit

open SourceFaithfulIs
open Finset
open BigOperators

noncomputable section

variable {α : Type} [DecidableEq α]

/-- **Same-lift bridging.**  A read in `R` bridges the selected length-`e` copy
at start `t` when one read covers the base before the copy at offset `d` and
the base after it at offset `d + e + 1`, both offsets inside the read.  This is
the modular form of the lifted interval condition `r' < t' ∧ t' + e < r' + L`
of `docs/bridging-source-semantics.md`: the read strictly contains the copy
with at least one base on either side. -/
def BridgesCopyLift (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (t : Fin S.len) : Prop :=
  ∃ r ∈ R, ∃ d ∈ Finset.range L, d + e + 1 < L ∧
    (r.val + d) % S.len = (t.val + S.len - 1) % S.len ∧
    (r.val + d + e + 1) % S.len = (t.val + e) % S.len

omit [DecidableEq α] in
/-- The corrected predicate implies the merged one. -/
theorem BridgesCopyLift.to_old {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {e : ℕ} {t : Fin S.len} (h : BridgesCopyLift S L R e t) :
    BridgesCopy S L R e t := by
  obtain ⟨r, hr, d, -, hd, h1, h2⟩ := h
  exact ⟨r, hr, ⟨⟨d, by omega⟩, h1.symm⟩,
    ⟨⟨d + e + 1, by omega⟩, by simpa [Nat.add_assoc] using h2.symm⟩⟩

omit [DecidableEq α] in
/-- **Same-lift bridging forces the read to be longer than the copy by two.**
This is the `e + 2 ≤ L` half of the lifted interval condition, and it is what
the merged endpoint-only predicate loses. -/
theorem BridgesCopyLift.length_bound {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e : ℕ} {t : Fin S.len}
    (h : BridgesCopyLift S L R e t) : e + 2 ≤ L := by
  obtain ⟨r, hr, d, -, hd, h1, h2⟩ := h
  omega

/-- Same-lift bridging is *decidable*, by the same finite check as the merged
predicate: the offset `d` is bounded by the read length. -/
instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ) (t : Fin S.len) :
    Decidable (BridgesCopyLift S L R e t) := by
  unfold BridgesCopyLift; infer_instance

/-! ## The difference is a genuine non-equivalence -/

/-- **The merged endpoint-only predicate bridges a copy across the complement
arc.** The truth `AAAAB`, read length `3`, copy of length `2` at start `0`, read
at start `2`: that read covers position `4` (the base before the copy) and
position `2` (the base after it) by travelling the complement arc `{2,3,4}`, and
`e + 2 = 4 > L = 3`. -/
theorem wraparound_witness_bridges_with_complement_arc :
    BridgesCopy WraparoundTripleRepeat.truth 3 WraparoundTripleRepeat.readStarts 2 0 := by
  unfold BridgesCopy ReadCovers
  decide

/-- The same instance is **not** bridged in the same-lift reading: the length
condition `e + 2 ≤ L` fails. -/
theorem wraparound_witness_not_bridged_lift :
    ¬ BridgesCopyLift WraparoundTripleRepeat.truth 3 WraparoundTripleRepeat.readStarts 2 0 := by
  intro h
  have hbound := BridgesCopyLift.length_bound h
  norm_num at hbound

/-- **The two predicates are not equivalent.** There is no passage from the
merged endpoint-only predicate to the corrected one: the `AAAAB` instance
above is a counterexample to it. -/
theorem BridgesCopy_ne_BridgesCopyLift :
    ¬ (∀ (S : Genome WraparoundTripleRepeat.Sym) (L : ℕ)
        (R : Finset (Fin S.len)) (e : ℕ) (t : Fin S.len),
        BridgesCopy S L R e t → BridgesCopyLift S L R e t) :=
  fun h => wraparound_witness_not_bridged_lift
    (h _ _ _ _ _ wraparound_witness_bridges_with_complement_arc)

/-! ## Corrected `I_s` -/

/-- A triple repeat is all-bridged, in the same-lift reading. -/
def IsTripleRepeatAllBridgedLift (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e : ℕ) (a b c : Fin S.len) : Prop :=
  BridgesCopyLift S L R e a ∧ BridgesCopyLift S L R e b ∧ BridgesCopyLift S L R e c

/-- An interleaved pair is bridged, in the same-lift reading. -/
def IsInterleavedPairBridgedLift (S : Genome α) (L : ℕ) (R : Finset (Fin S.len))
    (e₁ e₂ : ℕ) (a b c d : Fin S.len) : Prop :=
  BridgesCopyLift S L R e₁ a ∨ BridgesCopyLift S L R e₁ b ∨
    BridgesCopyLift S L R e₂ c ∨ BridgesCopyLift S L R e₂ d

/-- **`I_s` in the same-lift reading of `docs/bridging-source-semantics.md`**:
coverage, every triple repeat all-bridged, every interleaved repeat pair
bridged, with the corrected bridging predicate throughout. -/
def InformationFeasibleLift (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) : Prop :=
  Covers S L R ∧
    (∀ (e : Fin S.len) (a b c : Fin S.len), S.IsTripleRepeat e.val a b c →
      IsTripleRepeatAllBridgedLift S L R e.val a b c) ∧
    (∀ (e₁ e₂ : Fin S.len) (a b c d : Fin S.len),
      S.IsRepeat e₁.val a b → S.IsRepeat e₂.val c d → Interleaved S a b c d →
        IsInterleavedPairBridgedLift S L R e₁.val e₂.val a b c d)

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (a b c : Fin S.len) :
    Decidable (IsTripleRepeatAllBridgedLift S L R e a b c) := by
  unfold IsTripleRepeatAllBridgedLift; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e₁ e₂ : ℕ)
    (a b c d : Fin S.len) :
    Decidable (IsInterleavedPairBridgedLift S L R e₁ e₂ a b c d) := by
  unfold IsInterleavedPairBridgedLift; infer_instance

instance (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) :
    Decidable (InformationFeasibleLift S L R) := by
  unfold InformationFeasibleLift; infer_instance

/-- Coverage clause, as for the merged predicate. -/
theorem InformationFeasibleLift.covers {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} (h : InformationFeasibleLift S L R) :
    Covers S L R := h.1

/-- **Note §3 Fact D, now kernel-checked:** under the same-lift reading of
`I_s`, every triple repeat of the truth has length `≤ L - 2`.  The bound does
not mention `R`. -/
theorem informationFeasibleLift_triple_le {α : Type} [DecidableEq α]
    {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)} {e : ℕ} {a b c : Fin S.len}
    (h : InformationFeasibleLift S L R) (ht : S.IsTripleRepeat e a b c) :
    e + 2 ≤ L := by
  have h1 := h.2.1 ⟨e, ht.2.1⟩ a b c ht
  exact BridgesCopyLift.length_bound h1.1

/-- Every triple repeat of a corrected-`I_s` truth is strictly shorter than the
reads: `e + 1 < L`. -/
theorem informationFeasibleLift_triple_lt {α : Type} [DecidableEq α]
    {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)} {e : ℕ} {a b c : Fin S.len}
    (h : InformationFeasibleLift S L R) (ht : S.IsTripleRepeat e a b c) :
    e + 1 < L := by
  have := informationFeasibleLift_triple_le h ht
  omega

/-- **Corrected `I_s` excludes long Bresler triple repeats.** This is the
`InformationFeasible → ¬ HasLongTripleRepeat` boundary that
`AssemblyP1.BridgingBridge` could only record as external, because the merged
endpoint-only bridging admits the wraparound mode. -/
theorem informationFeasibleLift_no_longTripleRepeat {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L) (_hLG : L ≤ G) (S : Fin G → α)
    (R : Finset (Fin G)) (hfeas : InformationFeasibleLift ⟨G, hG, S⟩ L R) :
    ¬ RepeatAdapter.HasLongTripleRepeat hG S L := by
  rintro ⟨a, b, c, ℓ, hℓ1, hℓG, hab, hbc, hac, htri⟩
  have hpa : a % G < G := Nat.mod_lt _ hG
  have hpb : b % G < G := Nat.mod_lt _ hG
  have hpc : c % G < G := Nat.mod_lt _ hG
  have h1 : 1 ≤ ℓ := by omega
  have ht : (⟨G, hG, S⟩ : Genome α).IsTripleRepeat ℓ ⟨a % G, hpa⟩
      ⟨b % G, hpb⟩ ⟨c % G, hpc⟩ :=
    BridgingBridge.isTripleRepeat_of_maximalTriple (S := ⟨G, hG, S⟩)
      (a := a) (b := b) (c := c) (ℓ := ℓ) h1 hℓG hab hac hbc
      htri.1 (fun h => htri.2.1 h) (fun h => htri.2.2 h)
  have hle := informationFeasibleLift_triple_lt hfeas ht
  omega

/-- **The same conclusion for *every* certificate set.** The bound derived from
the all-bridged clause never mentions `R`, so corrected `I_s` excludes long
triple repeats whatever `R` is: the exact realized start range, a superset of
it, or any set at all. -/
theorem informationFeasibleLift_no_longTripleRepeat_any {α : Type}
    [DecidableEq α] {G L : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) (R : Finset (Fin G))
    (hfeas : InformationFeasibleLift ⟨G, hG, S⟩ L R) :
    ¬ RepeatAdapter.HasLongTripleRepeat hG S L :=
  informationFeasibleLift_no_longTripleRepeat hG hL2 hLG S R hfeas

omit [DecidableEq α] in
/-- All-bridged in the same-lift reading implies all-bridged in the merged
reading. -/
theorem IsTripleRepeatAllBridgedLift.to_old {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e : ℕ} {a b c : Fin S.len}
    (h : IsTripleRepeatAllBridgedLift S L R e a b c) :
    IsTripleRepeatAllBridged S L R e a b c :=
  ⟨BridgesCopyLift.to_old h.1, BridgesCopyLift.to_old h.2.1,
    BridgesCopyLift.to_old h.2.2⟩

omit [DecidableEq α] in
/-- Bridged in the same-lift reading implies bridged in the merged reading. -/
theorem IsInterleavedPairBridgedLift.to_old {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e₁ e₂ : ℕ} {a b c d : Fin S.len}
    (h : IsInterleavedPairBridgedLift S L R e₁ e₂ a b c d) :
    IsInterleavedPairBridged S L R e₁ e₂ a b c d := by
  rcases h with h | h | h | h
  · exact Or.inl (BridgesCopyLift.to_old h)
  · exact Or.inr (Or.inl (BridgesCopyLift.to_old h))
  · exact Or.inr (Or.inr (Or.inl (BridgesCopyLift.to_old h)))
  · exact Or.inr (Or.inr (Or.inr (BridgesCopyLift.to_old h)))

/-- **Corrected `I_s` implies merged `I_s`**, clause by clause: the corrected
bridging predicate is strictly stronger, so every corrected-feasible instance
is merged-feasible.  This is why every merged theorem of the repository keeps
holding, and why no merged counterexample is invalidated by the correction. -/
theorem InformationFeasibleLift.to_old {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} (h : InformationFeasibleLift S L R) :
    InformationFeasible S L R :=
  ⟨h.1, fun e a b c ht =>
      IsTripleRepeatAllBridgedLift.to_old (h.2.1 ⟨e, ht.2.1⟩ a b c ht),
    fun e₁ e₂ a b c d h₁ h₂ hi =>
      IsInterleavedPairBridgedLift.to_old
        (h.2.2 ⟨e₁, h₁.2.1⟩ ⟨e₂, h₂.2.1⟩ a b c d h₁ h₂ hi)⟩

/-! ## The #88 endpoint under the corrected reading -/

/-- **The same-length §6.2 ML endpoint under the corrected reading of `I_s`.**
Full corrected information feasibility, a realization, and a genuine §6.2
certificate for the truth give exact same-length ML dominance over the literal
§6.2 candidate class.  There is no long-triple-repeat premise and no culprit
statement: the corrected bridging clause supplies `¬ HasLongTripleRepeat`
itself. -/
theorem informationFeasibleLift_62_spelledML {α : Type} [DecidableEq α]
    [Fintype α] {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : OrientedSameLengthML.Realization G n) (R : Finset (Fin G))
    (hR : ∀ i : Fin n, ρ i ∈ R)
    (hfeas : InformationFeasibleLift ⟨G, hG, S⟩ L R)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    MLEscape.Is62SpelledMLMax (verts := verts) (toList := toList) (oMin := oMin)
      hG S (OrientedSameLengthML.observedOf hG S ρ) :=
  MLEscape.informationFeasible_62_spelledML_of_no_long_triple hG hL2 hLG S ρ R
    hR hfeas.to_old
    (informationFeasibleLift_no_longTripleRepeat hG hL2 hLG S R hfeas)
    hwx hStruth


/-! ## Instance audit: every merged `I_s` witness, rechecked -/

/-! **#99 counterexample witnesses survive the correction.** Each of the seven
counterexample instances of this repository satisfies the *corrected* `I_s`, so
none of the merged counterexample theorems loses its hypothesis.  The reason is
structural rather than lucky: their repeats are short (`e ≤ L - 2`), so
bridging is genuine in both readings. -/
section CounterexampleWitnesses

/-- `FixedLengthExactCounterexample`: truth `AAABB`, `L = 3`, starts `0,1,4`. -/
theorem fixedLengthExact_witness_corrected :
    InformationFeasibleLift FixedLengthExactCounterexample.truthGenome 3
      FixedLengthExactCounterexample.readStarts := by
  decide

/-- `FixedLengthBinomialCounterexample`: truth `AAACC`, `L = 3`, starts
`0,1,4`. -/
theorem fixedLengthBinomial_witness_corrected :
    InformationFeasibleLift FixedLengthBinomialCounterexample.truthGenome 3
      FixedLengthBinomialCounterexample.readStarts := by
  decide

/-- `FiniteSamplingCounterexample`: truth `AABBC`, `L = 3`, starts `0,3`. -/
theorem finiteSampling_witness_corrected :
    InformationFeasibleLift FiniteSamplingCounterexample.truthGenome 3
      FiniteSamplingCounterexample.readStarts := by
  decide

/-- `ExactVariantECounterexample`: truth `ACGT`, `L = 2`, starts `0,2`. -/
theorem exactVariantE_witness_corrected :
    InformationFeasibleLift ExactVariantECounterexample.truthGenome 2
      ExactVariantECounterexample.readStarts := by
  decide

/-- `SameLengthExactMLCounterexample`: truth `AABB`, `L = 2`, starts `1,3`. -/
theorem sameLengthExactML_witness_corrected :
    InformationFeasibleLift SameLengthExactMLCounterexample.truthGenome 2
      SameLengthExactMLCounterexample.readStarts := by
  decide

/-- `SameLengthSection62Counterexample`: truth `AAATAT`, `L = 3`, starts
`0,1,3,5`. -/
theorem sameLengthSection62_witness_corrected :
    InformationFeasibleLift SameLengthSection62Counterexample.truthGenome 3
      SameLengthSection62Counterexample.realizedStarts := by
  decide

/-- `Section62BridgingCounterexample`: truth `AAATT`, `L = 3`, starts
`0,1,4`. -/
theorem section62Bridging_witness_corrected :
    InformationFeasibleLift Section62BridgingCounterexample.truthGenome 3
      Section62BridgingCounterexample.realizedStarts := by
  decide

end CounterexampleWitnesses

/-- **The `AAAAB` instance is not corrected-feasible.** This is the single
kernel-checked `I_s` witness in the repository that the correction invalidates:
it is exactly the wraparound-bridged one.  `WraparoundTripleRepeat`'s claim that
the residual long-triple-repeat regime is non-empty, and the
`SameLength62Maximizer` header's use of the same instance for the same purpose,
therefore do not survive the correction. -/
theorem wraparound_not_informationFeasible_lift :
    ¬ InformationFeasibleLift WraparoundTripleRepeat.truth 3
        WraparoundTripleRepeat.readStarts := by
  decide

/-- The same instance remains feasible for the *merged* predicate, so the two
readings genuinely disagree on it. -/
theorem wraparound_information_feasible_merged :
    InformationFeasible WraparoundTripleRepeat.truth 3
      WraparoundTripleRepeat.readStarts :=
  WraparoundTripleRepeat.wraparound_information_feasible

/-- The culprit instance of `AssemblyP1.MLEscape` (`0000001`, `G = 7`,
`L = 3`) is infeasible in **both** readings, as its module header records: its
maximal triple repeat of length `2` lies in the mid-range band `2 ≤ ℓ < 4`,
which the merged all-bridged clause already excludes.  The non-vacuity pairing
there is therefore unaffected by the correction. -/
theorem truth0_not_information_feasible_lift :
    ¬ InformationFeasibleLift ⟨7, by norm_num, MLEscape.truth0⟩ 3
      (Finset.univ : Finset (Fin 7)) := by
  decide

end

end AssemblyP1.LiftAudit
