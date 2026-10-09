import AssemblyP1.MLEscape

/-!
# #211: the §6.2 same-length maximizer versus uniqueness up to rotation

This module audits, and then closes as far as the repository's own machinery
allows, the second conclusion schema of the oriented same-length §6.2 model:
**when the maximum-likelihood sequence is tied, is it the truth?**

The maximizer half of the question is already settled elsewhere and is *not*
re-proved here:

* `AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer`;
* `AssemblyP1.MLEscape.informationFeasible_62_spelledML` and
  `informationFeasible_62_spelledML_of_exact_subset`.

What this module adds is the tie analysis, and it is bad news for the uniqueness
reading of the 2016 sentence *as that reading is currently written down*:

1. **Every genuine §6.2 candidate under `I_s` is an exact tie**
   (`informationFeasible_62_exact_tie`). The `≤` in the maximizer theorem is an
   equality, so the maximizer statement is a tie statement by construction.
2. **The tie class is characterized, not restricted**: under `I_s`, a same-length
   word ties the truth exactly when it has the truth's window support
   (`same_support_word_ties_truth`), with no §6.2 certificate needed at all. The
   §6.2 side of the bridge
   (`SameLength62Maximizer.oriented_support_eq_of_genuine62`) puts every genuine
   §6.2 candidate inside that class, and `support_eq_iff_specCount_eq` shows the
   class is exactly the fibre of the truth's complete spectrum, counted by
   `docs/exact-same-length-spectrum-fibre-count.md`.
3. **The external complete-spectrum (BBT) premise is not a theorem of this
   model.** `AssemblyP1.OrientedSameLengthML.same_length_unique_up_to_rotation_of_bbt`
   consumes `hBBT : equal length-L spectrum → cyclic shift`. That premise is
   **false** for the same-length oriented model in general:
   `bbt_premise_refuted_G6_L2` exhibits two length-`6` binary circular words with
   equal length-`2` spectra that are not cyclic shifts, kernel-checked. So the
   uniqueness conclusion cannot be obtained from that route: the premise itself
   is the live residue, not a formality.
4. **The exact residue, stated as one proposition.** `SupportRigidity` is "every
   same-length circular word with the truth's window support is a cyclic shift
   of the truth". `support_rigidity_iff_fibre_singleton` shows it is equivalent
   under `I_s` to the spectrum-fibre form (`SpectrumFibreSingleton`), and
   `unique_62_maximizer_up_to_rotation_of_support_rigidity` shows it is exactly
   what the uniqueness reading of the §6.2 maximizer statement needs. §2 then
   isolates what closes it: `FibreFreedomForcesLongRepeat`, a purely
   combinatorial statement about circular words, suffices
   (`unique_maximizer_up_to_rotation_of_residue`), and `I_s` is precisely what
   forbids both of its disjuncts
   (`BridgingBridge.informationFeasible_no_long_triple_repeat` and
   `no_interleaved_long_repeats_of_Is`). §5 of the companion note
   `docs/same-length-62-tie-uniqueness-211.md` records the finite evidence.

§4 adds a **finite floor instance**: the first kernel-checked instance in the
repository at which the truth is simultaneously fully `I_s`-feasible and a
genuine §6.2 candidate (the `AABB`/`ABAB` witness of #88 could not provide this,
because its truth was not a member of the §6.2 class), together with the tie
conclusion verified at it and the fact that its fibre is a singleton
(`truth4_support_rigid`), so the residue is not vacuous there.

## Honest scope

Nothing here claims that the tie class is a singleton, and nothing here claims
it is not. The kernel-checked facts are the tie/equality theorems, the refutation
of the BBT premise, the finite floor instance, and the two finite checks of §3–§4
(`truth6_not_information_feasible`, `truth4_support_rigid`). The residue is a
named proposition, not a concealed hypothesis, and it is *not* the same as the
2016 paper's reconstruction theorem, although that theorem would imply it.

One distinction the wording of the maximizer statement invites, and that this
module keeps: the *tie class* — the set of circular genomes whose exact
likelihood equals the truth's — is characterized in theorem 2 as the support
class, while the *maximizer set* of
`SameLength62Maximizer.informationFeasible_62_maximizer` ranges over genuine §6.2
candidates only. Whether a given member of the tie class is itself a §6.2
candidate is a separate question, not settled here; it does not matter for the
residue, because the residue is stated over the support class.
-/

namespace AssemblyP1.SameLength62TieUniqueness

open AssemblyP1.OrientedSameLengthML
open AssemblyP1.OrientedRigidity
open AssemblyP1.SourceFaithfulIs

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. Every §6.2 maximizer under `I_s` is an exact tie

The maximizer theorem of `AssemblyP1.MLEscape` concludes `≤`. The same proof
concludes `=`, because the spectrum of a genuine same-length candidate is
forced to be the truth's spectrum. So the maximizer statement of this model is
a *tie* statement, and the uniqueness reading needs one further input.
-/

/-- **Same-length, under `I_s`, the truth's spectrum is determined by the truth's
window support.** Any circular word `D` of the same length as the truth whose
window support is the truth's has exactly the truth's length-`L` spectrum. No
§6.2 certificate, no candidate-class hypothesis: this is the escape machinery of
`AssemblyP1.MLEscape` applied to an *arbitrary* same-support word, which is the
form in which the reduction below is stated. -/
theorem Is_spectrum_eq_of_support_eq {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    (D : Fin G → α) (hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S) :
    ∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w
      = OrientedRigidity.specCount (L := L) hG S w := by
  have hnoesc : ¬ AssemblyP1.MLEscape.HasSpectralEscape hG S L :=
    AssemblyP1.MLEscape.informationFeasible_no_escape hG hL2 hLG S ρ hfeas
  have hcir : AssemblyP1.MLEscape.IsMassGPositiveCirculation hG S
      (OrientedRigidity.specCount (L := L) hG D) :=
    AssemblyP1.MLEscape.candidate_is_massG_positive_circulation hG S D ρ hsup
  exact AssemblyP1.MLEscape.eq_specCount_of_massG_le (L := L) hG S
    (OrientedRigidity.specCount (L := L) hG D) hcir
    (fun w => Nat.le_of_not_gt fun hgt => hnoesc
      ⟨OrientedRigidity.specCount (L := L) hG D, hcir, ⟨w, hgt⟩⟩)

/-- **The tie class is exactly the fibre of the truth's complete spectrum.**
Under `I_s`, support equality and spectrum equality coincide for a same-length
word. The `←` direction is purely formal (a spectrum is positive exactly on its
support); the `→` direction is `Is_spectrum_eq_of_support_eq`.

So the words that tie the truth under `I_s` are exactly the words in the fibre
of the truth's complete length-`L` spectrum, i.e. the fibre whose number of
rotation orbits `docs/exact-same-length-spectrum-fibre-count.md` counts with the
BEST theorem. Tie freedom is therefore exactly fibre freedom. -/
theorem support_eq_iff_specCount_eq {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    (D : Fin G → α) :
    OrientedRigidity.support (L := L) hG D
        = OrientedRigidity.support (L := L) hG S ↔
      (∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w
          = OrientedRigidity.specCount (L := L) hG S w) := by
  constructor
  · intro hsup w
    exact Is_spectrum_eq_of_support_eq hG hL2 hLG S ρ hfeas D hsup w
  · intro hspec
    ext w
    rw [(OrientedSameLengthML.specCount_pos_iff hG D w).symm,
      (OrientedSameLengthML.specCount_pos_iff hG S w).symm, hspec w]

/-- **Every genuine same-length §6.2 candidate is an exact tie.** Same
hypotheses as `AssemblyP1.MLEscape.informationFeasible_62_spelledML` *minus the
observation-level hypothesis* `hwx` — the equality does not need it, because it
is read off the two §6.2 certificates and the support bridge alone. The
conclusion is the maximizer theorem's `≤`, strengthened to `=`. -/
theorem informationFeasible_62_exact_tie {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    OrientedSameLengthML.exactLik (L := L) hG D (observedOf hG S ρ)
      = OrientedSameLengthML.exactLik (L := L) hG S (observedOf hG S ρ) := by
  have hsupD :=
    SameLength62Maximizer.oriented_support_eq_of_genuine62 (L := L) (toList := toList)
      hStruth hD rfl
  have heq := Is_spectrum_eq_of_support_eq hG hL2 hLG S ρ hfeas D hsupD
  exact OrientedSameLengthML.exactLik_congr_of_specCount_eq hG heq

/-- **The tie class is the same-support class, with no §6.2 certificate at
all.** Under `I_s`, a same-length circular word ties the truth's exact finite
objective exactly when it has the truth's window support. The `←` direction is
`Is_spectrum_eq_of_support_eq`; the `→` direction is the maximizer theorem. -/
theorem same_support_word_ties_truth {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    (D : Fin G → α) (hsup : OrientedRigidity.support (L := L) hG D
      = OrientedRigidity.support (L := L) hG S) :
    OrientedSameLengthML.exactLik (L := L) hG D (observedOf hG S ρ)
      = OrientedSameLengthML.exactLik (L := L) hG S (observedOf hG S ρ) := by
  have heq := Is_spectrum_eq_of_support_eq hG hL2 hLG S ρ hfeas D hsup
  exact OrientedSameLengthML.exactLik_congr_of_specCount_eq hG heq

/-- **The maximizer statement is a tie statement, hence not a uniqueness
statement.** For the same hypothesis set that
`AssemblyP1.MLEscape.informationFeasible_62_spelledML` carries — including its
observation-level hypothesis `_hwx` — both the `≤` of the maximizer schema and
the `=` of the tie schema hold. `_hwx` is underscore-prefixed because the
equality below does not use it: the observation clause is needed only to read
the §6.2 data as a spelled-candidate certificate, and this route reads the
support bridge directly.

The audit content is that the two conclusion schemas
`docs/ml-formalization-contract.md` requires to be kept apart are, in this
candidate class, *both true* — and the second one (uniqueness up to
equivalence) still does not follow from the first. See §2 for the missing
proposition. -/
theorem maximizer_and_tie_of_Is_and_62 {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (_hwx : ∀ w : Fin L → α,
      0 < OrientedSameLengthML.observedOf (L := L) hG S ρ w → w ∈ verts)
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    (∀ D : Fin G → α,
      SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
        (fun y => y) (fun y => y) oMin →
      OrientedSameLengthML.exactLik (L := L) hG D (observedOf hG S ρ)
        ≤ OrientedSameLengthML.exactLik (L := L) hG S (observedOf hG S ρ)) ∧
      (∀ D : Fin G → α,
        SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
          (fun y => y) (fun y => y) oMin →
        OrientedSameLengthML.exactLik (L := L) hG D (observedOf hG S ρ)
          = OrientedSameLengthML.exactLik (L := L) hG S (observedOf hG S ρ)) :=
  ⟨fun D hD => le_of_eq (informationFeasible_62_exact_tie hG hL2 hLG S ρ hfeas hStruth D hD),
    fun D hD => informationFeasible_62_exact_tie hG hL2 hLG S ρ hfeas hStruth D hD⟩

/-! ## 2. The exact residue: support rigidity

The uniqueness reading needs one proposition that this repository does not have:
`SupportRigidity`. It is stated here as a named predicate rather than smuggled
in as a hypothesis of a theorem, because it is the live mathematical content of
the uniqueness reading, and because the tempting external input (BBT) is refuted
by the model itself in §3.

Under `I_s` the residue is equivalent to the statement that the truth's spectrum
fibre is a singleton (`support_rigidity_iff_fibre_singleton`), i.e. to the fibre
count of `docs/exact-same-length-spectrum-fibre-count.md` being `1`; and §3
records that the external BBT premise which would deliver it does not hold in
this model.

`truth4_support_rigid` (§4) is a finite instance at which the residue does hold,
so the residue is not vacuous.
-/

/-- **Support rigidity of a circular truth.** Every circular word of the same
length whose length-`L` window support is the truth's is a cyclic shift of the
truth.

This is the *exact* open residue of the uniqueness reading in this model: under
`I_s` it is equivalent to fibre singularity
(`support_rigidity_iff_fibre_singleton`), and combined with the §6.2 bridge it is
the statement that no second tied maximizer exists. A reconstruction theorem
that recovers the truth from the read set would imply it; nothing in this
repository proves it. It is *not* refuted either — `bbt_premise_refuted_G6_L2`
refutes the *external* BBT premise at an instance that is not `I_s`-feasible
(`truth6_not_information_feasible`). -/
def SupportRigidity {G : ℕ} (hG : 0 < G) (S : Fin G → α) (L : ℕ) : Prop :=
  ∀ D : Fin G → α, OrientedRigidity.support (L := L) hG D
    = OrientedRigidity.support (L := L) hG S → OrientedFinal.IsCyclicShift hG D S

/-- **The spectrum-fibre form of the residue.** Two circular words of the same
length with equal length-`L` spectra are cyclic shifts. Refuted in general by
`equal_spectrum_not_cyclic_shift` below; recorded here as the form the residue
takes when the candidate class is given by spectra. -/
def SpectrumFibreSingleton {G : ℕ} (hG : 0 < G) (S : Fin G → α) (L : ℕ) : Prop :=
  ∀ D : Fin G → α, (∀ w : Fin L → α,
    OrientedRigidity.specCount (L := L) hG D w
      = OrientedRigidity.specCount (L := L) hG S w) →
    OrientedFinal.IsCyclicShift hG D S

/-- **Under `I_s`, the two forms of the residue agree.** Support equality and
spectrum equality are equivalent for same-length words once the truth is
information-feasible, so support rigidity and fibre singularity are the same
proposition. -/
theorem support_rigidity_iff_fibre_singleton {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ)) :
    SupportRigidity hG S L ↔ SpectrumFibreSingleton hG S L := by
  constructor
  · intro hsr D hspec
    refine hsr D ?_
    ext w
    rw [(OrientedSameLengthML.specCount_pos_iff hG D w).symm,
      (OrientedSameLengthML.specCount_pos_iff hG S w).symm, hspec w]
  · intro hfs D hsup
    refine hfs D ?_
    exact Is_spectrum_eq_of_support_eq hG hL2 hLG S ρ hfeas D hsup

omit [Fintype α] in
/-- **The uniqueness reading of the §6.2 maximizer, with the residue named.**
Under the §6.2 bridge, support rigidity makes every genuine same-length §6.2
candidate a cyclic shift of the truth. No `I_s` hypothesis is needed for this
step: it is the composition of the bridge with the residue proposition, and it
is the exact point at which the uniqueness reading is or is not true. -/
theorem unique_62_maximizer_up_to_rotation_of_support_rigidity {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) (hrig : SupportRigidity hG S L)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hStruth : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList
      (fun y => y) (fun y => y) oMin)
    (D : Fin G → α)
    (hD : SameLength62Maximizer.Is62Candidate62 ⟨G, hG, D⟩ verts toList
      (fun y => y) (fun y => y) oMin) :
    OrientedFinal.IsCyclicShift hG D S :=
  hrig D (SameLength62Maximizer.oriented_support_eq_of_genuine62 (L := L)
    (toList := toList) hStruth hD rfl)

/-! ### What `I_s` forbids, and what would close the residue

The residue is not a missing technicality of the plumbing: `I_s` itself forbids
both of the two repeat structures that a non-rigid spectrum fibre has to
manufacture. The two facts below are the `I_s` half; the combinatorial half is
`FibreFreedomForcesLongRepeat`.
-/

/-- **`I_s` forbids interleaved long maximal repeats.** A bridged copy of length
`e` straddles a read, so `e + 2 ≤ L`
(`SourceFaithfulIs.bridgesCopy_length`). Clause 3 of `I_s` bridges one of the
four copies of an interleaved pair of maximal repeats, so at least one of the two
lengths satisfies `e + 2 ≤ L`; two repeats of length `≥ L - 1` cannot. -/
theorem no_interleaved_long_repeats_of_Is {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (R : Finset (Fin G))
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L R)
    {e₁ e₂ : ℕ} {a b c d : Fin G}
    (h₁ : Genome.IsRepeat ⟨G, hG, S⟩ e₁ a b)
    (h₂ : Genome.IsRepeat ⟨G, hG, S⟩ e₂ c d)
    (hi : Interleaved ⟨G, hG, S⟩ a b c d)
    (hL₁ : L - 1 ≤ e₁) (hL₂ : L - 1 ≤ e₂) : False := by
  have hb : IsInterleavedPairBridged ⟨G, hG, S⟩ L R e₁ e₂ a b c d :=
    hfeas.interleaved h₁ h₂ hi h₁.2.1 h₂.2.1
  rcases hb with h | h | h | h
  · exact absurd (bridgesCopy_length h) (by omega)
  · exact absurd (bridgesCopy_length h) (by omega)
  · exact absurd (bridgesCopy_length h) (by omega)
  · exact absurd (bridgesCopy_length h) (by omega)

/-- **The exact combinatorial residue of the uniqueness reading.** If the fibre
of a circular word's complete length-`L` spectrum contains a word that is not a
cyclic shift of it, then the word carries a triple repeat of length `≥ L - 1`,
or two maximal repeats of length `≥ L - 1` whose selected starts interleave.

Both alternatives are repeat structures that `I_s` excludes outright, by the
triple-repeat clause and by `no_interleaved_long_repeats_of_Is` respectively.
This is the only mathematical input that separates the truth's maximizer
statement (proved) from its uniqueness-up-to-rotation reading (open in this
repository); it is a purely combinatorial statement about circular words and is
independent of the likelihood model.

`docs/same-length-62-tie-uniqueness-211.md` §5 records the exhaustive finite
check (`scripts/verify_samelength62_fibre_mechanism_211.py`): every circular
word whose spectrum fibre has two rotation orbits was found to satisfy one of
the two disjuncts, for every binary word of length ≤ 11 and every ternary word
of length ≤ 8. That is evidence, not a proof. -/
def FibreFreedomForcesLongRepeat {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (S : Fin G → α) : Prop :=
  (∃ D : Fin G → α,
      (∀ w : Fin L → α, OrientedRigidity.specCount (L := L) hG D w
          = OrientedRigidity.specCount (L := L) hG S w) ∧
      ¬ OrientedFinal.IsCyclicShift hG D S) →
    (∃ (e : ℕ) (a b c : Fin G), L - 1 ≤ e ∧ e < G ∧
        Genome.IsTripleRepeat ⟨G, hG, S⟩ e a b c) ∨
    (∃ (e₁ e₂ : ℕ) (a b c d : Fin G), L - 1 ≤ e₁ ∧ L - 1 ≤ e₂ ∧
        Genome.IsRepeat ⟨G, hG, S⟩ e₁ a b ∧ Genome.IsRepeat ⟨G, hG, S⟩ e₂ c d ∧
        Interleaved ⟨G, hG, S⟩ a b c d)

/-- **The uniqueness reading, given the combinatorial residue.** With
`FibreFreedomForcesLongRepeat` and full `I_s`, every same-length word with the
truth's window support — hence every genuine same-length §6.2 candidate — is a
cyclic shift of the truth. This is the exact shape of the missing proof: no
hypothesis about the likelihood, the observation or the §6.2 certificate is
needed beyond `I_s` itself. -/
theorem unique_maximizer_up_to_rotation_of_residue {G L n : ℕ}
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (ρ : Realization G n)
    (hfeas : InformationFeasible ⟨G, hG, S⟩ L (realizedStarts ρ))
    (hres : FibreFreedomForcesLongRepeat (L := L) hG S) :
    ∀ D : Fin G → α,
      OrientedRigidity.support (L := L) hG D
          = OrientedRigidity.support (L := L) hG S →
      OrientedFinal.IsCyclicShift hG D S := by
  intro D hsup
  by_contra hnot
  obtain hlong | hint := hres ⟨D,
    Is_spectrum_eq_of_support_eq (L := L) hG hL2 hLG S ρ hfeas D hsup, hnot⟩
  · -- a triple repeat of length `≥ L - 1` cannot be bridged: clause 2 of `I_s`
    obtain ⟨e, a, b, c, hLe, heG, htri⟩ := hlong
    obtain ⟨hab, _, _⟩ := hfeas.triples htri heG
    exact absurd (bridgesCopy_length hab) (by omega)
  · -- two interleaved repeats of length `≥ L - 1`: clause 3 of `I_s`
    obtain ⟨e₁, e₂, a, b, c, d, hLe₁, hLe₂, h₁, h₂, hi⟩ := hint
    exact no_interleaved_long_repeats_of_Is hG S (realizedStarts ρ) hfeas
      h₁ h₂ hi hLe₁ hLe₂

/-! ## 3. The external complete-spectrum premise is not a theorem of this model

`AssemblyP1.OrientedSameLengthML.same_length_unique_up_to_rotation_of_bbt`
consumes

```
hBBT : ∀ T, (∀ w, specCount T w = specCount S w) → IsCyclicShift T S
```

as an explicit external premise. For the *same-length oriented* model that
premise is false, and the finite instance below is the reason: two circular
words of the same length can have exactly the same multiset of length-`L`
windows and fail to be cyclic shifts. Equal spectra therefore do not pin down a
circular word, so the BBT route cannot deliver uniqueness in this model, and
the premise — not the bookkeeping — is the residue.

The instance is the smallest binary one: `G = 6`, `L = 2`. It agrees with
`docs/exact-same-length-spectrum-fibre-count.md` §"Checks and evidence", which
records that the capacity vector `AA = BB = 1, AB = BA = 2` has two cyclic
spelling orbits.
-/

/-- `G = 6`, for the concrete instance. -/
private theorem hG6 : 0 < 6 := by norm_num

/-- The truth `011001` as a length-`6` binary circular word. -/
def truth6 : Fin 6 → Fin 2 := ![0, 1, 1, 0, 0, 1]

/-- The same-length word `010011`, with the same multiset of length-`2` windows
and not a cyclic shift of `truth6`. -/
def cand6 : Fin 6 → Fin 2 := ![0, 1, 0, 0, 1, 1]

/-- **The `G = 6`, `L = 2` refutation witness is *not* `I_s`-feasible.** With
`L = 2` no copy of length `≥ 1` can be bridged at all (a bridged copy needs
`e + 2 ≤ L`), and `truth6` carries maximal repeats of length `2` at starts
`(0, 4)` and `(2, 5)` that interleave. The refutation is by
`no_interleaved_long_repeats_of_Is`, so the two repeat facts are the only
computations. Consequently `bbt_premise_refuted_G6_L2` refutes the *external*
BBT premise at an instance that lies **outside** the hypothesis surface of
`informationFeasible_62_maximizer`: the refuting witness is not a tied
maximizer, and it does not show that a tied maximizer exists under `I_s`. -/
theorem truth6_not_information_feasible :
    ¬ InformationFeasible ⟨6, hG6, truth6⟩ 2 Finset.univ := by
  intro hfeas
  have h₁ : Genome.IsRepeat ⟨6, hG6, truth6⟩ 2 0 4 := by decide
  have h₂ : Genome.IsRepeat ⟨6, hG6, truth6⟩ 2 2 5 := by decide
  have hi : Interleaved ⟨6, hG6, truth6⟩ 0 4 2 5 := by decide
  exact no_interleaved_long_repeats_of_Is hG6 truth6 Finset.univ hfeas
    h₁ h₂ hi (by omega) (by omega)

/-- **The two words have equal length-`2` spectra.** Kernel-checked. -/
theorem spectra_eq_G6_L2 :
    ∀ w : Fin 2 → Fin 2, OrientedRigidity.specCount (L := 2) hG6 cand6 w
      = OrientedRigidity.specCount (L := 2) hG6 truth6 w := by
  decide

/-- **The two words have equal window supports.** Kernel-checked. -/
theorem support_eq_G6_L2 :
    OrientedRigidity.support (L := 2) hG6 cand6
      = OrientedRigidity.support (L := 2) hG6 truth6 := by
  decide

/-- The value of a length-`6` binary word at an arbitrary integer position, read
around the circle. This is `OrientedRigidity.cyc` specialised to `G = 6`; the
`ℕ`-indexed form is used below so that the six possible shifts are reduced
modulo `6` without a motive failure on a `Fin` proof argument. -/
private def val6 (w : Fin 6 → Fin 2) : ℕ → Fin 2 :=
  fun i => w ⟨i % 6, by omega⟩

/-- **`cand6` is not a cyclic shift of `truth6`.** The shift is reduced modulo
`6` and the six possibilities are refuted. -/
theorem cand6_not_cyclic_shift_of_truth6 :
    ¬ OrientedFinal.IsCyclicShift hG6 cand6 truth6 := by
  rintro ⟨s, hs⟩
  have hs' : ∀ i : ℕ, val6 cand6 i = val6 truth6 (i + s) := hs
  have h2 : ∀ j : ℕ, val6 cand6 j = val6 truth6 (j + s % 6) := by
    intro j
    have e : val6 truth6 (j + s) = val6 truth6 (j + s % 6) := by
      have hv : (((⟨(j + s) % 6, by omega⟩ : Fin 6) : ℕ)
          = ((⟨(j + s % 6) % 6, by omega⟩ : Fin 6) : ℕ)) := by
        show (j + s) % 6 = (j + s % 6) % 6
        omega
      exact congrArg truth6 (Fin.ext hv)
    exact hs' j |>.trans e
  have h6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by
    omega
  rcases h6 with h | h | h | h | h | h
  · have hne : ¬ (val6 cand6 2 = val6 truth6 (2 + (s % 6))) := by rw [h]; decide
    exact hne (h2 2)
  · have hne : ¬ (val6 cand6 0 = val6 truth6 (0 + (s % 6))) := by rw [h]; decide
    exact hne (h2 0)
  · have hne : ¬ (val6 cand6 0 = val6 truth6 (0 + (s % 6))) := by rw [h]; decide
    exact hne (h2 0)
  · have hne : ¬ (val6 cand6 1 = val6 truth6 (1 + (s % 6))) := by rw [h]; decide
    exact hne (h2 1)
  · have hne : ¬ (val6 cand6 3 = val6 truth6 (3 + (s % 6))) := by rw [h]; decide
    exact hne (h2 3)
  · have hne : ¬ (val6 cand6 0 = val6 truth6 (0 + (s % 6))) := by rw [h]; decide
    exact hne (h2 0)

/-- **The external BBT premise fails in this model.** Instantiated at the
`G = 6`, `L = 2` binary instance: `cand6` has exactly the length-`2` spectrum of
`truth6` and is not a cyclic shift of it. -/
theorem bbt_premise_refuted_G6_L2 :
    ¬ (∀ T : Fin 6 → Fin 2, (∀ w : Fin 2 → Fin 2,
      OrientedRigidity.specCount (L := 2) hG6 T w
        = OrientedRigidity.specCount (L := 2) hG6 truth6 w) →
        OrientedFinal.IsCyclicShift hG6 T truth6) := by
  intro h
  exact cand6_not_cyclic_shift_of_truth6 (h cand6 spectra_eq_G6_L2)

/-- **Equal spectra do not imply cyclic shift: the exported counterexample.**
A single kernel-checked witness, stated as the failure of the BBT premise at a
concrete instance of the same-length oriented model. -/
theorem equal_spectrum_not_cyclic_shift :
    ∃ (G L : ℕ) (hG : 0 < G) (S D : Fin G → Fin 2),
      (∀ w : Fin L → Fin 2, OrientedRigidity.specCount (L := L) hG D w
          = OrientedRigidity.specCount (L := L) hG S w) ∧
        ¬ OrientedFinal.IsCyclicShift hG D S :=
  ⟨6, 2, hG6, truth6, cand6, spectra_eq_G6_L2, cand6_not_cyclic_shift_of_truth6⟩

/-! ## 4. A finite floor instance: an `I_s`-feasible truth that is a genuine §6.2
candidate

The `AABB`/`ABAB` witness of #88 shows the opposite: with the realized read set
`{1, 3}`, the truth's windows `AA` and `BB` are never observed, so the truth is
not even a member of the §6.2 class (that is what
`AssemblyP1.SameLengthExactMLCounterexample.truth_not_spelled_on_observed`
records). The instance below uses the **full** read set — one read at every one
of the four starts, which is the read set the source's `I_s` is stated over —
and then the truth is both fully `I_s`-feasible and a genuine §6.2 candidate. So
the hypothesis set of §1 is *satisfiable*, and the tie conclusion is verified at
an instance: every genuine same-length §6.2 candidate for the observed read set
ties `AABB` exactly.

`AABB` is the truth; `verts4` is its four length-`2` windows; `sp4` is the
spelling of the truth's own window walk `AA → AB → BB → BA`; `flow4` is the
flow that walk carries; the vertex throughput is `4` because
`strandsOf idRc verts4` enumerates each observed read class once per strand slot
and the walk departs every vertex exactly once.
-/

/-- `G = 4`, for the finite floor instance. -/
private theorem hG4 : 0 < 4 := by norm_num

/-- The truth `AABB` as a length-`4` binary circular word. -/
def truth4 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The strand / molecule-class type at `L = 2`: an oriented length-`2` word. -/
abbrev W4 : Type := Fin 2 → Fin 2

/-- Linearization of a strand. -/
def strandToList4 : W4 → List (Fin 2) := fun w => List.ofFn w

/-- The four length-`2` windows of `AABB`, i.e. the observed read molecules. -/
def w00 : W4 := ![0, 0]
def w01 : W4 := ![0, 1]
def w11 : W4 := ![1, 1]
def w10 : W4 := ![1, 0]

/-- The observed read molecules at the full read set. -/
def verts4 : List W4 := [w00, w01, w11, w10]

/-- The §6.2 spelling of `AABB`: its own window walk. -/
def sp4 : Section62Flow.Spelling (Fin 2) W4 4 where
  strand := ![w00, w01, w11, w10]
  hn := by norm_num

/-- The flow the spelling's cyclic walk carries. -/
def flow4 : Section62Flow.BdFlow (Fin 2) W4 := sp4.flow (fun y => y) 2

/-- The throughput vector: each vertex is departed once, and the edge list
enumerates each observed class once per strand slot. -/
def d4 : W4 → ℕ := fun _ => 4

/-- The §6.2 overlap graph on the four observed reads. -/
def graph4 : List (Section62Flow.BdEdge (Fin 2) W4) :=
  Section62Flow.overlapEdges (Fin 2) W4 strandToList4 (fun y => y) (fun y => y) 2 1
    verts4

/-- **`AABB` at the full read set is fully information-feasible.** Kernel-checked
on the source-faithful `InformationFeasible`, at the single-lift bridging
semantics. -/
theorem truth4_information_feasible :
    InformationFeasible ⟨4, hG4, truth4⟩ 2 Finset.univ := by
  decide

/-- The spelling `sp4` genuinely represents `AABB`. -/
theorem truth4_represents62 :
    SameLength62Maximizer.Represents62 ⟨4, hG4, truth4⟩ sp4 := by
  refine ⟨rfl, ?_⟩
  intro i r hr
  have : i = r := Fin.ext hr
  rw [this]
  fin_cases r <;> decide

/-- **`AABB` is a genuine §6.2 candidate for its own observed read set.**
Kernel-checked against the literal
`AssemblyP1.Section62Flow.SpelledFeasible62` in strict oriented single-strand
mode; the transitive reduction is vacuous here because every step is a maximal
proper overlap of length `readLen - 1`. -/
theorem truth4_spelledFeasible62 :
    Section62Flow.SpelledFeasible62 (Fin 2) W4 strandToList4 (fun y => y)
      (fun y => y) 2 1 verts4 sp4 flow4 (Section62Flow.noTerminals W4) d4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> decide
  · show Section62Flow.StepsInGraph (fun y => y) 2 sp4 graph4
    intro i
    fin_cases i <;> decide
  · show Section62Flow.StepsSurviveReduction (Fin 2) W4 strandToList4 (fun y => y)
        (fun y => y) 2 verts4 sp4 graph4
    intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> rfl
  · show Section62Flow.Feasible62 (Fin 2) W4 (fun y => y) verts4 graph4 flow4
        (Section62Flow.noTerminals W4) d4
    refine ⟨?_, Section62Flow.noTerminals_usage_zero W4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e _; exact Nat.zero_le _
    · intro v hv; fin_cases hv <;> decide
    · intro v hv; fin_cases hv <;> decide
    · intro v hv; fin_cases hv <;> decide

/-- The genuine §6.2 candidate predicate at the finite floor instance. -/
theorem truth4_is62Candidate :
    SameLength62Maximizer.Is62Candidate62 ⟨4, hG4, truth4⟩ verts4 strandToList4
      (fun y => y) (fun y => y) 1 :=
  ⟨4, sp4, flow4, Section62Flow.noTerminals W4, d4, truth4_represents62, rfl,
    truth4_spelledFeasible62⟩

/-- The realization with one read at every start. -/
def rho4 : OrientedSameLengthML.Realization 4 4 := fun i => i

/-- **A cyclic shift is witnessed by a shift below `G`.** The mod-shift bookkeeping
that makes `IsCyclicShift` decidable at a finite instance: a shift by any natural
number is a shift by its residue, and in the other direction a residue shift
gives the natural-number form. -/
theorem isCyclicShift_iff_fin_shift {α : Type} {G : ℕ} (hG : 0 < G)
    {T S : Fin G → α} :
    OrientedFinal.IsCyclicShift hG T S ↔
      ∃ s : Fin G, ∀ i : Fin G,
        T i = S ⟨(i.val + s.val) % G, Nat.mod_lt _ hG⟩ := by
  have hfin : ∀ (W : Fin G → α) (i : ℕ), OrientedRigidity.cyc hG W i
      = W ⟨i % G, Nat.mod_lt _ hG⟩ := fun _ _ => rfl
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨⟨s % G, Nat.mod_lt _ hG⟩, ?_⟩
    intro i
    have hidx : (⟨i.val % G, Nat.mod_lt _ hG⟩ : Fin G) = i :=
      Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have hmod : (i.val + s) % G = (i.val + (s % G)) % G := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    have h1 := hs i.val
    rw [hfin T i.val, hidx, hfin S (i.val + s)] at h1
    have h2 : (⟨(i.val + s) % G, Nat.mod_lt _ hG⟩ : Fin G)
        = ⟨(i.val + (s % G)) % G, Nat.mod_lt _ hG⟩ := Fin.ext hmod
    exact h2 ▸ h1
  · rintro ⟨s, hs⟩
    refine ⟨s.val, ?_⟩
    intro i
    have hideq : ((i % G) + s.val) % G = (i + s.val) % G := by
      have h1 : ((i % G) + s.val) % G = (i % G + s.val % G) % G := by
        rw [Nat.mod_eq_of_lt s.isLt]
      rw [h1, Nat.mod_add_mod, Nat.mod_eq_of_lt s.isLt]
    have h1 := hs ⟨i % G, Nat.mod_lt _ hG⟩
    rw [hfin T i, hfin S (i + s.val)]
    have h2 : (⟨((i % G) + s.val) % G, Nat.mod_lt _ hG⟩ : Fin G)
        = ⟨(i + s.val) % G, Nat.mod_lt _ hG⟩ := Fin.ext hideq
    exact h2 ▸ h1

/-- **At the finite floor instance the residue holds: the fibre is a singleton.**
Every length-`4` binary word with the window support of `AABB` — that is, with
all four length-`2` windows — is a cyclic shift of `truth4`. Kernel-checked via
`isCyclicShift_iff_fin_shift`, over all sixteen words. This is what keeps the
residue honest at the one instance where the hypothesis surface is known to be
satisfiable: the floor instance is not a tie witness, it is a rigidity
instance. -/
theorem truth4_support_rigid :
    ∀ D : Fin 4 → Fin 2,
      OrientedRigidity.support (L := 2) hG4 D
        = OrientedRigidity.support (L := 2) hG4 truth4 →
      OrientedFinal.IsCyclicShift hG4 D truth4 := by
  classical
  simp only [isCyclicShift_iff_fin_shift]
  decide +kernel

/-- **The tie conclusion, verified at the finite floor instance.** Every genuine
same-length §6.2 candidate for the observed read set has exactly the truth's
exact finite likelihood. Kernel-checked for the hypothesis side; the conclusion
is `informationFeasible_62_exact_tie` instantiated. -/
theorem truth4_tie_instance :
    ∀ D : Fin 4 → Fin 2,
      SameLength62Maximizer.Is62Candidate62 ⟨4, hG4, D⟩ verts4 strandToList4
        (fun y => y) (fun y => y) 1 →
      OrientedSameLengthML.exactLik (L := 2) hG4 D
          (OrientedSameLengthML.observedOf hG4 truth4 rho4)
        = OrientedSameLengthML.exactLik (L := 2) hG4 truth4
          (OrientedSameLengthML.observedOf hG4 truth4 rho4) :=
  fun D hD => informationFeasible_62_exact_tie hG4 (by norm_num) (by norm_num)
    truth4 rho4 truth4_information_feasible truth4_is62Candidate D hD

end

end AssemblyP1.SameLength62TieUniqueness
