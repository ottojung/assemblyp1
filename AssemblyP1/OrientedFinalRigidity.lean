import AssemblyP1.RepeatAdapter

/-!
# Final oriented same-length spectrum-rigidity theorem (issue #74)

Thin integration/wiring packet over the already-merged chain:

* abstract circulation rigidity (#68): `OrientedRigidity.unique_positive_circulation`;
* circular-spectrum adapter (#69): `OrientedRigidity.rigidity_same_spectrum`
  (balance and strong connectivity proved from the circular word);
* primitive/periodic repeat-theory adapter (#71/#76):
  `RepeatAdapter.primitive_rigidity_same_spectrum` and
  `RepeatAdapter.periodic_rigidity_same_spectrum`.

## Theorem surface (trust boundary)

* `oriented_same_length_spectrum_rigidity`: Lean-checked conditional on the
  explicit source-boundary premise `hno : ¬ HasLongTripleRepeat` (no Bresler
  triple repeat of length `≥ L - 1`). The primitive/periodic split is
  discharged internally by the kernel-checked dichotomy
  `RepeatAdapter.primitive_or_minimal_period`; no case-split hypothesis is
  exposed and no global multiplicity-`≤ 2` hypothesis is imposed.
* `I_s → no long triple repeat` (note §3, Fact D): source-supported boundary,
  kept outside Lean. This file does not define `I_s`, and does not claim the
  implication is kernel-checked.
* Complete-spectrum uniqueness up to rotation (BBT): explicit external premise
  consumed only by `rotation_uniqueness_of_bbt`. BBT itself is not formalized here.
* The project theorem proves **spectrum rigidity**. Equal spectrum gives a tie
  only for objectives factoring through the spectrum (plus fixed observed counts),
  via `spectrum_objective_tie`; this is not uniqueness of the ML maximizer.
-/

namespace AssemblyP1.OrientedFinal

open Finset
open BigOperators

/-- Cyclic-shift equivalence of two circular words (rotation, no reflection). -/
def IsCyclicShift {α : Type} {G : ℕ} (hG : 0 < G) (T S : Fin G → α) : Prop :=
  ∃ s : ℕ, ∀ i : ℕ,
    OrientedRigidity.cyc hG T i = OrientedRigidity.cyc hG S (i + s)

/-- **Thin final theorem (issue #74).** Under no long Bresler triple repeat,
every positive balanced circulation
of total mass `G` on the truth's oriented length-`L` window support is the
truth's ordinary length-`L` spectrum. The primitive/periodic split is closed
internally by `RepeatAdapter.primitive_or_minimal_period`. -/
theorem oriented_same_length_spectrum_rigidity {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ OrientedRigidity.support hG S ↔ 0 < B w)
    (hBbal : OrientedRigidity.Balanced OrientedRigidity.winPrefix
      OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
      (OrientedRigidity.support hG S) B)
    (hBtot : ∑ w ∈ OrientedRigidity.support hG S, B w = G) :
    ∀ w, B w = OrientedRigidity.specCount hG S w := by
  rcases RepeatAdapter.primitive_or_minimal_period hG S with hprim | ⟨p, hmin⟩
  · exact RepeatAdapter.primitive_rigidity_same_spectrum hG S hL hLG
      hprim hno B hBsup hBbal hBtot
  · exact RepeatAdapter.periodic_rigidity_same_spectrum hG S p hmin hL
      hno B hBsup hBbal hBtot

/-- **Spectrum-tie corollary.** Equal spectra tie for every objective that
factors through the spectrum (observed counts held fixed). This is equality of
objective values, not uniqueness of the maximizer. -/
theorem spectrum_objective_tie {α M : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ OrientedRigidity.support hG S ↔ 0 < B w)
    (hBbal : OrientedRigidity.Balanced OrientedRigidity.winPrefix
      OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
      (OrientedRigidity.support hG S) B)
    (hBtot : ∑ w ∈ OrientedRigidity.support hG S, B w = G)
    (F : ((Fin L → α) → ℕ) → M) :
    F B = F (OrientedRigidity.specCount hG S) := by
  have heq := oriented_same_length_spectrum_rigidity hG S hL hLG hno
    B hBsup hBbal hBtot
  exact congrArg F (funext heq)

/-- **Rotation uniqueness conditional on explicit BBT premise.** Given spectrum
rigidity plus an external complete-spectrum uniqueness input (`hBBT`: equal
spectra imply cyclic-shift equivalence — not proved here), a realized
competitor word is a rotation of the truth. -/
theorem rotation_uniqueness_of_bbt {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    (B : (Fin L → α) → ℕ)
    (hBsup : ∀ w, w ∈ OrientedRigidity.support hG S ↔ 0 < B w)
    (hBbal : OrientedRigidity.Balanced OrientedRigidity.winPrefix
      OrientedRigidity.winSuffix (OrientedRigidity.genomeNodes hG S)
      (OrientedRigidity.support hG S) B)
    (hBtot : ∑ w ∈ OrientedRigidity.support hG S, B w = G)
    (T : Fin G → α)
    (hreal : ∀ w : Fin L → α, B w = OrientedRigidity.specCount hG T w)
    (hBBT : ∀ T : Fin G → α,
      (∀ w : Fin L → α, OrientedRigidity.specCount hG T w =
        OrientedRigidity.specCount hG S w) → IsCyclicShift hG T S) :
    IsCyclicShift hG T S := by
  have heq := oriented_same_length_spectrum_rigidity hG S hL hLG hno
    B hBsup hBbal hBtot
  apply hBBT
  intro w
  rw [← hreal w]
  exact heq w

end AssemblyP1.OrientedFinal
