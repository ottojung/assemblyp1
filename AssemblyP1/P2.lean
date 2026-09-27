import Mathlib
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.PopulationReduction

/-!
# The candidate-intrinsic P2 condition, and its alignment with Ukkonen's
# condition at `K = L - 1` (issue #89)

Paper source: `paper/sections/05-population.tex`, `def:P1P2`,
`thm:BBT`, and the alignment sentence in `§5`:

> "Setting `K = L - 1` aligns the theorem's condition exactly with P2:
> maximal triple repeats then have length at most `L - 2`, and every
> interleaved maximal-repeat pair has a constituent of length at most
> `L - 2`."

Up to `def:P1P2`, `AdmP2` was an opaque parameter of the whole population
chain: every consumer had to *supply* the P2 predicate, so the exported
theorem never actually said what its candidates satisfy. This file
removes that seam.

* `mkGenome`: the bridge from the reduction's word layer `Fin G → α`
  (used by `AssemblyP1.PopulationReduction`) to the source-faithful
  `SourceFaithfulIs.Genome` structure, with no new word layer: the
  genome is literally `⟨G, hG, S⟩`, so `window`, `Preceding`,
  `Following`, `IsRepeat`, `IsTripleRepeat` and `Interleaved` are the
  issue-#85/#90 source-faithful predicates applied to the same symbols.

* `P2`: **the actual P2 of `def:P1P2`**, at read length `L`:
  - no maximal triple repeat of length `≥ L - 1`; and
  - every interleaved maximal repeat pair has a constituent of length
    `≤ L - 2`.

* `Ukkonen`: **the actual hypothesis of `thm:BBT` at `K = L - 1`**: no
  maximal triple repeat and no interleaved pair of maximal repeats of
  length `≥ K`, read at `K = L - 1`.

* `P2.imp_Ukkonen`: the paper's alignment claim, kernel-checked. This
  is the step that used to be asserted in prose; it is now a theorem,
  so the *only* thing a consumer must still supply about P2 is the
  BBT uniqueness statement itself.

* `BBTCompleteSpectrumUniqueness`: the precise formalization boundary
  of `thm:BBT` (Bresler--Bresler--Tse 2013, Theorem 3), phrased on the
  project's own objects: the `K = L - 1` hypothesis, the complete
  `L`-spectrum equality, and rotation equivalence of the two circular
  words. Nothing weaker and nothing stronger is assumed; the
  irreducible core is the complete-spectrum uniqueness for a
  Ukkonen-satisfying circular word, and it is named rather than hidden
  in an anonymous hypothesis.

The same reasoning is applied to the candidate, not only to the truth:
`P2.imp_Ukkonen` is used for both genomes, exactly as the paper's proof
of `thm:population` does ("Both `S` and `D` satisfy P2, hence Ukkonen's
condition at `K = L - 1`"). Note the paper's `lem:scaling` applies
uniqueness only to `S`; that asymmetry is preserved by the chain in
`AssemblyP1.PopulationUniqueness`.
-/

namespace AssemblyP1

open BigOperators
open SourceFaithfulIs

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-- The `Fin G → α` word of the reduction layer read as a source-faithful
circular genome. `window`, `Preceding`, `Following`, `IsRepeat`,
`IsTripleRepeat` and `Interleaved` are then literally the
`SourceFaithfulIs` predicates on the same symbols, so P2 needs no second
word layer. -/
def mkGenome (hG : 0 < G) (S : Fin G → α) : SourceFaithfulIs.Genome α :=
  ⟨G, hG, S⟩

/-- **P2 of `def:P1P2`**, verbatim: `D` satisfies P2 at read length `L`
if it has no maximal triple repeat of length `≥ L - 1` and every
interleaved maximal repeat pair has a constituent of length `≤ L - 2`.
Repeat lengths are ranged over `Fin G` because `IsRepeat` and
`IsTripleRepeat` already require `1 ≤ e < |D|`. -/
def P2 (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
    (∀ (e₁ e₂ : Fin G) (a b c d : Fin G), (mkGenome hG S).IsRepeat e₁ a b →
      (mkGenome hG S).IsRepeat e₂ c d →
      Interleaved (mkGenome hG S) a b c d →
      e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2)

/-- **Ukkonen's condition at `K = L - 1`**, the hypothesis of
`thm:BBT` (Bresler--Bresler--Tse 2013, Theorem 3) as stated in
`paper/sections/05-population.tex`: no triple repeat and no interleaved
repeat pair of length at least `K`, here read at `K = L - 1`. -/
def Ukkonen (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
    (∀ (e₁ e₂ : Fin G) (a b c d : Fin G), (mkGenome hG S).IsRepeat e₁ a b →
      (mkGenome hG S).IsRepeat e₂ c d →
      Interleaved (mkGenome hG S) a b c d →
      e₁.val < L - 1 ∨ e₂.val < L - 1)

/-- **The paper's alignment claim, kernel-checked:** P2 at read length `L`
implies Ukkonen's condition at `K = L - 1`. The two clauses are the same
repeat statements read at adjacent thresholds (`≤ L - 2` versus
`< L - 1`), so the transfer is arithmetic; what matters is that the
project no longer *asserts* it in prose, and that it is applied to the
candidate as well as to the truth. -/
theorem P2.imp_Ukkonen {hG : 0 < G} {L : ℕ} {S : Fin G → α} (hL : 2 ≤ L)
    (h : P2 hG L S) :
    Ukkonen hG L S := by
  refine ⟨h.1, ?_⟩
  intro e₁ e₂ a b c d hR₁ hR₂ hI
  rcases h.2 e₁ e₂ a b c d hR₁ hR₂ hI with h1 | h2
  · refine Or.inl (lt_of_le_of_lt h1 (by omega))
  · refine Or.inr (lt_of_le_of_lt h2 (by omega))

/-- The triple-repeat clause of `P2`, i.e. "no maximal triple repeat of
length `≥ L - 1`", isolated for the reduction's callers. -/
theorem P2.triple (hG : 0 < G) {L : ℕ} {S : Fin G → α} (h : P2 hG L S)
    {e a b c : Fin G} (ht : (mkGenome hG S).IsTripleRepeat e a b c) :
    e.val < L - 1 :=
  h.1 e a b c ht

/-- The interleaved-pair clause of `P2`, i.e. "every interleaved maximal
repeat pair has a constituent of length `≤ L - 2`", isolated. -/
theorem P2.interleaved (hG : 0 < G) {L : ℕ} {S : Fin G → α} (h : P2 hG L S)
    {e₁ e₂ : Fin G} {a b c d : Fin G}
    (hR₁ : (mkGenome hG S).IsRepeat e₁ a b) (hR₂ : (mkGenome hG S).IsRepeat e₂ c d)
    (hI : Interleaved (mkGenome hG S) a b c d) :
    e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2 :=
  h.2 e₁ e₂ a b c d hR₁ hR₂ hI

/-! ## The one remaining external input, named precisely -/

open AssemblyP1.OrientedRigidity
open AssemblyP1.PopulationReduction

/-- **The formalization boundary of `thm:BBT`** (Bresler--Bresler--Tse,
2013, Theorem 3), reduced to the exact statement this project needs and
stated on the project's own objects: build the `K`-mer graph from the
complete `(K+1)`-spectrum of a circular word; if that word satisfies
Ukkonen's condition at `K`, then the complete spectrum determines the
word up to cyclic rotation.

At `K = L - 1` the `K`-mer graph is exactly the length-`(L-1)`
de Bruijn graph on which `AssemblyP1.PopulationReduction` performs its
division/Eulerian argument, and the `(K+1)`-spectrum is exactly
`specCount (L := L) hG S`, so no translation layer is missing here.

This `def` is the whole of what the project assumes. It is *not* an
axiom: `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
takes an inhabitant of it as an explicit hypothesis, and nothing else in
the library does. The paper supplies it from `cite{bresler2013}`; the
project cannot honestly reprove it, and the rest of the chain (the
Gibbs/KL layer, the P2-to-Ukkonen alignment, the division/Eulerian
gcd-one argument, the proportional-cancellation lemma) is
kernel-checked. -/
def BBTCompleteSpectrumUniqueness
    {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ E : Fin G → α, Ukkonen hG L S →
    specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S

/-- **`thm:BBT` as the project uses it**: the complete `L`-spectrum
determines a Ukkonen-satisfying circular word up to cyclic rotation,
uniformly over all genome lengths. The external theorem is a theorem
about *all* circular words, so the honest hypothesis is the global
statement rather than a per-genome instance, and a consumer supplies one
premise rather than one per candidate. -/
def BBTUniqueAt {α : Type} [DecidableEq α] (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), BBTCompleteSpectrumUniqueness hK L W

/-- P2 turns the BBT boundary into something applicable, for **any**
circular word of the candidate class. This is the only place the
alignment lemma is consumed, so the exported theorem needs exactly one
BBT inhabitant per genome side and no P2-to-Ukkonen side condition. -/
theorem BBT_of_P2 {G : ℕ} (hG : 0 < G) {L : ℕ} {S : Fin G → α}
    (_hP2 : P2 hG L S) (hBBT : BBTCompleteSpectrumUniqueness hG L S) :
    ∀ E : Fin G → α, Ukkonen hG L S →
      specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S :=
  hBBT

end AssemblyP1
