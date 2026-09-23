import Mathlib
import AssemblyP1.PopulationReduction

/-!
# Thin final population uniqueness theorem (issue #73)

Paper source: `paper/sections/05-population.tex`, `thm:population` and its
proof chain (`lem:gibbs` → `lem:scaling`/corollary → `thm:BBT`).

This file is deliberately thin: it adds **no** graph, circulation, spelling,
or repeat infrastructure. Everything project-side is reused from
`AssemblyP1.PopulationReduction` (whose division–Eulerian gcd-one core was
Lean-checked in issue #70):

* `population_uniqueness_primitive_P2_words`: normalized equality forces
  equal lengths and equal ordinary spectra for primitive P2 genomes;
* `RotEquiv`: rotation equivalence of same-length circular words;
* `IsPrimitive`, `NormalizedEqual`: candidate hypothesis and
  normalized-spectrum equality.

Trust boundary (each external input is an explicit hypothesis, never an
axiom):

* **Gibbs/KL tie characterization** (Cover–Thomas): a population tie
  `ℓpop_S(D) = ℓpop_S(S)` holds iff the normalized spectra agree.
  Formalizing that real analysis here would dominate the file, so the tie
  itself is an opaque explicit parameter `PopTie`, and the Gibbs equality
  direction is the explicit premise `hGibbs`. The maximizer half of Gibbs
  (the truth is always a population maximizer) is likewise the explicit
  premise `hMaximizer`.
* **Bresler–Bresler–Tse (2013), Theorem 3** complete-spectrum uniqueness at
  `K = L - 1`: the explicit premises `hBBTS`/`hBBTD`. The P2 admissibility
  predicate `AdmP2` is an opaque explicit parameter: only the BBT
  uniqueness implication consumes it.

What is kernel-checked here:

* `population_tie_implies_rotation`: a population tie forces equal lengths
  and rotation equivalence, by composing the Gibbs bridge (`hGibbs`) with
  the reused #70 reduction and substituting the length identity into BBT
  uniqueness. Candidate hypotheses (primitivity and P2 for **both**
  genomes), tie semantics (`PopTie` vs `NormalizedEqual` kept distinct),
  and rotation equivalence (`RotEquiv`) are all explicit.
* `population_unique_ML_up_to_rotation`: the `UniqueSchema`-shaped
  packaging (maximizer ∧ every tie is rotation-equivalent to the truth),
  mirroring `AssemblyP1.Model.IsUniqueMaximumLikelihoodUpToEquiv` for the
  oriented primitive P2 candidate class.

Scope: the oriented spectrum model only. Nothing here transfers to
reverse-complement-collapsed molecule classes (see the paper's scope
note). This does not settle the finite 2016 question.
-/

namespace AssemblyP1.PopulationUniqueness

open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] [Fintype α]
variable {L G H : ℕ}
variable (hG : 0 < G) (hH : 0 < H) (S : Fin G → α) (D : Fin H → α)
variable (AdmP2 : ∀ {K : ℕ}, (Fin K → α) → Prop)
/-
Population tie of a candidate with the fixed truth: `PopTie E` means
`ℓpop_S(E) = ℓpop_S(S)`. Kept opaque: the Gibbs/KL analysis characterizing
ties is external (Cover–Thomas); the `hGibbs` premise below records exactly
the equality direction this file consumes.
-/
variable (PopTie : ∀ {K : ℕ}, (Fin K → α) → Prop)
/-
Truth-is-maximizer statement: `S` is a population maximizer over the
candidate class. Kept opaque: it is the maximizer half of external Gibbs.
-/
variable (PopMaximizer : Prop)

/-- A population tie forces equal lengths and rotation equivalence.
Composes the explicit Gibbs bridge with the reused #70 reduction
(`population_uniqueness_primitive_P2_words`) and substitutes the resulting
length identity into BBT uniqueness. Uniqueness is applied only to `S`
(via `hBBTS`); `hBBTD` is consumed inside the reused reduction. -/
theorem population_tie_implies_rotation
    (hL : 1 < L)
    (hPrimS : IsPrimitive S) (hPrimD : IsPrimitive D)
    (hP2S : AdmP2 S) (hP2D : AdmP2 D)
    (hTie : PopTie D)
    (hGibbs : PopTie D →
      NormalizedEqual (W := Fin L → α)
        (specCount (L := L) hG S) (specCount (L := L) hH D) G H)
    (hBBTS : ∀ E : Fin G → α, AdmP2 S →
      specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S)
    (hBBTD : ∀ E : Fin H → α, AdmP2 D →
      specCount (L := L) hH D = specCount (L := L) hH E → RotEquiv hH E D) :
    ∃ hGH : G = H, RotEquiv hG (hGH ▸ D) S := by
  have hNorm := hGibbs hTie
  obtain ⟨hGH, hSpec⟩ :=
    population_uniqueness_primitive_P2_words AdmP2 hG hH S D hL
      hPrimS hPrimD hP2S hP2D hNorm hBBTS hBBTD
  subst hGH
  refine ⟨rfl, ?_⟩
  show RotEquiv hG D S
  exact hBBTS _ hP2S hSpec

/-- `UniqueSchema`-shaped packaging for the oriented primitive P2 class:
the truth is a population maximizer, and every population tie is
rotation-equivalent to the truth (with the length identity carried by the
existential). Mirrors `AssemblyModel.IsUniqueMaximumLikelihoodUpToEquiv`
with `RotEquiv` as the genome equivalence. -/
theorem population_unique_ML_up_to_rotation
    (hL : 1 < L)
    (hPrimS : IsPrimitive S) (hPrimD : IsPrimitive D)
    (hP2S : AdmP2 S) (hP2D : AdmP2 D)
    (hTie : PopTie D)
    (hMaximizer : PopMaximizer)
    (hGibbs : PopTie D →
      NormalizedEqual (W := Fin L → α)
        (specCount (L := L) hG S) (specCount (L := L) hH D) G H)
    (hBBTS : ∀ E : Fin G → α, AdmP2 S →
      specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S)
    (hBBTD : ∀ E : Fin H → α, AdmP2 D →
      specCount (L := L) hH D = specCount (L := L) hH E → RotEquiv hH E D) :
    PopMaximizer ∧ ∃ hGH : G = H, RotEquiv hG (hGH ▸ D) S :=
  ⟨hMaximizer,
    population_tie_implies_rotation hG hH S D AdmP2 PopTie hL
      hPrimS hPrimD hP2S hP2D hTie hGibbs hBBTS hBBTD⟩

end AssemblyP1.PopulationUniqueness
