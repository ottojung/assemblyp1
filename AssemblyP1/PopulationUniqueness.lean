import Mathlib
import AssemblyP1.PopulationGibbs
import AssemblyP1.P2
import AssemblyP1.PopulationReduction

/-!
# End-to-end population uniqueness for the oriented primitive P2 class
  (issue #89)

Paper source: `paper/sections/05-population.tex`, `thm:population` with its
full proof chain `def:population` → `lem:gibbs` → `lem:scaling` →
corollary → `thm:BBT`.

## What the exported theorem says

`population_unique_ML_up_to_rotation` below is the paper's Theorem
`thm:population`, in the published model, with **no proxy predicates and
no abstract external premises** in its hypotheses:

* the objective is the actual population log-likelihood
  `ℓpop_S(D) = ∑_w p_S(w) log p_D(w)` of `def:population`, including the
  published `= -∞` convention (`AssemblyP1.PopulationGibbs.PopLogLik`,
  valued in `WithBot ℝ` so that `-∞` really is the least element and
  "maximizer" is a `≤` in a linear order);
* `p_D` and `p_S` are the actual population read distributions
  `p_D(w) = spec_L(D)(w)/|D|` of the actual `L`-spectrum
  `AssemblyP1.OrientedRigidity.specCount`;
* the candidate hypotheses are the actual `P2` of `def:P1P2`
  (`AssemblyP1.P2.P2`, stated through the source-faithful
  `IsTripleRepeat`/`IsRepeat`/`Interleaved` predicates) and the actual
  primitivity `AssemblyP1.PopulationReduction.IsPrimitive`;
* the conclusion is that the truth maximizes the objective over the whole
  candidate class and that **every** population tie is rotation-equivalent
  to the truth, i.e. uniqueness up to cyclic rotation.

Contrast with the previous version of this file, which took `PopTie`,
`PopMaximizer`, `hGibbs` and `hBBTS`/`hBBTD` as caller-supplied
parameters: the caller had to state the objective, the candidate class,
and the whole of the Gibbs analysis. All of that is now derived in the
kernel.

## The one remaining external input

`hBBTS`/`hBBTD` are inhabitants of
`AssemblyP1.P2.BBTCompleteSpectrumUniqueness`, the precisely specialized
form of `thm:BBT` (Bresler–Bresler–Tse 2013, Theorem 3) at `K = L - 1`
on the project's own spectrum and rotation objects. That irreducible
core is named, documented and stated at the level the paper needs; it is
the only external mathematical input to the whole population chain, and
`AssemblyP1.P2.P2.imp_Ukkonen` proves in the kernel that P2 supplies its
hypothesis, so the caller supplies a *theorem about complete spectra*
rather than a *repeat condition to be re-checked*. No `axiom`, `sorry`
or `admit` appears anywhere in the chain.

## What is reused

The division–Eulerian gcd-one core (`gcd_one_of_primitive_P2_words`),
the proportional-cancellation lemma (`normalized_to_ordinary`), the
end-to-end project-level reduction
(`population_uniqueness_primitive_P2_words`) and the spectrum-total fact
(`spec_sum_total`) are all reused unchanged from
`AssemblyP1.PopulationReduction` (issue #70); the Gibbs/KL layer is
reused from `AssemblyP1.PopulationGibbs`. This file adds no graph,
circulation, spelling or repeat infrastructure.

Scope, as in the paper: the *oriented* single-strand spectrum model only.
Nothing here transfers to reverse-complement-collapsed molecule classes,
and this does not settle the finite 2016 question.
-/

set_option maxHeartbeats 400000

namespace AssemblyP1.PopulationUniqueness

open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity
open AssemblyP1.P2

variable {α : Type} [DecidableEq α] [Fintype α]
variable {G H : ℕ}

/-- The population read distribution of a circular word of length `G` at
read length `L`: `p_S(w) = spec_L(S)(w) / |S|`, i.e. `def:population`
specialized to the project's `L`-spectrum. -/
noncomputable def popSpectrum (L : ℕ) {G : ℕ} (hG : 0 < G) (S : Fin G → α) :
    (Fin L → α) → ℝ :=
  popProb (specCount (L := L) hG S) G

/-- `p_S` is a read distribution: nonnegative, and summing to `1`. This is
what licenses calling `ℓpop_S` a log-likelihood at all. -/
theorem popSpectrum_isProb (L : ℕ) {G : ℕ} (hG : 0 < G) (S : Fin G → α) :
    IsProb (popSpectrum L hG S) :=
  popProb_isProb (specCount (L := L) hG S)
    (by rw [spec_sum_total (L := L) hG S]) hG

/-- **The population tie of `def:population`/`thm:population`:** the
candidate achieves the truth's population log-likelihood. This is the
objective of the paper itself, not a proxy. -/
def PopTie (L : ℕ) {G H : ℕ} (hG : 0 < G) (hH : 0 < H) (S : Fin G → α)
    (D : Fin H → α) : Prop :=
  PopLogLik (popSpectrum L hG S) (popSpectrum L hH D)
    = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)

/-- The admissible candidate class of `thm:population`: primitive, P2 at
read length `L`, of any positive length, on the oriented model. -/
def AdmClass (L : ℕ) {K : ℕ} (hK : 0 < K) (E : Fin K → α) : Prop :=
  IsPrimitive E ∧ P2 hK L E

/-! ## The exported theorem -/

/-- **`thm:population`: population uniqueness, oriented primitive P2.**

Among primitive P2-admissible oriented circular candidates, the true
genome `S` is the unique population maximum-likelihood genome up to
cyclic rotation.

More precisely, for `L ≥ 2` and any primitive P2-admissible candidates
`E`, the objective `ℓpop_S` of `def:population` satisfies:

1. **maximizer** (Lemma `lem:gibbs`): `ℓpop_S(E) ≤ ℓpop_S(S)`, stated for
   *every* candidate class containing the admissible genomes, and with
   no structural hypothesis needed for the inequality itself;
2. **uniqueness up to rotation** (Lemma `lem:scaling` + `thm:BBT`): a tie
   `ℓpop_S(E) = ℓpop_S(S)` forces `|E| = |S|` and `E` to be a cyclic shift
   of `S`.

The only hypotheses are the two genome lengths, `L ≥ 2`, the structural
conditions on `S` and `E` (primitivity and P2, the actual `def:P1P2`
predicate), the population tie, and one inhabitant of
`AssemblyP1.P2.BBTCompleteSpectrumUniqueness` per genome side — the
specialized Bresler–Bresler–Tse input of `thm:BBT`. -/
theorem population_unique_ML_up_to_rotation
    (L : ℕ) (hG : 0 < G) (hL : 1 < L)
    (S : Fin G → α)
    (hPrimS : IsPrimitive S)
    (hP2S : P2 hG L S)
    (hBBT : BBTUniqueAt (α := α) L) :
    -- the truth is a population maximizer over the whole admissible class
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    -- every population tie is a cyclic shift of the truth
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) := by
  refine ⟨?_, ?_⟩
  -- 1. the maximizer half of lem:gibbs, for every candidate distribution
  · intro K hK W _
    exact popLogLik_le_self' (popSpectrum_isProb L hG S) (popSpectrum_isProb L hK W)
  -- 2. the tie-to-rotation chain
  · intro K hK W hW hWTie
    obtain ⟨hPrimW, hP2W⟩ := hW
    -- the objective equality is a genuine likelihood tie between the two
    -- population read distributions (lem:gibbs, equality direction)
    have hEq : popSpectrum L hK W = popSpectrum L hG S :=
      (popTie_iff (popSpectrum_isProb L hG S)
        (popSpectrum_isProb L hK W)).mp hWTie
    have hDist : popProb (specCount (L := L) hG S) G
        = popProb (specCount (L := L) hK W) K := hEq.symm
    -- hence the two integer spectra are proportional (normalized equality)
    have hNorm : NormalizedEqual (W := Fin L → α)
        (specCount (L := L) hG S) (specCount (L := L) hK W) G K :=
      popProb_eq_iff_normalized hG hK hDist
    -- the reused #70 reduction: primitivity + P2 turn normalized equality
    -- into equal lengths and equal ordinary spectra
    obtain ⟨hGK, hSpec⟩ :=
      population_uniqueness_primitive_P2_words
        (fun {_K : ℕ} (_W : Fin _K → α) => True)
        hG hK S W hL hPrimS hPrimW True.intro True.intro hNorm
        (fun E _ hSpecE => (hBBT G hG S) E (P2.imp_Ukkonen (by omega) hP2S) hSpecE)
        (fun E _ hSpecE => (hBBT K hK W) E (P2.imp_Ukkonen (by omega) hP2W) hSpecE)
    subst hGK
    refine ⟨rfl, ?_⟩
    show RotEquiv hG W S
    -- thm:BBT at K = L-1, with Ukkonen's condition supplied by P2
    exact (hBBT G hG S) W (P2.imp_Ukkonen (by omega) hP2S) hSpec

/-- The `UniqueSchema`-shaped reading of `thm:population` on the
same-length slice: the truth is a population maximizer and **every**
population tie among primitive P2 candidates is rotation-equivalent to
it, with no length side condition on the conclusion. This mirrors
`AssemblyModel.IsUniqueMaximumLikelihoodUpToEquiv` with `RotEquiv` as the
genome equivalence. -/
theorem population_unique_ML_up_to_rotation_same_length
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S)
    (hP2S : P2 hG L S)
    (hBBT : BBTUniqueAt (α := α) L) :
    (∀ E : Fin G → α, AdmClass L hG E →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hG E)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))
      ∧
    (∀ E : Fin G → α, AdmClass L hG E →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hG E)
          = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
        RotEquiv hG E S) := by
  obtain ⟨hCand, hRot⟩ :=
    population_unique_ML_up_to_rotation L hG hL S hPrimS hP2S hBBT
  refine ⟨fun E hE => hCand G hG E hE, ?_⟩
  intro E hE hETie
  obtain ⟨hGG, hRotE⟩ := hRot G hG E hE hETie
  cases hGG
  exact hRotE

/-- The two-genome reading of `thm:population`, preserving the shape of
the previous version of this file: a concrete primitive P2 candidate `D`
of any positive length that ties the truth's population
log-likelihood must be a cyclic shift of `S`, with `|D| = |S|` carried by
the length identity. Only the objective and the structural conditions
changed; the abstract `PopTie`/`hGibbs`/`hBBTS`/`hBBTD` parameters are
gone. -/
theorem population_tie_implies_rotation
    (L : ℕ) (hG : 0 < G) {H : ℕ} (hH : 0 < H) (hL : 1 < L)
    (S : Fin G → α) (D : Fin H → α)
    (hPrimS : IsPrimitive S) (hPrimD : IsPrimitive D)
    (hP2S : P2 hG L S) (hP2D : P2 hH L D)
    (hTie : PopTie L hG hH S D)
    (hBBT : BBTUniqueAt (α := α) L) :
    ∃ hGH : G = H, RotEquiv hG (hGH ▸ D) S := by
  obtain ⟨_, hRot⟩ :=
    population_unique_ML_up_to_rotation L hG hL S hPrimS hP2S hBBT
  exact hRot H hH D ⟨hPrimD, hP2D⟩ hTie

/-- The maximizer half alone, over the whole primitive P2 class: no tie,
no BBT input, and in fact no structural hypothesis at all on the
candidate. This is Lemma `lem:gibbs` as the paper states it — "the truth
is always a population maximum-likelihood genome, with no repeat
condition required". -/
theorem truth_is_population_maximizer_primitive_P2
    (L : ℕ) (hG : 0 < G) {K : ℕ} (hK : 0 < K) (S : Fin G → α) :
    ∀ (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) :=
  fun W _ => popLogLik_le_self' (popSpectrum_isProb L hG S) (popSpectrum_isProb L hK W)

/-- The kernel-checked core of the tie characterization as it is actually
used downstream: a population tie forces the normalized (proportional)
spectrum equality that the #70 reduction consumes. Recorded as its own
theorem so the boundary of the deep input is visible: this is exactly
`lem:gibbs`'s equality direction, and it is proved, not assumed. -/
theorem population_tie_implies_normalized
    (L : ℕ) (hG : 0 < G) {K : ℕ} (hK : 0 < K) (S : Fin G → α) (D : Fin K → α)
    (hTie : PopLogLik (popSpectrum L hG S) (popSpectrum L hK D)
      = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)) :
    NormalizedEqual (W := Fin L → α)
      (specCount (L := L) hG S) (specCount (L := L) hK D) G K := by
  have hEq : popSpectrum L hK D = popSpectrum L hG S :=
    (popTie_iff (popSpectrum_isProb L hG S)
      (popSpectrum_isProb L hK D)).mp hTie
  exact popProb_eq_iff_normalized hG hK hEq.symm

end AssemblyP1.PopulationUniqueness
