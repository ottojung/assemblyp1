import AssemblyP1.PopulationUniqueness
import AssemblyP1.Issue94EulerianRealize
import AssemblyP1.P2RepeatResidual

/-!
# Board 94 / issue #89, front `94iface`: **the interface a route has to hit.**

This module is the integration endpoint for board 94. It says, exactly and
kernel-checkably, *what theorem closes issue #89*, in the weakest form in which
the endpoint actually consumes it. It does **not** prove that theorem; it
proves the reduction from it, so that any route (the ladder route, a
Cohn--Lempel block-deletion argument, a direct `Ukkonen` argument, anything)
has a single named target to hit and a single line to apply afterwards.

## 1. What the endpoint consumes, read off the proof

`AssemblyP1/PopulationUniqueness.lean:173-219` proves
`population_unique_ML_up_to_rotation` from one hypothesis,

```
  hPevzner : AssemblyP1.BBTEulerian.EulerianCycleObstruction (α := α) L
```

and then *derives* everything else. Following the proof, `hPevzner` is used
through `bbtUniqueAt_of_obstruction` at exactly **two** sites
(`PopulationUniqueness.lean:212` and `:214`), and at both sites:

* the word it is applied to is the truth `S` or the competitor `W`, which
  satisfy `P2` (hence `Ukkonen`) --- and, at both sites, `IsPrimitive`;
* it is used as `BBTCompleteSpectrumUniqueness hK L W`, whose competitor `E`
  ranges over **all** `Fin K → α`. `Ukkonen` is demanded of the *truth only*
  (`BBTCompleteSpectrumUniqueness` is `∀ E, Ukkonen … → specEq → RotEquiv`);
* no genome-length side condition is used: the quantifier over `K` is
  unrestricted.

So `BBTUniqueAt L` --- which ranges over **every** `Ukkonen` word at every
length --- is used only on `P2` **and** primitive words. That is the whole
slack, and `BBTP2Prim` below is exactly it.

## 2. The interface theorem

```lean
def BBTP2Prim (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), P2 hK L W → IsPrimitive W →
    ∀ E : Fin K → α,
      specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W
```

i.e. **complete-`L`-spectrum uniqueness, restricted to `P2`-and-primitive
truths, uniformly over all genome lengths.** It is `BBTCompleteSpectrumUniqueness`
at those truths, spelled out; the competitor `E` is unconstrained.

`BBTP2Prim L` is a `Prop` and **not** an inhabitant, here or anywhere in the
tree.

## 3. The reduction, kernel-checked

`population_unique_ML_of_P2Prim` is `thm:population` verbatim --- the exact
conclusion of `PopulationUniqueness.population_unique_ML_up_to_rotation` --- with
`BBTP2Prim L` in place of `hPevzner : EulerianCycleObstruction L`. The proof
is `PopulationUniqueness`'s proof with `BBTUniqueAt` supplied at the two sites
by `bbtCompleteSpec_of_P2Prim`. Likewise
`population_unique_ML_same_length_of_P2Prim` and
`population_tie_implies_rotation_of_P2Prim`.

Three corollaries pin the interface down from the other side:

* `bbTP2Prim_of_bbtUniqueAt` and `bbTP2Prim_of_obstruction`: the interface is
  implied by what is already postulated, so this module **weakens** the
  endpoint's hypothesis and never strengthens its conclusion. The exported
  theorems of `PopulationUniqueness` are untouched.
* `population_unique_ML_of_BBTUniqueAt`: the endpoint follows from `BBTUniqueAt L`
  in its source form, i.e. from `thm:BBT` as the project states it --- through
  the realization bridge of `Issue94EulerianRealize`
  (`obstruction_iff_bbtUniqueAt`), with no Eulerian-cycle object named. So
  after that bridge landed, the endpoint has a one-line path from the published
  theorem; **the endpoint is not blocked on anything of this project's own.**
* `bbtCompleteSpec_of_P2Prim'`: the pointwise form, for a single `P2`
  primitive word, with `P2.imp_Ukkonen` supplying `Ukkonen` of the truth only.

## 4. Why this is the right plug-in point for another route

`BBTP2Prim` is deliberately stated on the *project's own* objects
(`P2`, `IsPrimitive`, `specCount`, `RotEquiv`, `BBTCompleteSpectrumUniqueness`),
with no `EulerianCycle`, no `Matching`, no `pullback`, no `AltF` and no chord
vocabulary. A route that proves it needs none of that machinery, and the
equivalent Eulerian-cycle form is already known to be equivalent
(`BBTEulerian.UniqueEulerianCycle`, and at `2 ≤ L` also
`Issue94Realize.obstruction_iff_bbtUniqueAt`), so a route proved in the
Eulerian-cycle language can be converted before being applied here.

`docs/issue-94-long-window-interface-94.md` records the residual decomposition
(`K ≤ L - 1` vs `L ≤ K`) and the ladder route's placement; that part of the
picture needs `AssemblyP1.Issue94KShort`, whose import chain reaches
`AssemblyP1.Issue94OrbitSearch`. That module is excluded here **deliberately**:
this file is the light interface and must build without the heavy chain. The
decomposition theorems themselves live in
`AssemblyP1/Issue94LongWindowSplit.lean`, which imports this one.

## 5. What this does not do

* No inhabitant of `BBTP2Prim L`, at any `L`. Issue #89 is not settled. The
  remaining mathematical content is `thm:BBT` restricted to the `P2`-primitive
  class, and `BBTP2Prim L` is its exact statement.
* No definition is changed to make anything provable. `EulerianCycleObstruction`,
  `BBTUniqueAt`, `BBTCompleteSpectrumUniqueness`, `P2`, `Ukkonen`, `IsPrimitive`,
  `RotEquiv`, `specCount`, `AdmClass`, `popSpectrum`, `PopLogLik`, `PopTie` are
  used exactly as `P2.lean`, `BBTEulerian.lean`, `OrientedRigidity.lean` and
  `PopulationUniqueness.lean` state them.
* No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter
  suppression. §6 is the `#print axioms` audit and reports only `propext`,
  `Classical.choice`, `Quot.sound`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace AssemblyP1.Issue94Interface

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.Issue94Realize
open AssemblyP1.P2
open AssemblyP1.P2RepeatResidual
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationUniqueness

variable {α : Type} [DecidableEq α] [Fintype α] {G H L : ℕ}

/-! ## 2. The interface theorem -/

/-- **The interface a route has to hit** (`BBTP2Prim`): the complete `L`-spectrum
of a `P2`, primitive circular word determines it up to cyclic rotation, at every
genome length, with the competitor unconstrained.

This is `BBTCompleteSpectrumUniqueness` (`AssemblyP1/P2.lean:154`) restricted to
the `P2`-and-primitive truths, which is the whole of what
`PopulationUniqueness.population_unique_ML_up_to_rotation` asks of
`BBTUniqueAt`. See the module docstring §1 for the two use sites.

No `Ukkonen` hypothesis is stated, because `P2.imp_Ukkonen` supplies it;
`BBTCompleteSpectrumUniqueness` demands `Ukkonen` of the truth only, never of the
competitor. **This is a `Prop`; it is not an inhabitant.** -/
def BBTP2Prim (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), P2 hK L W → IsPrimitive W →
    ∀ E : Fin K → α,
      specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W

/-- The same statement in `BBTCompleteSpectrumUniqueness` packaging: no `E` in
the statement, the competitor quantified inside. This is what a route is most
likely to produce directly, and `bbtCompleteSpec_of_P2Prim` converts it to
`BBTP2Prim`. -/
def BBTP2Prim' (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), P2 hK L W → IsPrimitive W →
    BBTCompleteSpectrumUniqueness hK L W

/-- `BBTP2Prim'` is `BBTP2Prim`: the only difference is where the universal
quantifier over competitors sits, and `Ukkonen` of the truth is discharged by
`P2.imp_Ukkonen`. -/
theorem bbTP2Prim_iff_bbTP2Prim' {L : ℕ} (hL : 2 ≤ L) :
    BBTP2Prim (α := α) L ↔ BBTP2Prim' (α := α) L := by
  constructor
  · intro h K hK W hP2 hprim E _ hspec
    exact h K hK W hP2 hprim E hspec
  · intro h K hK W hP2 hprim E hspec
    exact h K hK W hP2 hprim E (P2.imp_Ukkonen hL hP2) hspec

/-! ## 3. The reduction, kernel-checked -/

/-- **`BBTCompleteSpectrumUniqueness` at a `P2`, primitive word, from the
interface.**  The pointwise form of `BBTP2Prim`, keeping the `Ukkonen` premise
of `BBTCompleteSpectrumUniqueness` explicit; it is discharged by
`P2.imp_Ukkonen` at the caller. -/
theorem bbtCompleteSpec_of_P2Prim' (hB : BBTP2Prim (α := α) L)
    {K : ℕ} (hK : 0 < K) (W E : Fin K → α) (hP2 : P2 hK L W)
    (hprim : IsPrimitive W)
    (hspec : specCount (L := L) hK W = specCount (L := L) hK E) :
    RotEquiv hK E W :=
  hB K hK W hP2 hprim E hspec

/-- **The same in `BBTCompleteSpectrumUniqueness` form.**  A route that produces
this packaging needs nothing else. -/
theorem bbtCompleteSpec_of_P2Prim (_hL : 2 ≤ L) (hB : BBTP2Prim (α := α) L)
    {K : ℕ} (hK : 0 < K) (W : Fin K → α) (hP2 : P2 hK L W)
    (_hprim : IsPrimitive W) : BBTCompleteSpectrumUniqueness hK L W :=
  fun E _hUkk hspec => hB K hK W hP2 _hprim E hspec

/-- **`thm:population` from the interface.**  The conclusion is
`PopulationUniqueness.population_unique_ML_up_to_rotation`'s conclusion
verbatim --- the same two conjuncts, the same `PopLogLik`, the same `AdmClass`,
the same `PopSpectrum` --- and the hypothesis is `BBTP2Prim L` instead of
`hPevzner : EulerianCycleObstruction L`.

The proof is `PopulationUniqueness`'s, with the two applications of
complete-spectrum uniqueness (its lines 212 and 214) supplied by
`hBBTS`/`hBBTD` below instead of by a `BBTUniqueAt`. Both applications are at a
truth which satisfies `P2` and primitivity, which is exactly `BBTP2Prim`'s
hypothesis; note that the competitors `E` range over all words, which is why
`BBTP2Prim` does not constrain `E`. -/
theorem population_unique_ML_of_P2Prim
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hBBT : BBTP2Prim (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) := by
  refine ⟨?_, ?_⟩
  -- 1. the maximizer half, `lem:gibbs`, no structural hypothesis needed
  · intro K hK W _
    exact popLogLik_le_self' (popSpectrum_isProb L hG S) (popSpectrum_isProb L hK W)
  -- 2. the tie-to-rotation chain
  · intro K hK W hW hWTie
    obtain ⟨hPrimW, hP2W⟩ := hW
    have hEq : popSpectrum L hK W = popSpectrum L hG S :=
      (popTie_iff (popSpectrum_isProb L hG S)
        (popSpectrum_isProb L hK W)).mp hWTie
    have hDist : popProb (specCount (L := L) hG S) G
        = popProb (specCount (L := L) hK W) K := hEq.symm
    have hNorm : NormalizedEqual (W := Fin L → α)
        (specCount (L := L) hG S) (specCount (L := L) hK W) G K :=
      popProb_eq_iff_normalized hG hK hDist
    -- the interface, at the truth `S`
    have hBBTS : ∀ E : Fin G → α, True →
        specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S :=
      fun E _ hSpecE => hBBT G hG S hP2S hPrimS E hSpecE
    -- the interface, at the truth `W`
    have hBBTD : ∀ E : Fin K → α, True →
        specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W :=
      fun E _ hSpecE => hBBT K hK W hP2W hPrimW E hSpecE
    obtain ⟨hGK, hSpec⟩ :=
      population_uniqueness_primitive_P2_words
        (fun {_K : ℕ} (_W : Fin _K → α) => True)
        hG hK S W hL hPrimS hPrimW True.intro True.intro hNorm hBBTS hBBTD
    subst hGK
    refine ⟨rfl, ?_⟩
    show RotEquiv hG W S
    exact hBBTS W True.intro hSpec

/-- The `same_length` reading of `thm:population`, from the interface: the truth
is a population maximizer and every population tie among primitive `P2`
candidates is rotation-equivalent to it, with no length side condition on the
conclusion. Mirrors
`PopulationUniqueness.population_unique_ML_up_to_rotation_same_length`. -/
theorem population_unique_ML_same_length_of_P2Prim
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hBBT : BBTP2Prim (α := α) L) :
    (∀ E : Fin G → α, AdmClass L hG E →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hG E)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))
      ∧
    (∀ E : Fin G → α, AdmClass L hG E →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hG E)
          = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
        RotEquiv hG E S) := by
  obtain ⟨hCand, hRot⟩ :=
    population_unique_ML_of_P2Prim L hG hL S hPrimS hP2S hBBT
  refine ⟨fun E hE => hCand G hG E hE, ?_⟩
  intro E hE hETie
  obtain ⟨hGG, hRotE⟩ := hRot G hG E hE hETie
  cases hGG
  exact hRotE

/-- The two-genome reading of `thm:population`, from the interface: a concrete
primitive `P2` candidate `D` of any positive length that ties the truth's
population log-likelihood is a cyclic shift of `S`, with `|D| = |S|` carried by
the length identity. Mirrors
`PopulationUniqueness.population_tie_implies_rotation`. -/
theorem population_tie_implies_rotation_of_P2Prim
    (L : ℕ) (hG : 0 < G) {H : ℕ} (hH : 0 < H) (hL : 1 < L)
    (S : Fin G → α) (D : Fin H → α)
    (hPrimS : IsPrimitive S) (hPrimD : IsPrimitive D)
    (hP2S : P2 hG L S) (hP2D : P2 hH L D)
    (hTie : PopTie L hG hH S D)
    (hBBT : BBTP2Prim (α := α) L) :
    ∃ hGH : G = H, RotEquiv hG (hGH ▸ D) S := by
  obtain ⟨_, hRot⟩ :=
    population_unique_ML_of_P2Prim L hG hL S hPrimS hP2S hBBT
  exact hRot H hH D ⟨hPrimD, hP2D⟩ hTie

/-! ### 3b. The long/short split of the interface -/

/-- **The short-range companion** (`P2LongUnique`): `BBTP2Prim` restricted to
genome lengths `K ≥ L` --- the *long* window. This is the reading in which a
`P2`, primitive word of length at least the read length has its complete
`L`-spectrum determine it.

The name is the interface's *long* half. Its short counterpart
(`ShortRangeUnique`, `K < L`) is **already a theorem** of the tree ---
`AssemblyP1.Issue94KShort.vertexCycleEq_short_window_general`, which holds for
an arbitrary circular word with no `P2`, no primitivity and no `Ukkonen` --- so
the two halves together are exactly `BBTP2Prim` (`long_short_of_long`, below).

`ShortRangeUnique` is not proved here: instantiating the already-proved
short-window theorem requires importing `AssemblyP1.Issue94KShort`, whose
transitive imports reach `AssemblyP1.Issue94OrbitSearch`. That instantiation is
`Issue94ShortWindowCombiner` in
`AssemblyP1/Issue94LongWindowSplit.lean`, which imports this module; see the
module docstring §4. `P2LongUnique` itself is a `Prop` and is **not** an
inhabitant. -/
def P2LongUnique (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), L ≤ K → P2 hK L W → IsPrimitive W →
    ∀ E : Fin K → α,
      specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W

/-- **The short-range companion** (`ShortRangeUnique`): `BBTP2Prim` restricted to
genome lengths `K < L`. True in the tree for *arbitrary* words; stated here with
the `P2`-and-primitive hypotheses so that the two halves compose exactly. -/
def ShortRangeUnique (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), K < L → P2 hK L W → IsPrimitive W →
    ∀ E : Fin K → α,
      specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W

/-- **Long and short together are the whole interface.**
`P2LongUnique L ∧ ShortRangeUnique L ↔ BBTP2Prim L`: at every genome length
either `K < L` or `L ≤ K`, and the two cases carry the two hypotheses. No `L ≥ 1`
is needed --- the split is a case split on the order of two naturals. -/
theorem long_short_of_long {L : ℕ} (hLong : P2LongUnique (α := α) L)
    (hShort : ShortRangeUnique (α := α) L) : BBTP2Prim (α := α) L := by
  intro K hK W hP2 hprim E hspec
  by_cases hLK : L ≤ K
  · exact hLong K hK W hLK hP2 hprim E hspec
  · exact hShort K hK W (by omega) hP2 hprim E hspec

/-- **The endpoint follows from the long half alone, plus the already-proved
short range.**  This is the form a route should aim at: prove `P2LongUnique L`
for `L`-long or larger genomes, and the short genomes are free.

`hShort` is discharged in the tree by
`AssemblyP1/Issue94KShort.vertexCycleEq_short_window_general` via
`bbtCompleteSpec_of_short_window`; see
`AssemblyP1/Issue94LongWindowSplit.lean` for the instantiation. -/
theorem population_unique_ML_of_long_unique
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hLong : P2LongUnique (α := α) L) (hShort : ShortRangeUnique (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) :=
  population_unique_ML_of_P2Prim L hG hL S hPrimS hP2S
    (long_short_of_long hLong hShort)

/-- **`BBTUniqueAt L` supplies the long half**, since it carries no length side
condition at all. So the endpoint's single remaining input, read off in the
reading a route should use, is `P2LongUnique L` alone. -/
theorem p2LongUnique_of_bbtUniqueAt {L : ℕ} (hL : 2 ≤ L)
    (hBBT : BBTUniqueAt (α := α) L) : P2LongUnique (α := α) L :=
  fun K hK W _ hP2 _hprim E hspec => hBBT K hK W E (P2.imp_Ukkonen hL hP2) hspec

/-! ## 4. The interface from the other side: nothing is lost -/

/-- **`BBTUniqueAt L` implies the interface.**  `BBTUniqueAt`
(`AssemblyP1/P2.lean:165`) ranges over every `Ukkonen` word at every genome
length; `P2.imp_Ukkonen` puts every word `BBTP2Prim` asks about into that class,
and no length condition is used. So the interface is strictly within reach of
what is already postulated. -/
theorem bbTP2Prim_of_bbtUniqueAt {L : ℕ} (hL : 2 ≤ L)
    (hBBT : BBTUniqueAt (α := α) L) : BBTP2Prim (α := α) L :=
  fun K hK W hP2 _hprim E hspec => hBBT K hK W E (P2.imp_Ukkonen hL hP2) hspec

/-- **No loss: the endpoint's existing hypothesis still implies the
interface**, hence everything above from it, and the exported theorems of
`PopulationUniqueness` are untouched by this module. -/
theorem bbTP2Prim_of_obstruction {L : ℕ} (hL : 2 ≤ L)
    (hObs : EulerianCycleObstruction (α := α) L) : BBTP2Prim (α := α) L :=
  bbTP2Prim_of_bbtUniqueAt hL (bbtUniqueAt_of_obstruction hL hObs)

/-- **The endpoint follows from `thm:BBT` in its source form.**  After the
realization bridge of `AssemblyP1/Issue94EulerianRealize` landed, `BBTUniqueAt L`
--- the project-formatted `thm:BBT` --- is enough, and **no
Eulerian-touring lemma of this project's own stands between the endpoint and
the published theorem.**  This is the clean dependency statement of #89; the
remaining input is a single external inhabitant, not an internal gap. -/
theorem population_unique_ML_of_BBTUniqueAt
    (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
    (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
    (hBBT : BBTUniqueAt (α := α) L) :
    ((∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
        PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
          ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
      PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
        = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
      ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) :=
  population_unique_ML_of_P2Prim L hG hL S hPrimS hP2S
    (bbTP2Prim_of_bbtUniqueAt (by omega) hBBT)

/-! ## 5. Executable audit -/

#print axioms AssemblyP1.Issue94Interface.long_short_of_long
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_long_unique
#print axioms AssemblyP1.Issue94Interface.p2LongUnique_of_bbtUniqueAt
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_iff_bbTP2Prim'
#print axioms AssemblyP1.Issue94Interface.bbtCompleteSpec_of_P2Prim'
#print axioms AssemblyP1.Issue94Interface.bbtCompleteSpec_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_same_length_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.population_tie_implies_rotation_of_P2Prim
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_of_bbtUniqueAt
#print axioms AssemblyP1.Issue94Interface.bbTP2Prim_of_obstruction
#print axioms AssemblyP1.Issue94Interface.population_unique_ML_of_BBTUniqueAt
#print axioms AssemblyP1.Issue94Realize.obstruction_iff_bbtUniqueAt
#print axioms AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation

end AssemblyP1.Issue94Interface