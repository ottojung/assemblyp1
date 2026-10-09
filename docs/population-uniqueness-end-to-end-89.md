# End-to-end population uniqueness from the real objective (issue #89)

> **2026-10-09 correction (board #221).** The acceptance criterion recorded as
> "NOT met" below was subsequently met on `main` (PR #117, merge `e9fcf01`):
> `AssemblyP1.Issue94Complete.population_unique_ML` is fully kernel-checked with
> **no external BBT premise**, proving optimality and uniqueness up to rotation
> over *every* positive-length primitive P2 candidate for a primitive P2 truth
> at `L >= 2`. Its `#print axioms` reports only `propext`, `Classical.choice`,
> `Quot.sound`. The residual `P2LongUnique L` named below is now inhabited by
> `AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2LongUnique` (a
> support-descent / component-antiderivative proof). The theorem
> `PopulationUniqueness.population_unique_ML_up_to_rotation` still literally
> takes `hPevzner : EulerianCycleObstruction L`; it is now a *reusable
> conditional core*, not the project endpoint. The historical 2016 referent
> remains a source gap, and the **finite** same-length rotation corollary still
> uses the external Bresler–Bresler–Tse input. See
> `paper/sections/05-population.tex` (Remark on the internal discharge).

_Status: kernel-checked Lean theorems, 2026-09-26, updated by
`docs/bbt-eulerian-cycle-89.md`. **The issue's acceptance criterion — that the
exported theorem take no BBT / complete-spectrum uniqueness premise — is NOT
met.** The objective and P2 work is complete and kernel-checked. The
`thm:BBT` bridge is now taken in the *Eulerian-cycle* form of Bresler–Bresler–Tse
2013, Theorem 3: the exported theorem takes
`hPevzner : BBTEulerian.EulerianCycleObstruction L` (uniqueness of the Eulerian
cycle of the condensed `(L-1)`-mer graph, with the long triple-repeat /
interleaved-repeat obstruction spelled out), and `P2.BBTUniqueAt` is *derived*
from it inside the proof by `BBTEulerian.bbtUniqueAt_of_obstruction` — it is no
longer a premise anywhere. The single remaining unproved statement of the chain
is `BBTEulerian.EulerianCycleObstruction` itself; see "Acceptance status" at
the end and `docs/bbt-eulerian-cycle-89.md` §6 for its exact shape. No `axiom`,
`sorry` or `admit` was added; `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for every exported theorem._

## What changed

Before this packet, `AssemblyP1/PopulationUniqueness.lean` exported

```text
population_unique_ML_up_to_rotation
  (PopTie  : ∀ {K}, (Fin K → α) → Prop)          -- opaque "tie"
  (PopMaximizer : Prop)                            -- opaque "truth is ML"
  (hGibbs : PopTie D → NormalizedEqual …)          -- the whole Gibbs argument
  (hBBTS / hBBTD : …)                              -- BBT, free-floating
```

so the *caller* had to supply the objective, the meaning of a population
tie, the maximizer claim, the entire Cover–Thomas analysis, and the
Bresler–Bresler–Tse analysis. The exported theorem therefore said almost
nothing about the published model: it said that a caller-chosen notion of
tie, joined by a caller-chosen bridge, implies a caller-supplied BBT
statement. The candidate condition `AdmP2` was likewise an opaque
parameter, so the theorem never said what its candidates satisfy.

All of those seams are now closed. The exported theorem states the actual
population objective and the actual P2 condition, and derives the
conclusion in the kernel.

## The exported theorem

```text
AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation
  {α} [DecidableEq α] [Fintype α] {G}
  (L : ℕ) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
  (hPrimS : PopulationReduction.IsPrimitive S)
  (hP2S   : P2 hG L S)
  (hPevzner : BBTEulerian.EulerianCycleObstruction (α := α) L) :
  ( (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
       PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
         ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))
    ∧
    (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
       PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
         = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
       ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) )
```

where

* `popSpectrum L hG S = AssemblyP1.OrientedRigidity.specCount (L := L) hG S / |S|`
  is the actual population read distribution `p_S(w) = spec_L(S)(w)/|S|` of
  `def:population`;
* `PopLogLik : (Fin L → α → ℝ) → (Fin L → α → ℝ) → WithBot ℝ` is
  `∑_w p_S(w) log p_D(w)`, with the **published** `ℓpop_S(D) = -∞`
  convention represented as `⊥`. Modelling `-∞` as `⊥` in `WithBot ℝ`
  matters: the maximizer claim then is a genuine `≤` in a linear order,
  not an opaque `Prop` the caller declares;
* `AdmClass L hK W = IsPrimitive W ∧ P2 hK L W` is primitivity together
  with **the actual P2 of `def:P1P2`**.

So: among primitive P2-admissible oriented circular candidates, the truth
maximizes the published population objective, and every population tie is
a cyclic shift of the truth (with the length identity carried explicitly).
This is `thm:population`.

Companion corollaries, all kernel-checked:

| theorem | content |
| --- | --- |
| `population_tie_implies_rotation` | the two-genome form, preserving the shape of the previous export: a concrete `D` of any positive length that ties is a rotation of `S` |
| `population_unique_ML_up_to_rotation_same_length` | the `AssemblyModel.IsUniqueMaximumLikelihoodUpToEquiv` packaging with `RotEquiv` as genome equivalence, on the same-length slice |
| `truth_is_population_maximizer_primitive_P2` | the maximizer half alone; note it needs *no* structural hypothesis on the candidate, as `lem:gibbs` states |
| `population_tie_implies_normalized` | the kernel-checked core of `lem:gibbs`'s equality direction: a population tie forces the proportional spectrum equality the #70 reduction consumes |

## Where each ingredient is proved

| paper step | Lean location | epistemic class |
| --- | --- | --- |
| `def:population` read distribution | `PopulationGibbs.popProb`, `popSpectrum_isProb` | kernel-checked |
| `lem:gibbs`, truth is a maximizer | `PopulationGibbs.popLogLik_le_self'` | kernel-checked |
| `lem:gibbs`, equality iff `p_D = p_S` | `PopulationGibbs.popTie_iff` (strict form) | kernel-checked |
| `p_D = p_S` ⇒ proportional spectra | `PopulationGibbs.popProb_eq_iff_normalized` | kernel-checked |
| `def:P1P2` (P2) | `P2.P2`, via `P2.mkGenome` | kernel-checked |
| P2 aligns with Ukkonen at `K = L-1` | `P2.P2.imp_Ukkonen` | kernel-checked |
| `lem:scaling` (gcd one) | `PopulationReduction.gcd_one_of_primitive_P2_words` (#70) | kernel-checked |
| corollary (normalized ⇒ ordinary) | `PopulationReduction.normalized_to_ordinary` (#70) | kernel-checked |
| `thm:BBT` at `K = L-1` | `BBTEulerian.EulerianCycleObstruction` (condensed-graph Eulerian-cycle uniqueness) | **external, named**; `P2.BBTCompleteSpectrumUniqueness` and `P2.BBTUniqueAt` are now *derived* from it |

`P2.mkGenome` is the bridge between the two word layers already in the
repository: the reduction's `Fin G → α` word is read as
`SourceFaithfulIs.Genome α`, so `P2` quantifies over the *source-faithful*
`IsTripleRepeat`, `IsRepeat` and `Interleaved` predicates rather than a
new, parallel repeat semantics.

## The one residual formalization boundary

> **Superseded 2026-10-09 (board #221).** This boundary was subsequently
> discharged internally by the support-descent / component-antiderivative proof
> (`concrete_p2LongUnique`); see the correction banner at the top and the
> "Acceptance status" supersession note. The material below records the
> pre-discharge state.

`thm:BBT` (Bresler–Bresler–Tse 2013, Theorem 3) was the only external
mathematical input at the time of this packet. It was treated as irreducible:
complete-spectrum uniqueness for a Ukkonen-satisfying circular word is
itself a substantial combinatorial theorem about Eulerian cycles in
de Bruijn graphs, and the project's own note
`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md` records that
the direct maximal-extension route has a genuine gap.

Rather than hide it, the exact smallest specialized statement is named:

```text
P2.BBTCompleteSpectrumUniqueness (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ E : Fin G → α, P2.Ukkonen hG L S →
    specCount (L := L) hG S = specCount (L := L) hG E → RotEquiv hG E S

P2.BBTUniqueAt (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), BBTCompleteSpectrumUniqueness hK L W
```

`P2.BBTUniqueAt` is *not* this packet's premise any more: it is now derived
from the Eulerian-cycle form of the same theorem,

```text
BBTEulerian.EulerianCycleObstruction (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), BBTEulerian.EulerianCycle hK L S σ →
      BBTEulerian.VertexCycleEq hK L S σ (Equiv.refl _) ∨
      BBTEulerian.LongObstruction hK L S
```

by `BBTEulerian.bbtUniqueAt_of_obstruction` (from `2 ≤ L`, which `hL : 1 < L`
supplies). `BBTEulerian.EulerianCycle` is a *presentation* of an Eulerian
cycle of the condensed `(L-1)`-mer multigraph and `BBTEulerian.VertexCycleEq`
is that cycle with the starting point forgotten, so the premise is Theorem 3
of Bresler–Bresler–Tse verbatim: the condensed `K`-mer graph of a
Ukkonen-satisfying genome has a **unique Eulerian cycle**, and a
non-rotational one forces a maximal triple repeat or two interleaved maximal
repeats of length `≥ L-1`. See `docs/bbt-eulerian-cycle-89.md`.

Properties of this boundary statement:

* it is phrased on the project's own objects, so no translation layer is
  missing — at `K = L - 1` the `K`-mer graph is exactly the
  length-`(L-1)` de Bruijn graph the #70 division/Eulerian argument runs
  on, and the `(K+1)`-spectrum is exactly `specCount`;
* it is *weaker* than the source theorem (the uniqueness implication only,
  no uniqueness-of-Eulerian-cycle statement), so nothing is smuggled in
  through it;
* `P2.imp_Ukkonen` is **proved**, so a consumer supplies a theorem about
  complete spectra rather than a repeat condition to be re-verified;
* it is a `def`, not an `axiom`, and the exported theorem takes an
  explicit inhabitant. A future packet that proves `BBTUniqueAt L` turns
  the exported theorem into an axiom-free end-to-end result with no change
  to its statement.

Everything else — the whole Gibbs/KL layer, the P2-to-Ukkonen alignment,
the division/Eulerian gcd-one argument, the proportional-cancellation
lemma, the rotation-invariance and non-primitivity of powers used to
refute the `W^g` competitor — is kernel-checked in this repository.

## Modeling decisions recorded here

* **`-∞` as `⊥` in `WithBot ℝ`.** `def:population` defines
  `ℓpop_S(D) = -∞` when a word read by the truth is not read at all by the
  candidate. `WithBot ℝ` is the order in which `-∞` is the least element,
  so the maximizer claim is a real inequality and the published convention
  is preserved rather than replaced by a "supports must agree" side
  condition. (With `EReal` or an `⊤`-valued convention the inequality would
  point the wrong way, which would silently falsify `lem:gibbs`.)
* **Tie semantics.** `PopLogLik pS pD = PopLogLik pS pS` in `WithBot ℝ`
  is exactly "the candidate achieves the truth's population
  log-likelihood". Note this is *stricter* than the `ℓpop_S(D) ≤ ℓpop_S(S)`
  reading: a candidate that omits a truth-read word gets `-∞` and is
  therefore not a tie. The paper's proof applies BBT only to candidates
  satisfying `ℓpop_S(D) = ℓpop_S(S)`, so this is the reading the proof
  needs and the one exported.
* **No `L ≤ |D|` hypothesis.** The paper states `L ≥ 2` with `L ≤ |D|`.
  The exported theorem assumes only `L ≥ 2`: the project's
  `OrientedRigidity.window` is defined for every `L`, so the length
  restriction is not needed by any step. This is a *strengthening*, not a
  deviation, and it is visible in the statement.
* **Genome-length side conditions.** `IsPrimitive` and `P2` are
  length-agnostic, so the class quantifies over all positive lengths `K`
  and the length identity `|W| = |S|` is an explicit existential in the
  conclusion rather than an ambient side condition.
* **P2 at `L` vs Ukkonen at `K = L - 1`.** `P2.imp_Ukkonen` requires
  `2 ≤ L`; with `L ≤ 1` the P2 interleaved clause is unsatisfiable for a
  real repeat, so the alignment holds vacuously but the threshold identity
  is not available. Since the exported theorem assumes `1 < L`, this is
  not a restriction on the result.

## What this does not do

* It does not prove `EulerianCycleObstruction` (equivalently
  `BBTUniqueAt`); see the boundary above and
  `docs/bbt-eulerian-cycle-89.md`.
* It does not answer the finite 2016 question. It answers the population
  question, and the paper's scope note (oriented single-strand model only)
  is unchanged: nothing here transfers to reverse-complement-collapsed
  molecule classes.
* It does not change the #70 regression `primitivity_insufficient`, which
  still shows that primitivity alone is insufficient: the P2 hypothesis
  and the BBT input are both genuinely used.


## Acceptance status (issue #89 criterion)

> **Superseded 2026-10-09 (board #221).** The criterion is now **met**. The
> `hPevzner : BBTEulerian.EulerianCycleObstruction` hypothesis below is no longer
> the project endpoint: that obstruction is discharged by the concrete
> component-antiderivative proof `AssemblyP1.Issue94ConcreteAntiderivative.concrete_p2LongUnique`,
> and `AssemblyP1.Issue94Complete.population_unique_ML` composes it with the
> short-window theorem to give the axiom-free end-to-end result (axioms only
> `propext`, `Classical.choice`, `Quot.sound`). The text below records the state
> of this packet *before* that discharge and is retained for provenance.

**At the time of this packet, not met.** The exported theorem still reads

```text
population_unique_ML_up_to_rotation
  (L) (hG : 0 < G) (hL : 1 < L) (S : Fin G → α)
  (hPrimS : IsPrimitive S) (hP2S : P2 hG L S)
  (hPevzner : BBTEulerian.EulerianCycleObstruction (α := α) L) : …
```

so a caller still supplies the uniqueness of the condensed graph's Eulerian
cycle --- now in the source's own object rather than as a complete-spectrum
black box (`BBTUniqueAt` is derived from it). Two routes were attempted; here
is exactly where they stand.

### Route A — reuse `OrientedFinalRigidity`. Refuted, kernel-checked.

The plan was to obtain `RotEquiv` from the kernel-checked same-length
spectrum rigidity (`oriented_same_length_spectrum_rigidity`, issue #74)
together with P2. `AssemblyP1/InterleavingNeededCounterexample.lean` now
rules this out: for

* `S = A B A C B C`, `E = A B C A C B`, `L = 2`, `G = 6`, over `{A,B,C}`,

it is kernel-checked that the complete `2`-spectra are **equal**, that both
words are **primitive**, that neither has a maximal Bresler triple repeat
(so the triple-repeat clause of P2 holds for both), and that `E` is **not** a
rotation of `S`. Both fail P2, and they fail it *only* through the
interleaved clause (`A` at starts `0,2` interleaves `B` at starts `1,4`;
for `E`, `A` at `0,3` interleaves `B` at `1,5`). So the interleaved clause —
not primitivity, not the triple clause, and not spectrum rigidity — is
exactly the hypothesis that rules out the second Eulerian circuit. The
existing circulation layer (`OrientedRigidity`, `RepeatAdapter`) contains no
statement about the *order* in which window edges are traversed, which is
precisely what a rotation claim needs.

### Route B — prove the Eulerian-cycle uniqueness in Lean. Identified precisely, not completed.

`AssemblyP1/BBTEulerian.lean` isolates the statement
(`EulerianCycleObstruction`, equivalently `UniqueEulerianCycle`) and proves the
whole reduction around it, and `docs/bbt-eulerian-cycle-89.md` §6 lists the
three remaining sub-steps (condensation bookkeeping, the maximal-extension
bridge from branch occurrences to maximal repeats, and the
triple-or-interleaved dichotomy), together with the exhaustive search
`scripts/verify_eulerian_cycle_uniqueness_89.py` that finds no counterexample
to the statement for `G ≤ 9` over alphabets of size `2` and `3`.

What the project side already delivers, and what is kernel-checked:

1. P2's triple clause gives node multiplicity `≤ 2` — the repeated-(L-1)-mer
   case is the only hard case; with all multiplicities `1` both words are
   simple cycles of the same multigraph and the conclusion is elementary.
2. The interleaved clause is the residual content (Route A's witness).

The remaining mathematical core is the classical BBT statement: two distinct
Eulerian circuits of the same `(L-1)`-mer multigraph force an interleaved
maximal repeat pair of length `≥ L - 1`. This is a genuine
word-level argument about traversal order with several delicate steps
(a maximal-extension lemma for pairs, the pairing/"crossing" dichotomy at
doubly-visited nodes, and arc arithmetic for the interleaving predicate).
It was not completed here; the honest assessment is that it exceeds a single
focused packet, and the repository already records a *related* gap in the
direct maximal-extension route
(`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md`).

A future packet that proves `BBTEulerian.EulerianCycleObstruction L` turns the
exported theorem into an axiom-free end-to-end result **with no change to its
statement** — the
hypothesis is already exactly the specialized theorem, nothing weaker and
nothing stronger. That is the recommended next step; the surrounding
infrastructure is in place and the reduction above is what the proof must
discharge.
