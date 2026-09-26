# #88 in the wraparound regime: the faithful §6.2 ML predicate, the graph-level
# contrapositive, and the one statement that is still missing

This note records the outcome of the wraparound-regime question left open at
the audited head `679e758`. Everything named `kernel-checked` below is proved in
`AssemblyP1/MLEscape.lean`, is in the default build, and appears in the
`#print axioms` audit of `AssemblyP1.lean`.

## 0. What this note does and does not settle

**Settled (kernel-checked).**

1. A *genuinely faithful* §6.2 maximum-likelihood predicate
   `Is62SpelledMLMax`: truth membership in the literal strict-oriented §6.2
   spelled-candidate class **and** dominance of every same-length candidate in
   that class under the exact finite likelihood.
2. The likelihood comparison in that class is the pointwise spectral comparison
   on the observed read types (`exactLik_le_of_spec_le`,
   `observed_spectral_excess_of_ml_failure`), with the direction of the
   implication stated and justified — the converse is *false*, see §3.
3. The graph-level reformulation of the whole question (`IsMassGPositiveCirculation`,
   `BeatsTruthSpectrum`, `HasSpectralEscape`) and the contrapositive
   `ml_failure_gives_spectral_escape`: a §6.2 same-length candidate that beats
   the truth's exact likelihood yields a positive balanced circulation of total
   mass `G` on the truth's window support that strictly exceeds the truth's
   spectrum.
4. **Two of the three steps of the culprit statement**, at the graph level:
   `spectralEscape_gives_longTriple` (an escape forces a long maximal triple
   repeat, by applying the existing rigidity chain to the escaping circulation)
   and `informationFeasible_escape_gives_wraparound` (under `I_s` that repeat
   cannot be mid-range, so it lies in the **wraparound band**
   `max (L - 1) (G - L) ≤ ℓ < G`, named by `HasWraparoundTripleRepeat`).
5. The target-shaped theorem
   `informationFeasible_62_spelledML_of_escape_crux`: **full `I_s` + a genuine
   §6.2 truth certificate + a realization + a genuine §6.2 candidate certificate
   ⟹ exact same-length ML dominance, with no long-triple-repeat premise at
   all**, covering the whole wraparound regime. Its single extra hypothesis is
   the culprit statement `EscapeForcesMidRangeRepeat`, which is a *combinatorial*
   assertion about the truth's own repeats and is stated at the graph/repeat
   level.
6. The precise content of the residual band: `HasMidRangeTripleRepeat`
   (`L - 1 ≤ ℓ < G - L`) is exactly the band clause 2 of `I_s` forbids
   (`informationFeasible_no_midRangeTriple`, from the sharp bridging dichotomy),
   and `¬ HasLongTripleRepeat` implies `¬ HasMidRangeTripleRepeat`, so the new
   nondegeneracy premise is strictly weaker than `hno` while being equivalent to
   it under `I_s`.

**Not settled.** Step 3, i.e. `EscapeForcesMidRangeRepeat`, is not proved. It is
stated as a `def` and used as an explicit hypothesis of the target theorem; no
`sorry`, no `admit`, no `axiom`. Steps 1 and 2 *are* proved, so the residual is
exactly: *an escape that also produces a wraparound-bridged long triple repeat
produces a mid-range one as well*. §4 gives the evidence, §5 the strategy and
the two sufficient intermediate goals, §6 what remains.

**Not revived.** The earlier `AABB`/`ABAB` instance is *not* a refutation of the
literal §6.2 maximizer theorem (truth membership fails there) and is not used
here; the audited correction in `docs/same-length-exact-ml-88-refutation.md` and
`docs/same-length-62-maximizer.md` stands.

## 1. Why the residual is a *band*, and which band

`AssemblyP1.BridgingBridge.tripleRepeat_bridged_length` is the sharp form of the
bridging fact: if a triple repeat of length `e` is all-bridged then

```
e + 2 ≤ L  ∨  G - e ≤ L
```

(the first disjunct is the intended straddling mode, the second is the
*wraparound* mode in which one read covers the whole complement arc). Since the
long-triple-repeat predicate asks for `e ≥ L - 1`, the first disjunct is
excluded and clause 2 of `I_s` forces `e ≥ G - L`. So

* `L - 1 ≤ e < G - L` is **impossible** under `I_s` (mid-range band, forbidden);
* `max (L - 1) (G - L) ≤ e < G` is the **wraparound regime**, and clause 2 of
  `I_s` does not reach it.

`HasMidRangeTripleRepeat` names the forbidden band, and
`informationFeasible_no_midRangeTriple` is the kernel-checked statement that
`I_s` excludes it. This is why the target theorem of §0.4 can drop `hno`: the
culprit statement produces an *impossible* repeat, not merely a long one.

The regime is non-empty: `AssemblyP1.WraparoundTripleRepeat` kernel-checks
`AAAAB` at `G = 5, L = 3` with full `I_s`, all windows observed, and a maximal
triple repeat of length `2 = L - 1 = G - L` (wraparound mode, bridged by the
read at start `2`, which covers the complement arc `{2,3,4}`). A second,
independent kernel-checked wraparound instance is `AssemblyP1.MLEscape.truth0`:
`0000001` at `G = 7, L = 3`, whose maximal triple repeat of length `2` lies in
`[L - 1, G - L) = [2, 4)` — i.e. it is in the *forbidden* band, which is why that
genome is not `I_s`-feasible (§4).

## 2. The ML predicate, with the conventions kept explicit

`Is62SpelledMLMax hG S x` (over `S D : Fin G → α`, `x` the observed read
multiplicities, `verts`/`toList`/`oMin` the literal §6.2 data) is

* `SameLength62Maximizer.Is62Candidate62 ⟨G, hG, S⟩ verts toList id id oMin`
  — *membership*: a `Spelling` of `G` positions that genuinely **represents**
  `S` (its strand at each position is `S`'s own length-`L` window there), a
  literal `Section62Flow.SpelledFeasible62` certificate, and the flow being the
  flow the walk itself carries; **and**
* for every `D : Fin G → α` carrying such a certificate for the same observed
  read set, `exactLik hG D x ≤ exactLik hG S x`.

Conventions, unchanged from `docs/ml-formalization-contract.md` and
`docs/oriented-same-length-ml-88.md`:

| choice | value | where |
| --- | --- | --- |
| read type | oriented single-strand length-`L` circular window, `rep = rc = id` | `SameLength62Maximizer` (strict mode) |
| genome equivalence | rotation only (`IsCyclicShift`) | `OrientedFinal` |
| candidate length | part of the type (`Fin G → α`), i.e. a restricted candidate universe | `Is62SpelledMLMax` |
| objective | exact Medvedev–Brudno multinomial, `(d_D w / G) ^ (x w)`, candidate-intrinsic `N(D) = G` | `OrientedSameLengthML.exactLik` |
| observation-only factor | `n! / ∏ w x w!` divided out; `exactLik_scale` reinstates it without changing any comparison | `OrientedSameLengthML.exactLik_scale` |
| observation | `observedOf hG S ρ` from a realization `ρ : Fin n → Fin G`; a `Finset` of starts is never the observation | `OrientedSameLengthML.observedOf` |
| sample size | `n = totalReads x`, not a free parameter | `OrientedSameLengthML.totalReads` |
| alphabet | `[Fintype α] [DecidableEq α]` | all theorems here |

The maximizer-only reading and the uniqueness-up-to-rotation reading are kept
apart as in the rest of the repository; only the former is claimed here.

`informationFeasible_62_spelledML_of_no_long_triple` recovers the audited result
in this predicate, so the new and old theorems are directly comparable: same
hypotheses, same objective, the new one stated with membership.

## 3. The likelihood comparison is the spectral comparison — in one direction

`exactLik_le_of_spec_le` proves the sufficient direction: if `D` has the truth's
window support and the observation is a realization on the truth, then

```
(∀ w, 0 < x w → specCount D w ≤ specCount S w)  ⟹  exactLik D x ≤ exactLik S x
```

The reason is that every factor `(d w / G) ^ (x w)` has base in `(0, 1]` on the
window support (a read type's multiplicity is at most `G`) and is `1` off it
(nothing is observed there), so the product over the support is monotone in each
multiplicity.

**The converse is false and is not claimed.** Two same-support same-length
spectra of equal total mass can differ in both directions at once, and the
likelihood product can then go either way depending on the observation. The
concrete instance, from the same definitions (`G = 5`, `L = 2`, alphabet
binary, same window support `{00, 01, 10}`):

```
truth      00001 : d(00) = 3, d(01) = 1, d(10) = 1
candidate  00101 : d(00) = 1, d(01) = 2, d(10) = 2
```

* observation `{01, 10}` (one read of each): `exactLik(cand) = (2/5)² (2/5)² =
  0.0256 > 0.0016 = (1/5)² (1/5)² = exactLik(truth)` — the candidate wins, and
  indeed `d(01) > d_S(01)`;
* observation `{00}`: `exactLik(cand) = (1/5) = 0.2 < 0.6 = (3/5) =
  exactLik(truth)` — the truth wins, although the pointwise domination of the
  second kind holds nowhere on the observed type `00` (`1 < 3`).

So `exactLik D ≤ exactLik S` does **not** imply the pointwise spectral
comparison, and the exact content of ML failure is the weaker
`observed_spectral_excess_of_ml_failure`: ML failure implies that *some observed
read type* has strictly larger multiplicity in `D`. That is all the reduction
needs, and it is the direction recorded in the module header. (This instance is
of course not `I_s`-feasible at `L = 2`; it is used only to show the direction
of the implication, not to make a claim about #88.)

## 4. The graph-level contrapositive, and the evidence for it

The question is now purely about the truth's window support:

> can a positive balanced circulation of total mass `G` on the truth's window
> support strictly exceed the truth's spectrum at some read type?

* `IsMassGPositiveCirculation hG S L B` is literally the triple of hypotheses
  that `OrientedFinal.oriented_same_length_spectrum_rigidity` consumes, with the
  candidate's spectrum replaced by an arbitrary weighting `B`.
* `eq_specCount_of_massG_le` is the small structural fact that makes the
  reduction work: a mass-`G` circulation that is pointwise bounded by the truth's
  spectrum *is* the truth's spectrum (total mass turns domination into
  equality). No primitivity, no period premise, no `hno`.
* `candidate_is_massG_positive_circulation` is the graph-level content of the
  §6.2 bridge: a same-support same-length candidate's spectrum is such a
  circulation.
* `ml_failure_gives_spectral_escape` is the contrapositive, at the level of the
  literal §6.2 class.

The culprit statement is therefore:

> `EscapeForcesMidRangeRepeat`: a spectral escape forces a maximal triple repeat
> of the truth of length `L - 1 ≤ ℓ < G - L`.

### 4.1 Kernel-checked, non-vacuous instance

`AssemblyP1.MLEscape.culprit_instance_checked` is the pairing that makes the
evidence non-vacuous:

* `cand0_is_escape` — the **premise** holds: truth `0000001`, candidate
  `0001001`, `G = 7`, `L = 3`, same window support, and the read type `100` has
  multiplicity `1` in the truth and `2` in the candidate;
* `truth0_has_midrange_triple` — the **conclusion** holds there: the maximal
  triple repeat at starts `0, 1, 4` of length `2 ∈ [2, 4)` (the three length-`2`
  windows are `00`; the symbol before start `0` and the symbol after start `4`
  are both the `1` at position `6`, so the copy is maximal on both sides).

The pairing is deliberate. An earlier harness in this repository's history was
void because the implication it checked had an unsatisfiable premise
(`docs/same-length-exact-ml-88-refutation.md` §4), and a non-vacuity companion
is the direct guard against repeating that.

### 4.2 Exhaustive search outside Lean

`scripts/issue88-wraparound-search.py` transcribes the same definitions and runs
the finite search. One structural remark makes it cheap: **`I_s` is monotone in
the start set** (every clause is a "some read does …" or coverage condition), so
"Some `R ∈ I_s`" is decided at the maximal start set `R = Fin G`.

| alphabet | `G ≤` | `I_s`-satisfiable `(S, L)` | escapes | escapes at an `I_s`-feasible `(S, L)` | culprit statement holds | violated |
| --- | --- | --- | --- | --- | --- | --- |
| binary | 7 | 908 | 258 | 0 | 258 | 0 |
| binary | 9 | (census 7) | 1584 | 0 | 1584 | 0 |
| 3-letter | 7 | (see below) | 1764 | 0 | 1764 | 0 |
| 4-letter | 6 | (see below) | 972 | 0 | 972 | 0 |

Reading the table:

* an *escape* is a same-support same-length candidate whose spectrum strictly
  exceeds the truth's on a support read type; there are many of them (they are
  the `A`-run / almost-periodic families, e.g. `0000001` vs `0001001`);
* **no** escape occurs at an `I_s`-feasible instance, in any of these ranges;
  this is the finite evidence for the conclusion of the target theorem;
* the culprit statement holds at **every** escape, including the ones that are
  not `I_s`-feasible, so the band it produces is the right one.

Reproduce with

```
python3 scripts/issue88-wraparound-search.py 9 2 7
python3 scripts/issue88-wraparound-search.py 7 3 7
python3 scripts/issue88-wraparound-search.py 6 4 6
```

**Why the quantified version is not in Lean.** The obvious
`decide`-statement — all binary truths and candidates at `G = 7`, all
`2 ≤ L ≤ 7` — was attempted and abandoned: with `Finset`-based `support` and
`specCount` the kernel's `whnf` evaluator needs hundreds of millions of steps
(the module went from 4 s to over 8 minutes and 18 GB before being killed). The
Lean side therefore keeps only the concrete, non-vacuous instance, which is the
part that is cheap to check and the part that guards against a void harness.
This is recorded as a deliberate build-cost decision, not as a proof.

## 5. Proof strategy for the culprit statement

The strategy is the contrapositive the question suggests, at the repeat level,
not "I_s ⟹ ¬ long triple repeat" (which is false).

**Step 1 (kernel-checked: `spectralEscape_gives_longTriple`).**
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity` proves that
`¬ HasLongTripleRepeat` gives spectrum rigidity for *any* mass-`G` positive
circulation of the support — its proof never uses that the circulation is the
spectrum of a word — so an escape forces a maximal triple repeat of the truth
of length `≥ L - 1`. Equivalently, `spectralEscape_contradiction` says an
escape and the absence of long triple repeats are incompatible.

**Step 2 (kernel-checked: `informationFeasible_escape_gives_wraparound`).** The
repeat of Step 1 cannot have length `< G - L`, because clause 2 of `I_s` forbids
that band (`informationFeasible_no_midRangeTriple`) and
`longTriple_band` splits the long triples into the mid-range band and the
wraparound band. So an escape forces a *wraparound* maximal triple repeat: one
whose complement arc has length `≤ L` and which is therefore bridged by a single
read lying inside its own complement arc. This is exactly the regime the
audited `hno` premise excluded and `I_s` does not forbid, and it is now a named,
decidable predicate, `HasWraparoundTripleRepeat`.

**Step 3 (the open combinatorial core, `EscapeForcesMidRangeRepeat`).** Show that a wraparound-bridged maximal
triple repeat of length `≥ G - L`, together with the existence of an escape,
forces a *shorter* maximal triple repeat inside the band `L - 1 ≤ ℓ < G - L`.
The search data says this is exactly what happens, and it says something
specific about the shape: every escape in the ranges searched is an
"almost-periodic" genome (a long constant or low-period run plus a small defect:
`A^{G-1}B`, `A^aB^b`, `(ABC)^k`-with-one-defect), and the mid-range triple is
always the pair of occurrences inside the run together with the *exposed*
occurrence just before the defect. For the `A`-run family with `L = 3` this is
completely transparent: in `0000001` the copies of `00` at starts `0, 1, 4` are
equal, the preceding symbols are `1, 0, 0` and the following symbols are
`0, 0, 1`, so the triple is maximal at length `2 = L - 1`, while the copy at
start `0` is bridgeable only in the wraparound mode and the copy at start `4` is
not bridgeable at all (no length-`3` read covers both position `3` and position
`6`). Step 3 must be proved for the general shape, not for the `A`-run family;
the `A`-run family is the model, not the argument.

Two weaker-looking intermediate goals that would each suffice, and are stated
here so that partial progress is usable:

* **(H1) long-read rigidity.** If `2L - 1 ≥ G`, then two same-length circular
  words with the same window support have the same spectrum. The search finds no
  escape with `2L - 1 ≥ G` in any range, and this is the classical
  long-read uniqueness regime; combined with Step 2's "escape forces a maximal
  triple repeat of length `≥ L - 1`" it closes the case `G ≤ 2L - 1`, which is
  the regime of the kernel-checked wraparound instances (`AAAAB`, `0000001`).
* **(H2) short repeat from a wraparound triple.** If the truth carries a maximal
  triple repeat of length `e ≥ max (L - 1) (G - L)` and there is an escape, then
  there is a maximal triple repeat of length in `[L - 1, G - L)`. This closes the
  remaining regime `G ≥ 2L`.

## 6. What remains open

* `EscapeForcesMidRangeRepeat` (equivalently `HasMidRangeTripleRepeat`-free
  spectrum rigidity, or the pair (H1)+(H2) above). Until it is proved,
  `informationFeasible_62_spelledML_of_escape_crux` is a theorem *about* the
  wraparound regime, not a proof of the §6.2 maximizer statement in it.
* The generalization of the culprit statement from *candidate-level* escapes (a
  same-support competitor) to `HasSpectralEscape` (arbitrary mass-`G` positive
  circulations of the support) is not formalized; the search only checks the
  candidate-level form. The two differ, since a mass-`G` circulation need not be
  the spectrum of any word.
* Whether the published 2016 sentence is meant with any support-based candidate
  restriction at all remains an interpretation question
  (`docs/source-notes/mb-formulation-referent-reconciliation.md`); the predicate
  of §2 is the literal §6.2 reading, and the note records that reading rather
  than resolving the question.

## 7. Kernel-checked theorem surface

`AssemblyP1.MLEscape`:

| theorem | content |
| --- | --- |
| `HasMidRangeTripleRepeat.longTriple` | a mid-range maximal triple repeat is a long one |
| `informationFeasible_no_midRangeTriple` | full `I_s` excludes the band `L - 1 ≤ ℓ < G - L` |
| `longTripleFree_no_midRangeTriple` | `¬ HasLongTripleRepeat` implies `¬ HasMidRangeTripleRepeat` |
| `Is62SpelledMLMax` | the faithful §6.2 maximizer predicate (membership + dominance) |
| `informationFeasible_62_spelledML_of_no_long_triple` | the audited result in that predicate |
| `observed_mem_support`, `specCount_le`, `factor_eq_one_of_not_mem` | factor-level facts: observation ⊆ support, multiplicity ≤ `G`, factor `1` off support |
| `exactLik_eq_prod_support` | the objective is the product over the truth's window support |
| `exactLik_le_of_spec_le` | pointwise spectral domination ⟹ likelihood inequality |
| `observed_spectral_excess_of_ml_failure` | ML failure ⟹ an observed read type strictly over-counted |
| `IsMassGPositiveCirculation`, `BeatsTruthSpectrum`, `HasSpectralEscape` | the graph-level culprit predicates |
| `HasWraparoundTripleRepeat` | a long triple repeat in the wraparound band `max (L - 1) (G - L) ≤ ℓ < G` |
| `isMaximalTriple_of_mod`, `longTriple_band` | transport to `Fin G` starts, and the split of the long triples into the two bands |
| `spectralEscape_contradiction`, `spectralEscape_gives_longTriple` | **step 1** of the culprit statement |
| `informationFeasible_escape_gives_wraparound`, `informationFeasible_no_escape_of_no_wraparound` | **step 2** of the culprit statement, and its contrapositive |
| `candidate_is_massG_positive_circulation` | a same-support candidate's spectrum is such a circulation |
| `eq_specCount_of_massG_le` | a mass-`G` circulation bounded by the truth's spectrum is the truth's spectrum |
| `ml_failure_gives_spectral_escape` | the §6.2 contrapositive |
| `EscapeForcesMidRangeRepeat` | the culprit statement (**not** proved) |
| `informationFeasible_62_spelledML_of_escape_crux` | the target-shaped theorem, with the culprit statement as its only extra hypothesis |
| `cand0_is_escape`, `truth0_has_midrange_triple`, `culprit_instance_checked` | the non-vacuous kernel-checked instance |

## 8. Reproduction

```
lake build
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML_of_escape_crux
#print axioms AssemblyP1.MLEscape.ml_failure_gives_spectral_escape
#print axioms AssemblyP1.MLEscape.culprit_instance_checked
EOF
python3 scripts/issue88-wraparound-search.py 9 2 7
```

All three `#print axioms` must report only `propext`, `Classical.choice`,
`Quot.sound`.
