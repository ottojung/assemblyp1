# Issue #209 audit: E/A strict counterexamples and hypothesis coverage

_Status: independent audit ledger, 2026-10-09; second verification pass
2026-10-09 (§9b, §11); third verification pass 2026-10-09 (§6, §7, §9b
correction, §9c, §11 defects 3–4). Owner: issue #209
(<https://vau.place/a/antonina/?issue=209>), a leaf of the meta-issue #217.
This document records what the repository's exact-multinomial (Variant E) and
fixed-`N` product-of-binomial-marginals (Variant A) negative results actually
establish, what they do not, the two documentation corrections they forced, and
the script defects and count error found across the three verification passes.

It does **not** re-run the Section 6.2 research programme (another issue owns
that) and it does **not** resolve which Medvedev–Brudno object Shomorony et al.
intended by "the maximum-likelihood formulation of the AP".

Epistemic classes used below are kept distinct:

| class | meaning |
|---|---|
| **kernel-checked** | proved in Lean 4 v4.34 / Mathlib v4.34.0, axiom surface reported in §6 |
| **exact arithmetic** | rational values re-derived from the definitions by an independent implementation (`scripts/verify_issue209_ea_witnesses.py`), no Lean involvement |
| **bounded evidence** | an exhaustive computation over a finite candidate class; complete for that class, not a proof about any larger class |
| **source note** | a reading of a cited paper, asserted in an existing note; not re-verified by this audit |

## 1. The ledger

All instances are error-free reads of common length `L` on a circular genome,
sampled independently and uniformly from the start positions (Shomorony et al.
2016 §2). `n` is the number of reads. `|S| = G` is the true length; `|D|` the
candidate length. "hypothesis" reports the clauses of the full source-faithful
predicate `SourceFaithfulIs.InformationFeasible` that are **non-vacuous**.

| id | truth `S` | `L` | realized starts | observation | competitor `D` | `\|D\|` | objective | `L(S)` | `L(D)` | ratio | hypothesis non-vacuous | status |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| E-1 | `ACGT` | 2 | `0,0,2` | `AC`×2, `GT`×1 | `ACACGT` | 6 | exact multinomial, `N = N(D)` | `3/64` | `1/18` | `32/27` | coverage | kernel-checked |
| E-2 | `AAABB` | 3 | `0,1,4` | `AAA`,`AAB`,`BAA` ×1 | `AAAAB` | 5 | exact multinomial | `6/125` | `12/125` | `2` | coverage + all-bridged triple repeat | kernel-checked |
| E-3 | `AAACC` | 3 | `0,1,4` | `AAA`,`AAC`,`CAA` ×1 | `AAAAC` | 5 | exact multinomial | `6/125` | `12/125` | `2` | coverage + all-bridged triple repeat | kernel-checked (E-2 relabeled) |
| E-4 | `AABB` | 2 | `1,3` | `AB`,`BA` ×1 | `ABAB` | 4 | exact multinomial | `1/8` | `1/2` | `4` | coverage | kernel-checked (coefficient divided out: `1/16`, `1/4`) |
| A-1 | `AAACC` | 3 | `0,1,4` | `AAA`,`AAC`,`CAA` ×1 | `AAAAC` | 5 | binomial marginals, fixed `N = 5` | `452984832/30517578125` | `7962624/244140625` | `1125/512` | coverage + all-bridged triple repeat | kernel-checked |
| **A-2** | `AAABB` | 3 | `0,1,4` | `AAA`,`AAB`,`BAA` ×1 | `AAAAB` | 5 | binomial marginals, fixed `N = 5` | `452984832/30517578125` | `7962624/244140625` | `1125/512` | coverage + all-bridged triple repeat | **kernel-checked, added by this audit** |
| A-3 | `AABB` | 2 | `1,3` | `AB`,`BA` ×1 | `ABAB` | 4 | binomial marginals, fixed `N = 4` | `729/16384` | `1/4` | `4096/729` | coverage | exact arithmetic only |
| A-4 | `ACGT` | 2 | `0,0,2` | `AC`×2, `GT`×1 | `ACACGT` | 6 | binomial marginals, fixed `N = 4` | `177147/16777216` | `1594323/134217728` | `9/8` | coverage | exact arithmetic only, needs the domain caveat of §5 |

Two cross-checks in this table are new relative to the repository notes.

**A-2 (new).** E-2 also refutes the fixed-`N` binomial objective, with the
*same* ratio `1125/512` as A-1, because `AAABB/AAAAB` and `AAACC/AAAAC` differ
only by a renaming of an otherwise unused symbol and the objective is invariant
under symbol renaming. `docs/fixed-length-exact-counterexample.md` claimed the
opposite ("It does **not** refute the Medvedev–Brudno separable/binomial
approximation"); that sentence is corrected in §8. The instance is now
kernel-checked by `AssemblyP1.Issue209EAudit.aaab_refutes_fixed_N_binomial`,
whose likelihood arithmetic is written locally in that module rather than
imported from `FixedLengthBinomialCounterexample`.

**A-3 (new).** The oriented same-length `AABB` witness of issues #88/#211 also
refutes Variant A at ratio `4096/729 > 1`. It is recorded here for completeness
of the E/A ledger; the instance itself belongs to those issues.

## 2. Hypothesis coverage: which clauses of `I_s` are exercised

`I_s` has three clauses (Shomorony et al. 2016 Eq. (1); the repeat semantics are
delegated to Bresler–Bresler–Tse 2013):

1. `R` covers `S`;
2. every triple repeat is all-bridged;
3. every pair of interleaved repeats is bridged.

| id | clause 1 (coverage) | clause 2 (all-bridged triple repeat) | clause 3 (interleaved pairs) |
|---|---|---|---|
| E-1 | non-vacuous (starts `{0,2}`) | vacuous — `ACGT` has **no** maximal repeat of any length | vacuous |
| E-2 / E-3 | non-vacuous (starts `{0,1,4}`) | **non-vacuous** — the `A` copies at starts `0,1,2` are a maximal length-1 triple repeat, bridged by the reads at `4,0,1` respectively | vacuous |
| E-4 | non-vacuous (starts `{1,3}`) | vacuous — two `A`s and two `B`s only | vacuous |

So **clause 3 of `I_s` is vacuous in every E/A witness in the library**. The
refutations rest on coverage plus the all-bridged triple-repeat clause. This is
a genuine hypothesis-coverage gap, not a defect: `I_s` is a *sufficient*
condition, and a witness may leave part of it unexercised. It is recorded here
because a reader must not conclude that the E/A refutation has been tested
against interleaved-repeat bridging. (Whether some other module exercises
clause 3 is outside this issue's scope; the name
`AssemblyP1.InterleavingNeededCounterexample` suggests a related but different
statement and should be reconciled by the owner of the implication lattice.)

Independent confirmation of the census: the audit script re-implements
`IsRepeat`, `IsTripleRepeat`, `BridgesCopy`, `Interleaved`, `Covers` and
`InformationFeasible` from the source definitions and reports, for `AAABB`,
6 maximal repeat *pairs* (3 unordered), 6 maximal *triples* (1 unordered) and
0 interleaved pairs — matching the hand census in
`docs/fixed-length-exact-counterexample.md` and the Lean `decide`.

Note also that the length-2 `AA` repeat at starts `0,1` of `AAABB` is **not**
bridged by the realization (a length-3 read cannot strictly extend a length-2
copy: `bridgesCopy_length` gives `e + 2 ≤ L`), and does not need to be, because
it is not interleaved with any other repeat. The witnesses are therefore
source-faithful rather than incidentally over-constrained.

## 3. Duplicate reads and strict ratios

`Covers`/`BridgesCopy` use the *set* of distinct latent starts; read-type
multiplicity appears only in the likelihood. Duplicating a realized read is
therefore legitimate on both sides of the comparison, and the audit checked the
parametric families.

| family | objective | ratio |
|---|---|---|
| `AAA` observed `k` times, `AAB`, `BAA` once each (`AAABB → AAAAB`) | exact multinomial | `2^k` (verified `k = 1..6`) |
| same observation (`n = k + 2`) | fixed-`N` binomial marginals, `N = 5` | `(1125/512)·(5/2)^(k-1)` (verified `k = 1..6`) |

The `2^k` family is already recorded in
`docs/fixed-length-exact-counterexample.md`; the binomial family is new. All
ratios are strict (`> 1`) for every `k ≥ 1`, so the refutations are not an
artifact of the minimal sample size.

## 4. Binomial zero-count factors

The literal Section 6.1 approximation is a product over the **whole** read-type
space, so unobserved types keep their `(1 - d_w/N)^n` factor
(`docs/fixed-length-binomial-counterexample.md`). The audit recomputed both
readings of A-1/A-2:

| reading of the type space | ratio |
|---|---|
| whole space, zero-count factors retained (the literal objective) | `1125/512` |
| zero-count factors dropped (a different objective) | `9/8` |

Both are `> 1`, so **the refutation is robust to this reading choice; only the
ratio moves.** The factors that differ between truth and competitor are, for
A-1/A-2: the truth carries zero-count factors for two types of multiplicity 1
(`ACC`,`CCA` resp. `ABB`,`BBA`), the competitor for one (`ACA` resp. `ABA`).

## 5. `N` as a parameter versus `|D| = N` as a constraint

This is the distinction the issue asked to be made explicit, and it is where a
correction is needed.

* In `AssemblyP1/FixedLengthBinomialCounterexample.lean` two restrictions are
  simultaneously in force, and they are **different**: (i) the candidate type is
  `Fin 5 → Base`, i.e. every candidate has `|D| = 5`; (ii) the marginal uses
  the fixed external `N = 5`. The module's `IsMaximumLikelihoodFixedLength`
  quantifies only over `|D| = 5`.
* The marginal `Binom(n,x) (d/N)^x (1-d/N)^(n-x)` is a probability only when
  `0 ≤ d/N ≤ 1`. The audit kernel-checks the general bound
  `AssemblyP1.Issue209EAudit.winCount_le_len : d_w ≤ N(D)` and its consequence
  `binomial_marginal_probability_on_le_len : |D| ≤ N → d_w/N ≤ 1`.
* Hence an external fixed `N` is **not** a mere parameter change. Three
  increasingly careful statements:
  1. On the class `|D| ≤ N` the literal objective is automatically a product of
     probabilities, for every candidate, with no further check.
  2. On the unrestricted class of circular candidates it is **not**: the audit
     exhibits the boundary concretely (`external_N_domain_boundary`): for the
     length-6 all-`A` candidate, `d_AAA = 6 > 5 = N`, so the marginal for an
     unobserved type is `(1 - 6/5)^3 = -1/125 < 0`.
  3. There is an intermediate region in between — the candidates satisfying
     `∀ w, d_w ≤ N` — on which the objective is well-defined but where
     `|D| > N` is possible.
* Consequence for A-4: the `ACGT → ACACGT` pair scores `9/8 > 1` under Variant A
  with `N = 4`, and the competitor has `|D| = 6 > N = 4` while still satisfying
  `∀ w, d_w ≤ 4` (its largest multiplicity is `2`). So A-4 is a legitimate
  counterexample for reading 2 if the candidate class is "the region where the
  literal marginal is a probability", but it is **not** a counterexample for the
  class `|D| ≤ N`, and it must not be cited as one without saying which region
  the reading intends. The A-1/A-2 witnesses avoid this entirely: they are
  same-length and hence land inside every one of the three regions.

## 6. Which competitor universes inherit the refutation

Negative results transfer *downward*: a counterexample in a subclass is a
counterexample in any superclass that contains it
(`docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §3).
Positive results do not transfer upward. Applying that to both objectives:

| candidate class | Variant E (exact multinomial) | Variant A (fixed-`N` binomial marginals) |
|---|---|---|
| all nonempty circular candidates | **refuted** (E-1 alone suffices; E-2..E-4 also) | **not a well-posed class**: the objective takes negative values (§5) |
| `\{D : ∀ w, d_w ≤ N\}` (where the marginal is a probability) | refuted (E-2..E-4) | **refuted** (A-1, A-2, A-3, A-4) |
| circular candidates with `\|D\| ≤ N` | refuted (E-2..E-4) | **refuted** (A-1, A-2, A-3; by inclusion from `\|D\| = N`) |
| fixed length `\|D\| = G` | **refuted** (E-2, E-3, E-4) | **refuted** (A-1, A-2) |
| Section 6.2 sequence-level flow-feasible set | **not refuted by these witnesses** | **not refuted by these witnesses** |

The last row is the honest boundary: in each E/A witness at least one of truth,
competitor carries an unobserved length-`L` window — for E-1 both do (`CG`,`TA`
in the truth and `CA`,`CG`,`TA` in the competitor), for E-2/E-3 the competitor
does (`ABA` resp. `ACA`), and for E-4 the **truth** does (`AA`,`BB`) while the
competitor `ABAB` is completely spelled — so no E/A witness places both objects
in the §6.2 feasible set. Which reading of Shomorony et al. is intended remains
open (#208, #217).

For both objectives, the refutation class containing all four E witnesses and
all four A witnesses is `{D : ∀ w, d_w ≤ N} ∩ (candidates whose windows are
unrestricted)`, i.e. the region where the objective is defined at all; the
smallest class that still contains the length-5 witnesses is `|D| = N`, which
is what the Lean modules quantify over. A parent-issue matrix row that says
"all circular candidates" is correct for Variant E only.

## 7. Axiom surfaces and Lean state

Every theorem of the five modules this issue is responsible for has an axiom
surface inside `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no
`native_decide`-style extra axioms. The hand-picked audit of the second pass
listed:

* `ExactVariantECounterexample.finite_unrestricted_exact_variant_e_counterexample`,
  `.truth_information_feasible`, `.truth_not_maximum_likelihood`,
  `.truth_likelihood`, `.competitor_likelihood`, `.competitor_beats_truth`,
  `.realized_reads`, `.truth_covers`;
* `FixedLengthExactCounterexample.fixed_length_exact_counterexample`,
  `.truth_information_feasible`, `.truth_not_maximum_likelihood`,
  `.likelihood_truth`, `.likelihood_competitor`, `.likelihood_ratio`,
  `.realized_reads`, `.truth_covers`;
* `FixedLengthBinomialCounterexample.fixed_length_binomial_counterexample`,
  `.truth_information_feasible`, `.truth_not_maximum_likelihood`,
  `.likelihood_truth`, `.likelihood_competitor`, `.likelihood_ratio`,
  `.likelihood_eq_relevant_prod`, `.realized_reads`, `.truth_covers`;
* `Issue209EAudit.aaab_refutes_fixed_N_binomial`, `.truth_information_feasible`,
  `.truth_not_maximum_likelihood`, `.likelihood_aaab`, `.likelihood_aaaab`,
  `.likelihood_ratio`, `.winCount_le_len`,
   `.binomial_marginal_probability_on_le_len`, `.external_N_domain_boundary`,
   `.likelihood_eq_relevant_prod`, `.realized_reads`, `.competitor_beats_truth`,
and for `SourceFaithfulIs`: `bridgesCopy_length`, `bridgesCopy_lifted_iff`,
`IsTripleRepeatAllBridged.bridgesRepeat`, `Interleaved.swap₂`.

**Re-audited in the second pass** (`scratch-209/axioms3.lean` → 41 names,
includes `FixedLengthExactCounterexample.truth_covers` and
`Issue209EAudit.competitor_beats_truth`, which the first pass's audit file
omitted): all 41 depend only on `[propext, Classical.choice, Quot.sound]`. No
new axiom, no `sorry`, no `native_decide`. The five modules build in isolation
(`lake build AssemblyP1.SourceFaithfulIs AssemblyP1.ExactVariantECounterexample
AssemblyP1.FixedLengthExactCounterexample
AssemblyP1.FixedLengthBinomialCounterexample AssemblyP1.Issue209EAudit` →
"Build completed successfully (8928 jobs)"); see §10.7 for the unrelated
full-library breakage.

**Superseded in the third pass by a complete sweep.** The second pass's file is
a hand-picked list, and the ledger had claimed it covered "42 names" — it covers
**41** (the count was off by one; see §11 defect 4). A complete sweep now
exists: `scripts/audit_issue209_axioms_full.py` parses the namespace stack of
the five modules, emits `#print axioms` for *every* `theorem` they declare, and
checks the report. Its output (`scratch-209/axioms-full.lean`,
`scratch-209/axioms-full-run.log`):

```
reported 116 / 116 theorems
  axiom-free: 11
  on the permitted three: 105
all 116 reported theorems have an axiom surface inside
  ['Classical.choice', 'Quot.sound', 'propext']
```

So every theorem of `SourceFaithfulIs`, `ExactVariantECounterexample`,
`FixedLengthExactCounterexample`, `FixedLengthBinomialCounterexample` and
`Issue209EAudit` has an axiom surface inside `[propext, Classical.choice,
Quot.sound]` — 105 of them on exactly those three, 11 (the pure predicate-logic
lemmas of `SourceFaithfulIs`, e.g. `notAllEq_swap₁`, `Genome.Agree_comm`,
`Interleaved.left_first`) on none. No `sorryAx`, no `native_decide`, no added
axiom, and no definition was weakened to obtain a proof. The sweep is generated
from the sources, so it cannot drift: add a theorem and re-running covers it.

**Re-executed in the third pass.** `lake env lean scratch-209/axioms3.lean`
was run again and reproduces `scratch-209/axioms3-run.log` byte for byte
(41 printed lines for 41 names; `binomial_marginal_probability_on_le_len`
wraps). The five modules still build in isolation ("Build completed
successfully (8928 jobs)"), and both inherited full-library failures of
§10.7 were re-measured: `lake build AssemblyP1.BBTTripleBridge` fails to
elaborate and `lake build AssemblyP1.Issue94Transposition` is killed by the
reaper (`Lean exited with code 137`). No new `sorry`, `admit` or `axiom`.

The shared hypothesis layer `SourceFaithfulIs.bridgesCopy_length` and
`bridgesCopy_lifted_iff` are also clean. The audit module is registered in the
root `AssemblyP1.lean` import list and in its axiom-audit block, so the library
build and CI cover it.

`I_s` membership in every witness module is a single `decide` on the *whole*
`InformationFeasible` predicate (all repeat lengths, all selected starts, both
bridging clauses), not a hand-listed repeat. No proxied bridging predicate is
used anywhere in the E/A chain.

## 8. Corrections issued by this audit

1. **`docs/fixed-length-exact-counterexample.md`**, "What this refutes and what
   it does not": the claim that the `AAABB` witness does **not** refute the
   separable/binomial approximation is wrong under the literal objective
   (ratio `1125/512`, now kernel-checked). Replaced by a precise scope:
   the witness refutes both E and the literal fixed-`N` objective; it still
   does not refute the Section 6.2 flow-feasible class, does not refute the
   *reduced* (zero-count-dropped) objective's ratio claim, and does not resolve
   the source question.
2. **`docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`** §4
   table and epistemic-status table: the reading-2 row said "over **all**
   circular candidates". Corrected to "over circular candidates with
   `|D| ≤ N` (in particular the length-`G` class)", with a pointer to §5 above;
   the `AAABB → AAAAB` row is added for reading 2 with the ratio `1125/512`.

No source fact, witness instance, likelihood value or `I_s` certificate was
changed. No definition was altered to make anything provable.

## 9. Independent recomputation (evidence, not proof)

`scripts/verify_issue209_ea_witnesses.py` shares no code with the Lean
library. It re-implements the circular genome, windows, the full `I_s`
predicate, the exact multinomial likelihood and the literal whole-space
binomial objective, and then checks, per witness: `I_s` membership, that the
realization reproduces the observation, the likelihood values and strict
ratios, the zero-count-factor sensitivity, duplicate-read families, the
`d ≤ N` domain, and the parameter reconstruction of §10.4. All checks pass.

Bounded searches (exhaustive over the stated class, **bounded evidence**):

* E over all `4^5 = 1024` length-5 genomes with the `AAABB` / `AAACC`
  observations, for each of the three objectives (exact E, binomial A with
  zero-count factors retained, binomial A with them dropped): the truth is
  never the maximizer.
* E over all circular genomes up to length 8 in `{A,C,G,T}` for the `ACGT`
  observation: the best value found is `1/18`, attained by `ACACGT`.
* **Maximizer census.** In each complete fixed-length class above, the maximum
  is attained exactly by the cyclic shift class of the *competitor*
  (`AAAAB`,`AAABA`,`AABAA`,`ABAAA`,`BAAAA` for E-2/A-2;
  `AAAAC`,… for E-3/A-1; `ABAB`,`BABA` for E-4). The truth's shift class never
  attains the maximum. This is stronger than "the truth is not a maximizer":
  it says the maximizer, when unique up to cyclic shift, is not the truth up to
  cyclic shift. It is **bounded evidence, not a kernel-checked theorem**.

## 9b. Second-pass re-verification (front #209, reconciliation run)

The audit was re-derived from scratch by a second, independently written
implementation (`scratch-209/independent_recheck.py`, this front; it shares no
code with the audit script and none with the Lean library) after two defects
were found in the audit script itself. Results of the second pass:

| item | second-pass result |
|---|---|
| all likelihood values in the §1 table (E-1..E-4, A-1..A-3) | reproduced exactly, including both zero-count readings |
| full `I_s` on every witness (clauses 1, 2 and 3) | holds; clause 3 vacuous in every one, as §2 records |
| duplicate-read families, `k = 1..6` | `2^k` for Variant E; `(1125/512)(5/2)^(k-1)` for Variant A |
| `d ≤ N` domain; `|D| ≤ N ⇒` product of probabilities; negative marginal for the length-6 all-`A` candidate with `N = 5` | confirmed |
| maximizer censuses over the complete length-5 and length-4 classes | confirmed, at both `N = 4` and `N = 5` |
| `ACGT` observation over all `≤ 8` circular candidates (`{A,C,G,T}`, 87380 objects) | max `1/18`, attained by exactly the six cyclic shifts of `ACACGT` |
| `AAABCBC → AAAAABC` "read-tiled" row (see §10.4) | ratio `27` **is** attained and **is** `I_s`-feasible |

Two things the second pass established that the first pass did not:

* **The fixed-length kernel checks do transfer to the unrestricted Variant E
  statement.** The values `6/125` (`AAABB`) and `12/125` (`AAAAB`) are proved in
  `FixedLengthExactCounterexample` against an objective restricted to
  `Fin 5 → Base`. The second pass recomputed both against the *unrestricted*
  objective (candidate-intrinsic `N(D)`), and they agree, so the
  subclass-to-superclass argument of
  `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §3 is
  verified numerically and not merely asserted. The unrestricted statement
  remains a mathematical transfer argument, not a separate kernel-checked
  theorem.
* **The binomial type space must be the model alphabet, not the candidate's
  symbol set.** The first implementation of the second-pass script scored the
  binomial objective over `sorted(set(cand.symbols)) ^ L`. That is *not*
  equivalent to the literal objective: an observed read type whose symbols do
  not occur in the candidate then silently loses its factor, which is `0`
  when `d_w = 0` and `x_w ≥ 1`. The bug inflated the census maximum
  (`14155776/244140625` at 10 candidates instead of `7962624/244140625` at 5)
  by letting relabelled candidates such as `AAAAC` score the `AAABB`
  observation while ignoring the `AAB`/`BAA` types entirely. Corrected to the
  model's `Fin 3 → Base` space, the second-pass numbers match the Lean
  objective. Recorded here because it is the same class of error as defect 2
  below: an objective quietly evaluated over a different set of read types.

**Correction to this table (third pass).** The first row above read
"all likelihood values in the §1 table (E-1..E-4, A-1..A-4) | reproduced
exactly". That was an overstatement for **A-4**: the second-pass script
evaluated every binomial objective over its single global alphabet
`DNA = "ABCG"`, so the `ACGT`/`ACACGT` row — whose Lean module uses
`DNA = A | C | G | T` — silently lost the `GT` and `TA` factors and produced
`243/4096` and `2187/32768` instead of `177147/16777216` and
`1594323/134217728`. The ratio `9/8` is invariant under that truncation, and
the script only asserted the ratio, so nothing failed. The §1 table's A-4
*values* are correct (they come from the audit script, which sets the alphabet
per section, and from hand arithmetic); what the second pass did **not** do is
reproduce them. See §11, defect 3.

## 10. Remaining blockers (concrete, for the parent matrix)

1. **Clause 3 of `I_s` is unexercised** by every E/A witness (§2). A witness in
   which a maximal interleaved repeat pair is genuinely bridged would close
   this; without one, the E/A refutation speaks only to coverage plus
   all-bridged triple repeats.
2. **The maximizer census of §9 is not kernel-checked.** Formalizing
   "`∀ c : Fin 5 → Base, likelihood c ≤ likelihood AAAAB`" is a 1024-candidate
   exhaustive check of a product over 64 read types; it was not attempted here.
   Until it is, "the ML sequence is a shift of the truth" is refuted for these
   instances only as bounded evidence.
3. **§6.2 feasible-set correspondence** remains open for both objectives, and
   is owned by other issues.
4. **~~The "read-tiled" row is unparameterized.~~ RESOLVED by the second pass
   (§9b).** The row is realizable and the ledger's reconstruction was correct;
   what was missing was that `scripts/verify_issue209_ea_witnesses.py` §F
   could not actually produce it because of defect 1 below. With that fixed,
   the parameters are `L = 3`, observed reads `AAA`×3, `AAB`, `ABC`, `BCA`,
   `CAA` (`n = 7`), distinct starts `{0, 1, 2, 5, 6}` with start `0` used three
   times; the exact-multinomial ratio is `3^3 = 27`, the observation is
   realizable, the starts cover the truth, and the `I_s` certificate holds
   under both implementations. 256 of the 625 ratio-27 observations with
   per-type counts in `0..4` are fully feasible, and 400 give coverage. It is
   still **not kernel-checked** in the Lean library, and it still says nothing
   about the Section 6.2 feasible set; the row in
   `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §4
   remains bounded evidence. What is fixed is that the parameters are now
   recorded and reproducible rather than absent.
5. **Source correspondence of the fixed-`N` reading.** That the approximation is
   a product over the *whole* read-type space, retaining zero-count factors, is
   a repository reading of Medvedev–Brudno §6.1 recorded in
   `docs/fixed-length-binomial-counterexample.md` and
   `docs/source-notes/medvedev-brudno-candidate-class.md`. This audit did not
   re-read the paper; it verified the arithmetic and the scope boundaries, not
   the source sentence. If the parent needs that reading upgraded to
   "source-verified", a fresh primary-source read is required (see §4 of this
   document for which readings were tested).
6. **Which objective the published sentence denotes** is unresolved, and no
   worker's summary changes that. The aggregate claim of #217 may state that
   every *objective-and-candidate-class* pair with a defensible reading has been
   resolved, but not that the 2016 question is settled.
7. **The full-library `lake build` is red for reasons outside this issue.**
   `AssemblyP1/BBTTripleBridge.lean` fails to elaborate at HEAD (17 errors,
   first at line 81) and `AssemblyP1/Issue94Transposition.lean` is killed by
   the OOM reaper (`Lean exited with code 137`). Neither file is touched by
   this front's commits and `git diff origin/main..HEAD` for this issue does
   not include them, so both failures are inherited from `origin/main`. Every
   module this front is responsible for —
   `SourceFaithfulIs`, `ExactVariantECounterexample`,
   `FixedLengthExactCounterexample`, `FixedLengthBinomialCounterexample`,
    `Issue209EAudit` — builds clean (`lake build <those modules>` → "Build
    completed successfully"), and all 116 theorems of those modules have an
    axiom surface inside `[propext, Classical.choice, Quot.sound]` (§7). A
    parent that needs one green `lake build` must repair `BBTTripleBridge`
    first; that is not an E/A blocker.

## 11. Defects found and fixed in this front

Defects 1–3 are in verification scripts; defect 4 is a wrong count in this
ledger's own description of the axiom audit. None of them changes any theorem,
witness instance, likelihood value or `I_s` certificate, and no definition was
altered to make anything provable.

1. **§F inherited a read length of 2.** Section E2(b) sets the read length to
   `2` and section F never resets it, so `exact_likelihood` in section F looked
   up length-3 read types among a candidate's *length-2* windows. Every
   multiplicity was `0`, every likelihood `0`, and the section reported
   "observations with ratio 27: 0", contradicting the ledger's own §10.4
   reconstruction. With `set_read_length(3)` restored, §F reports 625 ratio-27
   observations, 256 of them fully feasible. The script's own text was the
   authority for the §10.4 claim it failed to reproduce; the claim was right
   and the script was wrong.
2. **§G's `N = 4` census row was evaluated at `N = 5`.** The objective was a
   single hard-coded lambda `binomial_likelihood(c, ob, 5)`, so the row
   labelled `binomial A (N=4), AB/BA obs` reported the *N = 5* numbers
   (truth `16384/390625`, maximum `144/625` at `ABAB`,`BABA`). The row now
   passes `N` explicitly and two rows are printed: at `N = 4`, truth
   `729/16384` and maximum `1/4` at `ABAB`,`BABA` (ratio `4096/729`, matching
   §1's A-3); at `N = 5`, truth `16384/390625` and maximum `144/625`. The
   qualitative conclusion was unaffected — the truth is not a maximizer either
   way — so this was a reporting defect, not a mathematical one.
3. **(third pass) the second-pass script's `alpha` argument was dead, so A-4's
   binomial *values* were computed over the wrong type space.**
   `scratch-209/independent_recheck.py` called `witness(..., alpha="ACGT")`
   for E-1/A-4, but `witness` accepted `alpha` and never used it, and
   `L_A` iterated over the global `DNA = "ABCG"` — the alphabet of the
   *fixed-length* modules, not of `ExactVariantECounterexample`, whose
   `DNA = A | C | G | T`. Both alphabets have four letters, so the two
   objectives differ while every ratio is unchanged; the `GT`/`TA` factors of
   an unobserved type are dropped and the A-4 values came out `243/4096` and
   `2187/32768` instead of `177147/16777216` and `1594323/134217728`
   (§1's A-4 row, which is correct). Because the script asserted only
   strictness of the ratio, nothing failed and the §9b table claimed the A-4
   values had been "reproduced exactly" — see the correction there.
   Fixed in this front by threading `alpha` through `L_A`/`witness` and by
   asserting the ledger's E-row oracle values as well. The third-pass script
   (`scripts/verify_issue209_ea_witnesses_third_pass.py`) asserts every value of
   §1 against an oracle transcribed from the Lean theorems, and carries an
   explicit sensitivity check that exhibits the ratio-invariance trap.
4. **(third pass) the axiom audit's own theorem count was off by one.** §7
   reported that `scratch-209/axioms3.lean` audited "42 names". The file
   contains 41 `#print axioms` lines, and the run log prints 41 reports. The
   claim understated coverage rather than overstating it — every audited name
   was indeed clean — but a parent quoting "42 theorems checked" would be
   quoting a number that no artifact supports. Corrected, and superseded by the
   complete sweep of §7, which covers all 116 theorems of the five modules
   (`scripts/audit_issue209_axioms_full.py` → `scratch-209/axioms-full.lean`,
   `scratch-209/axioms-full-run.log`; 105 on the permitted three axioms, 11
   axiom-free).

## 9c. Third-pass re-verification (front #209, terminal pass)

A third implementation, `scripts/verify_issue209_ea_witnesses_third_pass.py`, was
written from scratch for this pass: it shares no code with the audit script or
with the second-pass script, and it re-derives every quantity against an
oracle of expected values transcribed from the Lean theorems named in each
witness row. 91 checks, all passing. Beyond reproducing §9b it

* reproduces **every** likelihood value in §1, A-4 included, and asserts each
  against the Lean/exact-arithmetic oracle;
* re-implements `I_s` from the source definitions with its own repeat,
  triple-repeat, interleaving and bridging code, and confirms clause 3 is
  vacuous in all four witnesses and clause 2 non-vacuous exactly for
  E-2/E-3;
* confirms the maximizer censuses, including that the maximizer set in each
  complete class is exactly the competitor's cyclic-shift class and never the
  truth's, and that the `≤ 8` `ACGT` class has 87380 objects with a unique
  (up to shift) maximizer `ACACGT` at `1/18`;
* confirms the read-tiled row's parameters and the 625/256/400 counts;
* exhibits the alphabet sensitivity of §11 defect 3 as a live check.

Class of this script's output: **exact arithmetic** and **bounded evidence**.

Primary sources relied on (unchanged by this audit):

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  *Information-optimal genome assembly via sparse read-overlap graphs*,
  Bioinformatics 32(17) (2016) i494–i502, §2 and §5, DOI
  10.1093/bioinformatics/btw450.
- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*, J.
  Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, DOI
  10.1089/cmb.2009.0047.
- Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high
  throughput shotgun sequencing*, BMC Bioinformatics 14(Suppl 5):S18 (2013),
  DOI 10.1186/1471-2105-14-S5-S18 (repeat/interleaving/bridging definitions).
