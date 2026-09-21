# Issue #48: finite ML is not restored by candidate-intrinsic checks

_Status: reconciled negative result for the issue-#48 repaired formulation.
Exact named witnesses, bounded exhaustive computation, a kernel-checked decisive
instance, and two short paper proofs. This note is an explicitly **additional**
repaired formulation; it is not a reinterpretation of any literature-derived
result. It does **not** settle the source-ambiguous Shomorony et al. question._

_Reproduction: `python3 scripts/verify_issue48_intrinsic_admissibility.py`
(exact `fractions.Fraction` arithmetic) and
`lake build` for [`AssemblyP1/Issue48FreeLengthCounterexample.lean`](../AssemblyP1/Issue48FreeLengthCounterexample.lean)._

---

## 1. The repaired formulation being tested

Issue #48 asks whether the external *true-length* axiom of the same-length
reconstruction theorem can be replaced by **candidate-intrinsic** conditions
that an assembler can check on a candidate sequence itself, while keeping the
finite-data regime. The formulation tested here is:

> **(R)** If the realized read placement `R` satisfies the source
> information-feasibility condition `I_s` for the truth `S`, and `S` is itself
> admitted by a candidate-intrinsic structural predicate, then `S` is
> maximum-likelihood among the candidates of **arbitrary length** admitted by
> that predicate.

`I_s` is the Shomorony et al. (2016) Eq. (1) condition (coverage, all triple
repeats all-bridged, interleaved pairs bridged), with the Bresler et al. (2013)
repeat/triple/interleaving/bridging semantics recorded in
[`bridging-source-semantics.md`](bridging-source-semantics.md): a length-`ℓ`
copy at lifted start `t` is bridged by a read at lifted start `r` iff
`r < t` and `t + ℓ < r + L`.

**Answer: (R) is false, in its strongest intrinsic form.**

## 2. Exact conventions (fixed for every claim below)

- **Model.** Circular true genome `S` of length `G`; error-free reads of common
  length `L ≤ G` at latent start positions; single-strand, oriented reads; no
  reverse-complement collapse. Genome equivalence is cyclic shift. These are the
  Shomorony/Bresler panel conventions.
- **Objective (free candidate length, Variant E).** The exact Medvedev–Brudno
  §6.1 read-count multinomial with candidate-intrinsic length `N(D) = len(D)`
  ([`ml-formalization-contract.md`](ml-formalization-contract.md) Variant E).
  For observed read-type counts `x_w` and candidate window counts `d_D(w)`,

  ```text
  L(D)/L(S) = ∏_{w : x_w > 0} ( G · d_D(w) / ( N(D) · d_S(w) ) )^{x_w},
  ```

  taken as `0` if some observed type is absent from `D`. The observation-only
  multinomial coefficient cancels. The fixed-length variant is the same with
  `G/N(D)` omitted; it is a **different** objective and is named separately
  below.
- **Candidate-intrinsic predicates** (properties of `D` and `L` alone, not of
  `R`):
  - `STRONG(D)`: no `(L−1)`-mer of `D` occurs twice. This is the candidate-only
    shadow of Bresler's "every maximal repeat bridged" condition (it is
    equivalent to "every maximal repeat of `D` has length `≤ L−2`").
  - `WEAK(D)`: every triple repeat of `D` has length `≤ L−2`, and every
    interleaved maximal-repeat pair has a constituent of length `≤ L−2`. This is
    the candidate-only shadow of source `I_s` at the full read set (§4).
  - `primitive(D)`: `D` is not a nontrivial power `w^m`, `m ≥ 2`.
- **Tie/equivalence semantics.** Every refutation below is by a **strict**
  likelihood gap (`L(D) > L(S)`). A strict competitor refutes both the
  "truth is a maximizer" and the "truth is the unique maximizer up to
  equivalence" readings for **every** equivalence relation and tie rule, so no
  equivalence or tie convention needs to be selected.

## 3. The negative witnesses

All entries are exact rational computations. `R` lists latent read starts; the
observed multiset is the corresponding multiset of length-`L` windows.

| # | predicate on truth | truth `S` | `G` | `L` | starts `R` | competitor `D` | `n` | `S` prim | `S` STRONG | `D` prim | `D` STRONG | `I_s(S,R)` | ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `WEAK` | `AAB` | 3 | 2 | `(1,2)` | `AB` | 2 | yes | no | yes | yes | yes | `9/4` |
| 2 | `STRONG` | `AABB` | 4 | 3 | `(0,3)` | `AAB` | 3 | yes | yes | yes | yes | yes | `16/9` |
| 3 | `STRONG` | `AABBC` | 5 | 3 | `(0,3)` | `AABC` | 4 | yes | yes | yes | yes | yes | `25/16` |
| 4 | `WEAK` (non-vacuous `I_s`) | `ABACABC` | 7 | 3 | `(1,1,1,3,6)` | `ABAC` | 4 | yes | no | yes | yes | yes | `16807/4096` |
| 5 | `STRONG` (non-vacuous `I_s`) | `AABACC` | 6 | 3 | `(0,2,5)` | `AABAC` | 5 | yes | yes | yes | yes | yes | `216/125` |

Rows 2, 3 and 5 are the strongest form: the truth itself is primitive and
`STRONG`, so it lies inside the strictest candidate class tested, and the
competitor is primitive and `STRONG` too. Row 4 is the non-vacuous form for the
literal source predicate: `ABACABC` has a bridged length-1 triple repeat
`A@(0,2,4)` and a bridged interleaved pair (a maximal repeat `A@(2,4)` paired
with `CAB@(3,6)`), so `I_s` holds non-trivially; its `STRONG`-admissible
competitor `ABAC` still wins by `16807/4096`. Row 5 is the strongest
non-vacuous form, with a `STRONG`+primitive truth and the same on the
competitor.

**Smallest shape.** A `STRONG` competitor can never strictly beat a truth of
equal length under the fixed-length objective (§5), so a strict free-length win
requires `n ≠ G`; the exhaustive minimum with the truth also `STRONG` is row 2
(`G=4`), and the overall minimum is row 1 (`G=3`, `L=2`, `n=2`). The script's
`--search` mode reproduces this exactly: over alphabets `{A,B}` and `{A,B,C}`,
`G≤6`, `L≤3`, `N≤4`, it finds 240 and 17268 coherent counterexamples with a
`WEAK` truth, and 120 and 11160 when the truth is also required `STRONG`, with
the two minimum shapes above.

## 4. Truth compatibility: `I_s` implies `WEAK`

**Lemma.** If `R ∈ I_s` for truth `S`, then `S` is `WEAK`-admissible.

**Proof.** `I_s` is monotone in `R`: adding reads preserves coverage and can
only turn an unbridged copy into a bridged one. Hence the full read set (one
read at every start) is also in `I_s`. On the full read set a length-`ℓ` copy is
bridgeable iff `ℓ ≤ L−2`, because `r < t` and `t+ℓ < r+L` has an integer
solution `r` exactly then. So the full read set lies in `I_s` iff every triple
repeat has length `≤ L−2` and every interleaved pair has a constituent of length
`≤ L−2`, which is `WEAK(S)`. ∎

Consequently the candidate class of (R) with predicate `WEAK` **contains the
truth**: the refutation is in the coherent regime, not an artifact of excluding
the truth from its own candidate class.

## 5. The complementary positive statement (fixed length + `STRONG`)

**Proposition.** Fix the candidate universe to `STRONG`-admissible genomes of
the true length `G`, scored by the **fixed-length** exact multinomial. Then the
truth is always a maximum-likelihood maximizer. No bridging hypothesis is used.

**Proof.** `STRONG(D)` forbids a repeated `(L−1)`-mer, so an `L`-mer occurring
twice would repeat its `(L−1)`-prefix; hence `d_D(w) ≤ 1` for every `w`. Every
observed `w` has `d_S(w) ≥ 1`, and equal candidate length makes every factor
`d_D(w)/d_S(w) ≤ 1`. Therefore `L(D) ≤ L(S)`. ∎

So `STRONG` is the crossover: sufficient under the true-length axiom,
insufficient without it. This fixed-length statement is a different objective
from the literature-derived same-length bridging theorem and does not replace
it.

## 6. Why the intrinsic checks cannot repair the free-length ranking

`WEAK` and `STRONG` constrain the **fibre** of the map `D ↦ d_D` (identity of a
spectrum and its proportional/tandem scale), not the ranking of candidates that
have **different** spectra. The free-length exact objective rewards the factor
`G/N(D)` together with empirical-frequency fitting. Whenever a shorter
`STRONG`-admissible candidate can carry the observed types with
`d_D(w) = d_S(w) = 1`, the ratio contains `(G/n)^{Σx_w} > 1`. This is
cross-spectrum **length shrinkage**, and it is left untouched by any
candidate-intrinsic repeat condition, because the assembler is not allowed to
know `G`. The checks do remove what they were designed to remove: proportional
`S²`/tandem scale ambiguity and long compressed-run competitors are
`STRONG`-inadmissible. They simply do not address the surviving mechanism.

Consistently with this, the reported unbounded family in the issue thread has
ratio exactly `(G/n)^N` and shows that no worst-case bound uniform in `N` can
hold; its realizations place all reads on a proper subset of the start
positions, so they are exponentially improbable under i.i.d. uniform sampling.
That is a statement about worst-case finite realizations, not about the
population limit.

## 7. What is not established here (explicit non-claims)

- **Unproved identifiability is not used.** The negative result above does
  **not** depend on whether `WEAK` (or any "P2") implies that the `L`-mer
  spectrum determines the genome up to cyclic shift. That implication is a
  separate, **unproved** conjecture; only bounded computational evidence for it
  is reported in the issue thread. No claim in this note asserts it, and the
  refutations are strict finite-likelihood inequalities that hold regardless of
  it.
- No claim for the reverse-complement-collapsed / `k`-molecule panel; on that
  panel uniqueness fails even under `STRONG` (issue thread witness
  `AACAGT`/`AACTGT` at `L=3`), so this note stays on the single-strand oriented
  panel where `I_s` is defined.
- No claim under the fixed-`N` binomial approximation (Variant A) or the
  Section 6.2 flow-feasible set (Variant F). The positive proposition in §5 is
  about the exact fixed-length multinomial, not about either of those.
- This does not settle the published Shomorony et al. question; it refutes one
  explicitly additional free-length repaired formulation.
- Minimality is exhaustive only within the stated bounded ranges; the named
  witnesses are individually exact, and the decisive instance is kernel-checked.

## 8. Diagnosis and handoff

The obstruction is finite sampling plus the free-length normalization, not
residual structural non-identifiability. The natural next repair is therefore
the population / infinite-read regime tracked by issue #45, or a
data-derived length/flow-feasibility bound on candidates. Neither is claimed
here. In particular, the finite negative and any population positive can
coexist: the divergent realizations are exponentially improbable under uniform
sampling, so a population repair would be a typicality statement rather than a
stronger candidate-intrinsic predicate.

## 9. Kernel check

`AssemblyP1/Issue48FreeLengthCounterexample.lean` kernel-checks row 2
(truth `AABB`, competitor `AAB`, `L=3`, starts `0,3`, observed `{AAB, BAA}`).
It proves `Covers truth 3`, `NoTripleRepeat truth`, `Strong truth 3`,
`Strong competitor 3`, `IsPrimitive truth`, `IsPrimitive competitor`, and
`likelihood truth < likelihood competitor` (`1/16 < 1/9`) by finite `decide`
over the instance. The bundled theorem is
`AssemblyP1.Issue48.issue48_free_length_counterexample`. The interleaved
conjunct of `I_s` is vacuous for this instance (the only maximal pairs are
`A@(0,1)` and `B@(2,3)`, whose starts do not alternate); the general
`I_s`/interleaving check for the named witnesses is done by the verification
script.

## 10. Epistemic summary

| Claim | Class | Basis |
|---|---|---|
| `I_s` truth ⇒ `WEAK`-admissible | **Proven** (paper) | monotonicity + full-read reduction |
| Fixed length + `STRONG` ⇒ truth is a maximizer | **Proven** (paper) | counting |
| (R) with `WEAK` universe is false | **Refuted** | row 1 exact, `9/4` |
| (R) with `STRONG`+primitive universe is false | **Refuted** | rows 2/3 exact |
| Non-vacuous `I_s` refutation | **Refuted** | rows 4/5 exact |
| Decisive instance | **Kernel-checked** | `Issue48FreeLengthCounterexample.lean`; `lake build` |
| Other witnesses and bounded exhaustive minimality | **Exact computation** | `scripts/verify_issue48_intrinsic_admissibility.py` |
| `WEAK`/P2 ⇒ spectrum determines genome | **Not claimed / unproved** | issue thread evidence only |
| Failure is cross-spectrum length shrinkage | **Interpretation supported by the witnesses** | §6 |

## 11. Sources and repository anchors

| Item | Source / anchor |
|---|---|
| `I_s` (coverage, all-bridged triples, bridged interleaved) | Shomorony, Kim, Courtade, Tse, *Bioinformatics* 32(17) (2016) i494–i502, Eq. (1); [`bridging-source-semantics.md`](bridging-source-semantics.md) |
| Repeat / triple-repeat / interleaving / bridging semantics | Bresler, Bresler, Tse, *BMC Bioinformatics* 14(Suppl 5):S18 (2013); [`bridging-source-semantics.md`](bridging-source-semantics.md) |
| Exact multinomial with candidate-intrinsic length | Medvedev & Brudno, *J. Comput. Biol.* 16(8) (2009) §6.1; [`ml-formalization-contract.md`](ml-formalization-contract.md) Variant E |
| Prior unrestricted-length exact counterexample | [`exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md) |
| Issue #48 statement and discussion | <https://github.com/ottojung/assemblyp1/issues/48> |
| Kernel check | [`AssemblyP1/Issue48FreeLengthCounterexample.lean`](../AssemblyP1/Issue48FreeLengthCounterexample.lean) |
| Verification script | [`scripts/verify_issue48_intrinsic_admissibility.py`](../scripts/verify_issue48_intrinsic_admissibility.py) |
