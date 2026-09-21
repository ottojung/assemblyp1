# Conclusion semantics of the 2016 ML open question: determination and residual ambiguity

_Status: focused conclusion-semantics audit for issue #36, 2026-09-20, based on
`origin/main` at `6781fec`. It independently re-retrieved the primary sources
(hashes in §1), determines the conclusion semantics on the axes of
maximizer-vs-uniqueness, genome equivalence, candidate length, and ties, and
reconciles the concurrently integrated
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
and
[`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md)
with the existing [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md)
and [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md).
It does **not** select which Medvedev–Brudno likelihood layer the sentence
intends, does **not** settle the published problem, and does **not** invent a
tie or equivalence rule the sources do not state. Every claim is labelled
**source fact**, **mathematical fact**, **source-supported inference**,
**interpretation**, or **source gap**._

## 0. Direct answer

The published sentence —

> “Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question.”

— does **not** by itself fix the conclusion semantics. The determination is:

1. **Maximizer vs uniqueness: not determined by the source.** The sentence
   states no tie rule, no uniqueness theorem, and no equivalence relation. A
   selected maximizer and a unique-up-to-equivalence maximizer are both literal
   readings. [source gap]
2. **Equivalence is not a free parameter.** The exact circular likelihood is
   invariant under cyclic rotation, so the stronger “every maximizer is the
   truth” schema **requires** cyclic shift to be in the equivalence. Reverse
   complement is forced **iff** the read-type space is Medvedev–Brudno’s
   reverse-complement molecule classes; under Shomorony et al.’s oriented
   read-type space it is not. No coarser equivalence has source support.
   [mathematical fact + source-supported inference]
3. **Candidate length: not fixed by the sentence.** The named exact multinomial
   has candidate-intrinsic `N(D)` and no length restriction; the §6.1 binomial
   approximation replaces `N(D)` by an external, known `N`; a leading
   contemporaneous ML-assembly formulation fixes the candidate length and
   justifies it by scale-invariance. The best operational fit is same/fixed
   length, but this is not what the sentence says. [source gap]
4. **Ties are generic and have no rule.** A contemporaneous ML-assembly source
   states that many distinct sequences attain maximum likelihood, so “the
   maximum-likelihood sequence” cannot be assumed unique without an
   equivalence convention. [source fact]
5. **Consequence for witnesses.** A competitor with *strictly* greater
   likelihood refutes both schemas for **every** equivalence and tie
   convention; equivalence and tie choices can only decide the fate of a
   *tied* competitor. The repository’s integrated strict Section 6.2 witnesses
   are of this equivalence-proof kind. [mathematical fact]

| Axis | Determination | Status |
|---|---|---|
| candidate object | single sequence (not a §6.2 flow) | source-supported inference |
| truth a maximizer? | required by the plain reading | interpretation |
| unique maximizer? | **not determined**; no tie/unique clause | source gap |
| cyclic shift in equivalence | **forced** for the strong schema | mathematical fact |
| reverse complement | **forced iff** molecule read types; not in Shomorony theory | mathematical fact + source gap |
| other equivalence | no source support | source fact |
| candidate length | **not determined**; fixed-length is best operational fit | source gap |
| ties | **not determined**; no tie rule; many equal-likelihood optima possible | source gap |

## 1. Independent retrieval and verification

All hashes below were recomputed for this note this run and match the ledger.

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., accepted typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Medvedev–Brudno (2009), published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| Ghodsi, *Constructing a genome assembly that has the maximum likelihood*, arXiv:1302.4391v3 | `https://arxiv.org/pdf/1302.4391` | `6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c` |

The Shomorony and MB09 quotations used below were re-located in the extracted
text of these byte-identical artifacts. [source fact]

## 2. Axis-by-axis determination

### 2.1 The sentence supplies no tie or uniqueness clause

Shomorony et al. (2016), Discussion (accepted typeset p. i501; source fact): the
paragraph contrasts information-feasible reconstruction with optimization
formulations — “there is no guarantee that this sequence corresponds to the
solution of an optimization-based formulation of the AP such as those considered
by Nagarajan and Pop (2009) and Medvedev and Brudno (2009)” — and then states the
open question. It does not define a tie-break, claim the optimum is unique,
quantify over every optimum, or name an equivalence relation. [source fact]

Medvedev–Brudno (2009) are no more explicit: §6.1 says “we attempt to assemble
the genome with the maximum global read-count likelihood”, and the abstract says
the framework assembles the genome that is “the most likely source of the
reads”, with no tie rule or uniqueness theorem. [source fact]

**Determination.** The singular “the maximum-likelihood sequence” cannot
distinguish a selected maximizer from a unique maximizer. Both repository
schemas remain correct to state:
[`../ml-formalization-contract.md`](../ml-formalization-contract.md)
`MaximizerSchema` (`∀ candidate, L(candidate) ≤ L(truth)`) and
`UniqueSchema` (`MaximizerSchema ∧` every tied candidate is equivalent to the
truth). This is the finding of
[`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md).
[source gap]

### 2.2 Cyclic shift is forced for the strong schema

Shomorony et al. work with a circular true sequence “up to cyclic shifts”
(§2 and Theorems 1/Corollary 1). Under the exact circular likelihood the
occurrence multiset of length-`L` windows and the candidate length are
rotation-invariant, hence the likelihood is too. [source fact + mathematical
fact]

**Determination.** If the equivalence does **not** identify some rotation of the
truth with the truth, that rotation is a distinct candidate with equal
likelihood, and the strong schema is false independently of any bridging
hypothesis. So cyclic shift is not an optional modeling nicety: it is
**required** by the strong schema. (The weak schema contains no equivalence and
is unaffected.) See [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
Lemma 1 and Fact 3. [mathematical fact]

### 2.3 Reverse complement is coupled to the read-type convention

Shomorony et al. use oriented length-`L` substrings; reverse complement appears
only as experimental preprocessing (“before running NOT-SO-GREEDY, we preprocess
the set of reads to include each read and its reverse complement”), which *adds*
orientation nodes rather than identifying a read with its reverse complement.
Medvedev–Brudno instead model a read as a DNA *molecule*, “an unordered pair of
strings … that are reverse complements of each other”, and represent “each
`k`-molecule … only once”; §6.1 nonetheless writes “There are `4^k` such
variables”, which counts oriented `k`-mers, not molecule classes — a
source-internal tension. [source fact]

**Determination.** Under molecule read types, a candidate and its reverse
complement always tie, so the strong schema **forces** reverse complement into
the equivalence. Under oriented read types they need not tie in general, so
reverse complement is **not** forced (and is absent from Shomorony’s theory).
The read-type space and the genome equivalence are therefore **one coupled
choice**, not two independent parameters. See
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
Fact 4. [mathematical fact + source-supporting facts]

### 2.4 No other genome equivalence has source support

The only identifications the cited sources describe are Shomorony’s cyclic
shift and Medvedev–Brudno’s reverse-complement molecule convention. Dihedral
(cyclic shift + reverse complement) is therefore the *largest* source-supported
equivalence, under the molecule panel; cyclic-shift-only is the natural
Shomorony panel. No source proposes identifying different-composition words.
[source fact]

### 2.5 Candidate length is not fixed by the sentence

Medvedev–Brudno §6.1 defines the exact likelihood for “a circular genome of
length `N(D)`” with per-type probability `d_i/N(D)` and the constraint
`N(D) = Σ_i d_i`; competitors are not restricted to the true length. The
binomial approximation then “replace[s] it by `N`, which is the length of the
actual genome”, and “we assume that the genome size is known.” Ghodsi
(arXiv:1302.4391v3), a contemporaneous ML-assembly formulation citing MB09 for
the sequencing model, optimizes over a superstring `A` of length `L` and states
“We have to assume that the length of the genome being assembled (denoted by
`L`) is known”, with the Appendix justification that a free `L` is
scale-degenerate. [source fact]

**Determination.** The 2016 sentence does not fix the competitor length. The
literal named exact multinomial admits arbitrary candidate length; the
operative §6.1 method and the contemporaneous community reading fix a known
length. Fixed/same-length is the best operational fit but is not stated by the
sentence, so a fixed-length result is a *restricted* result unless a source
argument fixes the referent. [source gap + interpretation]

### 2.6 Ties have no rule, and uniqueness cannot be assumed

No cited source supplies a tie-break at the open-question sentence. Ghodsi
states of the rounded optimum: “the resulting Eulerian graph may have many
tours, all of which will have equal likelihood. Therefore any final solution
(assembled sequence) is, by itself, only one of many possible solutions.”
[source fact]

**Determination.** An equivalence/tie convention is genuinely needed before
“the ML sequence is the true sequence” has a unique reading; the sentence does
not supply one. [source gap]

### 2.7 Consequence for counterexamples

Write `W` for the weak schema and `S = W ∧ (∀ candidate, L(candidate) =
L(truth) → candidate ≈ truth)`. If some candidate has `L(candidate) >
L(truth)`, then `W` is false, hence `S` is false for **every** `≈`. The
equivalence appears only in `S`’s uniqueness conjunct, reached only by tied
candidates. So a strictly-better competitor is equivalence- and tie-proof,
whereas a *tied* reverse-complement or rotation competitor is decisive only
under the corresponding panel. The integrated strict Section 6.2 witnesses are
of the strict kind; see
[`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md)
and [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md).
[mathematical fact]

## 3. Unresolved register

1. **Maximizer vs uniqueness.** The sentence does not select a schema.
   [source gap; §2.1]
2. **Which read-type space** (and therefore which equivalence) the 2016
   sentence intends. [source gap; §2.3]
3. **Which Medvedev–Brudno ML layer** is the referent (exact multinomial,
   fixed-`N` binomial, §6.2 flow, or a broad principle). [source gap;
   [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)]
4. **Candidate length**, fixed versus free. [source gap; §2.5]
5. **Read-type count** in MB09 §6.1: oriented `4^k` versus `(4^k + p_k)/2`
   molecule classes. [source-internal tension; §2.3]
6. **The accepted supplementary ZIP** remains unretrieved, so a likelihood or
   tie definition there is not excluded. [source gap]

## 4. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The 2016 sentence states no tie rule, uniqueness, or equivalence | source fact | accepted PDF, Discussion p. i501 |
| MB09 §6.1/abstract state no tie rule or uniqueness | source fact | JCB 16(8), §6.1, abstract |
| Shomorony target is `s` up to cyclic shifts | source fact | accepted PDF, §2, Theorems |
| Reverse complement is preprocessing in Shomorony, not an identification | source fact | accepted PDF, §4.1 |
| MB09 reads are reverse-complement molecule pairs, each represented once | source fact | JCB 16(8), §3.1, §4.1 |
| MB09 §6.1 writes `4^k` variables while counting `k`-molecules | source fact / source-internal tension | JCB 16(8), §6.1 |
| MB09 exact multinomial uses candidate-intrinsic `N(D)`; binomial replaces it by external `N` | source fact | JCB 16(8), §6.1 |
| Ghodsi fixes the assembly length to the known genome length | source fact | arXiv:1302.4391v3, §2, Appendix B |
| Ghodsi states many tours have equal likelihood | source fact | arXiv:1302.4391v3, §3 |
| Exact circular likelihood is cyclic-shift invariant | mathematical fact | rotation preserves length and window multiset |
| The strong schema requires cyclic shift in `≈` | mathematical fact | §2.2 |
| Reverse-complement equivalence is forced iff molecule read types are used | mathematical fact | §2.3 |
| A strict competitor refutes both schemas for every `≈` | mathematical fact | §2.7 |
| Which schema, read-type space, length, and ML layer the sentence intends | source gap | §§2, 3 |

## 5. Cross-references

- [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md):
  maximizer-vs-uniqueness source ambiguity.
- [`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md):
  the two invariance lemmas and Facts 3–5.
- [`conclusion-semantics-strict-witness-robustness.md`](conclusion-semantics-strict-witness-robustness.md):
  application to the integrated strict witnesses.
- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
  [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
  [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md):
  the ML referent and candidate class.
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md):
  the two conclusion schemas and the `genomeEquiv`-as-parameter rule.
- [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
  [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md):
  the integrated strict witnesses.
- [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md):
  negative transfer across candidate classes.
- [`conclusion-semantics-equivalence-and-length.md`](conclusion-semantics-equivalence-and-length.md):
  independent sharpening of the equivalence axis (same-spectrum mates tie, so
  the strong schema needs a spectrum-collapsing `≈`; cyclic shift/dihedral are
  necessary but not sufficient in general) and of the length axis (free length
  makes the strong schema false universally by tandem invariance).

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`;
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`;
Mohammadreza Ghodsi, *Constructing a genome assembly that has the maximum
likelihood*, arXiv:1302.4391v3 [cs.CE], 2016.
