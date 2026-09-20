# Issue #36: what the 2016 ML referent is, read off the cited objective and the citing paper's own likelihood

_Status: independent primary-source determination for issue #36, 2026-09-20. This
note adds two things to
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
and
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
which it independently re-verifies: (i) a reading of the word "formulation" from
Medvedev–Brudno's own sentence-level usage, and (ii) a likelihood-matching
argument that identifies which of Medvedev–Brudno's two probability models the
citing paper's own sampling model actually uses. It deliberately does **not**
re-derive the §6.2 graph/flow witnesses or any likelihood arithmetic; those are
covered by [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)
and the witness notes. Every claim is labelled **source fact**,
**source-supported interpretation**, **mathematical fact**, or **source gap**._

## 0. Bottom line

1. The accepted sentence never names an objective, section, or candidate class.
   **No primary source selects a unique referent** (source fact; §2.1).
2. Medvedev–Brudno's §6 opening states, as its own definition of the framework,
   that it "finds the genome that maximizes the global read-count likelihood"
   (source fact; §3.1). That makes the framework **sequence-valued**, and it
   makes the **named objective** the §6.1 exact global read-count likelihood with
   candidate-intrinsic `N(D)` (source fact; §3.2). The fixed-`N`
   product-of-binomials is introduced by MB as an explicit **approximation**, and
   the §6.2 flow is introduced as the **algorithm** (source facts; §3.3–3.4).
3. New discriminator (this note): the citing paper's own probabilistic model is
   i.i.d. uniform draws of length-`L` windows from a length-`G` circular genome
   (source fact; §2.3). The likelihood induced by that model is (up to an
   observation-only multinomial coefficient) **exactly MB09's §6.1 exact
   global read-count likelihood**, normalised by the candidate's own length. It
   is **not** MB09's product-of-binomial marginals (mathematical fact; §4).
4. Consequently the **probability model that matches the citing paper's own
   likelihood is reading (1) (exact multinomial, candidate-intrinsic `N(D)`),
   at least when competitor length is fixed to the paper's `G`.** The
   fixed-`N`/binomial reading (2) describes MB09's computational approximation,
   which neither paper's sampling statement uses (source-supported
   interpretation; §4, §6).
5. The word "formulation" itself does not decide: MB09 say both "we formulate
   the problem … as maximizing the likelihood" and "[t]his problem can be
   formulated as a minimum cost bidirected flow (biflow) problem" (source fact;
   §3.1). So the §6.2 flow is a live *operational* denotation, but it is the
   algorithm/relaxation for the sequence-level objective, not a second objective
   type (interpretation; §5).
6. Net: the most source-faithful reading of "the maximum-likelihood sequence" is
   **the exact read-frequency likelihood of a single candidate sequence**, with
   the §6.2 flow and the fixed-`N` marginals lying one level below it as
   algorithm and approximation. This refines, rather than simply repeats, the
   earlier notes' "best operational fit is reading (2)" ranking. It remains an
   **interpretation**, because the accepted text is silent.

## 1. Independent retrieval and verification

Retrieved this run (2026-09-20) and hashed:

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony et al., author-hosted version + appended supplement | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Howison–Zapata–Dunn (2013) | `https://mark.howison.org/Howison-Bioinformatics-2013.pdf` | `bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935` |
| Bresler–Bresler–Tse (2013), arXiv preprint | `https://arxiv.org/pdf/1301.0068` | `adc32a908ab06d033a778bd75d43eacc0463c4cc4231720684b4b2941cccae59` |
| Medvedev, *Genome Graphs*, PhD thesis (2010) | `https://hdl.handle.net/1807/26297` → bitstream `560c85dc-15e4-4cc3-99ff-ef402f9d1ade` | `97b604706ad288136616917262b3ab7662d5b2b28a4af1a8a2d4b680b3e42a63` |
| Medvedev–Brudno (2009) HTML full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | `f51df69c2da600c2c7d0d9fa562f1b53729680ae84fe11b4fd4e1fa25aff88f6` |

The four stable PDF hashes match the ledger already on `main`. **Provenance
fact.** The PMC HTML hash does not reproduce (this run `f51df6…`, on-`main`
ledger `d52c6e…`, an earlier independent fetch `4ba762…`): the page carries
dynamic markup, so no claim should rest on that hash. All MB09 quotations below
were re-read from this extraction and independently cross-checked against the
2010 thesis, whose text was also retrieved and hashed this run.

DOI verification (Crossref, this run): `btw450` → *Information-optimal genome
assembly via sparse read-overlap graphs*, *Bioinformatics* 32(17) i494–i502;
`btw267` → *Genome assembly from synthetic long read clouds*, same volume
32(12) i216–i224. The `btw267` DOI that appears in the first issue-#36 comment
is the wrong paper; `btw450` is correct, as the on-`main` provenance note already
records.

## 2. Source facts

### 2.1 The citing sentence and its immediate framing (Shomorony et al. 2016, §5)

> "Another direction for future work … is understanding whether, in
> information-feasible instances of the AP, the output of NOT-SO-GREEDY
> coincides with the solution of a combinatorial optimization problem. …
> there is no guarantee that this sequence corresponds to the solution of an
> optimization-based formulation of the AP such as those considered by
> Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As mentioned by
> Medvedev and Brudno (2009), parsimony-based formulations tend to encourage an
> over-collapsing of the repeats … **The maximum-likelihood formulation of the
> AP (Medvedev and Brudno, 2009), on the contrary, seems to be robust to these
> issues, and thus a good candidate for the 'correct' formulation. Understanding
> whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question.**"

Source facts: one paper-level citation; no section/equation/formula; the whole
accepted main text contains no likelihood formula, and `multinomial`/`binomial`
occur zero times. "AP" is the authors' own abbreviation for the Assembly Problem
(Introduction, printed p. i494).

### 2.2 What "these issues" are

Shomorony's "over-collapsing of the repeats" is a direct paraphrase of MB09's
§1.2 problem statement (source fact, §3). The syntactic role of the phrase "the
maximum-likelihood formulation" is therefore the **anti-parsimony object in
MB09's own paper**. That already tells us the referent is whatever MB09 set
against parsimony; §3 fixes which object that is.

### 2.3 The citing paper's own likelihood model

Shomorony et al. 2016, §2 (printed p. i495), verbatim:

> "each of the N reads is drawn independently and uniformly at random from the
> set of length-L substrings of s; `{s[t : t+L−1] : t = 1, …, G}`."

For a candidate string `x`, a single read therefore has probability
`d_x(r)/|x|` under `x`, and the read set's likelihood is
`∏_r (d_x(r)/|x|)` (with an observation-only multinomial coefficient). **Source
fact.** This is the only likelihood the citing paper defines or uses.

### 2.4 Medvedev–Brudno's three levels

**(a) Named objective — exact global read-count likelihood, §6.1.** MB09 §6
begins:

> "In this section, we describe our **maximum likelihood framework** for genome
> assembly, and give an algorithm that, given a set of reads (DNA molecules),
> **finds the genome that maximizes the global read-count likelihood**."

and §6.1:

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the number
> of times the `k`-molecule `i` appears in `D`. … the likelihood of the parameters
> of the distribution `(d_i)` given the outcome of the trials `(x_i)`, which we
> call the **global read-count likelihood** … In our approach, we attempt to
> assemble the genome with the maximum global read-count likelihood. …
> Unfortunately, since the multinomial distribution has the constraint that
> `N(D) = Σ_i d_i`, this [separability] is not possible."

The 2010 thesis gives the objective explicitly:
`L[d_1,…,d_{4^k} | x_1,…,x_{4^k}] = (n!/∏x_i!) ∏_i (d_i/N(D))^{x_i}`, and
repeats the non-separability sentence. **Source fact.**

**(b) Explicit approximation — product of binomial marginals, §6.1.**

> "Because the number of trials … is typically large, we can **approximate** the
> multinomial distribution as the product of the individual binomial
> distributions of each `X_i`. Since in the binomial approximation the length of
> the genome `N(D)` is a constant that is independent of each `d_i`, we can
> replace it by `N`, which is the length of the actual genome … **For our
> experiments, we assume that the genome size is known.**"

Thesis cost: `c_i(d_i) = −(x_i log d_i) − (n − x_i) log(N − d_i)`. **Source
fact.** MB label this an approximation to the exact objective, not a
redefinition of it.

**(c) Algorithm — §6.2 bidirected flow.** "We are now ready to describe our
algorithm for predicting copy counts … [a] convex min-cost biflow … any flow can
be decomposed into a collection of walks, [so] our flow represents a
**(non-contiguous) assembly** of the genome." **Source fact.**

**Consequence (source fact).** MB09 contain exactly three levels: a named
sequence-valued objective, an explicit approximation to it, and an algorithm.
The word "maximum likelihood framework" is used for the §6 enterprise as a
whole, while the *objective* it names is the exact §6.1 likelihood.

### 2.5 Contemporary readers describe the method, not the objective

Howison–Zapata–Dunn (2013), §5, re-read this run (source fact): the
Medvedev–Brudno ML assembler "requires as a parameter the accurate size of the
target genome", contrasted with Varma et al., which "starts from an approximate
size and estimates the actual size during the optimization". Varma–Ranade–Aluru
(2011) title themselves an "improved maximum likelihood formulation", i.e. the
community read genome-size treatment as part of the *method*. **Source fact +
interpretation (see §6.3).**

## 3. Reading the word "formulation"

### 3.1 MB09 use "formulate/formulation" for both the objective and the flow

MB09 §1.2 (source fact):

> "**We formulate the problem of genome assembly as maximizing the likelihood of
> the observed read frequencies**, rather than minimizing the length of the
> genome. **This problem can be formulated as a minimum cost bidirected flow
> (biflow) problem with convex costs** …"

So within a single paragraph MB09 "formulate" both (i) the likelihood objective
and (ii) the biflow that solves its approximation. **Consequence
(interpretation).** The phrase "the maximum-likelihood formulation of the AP"
cannot be disambiguated by the word "formulation" alone; both the objective and
the algorithm are "formulations" in MB09's own vocabulary.

### 3.2 But the sentence's predicate is about the objective

Shomorony says the ML formulation "seems to be robust" to over-collapsing.
"Robust to over-collapsing" is a statistical property of an **objective** (it
must not reward under-representing repeat copies), not of a flow-solver. MB09's
own explanation of that robustness is statistical, in §1.2: "the `k`-mers that
are present more often in the genome are more likely to be sampled … we formulate
the problem … as maximizing the likelihood of the observed read frequencies."
**Interpretation.** The sentence predicates robustness of the objective, which
points to §6.1's read-frequency likelihood (level (a)), with the approximation
(level (b)) as its computable form and the flow (level (c)) as its solver.

### 3.3 Why reading (4) ("broad principle") is disfavoured

The literal "broad principle" reading would make the robustness claim and the
open question nearly content-free. But the sentence does two specific things: it
attributes a definite property to a definite cited formulation, and it asks a
yes/no question about "the maximum-likelihood sequence". A purely unspecified
principle would leave the question undefined rather than merely ambiguous.
**Interpretation.** Reading (4) is the safest *logical* reading only in the
degenerate sense that the accepted text underdetermines the formula; it is not
the best reading of what the sentence is *about*.

## 4. The likelihood-matching argument (new discriminator)

### 4.1 The model match

Compare the three candidate probability models against the one the citing paper
actually uses (§2.3):

| Model | Formula on candidate `x` (reads `r`, counts `x_i` over types `i`) | Used by |
|---|---|---|
| exact multinomial (MB09 §6.1, level (a)) | `(n!/∏x_i!) ∏_i (d_x(i)/|x|)^{x_i}` | MB09 named objective; **Shomorony's own sampling model** |
| product of binomials (MB09 §6.1, level (b)) | `∏_i C(n,x_i) (d_x(i)/N)^{x_i} (1−d_x(i)/N)^{n−x_i}` | MB09 approximation only |
| §6.2 vertex flow cost | same `c_i` as (b) on flow values `d_i` | MB09 algorithm only |

Shomorony's §2 model gives `∏_r (d_x(r)/|x|)`, which — as a function of the
candidate's window counts — is exactly the exact-multinomial factor of §6.1
(the `n!/∏x_i!` coefficient is candidate-independent and does not affect the
argmax). **Mathematical fact.** It is **not** the product of binomial marginals:
the latter treats each type's count as an independent `Bin(n, d_i/N)` variable,
whereas the citing paper draws each read once from the categorical distribution
over windows.

### 4.2 Consequence for which witness matches the referent

If the open question's likelihood is the likelihood of the citing paper's own
model — the only likelihood it defines — then the source-matching objective is
**the exact candidate-intrinsic multinomial (reading 1)**, at least on the
fixed-length slice used by that paper. In the on-`main` witness terms this is the
objective addressed by the **exact (#31) same-length witness**, not the
**binomial (#32) witness**. The #32 witness matches MB09's *approximation*
(level (b)), which is a different statistical object.

**Interpretation (source-supported).** This cuts against an earlier tendency to
regard the binomial witness as the closer analogue of the group's native
same-length likelihood. The binomial is the analogue of MB09's *approximation*;
the multinomial is the analogue of both MB09's named objective and the citing
paper's model.

### 4.3 Candidate-length caveat

The citing paper fixes `|x| = G` (§2.3), whereas MB09's exact objective is
defined for candidate-intrinsic `N(D)` over arbitrary nonempty circular `D`.
The matching is therefore exact on the paper's fixed-length slice and holds for
the unrestricted class only via candidate-set inclusion (the same-length
witnesses lie in the larger class). **Mathematical fact.**

## 5. The consecutive-object caveat

The approximation (level (b)) does **not** simply relabel the exact objective:
it drops the constraint `N(D) = Σ_i d_i` (source fact: the thesis says the
constraint is exactly why the exact objective is not separable, and it is
"replace[d]" after the approximation). Consequently MB09's §6.2 flow is
**not** the fixed-length product-of-binomials over circular genomes; it is that
cost over **flows** with vertex lower bound 1 and flow conservation (source
fact: §6.2). **Interpretation.** So reading (2) and reading (3) should not be
conflated: (2) is a sequence-scoring approximation, (3) is a flow relaxation of
it. The sequence-valued referent, if it is either, is (2)'s objective evaluated
on sequences, not (3)'s feasible set.

## 6. Determination across the four readings

"Refutes ..." statements below are about what would bear on the published
question; no witness arithmetic is repeated here.

| Reading | Verdict from this note |
|---|---|
| (1) exact multinomial, candidate-intrinsic `N(D)` | **Best objective-level match.** It is the objective MB09 *name* ("finds the genome that maximizes the global read-count likelihood") and the objective the citing paper's own sampling model induces. [source-supported interpretation] |
| (2) §6.1 product of binomials, externally fixed `N` | **MB09's stated approximation / implemented method**, matching the "known genome size" descriptions of Howison and Varma. It is a level below (1), and is not the citing paper's likelihood. [source-supported interpretation] |
| (3) §6.2 flow feasible set | **The algorithm/relaxation**, not a second objective type. The sentence's object is a sequence; MB09's flow is a possibly non-contiguous assembly. [source fact + interpretation] |
| (4) broad ML principle | **Disfavoured** as the reading of what the sentence is about, though it remains the logically safest because the accepted text underdetermines the formula. [interpretation] |

**Determination (interpretation, not a source denotation).** The sentence most
faithfully denotes MB09's **read-frequency maximum-likelihood objective for a
single candidate sequence**, whose model in the citing paper's own terms is the
**exact multinomial with candidate-intrinsic normalisation**. MB09's
product-of-binomials and §6.2 flow are the approximation and the algorithm.

This does not overturn the on-`main` conclusion that the accepted text
underdetermines the referent; it supplies a reason to place (1) ahead of (2) as
the *objective-level* referent, where the earlier provenance note placed (2)
ahead on *operational* grounds. Both rankings are about different layers of the
same three-level object.

## 7. Residual choices and settlement status (no witness work)

The genuinely unresolved source choices remain, now with this note's leaning:

1. **Objective vs method.** Does "the maximum-likelihood formulation" name the
   objective (level (a)) or MB09's method (level (b)/(c))? This note argues the
   predicate and the citing paper's likelihood favour the objective; the
   Howison/Varma evidence favours the method as a description of MB09. [source
   gap]
2. **Candidate length / equivalence.** The citing paper fixes `G`; MB09's exact
   objective is intrinsic-length over circular candidates; MB09's biological
   object is a double-stranded molecule. [source gap]
3. **Conclusion semantics.** Truth-is-a-maximizer vs every-maximizer-is-truth,
   and ties. [source gap]
4. **Quantifier/regime.** Per-recorded-read-set vs high-coverage asymptotic.
   [source gap]

Because (1)–(4) are not fixed by the accepted text, any negative settlement must
state its reading explicitly. Under this note's leaning — objective-level,
exact-multinomial, fixed-length/per-instance — the source-matching witness is
the exact same-length one.

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted sentence names no section/equation/objective; no formula in main text | source fact | §5 + full-text scan; §2.1 |
| Citing paper's model is i.i.d. uniform length-`L` windows of a length-`G` circular genome | source fact | §2, p. i495; §2.3 |
| MB09 §6 states the framework finds the genome maximizing the global read-count likelihood | source fact | MB09 §6; thesis §4.4; §2.4 |
| MB09 §6.1 names and defines the exact global read-count likelihood with `N(D)` | source fact | MB09 §6.1; thesis Ch. 4; §2.4 |
| MB09 introduce fixed-`N` binomial marginals as an explicit approximation | source fact | MB09 §6.1; thesis; §2.4 |
| MB09 §6.2 output is a possibly non-contiguous flow | source fact | MB09 §6.2; §2.4 |
| "formulate" in MB09 covers both the objective and the biflow | source fact | MB09 §1.2; §3.1 |
| Citing paper's likelihood equals the exact-multinomial factor (up to a constant) | mathematical fact | §2.3 + §6.1 formula; §4.1 |
| Product-of-binomials is a different objective from the citing paper's likelihood | mathematical fact | §4.1 |
| Objective-level referent is (1); (2)/(3) are approximation/algorithm | source-supported interpretation | §3–§5 |
| Reading (4) disfavoured as the sentence's subject | interpretation | §3.3 |
| Accepted text underdetermines a unique referent | source gap | §2.1, §7 |

## 9. Locators

- I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, "Information-optimal
  genome assembly via sparse read-overlap graphs," *Bioinformatics* 32(17)
  (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`; sampling model printed
  p. i495; open-question paragraph printed p. i501.
- P. Medvedev, M. Brudno, "Maximum Likelihood Genome Assembly," *J. Comput.
  Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`; §1.2, §6.1, §6.2.
- P. Medvedev, *Genome Graphs*, PhD thesis, University of Toronto, 2010,
  Chapter 4 ("Maximum likelihood genome assembly"), §4.3–4.4.
- G. Bresler, M. Bresler, D. Tse, "Optimal assembly for high throughput shotgun
  sequencing," *BMC Bioinformatics* 14(Suppl 5):S18 (2013), arXiv:1301.0068,
  §1–2.
- G. Howison, F. Zapata, C. W. Dunn, "Toward a statistically explicit
  understanding of *de novo* sequence assembly," *Bioinformatics* 29(23) (2013)
  2959–2963, DOI `10.1093/bioinformatics/btt525`, §5.
- A. Varma, A. Ranade, S. Aluru, "An improved maximum likelihood formulation for
  accurate genome assembly," ICCABS 2011, 165–170, DOI
  `10.1109/ICCABS.2011.5729873`.
