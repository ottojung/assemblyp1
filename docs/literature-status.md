# Literature status: bridging conditions and maximum-likelihood assembly

_Status checked: 2026-09-17_

This document records a literature search for the open question described in
[`open-problem.md`](open-problem.md): whether the repeat-bridging conditions used
for information-feasible shotgun assembly guarantee that the true genome is a
maximum-likelihood genome under the maximum-likelihood formulation referenced by
Shomorony, Kim, Courtade, and Tse (2016).

## Executive conclusion

**I did not locate a published resolution of the exact 2016 open question.** In
particular, I did not find a paper proving that the Shomorony et al. bridging
conditions imply that the true sequence maximizes the Medvedev--Brudno
read-count likelihood, nor did I find a published counterexample showing that
those conditions can hold while another candidate genome has strictly greater
likelihood.

This is a literature-search conclusion, not a proof of absence. The search was
fairly broad: it used the exact wording of the open question, the title and DOI
of the 2016 paper, combinations of `bridging`, `interleaved repeat`, `triple
repeat`, `maximum likelihood`, `genome assembly`, and `identifiability`, later
work by the same authors, likelihood-based assembly literature, safe/complete
assembly literature, and recent papers and surveys through September 2026.
Scholarly search systems are not exhaustive, and papers can use different
terminology. The right status for this repository is therefore:

> **No resolution found as of 2026-09-17; the problem appears to remain open.**

An independent citation-graph search on 2026-09-19 reached the same conclusion by
intersecting the forward-citation sets of Shomorony et al. (2016), Medvedev–Brudno
(2009), and Bresler–Bresler–Tse (2013); the only works citing both the bridging and
ML lines are safe-and-complete papers and SAMA 2025. See
[`literature-search-citation-graph-2026-09-19.md`](literature-search-citation-graph-2026-09-19.md)
for the method, the exact intersections, and newly recorded adjacent citations.

A further independent search on 2026-09-20 of the 2016 authors' own post-2016 output found that the
Shomorony group continued the **identifiability / flow-decomposition** line (information-optimal
multi-sample flow decomposition; sharp thresholds for reconstruction from substring sets) without
addressing the maximum-likelihood question. See
[`literature/shomorony-group-post2016-identifiability-2026-09-20.md`](literature/shomorony-group-post2016-identifiability-2026-09-20.md).

A targeted search on 2026-09-20 of the **substring-spectrum reconstruction** literature found that
the combinatorial half of the question — whether the complete `L`-mer spectrum determines the
genome — is an old, fully characterized problem (Ukkonen 1992 conjecture; Pevzner 1995 proof),
restated with an explicit necessary-and-sufficient theorem in Çelikkanat et al., NeurIPS 2024,
Theorem 3.1. That characterization appears to coincide with the repository's Conjecture 4
(`I_s`-admissibility ⇒ spectrum uniqueness). This **relocates the open content to the statistical
layer**: a finite random sample need not rank the true spectrum first, even when the spectrum
determines the genome. See
[`literature/substring-spectrum-identifiability-2026-09-20.md`](literature/substring-spectrum-identifiability-2026-09-20.md).

A further targeted search on 2026-09-20 of the **post-2009 likelihood-assembly** literature found a
previously unrecorded primary source that *proves* the "truth is a maximizer" direction for the
Medvedev–Brudno fixed-length read-count objective: Ghodsi, Hill, Astrovskaya, Lin, Sommer, Koren,
Pop, *BMC Research Notes* 6:334, 2013 (`10.1186/1756-0500-6-334`). Their proof gives the KL identity
`Σ_s q_s log p_s = −D_KL(Q‖P) − H(Q)`, so the maximizer set is exactly the candidates whose induced
read-type distribution equals the observed one, and the true genome is a maximizer precisely when the
observed distribution equals the true spectrum. The same paper explicitly notes equal-likelihood
non-true optima can exist. This sharpens the tie semantics and shows the "truth-is-a-maximizer"
property is an empirical-spectrum-equality statement, not a consequence of repeat bridging alone, in
the unrestricted finite-sample exact objective. It does not settle the 2016 implication. See
[`literature/ghodsi-2013-truth-maximizes-2026-09-20.md`](literature/ghodsi-2013-truth-maximizes-2026-09-20.md).

There is substantial adjacent theory. The closest result is actually older than
the 2016 question: Bresler, Bresler, and Tse (2013) prove a likelihood-based
**necessary** condition. If a problematic interleaved pair or triple repeat has
all of its copies unbridged, there is another genome of the same length under
which the observed reads have the same likelihood. Shomorony et al. later give
stronger bridging conditions sufficient for exact reconstruction by their
Not-So-Greedy algorithm, and then explicitly ask whether those conditions also
suffice for the maximum-likelihood objective. The missing implication is exactly
the gap this repository is targeting.

A useful modern checkpoint is Salmela's 2025 paper *Sama: a contig assembler
with correctness guarantee*. Its related-work discussion still presents
information/correctness results (including Shomorony et al. 2016) and
maximum-likelihood/probabilistic formulations (including Medvedev--Brudno and
GAML) as separate lines of work. It does not cite a theorem joining them. That
is meaningful evidence that the 2016 question had not become a standard solved
result by 2025, though it is not by itself conclusive.

## 1. The exact target question

The source is:

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  **"Information-optimal genome assembly via sparse read-overlap graphs,"**
  *Bioinformatics* 32(17), 2016, i494--i502.
  DOI: <https://doi.org/10.1093/bioinformatics/btw450>

Near the end of the paper the authors write:

> "Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question."

The paper's information-feasible set \(\mathcal I_s\) requires, in addition to
coverage of the true circular genome \(s\), that:

1. triple repeats in \(s\) are **all-bridged**; and
2. interleaved repeats in \(s\) are **bridged**.

Under these hypotheses, their construction can be reduced to a graph with a
unique Eulerian cycle spelling the true sequence up to cyclic shift. This is an
algorithmic reconstruction theorem, not an optimization theorem about arbitrary
candidate genomes.

The maximum-likelihood formulation named in the discussion is:

- Paul Medvedev and Michael Brudno, **"Maximum Likelihood Genome Assembly,"**
  *Journal of Computational Biology* 16(8), 2009, 1101--1116.
  DOI: <https://doi.org/10.1089/cmb.2009.0047>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>

For a circular candidate genome \(D\) of length \(N(D)\), let \(d_i\) be the
number of occurrences in \(D\) of read/k-molecule type \(i\), and let \(x_i\)
be its observed count among \(n\) sampled reads. Under uniform independent
sampling, the exact global read-count likelihood is multinomial, with read-type
probabilities \(d_i/N(D)\):

\[
L(D\mid x) = \frac{n!}{\prod_i x_i!}
             \prod_i \left(\frac{d_i}{N(D)}\right)^{x_i}.
\]

Medvedev and Brudno then introduce a binomial/separable approximation in order
to solve a tractable convex min-cost flow problem. This distinction matters to
the formal statement: "the Medvedev--Brudno maximum-likelihood formulation" can
refer either to the exact global multinomial likelihood or to an optimization
approximation used by their algorithm. The 2016 discussion does not, in the
sentence containing the open question, spell out which level is intended.

There is a second ambiguity: the sentence says "the maximum-likelihood sequence
is the true sequence." Formally this could mean either:

- the true genome is **a** maximum-likelihood genome; or
- every maximum-likelihood genome is equivalent to the true genome (uniqueness,
  presumably up to the genome equivalence chosen in the model).

These are different statements whenever the likelihood has ties.

Accordingly, a paper should count as a resolution for this project only if its
theorem can genuinely be translated into one of those implications under a
source-faithful model, rather than merely showing that some assembler succeeds
under bridging conditions or that likelihood is useful empirically.

## 2. Search strategy

The search was performed in several overlapping directions.

### 2.1 Exact-statement and citation-oriented searches

Searches included:

- the exact sentence "bridging conditions ... maximum-likelihood sequence ...
  true sequence";
- the exact title of the 2016 paper together with `maximum likelihood`,
  `bridging`, `proof`, `counterexample`, and later years;
- DOI `10.1093/bioinformatics/btw450` with later-year and assembly-theory terms;
- the names Shomorony, Kim, Courtade, and Tse together with maximum-likelihood
  assembly terms;
- searches restricted to recent material (2025--2026).

The exact-statement searches repeatedly returned the original 2016 paper rather
than a later paper announcing a resolution.

### 2.2 Terminology searches

Because later authors need not repeat the wording of the question, searches also
covered combinations of:

- `bridged repeat`, `unbridged repeat`, `interleaved repeat`, `triple repeat`;
- `likelihood`, `maximum likelihood`, `read-count likelihood`, `generative
  model`;
- `identifiability`, `unique reconstruction`, `information feasibility`,
  `complete reconstruction`;
- `safe assembly`, `complete assembly`, `omnitig`, `misassembly probability`;
- `copy count`, `multiplicity`, `de Bruijn graph`, and `overlap graph`.

### 2.3 Adjacent research lines checked

The search explicitly examined:

- the Bresler--Bresler--Tse information-theoretic line preceding Shomorony et
  al.;
- later repeat-resolution work by overlapping authors, notably HINGE;
- improvements and applications of maximum-likelihood assembly (Varma--Ranade--
  Aluru, CGAL, GAML, SWALO);
- Bayesian/probabilistic assembly;
- safe-and-complete assembly via omnitigs and later graph-theoretic work;
- recent correctness-guarantee assembly, notably SAMA (2025);
- recent theoretical/survey writing on assembly.

The point of this wider sweep was to avoid the false conclusion that the problem
is open merely because nobody reused the 2016 paper's exact vocabulary.

## 3. Closest result: unbridged repeats imply an equal-likelihood competitor

The most directly relevant established theorem is:

- Guy Bresler, Ma'ayan Bresler, and David Tse,
  **"Optimal assembly for high throughput shotgun sequencing,"**
  *BMC Bioinformatics* 14(Suppl 5):S18, 2013.
  DOI: <https://doi.org/10.1186/1471-2105-14-S5-S18>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/>

Their Theorem 1 states, in the paper's terminology, that if there is a pair of
interleaved repeats or a triple repeat whose copies are all unbridged, then
there is another sequence \(s'\) of the same length under which the likelihood
of observing the reads is the same.

This result is unusually close to the target because it already talks about
**likelihood**, not merely graph ambiguity. It establishes a concrete
non-identifiability mechanism:

\[
\text{certain unbridged-repeat pattern}
\quad\Longrightarrow\quad
\exists s'\ne s\;:\;L(s'\mid R)=L(s\mid R).
\]

It therefore supplies a necessary condition for unambiguous reconstruction.
But it does **not** prove the desired direction

\[
R\in\mathcal I_s
\quad\Longrightarrow\quad
L(s\mid R)\ge L(D\mid R)\quad\text{for every candidate }D.
\]

Nor does it exclude a candidate with *higher* likelihood after the problematic
repeat ambiguities have been bridged.

There is also a notable gap between the necessary and sufficient repeat
conditions around triple repeats. The lower-bound ambiguity theorem only needs
a triple repeat to be "bridged" in the weak sense that at least one copy is
bridged in order to avoid that particular all-unbridged obstruction. The
MultiBridging/Not-So-Greedy sufficiency conditions require triple repeats to be
**all-bridged**. Thus there is room between known impossibility and known
algorithmic sufficiency even before maximum likelihood enters the story.

For this repository, the Bresler theorem is likely worth formalizing as an
adjacent theorem. It would validate the repeat and likelihood definitions and
would put a kernel-checked boundary immediately next to the open implication.

## 4. What the 2016 result proves, and why it does not settle maximum likelihood

Shomorony et al. prove that when the read set belongs to their
information-feasible set \(\mathcal I_s\), their Not-So-Greedy construction can
produce an overlap multigraph with a unique Eulerian cycle spelling \(s\) up to
cyclic shift.

That is stronger than merely saying a heuristic often works. It is an exact
reconstruction guarantee. Nevertheless, it does not compare the likelihood of
\(s\) to the likelihood of **every arbitrary competing genome**.

This distinction is fundamental:

- an assembly algorithm can use the placement/context information encoded by
  bridging to recover the truth;
- a likelihood objective scores a candidate by how probable the observed read
  multiplicities are under that candidate;
- a competitor considered by the likelihood optimization need not itself obey
  the true genome's bridging conditions.

So unique recovery by a particular graph construction does not automatically
imply global optimality under a separate statistical objective. The 2016
authors explicitly recognize this distinction in the Discussion when they
contrast optimization formulations with information-feasible reconstruction
and leave the maximum-likelihood connection open.

## 5. Later work by overlapping authors: HINGE does not close the gap

A particularly important paper to check is:

- Govinda M. Kamath, Ilan Shomorony, Fei Xia, Thomas A. Courtade, and David N.
  Tse, **"HINGE: long-read assembly achieves optimal repeat resolution,"**
  *Genome Research* 27(5), 2017, 747--756.
  DOI: <https://doi.org/10.1101/gr.216465.116>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC5411769/>

This is especially relevant because Shomorony, Courtade, and Tse are authors on
both papers and HINGE directly develops the bridged/unbridged-repeat viewpoint.
HINGE aims for a maximally resolved assembly graph: repeats that can be resolved
from the reads are separated, while unresolvable repeats remain collapsed. When
a unique finished assembly is not justified, the graph represents alternative
finished assemblies instead of arbitrarily selecting one.

HINGE is therefore strong evidence that the bridging framework remained active
after 2016. But it does not prove that the true genome is the maximizer of the
Medvedev--Brudno likelihood, and its main theorem/algorithmic objective is
repeat resolution rather than global maximum-likelihood optimality. I found no
maximum-likelihood resolution of the 2016 question in this paper.

## 6. Likelihood-based assembly results adjacent to the conjecture

A second cluster of work develops likelihood objectives themselves. These
papers are important because they clarify what an ML formalization can mean and
show that likelihood is useful in practice, but they do not derive ML
correctness from the Shomorony bridging conditions.

### 6.1 Medvedev--Brudno (2009): the foundational ML objective

Medvedev and Brudno replace the usual shortest/parsimonious assembly objective
with the genome most likely to have generated the observed reads. Their exact
read-count model is multinomial. They then need an approximation to obtain a
separable convex objective for bidirected network flow and use the resulting
method to estimate repeat copy counts.

Two details are especially important for `assemblyp1`:

1. the paper explicitly models double-stranded DNA using bidirected graphs,
   while the Shomorony exposition uses a circular sequence and cyclic shifts;
2. the exact global likelihood contains the candidate length \(N(D)\), whereas
   the tractable approximation uses additional assumptions/approximations,
   including a fixed or estimated genome length.

A proof about the approximation would not automatically be a proof about the
exact multinomial objective, and vice versa.

### 6.2 Varma--Ranade--Aluru (2011): improved ML formulation

- Aditya Varma, Abhiram Ranade, and Srinivas Aluru,
  **"An Improved Maximum Likelihood Formulation for Accurate Genome Assembly,"**
  ICCABS 2011.
  DOI: <https://doi.org/10.1109/ICCABS.2011.5729873>

This work reformulates the optimization directly as convex optimization,
supports varying read lengths, and weakens the requirement for an exact a priori
genome-length estimate by allowing a range. It is relevant to the modeling
question of candidate length, but it predates the 2016 open question and does
not prove a bridging-implies-ML theorem.

### 6.3 CGAL (2013): computing assembly likelihoods

- Atif Rahman and Lior Pachter,
  **"CGAL: computing genome assembly likelihoods,"**
  *Genome Biology* 14:R8, 2013.
  DOI: <https://doi.org/10.1186/gb-2013-14-1-r8>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3663106/>

CGAL gives a practical generative likelihood model incorporating fragment
lengths, start-site probabilities, sequencing error, and unmapped data, and
uses likelihood as an assembly-evaluation criterion. This broadens the
probabilistic model far beyond the error-free uniform-read abstraction of the
open question. It does not establish that bridging conditions force the true
sequence to maximize either its own richer likelihood or the 2009 read-count
likelihood.

### 6.4 Bayesian genome assembly (2014)

- Mark Howison, Felipe Zapata, Erika J. Edwards, and Casey W. Dunn,
  **"Bayesian Genome Assembly and Assessment by Markov Chain Monte Carlo
  Sampling,"** *PLoS ONE* 9(6), 2014, e99497.
  DOI: <https://doi.org/10.1371/journal.pone.0099497>

This work samples a posterior distribution over assembly hypotheses instead of
selecting one point estimate. It is conceptually adjacent because it makes
assembly uncertainty explicit, but it answers a different question and was
illustrated on a small bacteriophage genome.

### 6.5 GAML (2015)

- Vladimír Boža, Broňa Brejová, and Tomáš Vinař,
  **"GAML: genome assembly by maximum likelihood,"**
  *Algorithms for Molecular Biology* 10, 2015.
  DOI: <https://doi.org/10.1186/s13015-015-0052-6>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC4454275/>

GAML searches for a high-likelihood assembly under probabilistic models that can
combine diverse sequencing datasets, including sequencing errors and insert
lengths. Its search is practical/heuristic (simulated annealing over an assembly
space) rather than a theorem that the true genome must be the ML solution when
bridging conditions hold. It predates the 2016 statement as well.

### 6.6 SWALO (2021)

- Atif Rahman and collaborators,
  **"SWALO: scaffolding with assembly likelihood optimization,"**
  *Nucleic Acids Research* 49(20), 2021, e117.
  DOI: <https://doi.org/10.1093/nar/gkab717>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC8599790/>

SWALO uses a generative model to estimate gap lengths and decide whether joins
increase assembly likelihood. The authors describe it as a step toward
maximum-likelihood genome assembly. It operates at the scaffolding/joining
level and uses approximations and heuristics; it does not prove the bridging
conjecture.

Taken together, these works show continued interest in likelihood as an
assembly objective but no theorem located in this search connecting the
specific Shomorony bridging hypotheses to global ML optimality.

## 7. Dense-read / spectrum identifiability results

A separate classical line gives much stronger uniqueness statements when one
observes a complete substring spectrum rather than a finite random shotgun
sample.

The Ukkonen/Pevzner theory characterizes ambiguity caused by interleaved and
triple repeats. In the noiseless spectrum setting, once the read/k-mer length
exceeds the critical repeat length, the sequence is uniquely reconstructible;
below the critical length another sequence can have the same spectrum.
Bresler--Bresler--Tse can be viewed as extending this style of reasoning from a
complete spectrum to randomly sampled shotgun reads by introducing bridging.

These results are highly relevant conceptually because, for a complete exact
spectrum, candidate genomes can be constrained very strongly by substring
multiplicities. But the conjecture concerns a finite random sample, where the
empirical counts can fluctuate away from the true genome's exact substring
frequencies. Therefore spectrum uniqueness cannot simply be substituted for a
proof of ML optimality.

For `assemblyp1`, restricted cases in which the observed sample is the complete
\(L\)-spectrum (possibly with controlled multiplicity) may be useful stepping
stones: they remove sampling fluctuations and could reveal which part of the
conjecture is genuinely statistical rather than combinatorial.

## 8. Safe-and-complete assembly is related but logically different

Another important theoretical line asks which contigs can be output safely from
an assembly graph.

- Alexandru I. Tomescu and Paul Medvedev,
  **"Safe and complete contig assembly via omnitigs,"** RECOMB 2016.
  Preprint: <https://arxiv.org/abs/1601.02932>

Omnitigs characterize strings that occur in every genome represented by an
assembly graph and give a polynomial algorithm to enumerate safe contigs. Later
work develops the safe-and-complete framework further and investigates when
common graph objects such as unitigs are unsafe or incomplete.

For example:

- Amatur Rahman and Paul Medvedev,
  **"Assembler artifacts include misassembly because of unsafe unitigs and
  underassembly because of bidirected graphs,"** *Genome Research* 32, 2022,
  1746--1753.
  DOI: <https://doi.org/10.1101/gr.276601.122>

This theory provides precise correctness guarantees over a graph-defined set of
possible genomes. But "appears in every genome consistent with this graph" is
not the same predicate as "belongs to the genome of greatest probability under
a read-generating model." Safe assembly therefore gives useful proof patterns
and definitions of ambiguity but does not settle the ML question.

## 9. A recent status checkpoint: SAMA (2025)

The most useful recent paper found for checking the state of the field is:

- Leena Salmela,
  **"Sama: a contig assembler with correctness guarantee,"**
  *Algorithms for Molecular Biology* 20:9, 2025.
  DOI: <https://doi.org/10.1186/s13015-025-00280-y>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC12135590/>

Its Background section is informative because it surveys exactly the two
research directions relevant here.

First, it says that previous work has shown that, given enough information, a
unique and correct assembly can be found in polynomial time, citing Shomorony et
al. 2016 among the relevant correctness/information results. It then separately
discusses probabilistic frameworks, citing Medvedev--Brudno's maximum-likelihood
assembly and GAML.

SAMA's own contribution is a per-edge model of structural misassembly
probability in a de Bruijn graph, including missing data, and contigs with
correctness estimates. It does not claim a bridge between the two older lines.

This is not a formal literature-proof that nobody solved the 2016 question.
Nevertheless, it is strong negative evidence: a 2025 correctness-guarantee paper
that directly cites both the exact 2016 source and the ML literature still
presents them as distinct approaches rather than referring to a solved
bridging-to-ML theorem.

## 10. Other adjacent directions

### 10.1 Variable-length reads

Hui, Shomorony, Ramchandran, and Courtade studied overlap-based assembly from
variable-length reads and information-theoretic limits:

- Joseph Hui, Ilan Shomorony, Kannan Ramchandran, and Thomas A. Courtade,
  **"Overlap-based genome assembly from variable-length reads,"** ISIT 2016.
  DOI: <https://doi.org/10.1109/ISIT.2016.7541453>

This is adjacent to the information-optimal assembly line but changes the read
model rather than proving the ML implication.

### 10.2 Read errors and adversarial error models

Shomorony, Courtade, Tse, and related work also study fundamental assembly limits
when reads contain errors/erasures. These results refine when exact
reconstruction is information-theoretically possible but again do not identify
the maximum-likelihood genome under the 2009 objective.

### 10.3 Multiplicity/copy-number inference

Several later probabilistic graph methods estimate node/edge multiplicities in
de Bruijn graphs. These are close to the mechanism of the Medvedev--Brudno ML
method because repeat copy counts are precisely what read-count likelihoods
attempt to infer. Such methods may supply mathematical tools for the conjecture,
but their objectives/guarantees are generally local or inferential rather than a
global theorem comparing the true genome with every candidate genome.

## 11. Why apparently similar results do not count as a solution

The literature contains several statements that can sound almost equivalent to
the desired result. They are not.

| Result type | What it establishes | What is still missing |
| --- | --- | --- |
| Unbridged-repeat lower bound (Bresler et al. 2013) | Failure of bridging can create a distinct same-length genome with equal read likelihood | Does not show that satisfying the stronger bridging conditions makes truth globally ML |
| MultiBridging / Not-So-Greedy | A specific algorithm exactly reconstructs under bridging/information-feasibility assumptions | Does not compare the likelihood of truth against every arbitrary candidate |
| HINGE | Resolves bridged repeats and preserves ambiguity at unresolvable repeats | No Medvedev--Brudno ML optimality theorem |
| Full \(L\)-spectrum uniqueness | Truth is the unique sequence consistent with a sufficiently informative complete spectrum | Different observation model from a finite random shotgun sample |
| CGAL / GAML / SWALO | Likelihood is computable/useful and can guide assembly/scaffolding | Empirical/algorithmic likelihood optimization, not bridging \(\Rightarrow\) truth theorem |
| Omnitigs / safe assembly | Characterizes sequences safe across graph-consistent genomes | Graph consistency is not maximum probability under a generative model |
| SAMA | Bounds local misassembly probabilities, including missing data | Different statistical guarantee; no global ML implication |

The distinction most likely to cause a false positive in a literature search is
between **unique reconstructibility** and **unique maximum-likelihood
optimality**. The former says the observed information determines the genome
under a particular consistency/reconstruction model. The latter is a global
comparison under a probabilistic objective. A theorem proving one need not
prove the other unless an additional equivalence lemma connects the models.

## 12. Technical observations relevant to a proof or counterexample

The literature search sharpens several issues that should be explicit before the
Lean model is made concrete.

### 12.1 Exact multinomial likelihood versus algorithmic approximation

The exact Medvedev--Brudno global read-count likelihood is multinomial and
contains \(N(D)\) in the denominator. Their optimization algorithm replaces the
nonseparable objective by an approximation suitable for convex flow.
`assemblyp1` should not silently prove a theorem about one while calling it a
theorem about the other.

A clean first target is probably the exact generative likelihood, because it has
a direct probabilistic meaning and can be defined with exact arithmetic.
Approximate objectives can be formalized later as separate definitions.

### 12.2 Candidate genome length

If all candidates are constrained to have the true length \(G\), the common
factor \(G^{-n}\) does not affect likelihood ordering, leaving the read-type
multiplicities as the essential variables. If candidate lengths are allowed to
vary, the denominator changes with the candidate and the optimization problem is
different.

Bresler's equal-likelihood ambiguity theorem explicitly constructs another
genome of the same length, so its conclusion is robust to this distinction.
The desired sufficiency direction is more sensitive to it.

### 12.3 Latent read positions versus observed reads

Bridging is naturally a property of the true genome together with the sampled
start positions: a read bridges a particular occurrence because its true span
extends beyond that occurrence on both sides. Maximum likelihood, by contrast,
should be computed from the observed read strings/multiplicities after summing
over possible origins in a candidate genome.

The formal model should therefore distinguish a **sequencing realization**
(true start positions) from the **observable read multiset/count vector**.
Otherwise it is easy to give the likelihood estimator information that an
estimator does not actually observe.

### 12.4 Read multiplicity must not be discarded

Overlap-graph algorithms may deduplicate identical reads for graph
construction. The read-count likelihood fundamentally depends on multiplicity.
The foundational `Reads` type should therefore retain repeated observations or
an equivalent exact count vector, with deduplication represented only as a
projection used by an algorithm.

### 12.5 Genome equivalence

The Shomorony exposition treats a circular sequence up to cyclic shift. The
Medvedev--Brudno development explicitly models double-stranded DNA, which raises
reverse-complement equivalence. The theorem statement should choose the
appropriate source-faithful equivalence rather than letting implementation
convenience decide it.

## 13. Research directions suggested by the literature

The search did not produce a ready-made solution, but it does suggest a useful
order of attack.

### 13.1 Formalize the Bresler equal-likelihood obstruction first

This is the nearest established likelihood theorem and exercises almost all the
machinery needed later:

- circular genomes;
- repeats and interleaving;
- bridging by a sequencing realization;
- observed reads with multiplicity;
- candidate genomes;
- likelihood equality.

Successfully formalizing it would provide a strong regression test for the
chosen definitions.

### 13.2 Search finite instances for counterexamples to the sufficiency claim

The open question is particularly amenable to exhaustive finite search after the
model is fixed. For small alphabet/genome/read lengths one can enumerate:

1. a true circular genome \(s\);
2. finite read-start realizations satisfying coverage and the exact bridging
   predicates;
3. the resulting observed read-count vector;
4. competing candidate genomes \(D\) in the intended candidate universe; and
5. exact rational/integer likelihood comparisons.

A discovered counterexample would still need a small kernel-checkable Lean
proof, but computation can guide the search.

This direction is plausible because finite-sample empirical frequencies need
not equal the true genome's exact substring frequencies. Bridging can encode
enough positional context for a reconstruction algorithm to recover \(s\),
while an alternative genome might conceivably have substring multiplicities
that fit a particular random sample better. This is a motivation for searching,
not evidence that a counterexample exists.

### 13.3 Prove restricted positive cases

If no small counterexample appears, useful intermediate theorems include:

- repeat-free genomes;
- genomes with only one double-repeat structure;
- fixed candidate length;
- complete \(L\)-spectrum observations;
- samples whose empirical read counts exactly match the true genome's
  substring-frequency proportions;
- restricted candidate classes generated by the same overlap/de Bruijn graph.

These cases can help identify whether the difficult step is combinatorial
identifiability, statistical sampling fluctuation, or the size of the global
candidate space.

### 13.4 Separate existence from uniqueness of the MLE

The first theorem worth attempting may be only

\[
L(s\mid R)\ge L(D\mid R)\quad\forall D,
\]

not strict inequality modulo genome equivalence. If ties remain possible even
under bridging, `truthIsML` could hold while `mlIsTruth` fails. The literature
search did not locate a source that disambiguates the 2016 English sentence
sufficiently to collapse these two possibilities.

## 14. Current assessment for `assemblyp1`

The repository should continue to treat the question as genuinely unresolved,
with a prominent qualification that this is based on an extensive but
necessarily non-exhaustive literature search.

The strongest facts currently surrounding the target are:

1. **Necessity / ambiguity:** all-unbridged problematic interleaved or triple
   repeats yield a distinct same-length genome with the same read likelihood
   (Bresler--Bresler--Tse 2013).
2. **Algorithmic sufficiency:** coverage plus all-bridged triple repeats and
   bridged interleaved repeats suffice for exact reconstruction by
   MultiBridging/Not-So-Greedy-style methods (Bresler et al.; Shomorony et al.).
3. **ML objective:** the global read-count likelihood is a principled alternative
   to parsimony, with subsequent practical extensions and approximations
   (Medvedev--Brudno, Varma et al., CGAL, GAML, SWALO).
4. **No located bridge between 2 and 3:** no searched source proved or disproved
   that the specific information-feasibility/bridging hypotheses force the true
   genome to be the global maximum-likelihood sequence.
5. **Recent literature still separates the lines:** SAMA (2025) cites both
   Shomorony's correctness result and maximum-likelihood/probabilistic assembly
   as distinct prior approaches.

That makes the open question a reasonable target for a formal-methods project:
it is precisely stated enough to have small finite models, adjacent theorems
exist for validating the formalization, and a positive proof or explicit
counterexample would both constitute meaningful settlement once the exact ML
model and conclusion are source-justified.

## References

1. G. Bresler, M. Bresler, and D. Tse. **Optimal assembly for high throughput
   shotgun sequencing.** *BMC Bioinformatics* 14(Suppl 5):S18, 2013.
   <https://doi.org/10.1186/1471-2105-14-S5-S18>

2. P. Medvedev and M. Brudno. **Maximum Likelihood Genome Assembly.**
   *Journal of Computational Biology* 16(8):1101--1116, 2009.
   <https://doi.org/10.1089/cmb.2009.0047>

3. A. Varma, A. Ranade, and S. Aluru. **An Improved Maximum Likelihood
   Formulation for Accurate Genome Assembly.** ICCABS, 2011.
   <https://doi.org/10.1109/ICCABS.2011.5729873>

4. A. Rahman and L. Pachter. **CGAL: computing genome assembly likelihoods.**
   *Genome Biology* 14:R8, 2013.
   <https://doi.org/10.1186/gb-2013-14-1-r8>

5. M. Howison, F. Zapata, E. J. Edwards, and C. W. Dunn. **Bayesian Genome
   Assembly and Assessment by Markov Chain Monte Carlo Sampling.** *PLoS ONE*
   9(6):e99497, 2014. <https://doi.org/10.1371/journal.pone.0099497>

6. V. Boža, B. Brejová, and T. Vinař. **GAML: genome assembly by maximum
   likelihood.** *Algorithms for Molecular Biology*, 2015.
   <https://doi.org/10.1186/s13015-015-0052-6>

7. I. Shomorony, S. H. Kim, T. A. Courtade, and D. N. C. Tse.
   **Information-optimal genome assembly via sparse read-overlap graphs.**
   *Bioinformatics* 32(17):i494--i502, 2016.
   <https://doi.org/10.1093/bioinformatics/btw450>

8. A. I. Tomescu and P. Medvedev. **Safe and complete contig assembly via
   omnitigs.** RECOMB 2016. <https://arxiv.org/abs/1601.02932>

9. J. Hui, I. Shomorony, K. Ramchandran, and T. A. Courtade.
   **Overlap-based genome assembly from variable-length reads.** ISIT 2016.
   <https://doi.org/10.1109/ISIT.2016.7541453>

10. G. M. Kamath, I. Shomorony, F. Xia, T. A. Courtade, and D. N. Tse.
    **HINGE: long-read assembly achieves optimal repeat resolution.**
    *Genome Research* 27(5):747--756, 2017.
    <https://doi.org/10.1101/gr.216465.116>

11. A. Rahman et al. **SWALO: scaffolding with assembly likelihood
    optimization.** *Nucleic Acids Research* 49(20):e117, 2021.
    <https://doi.org/10.1093/nar/gkab717>

12. A. Rahman and P. Medvedev. **Assembler artifacts include misassembly
    because of unsafe unitigs and underassembly because of bidirected graphs.**
    *Genome Research* 32:1746--1753, 2022.
    <https://doi.org/10.1101/gr.276601.122>

13. P. Medvedev. **Theoretical Analysis of Sequencing Bioinformatics Algorithms
    and Beyond.** *Communications of the ACM* 66(7):118--125, 2023.
    <https://doi.org/10.1145/3571723>

14. L. Salmela. **Sama: a contig assembler with correctness guarantee.**
    *Algorithms for Molecular Biology* 20:9, 2025.
    <https://doi.org/10.1186/s13015-025-00280-y>
