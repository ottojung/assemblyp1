# Medvedev–Brudno candidate-genome and length semantics

_Status: source note for issue #5; parent issue #1._

Primary source:

- Paul Medvedev and Michael Brudno, “Maximum Likelihood Genome Assembly,”
  *Journal of Computational Biology* 16(8), 2009, 1101–1116.
  DOI: <https://doi.org/10.1089/cmb.2009.0047>
  Open full text: <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>

This note isolates one modeling dependency: what the paper says about the
candidate genome and its length for the **exact global read-count likelihood**,
and how that differs from the later tractable approximation and flow algorithm.

## 1. Exact global read-count likelihood: what is directly stated

Section 6.1 introduces a candidate (D) as a **circular genome** with its own
length (N(D)). If (d_i) is the number of occurrences of k-molecule type
(i) in (D), then one uniformly sampled start position in (D) produces type
(i) with probability (d_i/N(D)).

For (n) independent sampled reads with observed counts (x_i), the joint
count distribution is multinomial. Up to the observation-only multinomial
coefficient, the exact likelihood therefore has candidate-dependent factor

[
prod_i left(rac{d_i}{N(D)}ight)^{x_i}.
]

The paper then says that its goal is to assemble the genome with maximum global
read-count likelihood.

### Consequence

For the exact likelihood as introduced in Section 6.1, the candidate's own
length is part of the objective. The source does **not** at this point replace
(N(D)) by the true genome length or state that all candidate genomes must have
one fixed externally supplied length.

Accordingly, a formalization of the exact Section 6.1 likelihood should not
silently bake in fixed candidate length merely because later algorithmic
approximations do so.

## 2. The separable/binomial approximation changes the length semantics

Still in Section 6.1, the authors explain that the exact multinomial objective
is not separable in the copy-count variables (d_i), which prevents direct use
of convex-cost flow.

They then approximate the multinomial model by a product of individual
binomials. At that point they explicitly treat genome length as a constant
independent of each (d_i), replace (N(D)) by (N), the length of the actual
source genome, and state that for their experiments genome size is assumed
known.

### Consequence

The paper contains two materially different objects:

1. **Exact global likelihood:** candidate (D) is circular and contributes its
   own (N(D)) to the multinomial likelihood.
2. **Tractable approximation:** genome length is supplied as a fixed constant
   (N), intended to be the actual genome length (known or estimated
   externally).

A theorem about one should not be labeled a theorem about the other without a
separate argument relating them.

## 3. Section 6.2 adds a separate graph/flow feasible set

Section 6.2 constructs a transitively reduced bidirected overlap graph from the
observed reads. The paper imposes a lower bound of one on every read vertex, so
every observed read is represented in the resulting flow at least once. The
flow encodes read copy counts, and a flow may decompose into a collection of
walks; the authors explicitly describe it as representing a potentially
non-contiguous assembly.

### Consequence

The feasible objects searched by the Section 6.2 algorithm are not presented
simply as “all circular genomes (D)” from the Section 6.1 exact likelihood.
They are flows in a particular read-derived overlap graph with explicit lower
bounds and with an interpretation that may be non-contiguous.

Therefore the following identification is **not source-justified without an
extra correspondence argument**:

> exact-likelihood candidate genomes = feasible flow solutions of Section 6.2.

This distinction matters for AssemblyP1 because the 2016 open question refers
to a maximum-likelihood sequence, whereas a proof about the specific 2009 flow
algorithm could accidentally solve a narrower optimization problem.

## 4. What remains genuinely ambiguous

This source note does **not** settle the final candidate universe for the
published 2016 open question.

What is established from Medvedev–Brudno is:

- the exact likelihood is defined for a circular candidate (D) and depends on
  (N(D));
- the approximation fixes/replaces the length by an externally supplied
  constant (N);
- the implementation/optimization step searches a constrained overlap-graph
  flow space rather than explicitly quantifying over arbitrary circular
  genomes.

What is not established by this source alone is:

- whether Shomorony et al.'s 2016 phrase “maximum-likelihood sequence” intends
  the exact Section 6.1 objective over all circular candidates, the constrained
  graph/flow optimization used operationally in 2009, or another convention;
- whether the eventual AssemblyP1 theorem should restrict competitors to the
  true genome length;
- whether reverse-complement equivalence should be part of the candidate
  identity when reconciling the double-stranded 2009 model with the circular
  string exposition of 2016.

Those questions must remain explicit until resolved from the locked literature
ground truth and additional primary-source correspondence work.

## 5. Formalization impact

For later Lean work, this note supports separating at least these concepts:

- a circular candidate genome with an intrinsic length;
- exact read-count likelihood using that candidate length;
- an optional fixed-length/restricted-candidate variant;
- the binomial/separable approximation as a distinct definition;
- the Section 6.2 overlap-graph/flow feasible set as a distinct algorithmic
  object.

This separation avoids making a source-sensitive modeling decision merely
because one representation is easier to optimize or prove against.
