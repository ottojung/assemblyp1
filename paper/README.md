# AssemblyP1 white paper

**The Most Likely Genome** explains genome assembly as a graph reconstruction
problem, then studies when the true circular genome maximizes the probability
of short-read observations. The finite Bayes/MAP optimality theorem explains why likelihood is worth
studying: for an exact sampling model and a uniform prior, ML is the best
algorithm for prior-averaged correct reconstruction. This is the entrance
to the investigation, not its main assembly-specific answer.

The paper gives each substantial result its own mathematical recognition:
positive same-length circulation rigidity and conditional uniqueness,
historical and variable-length finite-sample likelihood counterexamples,
kernel-checked population identifiability for primitive P2 genomes, and
general Graver-basis rigidity certificates, exact effective-weight
criteria for the fixed-$N$ binomial surrogate, and formal distinctions
between graph-flow optimization and sequence-spelling preservation.

The main text develops the algorithms, the repeat structure, the likelihood
models, and the proofs. The appendices preserve detailed modeling choices,
verification scope, and historical source reconciliation. A full
[claim-to-proof index](../docs/verification.md) lives outside the paper.

## Download

The current white paper is available as a [PDF download](https://github.com/ottojung/assemblyp1/releases/download/whitepaper-latest/assemblyp1-white-paper.pdf).
After each successful main build, the Documents workflow updates the
whitepaper-latest GitHub Release; pull requests only build and validate
without publishing. Previous CI workflow artifacts are also available for
individual revisions.

## Citation and archival revisions

The paper is licensed [CC BY 4.0](../LICENSE.paper); code and build scripts
are [GPL-3.0-or-later](../LICENSE). Metadata for citation is in
[CITATION.cff](../CITATION.cff). The moving whitepaper-latest release is
not an immutable citation. Each signed paper-vX.Y.Z tag builds and
publishes its own versioned PDF with the complete corresponding source
available from that Git tag.

The main manuscript keeps the proofs and principal theorem statements.
Lengthy provenance notes are preserved under paper/technical-notes/
and in the source-level [verification index](../docs/verification.md).
These notes are not substitute premises for any theorem.

## Build

The build is reproducible and uses a pinned, minimal TeX dependency set. With
Guix available:

```sh
sh paper/build.sh
```

This builds a local Guix profile from [`manifest.scm`](manifest.scm) inside
`paper/.guix-profile/` (ignored by git, so no writable per-user Guix profile is
needed) and runs `latexmk` (pdflatex + biber), producing `main.pdf`. The
equivalent manual command, if your Guix supports ephemeral shells directly, is:

```sh
guix shell -m manifest.scm -- latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The TeX dependencies are only `texlive-scheme-basic`, `latexmk`, `biblatex`,
`biber`, `amsmath`, `amsfonts`, `amscls`, `geometry`, `hyperref`, `booktabs`,
`microtype`, `enumitem`, `xcolor`, `pgf`, and `lm` (scalable fonts). Generated
files are ignored by [`.gitignore`](.gitignore); the PDF is a build artifact
rather than a committed binary.

## Layout

```text
paper/
  main.tex                 title, abstract, includes, bibliography
  preamble.tex             packages, theorem environments, status macros
  references.bib           bibliography
  sections/
    01-introduction.tex    genomes, reads, bridging, the ML question, contributions
    02-model.tex           notation, sequencing model, I_s, likelihoods, schemas
    03-open-question.tex   the mathematical question and its ingredients
    04-finite-results.tex  rigidity theorem and finite reweighting counterexamples
    05-population.tex      population ML and the uniqueness theorem
    06-discussion.tex       synthesis, open problems, conclusion
    a-modeling-choices.tex deliberate explanations of modeling decisions
    b-epistemic-ledger.tex compact claim-status summary
    c-reproduction.tex     build and verification-index pointer
    d-referents-audit.tex      condensed source-referent audit
    e-decision-bounds.tex      auxiliary decision-theory estimates
    f-molecular-flow.tex      source-faithful reverse-complement and flow variants
  technical-notes/            full preserved modeling and evidence audits
  manifest.scm             pinned Guix TeX dependencies
  build.sh                 reproducible PDF build
```

## Relationship to repository research

Theorems, counterexamples, and their epistemic status follow the repository's
research notes and verification artifacts (Lean modules under `../AssemblyP1/`
and exact-rational scripts under `../scripts/`). For each kernel-checked witness, the exact module and theorem are recorded
in the [verification index](../docs/verification.md), rather than
repeated in Appendix B. Source-supported statements, independent finite
computations, and formal results have distinct evidence labels. Reproduction of the finite arithmetic does not by itself
verify the source-correspondence claims that identify a finite objective with
the one the published sentence intends.
