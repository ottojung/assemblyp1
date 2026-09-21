# AssemblyP1 white paper

A publication-oriented LaTeX manuscript studying the 2016 open question of
Shomorony, Kim, Courtade, and Tse: whether repeat-bridging conditions guarantee
that the maximum-likelihood assembly is the true genome. It grows out of, but is
not a conversion of, the repository synthesis
[`docs/maximum-likelihood-models-for-genome-assembly.md`](../docs/maximum-likelihood-models-for-genome-assembly.md).

The paper keeps four layers visibly separate: historical definitions, the
ambiguities those definitions leave open, results about the resulting
formulations, and project-introduced repairs. Every nontrivial claim carries an
epistemic status tag; Appendix B is the consolidated ledger.

## Build

The build is reproducible and uses a pinned, minimal TeX dependency set. With
Guix available:

```sh
sh build.sh
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
    01-introduction.tex
    02-model.tex            notation, sequencing model, I_s, likelihoods, schemas
    03-open-question.tex    the published sentence and its source gaps
    04-finite-results.tex   rigidity theorem and strict counterexamples
    05-population.tex       population ML and the repaired uniqueness theorem
    06-discussion.tex       failure modes, open problems, conclusion
    a-modeling-choices.tex  deliberate explanations of modeling decisions
    b-epistemic-ledger.tex  consolidated status of every claim
    c-reproduction.tex      build and verification instructions
  manifest.scm             pinned Guix TeX dependencies
  build.sh                 reproducible PDF build
```

## Relationship to repository research

Theorems, counterexamples, and their epistemic status follow the repository's
research notes and verification artifacts (Lean modules under `../AssemblyP1/`
and exact-rational scripts under `../scripts/`). Where the paper states a
kernel-checked finite witness, the corresponding module is named in
Appendix B; where a claim is only source-supported or computationally verified,
it is labeled as such. Reproduction of the finite arithmetic does not by itself
verify the source-correspondence claims that identify a finite objective with
the one the published sentence intends.
