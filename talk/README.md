# AssemblyP1 Beamer talk (issue #56)

A Beamer presentation about the AssemblyP1 project, aimed at software
developers working in a microbiology lab: technically strong programmers
who do not already know genome assembly, Lean, or the assembly-theory
literature.

The deck teaches assembly from strings and pictures (hidden genome,
reads, repeats, bridging), states the 2016 open question, walks the
finite result landscape (strict counterexamples plus the positive
same-length oriented rigidity result), presents the population
(infinite-read) repaired uniqueness theorem, and explains the research
workflow and Lean's certification role. Backup slides hold formulas,
modeling notes, strand conventions, and references.

## Build

Reproducible build with a pinned, minimal TeX dependency set. With Guix
available:

```sh
sh build.sh
```

This builds a local Guix profile from [`manifest.scm`](manifest.scm)
inside `talk/.guix-profile/` (ignored by git) and runs `latexmk`
(pdflatex), producing `main.pdf`. The equivalent manual command, if your
Guix supports ephemeral shells directly, is:

```sh
guix shell -m manifest.scm -- latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Source of truth

Theorem statuses track the white paper in [`paper/`](../paper/)
(which itself tracks the repository's Lean certificates and exact
computation scripts). The talk optimizes for intuition and pacing, not
completeness; every statement must stay technically correct as the
mathematics evolves.

## Layout

```text
talk/
  main.tex                 the deck (appendix = backup slides)
  manifest.scm             pinned Guix TeX dependencies (incl. beamer)
  build.sh                 reproducible PDF build
```
