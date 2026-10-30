# assemblyp1

**Finalized 2026-10-30:** [Paper v1.6.0](https://github.com/ottojung/assemblyp1/releases/tag/paper-v1.6.2) is the final versioned publication. All AssemblyP1 agents have been stopped and all related Antonina board issues closed. New sharp primitive-P2 separation and reverse-complement-class results are **paper-level mathematical theorems, not yet Lean-formalized**; historical physical-molecule transfer and bridging-threshold questions remain open. See [verification status](docs/verification.md).

AssemblyP1 studies a mathematical question about genome assembly:
**when does the true circular genome maximize the likelihood of the reads?**

The operational starting point is reconstruction: short reads overlap,
a graph records those overlaps, and repeats can produce competing paths.
Under coverage and repeat-bridging conditions, the 2016 Not-So-Greedy
algorithm reconstructs a genome by building and pruning a sparse
*read-overlap* graph, then finding a unique Eulerian spelling.

The project proves positive results about complete-spectrum rigidity and
population maximum-likelihood uniqueness, as well as exact finite-sample
examples where a competitor has higher likelihood. It includes Lean proofs,
an explanatory whitepaper, and two audience-specific presentations.

**Download the [latest white paper (PDF)](https://github.com/ottojung/assemblyp1/releases/download/whitepaper-latest/assemblyp1-white-paper.pdf)** for the full mathematical study,
or read its [LaTeX source](paper/main.tex). The PDF is automatically updated
from successful CI builds on main.

**Start with the [programmers' presentation](slides/programmers.md)** for a
worked graph construction and Not-So-Greedy.

See:

- [`docs/open-problem.md`](docs/open-problem.md) — source and informal statement;
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — staged formalization plan;
- [`docs/research-orchestration.md`](docs/research-orchestration.md) — multi-agent research/proof loop;
- [`docs/skills/README.md`](docs/skills/README.md) — operational AI research skills;
- [`AssemblyP1/OpenProblem.lean`](AssemblyP1/OpenProblem.lean) — current formal theorem schema;
- [`docs/bbt-eulerian-cycle-89.md`](docs/bbt-eulerian-cycle-89.md) — the external `thm:BBT` input (issue #89) in its source shape: uniqueness of the Eulerian cycle of the condensed `K`-mer graph;
- [`docs/intent-records/`](docs/intent-records/) — durable project intent.

## Historical research workflow (inactive)

Substantial research work is organized as a durable graph of narrow questions. The orchestrator distributed source research, model auditing, positive proof search, counterexample search, and Lean formalization to independent workers, and reconciled their exact propositions and evidence before integration. Source facts, conjectures, computational evidence, paper proofs, and kernel-checked Lean results remain explicitly distinct.

Historical process documentation: [`docs/skills/research-orchestrator.md`](docs/skills/research-orchestrator.md).

## Licensing and citation

The Lean source, scripts and build automation are free software under
[GNU GPL version 3 or later](LICENSE). Original manuscript prose and
presentation content are available under
[Creative Commons Attribution 4.0](LICENSE.paper), with third-party material
retaining its original rights.

For references, use [CITATION.cff](CITATION.cff). Stable signed publication
tags of the form paper-vX.Y.Z trigger a versioned GitHub Release
containing a PDF of that exact source revision. The whitepaper-latest
download continues to follow the tested main branch. The source and
verification index are bundled with the versioned Git tag.

## Build

```sh
lake build
```

The repository commits `lake-manifest.json` and pins matching Lean and Mathlib `v4.34.0` releases. Run `lake update` only when intentionally changing or regenerating dependency pins.

## Presentations

Two audience-specific [Slidev](https://sli.dev) decks — one for programmers, one
for biologists — live under [`slides/`](slides/) and are published together to
GitHub Pages. See [`slides/README.md`](slides/README.md) for local development,
`npm ci`/`npm run build`, validation, and deployment instructions.

```sh
cd slides
npm ci
npm run build
```

The LaTeX white paper under [`paper/`](paper/) is built by CI and published both as a workflow artifact and as a stable [downloadable PDF](https://github.com/ottojung/assemblyp1/releases/download/whitepaper-latest/assemblyp1-white-paper.pdf).
