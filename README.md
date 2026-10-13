# assemblyp1

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

**Start with the [programmers' presentation](slides/programmers.md)** for a
worked graph construction and Not-So-Greedy, or the
[whitepaper](paper/main.tex) for detailed definitions and theorems.

See:

- [`docs/open-problem.md`](docs/open-problem.md) — source and informal statement;
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — staged formalization plan;
- [`docs/research-orchestration.md`](docs/research-orchestration.md) — multi-agent research/proof loop;
- [`docs/skills/README.md`](docs/skills/README.md) — operational AI research skills;
- [`AssemblyP1/OpenProblem.lean`](AssemblyP1/OpenProblem.lean) — current formal theorem schema;
- [`docs/bbt-eulerian-cycle-89.md`](docs/bbt-eulerian-cycle-89.md) — the external `thm:BBT` input (issue #89) in its source shape: uniqueness of the Eulerian cycle of the condensed `K`-mer graph;
- [`docs/intent-records/`](docs/intent-records/) — durable project intent.

## Research workflow

Substantial research work is organized as a durable graph of narrow questions. The orchestrator may distribute source research, model auditing, positive proof search, counterexample search, and Lean formalization to independent workers, then reconciles their exact propositions and evidence before integration. Source facts, conjectures, computational evidence, paper proofs, and kernel-checked Lean results remain explicitly distinct.

Start broad agentic work with [`docs/skills/research-orchestrator.md`](docs/skills/research-orchestrator.md).

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

The LaTeX white paper under [`paper/`](paper/) is separate and still built as a
PDF artifact by CI.
