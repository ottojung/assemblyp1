# assemblyp1

A Lean formalization project for a theoretical genome-assembly open problem stated by Shomorony, Kim, Courtade, and Tse in *Bioinformatics* (2016): whether suitable repeat-bridging conditions are enough to guarantee that the maximum-likelihood assembly is the true genome.

The repository is deliberately starting from the mathematical model rather than from an attempted proof. The first milestone is to formalize the sequencing model, repeat/bridging definitions, and the maximum-likelihood formulation faithfully enough that the paper's open question has a precise Lean statement.

See:

- [`docs/open-problem.md`](docs/open-problem.md) — source and informal statement;
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — staged formalization plan;
- [`docs/research-orchestration.md`](docs/research-orchestration.md) — multi-agent research/proof loop;
- [`docs/skills/README.md`](docs/skills/README.md) — operational AI research skills;
- [`AssemblyP1/OpenProblem.lean`](AssemblyP1/OpenProblem.lean) — current formal theorem schema;
- [`docs/intent-records/`](docs/intent-records/) — durable project intent.

## Research workflow

Substantial research work is organized as a durable graph of narrow questions. The orchestrator may distribute source research, model auditing, positive proof search, counterexample search, and Lean formalization to independent workers, then reconciles their exact propositions and evidence before integration. Source facts, conjectures, computational evidence, paper proofs, and kernel-checked Lean results remain explicitly distinct.

Start broad agentic work with [`docs/skills/research-orchestrator.md`](docs/skills/research-orchestrator.md).

## Build

```sh
lake build
```

The repository commits `lake-manifest.json` and pins matching Lean and Mathlib `v4.34.0` releases. Run `lake update` only when intentionally changing or regenerating dependency pins.
