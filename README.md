# assemblyp1

A Lean formalization project for a theoretical genome-assembly open problem stated by Shomorony, Kim, Courtade, and Tse in *Bioinformatics* (2016): whether suitable repeat-bridging conditions are enough to guarantee that the maximum-likelihood assembly is the true genome.

The repository is deliberately starting from the mathematical model rather than from an attempted proof. The first milestone is to formalize the sequencing model, repeat/bridging definitions, and the maximum-likelihood formulation faithfully enough that the paper's open question has a precise Lean statement.

See:

- [`docs/open-problem.md`](docs/open-problem.md) — source and informal statement;
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — staged formalization plan;
- [`AssemblyP1/OpenProblem.lean`](AssemblyP1/OpenProblem.lean) — current formal theorem schema;
- [`docs/intent-records/`](docs/intent-records/) — durable project intent.

## Build

```sh
lake update
lake build
```

The project pins Lean and Mathlib to matching `v4.34.0` releases.