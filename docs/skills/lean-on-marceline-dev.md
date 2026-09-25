# Lean on Marceline Dev

Marceline Dev is AssemblyP1's **preferred execution target**. Use Lubko's Supabase command transport to reach `lubko://marceline-dev`; do not improvise a direct connection.

## Observed baseline

As of 2026-09-25, a fresh Marceline Dev workspace has:

- Git available (`git 2.54.0` in the observed image);
- GNU Guix available;
- an initially empty `/workspace`;
- no `lean`, `lake`, or `elan` executable on `PATH` by default;
- no `lubko-agent` executable on `PATH` by default;
- Guix package `lean4` at version 4.28.0.

AssemblyP1 currently pins `leanprover/lean4:v4.34.0` in `lean-toolchain`. Therefore the Guix `lean4` package is useful for **host smoke tests only**. A successful proof under Guix Lean 4.28.0 is not evidence that the AssemblyP1 project builds under its required toolchain.

## Basic host smoke test

A small standalone Lean proof can be used to check whether the host can execute Lean at all:

```sh
printf 'example (n : Nat) : n = n := by rfl\n' > /workspace/Smoke.lean
guix shell lean4 -- lean /workspace/Smoke.lean
```

Also record the smoke-test version:

```sh
guix shell lean4 -- lean --version
```

These commands test Marceline and Guix, not the repository.

## Project-valid Lean work

Before claiming any AssemblyP1 theorem or build is verified on Marceline:

1. create or recover an AssemblyP1 checkout/worktree on Marceline;
2. read its `lean-toolchain`;
3. ensure the **exact** pinned Lean toolchain is available (currently Lean 4.34.0);
4. prefer one shared Elan installation under `/home/lubko/.elan` once provisioned, rather than installing a private toolchain per worktree;
5. verify the version from inside the checkout;
6. reuse shared Lake/Mathlib dependencies when possible rather than allowing several worktrees to clone multi-gigabyte copies;
7. only then run focused `lean` checks and `lake build`.

Until the exact toolchain is provisioned, report project-level Lean verification as **blocked by toolchain provisioning**, not as passed using Guix Lean 4.28.0.

## Delegated-agent caveat

The Lubko command worker on Marceline can execute normal command jobs, but the observed baseline does not include the `lubko-agent` management CLI. If it remains unavailable, AssemblyP1 orchestrators must treat delegated-pool telemetry and launches as unavailable on Marceline; they must not interpret that as zero live agents and must not silently redirect new work to Phoebe. Direct bounded command work on Marceline remains available while the agent CLI is provisioned.

## Troubleshooting

- `lean: not found` / `lake: not found`: expected on the baseline image; do not mistake this for a Lubko transport failure.
- Need only a host smoke test: use `guix shell lean4 -- ...`.
- Need repository verification: provision the exact `lean-toolchain` version first.
- Empty `/workspace`: clone/recover the repository or worktree before project commands.
- `lubko-agent: not found`: agent-pool orchestration is not yet provisioned on this target; continue only work that does not require uncertain delegated capacity.
