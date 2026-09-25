# Lean on Marceline Dev

Marceline Dev is AssemblyP1's **preferred execution target**. Use Lubko's Supabase command transport to reach `lubko://marceline-dev`; do not improvise a direct connection.

## Observed baseline

As of 2026-09-25, a fresh Marceline Dev workspace has:

- Git available (`git 2.54.0` in the observed image);
- GNU Guix available;
- an initially empty `/workspace`;
- no `lean`, `lake`, or `elan` executable on `PATH` by default;
- a project-backed `lubko-agent` wrapper at `$HOME/.local/bin/lubko-agent`, dispatching through `uv` to `/workspace/our-lubko-with-agent`;
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

## Delegated agents

The Marceline environment exposes `$HOME/.local/bin` on `PATH`. Its `lubko-agent` wrapper is:

```sh
#!/bin/sh
exec /usr/local/bin/uv run --project /workspace/our-lubko-with-agent lubko-agent "$@"
```

Use normal commands such as `lubko-agent list --running --json`. The wrapper deliberately executes the dedicated checkout rather than a stale globally installed copy.

## Troubleshooting

- `lean: not found` / `lake: not found`: expected on the baseline image; do not mistake this for a Lubko transport failure.
- Need only a host smoke test: use `guix shell lean4 -- ...`.
- Need repository verification: provision the exact `lean-toolchain` version first.
- Empty `/workspace`: clone/recover the repository or worktree before project commands.
- `lubko-agent: not found`: verify `$HOME/.local/bin` is on `PATH` and that `/workspace/our-lubko-with-agent` exists.
