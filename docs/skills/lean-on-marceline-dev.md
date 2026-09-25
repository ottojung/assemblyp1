# Lean and managed agents on Marceline Dev

AssemblyP1's preferred execution target is `lubko://marceline-dev`.

Use Lubko's normal queue transport to execute commands on the host. The current
Lubko connector no longer ships the managed-agent runtime, so AssemblyP1 keeps
that CLI available from a pinned pre-removal Lubko checkout.

## Managed-agent runtime

The managed-agent checkout is:

```text
/workspace/our-lubko-with-agent
```

It is pinned to Lubko commit:

```text
c9de388653353865c7eb13bb3e0dbb112f05025f
```

This is the immediate parent of the Lubko change that removed
`src/lubko/agent.py` and the `lubko-agent` entry point.

The preferred launcher is a tiny wrapper rather than a globally installed copy:

```sh
mkdir -p "$HOME/.local/bin"

cat > "$HOME/.local/bin/lubko-agent" <<'EOF'
#!/bin/sh
exec uv run --project /workspace/our-lubko-with-agent lubko-agent "$@"
EOF

chmod +x "$HOME/.local/bin/lubko-agent"
```

For compatibility with old commands, `my-lubko-agent` may use the same pattern:

```sh
cat > "$HOME/.local/bin/my-lubko-agent" <<'EOF'
#!/bin/sh
exec uv run --project /workspace/our-lubko-with-agent my-lubko-agent "$@"
EOF

chmod +x "$HOME/.local/bin/my-lubko-agent"
```

If the checkout needs to be recreated:

```sh
git clone https://github.com/ottojung/lubko.git /workspace/our-lubko-with-agent
git -C /workspace/our-lubko-with-agent checkout --detach   c9de388653353865c7eb13bb3e0dbb112f05025f
```

Do not move this checkout to current Lubko `main` unless the managed-agent
runtime is deliberately restored there.

A quick agent-runtime smoke check is:

```sh
lubko-agent list --running --json
```

## Lean

Marceline has Guix. AssemblyP1 does not require the host's globally available
Lean version to match an old Phoebe installation for simple evaluator work.
For a tiny standalone Lean check, use Guix directly:

```sh
cat > /tmp/AssemblyP1Smoke.lean <<'EOF'
theorem add_zero_smoke (n : Nat) : n + 0 = n := by
  simp
EOF

guix shell lean4 -- lean /tmp/AssemblyP1Smoke.lean
```

For repository verification, the repository itself remains authoritative about
its Lean/Lake dependencies. Prefer the cheapest setup that can run the exact
project checks; do not duplicate multi-gigabyte dependency trees across many
worktrees. If a shared Mathlib/Lake cache is provisioned on Marceline, reuse it.

Before calling a Lean-changing branch complete, still run the repository's
required exact-head checks such as `lake build` and CI. A standalone Guix Lean
smoke test only verifies that Marceline can execute Lean proofs; it does not
replace project verification.

## Host assumptions

Currently verified on Marceline:

- Lubko queue commands execute successfully;
- Git and Guix are available;
- `uv` is available;
- the wrapper-backed `lubko-agent` CLI runs successfully from the pinned
  pre-removal Lubko checkout.

If any of these assumptions changes, repair the host setup rather than silently
falling back to Phoebe as the default execution target.
