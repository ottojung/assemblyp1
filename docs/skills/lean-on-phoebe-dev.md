# Lean on Phoebe Dev

Phoebe Dev already has the AssemblyP1 Lean toolchain installed through Elan. Reuse it; do not install a private toolchain in each worktree.

## Toolchain location and `PATH`

The executables are:

```text
/home/lubko/.elan/bin/lean
/home/lubko/.elan/bin/lake
/home/lubko/.elan/bin/elan
```

Lubko command jobs do not currently include that directory on `PATH`. Before running Lean work:

```sh
export PATH=/home/lubko/.elan/bin:$PATH
cd /workspace/assemblyp1   # or the active AssemblyP1 worktree
lean --version
```

Run the version check **inside an AssemblyP1 checkout/worktree**. Phoebe Dev intentionally has no global Elan default toolchain; the repository's `lean-toolchain` selects the project version. Do not run `elan default stable` or create a worktree-local `.elan` to work around this.

For a single command, this is equivalent:

```sh
cd /path/to/assemblyp1-worktree
PATH=/home/lubko/.elan/bin:$PATH lean --version
```

## Lake and disk usage

Lake resolves project dependencies in `.lake/packages`. In a brand-new worktree, even an apparently harmless command such as `lake env lean --version` may begin cloning dependencies. Do not use Lake as the initial toolchain check; use `lean --version` as above.

Mathlib is the large dependency and Phoebe Dev has a shared checkout under `/workspace/.shared-lake-packages`. Before the first Lake command in a fresh AssemblyP1 worktree, reuse that checkout when it matches the worktree's `lake-manifest.json`:

```sh
mathlib_rev=$(python3 -c 'import json; d=json.load(open("lake-manifest.json")); print(next(p["rev"] for p in d["packages"] if p["name"] == "mathlib"))')
shared_mathlib="/workspace/.shared-lake-packages/mathlib-$mathlib_rev"
test -d "$shared_mathlib"
test "$(git -C "$shared_mathlib" rev-parse HEAD)" = "$mathlib_rev"
mkdir -p .lake/packages
if [ ! -e .lake/packages/mathlib ] && [ ! -L .lake/packages/mathlib ]; then
    ln -s "$shared_mathlib" .lake/packages/mathlib
fi
```

If the matching shared Mathlib checkout does not exist, do not silently let many worktrees create multi-gigabyte private copies. Provision/reuse one shared checkout for that manifest revision first.

After the toolchain and dependency setup is correct, normal project commands are:

```sh
lake build
lake env lean AssemblyP1/OpenProblem.lean
```

Smaller transitive Lake dependencies may still be populated per worktree. The important disk-safety rules are: reuse `/home/lubko/.elan`, reuse the shared Mathlib checkout, and stop a fresh-worktree Lake invocation if it unexpectedly starts cloning Mathlib.

## Troubleshooting

- `lean`, `lake`, or `elan`: command not found — add `/home/lubko/.elan/bin` to `PATH`.
- `no default toolchain configured` — make sure the current directory is inside an AssemblyP1 checkout containing `lean-toolchain`; do not set a global default.
- Lake starts cloning Mathlib in a fresh worktree — stop it and configure `.lake/packages/mathlib` to use the matching shared checkout before continuing.
