import Lake
open Lake DSL

package «assemblyp1» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib AssemblyP1 where
  -- Build the root AND every submodule, including standalone proof modules
  -- that are not imported from AssemblyP1.lean.
  globs := #[.andSubmodules `AssemblyP1]
