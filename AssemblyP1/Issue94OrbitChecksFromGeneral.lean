import AssemblyP1.Issue94Step2Path

/-!
# Fully checked small-circle OrbitExcl certificates without enumeration

The original `t_oe_3` through `t_oe_7` each ran a nested
`by decide` over *all* functions `Fin K → Bin`, all chords, read lengths,
and shifts. The largest certificate took over 37 minutes and ~14 GiB of
Lean resident memory, exhausting a GitHub-hosted runner and ending in
SIGTERM/exit 143.

`Issue94Step2Path.orbitExcl_core` proves the precise exclusion for **every**
primitive circular genome, with no size bound and no need for P2.  Each
of the original small-circle theorems is now a special case of that
stronger theorem. No sample or statement has been omitted, no new
axiom, `sorry`, `native_decide` or trust shortcut is introduced.
-/

namespace AssemblyP1.Issue94OrbitSearch

open AssemblyP1
open AssemblyP1.RepeatAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.Issue94Step2Path

/-- General OrbitExcl, reusing the proved theorem that does not require P2. -/
theorem orbitExcl_all (K : ℕ) (hK : 0 < K) [NeZero K] :
    OrbitExcl K hK := by
  intro S a b Li j hprim hab _hL2 _hLK hjC
  have hprim' : IsPrimitive hK S := (isPrimB_iff hK S).mp hprim
  have hj : j.val ≤ pairBack hK S a.val b.val := by
    simpa only [pairBackC_eq] using hjC
  exact orbitExcl_core K hK S hprim' a b hab j.val hj

/-- Exhaustive size-3 case, now deduced from the stronger universal theorem. -/
theorem t_oe_3 : OrbitExcl 3 (by norm_num) := orbitExcl_all 3 (by norm_num)
/-- Exhaustive size-4 case, now deduced from the stronger universal theorem. -/
theorem t_oe_4 : OrbitExcl 4 (by norm_num) := orbitExcl_all 4 (by norm_num)
/-- Exhaustive size-5 case, now deduced from the stronger universal theorem. -/
theorem t_oe_5 : OrbitExcl 5 (by norm_num) := orbitExcl_all 5 (by norm_num)
/-- Exhaustive size-6 case, now deduced from the stronger universal theorem. -/
theorem t_oe_6 : OrbitExcl 6 (by norm_num) := orbitExcl_all 6 (by norm_num)
/-- Exhaustive size-7 case, now deduced from the stronger universal theorem. -/
theorem t_oe_7 : OrbitExcl 7 (by norm_num) := orbitExcl_all 7 (by norm_num)

#print axioms orbitExcl_all
#print axioms t_oe_7

end AssemblyP1.Issue94OrbitSearch
