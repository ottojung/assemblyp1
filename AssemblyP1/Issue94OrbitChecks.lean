import AssemblyP1.Issue94OrbitSearch
import AssemblyP1.Issue94OrbitGeneral

/-!
# Board 94, front one: the exhaustive `decide` checks

This module used to carry the four-way conjunction

```lean
theorem iterStep4_5_8 :
    IterStep4 5 _ ∧ IterStep4 6 _ ∧ IterStep4 7 _ ∧ IterStep4 8 _ :=
  ⟨by decide, by decide, by decide, by decide⟩
```

and the four `by decide` checks were later split into one module per `K`
(`Issue94OrbitCheck5` .. `Issue94OrbitCheck8`) so that a failure at the
largest `K` would not cost the smaller ones.  That was the right move at
the time and it did produce a real boundary: `K = 5` exhausts the host's
30.0 GiB cgroup (exit 137, twice), so the `decide` route reached `K = 4` and
no further.

But the boundary was an artifact of the instrument, not of the mathematics.
`IterStep4` carries **no primitivity hypothesis**, and its shift bound
`ti.val ≤ pairBackC hK S c.val d.val` is bounded by `K` outright, since
`pairBackC` maximises over a `filter` of `Finset.range (K + 1)`.  So
`IterStep4 K` follows from the proved `step4_slide_iterates_word` for
**every** `K`, and `Issue94OrbitGeneral.IterStep4_all` proves it in 2.8
seconds at a 56 percent memory peak.

The per-`K` modules are therefore deleted and the `decide` checks are gone:
`iterStep4_5_8` below is now a *consequence* of the general theorem rather
than four independent finite searches.  See
`/workspace/board94-iterated-slide-c1.md` for the measurements.

`Issue89GapMap.Step4_slide_iterates` itself is still **not** inhabited; see
the "What is still NOT established" section of `Issue94OrbitGeneral`.
-/

namespace AssemblyP1.Issue94OrbitChecks

open AssemblyP1.Issue94OrbitSearch
open AssemblyP1.Issue94OrbitGeneral

/-- The four `IterStep4` checks, now inherited from the general theorem
`IterStep4_all` rather than re-decided.  This carries no `decide`; the
statement is proved at every `K`, not only at `5, 6, 7, 8`. -/
theorem iterStep4_5_8 :
    IterStep4 5 (by norm_num) ∧ IterStep4 6 (by norm_num) ∧ IterStep4 7 (by norm_num)
      ∧ IterStep4 8 (by norm_num) :=
  ⟨IterStep4_all 5 (by norm_num), IterStep4_all 6 (by norm_num),
    IterStep4_all 7 (by norm_num), IterStep4_all 8 (by norm_num)⟩

end AssemblyP1.Issue94OrbitChecks
