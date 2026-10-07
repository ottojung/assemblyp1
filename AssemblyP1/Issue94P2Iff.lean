import AssemblyP1.P2

/-!
# Board 94, front 94-p2iff: `P2 ↔ Ukkonen` at `K = L - 1` — **UNVERIFIED**

> **STATUS: COMPILED, EXIT 0 (repaired by front 94-p2repair).**
>
> ```
> export LEAN_PATH=$(cd /workspace/assemblyp1-94-final && /home/lubko/.elan/bin/lake env printenv LEAN_PATH)
> cd /workspace/assemblyp1-94-p2repair
> /home/lubko/.elan/bin/lean AssemblyP1/Issue94P2Iff.lean ; echo "EXIT=$?"
> ```
>
> printed `EXIT=0` with no diagnostics.  All three theorems in this file are
> now **kernel-checked**, at every `L ≥ 0` and with no hypothesis beyond
> `0 < G`.  The only mathematical change made to this file was to
> `P2_iff_Ukkonen_of_noRange`: its backward direction is now proved directly
> from `IsRepeat`'s `1 ≤ e` conjunct instead of being delegated to
> `P2_iff_Ukkonen` with a side condition `2 ≤ L` that does not follow from
> anything.  `lean` is `leanprover/lean4:v4.34.0`, matching `lean-toolchain`.
> No `lake build`, no `lake env lean`, no `native_decide`, no `sorry`, no
> `admit`, no `axiom`, no `set_option`.  One `lean` at a time.
>
> The file is still **not** added to `AssemblyP1.lean`; integration is the
> orchestrator's decision.

## Why this module exists

`AssemblyP1/P2.lean:104` proves only `P2.imp_Ukkonen`.  Two committed
docstrings --- `AssemblyP1/Issue94TW1EdgeType.lean:537-539` and
`AssemblyP1/Issue94TW1EdgeType.lean:569-571` --- assert on the strength of that
one-way theorem that "`P2` is *strictly* stronger than `Ukkonen`" and therefore
that "`Ukkonen` does not supply the `P2` hypothesis".  If the converse holds,
those sentences are false.  This module states the converse.

## The mathematics, in full

`P2.lean:80-85` and `P2.lean:91-96` define the two conditions.  Compared clause
by clause:

* **Triple clause.** `P2.lean:81` and `P2.lean:92` are the *same line of source*:

  ```lean
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
  ```

  so the two clauses are the same proposition for every `L`, with no
  hypothesis.  This is `Iff.rfl`.

* **Interleaved clause.** `P2.lean:85` says `e₁.val ≤ L - 2 ∨ e₂.val ≤ L - 2`;
  `P2.lean:96` says `e₁.val < L - 1 ∨ e₂.val < L - 1`.  In `ℕ` these are the
  same statement for every `L ≥ 1`, since `x < L - 1 ↔ x + 1 ≤ L - 1 ↔
  x ≤ (L - 1) - 1 = L - 2` once `L - 1 ≠ 0`.  Forward is
  `P2.imp_Ukkonen` (`P2.lean:104-111`), which is proved under `2 ≤ L`;
  backward is the same arithmetic in the other order.

### The exact set of `L` at which the two differ

This is the part `BOARD94-DECSEARCH.md` §4 does not state, and it is sharper
than "`2 ≤ L`".

Write `A(L)` for "for all genomes, the `P2` and `Ukkonen` interleaved clauses
have the same truth value", and note that the clauses are only ever *reached*
with `hR₁ : (mkGenome hG S).IsRepeat e₁ a b`, whose first conjunct is
`1 ≤ (e₁ : ℕ) = e₁.val` (`SourceFaithfulIs.lean:111-113`).  So `e₁.val ≥ 1`
always holds in the clause.

* **`L = 0`.**  `L - 2 = 0` and `L - 1 = 0`.  The `P2` clause reads
  `e₁.val = 0 ∨ e₂.val = 0`; the `Ukkonen` clause reads
  `e₁.val < 0 ∨ e₂.val < 0`, which is `False` in `ℕ`.  Pointwise the two
  clauses are *not* interderivable (`e₁.val = 0` vs `⊥`), and the bare
  implication `x ≤ L - 2 → x < L - 1` is false at `L = 0` (take `x = 0`).
  **But** the clause is only ever evaluated at `e₁.val, e₂.val ≥ 1`, where the
  `P2` reading is also `False`.  So at `L = 0` the *propositions* `P2 hG 0 S`
  and `Ukkonen hG 0 S` still agree: both reduce to "no interleaved repeat
  pair at all", plus the (identical) triple clause.
* **`L = 1`.**  `L - 2 = 0` and `L - 1 = 0`.  Identical to `L = 0` after the
  `e.val ≥ 1` filter: both clauses are `False` whenever a pair exists.  The
  clauses are interderivable even pointwise at `x ≥ 1`, and agree as
  propositions.
* **`L ≥ 2`.**  The clauses are interderivable pointwise, by the arithmetic
  above.  This is the regime `2 ≤ L` that `P2.imp_Ukkonen` is stated in.

**Conclusion.** `P2 hG L S ↔ Ukkonen hG L S` holds for **every** `L ≥ 0`; the
hypothesis `2 ≤ L` in the first theorem below is what makes the *proof* a
one-line `omega` rather than a case analysis, and matches the hypothesis
already carried by `P2.imp_Ukkonen` and by all of its callers.  The
second theorem below drops the hypothesis.  Both are proposed; see the
status banner.  `docs/population-uniqueness-end-to-end-89.md:196-200` already
says the `L ≤ 1` case "holds vacuously", which is consistent with this and
does not need changing.

## What these theorems do NOT say

* Nothing about `thm:BBT`, `BBTEulerian.UniqueEulerianCycle`, or
  `BBTEulerian.EulerianCycleObstruction`.  None of those takes `P2`; they take
  `Ukkonen` (`BBTEulerian.lean:440-443`).
* Nothing about primitivity.  `BlocklessLadderVertexCycle`
  (`Issue94TW1EdgeType.lean:480-484`) additionally assumes
  `RepeatAdapter.IsPrimitive hK S`, `2 ≤ L` and `L ≤ K`, and `Ukkonen` does
  not supply any of those.  The converse of
  `blockless_of_uniqueEulerianCycle` therefore remains unavailable, for a
  reason that has nothing to do with `P2`.
* These are `Prop`-level equivalences of the project's own definitions.  They
  do not re-verify any of the paper's alignment prose, and they do not license
  the reading that the conditions are *identical statements of the source*.
-/

namespace AssemblyP1

open SourceFaithfulIs

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-- **Kernel-checked.**  The two triple-repeat clauses are the same proposition,
character for character (`P2.lean:81` versus `P2.lean:92`).  This holds for
every `L` and needs no hypothesis; it is the reason the triple half of the
equivalence is free. -/
theorem triple_clauses_identical (hG : 0 < G) (S : Fin G → α) :
    (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ↔
      (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) :=
  Iff.rfl

/-- **Kernel-checked** (`2 ≤ L`; the hypothesis-free form is
`P2_iff_Ukkonen_of_noRange` below).  `P2` and `Ukkonen` at `K = L - 1` are the
same proposition, not merely related one way.

This is the converse of `P2.imp_Ukkonen` (`P2.lean:104`), which is the
*forward* direction and is what the repository states today.  It is cheap:
the triple clauses are `Iff.rfl` (`triple_clauses_identical` above) and the
interleaved clauses differ only by the ℕ identity `x ≤ L - 2 ↔ x < L - 1`,
which is what `2 ≤ L` buys.  Every call site of `P2.imp_Ukkonen` may equally
run backwards.

**Where it fails.**  Not for any `L` as a statement about `P2` and
`Ukkonen`: the equivalence holds at every `L ≥ 0`.  What `2 ≤ L` buys is the
*proof*.  At `L = 0` and at `L = 1` the two thresholds degenerate,
`L - 2 = L - 1 = 0`, and the pointwise implication `e.val ≤ L - 2 → e.val <
L - 1` is *false* in ℕ (`L = 0`, `e.val = 0` is a counterexample); the
equivalence survives there only because `IsRepeat` forces `1 ≤ e.val`
(`SourceFaithfulIs.lean:112`), which makes both clauses unsatisfiable.  See
`P2_iff_Ukkonen_of_noRange` below for the hypothesis-free form, which must be
proved with that fact rather than with `omega` alone.

**What it does NOT say.**  It says nothing about `thm:BBT` or any Eulerian
statement, and in particular does not make `Ukkonen` supply primitivity or
the range condition `L ≤ K`. -/
theorem P2_iff_Ukkonen (hG : 0 < G) (S : Fin G → α) (hL : 2 ≤ L) :
    P2 hG L S ↔ Ukkonen hG L S := by
  refine ⟨P2.imp_Ukkonen hL, fun h => ⟨h.1, ?_⟩⟩
  intro e₁ e₂ a b c d hR₁ hR₂ hI
  rcases h.2 e₁ e₂ a b c d hR₁ hR₂ hI with hle₁ | hle₂
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **Kernel-checked.**  The hypothesis-free form: `P2` and `Ukkonen` at
`K = L - 1` are equivalent at *every* `L`, including `L = 0` and `L = 1`.

The point is that `P2_iff_Ukkonen` above is not the sharp statement.  The
two interleaved clauses are not interderivable pointwise at `L ≤ 1`
(`L - 2 = L - 1 = 0`, so `e.val ≤ 0` is not the same as `e.val < 0`), but the
clause is only ever reached with `e₁.val ≥ 1` and `e₂.val ≥ 1`, from
`IsRepeat`'s own `1 ≤ e` conjunct (`SourceFaithfulIs.lean:112`).  At those
values both clauses are `False`, so the propositions still agree.

Both directions are proved directly, by feeding `hR₁.1` and `hR₂.1` to `omega`
instead of `hL`; no case split on `L = 0` / `L = 1` is needed, and neither
direction is delegated to `P2_iff_Ukkonen`.  (An earlier draft *did* delegate
the backward direction to `P2_iff_Ukkonen` with a side condition `2 ≤ L`;
that side condition does not follow from anything and the draft did not
compile.  Delegation is unnecessary: `omega` closes both directions from the
`IsRepeat` bounds alone.)

**What it does NOT say.**  Nothing about `L = 0` being a meaningful read
length; the point is only that the two `Prop`s have the same inhabitants. -/
theorem P2_iff_Ukkonen_of_noRange (hG : 0 < G) (S : Fin G → α) :
    P2 hG L S ↔ Ukkonen hG L S := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
  · intro e₁ e₂ a b c d hR₁ hR₂ hI
    have h1 : 1 ≤ e₁.val := hR₁.1
    have h2 : 1 ≤ e₂.val := hR₂.1
    rcases h.2 e₁ e₂ a b c d hR₁ hR₂ hI with hle₁ | hle₂
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro e₁ e₂ a b c d hR₁ hR₂ hI
    have h1 : 1 ≤ e₁.val := hR₁.1
    have h2 : 1 ≤ e₂.val := hR₂.1
    rcases h.2 e₁ e₂ a b c d hR₁ hR₂ hI with hlt₁ | hlt₂
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end AssemblyP1
