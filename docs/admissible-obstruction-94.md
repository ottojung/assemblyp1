# The admissible obstruction for the #94 endgame (board 94, ENDGAME-STATEMENT)

Branch `board/94-endgame`, base `666e849`. Kernel-checked module:
`AssemblyP1/BBTAdmissibleObstruction.lean` (inside the lake target
`AssemblyP1`). Census script: `scripts/board94_endgame_statement.py`, output
`docs/board94-endgame-statement-census.txt`. Front report:
`/workspace/BOARD94-ENDGAME-1000.md`.

No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe` or linter suppression
occurs in the new module. Everything was checked with `lake env lean` only.

## 1. The statement-level fact, at general `G` and `L`

`BBTReplacement.longObstruction_iff_not_P2` (`hL : 2 ≤ L`) is an `Iff`
between `LongObstruction` and `¬ P2`. `LongObstruction`
(`BBTEulerian.lean:337`) is

* `(T)` `∃ e a b c, IsTripleRepeat e a b c ∧ L - 1 ≤ e.val`, or
* `(I)` `∃ e₁ e₂ a b c d, IsRepeat e₁ a b ∧ IsRepeat e₂ c d ∧
  Interleaved a b c d ∧ L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val`

and `P2` (`P2.lean:80`) is the conjunction of the two *negations of exactly
those statements*. Hence under `2 ≤ L`:

```lean
theorem P2_not_tripleClause      -- P2 ⊢ ¬ (T)
theorem P2_not_interleavedClause -- P2 ⊢ ¬ (I)
theorem P2_refutes_every_conclusion_inside_LongObstruction
    -- P2 ⊢ ¬ (T) ∧ ¬ (I) ∧ ¬ LongObstruction
```

all at general `G`, all in the kernel. **So the conclusion of the residual
cannot be `LongObstruction`, and it cannot be either disjunct on its own.**
This is stronger than the audits' finding (they had the disjunction only) and
it is the sharp answer to "which conjunct must be strengthened or replaced":
**both, and disjunct-wise.** `P2_implies_longObstruction_false_00101` records
the instance form at `S = 00101`, `L = 3`.

### What this does *not* say

It does **not** refute `InterleavingObstructionNeeded`
(`BBTReplacementInvariant.lean:620`). That `Prop` concludes `LongObstruction`
under six `θ`-hypotheses, none of which is `¬ LongObstruction`; the discharger
supplies that separately. Finding 1 refutes the *unconditional* shape
"`P2 → LongObstruction`", not the conditional one. Whether the conditional one
has an instance is a separate question, answered by census in §4.

## 2. The admissible form

`Genome.IsRepeat` is

```
1 ≤ e ∧ e < |D| ∧ a ≠ b ∧ Agree e a b ∧ Preceding a ≠ Preceding b ∧ Following e a ≠ Following e b
```

`P2`'s interleaved clause ranges only over `IsRepeat`, i.e. only over
**two-sided** maximal repeats. Dropping the `Preceding`-clause of `IsRepeat`
therefore makes the statement invisible to `P2`, while keeping everything else:
the `≥ L - 1` threshold, the following-maximality, and the interleaving of the
four starts.

```lean
def PrecedingBlocked (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Prop :=
  (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b

def IsRightRepeat (hG : 0 < G) (S : Fin G → α) (e a b : Fin G) : Prop :=
  1 ≤ e.val ∧ Agrees hG S e.val a b ∧ a ≠ b ∧
    (mkGenome hG S).Following e.val a ≠ (mkGenome hG S).Following e.val b

def AdmissibleObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ e₁ e₂ a b c d : Fin G,
    InterleavedStarts hG a b c d ∧ L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val ∧
      IsRightRepeat hG S e₁ a b ∧ IsRightRepeat hG S e₂ c d ∧
      (PrecedingBlocked hG S a b ∨ PrecedingBlocked hG S c d)
```

In words: **two interleaved doubled `(L-1)`-mers, each extending to the right
to length `≥ L - 1`, at least one of which extends to the left.** The
"doubled `(L-1)`-mer" reading is not an extra clause:
`admissible_fibres` proves `vtx a = vtx b ∧ vtx c = vtx d` from the statement.

Why this particular weakening and not another:

* **`Preceding` and not `Following`.** `BBTReplacement.selectedInterleaved_crux`
  (kernel-checked, `:272`) delivers a *preceding*-block at the selected starts
  of a selected interleaving on an obstruction-free genome, and
  `BBTMaximalExtension.preceding_ne_of_maxBack` is exactly the lemma that
  cannot remove it. The Following direction is available:
  `maximalRepeat_of_branch` / `max_of_agrees` give right-maximality. So the
  `Preceding`-clause is the *only* one of the two maximality clauses the
  endgame cannot produce, and dropping it is the minimal edit.
* **Why the threshold stays at `L - 1`.** Raising it (say one constituent to
  `≥ L`) also escapes `P2`, but it discards the agreement that the selected
  interleaving hands over for free (`AdmissibleObstruction`'s constituents are
  `≥ L - 1` by hypothesis, and the census shows `Following`-maximality is
  available at that length: 0 exceptions in range, §4). Keeping the threshold
  is the strongest admissible choice.
* **Why the `(T)` disjunct is dropped.** Two independent reasons.
  `P2_not_tripleClause` above shows it is refuted by `P2`. Independently, a
  census over all binary circular words with `G ≤ 8`, `2 ≤ L ≤ 4` finds **0**
  primitive `P2` words with any `(L-1)`-mer of multiplicity `≥ 3` (388
  primitive `P2` words; 48 non-primitive ones have such a mer). Since
  `IsTripleRepeat e a b c` with `e ≥ L - 1` exhibits three occurrences of one
  `(L-1)`-mer, on a **primitive** `P2` genome the `(T)` disjunct is not merely
  unproved but *false*, and `SelectedTriple` is therefore vacuous — which also
  retires the `(T)` branch of the endgame. **Census, not kernel**: the lemma
  "primitive + `P2` ⟹ no `(L-1)`-mer of multiplicity `≥ 3`" is unproved and is
  named in §5 as a missing hypothesis.

Minimality in both directions is therefore:

* `AdmissibleObstruction` is the **strongest** conclusion not refuted by `P2`
  among the edits that keep the `≥ L - 1` thresholds, the interleaving and one
  maximality clause (census: exactly one of the two maximality clauses can fail
  under `P2`, and it is always the `Preceding` one — 128 cases, 0 exceptions);
* it is not trivially true either (census: 128 of the 476 `P2` pairs, 912 of all
  pairs, `G ≤ 8`, `2 ≤ L ≤ 4`), so the residual is a real obligation.

### The replacement is a replacement, not a weakening

`isRepeat_not_precedingBlocked` / `interleavedClause_not_admissible`: a pair of
interleaved *maximal* repeats has different preceding symbols at both
constituents, at general `G`. So `(I)` and `AdmissibleObstruction` do not entail
one another.

## 3. Non-vacuity (kernel-checked)

`S = 00101`, `L = 3`: `P2` holds (`p2_hG5_S5_L3`), and

```
(a, b, e₁) = (1, 3, 3)   "010" at 1 and 3; Following 3 1 = S₄ = 1 ≠ S₁ = 0
(c, d, e₂) = (2, 4, 2)   "10"  at 2 and 4; Following 2 2 = S₄ = 1 ≠ S₁ = 0
```

are four interleaved starts, with `(c, d)` preceding-blocked (`S₁ = S₃ = 0`).

```lean
theorem P2_and_admissible_00101 :
    P2 BBTChords.hG5 3 S5b ∧ AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) S5b
```

`#print axioms` of that theorem: `propext` only. This is the minimal kernel
witness required by the front: a false-by-construction residual would hide as a
vacuous one, and this inhabitant is what separates `AdmissibleObstruction` from
every conclusion inside `LongObstruction`, each of which is refuted at this very
instance (`P2_implies_longObstruction_false_00101`).

## 4. Census (evidence, `scripts/board94_endgame_statement.py`)

Independent transcription from the Lean sources, *not* from the existing
board-94 scripts (per `BOARD94-RECONCILE-AUDIT.md` §3, two of those were
defective).

| claim | range | result |
| --- | --- | --- |
| `AdmissibleObstruction` **not** refuted by `P2` | `G ≤ 8`, `2 ≤ L ≤ 4` | holds at 128 of 476 `P2` pairs; smallest `(G,L,S) = (5,3,00101)` |
| `AdmissibleObstruction` not trivially true | same | holds at 912 of all pairs |
| `(I)`-clause never holds on a `P2` word | same | 0 occurrences (as `P2_not_interleavedClause` forces) |
| `(T)`-clause never holds on a *primitive* `P2` word | same | 0 of 388; 48 non-primitive `P2` words do have a triple-mer |
| an interleaved right-maximal pair under `P2` is always `Preceding`-blocked | same | 128 of 128; `Following`-blocked: 0 |
| **bad** selected-interleaving one-cycle on a `P2` genome | `G ≤ 6`, `2 ≤ L ≤ 3` | **0** (668 selected interleavings, all good) |

The last row is the load-bearing negative result: the census finds **no**
counterexample to `InterleavingObstructionNeeded` and **no** inhabitant of
`BadSelectedInterleavingWitness` in that range. It also means the census cannot
be used to argue that the current statement is refuted — it is not, in range.

## 5. The remaining chain to the #89 endpoint — named, not proved

The endpoint is `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`,
whose only non-kernel input is

```lean
def EulerianCycleObstruction (L : ℕ) : Prop :=
  ∀ K hK S, Ukkonen hK L S → ∀ σ, EulerianCycle hK L S σ →
    VertexCycleEq hK L S σ refl ∨ LongObstruction hK L S
```

consumed by `BBTEulerian.bbtCompleteSpec_of_obstruction`, whose discharger is
`not_longObstruction_of_Ukkonen hUkk`. The #89 endgame is exactly: prove
`EulerianCycleObstruction L` for the primitive-`P2` class. From
`AdmissibleObstruction` the chain, with every missing hypothesis listed:

1. **Extraction of the bad `θ`** — from a non-rotational `EulerianCycle σ` of
   the condensed `(L-1)`-mer graph, produce
   `θ = succOf σ : Fin K → Fin K` with `Function.Bijective θ`,
   `FibrePreserving θ`, `OneCycle θ`, `¬ OrbitVertexEq θ`.
   **CLOSED, kernel-checked** (`BBTEulerianSearch`, this branch):
   `succOf_bijective`, `fibrePreserving_succOf` and `oneCycle_succOf` give the
   three positive clauses, and `vertexCycleEq_to_orbit` /
   `orbit_to_vertexCycleEq` (assembled into `uniqueAt_iff_orbit`) bridge
   `¬ VertexCycleEq σ refl` with `¬ OrbitVertexEq θ`.  An earlier note in this
   file claimed `θ` bijective was still missing; that was wrong, it is proved.
2. **The support dichotomy** — `SelectedTriple θ ∨ SelectedInterleaved θ`
   (`BBTSupportInvariant.SupportDichotomy`). *Missing:* the whole statement;
   it is the external Arratia-descent content.
3. **`¬ SelectedTriple θ` from primitivity + `P2`** — needs
   *primitive `S`* and the lemma "no `(L-1)`-mer of multiplicity `≥ 3`
   on a primitive `P2` genome" (§2). **CLOSED, kernel-checked** on branch
   `agent/issue94-p2triple-maxext` (commit `1c7e466`), at general `G` and
   general `L`, in `AssemblyP1/P2TripleMaximalExtension.lean`:

   ```lean
   triple_extension_of_repeated              -- 3 distinct starts spelling one
                                             -- (L-1)-mer lie inside an
                                             -- IsTripleRepeat e, L-1 <= e < G
   mer_multiplicity_le_two_of_P2_primitive  -- (fibre v).card <= 2
   not_SelectedTriple_of_P2_primitive       -- ¬ SelectedTriple θ, for every θ
   ```

   The axiom audit of these four public theorems is
   `[propext, Classical.choice, Quot.sound]`.  Without primitivity this step
   does fail and the `(T)` branch is live — the counterexample is
   `S = 0101`, `G = 4`, `L = 3` (a square), where `SelectedTriple θ` holds
   for `θ = (0 2)(1 3)`.
4. **`SelectedInterleaved θ` ⟹ `AdmissibleObstruction`** — the new obligation
   this front states. *Missing:* everything. The kernel-checked input is
   `selectedInterleaved_crux` (a preceding-blocked constituent) plus
   `agrees_back` / `BackAgrees_shift` (right-maximality of the blocked pair);
   the unresolved part is that the block must occur at a pair of length `≥ L - 1`
   whose four starts interleave, and the case split of
   `BOARD94-BADNESS-0153.md` §5 (case 1 landing, case 2 both-blocked) is
   precisely the combinatorial core.
5. **`P2` and `AdmissibleObstruction` together ⟹ contradiction** — i.e.
   `P2 ∧ AdmissibleObstruction → False`. *This cannot be the plan*: §3 exhibits
   an instance where both hold. The contradiction must come from the `θ`-side
   too, i.e. the real obligation is
   `P2 ∧ bad θ ∧ ¬ SelectedTriple θ ∧ SelectedInterleaved θ → False`, and steps
   1–4 are its premises. **`AdmissibleObstruction` is a conclusion, never a
   hypothesis of the discharger.**
6. **`LongObstruction` is never needed again.** The discharger of
   `EulerianCycleObstruction` wants `VertexCycleEq ∨ LongObstruction`, and
   `P2` forbids `LongObstruction`; step 5 supplies `False` directly, so the
   chain does not re-enter `LongObstruction` at any point.

Also missing and not derivable from anything above: the two-genome side. The
endpoint is "primitive-`P2` source **+ primitive-`P2` candidate** + equal
`L`-spectrum ⟹ `RotEquiv`", and
`BBTEulerian.bbtCompleteSpec_of_obstruction` only needs `Ukkonen` on the
**source** (the candidate enters through `exists_matching`). If a future front
wants the candidate's `P2` to do work, the transfer
"`E` is `P2` at `L` ⟹ the extracted `θ` preserves something" must be stated
explicitly; it is currently nowhere in the library.