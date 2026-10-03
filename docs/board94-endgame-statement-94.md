# Board 94 — ENDGAME-STATEMENT front

Front: board 94, `ENDGAME-STATEMENT`, branch `board/94-endgame`, base `666e849`.

Scope: own the **statement** for the #94 residual, not a proof of the statement
as currently written. Audits read first: `BOARD94-RECONCILE-AUDIT.md` (7dd698e),
`BOARD94-TRIPLE-OBSTRUCTION.md` (26e41ac), `BOARD94-SUPPORT-DICHOTOMY.md`
(2956b55).

Deliverables on this branch:

* `AssemblyP1/BBTAdmissibleObstruction.lean` — the kernel-checked statement
  module, **inside the lake target** `AssemblyP1` (the reconcile audit's H5
  complaint about `scratch/` does not apply to it).
* `scripts/board94_endgame_statement.py` — an **independent** transcription of
  the definitions, written from the Lean sources, not from the existing
  board-94 scripts (two of which the audit found defective).
* `docs/admissible-obstruction-94.md` — the durable note, including §5, the
  named remaining chain to the endpoint.
* `docs/board94-endgame-statement-census.txt` — the census output.
* this file.

Toolchain note: this worktree had no `.lake` at all. To avoid a Mathlib rebuild
(no `lake build`, per instructions) the *prebuilt* `.lake` of the sibling
worktree `/workspace/assemblyp1-94-triple-vacuity` (same HEAD `666e849`) was
copied in by hard link, and `BBTReplacementInvariant.olean` — missing from
every cached `.lake` on this host — was produced with a single
`lake env lean -o` (13.8 s). No dependency tree was built; `Mathlib.olean` was
never touched. All checks below are `lake env lean`, one process at a time.

## 0. The three audit findings, restated as I read them

1. `longObstruction_iff_not_P2 (hL : 2 ≤ L) : LongObstruction hG L S ↔ ¬ P2 hG L S`
   (`BBTReplacementInvariant.lean:419`, kernel-checked, in build). Hence
   `P2 ∧ ¬ LongObstruction` is `P2`, i.e. **satisfiable, not vacuous**, and the
   *unconditional* residual "`P2 → LongObstruction`" is refuted by
   construction.
2. `SelectedTriple` is vacuous on a primitive `Ukkonen` word (census
   `G ≤ 10, L ≤ 4`), so the triple disjunct of `LongObstruction` is not where
   the work is.
3. Therefore the live residual is the interleaved disjunct, and the current
   `LongObstruction` conclusion is simultaneously too weak and redundant on the
   `SelectedTriple` side.

## 1. A correction to the audits, which changes the shape of the answer

Finding 1 does **not** refute `InterleavingObstructionNeeded`
(`BBTReplacementInvariant.lean:620`). That `Prop` concludes `LongObstruction`
under six `θ`-hypotheses — bijective, fibre-preserving, one-cycle, bad,
`¬ SelectedTriple`, `SelectedInterleaved` — and **none of them is
`¬ LongObstruction`**. A statement is refuted by an instance satisfying *all*
its hypotheses; `¬ LongObstruction` is only what the discharger has in hand. So
finding 1 refutes the unconditional shape, not the conditional one. My census
(§5) finds **no** instance of the conditional one either: 0 bad
selected-interleaving one-cycles on any `P2` genome for `G ≤ 6`, `2 ≤ L ≤ 3`
(668 selected interleavings, all good). So the residual is **not** red; it is
mis-*targeted*, in a way that is sharper than the audits state.

## 2. (a) The minimal admissible form

### Which conjunct must be strengthened or replaced: **both, and disjunct-wise**

`LongObstruction` is `(T) ∨ (I)`; `P2` is `¬(T) ∧ ¬(I)` at the same threshold.
So under `2 ≤ L` and `P2`, *every* conclusion taken inside `LongObstruction` is
false — the disjunction **and each disjunct separately**. Kernel-checked at
general `G` and `L`, from the library's own `P2.triple` / `P2.interleaved`:

```lean
theorem P2_not_tripleClause      (hL : 2 ≤ L) (hP2 : P2 hG L S) : ¬ TripleClause hG L S
theorem P2_not_interleavedClause (hL : 2 ≤ L) (hP2 : P2 hG L S) : ¬ InterleavedClause hG L S
theorem P2_refutes_every_conclusion_inside_LongObstruction
    (hL : 2 ≤ L) (hP2 : P2 hG L S) :
    ¬ TripleClause hG L S ∧ ¬ InterleavedClause hG L S ∧ ¬ LongObstruction hG L S
```

This is strictly stronger than the audits' finding (they had the disjunction
only) and it is the real answer to "which conjunct": the residual statement
cannot keep either of them, so the conclusion must leave `LongObstruction`
altogether. This is why the frontend question cannot be answered by a genome
hypothesis: **there is no derivable genome hypothesis that turns a `P2`
genome into a `LongObstruction`**, and no amount of extra genome-side
hypothesis (primitivity, period structure, `Ukkonen`) changes that, because
`longObstruction_iff_not_P2` holds at every `2 ≤ L` with no side conditions.
I say so plainly rather than inventing one.

### The exit that costs least

`Genome.IsRepeat` = `1 ≤ e ∧ e < |D| ∧ a ≠ b ∧ Agree e a b ∧ Preceding a ≠
Preceding b ∧ Following e a ≠ Following e b`. `P2`'s interleaved clause ranges
only over `IsRepeat`, i.e. over **two-sided** maximal repeats. Dropping the
`Preceding`-clause on one constituent puts the statement outside `P2`'s reach
while keeping the `≥ L - 1` threshold, the following-maximality and the
interleaving:

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

In words: **two interleaved doubled `(L-1)`-mers, each extending to the right to
length `≥ L - 1`, at least one of which extends to the left.** (The "doubled"
reading is a consequence, not an extra clause: `admissible_fibres` proves
`vtx a = vtx b ∧ vtx c = vtx d`.)

Why this edit and no other:

* **`Preceding`, not `Following`.** `selectedInterleaved_crux`
  (`BBTReplacementInvariant.lean:272`, kernel-checked) delivers a
  *preceding*-block at the selected starts; `preceding_ne_of_maxBack` is the
  lemma that cannot remove it; the `Following` direction is available from
  `max_of_agrees`. `Preceding`-clause is the only one of the two maximality
  clauses the endgame cannot produce, so dropping it is the minimal edit.
* **Threshold stays `≥ L - 1`.** Raising it also escapes `P2` but throws away
  the agreement the selected interleaving supplies for free. Census: at that
  threshold, `Following`-maximality holds with 0 exceptions under `P2`
  (128/128 pairs, `G ≤ 8`, `2 ≤ L ≤ 4`).
* **`(T)` dropped.** `P2_not_tripleClause` shows it is refuted; independently,
  on a primitive `P2` genome it is *false*, since a triple repeat of length
  `≥ L - 1` exhibits three occurrences of one `(L-1)`-mer, and the census finds
  **0** primitive `P2` words with any `(L-1)`-mer of multiplicity `≥ 3` (388
  primitive `P2` words; 48 non-primitive ones have one). That is also an
  independent confirmation of audit finding 2, on a wider range. **Census, not
  kernel** — the lemma is named as missing in §6 step 3.

Minimality, both directions: `AdmissibleObstruction` is the **strongest**
conclusion not refuted by `P2` among the edits keeping the `≥ L - 1`
thresholds, the interleaving and one maximality clause (census: under `P2`
exactly one maximality clause can fail, and it is always the `Preceding` one —
128 cases, 0 exceptions); and it is not trivially true (128 of 476 `P2` pairs,
912 of all pairs), so the residual remains a real obligation.

It is a **replacement**, not a weakening of the same thing:
`interleavedClause_not_admissible` proves at general `G` that a pair of
interleaved maximal repeats is never preceding-blocked, so `(I)` and
`AdmissibleObstruction` do not entail one another.

## 3. (b) Kernel check

`AssemblyP1/BBTAdmissibleObstruction.lean`, checked with `lake env lean`
(no errors; 7 `unusedSectionVars`-style warnings, no suppression added).
`#print axioms` output:

```
'AssemblyP1.BBTAdmissible.AdmissibleObstruction' does not depend on any axioms
'…P2_refutes_every_conclusion_inside_LongObstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'…P2_not_tripleClause'                → [propext, Classical.choice, Quot.sound]
'…P2_not_interleavedClause'           → [propext, Classical.choice, Quot.sound]
'…longObstruction_iff_clauses'         → [propext, Classical.choice, Quot.sound]
'…interleavedClause_not_admissible'    → [propext, Classical.choice, Quot.sound]
'…admissible_fibres'                   → [propext, Classical.choice, Quot.sound]
'…admissible_block_survives_P2'        → [propext, Classical.choice, Quot.sound]
'…admissible_00101'                    → [propext]
'…P2_and_admissible_00101'             → [propext]
'…P2_implies_longObstruction_false_00101' → [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `axiom`, no `native_decide`, no `unsafe`. The two
`decide`-closed witnesses depend on `propext` only, i.e. they are closed
computations over the concrete word `00101`.

Exact proposition text of the settled statement: the `AdmissibleObstruction`
block quoted in §2 and in `docs/admissible-obstruction-94.md` §2 (identical,
`#print`ed above).

## 4. (c) Non-vacuity, kernel-checked

`S = 00101`, `L = 3`, `P2` (`p2_hG5_S5_L3`), with

```
(a, b, e₁) = (1, 3, 3)   "010" at 1 and 3; Following 3 1 = S₄ = 1 ≠ S₁ = 0
(c, d, e₂) = (2, 4, 2)   "10"  at 2 and 4; Following 2 2 = S₄ = 1 ≠ S₁ = 0
```

four interleaved starts (`1 < 2 < 3 < 4`), with `(c, d)` preceding-blocked
(`S₁ = S₃ = 0`):

```lean
theorem P2_and_admissible_00101 :
    P2 BBTChords.hG5 3 S5b ∧ AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) S5b
```

This is the minimum the front demands: an explicit inhabitant of `P2 ∧
AdmissibleObstruction`. It is also exactly what separates the new statement from
every conclusion inside `LongObstruction`, each of which is refuted at this very
instance (`P2_implies_longObstruction_false_00101`).

## 5. (d) Falsification attempt, run **before** accepting (a)

`scripts/board94_endgame_statement.py`, transcribed from
`SourceFaithfulIs` / `BBTCondense` / `BBTEulerian` / `BBTSupportInvariant` /
`BBTEulerianSearch` / `BBTChords` / `P2` (file-header cites line numbers), not
from `scratch/case1_regime.py` / `case1_p.py`.

| attempted refutation of (a) | range | outcome |
| --- | --- | --- |
| `P2` refutes `AdmissibleObstruction` | `G ≤ 8`, `2 ≤ L ≤ 4`, all binary words | **refuted** as a refutation: 128 `P2` pairs satisfy it; smallest `(5,3,00101)` |
| `AdmissibleObstruction` trivially true under `P2` | same | 128 / 476 — not trivial |
| `(I)`-clause survives `P2` | same | 0 occurrences (as the kernel theorem forces) |
| `(T)`-clause survives `P2` on a **primitive** word | same | 0 of 388 primitive `P2` words |
| a `Following`-blocked (rather than `Preceding`-blocked) variant suffices | same | 0 cases; the `Preceding` clause is the exact one |
| **`InterleavingObstructionNeeded` is refuted** (the strong refutation, which would have made (a) moot) | `G ≤ 6`, `2 ≤ L ≤ 3`, all `P2` genomes, all one-cycles `θ` | **0 bad selected interleavings**; 668 selected interleavings, all good; 636 `SelectedTriple` instances, all on non-primitive `P2` words |

So (a) survives falsification, and the last row is the substantive negative
result: on the audited range the *current* statement is not refuted either, and
the smallest witness of the residual package is `00101` with `θ = θ5`, which is
**good** (`θ5_orbitVertexEq`, kernel-checked). Badness is the only missing
ingredient at the smallest witness.

## 6. (e) The remaining chain to the #89 endpoint — named, not proved

Full text in `docs/admissible-obstruction-94.md` §5. In brief, the endpoint's
only non-kernel input is `BBTEulerian.EulerianCycleObstruction L`, consumed by
`bbtCompleteSpec_of_obstruction` and discharged by
`not_longObstruction_of_Ukkonen hUkk`; the endgame is to prove it for the
primitive-`P2` class. Missing hypotheses, in order:

1. **`θ` bijective**: extract `θ = succOf σ` from a non-rotational
   `EulerianCycle σ` and prove bijectivity (`succOf σ = σ ∘ nextPos ∘ σ⁻¹`,
   a conjugate of a rotation — should be routine, not derived here).
2. **`SupportDichotomy`**: `SelectedTriple θ ∨ SelectedInterleaved θ`; the
   whole Arratia-descent content, unproved.
3. **`¬ SelectedTriple θ` from primitivity + `P2`**: needs the unproved lemma
   "no `(L-1)`-mer of multiplicity `≥ 3` on a primitive `P2` genome"
   (census only, 0 violations in 388 words). Without primitivity the `(T)`
   branch is live and this front's statement is not the whole story.
4. **`SelectedInterleaved θ ⟹ AdmissibleObstruction`**: the new obligation.
   Available kernel inputs: `selectedInterleaved_crux` (a preceding-blocked
   constituent) and `agrees_back` / `BackAgrees_shift` (right-maximality of the
   blocked pair). Unresolved: that the block sits at a pair of length `≥ L - 1`
   whose four starts interleave — exactly the case split of
   `BOARD94-BADNESS-0153.md` §5 (case 1 landing, case 2 both-blocked). Note
   `case1_landing` is refuted per the reconcile audit, so its corrected
   one-place-offset form is the right starting point.
5. **`P2 ∧ bad θ ∧ ¬ SelectedTriple θ ∧ SelectedInterleaved θ → False`** — the
   actual discharger. **It cannot be `P2 ∧ AdmissibleObstruction → False`**,
   because §4 exhibits an instance where both hold; `AdmissibleObstruction` is
   a conclusion and must never appear as a hypothesis of the discharger.
6. `LongObstruction` is never needed again: step 5 yields `False` directly.
7. **The candidate side.** The endpoint is "primitive-`P2` source + primitive-`P2`
   candidate + equal `L`-spectrum ⟹ `RotEquiv`", but
   `bbtCompleteSpec_of_obstruction` assumes `Ukkonen` on the **source** only;
   the candidate enters through `exists_matching`. If a successor wants the
   candidate's `P2` to do work, the transfer must be stated explicitly — it is
   nowhere in the library.

## 7. Verdict

The statement is sharpened and settled, kernel-checked, non-vacuous, and
survives an independent falsification attempt. The endpoint is **not** proved
and cannot be from this statement alone: the live residue is step 4 of §6,
i.e. `SelectedInterleaved θ ⟹ AdmissibleObstruction` together with the
primitivity lemma of step 3. Both are named, neither is proved, and no
`axiom`/`sorry` was introduced to make anything compile.

B94-ENDGAME-NONVACUOUS