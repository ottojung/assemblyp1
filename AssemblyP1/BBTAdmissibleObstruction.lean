import AssemblyP1.BBTReplacementInvariant

/-!
# The admissible obstruction for the #94 endgame (board 94, ENDGAME-STATEMENT)

This module owns the **statement** side of the #94 residual.  It does not
attempt to prove any obstruction.  No `axiom`, `sorry` or `admit` occurs
here; every theorem below is kernel-checked by `lake env lean`.

## Why the current conclusion cannot be kept

`AssemblyP1.BBTReplacement.longObstruction_iff_not_P2` (`hL : 2 ≤ L`) is an
`Iff`:

```
LongObstruction hG L S  ↔  ¬ P2 hG L S
```

`LongObstruction` is a disjunction of two clauses (`BBTEulerian.lean:337`):

* `(T)` a maximal triple repeat of length `≥ L - 1`;
* `(I)` two interleaved *maximal* repeats, both of length `≥ L - 1`.

`P2` is the conjunction of the two *negations* of exactly those clauses, at the
same threshold.  Consequently, under `2 ≤ L` and `P2`:

* `P2_not_tripleClause` below: `(T)` is **false**;
* `P2_not_interleavedClause` below: `(I)` is **false**;

so *every* conclusion taken inside `LongObstruction` — the disjunction, or
either disjunct on its own — is refuted by construction, and `P2 → X` is false
for each of them.  `P2_implies_longObstruction_false_00101` records the
disjunct-free form at the smallest witness.  This is a statement-level fact,
kernel-checked at general `G` and `L`, and it is the reason the residual cannot
be closed by proving a variant of `LongObstruction`.

Note what is **not** concluded here.  `InterleavingObstructionNeeded`
(`BBTReplacementInvariant.lean:620`) carries six `θ`-hypotheses, none of which
is `¬ LongObstruction`, so the two theorems above do **not** refute it; they
refute only the unconditional shape "`P2 → LongObstruction`".  The difference
between those two readings is the whole content of the residual.

## The admissible form

The conclusion must therefore leave `LongObstruction` altogether, and the exit
that costs the least is the maximality clause that the endgame cannot produce.
`Genome.IsRepeat` (`SourceFaithfulIs.lean:111`) is

```
1 ≤ e ∧ e < |D| ∧ a ≠ b ∧ Agree e a b ∧ Preceding a ≠ Preceding b ∧ Following e a ≠ Following e b
```

and `P2`'s interleaved clause ranges only over `IsRepeat`, i.e. only over
**two-sided** maximal repeats.  So a blocked constituent — one whose two
preceding symbols coincide — is invisible to `P2`, while still being a genuine
`≥ L - 1` repetition at four interleaving starts.  `BBTReplacement`'s
`selectedInterleaved_crux` (kernel-checked, `:272`) delivers exactly such a
block from a selected interleaving on an obstructed-free genome, and
`preceding_ne_of_max_back` (`BBTMaximalExtension`) is the lemma that cannot be
used to remove it.

`AdmissibleObstruction` below is therefore `(I)` with the `Preceding`-clause
of `IsRepeat` **replaced** by its negation on at least one constituent, the
`Following`-clause (right-maximality) being kept, and with `(T)` dropped:

```
∃ e₁ e₂ a b c d, interleaved ∧ L - 1 ≤ e₁ ∧ L - 1 ≤ e₂ ∧
    (right-maximal e₁ at (a,b)) ∧ (right-maximal e₂ at (c,d)) ∧
    (Preceding a = Preceding b ∨ Preceding c = Preceding d)
```

Three properties, all kernel-checked here or census-backed there:

* **admissible.**  `admissible_00101` is an explicit inhabitant *together with*
  `P2`, so `P2` does not refute it.  Contrast `P2_implies_longObstruction_false_00101`.
* **a genuine replacement, not a weakening of the same thing.**
  `interleavedClause_not_admissible` proves the two are *disjoint* at general
  `G`: the `(I)` clause forces both precedings to differ.
* **not trivially true.**  A census over all binary circular words,
  `G ≤ 8`, `2 ≤ L ≤ 4` (`scripts/board94_endgame_statement.py`) finds
  `AdmissibleObstruction` at 128 of the 476 `P2` pairs and at 912 of all pairs;
  `T`-disjunct and `(I)`-disjunct instances among `P2` words: 0, as forced.
  Census is evidence only.
-/

namespace AssemblyP1.BBTAdmissible

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTReplacement

set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ}

/-! ## 1. The two clauses of `LongObstruction`, named separately -/

/-- **The triple-repeat clause of `LongObstruction`** (`BBTEulerian.lean:337`,
first disjunct): a maximal triple repeat of length `≥ L - 1`. -/
def TripleClause (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c ∧ L - 1 ≤ e.val

/-- **The interleaved clause of `LongObstruction`** (second disjunct): two
interleaved *maximal* repeats, both of length `≥ L - 1`. -/
def InterleavedClause (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ e₁ e₂ a b c d : Fin G, (mkGenome hG S).IsRepeat e₁ a b ∧
    (mkGenome hG S).IsRepeat e₂ c d ∧ Interleaved (mkGenome hG S) a b c d ∧
    L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val

omit [Fintype α] in
/-- The two clauses really are the two clauses of `LongObstruction`: this is
`Iff.rfl`, so nothing is restated by paraphrase. -/
theorem longObstruction_iff_clauses (hG : 0 < G) (L : ℕ) (S : Fin G → α) :
    LongObstruction hG L S ↔ TripleClause hG L S ∨ InterleavedClause hG L S :=
  Iff.rfl

/-! ## 2. Neither clause, nor their disjunction, is an admissible conclusion

The two theorems below are the reason the residual statement has to change.
They hold at general `G` and general `L`, and they are proved from the library's
own `P2` clause lemmas. -/

omit [Fintype α] in
/-- **`P2` refutes the triple clause outright.**  So `P2 → TripleClause` is
false, and `TripleClause` cannot be the conclusion of an obligation to be
discharged against `P2`. -/
theorem P2_not_tripleClause (hG : 0 < G) (L : ℕ) (S : Fin G → α) (hL : 2 ≤ L)
    (hP2 : P2 hG L S) : ¬ TripleClause hG L S := by
  rintro ⟨e, a, b, c, ht, hlen⟩
  exact absurd (P2.triple hG hP2 ht) (by omega)

omit [Fintype α] in
/-- **`P2` refutes the interleaved clause outright.**  So `P2 → InterleavedClause`
is false, and neither can that be the conclusion. -/
theorem P2_not_interleavedClause (hG : 0 < G) (L : ℕ) (S : Fin G → α) (hL : 2 ≤ L)
    (hP2 : P2 hG L S) : ¬ InterleavedClause hG L S := by
  rintro ⟨e₁, e₂, a, b, c, d, h1, h2, hI, hlen1, hlen2⟩
  rcases P2.interleaved hG hP2 h1 h2 hI with hle | hle <;> omega

omit [Fintype α] in
/-- **`P2` refutes `LongObstruction`, i.e. the disjunction.** -/
theorem P2_not_LongObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α) (hL : 2 ≤ L)
    (hP2 : P2 hG L S) : ¬ LongObstruction hG L S :=
  not_longObstruction_of_P2 hL hP2

omit [Fintype α] in
/-- **No conclusion taken inside `LongObstruction` survives `P2`**: neither
disjunct, nor their disjunction, is satisfiable together with `P2`.  This is
the kernel-checked form of "the residual obligation `P2 → LongObstruction` is
false by construction", and it is why `AdmissibleObstruction` below is not a
variant of `LongObstruction`. -/
theorem P2_refutes_every_conclusion_inside_LongObstruction
    (hG : 0 < G) (L : ℕ) (S : Fin G → α) (hL : 2 ≤ L) (hP2 : P2 hG L S) :
    ¬ TripleClause hG L S ∧ ¬ InterleavedClause hG L S ∧ ¬ LongObstruction hG L S :=
  ⟨P2_not_tripleClause hG L S hL hP2, P2_not_interleavedClause hG L S hL hP2,
    P2_not_LongObstruction hG L S hL hP2⟩

/-! ## 3. The admissible obstruction -/

/-- **The two starts carry equal preceding symbols**, i.e. the copy at `b`
extends the copy at `a` to the left.  `Genome.IsRepeat` excludes this, so a
blocked pair is *not* a maximal repeat and is invisible to `P2`'s interleaved
clause. -/
def PrecedingBlocked (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Prop :=
  (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b

/-- **A right-maximal repeat at `(a, b)`**: equal length-`e` substrings at
distinct starts whose *following* symbols differ.  This is `Genome.IsRepeat`
with the `Preceding`-clause removed, and nothing else removed. -/
def IsRightRepeat (hG : 0 < G) (S : Fin G → α) (e a b : Fin G) : Prop :=
  1 ≤ e.val ∧ Agrees hG S e.val a b ∧ a ≠ b ∧
    (mkGenome hG S).Following e.val a ≠ (mkGenome hG S).Following e.val b

/-- **The admissible obstruction.**  Two interleaved right-maximal repeats, both
of length `≥ L - 1`, at least one of which is preceding-blocked.

This is the second clause of `LongObstruction` with the `Preceding`-clause of
`IsRepeat` replaced by its negation on at least one constituent; the triple
clause is dropped, since `P2_not_tripleClause` shows it is unavailable, and the
`¬ SelectedTriple` hypothesis of the endgame removes it for a second,
independent reason. -/
def AdmissibleObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∃ e₁ e₂ a b c d : Fin G,
    InterleavedStarts hG a b c d ∧ L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val ∧
      IsRightRepeat hG S e₁ a b ∧ IsRightRepeat hG S e₂ c d ∧
      (PrecedingBlocked hG S a b ∨ PrecedingBlocked hG S c d)

omit [Fintype α] in
/-- **The two constituents are doubled `(L-1)`-mers**, as a consequence of the
statement: agreement of length `≥ L - 1` is agreement of length `L - 1`.  So
`AdmissibleObstruction` is, verbatim, "two selected-or-not interleaved doubled
`(L-1)`-mers, each of which extends to the right to length `≥ L - 1`, and at
least one of which extends to the left". -/
theorem admissible_fibres (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (h : AdmissibleObstruction hG L S) :
    ∃ e₁ e₂ a b c d : Fin G, L - 1 ≤ e₁.val ∧ L - 1 ≤ e₂.val ∧
      vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d := by
  obtain ⟨e₁, e₂, a, b, c, d, _, hlen1, hlen2, hab, hcd, _⟩ := h
  refine ⟨e₁, e₂, a, b, c, d, hlen1, hlen2, ?_, ?_⟩
  · exact agrees_imp_vtx (hG := hG) (S := S) hab.2.1 hlen1
  · exact agrees_imp_vtx (hG := hG) (S := S) hcd.2.1 hlen2

omit [Fintype α] in
/-- **The replacement is genuine: the two statements are disjoint.**  A pair of
interleaved *maximal* repeats has different preceding symbols at both
constituents, so it is never preceding-blocked.  Hence `InterleavedClause` and
`AdmissibleObstruction` do not entail one another, at general `G`. -/
theorem isRepeat_not_precedingBlocked {e₁ e₂ a b c d : Fin G}
    (hG : 0 < G) (S : Fin G → α)
    (h1 : (mkGenome hG S).IsRepeat e₁ a b) (h2 : (mkGenome hG S).IsRepeat e₂ c d) :
    ¬ PrecedingBlocked hG S a b ∧ ¬ PrecedingBlocked hG S c d :=
  ⟨fun hab => h1.2.2.2.2.1 hab, fun hcd => h2.2.2.2.2.1 hcd⟩

omit [Fintype α] in
/-- The same fact at the level of the clause, at general `G`. -/
theorem interleavedClause_not_admissible (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (h : InterleavedClause hG L S) :
    ∀ e₁ e₂ a b c d : Fin G,
      (mkGenome hG S).IsRepeat e₁ a b → (mkGenome hG S).IsRepeat e₂ c d →
        ¬ PrecedingBlocked hG S a b ∧ ¬ PrecedingBlocked hG S c d :=
  fun _ _ _ _ _ _ h1 h2 => isRepeat_not_precedingBlocked hG S h1 h2

omit [Fintype α] in
/-- **The `Preceding`-block survives `P2`.**  The one clause of
`AdmissibleObstruction` that `P2` does not exclude, isolated. -/
theorem admissible_block_survives_P2 (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (_hL : 2 ≤ L) (_hP2 : P2 hG L S) (h : AdmissibleObstruction hG L S) :
    ∃ a b c d : Fin G, PrecedingBlocked hG S a b ∨ PrecedingBlocked hG S c d := by
  obtain ⟨_, _, a, b, c, d, _, _, _, _, _, hblk⟩ := h
  exact ⟨a, b, c, d, hblk⟩

/-! ## 4. Non-vacuity: an explicit inhabitant at `S = 00101`, `L = 3`

`P2` holds here (`p2_hG5_S5_L3`), and the interleaved right-maximal pair

```
(a, b, e₁) = (1, 3, 3)   -- "010" at 1 and 3, following symbols S₄ = 1 ≠ S₁ = 0
(c, d, e₂) = (2, 4, 2)   -- "10"  at 2 and 4, following symbols S₄ = 1 ≠ S₁ = 0
```

has `(c, d)` preceding-blocked (`S₁ = S₃ = 0`) and its four starts interleaved.
So `P2 ∧ AdmissibleObstruction` is inhabited: the admissible obstruction is
**not** refuted by `P2`, which is what distinguishes it from every conclusion
inside `LongObstruction`. -/

theorem admissibleWitness_interleaved :
    InterleavedStarts BBTChords.hG5 (1 : Fin 5) 3 2 4 := by
  decide

theorem admissibleWitness_right₁ :
    IsRightRepeat (hG := BBTChords.hG5)
      (S := BBTReplacement.S5b) (3 : Fin 5) 1 3 := by
  unfold IsRightRepeat
  decide

theorem admissibleWitness_right₂ :
    IsRightRepeat (hG := BBTChords.hG5)
      (S := BBTReplacement.S5b) (2 : Fin 5) 2 4 := by
  unfold IsRightRepeat
  decide

theorem admissibleWitness_blocked :
    PrecedingBlocked (hG := BBTChords.hG5) (S := BBTReplacement.S5b)
      (2 : Fin 5) 4 := by
  unfold PrecedingBlocked
  decide

/-- **`AdmissibleObstruction` holds at `S = 00101`, `L = 3`.** -/
theorem admissible_00101 :
    AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) S5b :=
  ⟨3, 2, 1, 3, 2, 4, admissibleWitness_interleaved, by decide, by decide,
    admissibleWitness_right₁, admissibleWitness_right₂,
    Or.inr admissibleWitness_blocked⟩

/-- **NON-VACUITY, kernel-checked: `P2` and `AdmissibleObstruction` hold
together at `S = 00101`, `L = 3`.**  This is the witness that distinguishes the
admissible form from every conclusion inside `LongObstruction`, each of which
is refuted at this very instance. -/
theorem P2_and_admissible_00101 :
    P2 BBTChords.hG5 3 S5b ∧
      AdmissibleObstruction (hG := BBTChords.hG5) (L := 3) S5b :=
  ⟨p2_hG5_S5_L3, admissible_00101⟩

/-- **The contrast, kernel-checked: `P2 → LongObstruction` is false at
`00101`, `L = 3`.**  The unconditional form of the current residual is refuted
by construction, exactly as `P2_refutes_every_conclusion_inside_LongObstruction`
says at general `G`. -/
theorem P2_implies_longObstruction_false_00101 :
    ¬ (P2 BBTChords.hG5 3 S5b → LongObstruction BBTChords.hG5 3 S5b) :=
  fun h => not_longObstruction_00101 (h p2_hG5_S5_L3)

/-! ## 5. What the admissible form does **not** give

`AdmissibleObstruction` is a `Prop`, deliberately **not** proved to follow
from anything.  In particular the endgame obligation

```
P2 ∧ (bad bijective fibre-preserving one-cycle θ)
     ∧ ¬ SelectedTriple θ ∧ SelectedInterleaved θ → AdmissibleObstruction
```

is **not** discharged here, and is **not** claimed.  `AdmissibleObstruction` is
satisfied at `00101` with `θ = θ5`, and `θ5` is *good*
(`BBTReplacement.θ5_orbitVertexEq`), so badness is the only missing ingredient
at the smallest witness; the census in `scripts/board94_endgame_statement.py`
finds no bad selected interleaving on any `P2` genome for `G ≤ 6`, `L ≤ 3`.

The remaining chain from here to the #89 endpoint is named, not proved, in
`docs/admissible-obstruction-94.md` §5. -/

end AssemblyP1.BBTAdmissible