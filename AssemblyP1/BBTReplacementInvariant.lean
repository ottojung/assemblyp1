import AssemblyP1.BBTSupportInvariant

/-!
# Audit of the `S = 001011`, `L = 3` candidate for the replacement invariant (issue #89)

## Status of this module: an audit, not an invariant

This file previously asserted `p2_hG6_S6_L3 : P2 hG6 3 S6` and built a
refutation of the bad-`θ` variant of `SelectedInterleaved_obstruction` on it.
**That `P2` hypothesis is false**, and is refuted below, kernel-checked.  The
refutation asserted by the earlier version of this file was therefore never
established; the file had never compiled, for this reason and not for a memory
reason (see `docs/bbt-replacement-invariant-host-constraint.md` for the
correction).

What survives at `S = 001011` is recorded faithfully here.  What does *not*
survive is stated as not surviving.  In particular:

- the candidate replacement invariant

  ```text
  bad θ  ⟹  SelectedInterleaved θ  ⟹  LongObstruction
  ```

  is **not** refuted by this instance, because `LongObstruction` holds here
  (`longObstruction_S6_L3`).  Its status is unchanged from front 9412's
  `selectedInterleaved_obstruction_false_00101`: open.

## Why the instance is self-refuting

`S = 001011` has two doubled `(L-1) = 2`-mers whose starts interleave:

```text
01 repeats at starts 1, 3
10 repeats at starts 2, 5
```

The four starts `1 < 2 < 3 < 5` alternate around the circle, and both
constituents have length `2 > L - 2 = 1`.  This is precisely the second
clause of `P2`, and precisely what `SelectedInterleaved` asks for.  The module's
own witness `T6` needs `SelectedInterleaved`, so at `L = 3` the mechanism that
would certify the counterexample is the very mechanism that disqualifies the
genome from being `P2`.  `001011` is exactly the shape of genome that
`AssemblyP1.InterleavingNeededCounterexample` exists to talk about.

## Cost notes (measured on this host, 2026-10-02)

Every `decide` here is over a *fixed* witness or a *fixed* vertex.  The
`6^6 = 46 656`-fold enumeration is not reintroduced anywhere: `SelectedTriple`
is `∃ v, 3 ≤ (fibre v).card ∧ Selects θ v`, so `no_triple_mult_001011` takes the
witness and splits over the four `(L-1) = 2`-tuples.  Whole-file elaboration
via `lake env lean` measures 3.4 s and well under 1 GiB.
-/

namespace AssemblyP1.BBTReplacement

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTSupport

set_option linter.unusedSectionVars false

/-- `0 < 6`, so that the numerals of the instance fix the length. -/
theorem hG6 : 0 < 6 := by decide

/-- **The candidate word `S = 001011`.** -/
def S6 : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

/-- **The candidate successor map** `θ = [3,5,1,4,2,0]` on `Fin 6`.
Its orbit from the origin is `0, 3, 4, 2, 1, 5`, a single six-cycle. -/
def T6 : Fin 6 → Fin 6 := ![3, 5, 1, 4, 2, 0]

instance : NeZero (mkGenome hG6 S6).len := ⟨by norm_num [mkGenome]⟩

/-! ## 1. The refutation of the `P2` hypothesis, kernel-checked -/

/-- **The witness that kills the instance.** `01` is a maximal repeat of length
`2` at starts `1` and `3`; `10` is a maximal repeat of length `2` at starts `2`
and `5`; the four starts interleave around the circle. -/
theorem interleaved_pair_001011 :
    (mkGenome hG6 S6).IsRepeat 2 1 3 ∧
      (mkGenome hG6 S6).IsRepeat 2 2 5 ∧
      Interleaved (mkGenome hG6 S6) 1 3 2 5 := by
  unfold mkGenome Genome.IsRepeat Genome.Agree Genome.window Genome.Preceding
    Genome.Following Interleaved FourDistinct InOpenArc Genome.cycl
  decide

/-- **`S = 001011` does NOT satisfy `P2` at `L = 3`, kernel-checked.**
The first clause (no maximal triple repeat of length `≥ L - 1 = 2`) is fine; the
second fails, witnessed by `interleaved_pair_001011`: both constituents have
length `2`, and `¬ (2 ≤ L - 2 = 1)`.

This is the refutation of `p2_hG6_S6_L3` as previously asserted in this file. -/
theorem not_P2_001011_L3 : ¬ P2 hG6 3 S6 := by
  rintro ⟨-, h2⟩
  obtain ⟨h1, h2', h3⟩ := interleaved_pair_001011
  exact absurd (h2 2 2 1 3 2 5 h1 h2' h3) (by decide)

/-- **The positive form of the same fact: `S = 001011` HAS a long obstruction
at `L = 3`**, with the interleaved pair above as the explicit witness.

Consequence: `¬ LongObstruction hG6 3 S6` is **false** here.  Any refutation of
a conditional that concludes in `LongObstruction` needs `¬ LongObstruction` at
its witness genome, so this instance cannot serve as that witness. -/
theorem longObstruction_001011 : LongObstruction hG6 3 S6 := by
  obtain ⟨h1, h2, h3⟩ := interleaved_pair_001011
  exact Or.inr ⟨2, 2, 1, 3, 2, 5, h1, h2, h3, by decide, by decide⟩

/-! ## 2. What survives at this instance -/

/-- **`θ = T6` is a bijective, fibre-preserving, one-cycle successor map, and
it is BAD**: its spelled vertex cycle `00, 01, 11, 10, 01, 10` is not a cyclic
shift of the truth's `00, 01, 10, 01, 11, 10`.

This is the clause that `BBTSupportInvariant.harmless_selected_crossing_00101`
lacks: there the crossing `θ` was *good*, so `SupportDichotomy` never applied to
it.  Here `θ` is genuinely bad, so it *is* in the scope of `SupportDichotomy`. -/
theorem bad_001011 :
    Function.Bijective T6 ∧
      FibrePreserving (hG := hG6) (L := 3) S6 T6 ∧
      OneCycle hG6 T6 ∧
      ¬ OrbitVertexEq (hG := hG6) (L := 3) S6 T6 := by
  decide

/-- **`T6` is a *selected* interleaving**: the interleaved pair
`01 ↦ {1,3}`, `10 ↦ {2,5}` is rematched. -/
theorem selectedInterleaved_T6 :
    SelectedInterleaved (hG := hG6) (L := 3) S6 T6 := by
  decide

/-- **No `(L-1)`-mer of `S = 001011` at `L = 3` has multiplicity `≥ 3`.**
The fibres are `00 ↦ {0}`, `01 ↦ {1,3}`, `10 ↦ {2,5}`, `11 ↦ {4}`, so the
`(T)` clause of `SupportDichotomy` is vacuous at this instance for every `θ`.

**Proof note.**  This was originally closed by `decide` over all `6^6`
candidate `θ`, which is a pathological elaboration (measured at 13.84 GiB and
SIGKILLed).  Since `SelectedTriple` is an `∃ v, 3 ≤ (fibre v).card ∧ Selects θ v`,
we instead introduce the existential witness and discharge each of the four
`(L-1) = 2`-tuples by `fin_cases` plus a small `decide` on the fibre
cardinality.  This is a four-fold case split, not a `6^6` enumeration. -/
theorem no_triple_mult_001011 :
    ∀ θ : Fin 6 → Fin 6, ¬ SelectedTriple (hG := hG6) (L := 3) S6 θ := by
  intro θ
  rintro ⟨v, hcard, _⟩
  fin_cases v <;> exact absurd hcard (by decide)

/-- **The support dichotomy itself holds at this instance**, witnessed by the
bad `θ = T6`: the `(T)` disjunct is unavailable for all `θ`, and `(I)` holds at
`T6`. -/
theorem supportDichotomy_T6 :
    SelectedTriple (hG := hG6) (L := 3) S6 T6 ∨
      SelectedInterleaved (hG := hG6) (L := 3) S6 T6 :=
  Or.inr selectedInterleaved_T6

/-- **Anti-vacuity of the surviving facts, and their limit.** `UniqueAt` at this
instance is **false**: `S = 001011` admits a bijective, fibre-preserving,
one-cycle `θ` whose spelled vertex cycle is not the truth's.  Via
`AssemblyP1.BBTEulerianSearch.uniqueAt_iff_orbit` (an `Iff`).

This is stated so that no reader can mistake the surviving facts for evidence
against `thm:BBT`, and it is exactly why they are *not* evidence for `#89`
either.  `BBTCompleteSpectrumUniqueness` is a statement about the complete
`L`-spectrum; `UniqueAt` quantifies over all one-cycle fibre-preserving
permutations of the *starts*, a strictly larger class.  The genome here also
has a `LongObstruction` (`longObstruction_001011`), so it is outside
`thm:BBT`'s hypothesis by construction. -/
theorem not_uniqueAt_001011 : ¬ UniqueAt hG6 3 S6 := by
  rw [uniqueAt_iff_orbit]
  intro h
  obtain ⟨hbi, hfp, hoc, hbad⟩ := bad_001011
  exact hbad (h T6 hbi hfp hoc)

/-! ## 3. What a genuine refutation of the candidate would need

Stated as a `Prop`, deliberately **not** proved and **not** claimed.  This is
the shape of witness a future refutation has to exhibit: a `P2` genome at which
a *bad* `θ` is a selected interleaving.  Front 9412 supplied the good-`θ`
version on `00101`; this file's earlier version tried to supply the bad-`θ`
version on `001011`, which is not `P2` and so does not.

Note the hypothesis `¬ LongObstruction` is redundant but kept explicit, since
`P2` gives it (`AssemblyP1.BBTEulerian.not_longObstruction_of_P2`) only via the
`2 ≤ L` side condition, and stating it keeps the intended use visible. -/
def BadSelectedInterleavingWitness : Prop :=
  ∃ (G : ℕ) (L : ℕ) (S : Fin G → Fin 2) (hG : 0 < G) (θ : Fin G → Fin G),
    P2 hG L S ∧ ¬ LongObstruction hG L S ∧
      Function.Bijective θ ∧ FibrePreserving (hG := hG) (L := L) S θ ∧
      OneCycle hG θ ∧ ¬ OrbitVertexEq (hG := hG) (L := L) S θ ∧
      SelectedInterleaved (hG := hG) (L := L) S θ

/-! ## 4. The reduction of the candidate invariant (front B94-INV-2600)

Everything above is an audit of one instance.  This section is the *general*
content: what the candidate replacement invariant reduces to, proved in the
kernel, plus the exact remaining obligation.

### 4.1 The statement, in the form that is true

The **raw** form, with no `θ` and no selection at all,

```text
SelectedInterleaved θ  ⟹  LongObstruction          -- `SelectedInterleaved_obstruction`
```

is **false**, kernel-checked: `BBTSupport.selectedInterleaved_obstruction_false_00101`
exhibits `θ = nextPos` on `S = 00101` at `L = 3`, where `SelectedInterleaved`
holds and `LongObstruction` fails; `00101` is `P2`, hence `Ukkonen`.  (Front
`BOARD94-BOUNDED-ELAB-2315` additionally reports the raw extension failing in
768 of 1024 generated instances; that is a Python count, evidence only.)

The form this front proves progress on is the **selected, blocked-pair**
statement.  Two halves of it are proved below, in the kernel:

* `interleaved_maximal_pair`: two interleaved doubled `(L-1)`-mers whose
  *preceding* symbols both differ already extend to two interleaved maximal
  repeats of length `≥ L-1`, i.e. to the second disjunct of `LongObstruction`.
  No `θ`, no selection: this is `BBTMaximalExtension.maximalRepeat_of_branch`
  applied twice.
* `selectedInterleaved_crux`: consequently a selected interleaving at a genome
  with **no** long obstruction has a *preceding-blocked* constituent --- one of
  the two pairs of selected starts carries the same preceding symbol, so the
  maximal extension is unavailable at that pair.
* `selectedInterleaved_coincides_selectedTriple`: if the two constituents of a
  selected interleaving are the *same* condensed vertex, then all four starts
  lie in one fibre, that vertex has multiplicity `≥ 4 ≥ 3` and is rematched,
  so `SelectedTriple` holds.

So the `(I)` clause of `SupportDichotomy` is load-bearing in exactly one
configuration: **two distinct interleaved fibres, both rematched, at least one
of them preceding-blocked at its two selected starts.**  Everything else is
discharged by the `(T)` clause or is a `LongObstruction` outright.

### 4.2 The remaining obligation, named

`BadSelectedInterleavingRemaining` below is the residual content: a bad,
bijective, fibre-preserving, one-cycle `θ` that selects two *distinct*
interleaved fibres, at least one of them preceding-blocked, must still force a
`LongObstruction` (through its first disjunct, a maximal triple repeat of length
`≥ L-1`).  It is stated as a `Prop` and **not proved**: no `axiom`, no `sorry`,
no `admit`. -/
section Reduction

open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **Rung 1, proved.**  Two interleaved doubled `(L-1)`-mers whose preceding
symbols both differ extend to two interleaved maximal repeats of length
`≥ L-1`: the second disjunct of `LongObstruction`.  Only
`BBTMaximalExtension.maximalRepeat_of_branch` and `BBTSupport.interleaved_iff`
are used. -/
theorem interleaved_maximal_pair {a b c d : Fin G}
    (hL : 2 ≤ L) (hab : a ≠ b) (hcd : c ≠ d)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hpa : (mkGenome hG S).Preceding a ≠ (mkGenome hG S).Preceding b)
    (hpc : (mkGenome hG S).Preceding c ≠ (mkGenome hG S).Preceding d)
    (hIA : Interleaved (mkGenome hG S) a b c d) :
    LongObstruction hG L S := by
  obtain ⟨e₁, he₁, hl₁⟩ := maximalRepeat_of_branch (α := α) hG S hL hab hva hpa
  obtain ⟨e₂, he₂, hl₂⟩ := maximalRepeat_of_branch (α := α) hG S hL hcd hvc hpc
  exact Or.inr ⟨e₁, e₂, a, b, c, d, he₁, he₂, hIA, hl₁, hl₂⟩

/-- **Rung 2, proved.**  Hence a selected interleaving at a genome with no long
obstruction has a preceding-blocked constituent.  This is the reduction that
replaces the false raw "selected interleaving extends to interleaved maximal
repeats": the extension is available unless one constituent is blocked, and
the block is located. -/
theorem selectedInterleaved_crux {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hS : SelectedInterleaved (hG := hG) (L := L) S θ)
    (hno : ¬ LongObstruction hG L S) :
    ∃ a b c d : Fin G,
      Interleaved (mkGenome hG S) a b c d ∧
        vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d ∧
        ((mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b ∨
          (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d) := by
  obtain ⟨a, b, c, d, hFDh, hva, hvc, _, _⟩ := hS
  have hIA : Interleaved (mkGenome hG S) a b c d := (interleaved_iff hG S a b c d).2 hFDh
  by_cases hpa : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b
  · exact ⟨a, b, c, d, hIA, hva, hvc, Or.inl hpa⟩
  · by_cases hpc : (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d
    · exact ⟨a, b, c, d, hIA, hva, hvc, Or.inr hpc⟩
    · exact absurd (interleaved_maximal_pair (hL := hL) (hab := hFDh.1.1)
        (hcd := hFDh.1.2.2.2.2.2) (hva := hva) (hvc := hvc) (hpa := hpa)
        (hpc := hpc) (hIA := hIA)) hno

/-- Four distinct elements of a finite type witness a cardinality bound. -/
theorem four_distinct_card {X : Type} [Fintype X] (f : Fin 4 → X)
    (h : Function.Injective f) : 4 ≤ Fintype.card X :=
  Fintype.card_le_of_injective f h

/-- **Rung 3, proved.**  If the two constituents of a selected interleaving are
the *same* condensed vertex, then the four selected starts lie in one fibre of
multiplicity `≥ 4 ≥ 3`, and that vertex is rematched, so `SelectedTriple`
holds.  This retires the degenerate configuration of the `(I)` clause. -/
theorem selectedInterleaved_coincides_selectedTriple {θ : Fin G → Fin G}
    {a b c d : Fin G}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hs1 : Selects hG L S θ (vtx hG L S a))
    (hvceq : vtx hG L S a = vtx hG L S c) :
    SelectedTriple (hG := hG) (L := L) S θ := by
  refine ⟨vtx hG L S a, ?_, hs1⟩
  let f : Fin 4 → fibre hG L S (vtx hG L S a) :=
    fun i => if i.val = 0 then ⟨a, (mem_fibre hG L S).mpr rfl⟩ else
      if i.val = 1 then ⟨b, (mem_fibre hG L S).mpr hva.symm⟩ else
      if i.val = 2 then ⟨c, (mem_fibre hG L S).mpr hvceq.symm⟩ else
      ⟨d, (mem_fibre hG L S).mpr (hvc.symm.trans hvceq.symm)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hval := congrArg Subtype.val hxy
    fin_cases x <;> fin_cases y <;>
      simp_all [f, hva, hvceq, hvc, hab, hac, had, hbc, hbd, hcd]
  have h4 : 4 ≤ (fibre hG L S (vtx hG L S a)).card := by
    simpa using (four_distinct_card f hf)
  omega

/-- **The consolidated crux, proved.**  At a genome with no long obstruction a
selected interleaving is of exactly two kinds: either its two constituents are
the same condensed vertex, in which case `SelectedTriple` holds, or they are
*distinct* vertices and one of them is preceding-blocked at its two selected
starts.  These two configurations are the whole remaining content of the `(I)`
clause; nothing else is left for it. -/
theorem selectedInterleaved_crux_or_triple {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hS : SelectedInterleaved (hG := hG) (L := L) S θ)
    (hno : ¬ LongObstruction hG L S) :
    SelectedTriple (hG := hG) (L := L) S θ ∨
      ∃ a b c d : Fin G,
        Interleaved (mkGenome hG S) a b c d ∧
          vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d ∧
          vtx hG L S a ≠ vtx hG L S c ∧
          ((mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b ∨
            (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d) := by
  obtain ⟨a, b, c, d, hFDh, hva, hvc, hs1, _⟩ := hS
  have hIA : Interleaved (mkGenome hG S) a b c d := (interleaved_iff hG S a b c d).2 hFDh
  by_cases hceq : vtx hG L S a = vtx hG L S c
  · exact Or.inl (selectedInterleaved_coincides_selectedTriple (θ := θ) (a := a) (b := b) (c := c) (d := d)
      (hab := hFDh.1.1) (hac := hFDh.1.2.1) (had := hFDh.1.2.2.1) (hbc := hFDh.1.2.2.2.1)
      (hbd := hFDh.1.2.2.2.2.1) (hcd := hFDh.1.2.2.2.2.2) (hva := hva) (hvc := hvc)
      (hs1 := hs1) (hvceq := hceq))
  · by_cases hpa : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b
    · exact Or.inr ⟨a, b, c, d, hIA, hva, hvc, hceq, Or.inl hpa⟩
    · by_cases hpc : (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d
      · exact Or.inr ⟨a, b, c, d, hIA, hva, hvc, hceq, Or.inr hpc⟩
      · exact absurd (interleaved_maximal_pair (hL := hL) (hab := hFDh.1.1)
          (hcd := hFDh.1.2.2.2.2.2) (hva := hva) (hvc := hvc) (hpa := hpa)
          (hpc := hpc) (hIA := hIA)) hno

/-- **The remaining obligation, stated and not proved.**  Rungs 1–3 leave
exactly one configuration for the `(I)` clause of `SupportDichotomy`: a bad
`θ` selecting two **distinct** interleaved fibres, at least one of them
preceding-blocked at its two selected starts.  Closing
`SelectedInterleaved_obstruction` for that configuration --- i.e. forcing a
`LongObstruction`, necessarily through its first disjunct, a maximal triple
repeat of length `≥ L-1` --- is what this front did not prove.

No `axiom`, `sorry` or `admit` occurs below; this is a `Prop`, not a proof. -/
def BadSelectedInterleavingRemaining : Prop :=
  ∃ (G : ℕ) (L : ℕ) (S : Fin G → Fin 2) (hG : 0 < G) (θ : Fin G → Fin G),
    2 ≤ L ∧ P2 hG L S ∧
      Function.Bijective θ ∧ FibrePreserving (hG := hG) (L := L) S θ ∧
      OneCycle hG θ ∧ ¬ OrbitVertexEq (hG := hG) (L := L) S θ ∧
      ¬ SelectedTriple (hG := hG) (L := L) S θ ∧
      SelectedInterleaved (hG := hG) (L := L) S θ ∧
      ¬ LongObstruction hG L S

end Reduction

/-! ## 5. The surviving configuration in the rematching language (front
B94-REM-2600)

Front `B94-INV-2600` reduced the `(I)` clause of `SupportDichotomy` to two
distinct interleaved fibres with a preceding-blocked constituent.  This
section adds three things.

* **§5.1 `P2` and `¬ LongObstruction` are the same hypothesis.**  The two
genome-side clauses of `BadSelectedInterleavingRemaining` are mutually
redundant (`longObstruction_iff_not_P2`), so the obligation is worth exactly
as much as its `¬ LongObstruction` clause alone: no `P2` has to be assumed
separately, and conversely no extra strength is lost by keeping it.

* **§5.2 the rematching permutation `ρ = nextPos⁻¹ ∘ θ`**, together with the
shift classes `shiftClass v = prevPos (fibre v)`.  `ρ` is a permutation of the
starts, it preserves every shift class, and `Selects v` is exactly
nontriviality of `ρ` on the fibre of `v` (`selects_iff_rematch`).  This is
the first structural description of a *bad* `θ` that does not mention
interleaving at all: the badness lives entirely in `ρ`.

* **§5.3 the surviving configuration**, `crux_rematchShape`: at
`¬ SelectedTriple` the two constituents of a selected interleaving are
*distinct* vertices each of multiplicity exactly **two**, one of them
preceding-blocked, and `ρ` moves a start of each of the two two-element
fibres.  Together with §5.1 this is a strictly sharper statement of the
remaining obligation than the previous front's.

The obligation itself is **not** closed here; §5.4 names what is left. -/

section Rematching

open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **`Ukkonen` implies `P2`**: the two clauses are the same repeat statements
at adjacent thresholds. -/
theorem ukkonen_imp_P2 (hL : 2 ≤ L) (h : Ukkonen hG L S) : P2 hG L S :=
  ⟨h.1, fun e₁ e₂ a b c d h1 h2 h3 =>
    match h.2 e₁ e₂ a b c d h1 h2 h3 with
    | Or.inl h1' => Or.inl (by omega)
    | Or.inr h2' => Or.inr (by omega)⟩

/-- **`P2` and `LongObstruction` exclude exactly each other at `2 ≤ L`.**
This makes the two genome-side hypotheses of
`BadSelectedInterleavingRemaining` mutually redundant: that obligation is
worth exactly as much as its `¬ LongObstruction` clause alone. -/
theorem longObstruction_iff_not_P2 (hL : 2 ≤ L) : LongObstruction hG L S ↔ ¬ P2 hG L S := by
  constructor
  · intro h hP2; exact not_longObstruction_of_P2 hL hP2 h
  · intro hP2
    exact (longObstruction_iff_not_Ukkonen (S := S)).mpr
      (fun hU => hP2 (ukkonen_imp_P2 hG L S hL hU))

/-! ## The rematching permutation and the shift classes -/

/-- One position back is injective on the circle. -/
theorem prevPos_injective : Function.Injective (prevPos hG) := by
  intro x y hxy
  calc x = nextPos hG (prevPos hG x) := (nextPrev _ _).symm
    _ = nextPos hG (prevPos hG y) := by rw [hxy]
    _ = y := nextPrev _ _

/-- **The shift class of `v`**: `prevPos (fibre v)`, the starts from which the
traversal must enter `v`. -/
def shiftClass (v : Fin (L - 1) → α) : Finset (Fin G) := (fibre hG L S v).image (prevPos hG)

theorem mem_shiftClass {v : Fin (L - 1) → α} {x : Fin G} :
    x ∈ shiftClass hG L S v ↔ nextPos hG x ∈ fibre hG L S v := by
  constructor
  · intro hx
    rw [shiftClass] at hx
    have hx' := Finset.mem_image.mp hx
    obtain ⟨y, hy, hxy⟩ := hx'
    rw [← hxy, nextPrev]
    exact hy
  · intro h
    rw [shiftClass]
    exact Finset.mem_image.mpr ⟨nextPos hG x, h, prevNext hG x⟩

theorem card_shiftClass (v : Fin (L - 1) → α) :
    (shiftClass hG L S v).card = (fibre hG L S v).card :=
  Finset.card_image_of_injective _ (prevPos_injective hG)

/-- The **rematching permutation** `ρ = nextPos⁻¹ ∘ θ`. -/
def rematch (θ : Fin G → Fin G) (x : Fin G) : Fin G := prevPos hG (θ x)

theorem rematch_nextPos (θ : Fin G → Fin G) (x : Fin G) : nextPos hG (rematch hG θ x) = θ x :=
  nextPrev _ _

/-- `ρ` is injective. -/
theorem rematch_injective {θ : Fin G → Fin G} (hθ : Function.Injective θ) :
    Function.Injective (rematch hG θ) := by
  intro x y h
  exact hθ (by simpa only [rematch_nextPos] using congrArg (nextPos hG) h)

/-- `ρ` preserves every shift class. -/
theorem mem_rematch_shiftClass {θ : Fin G → Fin G} (hθ : FibrePreserving (hG := hG) (L := L) S θ)
    (v : Fin (L - 1) → α) {x : Fin G} (hx : x ∈ shiftClass hG L S v) : rematch hG θ x ∈ shiftClass hG L S v := by
  have hx' : nextPos hG x ∈ fibre hG L S v := (mem_shiftClass hG L S).mp hx
  refine (mem_shiftClass hG L S).mpr ?_
  refine (mem_fibre (hG := hG) (L := L) (S := S) (v := v)).mpr ?_
  change vtx hG L S (nextPos hG (prevPos hG (θ x))) = v
  rw [nextPrev, hθ x]
  exact (mem_fibre (hG := hG) (L := L) (S := S) (v := v)).mp hx' 

/-- **Rematching is nontriviality of `ρ` on the fibre.** -/
theorem selects_iff_rematch {θ : Fin G → Fin G} (v : Fin (L - 1) → α) :
    Selects (hG := hG) (L := L) S θ v ↔
      ∃ x, x ∈ fibre hG L S v ∧ rematch hG θ x ≠ x := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun hc => ?_⟩
    have h1 := nextPrev hG (θ x)
    simp only [rematch] at hc
    rw [hc] at h1
    exact h h1.symm
  · rintro ⟨x, hx, hc⟩
    refine ⟨x, hx, fun he => ?_⟩
    simp only [rematch] at hc
    exact hc (by rw [he, prevNext])

/-! ## Cardinality bookkeeping -/

theorem card_ge_two {X : Type} [Fintype X] {s : Finset X} {a b : X}
    (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) : 2 ≤ s.card := by
  let f : Fin 2 → ↥s := fun i => if i.val = 0 then ⟨a, ha⟩ else ⟨b, hb⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    fin_cases x <;> fin_cases y <;> simp_all [f]
  simpa using (Fintype.card_le_of_injective f hf)

theorem card_ge_three {X : Type} [Fintype X] {s : Finset X} {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : 3 ≤ s.card := by
  let f : Fin 3 → ↥s := fun i =>
    if i.val = 0 then ⟨a, ha⟩ else if i.val = 1 then ⟨b, hb⟩ else ⟨c, hc⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    fin_cases x <;> fin_cases y <;> simp_all [f]
  simpa using (Fintype.card_le_of_injective f hf)

theorem card_ge_three_ne {X : Type} [Fintype X] {s : Finset X} {a b w : X}
    (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (ha : a ∈ s) (hb : b ∈ s) (hw : w ∈ s) : 3 ≤ s.card := by
  let f : Fin 3 → ↥s := fun i =>
    if i.val = 0 then ⟨a, ha⟩ else if i.val = 1 then ⟨b, hb⟩ else ⟨w, hw⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    fin_cases x <;> fin_cases y <;> simp_all [f]
  simpa using (Fintype.card_le_of_injective f hf)

/-- **The two constituents of a selected interleaving at `¬ SelectedTriple` are
distinct vertices of fibre cardinality exactly two.** -/
theorem selectedInterleaving_fibreSize {θ : Fin G → Fin G} {a b c d : Fin G}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hs1 : Selects (hG := hG) (L := L) S θ (vtx hG L S a))
    (hs2 : Selects (hG := hG) (L := L) S θ (vtx hG L S c))
    (hnT : ¬ SelectedTriple (hG := hG) (L := L) S θ) :
    vtx hG L S a ≠ vtx hG L S c ∧
      (fibre hG L S (vtx hG L S a)).card = 2 ∧ (fibre hG L S (vtx hG L S c)).card = 2 := by
  have hmem (x : Fin G) (v : Fin (L - 1) → α) (h : vtx hG L S x = v) : x ∈ fibre hG L S v :=
    (mem_fibre (hG := hG) (L := L) (S := S)).mpr h
  have hneq : vtx hG L S a ≠ vtx hG L S c := by
    intro h
    have h3 : 3 ≤ (fibre hG L S (vtx hG L S a)).card :=
      card_ge_three hab hac hbc (hmem a _ rfl) (hmem b _ hva.symm) (hmem c _ h.symm)
    exact hnT ⟨vtx hG L S a, h3, hs1⟩
  refine ⟨hneq, ?_, ?_⟩
  · have hlo := card_ge_two hab (hmem a _ rfl) (hmem b _ hva.symm)
    have hhi : (fibre hG L S (vtx hG L S a)).card ≤ 2 := by
      by_contra hc
      exact hnT ⟨vtx hG L S a, by omega, hs1⟩
    omega
  · have hlo := card_ge_two hcd (hmem c _ rfl) (hmem d _ hvc.symm)
    have hhi : (fibre hG L S (vtx hG L S c)).card ≤ 2 := by
      by_contra hc
      exact hnT ⟨vtx hG L S c, by omega, hs2⟩
    omega


theorem card_two_two_mem {X : Type} [Fintype X] {s : Finset X} {a b x : X}
    (hcard : s.card = 2) (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) (hx : x ∈ s) :
    x = a ∨ x = b := by
  by_contra hne
  push_neg at hne
  exact absurd (card_ge_three_ne hab hne.1.symm hne.2.symm ha hb hx) (by omega)

/-- **The surviving configuration, in the `ρ` language.**  At
`¬ SelectedTriple`, a selected interleaving is two *distinct* interleaved
fibres, each of multiplicity exactly two, at least one of them
preceding-blocked at its two selected starts; and `ρ = nextPos⁻¹ ∘ θ` moves at
least one of the four selected starts --- that is where the badness lives. -/
theorem crux_rematchShape {θ : Fin G → Fin G} (hL : 2 ≤ L)
    (hSel : SelectedInterleaved (hG := hG) (L := L) S θ)
    (hno : ¬ LongObstruction hG L S) (hnT : ¬ SelectedTriple (hG := hG) (L := L) S θ) :
    ∃ a b c d : Fin G,
      Interleaved (mkGenome hG S) a b c d ∧
        vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d ∧
        vtx hG L S a ≠ vtx hG L S c ∧
        (fibre hG L S (vtx hG L S a)).card = 2 ∧
        (fibre hG L S (vtx hG L S c)).card = 2 ∧
        ((mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b ∨
          (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d) ∧
        (rematch hG θ a ≠ a ∨ rematch hG θ b ≠ b ∨
          rematch hG θ c ≠ c ∨ rematch hG θ d ≠ d) := by
  obtain ⟨a, b, c, d, hFD, hva, hvc, hs1, hs2⟩ := hSel
  have hIA : Interleaved (mkGenome hG S) a b c d :=
    (interleaved_iff hG S a b c d).2 hFD
  have hneq : vtx hG L S a ≠ vtx hG L S c ∧
      (fibre hG L S (vtx hG L S a)).card = 2 ∧
      (fibre hG L S (vtx hG L S c)).card = 2 :=
    selectedInterleaving_fibreSize (α := α) hG L S (θ := θ) (a := a) (b := b) (c := c) (d := d)
      (hva := hva) (hvc := hvc) (hab := hFD.1.1) (hac := hFD.1.2.1) (had := hFD.1.2.2.1)
      (hbc := hFD.1.2.2.2.1) (hbd := hFD.1.2.2.2.2.1) (hcd := hFD.1.2.2.2.2.2) hs1 hs2 hnT
  have hblock : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b ∨
      (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d := by
    by_cases hpa : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b
    · exact Or.inl hpa
    · by_cases hpc : (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d
      · exact Or.inr hpc
      · exact absurd (interleaved_maximal_pair (α := α) hG L S (hL := hL)
          (hab := hFD.1.1) (hcd := hFD.1.2.2.2.2.2) (hva := hva) (hvc := hvc)
          (hpa := hpa) (hpc := hpc) (hIA := hIA)) hno
  obtain ⟨x, hxm, hρ⟩ :=
    (selects_iff_rematch (α := α) hG L S (v := vtx hG L S a)).mp hs1
  have hxa : x = a ∨ x = b := card_two_two_mem hneq.2.1 hFD.1.1
    ((mem_fibre (hG := hG) (L := L) (S := S)).mpr rfl)
    ((mem_fibre (hG := hG) (L := L) (S := S)).mpr hva.symm) hxm
  refine ⟨a, b, c, d, hIA, hva, hvc, hneq.1, hneq.2.1, hneq.2.2, hblock, ?_⟩
  rcases hxa with rfl | rfl
  · exact Or.inl hρ
  · exact Or.inr (Or.inl hρ)

/-! ### 5.4 The remaining obligation, restated -/

/-- **The reduced form of `BadSelectedInterleavingRemaining`.**  By §5.1 the
`P2` and `¬ LongObstruction` clauses are equivalent, so the previous front's
obligation is settled by this one: it assumes **nothing** about the genome and
asks that a bad, bijective, fibre-preserving, one-cycle `θ` which selects an
interleaving without selecting a triple must exhibit a long obstruction.

This is the statement the next front has to prove, and it is stated here as a
`Prop`: no `axiom`, no `sorry`, no `admit`. -/
def InterleavingObstructionNeeded : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (θ : Fin K → Fin K), 2 ≤ M →
    Function.Bijective θ → FibrePreserving (hG := hK) (L := M) S θ →
      OneCycle hK θ → ¬ OrbitVertexEq (hG := hK) (L := M) S θ →
      ¬ SelectedTriple (hG := hK) (L := M) S θ →
      SelectedInterleaved (hG := hK) (L := M) S θ → LongObstruction hK M S

/-- The reduced obligation discharges the previous front's. -/
theorem not_remaining_of_interleavingObstruction (hI : InterleavingObstructionNeeded) :
    ¬ BadSelectedInterleavingRemaining := by
  rintro ⟨K, M, S, hK, θ, hM, _, hbi, hfp, hoc, hbad, hnT, hSel, hno⟩
  exact hno (hI K M S hK θ hM hbi hfp hoc hbad hnT hSel)

end Rematching

end AssemblyP1.BBTReplacement

