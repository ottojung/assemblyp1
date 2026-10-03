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

/-! ## 6. The two-transposition step: the criterion is *crossing*, and
`TwoTranspositionsBlock` is **false**

Front `94a02` (§7 of `BOARD94-REMAINING-2600.md`) named
`TwoTranspositionsBlock` as the single missing statement, and its §8 asked
first for the map-walking cycle criterion: that `nextPos ∘ ρ` being a single
cycle forces the transpositions of `ρ`, read in the cyclic order
`0, 1, …, K - 1`, to form a single descending run (`Arratia`--`Buchberger`--
`Reid` / `Haar`--`Vahidi`--`Wolf`).

**That criterion is the wrong one, and in the `ρ` language of §5 it is false.**
Here `nextPos` is the successor of the circle itself, so `nextPos ∘ ρ` is a
`K`-cycle exactly when the chords of `ρ` **cross** — and the crux
configuration of §5.3 already *assumes* the crossing, because the two
constituents interleave.  §6.1 records the correct criterion, kernel-checked
at `K = 5`, the size at which it bites, and §6.2 derives what it implies for
the crux configuration.

**Worse, `TwoTranspositionsBlock` itself is false, and it is refuted by the very
`00101` crossing that §5 was built around** (§6.4): at `S = 00101`, `L = 3`,
the honest crossing `θ5 = ![3, 4, 1, 2, 0]` has
`ρ5 = ![2, 3, 0, 1, 4] = (0 2)(1 3) = (prevPos 1 prevPos 3)(prevPos 2
prevPos 4)`, its four starts `1 < 2 < 3 < 4` interleave,
`Preceding 2 = Preceding 4` — so the `Preceding`-clause of
`TwoTranspositionsBlock` **is satisfied** — and yet
`¬ LongObstruction BBTChords.hG5 3 S5b`, because `00101` is `P2`.  The single
clause that fails to exclude this instance is exactly the clause the previous
front identified as the intended exclusion, and it is **not repairable** in
that form: at a crossing, one of the two constituents is *expected* to be
preceding-blocked, since an unblocked constituent would already give the
second disjunct of `LongObstruction` (`interleaved_maximal_pair`).  What
excludes `00101` is **badness** (`θ5` is `OrbitVertexEq`, i.e. good), which
`TwoTranspositionsBlock` as stated does not mention.  §6.5 records the
strengthened, not-yet-refuted form. -/

section TwoTranspositions

open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α)

/-- **`00101` as a local `def`.**  `BBTChords.S5` is opaque to the kernel from
here — `(mkGenome BBTChords.hG5 BBTChords.S5).len` does not reduce, so no
`Fintype (Fin _)` and hence no `Decidable` instance for `LongObstruction`
materialises.  The local copy is definitionally equal (`S5b_eq`) and does
reduce, which is what makes the finite verifications below possible. -/
def S5b : Fin 5 → Fin 2 := ![0, 0, 1, 0, 1]

instance : NeZero (mkGenome BBTChords.hG5 S5b).len := ⟨by norm_num [mkGenome]⟩

theorem S5b_eq : S5b = BBTChords.S5 := rfl

/-! ### 6.1 The correct cycle criterion: crossing, not a descending run -/

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- **At `K = 5`, the cycle criterion is exactly crossing.**  If `ρ` is an
involution, moves something, and `nextPos ∘ ρ` is a single cycle, then `ρ` is
*two* disjoint transpositions whose chords cross on the circle
(`InterleavedStarts`).

This is the kernel-checked `K = 5` case of the criterion the previous front
asked for.  Note what comes out: the **crossing** condition — which is what
the crux configuration of §5.3 already assumes — and never a nested
("descending") pair.  `one_transposition_not_oneCycle_5` below shows the other
half: a lone transposition never gives a `K`-cycle, so the interesting
transposition count is `2`, not `1`. -/
theorem crossing_criterion_5 :
    ∀ ρ : Fin 5 → Fin 5,
      (∀ x, ρ (ρ x) = x) → ¬ (∀ x, ρ x = x) →
      OneCycle BBTChords.hG5 (fun x => nextPos BBTChords.hG5 (ρ x)) →
      ∃ a b c d : Fin 5,
        ρ a = b ∧ ρ b = a ∧ ρ c = d ∧ ρ d = c ∧ InterleavedStarts BBTChords.hG5 a b c d := by
  decide

/-- **A single transposition never works.**  On `Fin 5`, `nextPos ∘ (a b)` is
never a single cycle, for any `a ≠ b`.  Kernel-checked; this is the `K = 5`
instance of the obstruction that makes the *crossing pair*, and not a lone
transposition, the configuration of interest. -/
theorem one_transposition_not_oneCycle_5 :
    ∀ (a b : Fin 5), a ≠ b →
      ¬ OneCycle BBTChords.hG5
        (fun x => nextPos BBTChords.hG5 (if x = a then b else if x = b then a else x)) := by
  decide

/-- **The general form of the correct criterion, stated and NOT proved here**:
for an involution `ρ` of `Fin K` with nonempty support, `nextPos ∘ ρ` is a
single cycle only if the number of transpositions is positive and even, and
the chords pairwise cross.  Recorded as a `Prop`: no `axiom`, no `sorry`,
no `admit`. -/
def CrossingCriterion : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (ρ : Fin K → Fin K),
    (∀ x, ρ (ρ x) = x) → ¬ (∀ x, ρ x = x) →
    OneCycle hK (fun x => nextPos hK (ρ x)) →
    ∃ t : ℕ, 0 < t ∧ t + 1 ≤ 2 * t ∧
      (∀ i : Fin t, ∃ a b : Fin K, ρ a = b ∧ ρ b = a ∧
        ∀ j : Fin t, j ≠ i → ∃ c d : Fin K, ρ c = d ∧ ρ d = c ∧
          ((c - a) % K < (d - b) % K ∧ (d - a) % K < (c - b) % K ∨
           (c - b) % K < (d - a) % K ∧ (d - b) % K < (c - a) % K))

/-! ### 6.2 What the criterion gives at the crux configuration -/

/-- **The `00101` crossing successor, `θ5 = ![3, 4, 1, 2, 0]`, is exactly
`nextPos ∘ ρ5`.**  Its orbit from the origin is `0, 3, 2, 1, 4`, a single
five-cycle. -/
def θ5 : Fin 5 → Fin 5 := ![3, 4, 1, 2, 0]

/-- **Its rematching permutation `ρ5 = nextPos⁻¹ ∘ θ5 = ![2, 3, 0, 1, 4]`, i.e.
the involution `(0 2)(1 3)`. -/
def ρ5 : Fin 5 → Fin 5 := fun x => prevPos BBTChords.hG5 (θ5 x)

theorem θ5_is_nextPos_ρ5 : ∀ x : Fin 5, θ5 x = nextPos BBTChords.hG5 (ρ5 x) := by decide

theorem ρ5_values :
    ρ5 0 = 2 ∧ ρ5 1 = 3 ∧ ρ5 2 = 0 ∧ ρ5 3 = 1 ∧ ρ5 4 = 4 := by decide

theorem ρ5_is_rematch (x : Fin 5) :
    rematch BBTChords.hG5 θ5 x = ρ5 x := rfl

/-- `ρ5` is a permutation. -/
theorem ρ5_bij : Function.Bijective ρ5 := by decide

/-- `θ5` is one cycle. -/
theorem θ5_oneCycle : OneCycle BBTChords.hG5 θ5 := by decide

/-- `θ5` preserves the fibres. -/
theorem θ5_fibrePreserving : FibrePreserving (hG := BBTChords.hG5) (L := 3) S5b θ5 := by decide

/-- `ρ5` preserves every shift class of `S5b` at `L = 3`, kernel-checked. -/
theorem ρ5_shiftClass :
    ∀ v : Fin 2 → Fin 2, ∀ x : Fin 5,
      x ∈ shiftClass (hG := BBTChords.hG5) (L := 3) S5b v →
      ρ5 x ∈ shiftClass (hG := BBTChords.hG5) (L := 3) S5b v := by
  decide

/-- **The four starts `1 < 2 < 3 < 4` interleave**: the two doubled `2`-mers
`01` at `{1, 3}` and `10` at `{2, 4}`.  This is the crossing itself. -/
theorem starts_interleave_00101 :
    InterleavedStarts BBTChords.hG5 (1 : Fin 5) (3 : Fin 5) (2 : Fin 5) (4 : Fin 5) := by
  decide

/-- **`θ5` selects that interleaving**: `SelectedInterleaved θ5` at `00101`,
`L = 3`, kernel-checked at the explicit `θ5`. -/
theorem θ5_selectedInterleaved : SelectedInterleaved (hG := BBTChords.hG5) (L := 3) S5b θ5 := by
  decide

/-- **The `Preceding`-clause of `TwoTranspositionsBlock` is *satisfied* at the
harmless crossing**: `Preceding 2 = Preceding 4 = 0`.  This is the fact that
kills the statement: at a crossing the blocked constituent is normally *part*
of the configuration. -/
theorem preceding_blocked_00101 :
    (mkGenome BBTChords.hG5 S5b).Preceding 2 = (mkGenome BBTChords.hG5 S5b).Preceding 4 := by
  decide

/-- **The two transpositions of `ρ5` are the shift-class versions of the two
interleaved pairs**: `(prevPos 1 prevPos 3) = (0 2)` and
`(prevPos 2 prevPos 4) = (1 3)`.  This is exactly the shape
`TwoTranspositionsBlock` demands, with `(a, b, c, d) = (1, 3, 2, 4)`. -/
theorem ρ5_transpositions :
    ρ5 (prevPos BBTChords.hG5 (1 : Fin 5)) = prevPos BBTChords.hG5 (3 : Fin 5) ∧
    ρ5 (prevPos BBTChords.hG5 (3 : Fin 5)) = prevPos BBTChords.hG5 (1 : Fin 5) ∧
    ρ5 (prevPos BBTChords.hG5 (2 : Fin 5)) = prevPos BBTChords.hG5 (4 : Fin 5) ∧
    ρ5 (prevPos BBTChords.hG5 (4 : Fin 5)) = prevPos BBTChords.hG5 (2 : Fin 5) := by
  decide

/-- **`00101` has no long obstruction at `L = 3`**: `P2`, hence `Ukkonen`. -/
theorem not_longObstruction_00101 : ¬ LongObstruction BBTChords.hG5 3 S5b :=
  not_longObstruction_of_Ukkonen (P2.imp_Ukkonen (by decide) p2_hG5_S5_L3)

/-! ### 6.3 `TwoTranspositionsBlock`, verbatim -/

/-- **The statement the previous front named `TwoTranspositionsBlock`**, in the
`ρ` language: `S` is a `P2` word, `ρ` is a permutation preserving every shift
class, `θ = nextPos ∘ ρ` is one cycle, and `ρ` carries the two disjoint
transpositions `(prevPos a  prevPos b)` and `(prevPos c  prevPos d)` with
`a, b` and `c, d` interleaved and one constituent preceding-blocked.  Then
`LongObstruction`.

The quadruple `(a, b, c, d)` is universally quantified rather than existentially
as the prose statement has it; the two forms are equivalent, and the
universal one is the one a counterexample can be fed to.  `InterleavedStarts`
(from `BBTChords`) is used rather than `Interleaved` (whose head is a `Genome`
structure) purely so that the finite verification below is possible;
`interleaved_iff` identifies the two.

This `Prop` is **false**: `not_TwoTranspositionsBlock`. -/
def TwoTranspositionsBlock : Prop :=
  ∀ (K M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (_hM : 2 ≤ M) (ρ : Fin K → Fin K)
    (a b c d : Fin K),
    Function.Bijective ρ →
    P2 hK M S →
    (∀ v : Fin (M - 1) → Fin 2, ∀ x : Fin K,
      x ∈ shiftClass (hG := hK) (L := M) S v → ρ x ∈ shiftClass (hG := hK) (L := M) S v) →
    (InterleavedStarts hK a b c d ∧
      ρ (prevPos hK a) = prevPos hK b ∧ ρ (prevPos hK b) = prevPos hK a ∧
      ρ (prevPos hK c) = prevPos hK d ∧ ρ (prevPos hK d) = prevPos hK c ∧
      ((mkGenome hK S).Preceding a = (mkGenome hK S).Preceding b ∨
        (mkGenome hK S).Preceding c = (mkGenome hK S).Preceding d)) →
    LongObstruction hK M S

/-! ### 6.4 The refutation -/

/-- **`TwoTranspositionsBlock` is false**, witnessed by the honest `00101`
crossing.  Every antecedent is realised at `K = 5`, `M = 3`, `ρ = ρ5`,
`(a, b, c, d) = (1, 3, 2, 4)`: `00101` is `P2` (`p2_hG5_S5_L3`), `ρ5` is a
permutation preserving every shift class, `θ5 = nextPos ∘ ρ5` is one cycle,
the two transpositions are `(prevPos 1 prevPos 3)` and
`(prevPos 2 prevPos 4)`, the starts interleave, and
`Preceding 2 = Preceding 4` — while `LongObstruction` is refuted by
`not_longObstruction_00101`. -/
theorem not_TwoTranspositionsBlock : ¬ TwoTranspositionsBlock := by
  intro h
  exact not_longObstruction_00101
    (h 5 3 S5b BBTChords.hG5 (by decide) ρ5 1 3 2 4 ρ5_bij
      (S5b_eq ▸ p2_hG5_S5_L3) ρ5_shiftClass
      ⟨starts_interleave_00101, ρ5_transpositions.1, ρ5_transpositions.2.1,
        ρ5_transpositions.2.2.1, ρ5_transpositions.2.2.2,
        Or.inr preceding_blocked_00101⟩)

/-! ### 6.5 The strengthened form that survives, and it is not new -/

/-- **`θ5` is GOOD**: it spells the truth's own vertex cycle up to rotation.
This is the same fact as `BBTSupportInvariant.harmless_selected_crossing_00101`,
at the explicit `θ5`.  It is *what* excludes the counterexample of §6.4, and
it is the one hypothesis `TwoTranspositionsBlock` did not mention. -/
theorem θ5_orbitVertexEq : OrbitVertexEq (hG := BBTChords.hG5) (L := 3) S5b θ5 := by
  decide

/-- **`TwoTranspositionsBlock` with the badness clause added.**  This is the
form that survives §6.4: `θ5_orbitVertexEq` is exactly the missing
hypothesis.  It is stated as a `Prop` and **not proved**: no `axiom`, no
`sorry`, no `admit`.

It is also *not a new obligation*: it is `InterleavingObstructionNeeded`
(§5.4) restricted to the two-transposition case, so a front that discharges
this has not gained anything over the one that discharges §5.4 directly. -/
def TwoTranspositionsBlockBad : Prop :=
  ∀ (K M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (hM : 2 ≤ M) (ρ : Fin K → Fin K)
    (a b c d : Fin K),
    Function.Bijective ρ → P2 hK M S →
    OneCycle hK (fun x => nextPos hK (ρ x)) →
    (∀ v : Fin (M - 1) → Fin 2, ∀ x : Fin K,
      x ∈ shiftClass (hG := hK) (L := M) S v → ρ x ∈ shiftClass (hG := hK) (L := M) S v) →
    ¬ OrbitVertexEq (hG := hK) (L := M) S (fun x => nextPos hK (ρ x)) →
    (InterleavedStarts hK a b c d ∧
      ρ (prevPos hK a) = prevPos hK b ∧ ρ (prevPos hK b) = prevPos hK a ∧
      ρ (prevPos hK c) = prevPos hK d ∧ ρ (prevPos hK d) = prevPos hK c ∧
      ((mkGenome hK S).Preceding a = (mkGenome hK S).Preceding b ∨
        (mkGenome hK S).Preceding c = (mkGenome hK S).Preceding d)) →
    LongObstruction hK M S

end TwoTranspositions
/-! ## 7. The backward-extension step, and the common-back-step obstruction

Front `94a03` (§2 of `/workspace/BOARD94-TWOTRANS-0101.md`) settled that the
cycle criterion is *crossing* and that `TwoTranspositionsBlock` is false, and
§8 of the same report names the honest next step: the genome side.  This
section supplies it.

`AssemblyP1.BBTMaximalExtension` (§3a of that module) carries the *definitions*
for stepping backwards --- `BackAgrees`, `backAgreeSet`, `max_back_agrees`,
`preceding_ne_of_max_back` --- and says, in its own module docstring, exactly
what is missing:

> **Not proved.**  The index arithmetic that combines a backward step of size
> `p` with a forward agreement of length `e₀` yields an agreement of length
> `e₀ + p` at the extended pair; this is what is needed to compose §3a with §2.

That index arithmetic is `agrees_back` below, and it is kernel-checked (§7.1).
With it, and with the fact that a common rotation preserves the alternation
clause (`interleaved_iter`, §7.2), the two halves compose and give
`commonBackStep_obstruction` (§7.3): **two interleaved pairs carrying the same
`(L-1)`-mers, which agree backwards for the same number of places and stop
there, are two interleaved maximal repeats of length `≥ L - 1`**, i.e. a
`LongObstruction`.  §7.4 turns it into a new necessary condition on the crux
configuration of §5.3, `crux_commonBackStep_obstruction`.

Note what is *not* assumed anywhere: the genome-side `Preceding`-clause of
front `94a02` §7 is **not** a hypothesis of any statement here.  It is a
consequence of `¬ LongObstruction` (`interleaved_maximal_pair`), so assuming it
would be circular; every theorem below is proved from `¬ LongObstruction` or
from the truth, and the `Preceding` facts that are used are *derived* from the
maximality of the backward agreement (`preceding_ne_of_maxBack`), never assumed. -/

section BackwardExtension

open OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph

variable {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)

/-! ## A. reading symbols at shifted occurrences -/

lemma cyc_turn (i : ℕ) : cyc hG S (i + G) = cyc hG S i := by
  simp [cyc]

lemma cyc_prev_step (x : Fin G) (i : ℕ) :
    cyc hG S ((prevPos hG x).val + i) = cyc hG S (x.val + G - 1 + i) := by
  have h1 : ((prevPos hG x).val + i) % G = (x.val + G - 1 + i) % G := by
    simp only [prevPos]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  simp only [cyc]
  congr 1
  exact Fin.ext h1

lemma cyc_prev_fwd (x : Fin G) (j : ℕ) :
    cyc hG S ((prevPos hG x).val + (j + 1)) = cyc hG S (x.val + j) := by
  rw [cyc_prev_step hG S x (j + 1)]
  have key : (x.val + G - 1 + (j + 1)) = (x.val + j) + G := by omega
  rw [key]
  exact cyc_turn hG S (x.val + j)

/-- Agreement implies agreement of the `(L-1)`-mers, as soon as the
agreement is at least `L-1` long. -/
lemma prevPos_inj {x y : Fin G} : prevPos hG x = prevPos hG y → x = y := by
  intro hxy
  calc x = nextPos hG (prevPos hG x) := (nextPrev _ _).symm
    _ = nextPos hG (prevPos hG y) := by rw [hxy]
    _ = y := nextPrev _ _

lemma prevPos_iter_inj : ∀ (q : ℕ) {x y : Fin G},
    (prevPos hG)^[q] x = (prevPos hG)^[q] y → x = y := by
  intro q
  induction q with
  | zero => intro x y h; exact h
  | succ q ih =>
    intro x y h
    have h' : prevPos hG x = prevPos hG y := ih (by
      simpa only [Function.iterate_succ_apply] using h)
    exact prevPos_inj hG h'

lemma agrees_imp_vtx {L e : ℕ} {x y : Fin G} (hag : Agrees hG S e x y) (he : L - 1 ≤ e) :
    vtx hG L S x = vtx hG L S y := by
  funext d
  have hd : d.val < e := lt_of_lt_of_le d.isLt he
  exact hag ⟨d.val, hd⟩

/-! ## B. combining a backward step with a forward agreement -/

lemma BackAgrees_mono {a b : Fin G} {p p' : ℕ} (hp : p' ≤ p)
    (hag : BackAgrees hG S a b p) : BackAgrees hG S a b p' := by
  intro d
  have hlt : d.val < p' := by omega
  exact hag ⟨d.val, by omega⟩

/-- **Backward agreement shifts.** -/
lemma BackAgrees_shift {a b : Fin G} {p q : ℕ}
    (hag : BackAgrees hG S a b (p + q)) :
    BackAgrees hG S ((prevPos hG)^[q] a) ((prevPos hG)^[q] b) p := by
  intro e
  simp only [BackAgrees] at hag ⊢
  have hlt : e.val + q < p + q := by omega
  have h := hag ⟨e.val + q, hlt⟩
  have keyA : (prevPos hG)^[e.val + q] a = (prevPos hG)^[e.val] ((prevPos hG)^[q] a) :=
    Function.iterate_add_apply _ _ _ _
  have keyB : (prevPos hG)^[e.val + q] b = (prevPos hG)^[e.val] ((prevPos hG)^[q] b) :=
    Function.iterate_add_apply _ _ _ _
  rw [← keyA, ← keyB]
  exact hag ⟨e.val + q, hlt⟩

lemma agrees_back_step {a b : Fin G} {e₀ : ℕ}
    (hag : Agrees hG S e₀ a b) (h1 : BackAgrees hG S a b 1) :
    Agrees hG S (e₀ + 1) (prevPos hG a) (prevPos hG b) := by
  intro d
  refine Fin.cases ?case0 (fun j => ?_) d
  · simpa using h1 (0 : Fin 1)
  · simp only [BackAgrees] at h1
    simp only [Fin.val_succ]
    rw [cyc_prev_fwd hG S a j.val, cyc_prev_fwd hG S b j.val]
    exact hag ⟨j.val, by omega⟩

/-- **THE MISSING INDEX ARITHMETIC.**  A backward agreement of `q + 1`
positions, combined with a forward agreement of `e₀` positions, is a forward
agreement of `e₀ + q` positions at the backward-shifted occurrences. -/
lemma agrees_back : ∀ (p e₀ : ℕ) (a b : Fin G),
    BackAgrees hG S a b p → Agrees hG S e₀ a b →
    Agrees hG S (e₀ + p) ((prevPos hG)^[p] a) ((prevPos hG)^[p] b) := by
  intro p
  induction p with
  | zero =>
    intro e₀ a b _ hag
    simpa only [Function.iterate_zero, id_eq, Nat.add_zero] using hag
  | succ p ih =>
    intro e₀ a b hagp hag
    have h1 : BackAgrees hG S a b 1 :=
      BackAgrees_mono (hG := hG) (S := S) (a := a) (b := b) (p' := 1) (p := p + 1)
        (by omega) hagp
    have h2 : BackAgrees hG S (prevPos hG a) (prevPos hG b) p :=
      BackAgrees_shift (hG := hG) (S := S) (a := a) (b := b) (p := p) (q := 1) hagp
    rw [Function.iterate_succ_apply (prevPos hG) p a, Function.iterate_succ_apply (prevPos hG) p b]
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ih (e₀ := e₀ + 1) (a := prevPos hG a) (b := prevPos hG b) h2
        (agrees_back_step (hG := hG) (S := S) hag h1))

/-! ## C. the alternation clause is rotation invariant -/

def distVal (x y : Fin G) : ℕ := (y.val + G - x.val) % G

lemma mod_turn {a b : ℕ} (h : b + G = a) : a % G = b % G := by
  rw [← h, Nat.add_mod_right]

lemma dec1 (v : ℕ) (hv : v < G) (h1 : v ≠ 0) : (v + G - 1) % G = v - 1 := by
  rw [show v + G - 1 = (v - 1) + G by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma stepA (u v : ℕ) (hu : u < G) (hv : v < G) (h1 : u = 0) (h2 : v = 0) :
    ((u + G - 1) % G + G - (v + G - 1) % G) % G = (u + G - v) % G := by
  rcases h1 with rfl
  rcases h2 with rfl
  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : G - 1 < G)]
  have e : (G - 1) + G - (G - 1) = G := by omega
  rw [e, Nat.mod_self, Nat.sub_zero, Nat.mod_self]

lemma stepB (u v : ℕ) (hv : v < G) (h1 : u = 0) (h2 : v ≠ 0) :
    ((u + G - 1) % G + G - (v + G - 1) % G) % G = (u + G - v) % G := by
  have k1 : (u + G - 1) % G = G - 1 := by
    rw [h1, Nat.zero_add, Nat.mod_eq_of_lt (by omega : G - 1 < G)]
  have k2 : (v + G - 1) % G = v - 1 := dec1 v hv h2
  rw [k1, k2]
  have hz : (((G - 1) + G - (v - 1) : ℕ) : ℤ) = (((u + G - v + G : ℕ) : ℤ)) := by
    have c2 : (((v - 1 : ℕ) : ℤ)) = (v : ℤ) - 1 := by omega
    have c4 : ((u + G - v + G : ℕ) : ℤ) = (u : ℤ) + (G : ℤ) - v + (G : ℤ) := by omega
    have c5 : ((G - 1 + G : ℕ) : ℤ) = (G : ℤ) - 1 + (G : ℤ) := by omega
    rw [Nat.cast_sub (by omega : v - 1 ≤ (G - 1) + G), c5, c2, c4]
    omega
  have e : (G - 1) + G - (v - 1) = u + G - v + G := by exact_mod_cast hz
  rw [e]
  exact mod_turn (G := G) (a := u + G - v + G) (b := u + G - v) (by omega)

lemma stepC (u v : ℕ) (hu : u < G) (h1 : u ≠ 0) (h2 : v = 0) :
    ((u + G - 1) % G + G - (v + G - 1) % G) % G = (u + G - v) % G := by
  have k1 : (u + G - 1) % G = u - 1 := dec1 u hu h1
  have k2 : (v + G - 1) % G = G - 1 := by
    rw [h2, Nat.zero_add, Nat.mod_eq_of_lt (by omega : G - 1 < G)]
  rw [k1, k2]
  have e : (u - 1) + G - (G - 1) = u := by omega
  rw [e, h2, Nat.sub_zero]
  exact (mod_turn (G := G) (a := u + G) (b := u) (by omega)).symm

lemma stepD (u v : ℕ) (hu : u < G) (hv : v < G) (h1 : u ≠ 0) (h2 : v ≠ 0) :
    ((u + G - 1) % G + G - (v + G - 1) % G) % G = (u + G - v) % G := by
  have k1 : (u + G - 1) % G = u - 1 := dec1 u hu h1
  have k2 : (v + G - 1) % G = v - 1 := dec1 v hv h2
  rw [k1, k2]
  have hz : (((u - 1) + G - (v - 1) : ℕ) : ℤ) = (((u + G - v : ℕ) : ℤ)) := by
    have c2 : (((v - 1 : ℕ) : ℤ)) = (v : ℤ) - 1 := by omega
    have c3 : ((u + G - v : ℕ) : ℤ) = (u : ℤ) + (G : ℤ) - v := by omega
    have c5 : ((u - 1 + G : ℕ) : ℤ) = (u : ℤ) - 1 + (G : ℤ) := by omega
    rw [Nat.cast_sub (by omega : v - 1 ≤ (u - 1) + G), c5, c2, c3]
    omega
  have e : (u - 1) + G - (v - 1) = u + G - v := by exact_mod_cast hz
  rw [e]

lemma distVal_step1 (u v : ℕ) (hu : u < G) (hv : v < G) :
    ((u + G - 1) % G + G - (v + G - 1) % G) % G = (u + G - v) % G := by
  by_cases h1 : u = 0
  · by_cases h2 : v = 0
    · exact stepA u v hu hv h1 h2
    · exact stepB u v hv h1 h2
  · by_cases h2 : v = 0
    · exact stepC u v hu h1 h2
    · exact stepD u v hu hv h1 h2

lemma distVal_step (x y : Fin G) :
    distVal (prevPos hG x) (prevPos hG y) = distVal x y := by
  simp only [distVal, prevPos]
  exact distVal_step1 (G := G) y.val x.val y.isLt x.isLt

lemma distVal_iter : ∀ (q : ℕ) (x y : Fin G),
    distVal ((prevPos hG)^[q] x) ((prevPos hG)^[q] y) = distVal x y := by
  intro q
  induction q with
  | zero => intro x y; rfl
  | succ q ih =>
    intro x y
    have h : distVal ((prevPos hG)^[q] (prevPos hG x))
        ((prevPos hG)^[q] (prevPos hG y)) = distVal (prevPos hG x) (prevPos hG y) :=
      ih (prevPos hG x) (prevPos hG y)
    rw [show (prevPos hG)^[q + 1] x = (prevPos hG)^[q] (prevPos hG x)
        from Function.iterate_succ_apply (prevPos hG) q x,
        show (prevPos hG)^[q + 1] y = (prevPos hG)^[q] (prevPos hG y)
        from Function.iterate_succ_apply (prevPos hG) q y,
      h, distVal_step hG x y]

lemma inOpenArc_iff {x y z : Fin G} :
    InOpenArc (mkGenome hG S) x y z ↔ (0 < distVal x z ∧ distVal x z < distVal x y) := by
  have hlen : (mkGenome hG S).len = G := len_mkGenome (α := α) hG S
  simp only [InOpenArc, hlen]
  rfl

lemma inOpenArc_iter {x y z : Fin G} (q : ℕ) :
    (InOpenArc (mkGenome hG S) ((prevPos hG)^[q] x) ((prevPos hG)^[q] y)
        ((prevPos hG)^[q] z)) ↔ InOpenArc (mkGenome hG S) x y z := by
  rw [inOpenArc_iff, inOpenArc_iff]
  rw [distVal_iter hG q x z, distVal_iter hG q x y]


lemma interleaved_iter : ∀ (q : ℕ) {a b c d : Fin G},
    Interleaved (mkGenome hG S) a b c d →
    Interleaved (mkGenome hG S) ((prevPos hG)^[q] a) ((prevPos hG)^[q] b)
      ((prevPos hG)^[q] c) ((prevPos hG)^[q] d) := by
  intro q a b c d hIA
  have h1 : (prevPos hG)^[q] a ≠ (prevPos hG)^[q] b := fun h => hIA.1.1 (prevPos_iter_inj (hG := hG) (q := q) h)
  have h2 : (prevPos hG)^[q] a ≠ (prevPos hG)^[q] c := fun h => hIA.1.2.1 (prevPos_iter_inj (hG := hG) (q := q) h)
  have h3 : (prevPos hG)^[q] a ≠ (prevPos hG)^[q] d := fun h => hIA.1.2.2.1 (prevPos_iter_inj (hG := hG) (q := q) h)
  have h4 : (prevPos hG)^[q] b ≠ (prevPos hG)^[q] c := fun h => hIA.1.2.2.2.1 (prevPos_iter_inj (hG := hG) (q := q) h)
  have h5 : (prevPos hG)^[q] b ≠ (prevPos hG)^[q] d := fun h => hIA.1.2.2.2.2.1 (prevPos_iter_inj (hG := hG) (q := q) h)
  have h6 : (prevPos hG)^[q] c ≠ (prevPos hG)^[q] d := fun h => hIA.1.2.2.2.2.2 (prevPos_iter_inj (hG := hG) (q := q) h)
  refine ⟨⟨h1, h2, h3, h4, h5, h6⟩, ?_⟩
  rw [inOpenArc_iter (hG := hG) (S := S) (q := q) (x := a) (y := b) (z := c),
    inOpenArc_iter (hG := hG) (S := S) (q := q) (x := a) (y := b) (z := d)]
  exact hIA.2

/-! ## D. the common-back-step obstruction -/

/-- **`BackAgrees` at `p + 1` is `BackAgrees` at `p` plus one more place.** -/
lemma backAgrees_succ {p : ℕ} {a b : Fin G} (hag : BackAgrees hG S a b p)
    (hcon : cyc hG S (prevPos hG ((prevPos hG)^[p] a)).val
      = cyc hG S (prevPos hG ((prevPos hG)^[p] b)).val) :
    BackAgrees hG S a b (p + 1) := by
  simp only [BackAgrees]
  intro d
  by_cases h : d.val < p
  · exact hag ⟨d.val, h⟩
  · have h1 : d.val = p := by omega
    rw [h1]
    exact hcon

/-- **Maximality of the backward agreement gives differing preceding symbols.** -/
lemma preceding_ne_of_maxBack {p : ℕ} {a b : Fin G}
    (hag : BackAgrees hG S a b p) (hnot : ¬ BackAgrees hG S a b (p + 1)) :
    (mkGenome hG S).Preceding ((prevPos hG)^[p] a)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[p] b) := by
  rw [preceding_eq_prevPos hG S, preceding_eq_prevPos hG S]
  intro hcon
  apply hnot
  exact backAgrees_succ (hG := hG) (S := S) (p := p) (a := a) (b := b) hag hcon

/-- **THE COMMON-BACK-STEP OBSTRUCTION.**  Two interleaved pairs carrying the
same `(L-1)`-mers, both of which agree backwards for `r + 1` places and stop
there, are two interleaved maximal repeats of length `≥ L - 1`. -/
theorem commonBackStep_obstruction {L : ℕ} (hL : 2 ≤ L) {a b c d : Fin G} (r : ℕ)
    (hIA : Interleaved (mkGenome hG S) a b c d)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hba : BackAgrees hG S a b (r + 1)) (hba' : ¬ BackAgrees hG S a b (r + 2))
    (hbc : BackAgrees hG S c d (r + 1)) (hbc' : ¬ BackAgrees hG S c d (r + 2)) :
    LongObstruction hG L S := by
  have hagab : Agrees hG S (L - 1) a b := fun d => congrFun hva d
  have hagcd : Agrees hG S (L - 1) c d := fun d => congrFun hvc d
  have hA1 : Agrees hG S (L - 1 + (r + 1)) ((prevPos hG)^[r + 1] a) ((prevPos hG)^[r + 1] b) :=
    agrees_back (α := α) (hG := hG) (S := S) (p := r + 1) (e₀ := L - 1) a b hba hagab
  have hA2 : Agrees hG S (L - 1 + (r + 1)) ((prevPos hG)^[r + 1] c) ((prevPos hG)^[r + 1] d) :=
    agrees_back (α := α) (hG := hG) (S := S) (p := r + 1) (e₀ := L - 1) c d hbc hagcd
  have hvt1 : vtx hG L S ((prevPos hG)^[r + 1] a) = vtx hG L S ((prevPos hG)^[r + 1] b) :=
    agrees_imp_vtx (hG := hG) (S := S) hA1 (by omega)
  have hvt2 : vtx hG L S ((prevPos hG)^[r + 1] c) = vtx hG L S ((prevPos hG)^[r + 1] d) :=
    agrees_imp_vtx (hG := hG) (S := S) hA2 (by omega)
  have hpr1 : (mkGenome hG S).Preceding ((prevPos hG)^[r + 1] a)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[r + 1] b) :=
    preceding_ne_of_maxBack (hG := hG) (S := S) (p := r + 1) hba hba'
  have hpr2 : (mkGenome hG S).Preceding ((prevPos hG)^[r + 1] c)
      ≠ (mkGenome hG S).Preceding ((prevPos hG)^[r + 1] d) :=
    preceding_ne_of_maxBack (hG := hG) (S := S) (p := r + 1) hbc hbc'
  have hne1 : (prevPos hG)^[r + 1] a ≠ (prevPos hG)^[r + 1] b :=
    fun h => hIA.1.1 (prevPos_iter_inj (hG := hG) (q := r + 1) h)
  have hne2 : (prevPos hG)^[r + 1] c ≠ (prevPos hG)^[r + 1] d :=
    fun h => hIA.1.2.2.2.2.2 (prevPos_iter_inj (hG := hG) (q := r + 1) h)
  obtain ⟨e₁, he₁, hlen₁⟩ :=
    maximalRepeat_of_branch (α := α) (hG := hG) (S := S) (L := L) hL hne1 hvt1 hpr1
  obtain ⟨e₂, he₂, hlen₂⟩ :=
    maximalRepeat_of_branch (α := α) (hG := hG) (S := S) (L := L) hL hne2 hvt2 hpr2
  exact interleaved_disjunct (hG := hG) (S := S) he₁ he₂
    (interleaved_iter (hG := hG) (S := S) (q := r + 1) hIA) hlen₁ hlen₂

/-! ## E. a new necessary condition on the crux configuration -/

/-- **No common backward step.**  At a configuration that contradicts
`LongObstruction`, the two interleaved constituents cannot share their maximal
backward agreement: the two pairs' backward agreements stop at different
places. -/
theorem crux_no_commonBackStep {L : ℕ} (hL : 2 ≤ L)
    (hno : ¬ LongObstruction hG L S) :
    ¬ ∃ (a b c d : Fin G) (r : ℕ),
        Interleaved (mkGenome hG S) a b c d ∧
        vtx hG L S a = vtx hG L S b ∧ vtx hG L S c = vtx hG L S d ∧
        BackAgrees hG S a b (r + 1) ∧ ¬ BackAgrees hG S a b (r + 2) ∧
        BackAgrees hG S c d (r + 1) ∧ ¬ BackAgrees hG S c d (r + 2) := by
  rintro ⟨a, b, c, d, r, hIA, hva, hvc, hba, hba', hbc, hbc'⟩
  exact hno (commonBackStep_obstruction (α := α) hG S (L := L) (a := a) (b := b) (c := c)
    (d := d) (r := r) hL hIA hva hvc hba hba' hbc hbc')

/-- **The new condition, in the shape of §5.3.**  At the crux configuration of
`crux_rematchShape` --- two *distinct* interleaved fibres of multiplicity
exactly two, one of them preceding-blocked, with the rematching `ρ` nontrivial on
a start of each --- the two constituents' maximal backward agreements stop at
**different** places.  So the surviving configuration is *not* two constituents
that both stop after the same number of backward steps; one of them is
unblocked, or the two backward steps differ.

The `Preceding` and `rematch` clauses are carried for fidelity with
`crux_rematchShape`; they are hypotheses of that shape and are **not** used in
the proof, precisely because they cannot be. -/
theorem crux_commonBackStep_obstruction {L : ℕ} (hL : 2 ≤ L) {θ : Fin G → Fin G}
    (hno : ¬ LongObstruction hG L S) (hnT : ¬ SelectedTriple (hG := hG) (L := L) S θ)
    {a b c d : Fin G}
    (hIA : Interleaved (mkGenome hG S) a b c d)
    (hva : vtx hG L S a = vtx hG L S b) (hvc : vtx hG L S c = vtx hG L S d)
    (hne : vtx hG L S a ≠ vtx hG L S c)
    (hca : (fibre hG L S (vtx hG L S a)).card = 2)
    (hcc : (fibre hG L S (vtx hG L S c)).card = 2)
    (hprec : (mkGenome hG S).Preceding a = (mkGenome hG S).Preceding b ∨
      (mkGenome hG S).Preceding c = (mkGenome hG S).Preceding d)
    (hρ : rematch hG θ a ≠ a ∨ rematch hG θ b ≠ b ∨
      rematch hG θ c ≠ c ∨ rematch hG θ d ≠ d) :
    ¬ ∃ (r : ℕ), BackAgrees hG S a b (r + 1) ∧ ¬ BackAgrees hG S a b (r + 2) ∧
        BackAgrees hG S c d (r + 1) ∧ ¬ BackAgrees hG S c d (r + 2) := by
  rintro ⟨r, hba, hba', hbc, hbc'⟩
  exact hno (commonBackStep_obstruction (α := α) hG S (L := L) (a := a) (b := b) (c := c)
    (d := d) (r := r) hL hIA hva hvc hba hba' hbc hbc')

end BackwardExtension


/-! ## 8. Case 3 of §5 of `/workspace/BOARD94-BADNESS-0153.md`: a genome of
minimal period `G / 2` has no bad `θ` at all

§5 of that report leaves three cases; case 3 is the one where the two
constituents' backward agreements both run the whole way round, i.e. the
genome is periodic.  §7 names it as *"a two-periodic genome has no bad `θ`"*,
with `ρ = nextPos⁻¹ ∘ θ` permuting two 2-element shift classes and `θ`
one-cycling only at a crossing — but that description over-complicates it.

**The exact fact.**  Let `n < G` be a period of the word and suppose every
`(L-1)`-mer occurs exactly twice.  Then *every* fibre-preserving map `θ`
satisfies `OrbitVertexEq` (`half_no_bad_theta`), and in particular there is no
bijective, fibre-preserving, one-cycle `θ` that is not
`OrbitVertexEq` (`half_no_bad_theta_twoPeriod`).  Neither bijectivity nor
one-cycleness is used, and neither is the preceding-blocked clause.

**Why it is easy, in one line.**  If `vtx` has period `n` and every fibre has
size two, then the fibre of `vtx x` is `{x, rotAdd n x}`, so `θ x ∈
{nextPos x, rotAdd n (nextPos x)}`: *`θ` advances one step around the circle,
modulo `n`*.  Iterating, `θ^[j]` is `rotAdd j` modulo `n`, and since `vtx` has
period `n` the two give the same vertex.  Hence the orbit of `θ` reads off
the truth's own vertex cycle with shift `k = 0` — `θ` is good.  The two
transpositions of `ρ` are indeed forced (each is `(x  x + n - 1)` or an
identity), which is why `ρ` permutes two-element shift classes, but the
crossing question never arises: `θ` cannot be bad in the first place.

The whole `α`-polymorphic statement is proved by hand at general `G` and `n`;
nothing here is a finite check. -/

section HalfPeriod

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open OrientedRigidity

variable {G : ℕ} (hG : 0 < G) (L : ℕ)

/-- Reading a circular position only depends on its residue. -/
lemma half_cyc_mod {α : Type} [DecidableEq α] {S : Fin G → α} (u v : ℕ) (h : u % G = v % G) :
    cyc hG S u = cyc hG S v := by
  calc cyc hG S u = cyc hG S (u % G) := cyc_mod hG S u
    _ = cyc hG S (v % G) := by rw [h]
    _ = cyc hG S v := (cyc_mod hG S v).symm

/-- **A period of the word is a period of the vertex function.**
`vtx hG L S (rotAdd hG n x) = vtx hG L S x`. -/
lemma half_vtx_period {α : Type} [DecidableEq α] {S : Fin G → α} {n : ℕ}
    (hper : ∀ i : ℕ, cyc hG S i = cyc hG S (i + n)) (x : Fin G) :
    vtx hG L S (rotAdd hG n x) = vtx hG L S x := by
  unfold vtx
  funext d
  change cyc hG S ((rotAdd hG n x).val + d.val) = cyc hG S (x.val + d.val)
  rw [show (rotAdd hG n x).val = (x.val + n) % G from rfl]
  have h1 := half_cyc_mod (hG := hG) (S := S) ((x.val + n) % G + d.val)
    (x.val + d.val + n) ((Nat.mod_add_mod (x.val + n) G d.val).trans (by congr 1; omega))
  rw [h1]
  exact (hper (x.val + d.val)).symm


/-- **A fibre-preserving map lands on one of the two occurrences.** -/
lemma half_theta_land {α : Type} [DecidableEq α] [Fintype α] {S : Fin G → α} {n : ℕ}
    {hper : ∀ i : ℕ, cyc hG S i = cyc hG S (i + n)} {hn : 0 < n} {hnG : n < G}
    (hfib : ∀ x : Fin G, (fibre hG L S (vtx hG L S x)).card = 2)
    (θ : Fin G → Fin G) (hfp : FibrePreserving (hG := hG) (L := L) S θ) (x : Fin G) :
    θ x = nextPos hG x ∨ θ x = rotAdd hG n (nextPos hG x) := by
  have hmem (z w : Fin G) (h : vtx hG L S z = vtx hG L S w) :
      z ∈ fibre hG L S (vtx hG L S w) :=
    (mem_fibre (hG := hG) (L := L) (S := S)).mpr h
  have hcard : (fibre hG L S (vtx hG L S (nextPos hG x))).card = 2 := hfib _
  have hsh : vtx hG L S (rotAdd hG n (nextPos hG x)) = vtx hG L S (nextPos hG x) :=
    half_vtx_period hG L hper _
  have hne : nextPos hG x ≠ rotAdd hG n (nextPos hG x) := by
    intro h
    have h1 := congrArg Fin.val h
    simp only [nextPos, rotAdd, Fin.val_mk] at h1
    have hq := Nat.mod_add_div ((x.val + 1) % G + n) G
    have h4 : ((x.val + 1) % G + n) / G = 0 := by
      rcases Nat.eq_zero_or_pos (((x.val + 1) % G + n) / G) with hz | hz
      · exact hz
      · have h5 : G ≤ G * (((x.val + 1) % G + n) / G) := by
          have := Nat.mul_le_mul_right G hz
          simpa [Nat.mul_comm] using this
        omega
    rw [h4, Nat.mul_zero] at hq
    have h6 : (x.val + 1) % G + n = (x.val + 1) % G + n := by omega
    omega
  exact card_two_two_mem hcard hne
    (hmem _ _ rfl) (hmem _ _ hsh) (hmem _ _ (hfp x))

/-- **CASE 3.  A genome with a period `n < G` in which every `(L-1)`-mer
occurs exactly twice has no bad `θ` at all**: every fibre-preserving map
satisfies `OrbitVertexEq`.  In particular this disposes of case 3 of §5 of
`/workspace/BOARD94-BADNESS-0153.md`, i.e. a genome of minimal period
`G = 2 * n` (there `n < G`, every `(L-1)`-mer occurs exactly twice, and every
occurrence pair is preceding-blocked).  No bijectivity and no one-cycle
hypothesis is needed. -/
theorem half_no_bad_theta {α : Type} [DecidableEq α] [Fintype α]
    {S : Fin G → α} {n : ℕ} (hnG : n < G) (hn : 0 < n)
    (hper : ∀ i : ℕ, cyc hG S i = cyc hG S (i + n))
    (hfib : ∀ x : Fin G, (fibre hG L S (vtx hG L S x)).card = 2)
    (θ : Fin G → Fin G) (hfp : FibrePreserving (hG := hG) (L := L) S θ) :
    OrbitVertexEq (hG := hG) (L := L) S θ := by
  have hvtx (z : Fin G) : vtx hG L S (rotAdd hG n z) = vtx hG L S z :=
    half_vtx_period (hG := hG) (L := L) (hper := hper) z
  have key : ∀ (j : ℕ) (x : Fin G),
      vtx hG L S (θ^[j] x) = vtx hG L S (rotAdd hG j x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply]
      rcases half_theta_land (α := α) (hG := hG) (L := L) (hn := hn) (hnG := hnG)
        (hper := hper) hfib θ hfp x with h | h
      · rw [h, ih, nextPos, rotAdd_rotAdd]
      · rw [h, ih, nextPos, rotAdd_rotAdd]
        have e : rotAdd hG (j + n) (rotAdd hG 1 x) = rotAdd hG n (rotAdd hG (j + 1) x) := by
          rw [rotAdd_rotAdd, rotAdd_rotAdd]
          congr 1
          omega
        rw [e, hvtx]
  refine ⟨⟨0, hG⟩, fun j => ?_⟩
  simpa using (key j.val (origin hG))

/-- **CASE 3 of §5 of `/workspace/BOARD94-BADNESS-0153.md`, verbatim: there is
no bad `θ` at a genome of minimal period `G = 2 * n`.**  `hG2` says the
minimal period is exactly `G / 2`, `hper` that `n` is a period of the word (so
every `(L-1)`-mer occurring at `x` also occurs at `x + n`), and `hfib` that
every `(L-1)`-mer occurs **exactly twice**.  `hprec` records the remaining
clause of case 3 --- every occurrence pair is preceding-blocked --- and is
**not used**: the conclusion does not need it.  In this regime a
preceding-blocked pair is automatic, since `Preceding` has period `n`.

Note that no bijectivity and no one-cycle hypothesis is needed:
`half_no_bad_theta` gives `OrbitVertexEq` for *every* fibre-preserving `θ`. -/
theorem half_no_bad_theta_twoPeriod {α : Type} [DecidableEq α] [Fintype α]
    {S : Fin G → α} {n : ℕ} (hG2 : G = 2 * n) (hn : 0 < n)
    (hper : ∀ i : ℕ, cyc hG S i = cyc hG S (i + n))
    (hfib : ∀ x : Fin G, (fibre hG L S (vtx hG L S x)).card = 2)
    (_hprec : ∀ (x : Fin G),
      (mkGenome hG S).Preceding x = (mkGenome hG S).Preceding (rotAdd hG n x))
    (θ : Fin G → Fin G) :
    ¬ (Function.Bijective θ ∧ FibrePreserving (hG := hG) (L := L) S θ ∧
        OneCycle hG θ ∧ ¬ OrbitVertexEq (hG := hG) (L := L) S θ) := by
  have hnG : n < G := by omega
  rintro ⟨_, hfp, _, hb⟩
  exact hb (half_no_bad_theta (α := α) hG L hnG hn hper hfib θ hfp)

/-- The anti-vacuity anchor at `K = 4`: for `S = 0101` (minimal period `2 = G/2`)
at `L = 2`, `decide` confirms there is **no** bijective, fibre-preserving,
one-cycle `θ` that fails `OrbitVertexEq`. -/
def S4b : Fin 4 → Fin 2 := ![0, 1, 0, 1]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem half_no_bad_0101_4 :
    ¬ ∃ θ : Fin 4 → Fin 4,
        Function.Bijective θ ∧
          FibrePreserving (hG := (by decide : (0 : ℕ) < 4)) (L := 2) S4b θ ∧
          OneCycle (hG := (by decide : (0 : ℕ) < 4)) θ ∧
          ¬ OrbitVertexEq (hG := (by decide : (0 : ℕ) < 4)) (L := 2) S4b θ := by
  decide

end HalfPeriod

/-! ## 9. Case 1 of §5: the census filter of front `94a04` is buggy, and the
sharp statement of the case-1 residual

§5 of `/workspace/BOARD94-BADNESS-0153.md` leaves three cases; §9 of
`/workspace/BOARD94-CASE3-0300.md` (front `94a05`) disposed of case 3 (§8
above) and named **case 1** --- *exactly one constituent preceding-blocked, the
other unblocked* --- as the next target, with the suggestion that the blocked
pair's maximal backward step `p` should land its maximal repeat *onto* the
unblocked pair's, or at least interleave with it after one further backward step.

**A warning about the census of §4 of `94a04`.**  `scratch/backstep_census.py`
computes `p2(S, L)` with a triple-repeat clause of the form

```text
while e < G-1 and |{S[t₀+i] : i < e+1}| = 1 and ... do e := e+1
```

which takes the set of symbols *inside one window* rather than comparing the
three windows position by position.  That clause therefore almost never fires,
so the "`¬ LongObstruction` genomes" columns of that table admit obstructed
genomes.  The census in this section uses the predicate transcribed from
`LongObstruction` itself (`scratch/case1_fixed.py`).

**What the corrected census shows** (all binary circular words, `G ≤ 10`, all
`2 ≤ L ≤ G+1`, all case-1 quadruples, `vtx a ≠ vtx c`, both with and without a
long obstruction): whenever the genome has *no* long obstruction, the maximal
backward step of the blocked pair lands it **exactly onto** the unblocked pair:
`{c−p, d−p} = {a,b}` in all 2680 such configurations in range, and never on a
pair that interleaves with `(a,b)`.  Without the `¬ LongObstruction`
hypothesis the landing fails — 188 232 interleaving outcomes in range — which is
the obstruction itself, so the statement is not vacuous.  This is **evidence,
not proof**: a Python enumeration whose correspondence to the Lean definitions
is not machine-checked, with range ending at `G = 10`.

**The kernel-checked correction.**  The apparent counterexample that the buggy
filter produces is `G = 7`, `L = 3`, `S = 0100101`, `(a,b,c,d) = (0,3,6,1)`,
`p = 3`, where the blocked pair's maximal repeat sits at `(3,5)`, which neither
coincides with `(0,3)` nor interleaves with it (it *shares* the start `3`).  That
genome is **not** a case-1 configuration: it carries a maximal triple repeat of
length `3 ≥ L−1 = 2` (`triple_0100101`), hence `LongObstruction`
(`longObstruction_0100101`).  So the case-1 statement of §9 of the case-3
report is **not** refuted by it.

**The residual, stated as a `Prop`.**  `case1_landing` below is the sharp
version of §9's case-1 claim: the third disjunct (interleaving) is not needed at
all.  It is stated here and **not proved**: no `axiom`, no `sorry`, no `admit`.
Its genome-side `Preceding` clauses are *hypotheses of the configuration*, not
assumed conclusions, and the only genome-side hypothesis used in the census that
supports it is `¬ LongObstruction`, which is a hypothesis of the front's regime,
not the conclusion of `interleaved_maximal_pair`. -/

section Case1

open SourceFaithfulIs
open AssemblyP1
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open OrientedRigidity

variable {G : ℕ} (hG : 0 < G) (L : ℕ)

theorem hG7c : 0 < 7 := by decide

/-- `S = 0100101`, the genome behind the apparent case-1 counterexample. -/
def S7c : Fin 7 → Fin 2 := ![0, 1, 0, 0, 1, 0, 1]

/-- **`0100101` has a maximal triple repeat of length `3` at starts `0, 3, 5`**:
the three windows are `010`, the preceding symbols are `1, 0, 1` (not all
equal) and the following symbols are `0, 1, 1` (not all equal).  This is the
kernel-checked reason that the `¬ LongObstruction` filter of front `94a04`'s
census is wrong on this genome: it admits `0100101` as `P2`. -/
theorem triple_0100101 :
    (mkGenome hG7c S7c).IsTripleRepeat 3 (0 : Fin 7) (3 : Fin 7) (5 : Fin 7) := by
  unfold mkGenome Genome.IsTripleRepeat Genome.Agree Genome.window
    Genome.Preceding Genome.Following Genome.cycl
  decide

/-- ... so `0100101` has a long obstruction at `L = 3`, and hence no bad `θ`. -/
theorem longObstruction_0100101 : LongObstruction hG7c 3 S7c :=
  Or.inl ⟨3, (0 : Fin 7), (3 : Fin 7), (5 : Fin 7), triple_0100101, by decide⟩

/-- **THE CASE-1 LANDING STATEMENT, verbatim.**  Case 1 of §5: two interleaved
pairs carrying the same `(L−1)`-mers, two *distinct* vertices, the first pair
**unblocked** (`Preceding a ≠ Preceding b`, so its maximal backward step is `0`
and it is a maximal repeat at its own starts), the second pair **blocked** with
maximal backward step `p` (`BackAgrees … p ∧ ¬ BackAgrees … (p+1)`, so `p ≥ 1`).
If the genome has **no long obstruction**, then stepping the blocked pair `p`
places backwards lands it **exactly onto** the unblocked pair.

The third disjunct of §9's claim (the two pairs *interleave*) is not needed, and
the two crossed orientations are written out explicitly because the statement is
order-free in `(a,b)` and `(c,d)`.

**Not proved.**  This is a `Prop`: no `axiom`, no `sorry`, no `admit`.  What is
known is the census of the section docstring (evidence, not proof) and the
`G = 5`/`G = 6` instances of the same shape, which `decide` can only reach at the
cost of a full genome enumeration that does not fit this host's 300 s
elaboration bound. -/
def case1_landing : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (a b c d : Fin K) (p : ℕ),
    2 ≤ M →
      Interleaved (mkGenome hK S) a b c d →
      vtx hK M S a = vtx hK M S b →
      vtx hK M S c = vtx hK M S d →
      vtx hK M S a ≠ vtx hK M S c →
      (mkGenome hK S).Preceding a ≠ (mkGenome hK S).Preceding b →
      (mkGenome hK S).Preceding c = (mkGenome hK S).Preceding d →
      BackAgrees hK S c d p →
      ¬ BackAgrees hK S c d (p + 1) →
      ¬ LongObstruction hK M S →
      (prevPos hK)^[p] c = a ∧ (prevPos hK)^[p] d = b ∨
      (prevPos hK)^[p] c = b ∧ (prevPos hK)^[p] d = a

end Case1

end AssemblyP1.BBTReplacement
