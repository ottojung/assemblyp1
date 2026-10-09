import AssemblyP1.SourceFaithfulIs

/-!
# Oriented versus double-strand bridging: a kernel-checked non-equivalence

`AssemblyP1.SameLengthSection62Counterexample` kernel-checks, for the molecule
(reverse-complement-collapsed) Medvedev–Brudno read representation, that the
truth `S = AAATAT` satisfies Shomorony et al.'s information-feasible set `I_s`
for the realized read set `{0,1,3,5}`, and that the competitor `D = AAAAAT`
strictly beats it (exact same-length multinomial ratio `3`, literal §6.1
fixed-`N` binomial ratio `5`).  That witness is therefore a counterexample for
the reading "Shomorony's oriented `I_s` jointly with the MB09 molecule
objective" — and only for that reading.

This module checks the *other* double-strand reading and shows that the two are
**not** interchangeable.  Bresler, Bresler and Tse (2013), "Discussions and
extensions", give an explicit double-strand reduction into their single-strand
model:

> "DNA is double-stranded and consists of a length-`G` sequence `u` and its
> reverse complement `u~`. Each read is either sampled from `u` or `u~`. This
> more realistic scenario can be mapped into our single-strand model by defining
> `s` as the length-`2G` concatenation of `u` and `u~`, transforming each read
> into itself and its reverse complement so that there are `2N` reads.
> Generalized Ukkonen's conditions hold verbatim for this problem …"

Under that reduction the `AAATAT → AAAAAT` witness is **inadmissible**: its
doubled genome is the length-`12` circle `AAATATATATTT`, and that circle carries
a maximal triple repeat of length `4` (the word `ATATA` at starts `2, 4, 6`).
Since a bridged copy of length `e` needs `e + 2 ≤ L`
(`AssemblyP1.SourceFaithfulIs.bridgesCopy_length`), no read of length `L = 3`
can bridge any copy of it, for **any** read set.  Hence the doubled instance is
not `I_s`-feasible, and the integrated molecule witness transmits neither a
counterexample nor a positive result to the Bresler double-strand reading.

The module is a deliberately tiny evaluator.  It fixes the doubled genome, proves
the delicate three-copy-maximality content of that triple repeat by computation
on the shared `Genome` substrate of `AssemblyP1.SourceFaithfulIs`, kernel-checks
the read-partner placements that Bresler's doubling induces, and derives
non-feasibility from the already kernel-checked length obstruction.  It adds no
new library infrastructure and is not witness-specific beyond this instance.

See `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`
for the mathematical appendix, the audited witnesses, and the explicit
non-equivalences.
-/

namespace AssemblyP1.DoubleStrandBridgingTransfer

open AssemblyP1.SourceFaithfulIs

/-- Two-symbol alphabet for the audit; the reverse-complement involution is
`A ↔ T`. -/
inductive Base where
  | A
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base where
  elems := {Base.A, Base.T}
  complete := by intro x; cases x <;> simp

/-- DNA reverse complement on the two-symbol alphabet. -/
def comp : Base → Base
  | .A => .T
  | .T => .A

/-- The Bresler doubled genome `S · ρ(S)` of `S = AAATAT`, i.e. the length-`12`
circle `AAATATATATTT`.  This is the circle the 2013 remap feeds to the
single-strand conditions. -/
def doubled : Genome Base where
  len := 12
  len_pos := by decide
  sym := ![.A, .A, .A, .T, .A, .T, .A, .T, .A, .T, .T, .T]

/-! ### The doubled genome really is `S · ρ(S)`

The symbol list is kernel-checked to be exactly `AAATAT` followed by
`ATATTT = ρ(AAATAT)`, i.e. Bresler's `u ~`.
-/

/-- The doubled genome is the length-`12` circle `AAATATATATTT`. -/
theorem doubled_symbols :
    (List.ofFn doubled.sym) = [.A, .A, .A, .T, .A, .T, .A, .T, .A, .T, .T, .T] := by
  decide

/-! ### The Bresler read-partner placements

In the doubled circle, the reverse complement of the length-`3` window starting
at absolute position `b` is the window starting at absolute position
`2G - b - L`.  Kernel-checked for the four distinct starts of the realized
`AAATAT` read set and their partners: start `0 ↦ 9`, `1 ↦ 8`, `3 ↦ 6`, and the
wrapping read at `11 ↦ 10`.
-/

theorem partner_placements :
    doubled.window 3 ⟨9, by decide⟩ 0 = comp (doubled.window 3 ⟨0, by decide⟩ 2) ∧
      doubled.window 3 ⟨8, by decide⟩ 0 = comp (doubled.window 3 ⟨1, by decide⟩ 2) ∧
      doubled.window 3 ⟨6, by decide⟩ 0 = comp (doubled.window 3 ⟨3, by decide⟩ 2) ∧
      doubled.window 3 ⟨10, by decide⟩ 0 = comp (doubled.window 3 ⟨11, by decide⟩ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### The unbridgeable maximal triple repeat of the doubled genome

`ATATA` occurs at starts `2, 4, 6`.  It is maximal in the source's three-copy
sense: the symbols preceding the three copies are `A, T, T` (not all equal) and
the symbols following them are `A, A, T` (not all equal), so the copy triple
cannot be extended in either direction.
-/

theorem doubled_agree_2_4 : Genome.Agree doubled 4 ⟨2, by decide⟩ ⟨4, by decide⟩ := by
  intro d; fin_cases d <;> rfl

theorem doubled_agree_2_6 : Genome.Agree doubled 4 ⟨2, by decide⟩ ⟨6, by decide⟩ := by
  intro d; fin_cases d <;> rfl

theorem doubled_agree_4_6 : Genome.Agree doubled 4 ⟨4, by decide⟩ ⟨6, by decide⟩ := by
  intro d; fin_cases d <;> rfl

/-- The length-`4` repeat `ATATA` at starts `2, 4, 6` is a maximal triple repeat
of the doubled genome. -/
theorem doubled_triple_repeat :
    Genome.IsTripleRepeat doubled 4 ⟨2, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    doubled_agree_2_4, doubled_agree_2_6, doubled_agree_4_6,
    by decide, by decide⟩

/-! ### The headline non-equivalence

Because a bridged copy of length `e` must satisfy `e + 2 ≤ L`, the length-`4`
repeat cannot be bridged by any read of length `L = 3`, whatever the realized
read set is.  Clause 2 of `I_s` is therefore violated for every read set.
-/

/-- **The Bresler-doubled instance of the `AAATAT → AAAAAT` witness is not
`I_s`-feasible, for every realized read set.**

The single-strand `I_s` certificate of the *undoubled* witness is kernel-checked
on `main` (`AssemblyP1.SameLengthSection62Counterexample.truth_source_certificate`),
so the same underlying witness is `I_s`-feasible in the molecule reading and
`I_s`-infeasible in the Bresler double-strand reading.  The two readings are
genuinely different, and no claim may be transferred silently from one to the
other. -/
theorem doubled_not_information_feasible (R : Finset (Fin 12)) :
    ¬ InformationFeasible doubled 3 R := by
  intro h
  have hab : IsTripleRepeatAllBridged doubled 3 R 4 ⟨2, by decide⟩ ⟨4, by decide⟩
      ⟨6, by decide⟩ :=
    InformationFeasible.triples h doubled_triple_repeat (by decide)
  have hlen : (4 : ℕ) + 2 ≤ 3 := bridgesCopy_length hab.1
  omega

end AssemblyP1.DoubleStrandBridgingTransfer
