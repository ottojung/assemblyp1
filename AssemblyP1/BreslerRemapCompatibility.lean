import AssemblyP1.SourceFaithfulIs
import AssemblyP1.DoubleStrandBridgingTransfer
import AssemblyP1.SameLengthSection62Counterexample

/-!
# Exact compatibility of the Bresler 2G remap (V3) with the oriented model

`AssemblyP1.DoubleStrandBridgingTransfer` kernel-checks one direction of the
relation between the Bresler, Bresler and Tse (2013) double-strand remap (V3)
and the oriented single-strand information-feasible set `I_s` of Shomorony et
al. (2016) (V1/V2): the `AAATAT → AAAAAT` witness is `I_s`-feasible on the
single strand but *not* on the Bresler-doubled length-`2G` circle.  This module
kernel-checks the **other direction**, and hence that the two models are
genuinely **incomparable** rather than one being a refinement of the other.

The Bresler remap maps a circular genome `S` to the length-`2G` circle
`S · ρ(S)` and each realized read to itself and its reverse complement.  It is
*sound* (V3 ⟹ V1/V2) only if every realized read of the circular genome has a
**faithful seat** in `S · ρ(S)`: a wrapping read's string need not occur in
`S · ρ(S)`, and the natural-seat completion `t ↦ G + t` then places it at a
position where it does not occur.  The witness `S = GGGA` exhibits exactly this:

* `I_s` on the **doubled** circle `GGGATCCC` with the natural-seat doubled read
  set `{0,1,4,5,6,7}` **holds**;
* `I_s` on `S = GGGA` with the realized read set `{0,1,2}` **fails** — the
  maximal triple repeat `G @ {0,1,2}` has its copy at position `0`
  unbridgeable, because no read of the realized set covers a base before `0`;
* the doubled reading holds *only* because the natural-seat completion places
  the wrapping read `GAG` (and its reverse complement `CTC`) at seats `6` and
  `7`, where the actual windows are `CCG` and `CGG`.  Both seats are spurious.

Together with the `AAATAT` witness (V1/V2 holds, V3 fails), this shows the
Bresler remap is neither sound nor complete relative to the oriented model.  The
exact compatibility locus is the conjunction of

* **(R1) read-seat preservation** — every realized read has a faithful seat in
  `S · ρ(S)`;
* **(R2) seam–wrap agreement** — `j_S(w) = wrap_S(w) + wrap_S(ρ(w))` for every
  word `w`, i.e. the doubled and two-disjoint-circles candidate spectra agree;
* **(R3) feasibility on the doubled circle** — `I_s` holds on `S · ρ(S)`.

The two-disjoint-circles duplex model (V5, `AssemblyP1.TwoDisjointCirclesDuplex`)
resolves R1 and R2 **by construction** under its circle-by-circle reading, and
is exactly compatible with V1/V2 (the `rc` symmetry).  Hence V3 coincides with
V5 exactly on the R1∧R2∧R3 locus; off it, V3 is a seam artifact and no verdict
may be transferred between V3 and V5 without naming the reading.  See
`docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`
§11 for the appendix.

The module is a deliberately tiny evaluator on the shared `Genome` substrate of
`AssemblyP1.SourceFaithfulIs`; it adds no library infrastructure.
-/

namespace AssemblyP1.BreslerRemapCompatibility

open AssemblyP1.SourceFaithfulIs

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-- Four-symbol DNA alphabet, so that the `GGGA` witness has the two symbols
`G`, `C` that the two-symbol `AAATAT` witness lacks. -/
inductive Base4 where
  | A
  | C
  | G
  | T
  deriving DecidableEq, Inhabited, Repr

instance : Fintype Base4 where
  elems := {Base4.A, Base4.C, Base4.G, Base4.T}
  complete := by intro x; cases x <;> simp

/-- DNA complement on the four-symbol alphabet. -/
def comp4 : Base4 → Base4
  | .A => .T
  | .T => .A
  | .C => .G
  | .G => .C

/-! ### The `GGGA` witness and its Bresler doubling -/

/-- The true circular genome `S = GGGA` of length `4`. -/
abbrev ggga : Genome Base4 where
  len := 4
  len_pos := by norm_num
  sym := ![.G, .G, .G, .A]

/-- The Bresler doubled circle `S · ρ(S) = GGGATCCC`, of length `8`.  Its second
half `TCCC` is `ρ(GGGA) = comp(reverse(GGGA))`. -/
abbrev gggaDbl : Genome Base4 where
  len := 8
  len_pos := by norm_num
  sym := ![.G, .G, .G, .A, .T, .C, .C, .C]

/-- The symbol list of the doubled circle is exactly `GGGA` followed by
`TCCC = ρ(GGGA)`. -/
theorem gggaDbl_symbols :
    (List.ofFn gggaDbl.sym) = [.G, .G, .G, .A, .T, .C, .C, .C] := by
  decide

/-- The realized distinct read starts of `GGGA`; the sampling realization used in
the appendix is `[0,1,2]` (all distinct). -/
def gggaStarts : Finset (Fin 4) := {0, 1, 2}

/-- The Bresler-doubled read starts in the natural-seat reading: the seats
`0,1` of the non-wrapping reads, the partner seats `5,4`, and the seats `6,7`
of the *wrapping* read `GAG` and its reverse complement `CTC`. -/
def gggaDblStarts : Finset (Fin 8) := {0, 1, 4, 5, 6, 7}

/-! ### The two directions of the incomparability

`gggaDbl_information_feasible` is the V3 hypothesis; `ggga_not_information_feasible`
is the negation of the V1/V2 hypothesis.  Together they show V3 does not imply
V1/V2. -/

/-- **The Bresler-doubled `GGGA` instance is `I_s`-feasible.**  This is
`SourceFaithfulIs.InformationFeasible` at full strength — coverage, every triple
repeat all-bridged, and every interleaved pair bridged — discharged by finite
`decide` on the length-`8` doubled circle `GGGATCCC` with the natural-seat
doubled read set `{0,1,4,5,6,7}`. -/
theorem gggaDbl_information_feasible :
    InformationFeasible gggaDbl 3 gggaDblStarts := by
  decide

/-- **The undoubled `GGGA` instance is not `I_s`-feasible.**  The maximal triple
repeat `G @ {0,1,2}` (length `1`) has its copy at position `0` unbridgeable by
the realized read set `{0,1,2}`: a read bridges the copy at `0` only from the
seat `3`, which is not in the set.  Hence clause 2 of `I_s` fails. -/
theorem ggga_not_information_feasible :
    ¬ InformationFeasible ggga 3 gggaStarts := by
  decide

/-- **V3 does not imply V1/V2 (under the natural-seat reading).**  The doubled
`GGGA` instance satisfies the Bresler-remapped `I_s` while the undoubled genome
does not satisfy the oriented `I_s`.  This is the R1 (read-seat) failure. -/
theorem remap_natural_seat_not_sound :
    InformationFeasible gggaDbl 3 gggaDblStarts ∧
      ¬ InformationFeasible ggga 3 gggaStarts :=
  ⟨gggaDbl_information_feasible, ggga_not_information_feasible⟩

/-! ### Why: the wrapping read's seats are spurious

The read at `S`-start `2` is `GAG` (it wraps: `2 > G - L = 1`).  Its reverse
complement is `CTC`.  Neither word occurs in `S · ρ(S) = GGGATCCC`.  The
natural-seat completion nevertheless places them at the seats `6` and `7`, whose
windows are `CCG` and `CGG`.  Those two windows are what bridge the copy at
position `0`; without them the doubled instance is not `I_s`-feasible.  This is
the R1 artifact. -/

/-- The wrapping read `GAG` of `S = GGGA` at start `2`. -/
def gag : Fin 3 → Base4 := ![.G, .A, .G]

/-- The reverse complement `CTC` of the wrapping read `GAG`. -/
def ctc : Fin 3 → Base4 := ![.C, .T, .C]

/-- The window at the natural seat `6` is `CCG`, not the wrapping read `GAG`. -/
theorem seat6_spurious :
    gggaDbl.window 3 ⟨6, by norm_num⟩ ≠ gag := by
  decide

/-- The window at the natural seat `7` is `CGG`, not the reverse complement
`CTC` of the wrapping read. -/
theorem seat7_spurious :
    gggaDbl.window 3 ⟨7, by norm_num⟩ ≠ ctc := by
  decide

/-- The two spurious seats `6` and `7` are exactly the seats contributed by the
wrapping read: they are absent from the seats of the two non-wrapping reads. -/
theorem spurious_seats_are_the_wrapping_pair :
    gggaDblStarts = ({0, 1, 4, 5} : Finset (Fin 8)) ∪ {6, 7} := by
  decide

/-! ### The other direction: V1/V2 does not imply V3

This direction is the already kernel-checked `AAATAT` witness, imported from
`AssemblyP1.SameLengthSection62Counterexample` (oriented feasibility) and
`AssemblyP1.DoubleStrandBridgingTransfer` (doubled infeasibility). -/

/-- **V1/V2 does not imply V3.**  The `AAATAT` witness is `I_s`-feasible on the
oriented single strand but not on the Bresler-doubled length-`12` circle, for
*every* realized read set.  This is the R3 (feasibility on the doubled circle)
failure, caused by the seam-created maximal triple repeat `ATAT @ {2,4,6}`. -/
theorem remap_not_complete :
    InformationFeasible SameLengthSection62Counterexample.truthGenome 3
        SameLengthSection62Counterexample.realizedStarts ∧
      (∀ R : Finset (Fin 12),
        ¬ InformationFeasible DoubleStrandBridgingTransfer.doubled 3 R) :=
  ⟨SameLengthSection62Counterexample.truth_information_feasible,
    DoubleStrandBridgingTransfer.doubled_not_information_feasible⟩

/-! ### The V5 reconciliation

The two-disjoint-circles model (V5) applies `I_s` circle-by-circle to `S` and
`rc(S)`.  For the `GGGA` witness the reverse-complement circle is `rc(S) = TCCC`
and the partner read set of `{0,1,2}` is `{0,1,3}`.  Both circle-by-circle
conjuncts fail, matching V1/V2 and diverging from the natural-seat V3.  This is
the concrete reconciliation: V3 and V5 disagree exactly on the R1 locus. -/

/-- The reverse-complement circle `rc(GGGA) = TCCC`. -/
abbrev tccc : Genome Base4 where
  len := 4
  len_pos := by norm_num
  sym := ![.T, .C, .C, .C]

/-- The partner read set of `{0,1,2}` under the V5 read map
`t ↦ (G - t - L) mod G`, i.e. `(4 - t - 3) mod 4`. -/
def tcccPartnerStarts : Finset (Fin 4) := {0, 1, 3}

/-- The V5 circle-by-circle hypothesis for the `GGGA` witness fails on both
circles.  Since V5 circle-by-circle is exactly equivalent to `I_s` on `S`, this
matches `ggga_not_information_feasible` and shows V5 sides with V1/V2, not with
the natural-seat V3. -/
theorem v5_ggga_fails :
    ¬ InformationFeasible ggga 3 gggaStarts ∧
      ¬ InformationFeasible tccc 3 tcccPartnerStarts := by
  refine ⟨ggga_not_information_feasible, ?_⟩
  decide

end AssemblyP1.BreslerRemapCompatibility
