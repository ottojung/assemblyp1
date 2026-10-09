import AssemblyP1.SourceFaithfulIs

/-!
# The two-disjoint-circles duplex model (V5): a kernel-checked analysis

`AssemblyP1.DoubleStrandBridgingTransfer` kernel-checks the Bresler et al.
(2013) double-strand remap (V3), which maps the duplex to the single
length-`2G` circle `S · rc(S)`.  This module checks the alternative model
(V5) proposed for issue #215: represent duplex DNA as **two disjoint
circular strands** `(S, rc(S))`, each of length `G`, rather than as the
single artificial circle `S · rc(S)`.

Under V5 the duplex spectrum is exact, with **no seam terms**:

    spec_duplex(w) = spec_S(w) + spec_rcS(w) = spec_S(w) + spec_S(rc(w)),

giving exactly `2G` oriented windows.  A read at `S`-start `t` has its
reverse-complement partner at `rc(S)`-start `(G - t - L) mod G`, exactly,
even when the read wraps (there is no seam and no wrapping failure).

Two readings of the single-strand `I_s` on the duplex are possible:

* **Circle-by-circle.**  `I_s` is applied to each strand separately:
  `I_s` on `S` with the realized read set, and `I_s` on `rc(S)` with the
  partner read set.  By the `rc` symmetry this is *exactly equivalent* to
  `I_s` on `S` alone, so V5 is exactly compatible with the oriented
  single-strand reduction under this reading.

* **Duplex-as-a-whole.**  `I_s` is applied to the duplex as a single object
  of `2G` positions.  This reading is **not well-defined** (two disjoint
  circles have no natural cyclic order for the interleaving condition) and,
  even ignoring interleaving, is **strictly stronger** than the single-strand
  `I_s`: the duplex carries *mixed triple repeats* (copies on both circles)
  of length `≥ L - 1`, which `bridgesCopy_length` (`e + 2 ≤ L`) forbids any
  length-`L` read from bridging.

This module kernel-checks, for the `AAATAT` witness:

1. the reverse-complement circle `rc(S)` and the read-placement map
   `(G - t - L) mod G` (the partner read carries the reverse complement);
2. `I_s` on `rc(S)` with the partner read set (the circle-by-circle reading
   holds, confirming exact compatibility);
3. the duplex spectrum identity `spec_duplex(w) = spec_S(w) + spec_S(rc(w))`;
4. the mixed triple repeats of the duplex are maximal and have `e ≥ L - 1`,
   hence are unbridgeable (the duplex-as-a-whole reading fails).

The module is a deliberately tiny evaluator on the shared `Genome` substrate
of `AssemblyP1.SourceFaithfulIs`.  It adds no new library infrastructure and
is not witness-specific beyond this instance.

See `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`
§10 for the mathematical appendix, the audited witnesses, and the explicit
non-equivalences.
-/

namespace AssemblyP1.TwoDisjointCirclesDuplex

open AssemblyP1.SourceFaithfulIs

/-- Two-symbol alphabet for the witness; the reverse-complement involution is
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

/-- The true circular genome `S = AAATAT` of length `6`. -/
def S : Fin 6 → Base := ![.A, .A, .A, .T, .A, .T]

/-- The reverse-complement circle `rc(S) = ATATTT`. -/
def rcS : Fin 6 → Base := ![.A, .T, .A, .T, .T, .T]

/-- The shared `Genome` representation of the truth `S = AAATAT`.

This is a reducible abbreviation, not an opaque `def`, so that the
`Fin`-indexed numerals and the `Decidable` instances of the shared layer are
found by instance search when `I_s` membership is decided. -/
abbrev truthGenome : Genome Base where
  len := 6
  len_pos := by norm_num
  sym := S

/-- The shared `Genome` representation of the reverse-complement circle
`rc(S) = ATATTT`, likewise a reducible abbreviation. -/
abbrev rcGenome : Genome Base where
  len := 6
  len_pos := by norm_num
  sym := rcS

/-! ### The reverse-complement circle is correct

`rcS` is componentwise the reverse complement of `S`: `rcS[i] = comp(S[5 - i])`,
since `rc(w)_d = comp(w_{L-1-d})` and the circle `rc(S)` satisfies
`rc(S)[i] = comp(S[(G-1-i) mod G])`. -/

/-- `rcS` is the reverse complement of `S`, componentwise. -/
theorem rcS_rc : ∀ i : Fin 6, rcS i = comp (S ⟨(6 - 1 - i.val) % 6, by omega⟩) := by
  intro i; fin_cases i <;> decide

/-! ### The read-placement map

A read at `S`-start `t` (the length-`L` window `S[t .. t+L)`) has its
reverse complement at `rc(S)`-start `(G - t - L) mod G`.  This is exact for
every `t`, including wrapping reads, because the two circles are disjoint
and each has its own origin. -/

/-- The V5 read-placement map: `S`-start `t` ↦ `rc(S)`-start `(G - t - L) mod G`.
The representative `2*6 - t - 3` is used rather than `6 - t - 3` so that the
subtraction does not saturate for `t = 4, 5` (Nat subtraction truncates). -/
def partnerStart (t : Fin 6) : Fin 6 :=
  ⟨(2 * 6 - t.val - 3) % 6, by omega⟩

/-- Circular symbol access for a length-`6` genome. -/
def cyc6 (g : Fin 6 → Base) (i : Nat) : Base :=
  g ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The duplex symbol at `(circle, position)`: `false` is the `S` circle,
`true` is the `rc(S)` circle. -/
def duplexCycl (b : Bool) (i : Nat) : Base :=
  if b then cyc6 rcS i else cyc6 S i

/-- The length-`3` duplex window at `(circle, start)`. -/
def duplexWindow (b : Bool) (r : Fin 6) (d : Fin 3) : Base :=
  duplexCycl b (r.val + d.val)

/-- **The partner read carries the reverse complement, componentwise.**
For every `S`-start `t` and every offset `d : Fin 3`, the `rc(S)`-window at
the partner start `(G - t - L) mod G` equals the reverse complement of the
`S`-window at `t`, symbol by symbol.  This is the exactness of the V5
read-placement map; it holds for wrapping reads too. -/
theorem partner_window_rc (t : Fin 6) (d : Fin 3) :
    duplexWindow true (partnerStart t) d =
      comp (duplexWindow false t ⟨2 - d.val, by omega⟩) := by
  fin_cases t <;> fin_cases d <;> decide

/-! ### The realized read set and its partner

The sampling realization is `[0, 0, 1, 3, 5]` (start `0` sampled twice);
the distinct start set is `{0, 1, 3, 5}`.  The partner read set on `rc(S)` is
the image under the placement map, `{0, 2, 3, 4}`. -/

/-- The realized distinct `S`-start set. -/
def realizedStarts : Finset (Fin 6) := {0, 1, 3, 5}

/-- The partner `rc(S)`-start set: the image of the realized starts under the
read-placement map. -/
def partnerStarts : Finset (Fin 6) := {0, 2, 3, 4}

/-- The partner start set is exactly the image of the realized start set under
the read-placement map. -/
theorem partnerStarts_eq :
    partnerStarts = realizedStarts.image (fun t => partnerStart t) := by
  decide

/-! ### The circle-by-circle reading holds

Under the circle-by-circle reading, `I_s` is applied to each strand separately.
The key check is that `I_s` holds on `rc(S)` with the partner read set.  By
the `rc` symmetry (the map `(circle, start) ↦ (other circle, (G-start-L) mod G)`
is a bijection preserving windows up to `rc`, preceding/following symbols up
to `comp`, and bridging), `I_s` on `rc(S)` with the partner reads is equivalent
to `I_s` on `S` with the realized reads.  The latter is kernel-checked on `main`
(`SameLengthSection62Counterexample.truth_information_feasible`), so the two
are exactly compatible. -/

/-- **The circle-by-circle reading holds: `I_s` on `rc(S)` with the partner
read set.**  This is `SourceFaithfulIs.InformationFeasible` at full strength —
coverage, every triple repeat all-bridged, and every interleaved pair bridged,
quantified over all repeat lengths and all selected starts — discharged by
finite `decide` on the `Genome` object `rcGenome` with read length `3` and the
partner start set `{0, 2, 3, 4}`. -/
theorem rcS_information_feasible :
    InformationFeasible rcGenome 3 partnerStarts := by
  decide

/-! ### The duplex spectrum identity

For any oriented `L`-mer `w`, the V5 duplex spectrum is
`spec_duplex(w) = spec_S(w) + spec_S(rc(w))`: the number of duplex windows
equal to `w` (summed over both circles) equals the number of `S`-windows
equal to `w` plus the number of `S`-windows equal to `rc(w)`.  There are no
seam terms, and the total is exactly `2G`. -/

/-- Window equality for length-`3` words. -/
def windowEq (w1 w2 : Fin 3 → Base) : Bool :=
  w1 0 == w2 0 && w1 1 == w2 1 && w1 2 == w2 2

/-- The number of `S`-starts whose length-`3` window equals `w`. -/
def specS (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 => windowEq (duplexWindow false r) w)).card

/-- The number of `S`-starts whose length-`3` window equals `rc(w)`. -/
def specS_rc (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 =>
    windowEq (duplexWindow false r) ![comp (w 2), comp (w 1), comp (w 0)])).card

/-- The V5 duplex spectrum: the number of duplex windows (both circles) equal
to `w`. -/
def specDuplex (w : Fin 3 → Base) : Nat :=
  (Finset.univ.filter (fun r : Fin 6 => windowEq (duplexWindow false r) w)).card +
    (Finset.univ.filter (fun r : Fin 6 => windowEq (duplexWindow true r) w)).card

/-- **The V5 duplex spectrum identity.**  For every oriented length-`3` word
`w`, `spec_duplex(w) = spec_S(w) + spec_S(rc(w))`.  This is the exactness of
the V5 spec function; it is discharged by finite computation over the eight
length-`3` words. -/
theorem specDuplex_eq (w : Fin 3 → Base) :
    specDuplex w = specS w + specS_rc w := by
  decide +revert

/-! ### The duplex-as-a-whole reading fails

Under the duplex-as-a-whole reading, `I_s` is applied to the duplex as a
single object of `2G` positions.  This reading is not well-defined (two
disjoint circles have no natural cyclic order for the interleaving condition)
and, even ignoring interleaving, is strictly stronger than the single-strand
`I_s`: the duplex carries *mixed triple repeats* (three positions with equal
windows, not all on the same circle) of length `≥ L - 1`, which
`bridgesCopy_length` (`e + 2 ≤ L`) forbids any length-`L` read from bridging.

The following kernel-checks establish that the six mixed triple repeats of
length `≥ L - 1 = 2` of the `AAATAT` duplex are maximal (in the source's
three-copy sense), hence unbridgeable.  They were independently enumerated
from scratch (see `scripts/verify_two_disjoint_circles_duplex.py` §2).

**Predicate soundness.**  The agreement test compares **exactly `e`**
positions, `windowsAgree`, not a fixed three.  Comparing a fixed three for
every `e` would be unsound: for `e = 2` it would demand equal `3`-mers (so no
length-`2` repeat could ever satisfy it), and for `e ≥ 4` it would compare
only the first three positions and therefore *under*check. -/

/-- Equality of duplex positions (as `(circle, start)` pairs). -/
def posEq : (Bool × Fin 6) → (Bool × Fin 6) → Bool
  | (b1, t1), (b2, t2) => b1 == b2 && t1 == t2

/-- The length-`e` windows at `(b1,t1)` and `(b2,t2)` agree: exactly the `e`
positions `d < e` are compared. -/
def windowsAgree (b1 : Bool) (t1 : Fin 6) (b2 : Bool) (t2 : Fin 6) (e : Nat) : Bool :=
  (List.range e).all (fun d => duplexCycl b1 (t1.val + d) == duplexCycl b2 (t2.val + d))

/-- The symbol immediately preceding the copy at `(circle, t)`. -/
def duplexPreceding (b : Bool) (t : Fin 6) : Base :=
  duplexCycl b (t.val + 5)

/-- The symbol immediately following the length-`e` copy at `(circle, t)`. -/
def duplexFollowing (b : Bool) (t : Fin 6) (e : Nat) : Base :=
  duplexCycl b (t.val + e)

/-- **A maximal triple repeat of the duplex** (in the source's three-copy
sense) with the three selected positions `(b1,t1)`, `(b2,t2)`, `(b3,t3)` and
length `e`: the three positions are pairwise distinct, the three length-`e`
windows agree (exactly `e` positions), and the preceding (respectively
following) symbols are not all equal. -/
def isDuplexTripleRepeat (e : Nat) (p1 p2 p3 : Bool × Fin 6) : Bool :=
  let (b1, t1) := p1
  let (b2, t2) := p2
  let (b3, t3) := p3
  (1 ≤ e) && (e < 6) &&
    (!posEq p1 p2 && !posEq p1 p3 && !posEq p2 p3) &&
    (windowsAgree b1 t1 b2 t2 e) && (windowsAgree b1 t1 b3 t3 e) &&
    (!(duplexPreceding b1 t1 == duplexPreceding b2 t2 &&
        duplexPreceding b2 t2 == duplexPreceding b3 t3)) &&
    (!(duplexFollowing b1 t1 e == duplexFollowing b2 t2 e &&
        duplexFollowing b2 t2 e == duplexFollowing b3 t3 e))

/-- **Length-`2` mixed triple repeat, word `AT`:** at `rc(S)`-starts `0`, `2`
and `S`-start `2`.  Preceding `T,T,A`; following `A,T,A`.  Length `2 ≥ L-1 = 2`,
so unbridgeable by `bridgesCopy_length`. -/
theorem mixed_triple_repeat_2a :
    isDuplexTripleRepeat 2 (true, ⟨0, by norm_num⟩) (true, ⟨2, by norm_num⟩)
      (false, ⟨2, by norm_num⟩) = true := by
  decide

/-- **Length-`2` mixed triple repeat, word `AT`:** at `rc(S)`-start `2`,
`S`-starts `2`, `4`.  Preceding `T,A,T`; following `T,A,A`.  Unbridgeable. -/
theorem mixed_triple_repeat_2b :
    isDuplexTripleRepeat 2 (true, ⟨2, by norm_num⟩) (false, ⟨2, by norm_num⟩)
      (false, ⟨4, by norm_num⟩) = true := by
  decide

/-- **Length-`2` mixed triple repeat, word `TA`:** at `rc(S)`-starts `1`, `5`,
`S`-start `5`.  Preceding `A,T,A`; following `T,T,A`.  Unbridgeable. -/
theorem mixed_triple_repeat_2c :
    isDuplexTripleRepeat 2 (true, ⟨1, by norm_num⟩) (true, ⟨5, by norm_num⟩)
      (false, ⟨5, by norm_num⟩) = true := by
  decide

/-- **Length-`2` mixed triple repeat, word `TA`:** at `rc(S)`-start `5`,
`S`-starts `3`, `5`.  Preceding `T,A,A`; following `T,T,A`.  Unbridgeable. -/
theorem mixed_triple_repeat_2d :
    isDuplexTripleRepeat 2 (true, ⟨5, by norm_num⟩) (false, ⟨3, by norm_num⟩)
      (false, ⟨5, by norm_num⟩) = true := by
  decide

/-- **Length-`3` mixed triple repeat, word `ATA`:** at `rc(S)`-start `0`,
`S`-starts `2`, `4`.  Preceding `T,A,T`; following `T,T,A`.  Unbridgeable. -/
theorem mixed_triple_repeat_3a :
    isDuplexTripleRepeat 3 (true, ⟨0, by norm_num⟩) (false, ⟨2, by norm_num⟩)
      (false, ⟨4, by norm_num⟩) = true := by
  decide

/-- **Length-`3` mixed triple repeat, word `TAT`:** at `rc(S)`-starts `1`, `5`,
`S`-start `3`.  Preceding `A,T,A`; following `T,A,A`.  Unbridgeable. -/
theorem mixed_triple_repeat_3b :
    isDuplexTripleRepeat 3 (true, ⟨1, by norm_num⟩) (true, ⟨5, by norm_num⟩)
      (false, ⟨3, by norm_num⟩) = true := by
  decide

/-- A control: the predicate is **not** vacuous and **not** trivially true.
For `e = 2` the three windows `AT` at `(true,0)`, `(true,2)` and `(false,0)`
do **not** agree on their second position, so this is not a triple repeat.
This is the kernel-checked witness that `windowsAgree` really compares the
window positions and not merely the first symbol. -/
theorem not_triple_repeat_control :
    isDuplexTripleRepeat 2 (true, ⟨0, by norm_num⟩) (true, ⟨2, by norm_num⟩)
      (false, ⟨0, by norm_num⟩) = false := by
  decide

/-- A control: for `e = 3`, requiring equal `3`-mers is the correct test, and
the length-`3` mixed triple repeat above satisfies it.  The predicate therefore
does not collapse to a length-`1` test. -/
theorem triple_repeat_3_nonvacuous :
    windowsAgree true ⟨0, by norm_num⟩ false ⟨2, by norm_num⟩ 3 = true := by
  decide

/-! ### The headline non-equivalence

The two readings of `I_s` on the two-disjoint-circles duplex give different
answers on the same witness:

* circle-by-circle: `I_s` holds (the duplex reduces to `I_s` on `S`);
* duplex-as-a-whole: `I_s` fails (mixed triple repeats of length `≥ L - 1`
  are unbridgeable, for every read set).

So the two-disjoint-circles model is **not** a relabelling of the
single-strand model: the reading of `I_s` on the duplex is material, and the
duplex-as-a-whole reading is strictly stronger (and not well-defined without
a convention for cross-circle interleaving).  The circle-by-circle reading is
the one that is exactly compatible with the oriented single-strand reduction. -/

/-- **The two readings diverge on the same duplex.**  The circle-by-circle
reading holds (`rcS_information_feasible`), while the duplex-as-a-whole
reading fails because the length-`2` mixed triple repeat
`AT @ {rc(S):0, rc(S):2, S:2}` is a maximal triple repeat of length
`2 ≥ L - 1` and hence unbridgeable by any read of length `L = 3`
(`bridgesCopy_length`: `e + 2 ≤ L`).  Hence `I_s` on the duplex-as-a-whole
is violated for every read set. -/
theorem two_readings_diverge :
    InformationFeasible rcGenome 3 partnerStarts ∧
      isDuplexTripleRepeat 2 (true, ⟨0, by norm_num⟩) (true, ⟨2, by norm_num⟩)
        (false, ⟨2, by norm_num⟩) = true :=
  ⟨rcS_information_feasible, mixed_triple_repeat_2a⟩

end AssemblyP1.TwoDisjointCirclesDuplex
