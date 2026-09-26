# Audit: the bridging predicate, the corrected same-lift reading, and what it does to #88

Status: **kernel-checked** (`AssemblyP1/BridgesCopyLift.lean`, in the default build
and the `AssemblyP1.lean` axiom audit). No `sorry`, no `admit`, no new axioms;
the audit reports only `propext`, `Classical.choice`, `Quot.sound`.

## 1. The finding

`docs/bridging-source-semantics.md` records the source's bridging condition as a
**single-lift half-open interval** condition: a read `[r, r+L)` bridges a chosen
lifted occurrence `[t, t+ℓ)` exactly when

```
r < t      and      t + ℓ < r + L
```

i.e. the read **strictly contains** the selected copy, with at least one base on
each side. In that reading, a bridged copy must satisfy `ℓ + 2 ≤ L`.

`SourceFaithfulIs.BridgesCopy`, as merged, is **endpoint-only and modular**:

```
∃ r ∈ R, ReadCovers S L r ((t + G - 1) % G) ∧ ReadCovers S L r ((t + ℓ) % G)
```

It asks only that a read *touch* the base before the copy and the base after it.
It does **not** ask the read to contain the copy. When the complement arc is
short (`G - ℓ ≤ L`) one read reaches both flank bases by travelling the *other*
way round the circle. That is a read sitting on the opposite arc, not a read
extending a base on each side of the occurrence, so the two readings differ
exactly there, and the merged predicate is the **weaker** one. Consequently the
merged `InformationFeasible` (hence `I_s`) is **weaker than the source formula
records**: it accepts data sets the source would reject.

This is exactly the `e + 2 ≤ L ∨ G - e ≤ L` dichotomy of
`AssemblyP1.BridgingBridge.bridgingLength`: the merged predicate delivers the
first disjunct (straddling mode) *or* the second (wraparound mode), and the
second disjunct is not bridging in the source sense.

## 2. The kernel-checked non-equivalence

`AssemblyP1.LiftAudit.wraparound_witness_bridges_with_complement_arc` and
`wraparound_witness_not_bridged_lift`: the truth `AAAAB` at read length `3`,
copy of length `2` at start `0`, read at start `2`. That read covers position
`4` (the base before the copy) and position `2` (the base after it) across the
complement arc `{2,3,4}`, and `ℓ + 2 = 4 > L = 3`. So the merged predicate
bridges a copy that the source's interval formula does not bridge, and
`BridgesCopy_ne_BridgesCopyLift` records that the two are **not equivalent**
(the corrected one is strictly stronger, `BridgesCopyLift.to_old`).

Three independent computational readings of the corrected predicate (the
modular offset form, the direct lifted interval form, and Lean's `decide`) were
cross-checked and agree at every repository instance
(`scripts/issue88-bridging-lift-audit.py`).

## 3. The corrected predicate and its consequences

`LiftAudit.BridgesCopyLift S L R e t` is the modular form of the lifted
interval condition: the same read covers the base before the copy at offset `d`
and the base after it at offset `d + ℓ + 1`, both inside the read. Two proved
facts carry the whole correction:

| theorem | content |
| --- | --- |
| `BridgesCopyLift.to_old` | corrected ⟹ merged (strictly stronger) |
| `BridgesCopyLift.length_bound` | corrected ⟹ `ℓ + 2 ≤ L` |

and, with clause 2 of `I_s` restated in terms of it
(`LiftAudit.InformationFeasibleLift`):

| theorem | content |
| --- | --- |
| `informationFeasibleLift_triple_le` | corrected `I_s` ⟹ every triple repeat has length `≤ L - 2` |
| `informationFeasibleLift_no_longTripleRepeat` | **corrected `I_s` ⟹ `¬ HasLongTripleRepeat`** |
| `informationFeasibleLift_no_longTripleRepeat_any` | the same, for *every* certificate set `R` |
| `InformationFeasibleLift.to_old` | corrected `I_s` ⟹ merged `I_s`, clause by clause |
| `informationFeasibleLift_62_spelledML` | the #88 §6.2 ML endpoint under corrected `I_s`, with **no** long-triple-repeat premise and **no** culprit statement |

`informationFeasibleLift_no_longTripleRepeat` is note §3 "Fact D"
(`InformationFeasible → ¬ HasLongTripleRepeat`), which every module in this
repository has recorded as **external / not kernel-checked** precisely because
the merged predicate could not deliver it. It is now kernel-checked, in the
source-faithful reading.

### Effect on #88

* The `EscapeForcesMidRangeRepeat` crux of `AssemblyP1.MLEscape` is **not
  needed** in the source-faithful regime. It was introduced only because the
  merged predicate left the wraparound band (`max (L-1) (G-L) ≤ ℓ < G`)
  *reachable*; under the corrected predicate a triple repeat in that band has
  `ℓ + 2 > L` and is unbridgeable, so `I_s` cannot hold. Steps 1 and 2 of the
  culprit statement remain true, and the crux remains a true-looking statement
  of the merged model, but the published hypothesis does not leave the regime in
  which it was needed.
* The ML endpoint becomes `informationFeasible_62_spelledML_of_no_long_triple`
  at `hno := informationFeasibleLift_no_longTripleRepeat`.

## 4. Instance audit: every merged `I_s` witness, rechecked

All checks are `decide` on the predicate itself, inside
`AssemblyP1/BridgesCopyLift.lean`.

| module | truth | `L` | starts | merged `I_s` | **corrected `I_s`** | verdict |
| --- | --- | --- | --- | --- | --- | --- |
| `ExactVariantECounterexample` | `ACGT` | 2 | `{0,2}` | yes | **yes** | counterexample kept |
| `SameLengthExactMLCounterexample` | `AABB` | 2 | `{1,3}` | yes | **yes** | counterexample kept |
| `FiniteSamplingCounterexample` | `AABBC` | 3 | `{0,3}` | yes | **yes** | counterexample kept |
| `FixedLengthBinomialCounterexample` | `AAACC` | 3 | `{0,1,4}` | yes | **yes** | counterexample kept |
| `FixedLengthExactCounterexample` | `AAABB` | 3 | `{0,1,4}` | yes | **yes** | counterexample kept |
| `Section62BridgingCounterexample` | `AAATT` | 3 | `{0,1,4}` | yes | **yes** | counterexample kept |
| `SameLengthSection62Counterexample` | `AAATAT` | 3 | `{0,1,3,5}` | yes | **yes** | counterexample kept |
| `WraparoundTripleRepeat` | `AAAAB` | 3 | all | yes | **no** | witness superseded (§5) |
| `SameLength62Maximizer` header instance | `AAAAB` | 3 | all | yes | **no** | claim superseded (§5) |
| `MLEscape.truth0` (culprit instance) | `0000001` | 3 | all | no | **no** | unaffected |

**All seven #99 counterexample witnesses pass the corrected `I_s`**, so no
counterexample needs a replacement. The reason is structural, not luck: in every
one of them the repeats are short (`e ≤ L - 2`), so bridging is genuine in both
readings and the two predicates agree on those instances. Consequently:

* every merged counterexample theorem (`#99` and its siblings) keeps its
  hypothesis and its conclusion, and the audited conclusion — *source-faithful
  bridging hypotheses do not force the truth to be an ML maximizer* — is
  **unchanged and still kernel-checked**, now under the stronger hypothesis;
* the corrected `I_s` is non-vacuous: the seven instances witness it;
* the `#88` culprit instance `0000001` is infeasible in *both* readings (its
  maximal triple repeat of length `2` lies in the mid-range band `2 ≤ ℓ < 4`,
  already excluded by the merged clause), so the non-vacuity pairing there is
  unaffected.

## 5. The two failures: what replaces them

Both failing instances are `AAAAB`, and neither is a likelihood counterexample —
they are *feasibility* witnesses, used for one purpose only: to show that the
residual long-triple-repeat regime is non-empty.

* `AssemblyP1.WraparoundTripleRepeat` exists solely for that purpose ("the
  premise `¬ HasLongTripleRepeat` **cannot** be discharged from
  `InformationFeasible`"). Under the corrected reading that claim is not merely
  unsupported, it is **false**: `informationFeasibleLift_no_longTripleRepeat`
  discharges the premise. The correct rescoping is not a new instance but a
  rescoped claim, and the module's content becomes: *for the merged
  endpoint-only predicate the wraparound mode is real and the regime is
  non-empty; for the source-faithful same-lift predicate the regime is empty.*
  No replacement instance is required, and none exists: no `I_s`-feasible
  instance (corrected) can carry a long triple repeat at all, by the theorem
  above. Searching for a corrected-`I_s` replacement that still exhibits a long
  triple repeat is therefore not a search but a contradiction.
* The `SameLength62Maximizer` module header uses the same instance for the same
  purpose ("the residual regime is therefore non-empty, which is exactly why the
  premise is left visible"). Under the corrected reading the premise is
  dischargeable and the header's justification must be rescoped in the same way.
  The theorem `informationFeasible_62_maximizer` itself is unaffected: its
  `hno` premise is an explicit hypothesis, and its other hypotheses
  (`hfeas`, `hR`) are already documented as unused.

No counterexample search is needed for the failures, because the failures are
not counterexamples. Had any of the seven *counterexample* witnesses failed the
corrected `I_s`, it would have had to be replaced or rescoped, since a
counterexample proven under a hypothesis the source does not impose is not a
counterexample to the source's claim; the audit shows that case does not arise.

## 6. Merged theorems: what stays true

Nothing in the merged development is invalidated, because
`SourceFaithfulIs.BridgesCopy` and `SourceFaithfulIs.InformationFeasible` are
**left untouched** and every theorem that uses them is stated with them as
hypotheses. Concretely:

* all theorem statements and proofs in the repository continue to hold
  verbatim; no merged file had to be edited for the correction to be provable;
* the theorems that *consume* `I_s` keep meaning what they said. In particular
  `BridgingBridge`'s dichotomy, `MLEscape.informationFeasible_no_midRangeTriple`
  and `MLEscape.informationFeasible_62_spelledML_of_no_long_triple` remain true
  — they are true under the *weaker* hypothesis and the weaker hypothesis is
  still what they assume;
* the audit-relevant change is interpretive, not logical: the merged `I_s` is
  now known **not** to be the source's `I_s`, and any claim of the form "this
  data is source-feasible" must use the corrected predicate.

## 7. `R`: subset-only versus exact realized range

`InformationFeasible S L R` is **upward closed in `R`** (coverage and bridging
are both "some `r ∈ R`" clauses). So

* the subset-only reading used by the merged endpoints (`R ⊇ range ρ` with
  feasibility of some larger `R`) is a **weaker hypothesis** than exact-range
  feasibility, and admits data the source would reject;
* `scripts/issue88-exact-range-search.py` and
  `scripts/issue88-exact-range-fast.py` quantify the gap exactly. Binary
  `G = 5`, all `2 ≤ L ≤ 5`, every realization with `n ≤ 3` reads:

  | quantity | value |
  | --- | --- |
  | realizations enumerated | 7040 |
  | exact-range `I_s`-feasible | 3850 |
  | subset-only `I_s`-feasible (some `R ⊇ range ρ`) | 5390 |
  | subset-only feasible but **not** exact-range feasible | 1540 |
  | ML failures (a same-support candidate strictly beats the truth) at exact-range-feasible data | 0 |
  | of those, without a mid-range maximal triple repeat | 0 |

  The extreme case is a data set consisting of a **single** realized read, e.g.
  `S = 00000`, `L = 2`, realized range `{4}`: the subset-only reading accepts it
  because the unrelated set `{0,2,4}` is `I_s`-feasible, while the data itself
  satisfies clause 1 (coverage) nowhere. So the subset-only reading is not a
  harmless generalisation: it admits read collections that are not even
  covering. The same run finds no ML failure at any exact-range-feasible data
  in that range, consistent with the §3 conclusion that corrected `I_s` leaves
  no room for an escape.

Audit answer for the final #88 theorem: **no, exact-range semantics should not
be part of it, and the reason is stronger than a convention.** Under the
corrected predicate the conclusion does not mention `R` at all
(`informationFeasibleLift_no_longTripleRepeat_any`): corrected `I_s` excludes
long triple repeats for *any* certificate set, so the theorem is the same
statement whether `R` is the realized range, a superset of it, or an arbitrary
set. For the merged predicate the question is moot for a second reason, already
recorded in `SameLength62Maximizer`: `hfeas` and `hR` are not used by the ML
endpoint at all. Exact-range semantics *should* be required of any statement
that is read as a claim about the realized data (e.g. "this realized read
collection is `I_s`-feasible"), and that is where the audit above applies.

## 8. Recommendation

1. Merge the corrected predicate as the source-faithful one, keeping the merged
   predicate available under a name that says what it is (endpoint-only,
   wraparound-permitting). Both are in `AssemblyP1/LiftAudit`-style modules, so
   this is additive.
2. Rescope `AssemblyP1/WraparoundTripleRepeat` and the
   `SameLength62Maximizer` header from "the residual regime is non-empty" to
   "the residual regime is non-empty for the endpoint-only predicate and empty
   for the source-faithful one", with the new theorems as the reason.
3. Then re-derive the #88 endpoint as
   `informationFeasibleLift_62_spelledML` and retire
   `EscapeForcesMidRangeRepeat` from the public theorem's hypotheses. That
   retirement is a *statement* change and should be recorded as such, not made
   silently: the crux is a statement about the merged model, and the crux
   searches recorded in `docs/issue88-wraparound-contrapositive.md` remain valid
   evidence for it.
4. Keep the crux itself open for the merged model (it is not proved, and the
   searches found no counterexample), since `docs/issue88-wraparound-contrapositive.md`
   remains the record for that model version.

## 9. Reproduction

```
lake build
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.LiftAudit.BridgesCopy_ne_BridgesCopyLift
#print axioms AssemblyP1.LiftAudit.informationFeasibleLift_no_longTripleRepeat
#print axioms AssemblyP1.LiftAudit.informationFeasibleLift_62_spelledML
#print axioms AssemblyP1.LiftAudit.wraparound_not_informationFeasible_lift
EOF
python3 scripts/issue88-bridging-lift-audit.py
python3 scripts/issue88-exact-range-search.py 5 2 2 2 5
```
