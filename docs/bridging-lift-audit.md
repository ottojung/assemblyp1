# Audit of the bridging predicate: the single-lift span condition, and what it decides

Status: **settled and merged.** `SourceFaithfulIs.BridgesCopy` *is* the
source-faithful predicate, the correction is kernel-checked
(`SourceFaithfulIs.bridgesCopy_length`,
`BridgingBridge.informationFeasible_no_long_triple_repeat`,
`OrientedSameLengthML.informationFeasible_exactLik_maximizer`,
`SameLength62Maximizer.informationFeasible_62_maximizer`,
`AssemblyP1.MLEscape.informationFeasible_62_spelledML`), and the whole
`#88` endpoint follows from it. No `sorry`, no `admit`, no new axioms; the audit
in `AssemblyP1.lean` reports only `propext`, `Classical.choice`, `Quot.sound`.

## 0. Verdict: the single-lift reading is the source-faithful one

The endpoint-only reading is not an alternative interpretation of the source; it
is a mis-transcription. The arguments, in the order they matter:

1. **The source clause is a span clause, not a set-membership clause.** Bresler
   et al. (2013) state that a substring occurrence is bridged when a read covers a
   base on both sides of it, and illustrate it by a read drawn *through* the
   occurrence (Fig. 5 and the paragraph before Theorem 1); Shomorony et al.
   (2016) restate it as a read that "extends at least one base before and at
   least one base after the repeat segment" (§3, Fig. 6). Both are statements
   about where the read *starts and ends* relative to the occurrence, i.e. about
   the read's contiguous span containing the occurrence.
   `docs/bridging-source-semantics.md` §"Bridging a copy" transcribes exactly
   that as `r < t` and `t + ℓ < r + L`, and the paper's own model section uses
   `ℓ ≤ L - 2` repeatedly. The endpoint-only reading therefore contradicts the
   repository's documented model; it is the predicate that was out of step with
   the source, not the other way round.
2. **The extra disjunct is only reachable in a degenerate long-read regime.** For
   a read to reach `t - 1` and `t + ℓ` without containing the copy, it must
   travel the complement arc, which needs `L ≥ G - ℓ + 1`. The two readings
   therefore *coincide* whenever `G - ℓ > L`, which covers every regime the
   sequencing model is about (`ℓ ≪ L ≪ G`); they differ only in a mode in which a
   read spanning essentially the whole genome is counted as bridging a repeat it
   never touches.
3. **The literal set-membership reading would falsify the source's own sufficient
   condition.** A read of length `G - ℓ + 1` or more covers both flank bases
   without covering the copy. Under the endpoint-only reading such a data set is
   `I_s`-feasible, yet no read spans any of its repeats, so the
   Not-So-Greedy / MultiBridging conclusions the sources draw from bridging do
   not follow from the data. A reading under which the sources' own theorems fail
   is not a faithful reading of their definition.
4. **The copy coordinate is not itself a free choice.** A copy of length
   `ℓ < S.len` is the arc `[t, t + ℓ) (mod G)`, so its start `t : Fin S.len` and
   its two flanking bases `t - 1`, `t + ℓ` are single, well-defined coordinates;
   the maximality conditions of `IsRepeat` / `IsTripleRepeat` use the same
   convention. What is *not* determined by the circle alone is the **relative
   lift of the read** with respect to the copy: the read arc `[r, r + L)` can be
   paired with the copy arc starting at `t` or at `t + S.len`. The source's span
   semantics fixes that pairing (the read must start before the copy and end
   after it in one lift), and that is precisely what `BridgesCopy` now states.
   The free choice of *origin* is not what the normalization is for: a read or
   copy crossing the origin is already handled correctly by the `% len` phrasing,
   in both readings.
5. **`L ≤ G` does not legitimize the complement-arc disjunct.** It only bounds the
   number of turns, which is what let the old `bridgingLength` reduce to two
   cases; it does not remove the complement-arc case, which still exists whenever
   `G - ℓ ≤ L`. It is a *hypothesis of the arithmetic*, not a source convention
   licensing the disjunct.
6. **Direction of the error is the safe one.** The endpoint-only predicate is
   *weaker* than the source's, so endpoint-only `I_s`-feasibility is a weaker
   hypothesis, never a spurious one. Every counterexample proved under it stays
   valid — and each of the seven `I_s` witnesses is separately re-certified under
   the canonical predicate (§4). The correction cannot invalidate a negative
   result; it only makes positive ones harder, and here it makes the hypothesis
   faithful.

`SourceFaithfulIs.bridgesCopy_lifted_iff` is the checked form of points 1 and 4:
it proves the definition *is* the source's interval condition on a suitable
integer lift, so the modelling normalization is verified rather than assumed.

## 1. What the canonical predicate is

```lean
def BridgesCopy (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (t : Fin S.len) : Prop :=
  ∃ r ∈ R, ∃ d : Fin L, d.val + e + 1 < L ∧ (r.val + d.val + 1) % S.len = t.val
```

One realized read `r`, one offset `d`, the copy's start at offset `d + 1` of that
read, and the copy's successor still inside the read. `d : Fin L` rather than a
bare `ℕ` is what keeps `InformationFeasible` decidable, so the concrete `by
decide` proofs of the counterexample and witness modules are unaffected.

Its sharp consequence is

```lean
theorem bridgesCopy_length (hb : BridgesCopy S L R e t) : e + 2 ≤ L
```

which the endpoint-only condition could not give. From it,
`BridgingBridge.informationFeasible_no_long_triple_repeat : 2 ≤ L → R ∈ I_s →
¬ HasLongTripleRepeat` — the external "Fact D" of
`docs/oriented-same-length-ml-88.md` §3, which this repository could not prove
before.

## 2. One canonical predicate, not a duplicate Lift API

An earlier revision of this packet kept the two readings side by side
(`LiftAudit.BridgesCopyLift` for the source-faithful one,
`SourceFaithfulIs.BridgesCopy` for the endpoint-only one) on the grounds that
renaming would be a large cosmetic diff. **That duplication is not in the merged
surface**, and the reason is not cosmetic:

* the hazard was that `SourceFaithfulIs.BridgesCopy` sat in a module whose *name*
  claims source fidelity while implementing the weaker reading, so a reader
  meeting either name could not tell which one the theorems consumed;
* the fix that survives is the opposite of a rename: the source-faithful
  definition *takes over the canonical name*, so `BridgesCopy` and
  `InformationFeasible` now mean the source's `I_s` everywhere, with no second
  API to disambiguate;
* the one theorem that was genuinely *about* the endpoint-only reading,
  `BridgingBridge.bridgingLength` (whose second disjunct, `S.len - e ≤ L`, is
  vacuous under the canonical predicate), is kept with its old shape under an
  explicit header saying its second disjunct is unreachable, and
  `SourceFaithfulIs.bridgesCopy_length` is given as the one-line reason. That is
  the only historical lemma that needed a shape change, and it is documented
  rather than silently retained.

No symbol is named `…EndpointOnly` or `…Lift`, and nothing in the public surface
can be mistaken for the endpoint-only reading.

## 3. Consequence for the "wraparound regime"

`docs/issue88-wraparound-contrapositive.md` is retracted. `HasWraparoundTripleRepeat`,
the `longTriple_band` split, `EscapeForcesMidRangeRepeat`,
`informationFeasible_escape_gives_wraparound` and
`informationFeasible_62_spelledML_of_escape_crux` are **deleted**, not
deprecated, and no theorem in the repository mentions them. `AssemblyP1.MLEscape`
keeps `HasMidRangeTripleRepeat` and `informationFeasible_no_midRangeTriple` as a
*description* of what clause 2 rules out; the mid-range band is a strict subset of
the excluded range, and `informationFeasible_no_escape` is a theorem.

`AssemblyP1.WraparoundTripleRepeat` is retained in the *opposite* direction: its
former witness `AAAAB` (`G = 5`, `L = 3`, all five starts) is now kernel-checked as
**not** `I_s`-feasible — one `decide` on `InformationFeasible` itself
(`aaaab_not_information_feasible`) — which pins the artifact down. Its long triple
repeat is still recorded, because that is exactly what clause 2 now forbids.

## 4. The seven `I_s` witnesses, re-run under the canonical predicate

Seven mature witnesses discharge **full** `InformationFeasible` by a single
`decide` on the whole predicate — coverage, every triple repeat all-bridged,
every interleaved pair of repeats bridged, quantified over every admissible
repeat length and every selection of starts. They were all re-run (i.e. their
modules force-rebuilt and their `decide` proofs re-kernel-checked) after the
migration, and each is listed in the `AssemblyP1.lean` axiom audit:

| module | theorem | genome / `L` / starts |
| --- | --- | --- |
| `ExactVariantECounterexample` | `truth_information_feasible` | `L = 2`, no repeat at all, clauses 2–3 vacuous |
| `FiniteSamplingCounterexample` | `truth_information_feasible` | `AABBC`, `L = 3` |
| `FixedLengthBinomialCounterexample` | `truth_information_feasible` | `L = 3` |
| `FixedLengthExactCounterexample` | `truth_information_feasible` | `L = 3` |
| `SameLengthExactMLCounterexample` | `truth_information_feasible` | `L = 2`, starts `{1, 3}` |
| `SameLengthSection62Counterexample` | `truth_information_feasible` | `L = 3`, starts `{0, 1, 3, 5}` |
| `Section62BridgingCounterexample` | `truth_information_feasible` | `L = 3`, starts `{0, 1, 4}` |

The direction of the re-check is safe by §0.6: the canonical predicate is
*stronger*, so `I_s` is a *smaller* set, and a witness feasible under the
endpoint-only reading is automatically feasible under the canonical one. The
re-run is nevertheless done as a re-check rather than argued, because
`decide` failures would be silent otherwise.

## 5. The endpoint, and the start set its hypothesis is stated at

The exported endpoint is

```lean
AssemblyP1.MLEscape.informationFeasible_62_spelledML
```

hypotheses: `0 < G`, `2 ≤ L`, `L ≤ G`, a realization `ρ` of `n` reads on the
truth `S`, **full source-faithful `InformationFeasible` at
`realizedStarts ρ`**, the §6.2 read-type data, and a genuine §6.2 certificate for
the truth. Conclusion: `Is62SpelledMLMax`, i.e. the truth is a genuine §6.2
candidate *and* every same-length genuine §6.2 candidate has exact same-length
Medvedev–Brudno likelihood at most the truth's. There is **no** `hno`, **no**
escape, **no** culprit premise, and **no** auxiliary start set.

`realizedStarts ρ` is the range of the realization and is the canonical such set
(`OrientedSameLengthML.realizedStarts`, re-exported by
`AssemblyP1.MLEscape.realizedStarts`). This is the point of a separate audit that
found the previous endpoint took an arbitrary `R : Finset (Fin G)` with the
**one-sided** hypothesis `hR : ∀ i, ρ i ∈ R`, and did not even use `hR`. That is a
real weakening, not redundancy: `R` may carry start positions at which no read was
drawn, every clause of `I_s` is a "some `r ∈ R` does …" or a coverage condition,
and an added start *manufactures a bridging read the sample does not contain*.
The fixed surface is:

| theorem | start set of the `I_s` hypothesis | status |
| --- | --- | --- |
| `SameLength62Maximizer.informationFeasible_62_maximizer` | `realizedStarts ρ` | **the endpoint** |
| `OrientedSameLengthML.informationFeasible_exactLik_maximizer` | `realizedStarts ρ` | same, at the objective level |
| `…_of_exact_R` / `…_of_exact_subset` | `R`, with `hanti` so that `R = realizedStarts ρ` | faithful, through a pinned `R` |
| `…_of_superset_starts` | arbitrary `R ⊇ range ρ` | **strictly weaker**, named accordingly |

The transfer that makes the pinning explicit is
`OrientedSameLengthML.informationFeasible_of_exact_subset`: `hsub` together with
`hanti : ∀ r ∈ R, ∃ i, ρ i = r` says exactly `R = realizedStarts ρ`, so the two
`I_s` hypotheses become the same proposition. The missing `hanti` was the seam.

## 6. Only the repeat-length bound is `R`-independent

Care is needed here, and an earlier draft got it wrong. What is true:

* `bridgesCopy_length : BridgesCopy → e + 2 ≤ L` never mentions `R`, and
  therefore `I_s` excludes long triple repeats — `ℓ ≥ L - 1` — **for every `R`
  whatsoever**. For *that bound* the exact-range-versus-superset question is
  moot, and the `#88` endpoint does not otherwise depend on `R`.
* It is **not** a claim that feasibility ignores `R`. Clause 1, coverage, does
  mention `R`, and clauses 2 and 3 are existential in `R`; so the exact-range and
  subset-only readings of `I_s` are genuinely different predicates. §7 measures
  exactly how different.
* Note the asymmetry: the canonical predicate is *stronger*, so exact-range
  feasibility is a *stronger* hypothesis than subset-only feasibility. The two
  readings are therefore not interchangeable for the hypothesis side, which is
  why the endpoint is stated at the range of `ρ`.

## 7. Exact-range versus subset-only: the counts

`scripts/issue88-exact-range-search.py` transcribes the Lean definitions
literally and decides `I_s` per subset; `scripts/issue88-exact-range-fast.py`
decides the same predicate as a hitting-set condition over precomputed option
sets. Both are run at binary `G = 5`, all `2 ≤ L ≤ 5`, `nmax = 3`, i.e. 7040
realizations.

| quantity | endpoint-only | canonical |
| --- | --- | --- |
| realizations enumerated | 7040 | 7040 |
| exact-range `I_s`-feasible | 2790 | 1380 |
| subset-only `I_s`-feasible (some `R ⊇ range ρ`) | 4720 | 4660 |
| subset-only feasible but **not** exact-range feasible | 1930 | 3280 |
| ML failures (a same-support candidate strictly beats the truth) at exact-range-feasible data | 0 | 0 |
| of those, without a mid-range maximal triple repeat | 0 | 0 |

**Harness defect found and fixed by this audit.** The fast harness built each
copy's *option set* as `{r : BridgesCopy L (all starts) e t}`, i.e. it asked
whether the copy is bridged by the whole start set rather than by the single read
`r`. That predicate is true as soon as *any* read bridges, so every option set
came out equal to the full set of starts and clauses 2 and 3 of `I_s` were
silently void; the harness therefore disagreed with the literal transcription.
It also used `any` for the all-bridged triple-repeat clause, where `I_s` says
`all`. Both are fixed: option sets are `{r : BridgesCopy L [r] e t}` and each
requirement carries the quantifier its clause uses (`all` for a triple repeat,
`any` for an interleaved pair). The two harnesses are now verified to produce
*identical* feasible sets, by `--cross-check`, which compares them set by set for
every truth and every start subset, for **both** bridging readings. The
`2790 / 4720 / 1930` row above is what the audit reported after fixing the
harness; the `3850 / 5390 / 1540` figures in the earliest draft of this note came
from the defect and are void. The headline gap is *larger* than first stated, not
smaller.

The extreme case is a data set consisting of a **single** realized read, e.g.
`S = 00000`, `L = 2`, realized range `{4}`: the subset-only reading accepts it
because an unrelated larger set is `I_s`-feasible, while the data itself is not.
So exact-range semantics *is* required of any statement read as a claim about the
realized data, which is what §5 does.

Audit answer for the endpoint: **exact-range semantics is part of the final
theorem, and it is a statement about the actual sample.** The reason is stronger
than a convention: a bridging read in `I_s` contributes to the observation the
likelihood consumes, so if `R` may contain starts that were never sampled, the
`I_s` hypothesis is not a statement about the data at all. That is why the
endpoint is stated at `realizedStarts ρ`.

## 8. What the searches now show

`scripts/issue88-wraparound-search.py` was corrected to the canonical predicate
(`--endpoint-only` reproduces the historical figures). It asks, for every genome
and read length in range, whether a same-support same-length candidate ever
strictly exceeds the truth's spectrum on a support read type ("escape"), and
whether such an escape can occur at an `I_s`-feasible instance.

| alphabet | `G ≤` | `I_s`-satisfiable `(S, L)`, canonical | endpoint-only | escapes | escapes at an `I_s`-feasible `(S, L)` |
| --- | --- | --- | --- | --- | --- |
| binary | 7 | 830 | 908 | 258 | 0 |
| binary | 9 | (census 7) | — | 1584 | 0 |
| 3-letter | 7 | 13896 | — | 1764 | 0 |
| 4-letter | 6 | 21656 | — | 972 | 0 |

The `I_s` census drops under the canonical predicate, as it must (§0.6). No
escape occurs at an `I_s`-feasible instance in any range, and the correctness of
the canonical `I_s` is not in question: it is non-vacuous (830 satisfiable pairs
already at binary `G ≤ 7`) and it excludes every long triple repeat, as
`informationFeasible_no_long_triple_repeat` says.

This is evidence about the *finite* ranges searched, not a completeness proof; the
proved statement is the kernel-checked one, and it does not depend on these runs.

## 9. Scope check on the downstream claims

* `informationFeasible_no_long_triple_repeat` is exactly note §3 Fact D ("a
  length-`L` read bridges a copy of length `ℓ` only if `ℓ ≤ L - 2`; hence
  `R ∈ I_s` forbids triple repeats of length `≥ L - 1`"), and it is proved, not
  quoted. It is a statement about the *hypothesis* side only; no likelihood claim
  is smuggled in.
* `informationFeasible_62_spelledML` is **not** a resolution of the open problem
  as published. Its hypotheses include a realization `ρ`, the §6.2 read-type data,
  and a genuine §6.2 candidate certificate for the truth; its conclusion ranges
  over the literal same-length §6.2 class. What the correction buys is the removal
  of the *repeat-side* residual premise `hno` (and hence of
  `EscapeForcesMidRangeRepeat`) from that endpoint. It is not a passage to
  unrestricted candidate length, to all circular words, or to uniqueness up to
  rotation, and `docs/open-problem.md`'s statement of the published problem is not
  thereby settled.

## 10. Reproduction

```
lake build
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_lifted_iff
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_length
#print axioms AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat
#print axioms AssemblyP1.SameLength62Maximizer.informationFeasible_62_maximizer
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML
EOF
python3 scripts/issue88-exact-range-search.py 5 2 3 2 5
python3 scripts/issue88-exact-range-fast.py  5 2 3 2 5 --bridge endpoint
python3 scripts/issue88-exact-range-fast.py  5 2 3 2 5 --cross-check
python3 scripts/issue88-wraparound-search.py  9 2 7
```

The `#print axioms` lines must each report only `propext`, `Classical.choice`,
`Quot.sound`. The `search` and `fast` commands must print identical feasibility
counts (endpoint-only: 2790 / 4720 / 1930; canonical: 1380 / 4660 / 3280), and
`--cross-check` must print `AGREE`; if the fast harness ever diverges from the
literal transcription, it has regressed.
