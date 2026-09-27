# The bridging source-semantics fix: the #88 wraparound regime was an artifact

**Status: settled, kernel-checked.** This note records a source-fidelity bug in
`AssemblyP1.SourceFaithfulIs.BridgesCopy`, the fix, its two consequences, the
blast radius, and the resulting theorem surface. It supersedes the "Fact D is
false" reading in `docs/same-length-exact-ml-88-refutation.md` §5 and
`docs/oriented-same-length-ml-88.md`, and it retracts
`docs/issue88-wraparound-contrapositive.md` §1–§8.

## 1. The bug

`docs/bridging-source-semantics.md` records the source's condition: a read
interval `[r, r+L)` bridges a lifted occurrence interval `[t', t'+e)` exactly when

```
r < t'   and   t' + e < r + L
```

on a suitable integer lift — Bresler et al. 2013, Fig. 5 and the paragraph
immediately before Theorem 1; Shomorony et al. 2016 §3/Fig. 6. One read must
*strictly straddle* the occurrence; "contains the repeated substring" is
explicitly not enough.

`BridgesCopy` was instead transcribed endpoint-wise:

```lean
∃ r ∈ R, ReadCovers S L r ((t + S.len - 1) % S.len) ∧
          ReadCovers S L r ((t + e) % S.len)
```

This is strictly weaker, and the gap is exactly the complementary arc. A read of
length `L` whose covered positions straddle the origin covers `(t-1) % G` and
`(t+e) % G` whenever the *complement* of the occurrence has length `≤ L - 1` —
without the read containing any part of the occurrence. For a long occurrence
this makes the endpoint-wise condition satisfiable by a read that lies entirely
in the complement.

Concretely, in the kernel-checked instance `AAAAB` (`G = 5`, `L = 3`, all five
starts), the length-`2` triple repeat at starts `0, 1, 2` satisfied the
endpoint-wise condition and so passed clause 2 of `I_s`, and no length-`3` read
contains that copy at all.

## 2. The fix

`BridgesCopy` is now the source's straddling condition, minimally transcribed:

```lean
def BridgesCopy (S : Genome α) (L : ℕ) (R : Finset (Fin S.len)) (e : ℕ)
    (t : Fin S.len) : Prop :=
  ∃ r ∈ R, ∃ d : Fin L, d.val + e + 1 < L ∧ (r.val + d.val + 1) % S.len = t.val
```

The occurrence's start sits at offset `d + 1` of the realized read at `r`. Since
reads are substrings of the genome, the predecessor of the occurrence is
automatically at offset `d` and the successor at offset `d + e + 1` **of the same
read interval**, and `d + e + 1 < L` says the successor is still inside that
read. No separate modular endpoint clauses are needed, and `d : Fin L` (rather
than a bare `ℕ`) keeps `InformationFeasible` decidable, so the concrete `by
decide` proofs of the counterexample modules are unaffected.

`SourceFaithfulIs.bridgesCopy_lifted_iff` proves this is *exactly* the source's
interval formulation on a lift:

```lean
BridgesCopy S L R e t  ↔
  ∃ r ∈ R, ∃ t', t' % S.len = t.val % S.len ∧ r.val < t' ∧ t' + e < r.val + L
```

## 3. Two consequences, both kernel-checked

| theorem | content |
| --- | --- |
| `SourceFaithfulIs.bridgesCopy_length` | `BridgesCopy S L R e t → e + 2 ≤ L` |
| `BridgingBridge.informationFeasible_no_long_triple_repeat` | `2 ≤ L → R ∈ I_s → ¬ RepeatAdapter.HasLongTripleRepeat` |

The first is arithmetic: the bridging read sits at offset `d ≥ 0` and must reach
offset `d + e + 1 < L`.

The second is the "Fact D" that `docs/oriented-same-length-ml-88.md` §3 had
recorded as *external* and that this repository could not prove: a long maximal
triple repeat is a `Genome.IsTripleRepeat`, so clause 2 of `I_s` makes all three
of its copies bridged, so `e + 2 ≤ L`, so `e ≤ L - 2`, contradicting `e ≥ L - 1`.
No bound relating `L` to the genome length is needed, and there is no
"wraparound" case, because a bridged copy is two bases shorter than the read that
straddles it whatever the genome length is.

## 4. Blast radius

**Unaffected (all still compile, all their `by decide` `I_s` proofs included).**
Every module that constructs an `I_s` instance: `ExactVariantECounterexample`
(`L = 2`), `SameLengthExactMLCounterexample` (`L = 2`), `FiniteSamplingCounterexample`,
`FixedLengthExactCounterexample`, `FixedLengthBinomialCounterexample`,
`SameLengthSection62Counterexample`, `Section62BridgingCounterexample` (all
`L = 3`). None of them carries a long triple repeat, which is exactly what the
corrected `I_s` requires, so clause 2 is satisfiable at each of them. This was
verified independently, outside Lean, with the same definitions
(`scripts/issue88-source-semantics-check.py`): the corrected `I_s` is non-vacuous
at every `(G, L)` examined, and no feasible instance carries a long triple
repeat. E.g. for `G = 5` over a binary alphabet, with all five starts:

| `L` | `I_s`-feasible genomes | of those, with a long triple repeat |
| --- | --- | --- |
| 2 | 2 | 0 |
| 3 | 22 | 0 |
| 4 | 32 | 0 |
| 5 | 32 | 0 |

**Affected, and rewritten.**

* `BridgingBridge.bridgingLength` keeps its two-disjunct statement so that
  references do not break, but the `S.len - e ≤ L` disjunct is now unreachable;
  the proof is one line. `SharpNoLongTripleRepeat` and
  `informationFeasible_sharp_no_long_triple_repeat` are **deleted**: the
  nondegeneracy hypothesis they encoded was a fact about the wrong predicate.
* `WraparoundTripleRepeat` no longer kernel-checks a counterexample. It now
  kernel-checks the refutation of its own former instance
  (`aaaab_not_information_feasible`, a single `decide`), together with the long
  triple repeat it does carry (`aaaab_has_long_triple_repeat`) and the fact that
  all its windows are observed. That pair is the artifact, pinned down.
* `MLEscape` loses the culprit statement `EscapeForcesMidRangeRepeat`, the band
  `HasWraparoundTripleRepeat`, `longTriple_band`, the two `informationFeasible_*_
  wraparound` theorems, and the `G - L` escape route. In exchange,
  `informationFeasible_no_escape` (`I_s → ¬ HasSpectralEscape`) and
  `informationFeasible_62_spelledML` are **theorems**.
* `OrientedSameLengthML.informationFeasible_exactLik_maximizer` and
  `SameLength62Maximizer.informationFeasible_62_maximizer` drop their
  `¬ HasLongTripleRepeat` premises. The audit finding recorded in
  `docs/same-length-62-maximizer.md` §5 — that `_hfeas` was unused — is
  correspondingly obsolete: `_hfeas` is now what supplies the nondegeneracy.

## 5. The exact-range tightening (also this commit)

Independently of the bridging fix, `I_s` is now stated at the range of the
realization. `AssemblyP1.MLEscape.realizedStarts ρ` is that range, and

* `mem_realizedStarts : r ∈ realizedStarts ρ ↔ ∃ i, ρ i = r`,
* `informationFeasible_of_exact_subset : R ⊇ range ρ ∧ (∀ r ∈ R, ∃ i, ρ i = r) →
  InformationFeasible … (realizedStarts ρ)`

so the previous surface's `hR : ∀ i, ρ i ∈ R` was only half of what issue #88's
statement needs; the missing half is the absence of *spurious* starts, which
matters because every clause of `InformationFeasible` is a "some `r ∈ R` does …"
or a coverage condition, so inflating `R` can only make `I_s` easier to satisfy.
`informationFeasible_62_spelledML` and
`informationFeasible_62_spelledML_of_no_long_triple_exact` are stated with no
`R` at all; `informationFeasible_62_spelledML_of_subset_starts` keeps the weaker
subset form for comparison and is explicitly labelled unfaithful.

## 6. Resulting theorem surface for #88

`AssemblyP1.MLEscape.informationFeasible_62_spelledML`:

> Let `S` be a circular word of length `G`, `ρ` a realization of `n` reads on `S`,
> `2 ≤ L ≤ G`, and suppose the realized reads satisfy full source-faithful
> `InformationFeasible` at length `L`. Suppose the truth is a genuine §6.2
> candidate for the observed read set. Then every **same-length genuine §6.2
> candidate** `D` for the same observed read set has exact same-length
> Medvedev–Brudno likelihood at most the truth's.

The hypothesis list is exactly the source's: `2 ≤ L ≤ G`, full `I_s` at the
realized starts, and the §6.2 data. There is no long-triple-repeat premise, no
primitivity or period premise, and no escape, culprit or spectrum-rigidity
hypothesis. Axioms: `propext`, `Classical.choice`, `Quot.sound` only
(`AssemblyP1.lean` audit, 44 constants).

## 7. Honest limits

* The statement is the **maximizer** reading of "the maximum-likelihood sequence
  is the true sequence": it says the truth is *a* maximizer, not that it is the
  unique one up to cyclic shift. The repository keeps those apart throughout and
  only the former is claimed here.
* The candidate class is the literal §6.2 class, i.e. same-length
  `Fin G → α` words carrying a `SpelledFeasible62` certificate for the observed
  read set. The **unrestricted** same-length claim is refuted, kernel-checked, by
  `AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`,
  and is untouched by this fix.
* Whether the published 2016 sentence was intended with any support-based
  candidate restriction at all remains an open interpretation question
  (`docs/source-notes/mb-formulation-referent-reconciliation.md`); this note
  records the §6.2 reading, it does not resolve the question.
* `bridgesCopy_lifted_iff` is the only place where the "suitable integer lift"
  modelling normalization of `docs/bridging-source-semantics.md` is carried
  explicitly in Lean. It is a theorem, not an axiom, and its two directions are
  proved, so the normalization is checkable rather than assumed.

## 8. Issue #88 update (text prepared; not posted)

The `gh` CLI is not available in the environment this fix was made in, so the
issue update is recorded here for a later run to post verbatim. It supersedes
the "not settled" status of #88.

> **#88 — settled (maximizer reading), by a source-semantics fix.**
>
> The statement `AssemblyP1.MLEscape.informationFeasible_62_spelledML` is
> kernel-checked: full source-faithful `I_s` at the exact range of the realized
> reads, plus the §6.2 truth certificate, and **no** long-triple-repeat, escape
> or culprit premise.
>
> The blocker was not combinatorial. `SourceFaithfulIs.BridgesCopy` had been
> transcribed endpoint-wise rather than as the source's strict straddling of the
> occurrence, so a read could "bridge" a long repeat by spanning the
> complementary circular arc. That produced (a) a spurious "wraparound mode" in
> `BridgingBridge.bridgingLength`, (b) a kernel-checked counterexample
> (`AAAAB`, `G = 5`, `L = 3`) to "Fact D", and (c) a residual culprit statement
> `EscapeForcesMidRangeRepeat` carried as an unproved hypothesis of the target
> theorem. With the source's condition, `bridgesCopy_length : e + 2 ≤ L` and
> `informationFeasible_no_long_triple_repeat : 2 ≤ L → I_s →
> ¬ HasLongTripleRepeat`; the counterexample is refuted
> (`WraparoundTripleRepeat.aaaab_not_information_feasible`) and the culprit
> statement is deleted as void.
>
> The theorem is the **maximizer** reading ("the truth is *a* maximizer"), in
> the literal §6.2 same-length candidate class, with the exact Medvedev–Brudno
> objective. Uniqueness up to cyclic shift is not claimed. The unrestricted
> same-length claim remains refuted, kernel-checked, by
> `SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`.
> Whether the 2016 sentence intends any support-based candidate restriction is
> still an open interpretation question.
>
> Details: `docs/bridging-source-semantics-fix.md`,
> `docs/bridging-source-semantics.md` ("Correction"),
> `docs/issue88-wraparound-contrapositive.md` §9.

## 9. Reproduction

```
lake build
lake env lean - <<'EOF'
import AssemblyP1
#print axioms AssemblyP1.MLEscape.informationFeasible_62_spelledML
#print axioms AssemblyP1.BridgingBridge.informationFeasible_no_long_triple_repeat
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_length
#print axioms AssemblyP1.SourceFaithfulIs.bridgesCopy_lifted_iff
#print axioms AssemblyP1.WraparoundTripleRepeat.aaaab_not_information_feasible
EOF
python3 scripts/issue88-source-semantics-check.py 5 2
python3 scripts/issue88-source-semantics-check.py 4 3
```

All five `#print axioms` must report only `propext`, `Classical.choice`,
`Quot.sound`.
