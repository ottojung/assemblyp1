# Independent audit: the integrated `AAATT` truth/read instance against the exact Shomorony 2016 bridging condition

_Status: independent primary-source audit + exact finite computation, 2026-09-20.
Written adversarially against the repository's own reconstruction, with a fresh
implementation that imports no repository module. Records a **confirmation**
plus two minor, non-falsifying mismatches. It does not settle the Shomorony et
al. open question, which ML layer the 2016 sentence denotes, or the tie
convention._

_Reproduction:_

```sh
python3 scripts/audit_aaatt_bridging_source.py
# kernel check of the integrated instance:
lake build AssemblyP1.Section62LowerBoundOneCounterexample
```

## 0. Verdict

The integrated `AAATT` truth/read instance **satisfies the exact
information-feasible bridging condition `I_s`** under the source definitions and
conventions, including the repeat/triple-repeat maximality clauses, the strict
Figure-5 bridging predicate, circular indexing, and read placement. The
reverse-complement convention does not disturb the bridging certificate. No
falsifying mismatch was found.

Two minor mismatches are recorded, both harmless to the instance and to
`I_s`:

1. a factual prose slip in
   [`section62-bidirected-lowerbound1-determination.md`](../section62-bidirected-lowerbound1-determination.md)
   §4.1, which calls `11` at `{3,4}` a length-`2` repeat (it is not);
2. the Lean `SourceCertificate` is a sound **instance-tailored** certificate,
   not a definitional transcription of the general `I_s` predicate: it
   hard-codes the unique triple repeat rather than quantifying over all of
   them.

## 1. Primary sources and the exact condition

The bridging condition used is the one Shomorony et al. (2016) Eq. (1)
attributes to Bresler, Bresler & Tse (2013):

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  "Information-optimal genome assembly via sparse read-overlap graphs,"
  *Bioinformatics* 32(17), 2016, i494–i502, Eq. (1) and §3, Fig. 6.
- Guy Bresler, Ma'ayan Bresler, David Tse, "Optimal assembly for high
  throughput shotgun sequencing," *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
  [PMC3706340](https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/), retrieved
  2026-09-20. [source fact, text re-read this run]

Verbatim from the retrieved primary text [source fact]:

> "A repeat of length `l` is a subsequence appearing twice, at some positions
> `t1, t2` (so `s_t1^l = s_t2^l`) that is maximal (i.e. `s(t1 - 1) ≠ s(t2 - 1)`
> and `s(t1 + l) ≠ s(t2 + l)`). Similarly, a triple repeat of length `l` is a
> subsequence appearing three times, at positions `t1, t2, t3`, such that
> `s_t1^l = s_t2^l = s_t3^l`, and such that neither of
> `s(t1 - 1) = s(t2 - 1) = s(t3 - 1)` nor
> `s(t1 + l) = s(t2 + l) = s(t3 + l)` holds. … A pair of repeats refers to two
> repeats, each having two copies. A pair of repeats, one at positions `t1, t3`
> with `t1 < t3` and the second at positions `t2, t4` with `t2 < t4`, is
> interleaved if `t1 < t2 < t3 < t4` or `t2 < t1 < t4 < t3`."

> Figure 5: "A subsequence `s_t^l` is bridged if and only if there exists at
> least one read which covers at least one base on both sides of the
> subsequence, i.e. the read arrives in the preceding length `L-l-1` interval."

> "we will call a repeat or a triple repeat bridged if at least one copy of the
> repeat is bridged, and a pair of interleaved repeats bridged if at least one
> of the repeats is bridged."

> MultiBridging (Theorem 6): "(a) all interleaved repeats are bridged; (b) all
> triple repeats are all-bridged; (c) the sequence is covered by the reads."

Shomorony et al. reuse this as `I_s` on a circular sequence. [source fact +
delegation documented in `../bridging-source-semantics.md` §"Source
correspondence"]

**Linear vs circular bridging.** On a circular genome the source phrase
"covers at least one base on both sides" cannot by itself distinguish the two
arcs: a read can cover both flanks by wrapping the *other way around* without
containing the copy. The source's own clarification — "the read arrives in the
preceding length `L-ℓ-1` interval" — pins the intended read start to the
`L-ℓ-1` positions that place the read so that it **contains the copy and extends
at least one base on each side**. On an integer lift this is exactly

```text
r < t   and   t + ℓ < r + L .
```

This is the repository's accepted normalization `../bridging-source-semantics.md`
§"Bridging a copy", and it is the predicate audited here. [source fact +
modeling normalization]

## 2. Instance under audit

The integrated instance is the one kernel-checked in
[`AssemblyP1/Section62LowerBoundOneCounterexample.lean`](../../AssemblyP1/Section62LowerBoundOneCounterexample.lean)
and described in
[`section62-bidirected-lowerbound1-determination.md`](../section62-bidirected-lowerbound1-determination.md)
Witness 1. [repository fact]

```text
truth        S = AAATT   (circular, G = 5)        0:A 1:A 2:A 3:T 4:T
read length  L = 3
realized starts (0, 1, 4)                          n = 3
```

A second `AAATT` read instance appears in the repository with the *same* truth
but latent starts `(0, 0, 1, 4)` — the non-spellable arbitrary-§6.2-flow search
witness (`../section62-arbitrary-flow-witness-and-search.md`). Because bridging
depends only on the *set* of read placements, both were audited. [repository
fact]

## 3. Independent computation

`scripts/audit_aaatt_bridging_source.py` re-implements the source definitions
above from scratch (no repository import), on a circular word, with an integer
lift for bridging and origin-independent cyclic alternation for interleaving.
Result [verified computation]:

```text
S = AAATT, L = 3, starts (0,1,4):
  coverage                 True
  maximal repeat pairs     A@{0,2} (len 1), T@{3,4} (len 1), AA@{0,1} (len 2)
  maximal triple repeats   A@{0,1,2} (len 1)
  triple-bridge failures   []
  interleaved pairs        []
  interleave failures      []
  I_s                      True

S = AAATT, L = 3, starts (0,0,1,4): I_s True (same obligations)
```

Coverage is exact: read starts `0,1,4` cover positions
`{0,1,2} ∪ {1,2,3} ∪ {4,0,1} = {0,1,2,3,4}`.

The unique triple repeat is the length-`1` run `A@{0,1,2}`. Its maximality
condition holds: the preceding symbols are `s(4),s(0),s(1) = T,A,A` (not all
equal) and the following symbols are `s(1),s(2),s(3) = A,A,T` (not all equal).
Each copy is strictly bridged [verified computation]:

```text
copy t=0  bridged by read start 4   (lift: read [4,7) ⊃ copy [5,6))
copy t=1  bridged by read start 0   (read [0,3) = A A T ⊃ copy [1,2) with flanks 0,2)
copy t=2  bridged by read start 1   (read [1,4) = A A T ⊃ copy [2,3) with flanks 1,3)
```

The interleaving conjunct is vacuous: the only four-distinct-start candidate is
`A@{0,2}` with `T@{3,4}`, whose cyclic label order is `A,A,T,T` (adjacent, not
alternating); the other pairings share a start. So no maximal-repeat pair is
interleaved. Hence `I_s` holds, and it holds under both the strict predicate and
the weaker "cover both flanks" reading (the strict one is stronger here).

## 4. Reverse complements

Shomorony et al.'s theory is **single-stranded**: §2 is a circular sequence `s`
of length `G` with reads drawn as its length-`L` substrings, and §3 seeks `s` up
to cyclic shifts; reverse complements enter only as §4.1 experimental
preprocessing ("include each read and its reverse complement"). [source fact,
recorded in `reverse-complement-strand-convention.md` §3]

Bridging is a property of a read's **placement on the true genome**, so
relabelling read types by their reverse-complement molecule class does not
change the bridging certificate. The audit checks this explicitly: the reads at
starts `0,1,4` have windows `AAA, AAT, TAA` (self-classes unchanged under
`A↔T` reversal on these words), and adding reverse-complement reads can only
*add* bridging witnesses. [verified computation]

The instance does mix conventions across sources in one respect: the §6.1
likelihood side collapses read types to revcomp classes (a Medvedev–Brudno
convention), while the bridging side is Shomorony's single-strand one. That
cross-source panel is already recorded in
[`reverse-complement-strand-convention.md`](reverse-complement-strand-convention.md)
§5–6; it does **not** affect the bridging audit, which is single-strand and
placement-based. [modeling/source dependency, pre-existing]

## 5. Read positions and circularity

- **Read positions.** Bridging is evaluated from the realized latent starts
  `(0,1,4)` on the true genome, exactly as the source requires (bridging is a
  property of the realized sequencing, not of the observable read multiset).
  [source fact + repository agreement]
- **Circularity.** The circular substrate is handled by modular access for
  coverage/windows and by an integer lift for bridging. The copy at `t=0` is
  bridged by the origin-crossing read at start `4`; without the lift this copy
  would be wrongly counted as unbridged. The audit's lift agrees with the source
  interval reading. [mathematical normalization + verified computation]
- **Multiplicity.** For the integrated instance the realized starts are
  distinct, so a `Finset` of starts is faithful. The Lean field
  `readStarts : Finset (Fin 5)` therefore cannot represent repeated latent
  starts; this is immaterial for the integrated `(0,1,4)` instance but means the
  `(0,0,1,4)` variant is not the object the Lean file certifies.

## 6. Comparison with the repository formalization

The kernel-checked formalization is
`AssemblyP1/Section62LowerBoundOneCounterexample.lean`:

| source obligation | Lean declaration | audit outcome |
|---|---|---|
| coverage | `Covers` (line 168), `truth_covered` (171) | **matches** source |
| all triple repeats all-bridged | `TripleAllBridged` (179), `truth_triple_all_bridged` (186) | **sound for this instance**; see limitation (2) |
| interleaving bridged | `hasInterleavingB` (211) / `HasInterleaving` (225), `no_interleaving` (229) | **matches**; `decide`-complete over the finite index range |
| conjunction `I_s` | `SourceCertificate` (236), `truth_source_certificate` (238) | **sound instance certificate**; see (2) |

I rebuilt the module (`lake build AssemblyP1.Section62LowerBoundOneCounterexample`:
"Build completed successfully") and checked the axioms of
`se62_lower_bound_one_counterexample` and `truth_source_certificate`: both depend
only on `propext`, `Classical.choice`, `Quot.sound`; the file contains no
`sorry`, `axiom`, `admit`, or `native_decide` (grep-confirmed). [kernel check]

The Lean bridging clause itself is exactly the strict predicate for this
instance: for `L=3, ℓ=1` the only start that puts the read around the copy with
one base on each side is `r = t-1`, and `TripleAllBridged` requires exactly
`(r+1) % 5 = t`, i.e. `r = t-1`. The three witnesses `4,0,1` are the ones the
independent enumeration finds. [verified computation]

## 7. Mismatches recorded

**(1) Prose slip: `11@{3,4}` is not a length-`2` repeat.**
`section62-bidirected-lowerbound1-determination.md` §4.1 says "The length-`2`
repeats (`00` at `{0,1}`, `11` at `{3,4}`)". Independent enumeration finds the
maximal repeat pairs `A@{0,2}` (len `1`), `T@{3,4}` (len `1`), `AA@{0,1}`
(len `2`); there is no length-`2` repeat at `{3,4}` (`window(3,2)=TT`,
`window(4,2)=TA`). The claim is harmless: the corrected repeat set still yields
no interleaved pair, so the `I_s` conclusion is unchanged. The section has been
corrected in place. [verified computation; repository fact]

**(2) `SourceCertificate` is instance-tailored, not the general `I_s`
predicate.** `TripleAllBridged` asserts all-bridging for the single hard-coded
triple repeat `A@{0,1,2}` and does not quantify over triple repeats, so
`SourceCertificate` alone does not *definitionally* entail Shomorony's `I_s`;
its soundness for the instance rests on the (independently confirmed) fact that
this is the only maximal triple repeat. This is a scoping limitation of the
finite certificate, not an error in the instance or in the checked theorem. The
Python verifier does enumerate all triple repeats and agrees. A future
formalization aiming at the general implication should quantify over the repeat
predicate rather than hard-code the instance. [repository fact + verified
computation]

No other mismatch was found; in particular the maximality clauses, the strict
bridging predicate, circularity, read placement, and the vacuity of the
interleaving conjunct all match the primary source.

## 8. Epistemic summary

| claim | status |
|---|---|
| Bresler repeat / triple-repeat / interleaving / Figure-5 bridging prose as quoted | **source fact** (`PMC3706340`, retrieved 2026-09-20) |
| Shomorony Eq. (1) delegates `I_s` to those definitions | **source fact** (via `../bridging-source-semantics.md`) |
| Strict lift predicate `r < t ∧ t+ℓ < r+L` is the source-bridging normalization | **source fact + modeling normalization** |
| `AAATT`, `L=3`, starts `(0,1,4)` satisfies exact `I_s` | **verified computation** (`scripts/audit_aaatt_bridging_source.py`, exact) |
| `AAATT`, `L=3`, starts `(0,0,1,4)` also satisfies `I_s` | **verified computation** |
| Integrated Lean `SourceCertificate` is sound for the instance and kernel-checked on three standard axioms | **kernel check** (`lake build`, `#print axioms`) |
| `11@{3,4}` is a length-`2` repeat | **false / prose slip**, corrected, harmless |
| Lean certificate is definitionally the general `I_s` | **not established** (instance-tailored; sound here) |
| Reverse complements disturb the bridging certificate | **no** (placement-based, single-strand theory) |
| Which ML layer/tie/candidate-class conventions the 2016 sentence denotes | **open**, unchanged |

Primary sources: Bresler, Bresler & Tse 2013, *BMC Bioinformatics*
14(Suppl 5):S18, [PMC3706340](https://pmc.ncbi.nlm.nih.gov/articles/PMC3706340/);
Shomorony, Kim, Courtade & Tse 2016, *Bioinformatics* 32(17) i494–i502,
DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
