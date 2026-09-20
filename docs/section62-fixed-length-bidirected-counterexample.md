# Fixed-length likelihood-improving competitors under the Section 6.2 bidirected-flow constraints

_Status: source reading + mathematical argument + bounded exhaustive exact-rational
computation, 2026-09-20. Classified by epistemic class. Reproduces and extends
issue #36. Does not settle which §6.1/§6.2 object the Shomorony et al. sentence
intends._

_Reproduction: `python3 scripts/se62_fixed_length_bidirected_search.py`
(all assertions pass; deterministic; exact `fractions.Fraction` arithmetic;
about three minutes on the development host; `--quick` runs the smaller
scopes)._

---

## 0. Answer at a glance

1. **Question.** Can a *fixed-length* candidate genome `D` (`|D| = |S| = G`)
   that strictly improves the likelihood over the truth `S` also be admissible
   under the Medvedev–Brudno §6.2 bidirected-overlap-flow constraints, in an
   instance where the truth `S` is itself admissible and the bridging hypothesis
   `I_s` holds?

2. **Yes — under the source's "set of reads" / per-type lower bound together
   with the bidirected (reverse-complement) reading.** The minimal witness is

   ```
   L = 3,  G = 6
   truth       S = AAATAT        competitor D = AAAAAT
   starts (0,0,1,3,5), N = 5
   observed molecules x = { AAA:2, AAT:1, ATA:1, TAA:1 }
   ```

   `I_s` holds, both `S` and `D` are §6.2 sequence-level feasible (their
   window-spectrum supports both equal `supp(x)`), and `D` strictly improves
   both the exact fixed-length multinomial (`L(D)/L(S) = 3`) and the literal
   §6.1 separable binomial (`5`).

3. **The counterexample is not isolated.** Exhaustive search over the recorded
   scope finds **4608** fixed-length competitor instances at `G = 6`, `L = 3`
   (over 12 truths, one rotation/reverse-complement orbit) with exact-likelihood
   ratios from `3` to `81`; every one of the 4608 also strictly improves the
   §6.1 binomial. Outside `(G,L) = (6,3)` the scope contains no counterexample.

4. **The per-occurrence reading blocks it in scope.** If every sampled read
   occurrence is a distinct vertex with lower bound `1` (`d_D(w) ≥ x_w`), then
   in the same bounded scope there are **zero** counterexamples, and there are
   also zero under the single-strand (no reverse-complement) reading. The
   truth's failure in the witness is exactly `d_S(AAA) = 1 < x_AAA = 2`.

5. **Consequence.** The well-posed fixed-length statement “`I_s` ∧ `S ∈ F_flow`
   ⇒ `S` is ML over `F_flow`” is **refuted** under the per-type bidirected
   reading, and remains **open** under the per-occurrence reading. This is the
   reading ambiguity already flagged in
   `docs/section-6-2-feasible-set-membership.md` §6, now resolved in opposite
   directions for the two readings.

---

## 1. Model and the two lower-bound readings

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397.

Section 6.2 (source facts, quoted in `docs/section62-bidirected-flow-feasibility.md` §1):

- “The first step is to build a **bidirected** overlap graph **from the set of
  reads, which are DNA molecules**. The vertices of this graph are the reads.”
- “Each vertex has a **lower bound of 1** since it represents a read that must
  be present in the genome at least once.”
- “Since any flow can be decomposed into a collection of walks, our flow
  represents a (non-contiguous) assembly.”
- Observation 7: “The number of times `W` visits `r` is equal to the number of
  times `r` appears a submolecule of the molecule spelled by `W`.”

By Observation 7, a circular molecule `D` is spelled by a walk of read vertices
iff **(a)** every length-`L` submolecule of `D` is an observed read molecule and
**(b)** every observed read molecule occurs in `D`. In particular the *support*
of `D`'s length-`L` window spectrum must equal the observed read-molecule
support. (Derivation in `docs/section-6-2-feasible-set-membership.md` §2 and
`docs/section62-bidirected-flow-feasibility.md` §2; not re-derived here.)

Two readings of the lower bound “1” are possible, because the source says *set*
of reads but samples are usually multisets:

| reading | vertex | lower bound | feasible molecules `D` |
|---|---|---|---|
| **per-occurrence** | each sampled read occurrence | `d_D(w) ≥ x_w` | support equality **and** uses each occurrence |
| **per-type** | each distinct read molecule | `d_D(w) ≥ 1` | support equality only |

The phrase “**set** of reads” and “DNA molecules” (a molecule is an unordered
reverse-complement pair) support the **per-type bidirected** reading; the
per-occurrence reading is the common multiset reading. Both are analysed here
and both were flagged as unresolved in the repository.

**Candidates.** This note restricts to *fixed-length* candidates `|D| = G`,
the class relevant to the fixed-length likelihood question of issues #31/#32.
Under the per-occurrence lower bound a length-`G` molecule is feasible only if
`N ≤ G`; under the per-type lower bound `N` is unconstrained.

---

## 2. The counterexample

```
S = A A A T A T          (G = 6)
D = A A A A A T          (G = 6)
L = 3
starts (0, 0, 1, 3, 5)   (N = 5)
```

### 2.1 Realized reads and observed molecules

`A↔T` is the DNA reverse-complement involution (the witness uses only `A`,`T`).

| start | read | reverse complement | molecule class |
|---|---|---|---|
| 0 | `AAA` | `TTT` | `AAA` |
| 0 | `AAA` | `TTT` | `AAA` |
| 1 | `AAT` | `ATT` | `AAT` |
| 3 | `TAT` | `ATA` | `ATA` |
| 5 | `TAA` | `TTA` | `TAA` |

So `x = {AAA:2, AAT:1, ATA:1, TAA:1}` and `supp(x) = {AAA, AAT, ATA, TAA}`.

### 2.2 Both molecules are §6.2-feasible

Window spectra over molecule classes:

```
S = AAATAT :  AAA, AAT, ATA, TAT, ATA, TAA
              ->  d_S = {AAA:1, AAT:1, ATA:3, TAA:1}
D = AAAAAT :  AAA, AAA, AAA, AAT, ATA, TAA
              ->  d_D = {AAA:3, AAT:1, ATA:1, TAA:1}
```

Both spectra have support exactly `supp(x)`, so both molecules are spelled by
the cyclic window walk in the bidirected overlap graph (consecutive windows
overlap in `L−1 = 2` symbols, so the edges exist for any `o_min ≤ 2`; transitive
reduction preserves spelled molecules). The lower bound `1` per type is met by
both. Direct circuit verification is performed by
`walk_is_bidirected_circuit` in the reproduction script.

Note `d_S(ATA) = 3`: the truth contains `ATA` twice plus `TAT`, whose
reverse-complement *is* `ATA`. This reverse-complement collapse is what creates
the exploitable multiplicity.

### 2.3 `I_s` holds

- **Coverage.** The reads at starts `0,0,1,3,5` cover all six positions.
- **Triple repeat.** The only triple repeat is the `A`-run at positions
  `{0,1,2,4}`; each copy is bridged (`0` by the read at `5`, `1` by the read at
  `0`, `2` by the read at `1`, `4` by the read at `3`).
- **Interleaved repeats.** The maximal repeat pairs are the `A` copies, the
  `A`-run pairs, and `ATA@(2,4)`; no two have four cyclically alternating
  starts. So the interleaving conjunct is vacuous.

The search enforces these hypotheses mechanically and the script re-checks them;
`check_I_s(S, starts, …) = True`.

### 2.4 The competitor strictly wins

Both objectives compare equal-length molecules:

```
exact multinomial:  L(D)/L(S) = (3/1)^2 · (1/1)^1 · (1/3)^1 · (1/1)^1 = 3
§6.1 binomial, N0 = G = 6, n = 5:
                    (3/6)^2 (3/6)^3 / (1/6)^2 (5/6)^3
                  · (1/6)(5/6)^4 / (1/6)(5/6)^4
                  · (1/6)(5/6)^4 / (3/6)(3/6)^4
                  · (1/6)(5/6)^4 / (1/6)(5/6)^4        = 5
```

So `D` beats `S` under both the exact fixed-length objective and the literal
Medvedev–Brudno §6.1 separable binomial.

### 2.5 Reading dependence

The truth fails the **per-occurrence** lower bound: `d_S(AAA) = 1 < x_AAA = 2`.
Hence under the multiset (per-occurrence) reading the truth is not a §6.2
candidate at all, and the witness reduces to the same obstruction as the
read-tiled `AAABCBC → AAAAABC` witness. The refutation above is specific to the
per-type reading implied by the source's “set of reads”.

---

## 3. Bounded exhaustive search

`scripts/se62_fixed_length_bidirected_search.py` fixes `|D| = G` and, for every
`I_s`-satisfying realization in which the truth is §6.2-feasible, enumerates
every fixed-length candidate `D` with the same molecule-support, keeps those
that are §6.2-feasible, and tests both objectives. Scope and results:

| reading | lower bound | G | L | σ | instances | counterexamples |
|---|---|---|---|---|---|---|
| single-strand | per-occurrence | 4–7 | 3,4 | 2,3 | many | **0** |
| single-strand | per-type | 4–7 | 3,4 | 2,3 | many | **0** |
| bidirected | per-occurrence | 4–7 | 3,4 | 2,3 | many | **0** |
| bidirected | per-type | 4,5 | 3 | 2,3 | — | **0** |
| bidirected | per-type | **6** | **3** | 2,3 | 12 656 / 130 634 | **4608 / 4608** |
| bidirected | per-type | 7 | 3,4 | 2,3 | many | **0** |

Total 476 124 instances searched. The 4608 bidirected per-type witnesses cover
**12 truths** — the rotation/complement orbit of `AAATAT` — and 384 distinct
`(truth, starts)` realizations; the exact-likelihood ratio ranges over
`{3, 9, 27, 81}` and the binomial ratio over `{5, 25, 125, 625}`, always `> 1`.
Every witness was independently re-verified with the direct bidirected circuit
check for both the truth and the competitor.

The counterexample is confined to `(G,L) = (6,3)` in the recorded scope; `G = 8`
was not exhaustively searched. The zero counts are computational evidence
bounded by the stated scope, not a proof of absence.

---

## 4. Why the witness works

The mechanism is structural and independent of the particular labels:

1. Reverse complementarity makes the truth's window spectrum **non-simple**:
   a window and the reverse complement of another window can coincide, so a
   molecule can carry more occurrences of a type than the number of times it
   was observed. Here `TAT ~ ATA` gives `d_S(ATA) = 3`.
2. Under the per-type lower bound, feasibility is **support equality only**, so
   any molecule sharing the support is admissible regardless of how the
   multiplicities are distributed.
3. The observed data can over-represent a single type (`x_AAA = 2`, or up to `5`
   for the `N = 8` members). A candidate that shifts multiplicity onto that type
   (here `D = AAAAAT` with `d_D(AAA) = 3`) then improves any likelihood that is
   increasing in `d_D(w)^{x_w}`.

The single-strand reading removes step 1 (`TAT ≠ ATA`), and the per-occurrence
lower bound removes step 2; the counterexample is precisely the intersection of
the bidirected reading with the per-type lower bound.

---

## 5. Relation to existing repository results

| existing claim | location | status after this note |
|---|---|---|
| “No current counterexample has both truth and competitor in the sequence-level §6.2 feasible set” | `docs/section-6-2-feasible-set-membership.md` §0.4, §3 | True for per-occurrence; **false** for the per-type bidirected reading, where 4608 fixed-length witnesses exist |
| “The well-posed sequence-level question remains open” | `docs/section-6-2-feasible-set-membership.md` §5; `docs/section62-bidirected-flow-feasibility.md` §6 | **Refuted under the per-type bidirected reading**; open under per-occurrence |
| bounded search zero-counterexample over 85 572 instances | `docs/section62-bidirected-flow-feasibility.md` §5 | Consistent: that search used the per-occurrence lower bound and `N = G`; the per-type, variable-`N` regime is new |
| read-tiled `AAABCBC → AAAAABC` competitor is §6.2-feasible, truth not | `docs/read-tiled-counterexample.md`; `AssemblyP1/Section62FlowObstruction.lean` | Unchanged; the new witness additionally has a feasible truth under the per-type reading |

The per-type reading is not exotic: it is the literal reading of the source's
“set of reads” whose vertices are “DNA molecules” and whose per-vertex lower
bound is `1`.

---

## 6. Epistemic status

| claim | status |
|---|---|
| §6.2 object is a bidirected read-overlap flow; lower bound `1` per read vertex; output may be non-contiguous | **source fact** (PMC3154397 §6.2) |
| Observation-7 sequence-level criterion (support equality ∧ lower bound) | **mathematical argument** (cited derivation) |
| `S = AAATAT`, `D = AAAAAT` witness: `I_s`, both §6.2-feasible, exact ratio `3`, binomial ratio `5` | **verified computation** (exact rationals) + hand check in §2 |
| 4608 bidirected per-type counterexamples over 12 truths at `G=6,L=3`, ratios `3`–`81` | **verified computation**, bounded exhaustive |
| zero counterexamples in the other recorded scopes | **verified computation**, bounded exhaustive |
| “`I_s` ∧ truth §6.2-feasible ⇒ truth ML over fixed-length §6.2” is false per-type | **follows** from the verified witness |
| same statement remains open per-occurrence | **open** (bounded zero evidence only) |
| which reading the printed lower bound intends | **source ambiguity**, unchanged |
| which §6.1/§6.2 object the 2016 sentence intends | **source ambiguity**, unchanged |

---

## 7. Open questions

1. **Per-occurrence reading.** No counterexample was found for `G ≤ 7, L ≤ 4`.
   Is the per-occurrence statement true, or does a larger counterexample exist?
2. **Large-`G` boundary.** The bidirected per-type phenomenon is confined to
   `G = 6` in scope; `G = 8` was not exhaustively searched, and the structural
   mechanism of §4 does not predict it must stop at `G = 6`.
3. **`o_min`.** The witness uses `L−1` overlaps, so it is stable for every
   `o_min ≤ L−1`; smaller `o_min` only adds edges. `o_min > L−1` makes any
   assembly impossible, so the relevant parameter range is `o_min ≤ L−1`.
4. **Accepted-text provenance and tie semantics** remain as recorded in
   `docs/source-notes/ml-objective-candidate-class-resolution.md`.

---

## 8. Reproduce

```sh
python3 scripts/se62_fixed_length_bidirected_search.py          # full, ~3 min
python3 scripts/se62_fixed_length_bidirected_search.py --quick  # G,L <= 6,3
```

The script asserts the recorded counts for every scope, re-verifies every
counterexample with the direct bidirected circuit check, and re-checks `I_s`;
it exits non-zero on any regression. All arithmetic is exact
`fractions.Fraction`.

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397.
Cross-references: `docs/section-6-2-feasible-set-membership.md`,
`docs/section62-bidirected-flow-feasibility.md`,
`docs/read-tiled-counterexample.md`, `AssemblyP1/Section62FlowObstruction.lean`.
