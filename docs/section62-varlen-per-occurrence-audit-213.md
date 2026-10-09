# Audit of the variable-length, per-occurrence, bidirected §6.2 witness `AAATT → AAAATT` (issue #213)

_Status: independent adversarial audit + kernel-checked certificate additions,
2026-10-09. Every claim below is labelled **source fact**, **source-supported
inference**, **mathematical argument**, **verified computation**, **kernel-checked**,
**bounded evidence**, or **open**._

_Purpose._ The parent issue is #217. This leaf owns one cell of the matrix the
parent must justify: *bidirected* (reverse-complement) reading of
Medvedev–Brudno (2009) §6.2, candidates **not** constrained in length, the §6.1
literal product of binomial marginals with external `N`, and the **per-occurrence**
admissibility rule (the strictly stronger `d ≥ x` reading of the §6.2 vertex lower
bound). It audits the merged witness rather than re-finding it, and it records
exactly which neighbouring cells the witness does **not** reach.

_Reproduction:_

```sh
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py            # 55 checks
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py --census   # bounded census
lake build AssemblyP1.Section62VarlenPerOccurrence                        # new certificate
```

The Python script shares no code with `scripts/verify_se62_bridging_flow_counterexample.py`,
`scripts/verify_se62_mb09_bidirected_graph.py`, `scripts/verify_samelength_se62_counterexample.py`
or any Lean module; it is a second, independent implementation of the whole
certificate. The Lean module re-uses the merged instance and graph layer of
`AssemblyP1.Section62BridgingCounterexample` and adds the four audit-specific
statements; every theorem in it depends only on `propext`, `Classical.choice`
and `Quot.sound`, and the module kernel-replays through `leanchecker`.

---

## 0. Verdict at a glance

The merged witness **survives** the audit, and the audit hardens it:

1. **The witness is correct as stated.** Under the molecule-class reading of
   MB09 §6.1–§6.2 forced by §6.2 itself (vertices are the read *molecules*, `d_i`
   is the flow through vertex `i`), with `S = AAATT`, `D = AAAATT`, `L = 3`,
   `o_min = 2`, realized starts `(0,1,4)`, `n = 3`, external `N = 5`, the literal
   §6.1 product of binomial marginals satisfies `L(D)/L(S) = 9/8 > 1`. [mathematical
   argument + verified computation + kernel-checked]

2. **The per-occurrence strengthening does not rescue the truth.** The truth's
   throughput vector satisfies the *stronger* rule `d_S(w) ≥ x(w)` (with slack),
   and so does the competitor's. So this cell is refuted without appealing to the
   source's weaker per-vertex rule. [verified computation + kernel-checked]

3. **New: the witness lifts to the whole flow universe, and further.** The
   competitor's throughput vector is the **unique maximizer** of the literal §6.1
   objective over the *entire* §6.1 domain `0 ≤ d_i ≤ N`, not merely over the
   candidate class that was searched. No §6.2 flow of any kind can beat it, so
   the refutation cannot be an artifact of a restricted candidate class.
   [kernel-checked]

4. **Boundary: the same-length cells do not follow from this witness.**
   `∑_i d_D(i) = 6 ≠ 5 = N = ∑_i d_S(i)`, so the competitor is outside the
   length-constrained domain `∑ d_i = N` that the same-length cell imposes; and
   inside that slice the truth's vector is *already* a maximizer. A same-length
   refutation needs a different pair. [verified computation + kernel-checked]

5. **The oriented/single-strand reading inverts this witness**, and the strict
   reading of “the `4^k` §6.1 count” excludes both molecules. That fork is
   resolved in favour of molecule classes *given* §6.2
   (`docs/source-notes/mb09-se61-index-orientation-resolution.md`); the witness
   is stated for that reading only. [verified computation, source-supported inference]

---

## 1. The instance, re-derived from scratch

The audit script rebuilds the sequencing model from MB09 §3.1: a read is a DNA
molecule (an unordered reverse-complement strand pair), so a word and its
reverse complement are one molecule class. The witness alphabet is `{A, T}` with
the involution `A ↔ T` (a sub-alphabet of DNA, not a different alphabet). [source fact]

```text
alphabet          {A, T}, reverse-complement involution A <-> T
truth             S = AAATT          (G = 5)
read length       L = 3, o_min = L - 1 = 2
realized starts   (0, 1, 4)          (n = 3 reads)
external size     N = |S| = 5
observed          x = { AAA:1, AAT:1, TAA:1 }        (read-molecule classes)
truth spectrum    d_S = { AAA:1, AAT:2, TAA:2 }      (|S| = 5)
competitor        D = AAAATT         (|D| = 6)
competitor spec   d_D = { AAA:2, AAT:2, TAA:2 }      (|D| = 6)
```

Re-derived quantities: the four `{A,T}` length-`3` molecule classes are
`AAA, AAT, ATA, TAA` (`2³/2`, no odd-length strand being self-complementary); the
witness uses three of them. Over the full DNA alphabet there are `32` classes
and all other `29` have `x = d = 0`, so their §6.1 factors are `1`. [verified computation]

**Correction of the merged prose, re-confirmed.** The historical `d_S =
{AAA:2, AAT:2, TAA:1}` table entry is wrong; the start-`3` window of `AAATT` is
`TTA`, class `TAA`, so `d_S = {AAA:1, AAT:2, TAA:2}`. The merged note and
`docs/section62-mb09-bidirected-graph-audit.md` §4 already record this; the audit
confirms it independently. [verified computation]

---

## 2. `I_s`, decided again by explicit enumeration

The audit implements the source predicate from scratch (Bresler et al.'s maximal
repeat/two-sided maximality plus Shomorony et al. Eq. (1): coverage, every
maximal triple repeat all-bridged, every interleaved pair of maximal repeats
bridged, with the single-read strict-straddle bridging condition `r < t'` and
`t' + e < r + L` on a suitable integer lift), and decides it for
`(S, starts = (0,1,4))` over all `1 ≤ e < 5` and all selected starts. [verified computation]

- coverage holds;
- the only maximal triple repeat is the length-`1` `A` at starts `0,1,2`, and all
  three copies are bridged by single reads (copy `0` by the read at `4`, copy `1`
  by the read at `0`, copy `2` by the read at `1`);
- there is **no** interleaved pair of maximal repeats, so the third clause is
  vacuous.

This agrees with the kernel-checked `SourceFaithfulIs.InformationFeasible`
discharge in `AssemblyP1.Section62BridgingCounterexample` (the shared, authoritative
predicate, at full strength). [kernel-checked + verified computation]

---

## 3. The actual MB09 §6.2 graph and the two circuits

The audit builds the bidirected read-overlap graph on the three observed read
molecules independently: for every ordered pair of molecules, every strand pair
(the class representative and its reverse complement) and every proper overlap
length in `[o_min, L)`, with the MB09 §3.3 incidence at each endpoint. It
reproduces the **10 edges** of `docs/section62-mb09-bidirected-graph-audit.md`
§2, including the two twice-positive/twice-negative self-loops. [verified computation]

- **Transitive edge reduction.** Under the literal “spelled by two shorter
  overlaps” reading (allowing an *arbitrary* middle strand and arbitrary shorter
  lengths, not only the maximal ones) **zero** of the 10 edges are reducible;
  under the alternative longer-proper-overlap reading, zero as well. So the
  reduction is vacuous on the whole graph, and in particular on every edge the
  witnesses use. [verified computation]
- **Both walks are genuine bidirected circuits.** Every step of the cyclic
  window walk of `S` and of `D` is a real graph edge of length `L−1 = 2`, and at
  every interior vertex the arriving and departing incidences are opposite
  (MB09 §3.2). [verified computation]
- **The induced flows are §6.2-admissible.** Vertex throughputs are the molecule
  spectra (Observation 7), every read vertex has throughput `≥ 1` (the §6.2
  vertex lower bound), every edge carries flow `≥ 0` (edge lower bounds `0`, all
  upper bounds `∞`), the signed-incidence balance is `0` at every read vertex,
  and no supersource/supersink edge is used. [verified computation + kernel-checked]
- **Conjugation closure.** The edge set is closed under reverse-complement
  conjugation, a consistency check on the four-cases construction. [verified computation]

Conclusion: **a spelled bidirected circuit is an admissible §6.2 flow**, so both
`S` and `D` are §6.2 candidates on the actual transitively reduced read-overlap
graph. [mathematical argument + verified computation]

---

## 4. The two admissibility readings, kept apart

These are the two readings the issue asks to distinguish.

| reading | statement (for a spelled candidate) | source status |
|---|---|---|
| **per-vertex** (source) | `supp(spec_L(D)) = supp(x)` and every observed read molecule occurs at least once — the §6.2 vertex lower bound `1` read through Observation 7 | **source fact** (MB09 §6.2, Observation 7) |
| **per-occurrence** (strengthening) | additionally `d_D(w) ≥ x(w)` for every observed type `w` | **source-supported inference**: strictly stronger, *not* the §6.2 definition |

For this witness **both** hold on **both** sides:

```text
per-vertex      : truth yes, competitor yes
per-occurrence  : truth yes, competitor yes
                (d_S = (1,2,2) ≥ x = (1,1,1), strict in AAT and TAA)
```

So the variable-length refutation does **not** depend on which rule is used: the
stronger per-occurrence rule omits neither the truth nor the competitor. This is
the audit's main positive finding for the parent matrix — it upgrades the merged
note's “the certificate is a stronger sufficient condition that happens to hold”
to “the stronger condition holds, and the refutation stands under either". [verified computation + kernel-checked]

The mechanism is the source's own, and it is where the per-occurrence rule bites
*because* of reverse complementarity: `ATT ~ AAT` and `TTA ~ TAA`, so the truth
contains `2` copies of the `AAT` class and `2` of the `TAA` class while only one
read of each was sampled; the slack is what makes `d_S ≥ x` true with `n = 3 < N = 5`.

---

## 5. The §6.1 domain and the objective

- **Domain.** `0 ≤ d_i ≤ N = 5` is checked for both spectra over all `32` DNA
  molecule classes (max multiplicity is `2` on each side), and `n = 3 ≤ N = 5`.
  [verified computation + kernel-checked]
- **Objective.** The literal §6.1 product is evaluated over the *whole* class
  space with the zero-count factors retained. Every unobserved class has
  `d = 0` in both candidates, so each contributes the factor `1`; the ratio is
  carried entirely by the `AAA` coordinate (`1 → 2`), giving exactly
  `9/8 = 18/16 > 1`. [verified computation + kernel-checked]

---

## 6. New: the placement of the witness inside the objective domain

The strongest audit result, and the reason the witness cannot be dismissed as a
restricted-search artifact. Over the whole domain, the objective is separable, so
the audit enumerates the entire box `[0,N]^{#observed}` (and checks the
unobserved classes separately):

```text
maximum of the §6.1 objective over the domain : attained by exactly one vector
the maximizer is d_D = { AAA:2, AAT:2, TAA:2 }
the truth's own slice value                  : strictly below it
the same-length slice (sum d = N = 5)        : the truth's (1,2,2) attains it
```

Why: for a class with `x_w = 1, n = 3`, the marginal `3 (d/5)(1−d/5)²` is
maximized on the domain `0 ≤ d ≤ 5` uniquely at `d = 2`; for an unobserved class
the marginal `(1−d/5)³` is maximized uniquely at `d = 0`. Hence `d_D` is the
**unique** maximizer of the objective over the entire §6.1 domain. [verified computation,
kernel-checked for the comparison and the coordinate bounds]

Two consequences for the parent matrix:

- **The lift to the flow universe is free and maximal.** `FlowThroughput d`
  quantifies over *all* feasible §6.2 flows on the observed-molecule graph
  (not only spelled circuits), and both `d_S` and `d_D` are members. Since `d_D`
  is the global optimum, no flow — spelled or not, terminal-using or not — can be
  more likely. [kernel-checked]
- **The length-constrained domain is the only thing that saves the truth.** Add
  `∑ d_i = N` (the same-length cell) and `d_D` leaves the domain. [verified computation
  + kernel-checked]

---

## 7. New: the certificate in Lean

`AssemblyP1/Section62VarlenPerOccurrence.lean` imports the merged witness module
and adds, kernel-checked:

| theorem | content |
|---|---|
| `dS_domain`, `dD_domain` | both spectra satisfy `0 ≤ d_i ≤ N = 5` |
| `dS_flow_throughput`, `dD_flow_throughput` | both throughput vectors are realized by a feasible §6.2 flow (`FlowThroughput`, quantified over all flows) |
| `truth_rule_agreement` | per-vertex **and** per-occurrence admissibility of both molecules, plus the truth's slack |
| `lik_le_likD_of_domain` | `d_D` maximizes the §6.1 objective over the **entire** domain |
| `lik_lt_likD_of_ne` | it is the **unique** maximizer |
| `competitor_is_unique_optimizer` | the previous three composed with `FlowThroughput dD` and `dD ≠ dS` |
| `truth_not_maximizer_in_flow_universe` | `∃ d, FlowThroughput d ∧ Domain d ∧ lik obs dS < lik obs d` |
| `not_all_feasible_throughputs_le_truth` | the negated universal form of the refuted claim |
| `sum_dS`, `sum_dD` | `∑ d_S = 5`, `∑ d_D = 6` |
| `competitor_outside_length_constrained_domain` | `∑ d_D ≠ ∑ d_S`, i.e. the fixed-length boundary |

The module contains no `sorry`, `axiom`, `admit` or `native_decide`; each listed
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited with
`#print axioms` and `lake env leanchecker`), and the shared hypothesis side is
the authoritative `SourceFaithfulIs.InformationFeasible` predicate inherited from
the merged module.

---

## 8. What this witness does **not** reach

Recorded so the parent does not over-claim from it. [mathematical argument + verified computation]

1. **Same-length candidates (`|D| = N`).** Excluded: `|D| = 6 ≠ 5 = N = |S|`, and
   `∑ d_D = 6 ≠ 5 = ∑ d_S`. Within the sum-constrained slice the truth's vector
   is itself a maximizer, so this instance gives no same-length refutation.
2. **Fixed-length + per-occurrence.** Still **open** in scope. The audit census
   found **zero** same-length per-occurrence beats over its whole scope (§9),
   agreeing with the sibling note `docs/section62-same-length-bidirected-counterexample.md`
   (§9). Bounded evidence, not a proof.
3. **Fixed-length + per-vertex (the source rule).** Refuted, but by a different
   pair: `S = AAATAT → D = AAAAAT` (`G = 6`, ratio `5` binomial, `3` exact) of
   `docs/section62-same-length-bidirected-counterexample.md`. It does **not**
   follow from the `AAATT` witness, and it fails under the per-occurrence rule.
4. **Strict oriented `4^k` indexing.** The witness inverts: under oriented
   indexing the truth's spectrum is `{AAA:1, AAT:1, ATT:1, TTA:1, TAA:1}` and the
   observed reads are `{AAA:1, AAT:1, TAA:1}`, so neither molecule is a candidate
   at all. The molecule-class reading is the operative one *given* §6.2.
5. **A different objective.** Under the exact candidate-intrinsic multinomial the
   pair is a strict improvement as well (`125/108 > 1`), so the witness is not a
   tie there — but that cell is already refuted by same-length witnesses, so this
   adds nothing.
6. **Which MB09 object the 2016 sentence denotes. Unchanged source ambiguity**;
   this audit says nothing about it.

---

## 9. Bounded census (evidence, not proof)

Scope: truths are the circular `{A,T}`-strings of length `G` up to rotation; a
realization is a multiplicity vector over its `G` starts (`0..maxmul`); the truth
must be per-occurrence feasible (support equality and `d_S ≥ x`) and satisfy
`I_s`; a competitor is any circular string of length up to `G+2` with the same
support, `d ≥ x` and `d ≤ N`. Rows below are `(truth, realization)` counts and
`(instance, competitor)` beat counts. [bounded evidence]

| `G` | `L` | `maxmul` | per-occurrence-feasible `I_s` realizations | variable-length beats | smallest ratio | same-length beats |
|---|---|---|---|---|---|---|
| 5 | 3 | 1 | 58 | 56 | `9/8` (`AAATT→AAAATT`) | **0** |
| 5 | 3 | 2 | 532 | 126 | `9/8` | **0** |
| 5 | 3 | 3 | 2150 | 224 | `9/8` | **0** |
| 6 | 3 | 1 | 132 | 160 | `128/125` | **0** |
| 6 | 3 | 2 | 2216 | 536 | `128/125` | **0** |
| 6 | 3 | 3 | 12453 | 1162 | `128/125` | **0** |

Reading of the table: the variable-length per-occurrence mechanism is **not**
isolated — beats exist at every scope point, with `9/8` the smallest ratio in the
`G = 5` scope (the audited witness) and `128/125` in the `G = 6` scope (the
`AAATAT → AAAATAT` family the merged note records). The zero same-length rows are
consistent with the sibling note's bounded zero. Both are bounded evidence about
the stated scope; neither is a proof of absence.

---

## 10. Epistemic status

| claim | status |
|---|---|
| MB09 §6.1 fixed-`N` product of binomial marginals with `0 ≤ d_i ≤ N`; §6.2 bidirected flow on the transitively reduced read-overlap graph, vertex lower bound `1`, edge bounds `0`/`∞`, supersource/supersink, `d_i` = vertex flow | **source fact** (MB09 §3.1–§3.4, §5.2, §6.1–§6.2) |
| reads are DNA molecules, one vertex per molecule class | **source fact** |
| per-vertex rule is the source rule; per-vertex ⇒ support equality for a spelled molecule | **source-supported inference** + mathematical argument (Observation 7) |
| `d ≥ x` (per-occurrence) is strictly stronger than the source rule | **mathematical argument** |
| MB09 §6.2 imposes no constraint on the *length* of the candidate; `N` enters only the objective and the domain bound | **source fact** (no such sentence exists in §6.2); the length-constrained reading is an added assumption, recorded here |
| instance data `x`, `d_S`, `d_D`, graph (10 edges), two circuits, reduction vacuous, admissibility under both rules, domain, ratio `9/8` | **verified computation** (independent script) |
| `I_s` holds for `(S, (0,1,4))`, full enumeration, no interleaved pair | **verified computation** + **kernel-checked** (`SourceFaithfulIs.InformationFeasible`) |
| `d_D` is the unique maximizer over the whole §6.1 domain | **kernel-checked** (`lik_le_likD_of_domain`, `lik_lt_likD_of_ne`) |
| both throughput vectors are in the §6.2 flow universe | **kernel-checked** (`FlowThroughput`) |
| the refuted cell (bidirected, variable-length, per-occurrence) is settled negatively | **kernel-checked** (`truth_not_maximizer_in_flow_universe`) |
| same-length per-occurrence cell: no beats in the stated scope | **bounded evidence** |
| single-strand/oriented reading of this witness | **open** (inverted, not refuted) |
| which MB09 object the 2016 sentence denotes | **open**, unchanged |

---

## 11. Reproduce

```sh
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py            # 55 checks
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py --census   # bounded census
lake build AssemblyP1.Section62VarlenPerOccurrence
```

The Python script prints every intermediate graph edge, bridge witness and
objective factor, and exits non-zero on any failure; all arithmetic is exact
(`fractions.Fraction`). The census is run only under `--census` and takes about
20 s on a laptop.

---

## 12. Recorded blockers observed while auditing (not caused by this issue)

On this worktree at `cc0aa8a` (= `origin/main`), a **full** `lake build` fails in
four modules that this issue does not touch, both with and without my change
(verified by building the pristine root as well):

- `AssemblyP1/BBTTripleBridge.lean` — genuine source-level type errors
  (e.g. line 81 declares `cyc_congr {x y : ℕ} (h : x % G = y)` where the
  `Fin.ext` application needs `x % G = y % G`), introduced when the file was
  split for bounded elaboration in `42ebed7`;
- `AssemblyP1/Issue94OrbitSearch.lean`, `AssemblyP1/Issue94Transposition.lean`,
  `AssemblyP1.Issue94WitnessPair.lean` — the compiler is killed (exit `137`)
  while elaborating them on this host (they succeed in CI with 6G swap).

Consequence: the root aggregator `AssemblyP1.lean` cannot currently be built, so
the module registration and the `#print axioms` block added for this issue are
verified by an equivalent standalone probe (`import AssemblyP1.Section62VarlenPerOccurrence`
+ the same nine `#print axioms` lines, each reporting only
`[propext, Classical.choice, Quot.sound]`) and by `lake env leanchecker`, not by a
root build. These four failures are pre-existing and are reported here so that
the parent does not attribute them to this leaf.

---

## 13. Relation to the repository's existing results

| existing claim | location | status after this audit |
|---|---|---|
| variable-length per-occurrence case resolved negatively, ratio `9/8` | `docs/bridging-se62-flow-ml-counterexample.md` §3, §7 | **confirmed** independently; strengthened by the flow-universe and global-optimality certificates |
| the sequence-level support/`d ≥ x` certificate is not §6.2 feasibility | same, §2 | unchanged and correct |
| same-length cell refuted under the per-vertex rule (`AAATAT→AAAAAT`) | `docs/section62-same-length-bidirected-counterexample.md` | unchanged; **not** implied by this witness |
| same-length per-occurrence cell open, bounded zero | same, §3, §7 | corroborated by this audit's census (§9) |
| `4^k` vs molecule-class index fork resolved to molecule classes given §6.2 | `docs/source-notes/mb09-se61-index-orientation-resolution.md` | unchanged; the audited witness is stated for that reading only |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.1–§3.4, §5.2, §6.1–§6.2,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1) and §5.
