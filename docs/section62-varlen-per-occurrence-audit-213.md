# Audit of the variable-length, per-occurrence, bidirected §6.2 witness `AAATT → AAAATT` (issue #213)

_Status: independent adversarial audit + kernel-checked certificate additions,
2026-10-09 (re-verified from a clean module artifact: the certificate module was
rebuilt after deleting its `.olean`/`.ilean`, the axiom probe was widened to all
35 theorems, and the script, census and blocker checks were re-run; see §11).
Every claim below is tagged **fact**,
**inference**, or **choice**, and additionally carries its verification class
(**source fact**, **kernel-checked**, **verified computation**, **bounded
evidence**, or **open**). A **fact** is something established from the source
text or by computation/proof; an **inference** is a consequence drawn by the
author from facts; a **choice** is a modelling decision that the source does not
determine, and that another defensible reading could replace._

_Purpose._ The parent issue is #217. This leaf owns one cell of the matrix the
parent must justify: *bidirected* (reverse-complement) reading of
Medvedev–Brudno (2009) §6.2, candidates **not** constrained in length, the §6.1
literal product of binomial marginals with external `N`, and the **per-occurrence**
admissibility rule (the strictly stronger `d ≥ x` reading of the §6.2 vertex lower
bound). It audits the merged witness rather than re-finding it, and it records
exactly which neighbouring cells the witness does **not** reach.

_Reproduction:_

```sh
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py            # 60 checks
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py --census   # bounded census
lake build AssemblyP1.Section62VarlenPerOccurrence                        # new certificate
```

The Python script shares no code with `scripts/verify_se62_bridging_flow_counterexample.py`,
`scripts/verify_se62_mb09_bidirected_graph.py`, `scripts/verify_samelength_se62_counterexample.py`
or any Lean module; it is a second, independent implementation of the whole
certificate. The Lean module re-uses the merged instance and graph layer of
`AssemblyP1.Section62BridgingCounterexample` and adds the audit-specific
statements; every theorem in it depends only on `propext`, `Classical.choice`
and `Quot.sound`, and the module kernel-replays through `leanchecker`.

The `--census` run is **not** part of the certificate: it is a bounded search
over a scope declared in §9, and its zero rows are evidence about that scope
only. The `#212` sibling issue has since produced a same-length per-occurrence
counterexample outside that scope; §8 item 2 and §9 record why the two are
compatible.

---

## 0. Verdict at a glance

The merged witness **survives** the audit, and the audit hardens it:

1. **The witness is correct as stated.** Under the molecule-class reading of
   MB09 §6.1–§6.2 forced by §6.2 itself (vertices are the read *molecules*, `d_i`
   is the flow through vertex `i`), with `S = AAATT`, `D = AAAATT`, `L = 3`,
   `o_min = 2`, realized starts `(0,1,4)`, `n = 3`, external `N = 5`, the literal
   §6.1 product of binomial marginals satisfies `L(D)/L(S) = 9/8 > 1`. [fact —
   mathematical argument + verified computation + kernel-checked]

2. **The per-occurrence strengthening does not rescue the truth.** The truth's
   throughput vector satisfies the *stronger* rule `d_S(w) ≥ x(w)` (with slack),
   and so does the competitor's. So this cell is refuted without appealing to the
   source's weaker per-vertex rule. [fact — verified computation + kernel-checked]

3. **The witness lifts to the whole flow universe, and further.** The
   competitor's throughput vector is the **unique maximizer** of the literal §6.1
   objective over the *entire* §6.1 domain `0 ≤ d_i ≤ N`, not merely over the
   candidate class that was searched. No §6.2 flow whose throughput vector lies
   inside that domain can beat it, so the refutation cannot be an artifact of a
   restricted candidate class. [fact — kernel-checked]

4. **New in this refresh: the lift also reaches the terminal-allowed flow
   universe.** Both throughput vectors are realized by flows satisfying the
   `Admissible` clauses with supersource/supersink usage left *free*
   (`dS_flow_throughput_general`, `dD_flow_throughput_general`), so the
   refutation does not depend on the zero-terminal-usage reading of §6.2's
   "prohibitively large costs" either. The remaining, and only, real limitation
   of the lift is the *reverse* direction, stated precisely in §6.1.
   [fact — kernel-checked]

5. **Boundary: the same-length cells do not follow from this witness.**
   `∑_i d_D(i) = 6 ≠ 5 = N = ∑_i d_S(i)`, so the competitor is outside the
   length-constrained domain `∑ d_i = N` that the same-length cell imposes; and
   inside that slice the truth's vector is *already* a maximizer. A same-length
   refutation needs a different pair. [fact — verified computation + kernel-checked]

6. **The oriented/single-strand reading inverts this witness**, and the strict
   reading of "the `4^k` §6.1 count" excludes both molecules. That fork is
   resolved in favour of molecule classes *given* §6.2
   (`docs/source-notes/mb09-se61-index-orientation-resolution.md`); the witness
   is stated for that reading only. [inference + verified computation,
   source-supported]

7. **The fixed-`N` vs actual-binomial ambiguity does not bite here.** With the
   binomial size taken to be the candidate's own length instead of the external
   `N`, the ratio becomes `1953125/1594323 > 1` (new check `(V)`), so this pair
   is a strict improvement under both readings. The ambiguity is nevertheless
   still open as a question about §6.1; see §4.3. [fact — verified computation]

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
and all other `29` have `x = d = 0`, so their §6.1 factors are `1`. [fact — verified computation]

Tags for this section: that a read is a reverse-complement molecule class is
**fact about the source** (MB09 §3.1, [source fact]); using the `{A,T}`
sub-alphabet, `L = 3`, `o_min = L − 1`, `N = |S|` and this particular realization
are **instance data / choices** carried over from the merged witness, not
source-determined; the spectra and counts above are **facts** re-derived by the
audit.

**Correction of the merged prose, re-confirmed.** The historical `d_S =
{AAA:2, AAT:2, TAA:1}` table entry is wrong; the start-`3` window of `AAATT` is
`TTA`, class `TAA`, so `d_S = {AAA:1, AAT:2, TAA:2}`. The merged note and
`docs/section62-mb09-bidirected-graph-audit.md` §4 already record this; the audit
confirms it independently. [fact — verified computation]

---

## 2. `I_s`, decided again by explicit enumeration

The audit implements the source predicate from scratch (Bresler et al.'s maximal
repeat/two-sided maximality plus Shomorony et al. Eq. (1): coverage, every
maximal triple repeat all-bridged, every interleaved pair of maximal repeats
bridged, with the single-read strict-straddle bridging condition `r < t'` and
`t' + e < r + L` on a suitable integer lift), and decides it for
`(S, starts = (0,1,4))` over all `1 ≤ e < 5` and all selected starts. [fact — verified computation]

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
§2, including the two twice-positive/twice-negative self-loops. [fact — verified computation]

- **Transitive edge reduction.** Under the literal “spelled by two shorter
  overlaps” reading (allowing an *arbitrary* middle strand and arbitrary shorter
  lengths, not only the maximal ones) **zero** of the 10 edges are reducible;
  under the alternative longer-proper-overlap reading, zero as well. So the
  reduction is vacuous on the whole graph, and in particular on every edge the
  witnesses use. [fact — verified computation]
- **Both walks are genuine bidirected circuits.** Every step of the cyclic
  window walk of `S` and of `D` is a real graph edge of length `L−1 = 2`, and at
  every interior vertex the arriving and departing incidences are opposite
  (MB09 §3.2). [fact — verified computation]
- **The induced flows are §6.2-admissible.** Vertex throughputs are the molecule
  spectra (Observation 7), every read vertex has throughput `≥ 1` (the §6.2
  vertex lower bound), every edge carries flow `≥ 0` (edge lower bounds `0`, all
  upper bounds `∞`), the signed-incidence balance is `0` at every read vertex,
  and no supersource/supersink edge is used. [fact — verified computation + kernel-checked]
- **Conjugation closure.** The edge set is closed under reverse-complement
  conjugation, a consistency check on the four-cases construction. [fact — verified computation]

Conclusion: **a spelled bidirected circuit is an admissible §6.2 flow**, so both
`S` and `D` are §6.2 candidates on the actual transitively reduced read-overlap
graph. [inference from facts — mathematical argument + verified computation]

---

## 4. The assumption surface: what is source, what is the project's own
strengthening, and what is a free modelling choice

This is the section the issue asks for, and it is kept deliberately sharper than
the merged note. Three different things are in play and they must not be
conflated.

### 4.1 The two admissibility readings

| reading | statement (for a spelled candidate) | tag | source status |
|---|---|---|---|
| **per-vertex** `d_w = 1`-style rule (historical) | `supp(spec_L(D)) = supp(x)` and every observed read molecule occurs at least once — the §6.2 vertex lower bound `1` read through Observation 7 | **choice**, source-fact-backed | **source fact**: MB09 §6.2, Observation 7. This is the rule the source states. |
| **per-occurrence** `d ≥ x` (project level) | additionally `d_D(w) ≥ x(w)` for every observed type `w` | **choice**, project-level | **project-level strengthening, NOT source fact.** No sentence of MB09 §6.2 requires a candidate to contain an observed molecule more often than it was sampled. §6.2 gives each read *vertex* a lower bound of `1`; §4.1 says each `k`-molecule is represented only once, so a duplicated observation enters as a single vertex and the source rule stays per-vertex. |

The per-occurrence rule is **strictly stronger** than the per-vertex rule
(`d ≥ x` with `x ≥ 1` on the observed support forces support equality plus more).
That it is a strengthening is a **fact** (mathematical argument); that the
project is entitled to impose it is a **choice**, and the parent #217 must carry
it as an assumption of this cell, not as part of the source claim. This is the
same labelling that the sibling issue #212 uses for its cell, and the two cells
share this definition (compared in §14).

For this witness **both** hold on **both** sides:

```text
per-vertex      : truth yes, competitor yes
per-occurrence  : truth yes, competitor yes
                 (d_S = (1,2,2) ≥ x = (1,1,1), strict in AAT and TAA)
```

So the variable-length refutation does **not** depend on which rule is used: the
stronger per-occurrence rule omits neither the truth nor the competitor. This is
the audit's main positive finding for the parent matrix — it upgrades the merged
note's "the certificate is a stronger sufficient condition that happens to hold"
to "the stronger condition holds, and the refutation stands under either".
[fact — verified computation + kernel-checked]

The mechanism is the source's own, and it is where the per-occurrence rule bites
*because* of reverse complementarity: `ATT ~ AAT` and `TTA ~ TAA`, so the truth
contains `2` copies of the `AAT` class and `2` of the `TAA` class while only one
read of each was sampled; the slack is what makes `d_S ≥ x` true with `n = 3 < N = 5`.
[inference, checked in computation]

### 4.2 Residual source ambiguity (honest statement, unresolved)

1. **Which rule does MB09 §6.1–§6.2 intend?** The text visible to this audit
   states only the per-vertex lower bound. Whether the project's `d ≥ x`
   per-occurrence reading is *intended* by the source, or is only a defensible
   strengthening the project chose in order to make the statement non-trivial,
   is **not determined by the source text** and this audit does **not** resolve
   it. Consequence for the parent matrix, stated carefully because the direction
   of implication matters:
   - A refutation proved under the *stronger* per-occurrence hypothesis does
     **not** by itself refute the source's per-vertex statement, because the
     stronger statement has more hypotheses and is therefore easier to refute.
   - For *this* instance it nevertheless refutes both, because **both molecules
     satisfy the source per-vertex rule as well** (§4.1 table). That is the
     reason this cell is safe to report as a negative result under either
     reading, and it is a property of this witness, not of the strengthening in
     general.
   - The assumption surface of the cell therefore differs by reading: under the
     per-vertex reading the instance is a §6.2 candidate by the source's own
     rule; under the per-occurrence reading it is a candidate only under the
     project's strengthening.
   [**open** — recorded, not resolved here; the per-instance stability is a
   fact, verified computation + kernel-checked]
2. **Fixed `N` or actual binomial size?** MB09 §6.1's literal formula takes the
   binomial size to be the *known* genome size `N`, an external parameter; a
   competing reading takes the binomial size to be the candidate's own length.
   Which one the source intends is a genuine residual ambiguity (see
   `docs/formalization-plan.md`). For *this* pair the ambiguity is immaterial:
   `N = |S| = 5`, so the truth's likelihood is identical under both, and the
   competitor's ratio is `9/8` under fixed `N` and `1953125/1594323` under the
   candidate-intrinsic size — both `> 1`. [**open** in general; **fact** that it
    does not affect this cell — verified computation, check `(V)`.]

---

## 5. The §6.1 domain and the objective

- **Domain.** `0 ≤ d_i ≤ N = 5` is checked for both spectra over all `32` DNA
  molecule classes (max multiplicity is `2` on each side), and `n = 3 ≤ N = 5`.
  [fact — verified computation + kernel-checked]
- **Objective.** The literal §6.1 product is evaluated over the *whole* class
  space with the zero-count factors retained. Every unobserved class has
  `d = 0` in both candidates, so each contributes the factor `1`; the ratio is
  carried entirely by the `AAA` coordinate (`1 → 2`), giving exactly
  `9/8 = 18/16 > 1`. [fact — verified computation + kernel-checked]
- **Read types.** The exact read molecules of the realization are the three
  classes `AAA`, `AAT`, `TAA` with multiplicities `x = (1,1,1)`; the graph is
  built on exactly those three vertices, and no other class occurs in either
  candidate. This is the domain the certificate is about: the observed-molecule
  graph of §3 and the box `0 ≤ d_i ≤ 5` over all `32` DNA classes of §5.
  [fact — verified computation]

---

## 6. The placement of the witness inside the objective domain

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
**unique** maximizer of the objective over the entire §6.1 domain. [fact — verified computation,
kernel-checked for the comparison and the coordinate bounds]

Consequences for the parent matrix:

- **The lift to the flow universe is free and maximal.** `FlowThroughput d`
  quantifies over feasible §6.2 flows on the observed-molecule graph with zero
  supersource/supersink usage (not only spelled circuits), and both `d_S` and
  `d_D` are members. `FlowThroughputGeneral d` quantifies over admissible flows
  with terminal usage left *free*, and both are members of that too
  (`dS_flow_throughput_general`, `dD_flow_throughput_general`). Since `d_D`
  is the global optimum, no flow — spelled or not, terminal-using or not —
  whose throughput vector lies inside the §6.1 domain `0 ≤ d_i ≤ N` can be more
  likely (`competitor_maximizes_general_flow_universe`). [fact — kernel-checked]
- **The length-constrained domain is the only thing that saves the truth.** Add
  `∑ d_i = N` (the same-length cell) and `d_D` leaves the domain. [fact — verified computation
  + kernel-checked]

---

## 7. New: the certificate in Lean

`AssemblyP1/Section62VarlenPerOccurrence.lean` imports the merged witness module
and adds, kernel-checked:

| theorem | content |
|---|---|
| `dS_domain`, `dD_domain` | both spectra satisfy `0 ≤ d_i ≤ N = 5` |
| `dS_flow_throughput`, `dD_flow_throughput` | both throughput vectors are realized by a feasible §6.2 flow (`FlowThroughput`: zero supersource/supersink usage) |
| `truth_rule_agreement` | per-vertex **and** per-occurrence admissibility of both molecules, plus the truth's slack |
| `lik_le_likD_of_domain` | `d_D` maximizes the §6.1 objective over the **entire** domain |
| `lik_lt_likD_of_ne` | it is the **unique** maximizer |
| `competitor_is_unique_optimizer` | the previous three composed with `FlowThroughput dD` and `dD ≠ dS` |
| `truth_not_maximizer_in_flow_universe` | `∃ d, FlowThroughput d ∧ Domain d ∧ lik obs dS < lik obs d` |
| `not_all_feasible_throughputs_le_truth` | the negated universal form of the refuted claim |
| **new** `dS_flow_throughput_general`, `dD_flow_throughput_general` | both throughput vectors are realized by an admissible flow with terminal usage left free (`FlowThroughputGeneral`) |
| **new** `truth_not_maximizer_in_general_flow_universe`, `not_all_general_flows_le_truth` | the same refutation inside the general, terminal-allowed flow universe |
| **new** `competitor_maximizes_general_flow_universe` | `d_D` maximizes the objective over **every** candidate class inside the domain, spelled or not |
| `sum_dS`, `sum_dD` | `∑ d_S = 5`, `∑ d_D = 6` |
| `competitor_outside_length_constrained_domain` | `∑ d_D ≠ ∑ d_S`, i.e. the fixed-length boundary |

The module contains no `sorry`, `axiom`, `admit` or `native_decide`; each listed
theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited with
`#print axioms` and `lake env leanchecker`), and the shared hypothesis side is
the authoritative `SourceFaithfulIs.InformationFeasible` predicate inherited from
the merged module.

### 7.1 The precise limitation on lifting a spelled-circuit witness into the
full flow universe

The issue asks for this explicitly, so it is stated in both directions instead of
being left as "the lift is free".

- **Spelled circuit → flow universe: valid, and checked.** A spelled circuit
  carries flow `1` on each of its own step edges, uses neither terminal, and its
  vertex throughputs are the molecule spectrum (Observation 7). Hence it is a
  member of `FlowThroughput` and of the wider `FlowThroughputGeneral`. Both
  directions of that statement are kernel-checked here (`dS_flow_throughput`,
  `dS_flow_throughput_general`, and the competitor's). [fact]
- **Flow universe → spelled circuit: NOT valid in general.** A feasible §6.2 flow
  is only required to satisfy the four `Admissible` clauses (edge lower bound `0`,
  vertex lower bound `1`, signed-incidence balance `0`, vertex throughput `= d`);
  nothing requires its vertex throughput vector to be the window spectrum of a
  single circular molecule. So a throughput vector inside the flow universe need
  not be realizable by any spelled candidate, and a *positive* maximality claim
  proved at the spelled level does **not** transfer up to the flow universe.
  Producing an actual non-spelled feasible flow whose throughput no candidate
  realizes is the business of issue #214 and is **not** attempted here.
  [inference — the clause list is quoted from `AssemblyP1.Section62BidirectedFlow`,
  lines 361–367]
- **Why the limitation does not bite this cell.** `d_D` is the *unique* maximizer
  of the objective over the whole §6.1 domain, so `lik obs dS < lik obs d ≤
  lik obs dD` for **every** throughput vector in **any** candidate class inside
  the domain (`competitor_maximizes_general_flow_universe`). The refutation is
  therefore invariant under every admissible restriction *and* every admissible
  enlargement of the candidate class. Independently, the competitor's vector is
  itself realized by the spelled molecule `AAAATT`, so the instance-level
  refutation also holds at the spelled level without invoking the lift at all.
  [inference from kernel-checked facts]
- **The one thing the lift does not give.** Nothing here says the *truth's*
  membership is invariant: the truth is a member of both universes only because
  its own spelled circuit is admissible. If a future reading of §6.2 (for example
  a reading with the per-occurrence rule *not* satisfied by the truth) removed
  the truth from the candidate class, the claim "the truth is not the maximizer"
  would become vacuous rather than false — a different logical situation from the
  one certified here. [inference — recorded as a scope caveat for #217]

---

## 8. What this witness does **not** reach

Recorded so the parent does not over-claim from it. [inference + verified computation]

1. **Same-length candidates (`|D| = N`).** Excluded: `|D| = 6 ≠ 5 = N = |S|`, and
   `∑ d_D = 6 ≠ 5 = ∑ d_S`. Within the sum-constrained slice the truth's vector
   is itself a maximizer, so this instance gives no same-length refutation.
2. **Fixed-length + per-occurrence.** Still **open in the scope of §9**, but no
   longer open in general: the sibling issue **#212** reports a kernel-checked
   same-length per-occurrence counterexample (`S = ATATACAC → D = ATACACAC`,
   `G = |S| = |D| = 8`, `L = 3`, `n = 6`, `N = 8`, ratios `9/5` under literal
   §6.1 and `3/2` under the exact multinomial, both candidates per-occurrence
   feasible with `d_S ≥ x` and `d_D ≥ x`). The **zero** same-length rows of this
   audit's census (§9) are compatible with it, because the census scope is the
   two-letter `{A,T}` alphabet with `G ≤ 6`, read multiplicity `≤ 3`, competitor
   length `≤ G + 2` and `N = |S|`; #212's witness lives on the four-letter DNA
   alphabet at `G = 8`. So the census zero is a statement about the `{A,T}` small
   `G` regime, not a statement about the cell. That sibling result is **#212's
   evidence, not this issue's**; this audit does not re-verify it.
   [bounded evidence here; the #212 result is a kernel-checked fact **as
   reported**, unverified by this leaf]
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
   adds nothing. Under the actual-binomial reading of §6.1 (binomial size =
   candidate length) it is a strict improvement too (`1953125/1594323 > 1`), so
   the fixed-`N` ambiguity does not create a cell in which this pair is a tie.
6. **Which MB09 object the 2016 sentence denotes. Unchanged source ambiguity**;
   this audit says nothing about it.
7. **A cell in which the *truth* is not a candidate.** The certificate's
   hypothesis is that both molecules are §6.2 candidates; it says nothing about
   regimes where the truth itself leaves the candidate class.

---

## 9. Bounded census (evidence, not proof)

Scope: truths are the circular `{A,T}`-strings of length `G` up to rotation; a
realization is a multiplicity vector over its `G` starts (`0..maxmul`); the truth
must be per-occurrence feasible (support equality and `d_S ≥ x`) and satisfy
`I_s`; a competitor is any circular string of length up to `G+2` with the same
support, `d ≥ x` and `d ≤ N`; `N = |S|`; the alphabet is the two-letter
sub-alphabet `{A,T}`, so the molecule-class space has `2^L / 2` classes.
Rows below are `(truth, realization)` counts and `(instance, competitor)` beat
counts. [fact about the stated scope — bounded evidence]

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
consistent with the sibling note's bounded zero, and both are bounded evidence
about the stated scope; neither is a proof of absence. **The zero same-length rows
must not be read as evidence against the cell**: #212's same-length
per-occurrence witness lives outside this scope (four-letter DNA alphabet,
`G = 8`), and this census does not reach it.

---

## 10. Epistemic status

Every claim is tagged **fact** / **inference** / **choice** in the first column
and its verification class in the last.

| claim | tag | verification |
|---|---|---|
| MB09 §6.1 fixed-`N` product of binomial marginals with `0 ≤ d_i ≤ N`; §6.2 bidirected flow on the transitively reduced read-overlap graph, vertex lower bound `1`, edge bounds `0`/`∞`, supersource/supersink, `d_i` = vertex flow | **fact** (about the source) | **source fact** (MB09 §3.1–§3.4, §5.2, §6.1–§6.2) |
| reads are DNA molecules, one vertex per molecule class | **fact** (about the source) | **source fact** |
| per-vertex rule is the source rule; per-vertex ⇒ support equality for a spelled molecule | **inference** | mathematical argument (Observation 7) |
| `d ≥ x` (per-occurrence) is strictly stronger than the source rule | **fact** (mathematical) | mathematical argument |
| imposing `d ≥ x` on the candidate class (the "per-occurrence rule") | **choice** | **project-level strengthening, not source fact** — labelled as such; the cell must be read with it as a hypothesis |
| representing reads as reverse-complement *molecule classes* rather than oriented strands | **choice**, source-supported | resolved to molecule classes given §6.2; the alternative inverts this witness (§8 item 4) |
| taking the external size to be `N = |S|` and the candidate length to be unconstrained | **choice** | matches the merged witness and the issue statement; §4.2 records the residual ambiguity |
| MB09 §6.2 imposes no constraint on the *length* of the candidate; `N` enters only the objective and the domain bound | **fact** (about the source) | **source fact** (no such sentence exists in §6.2); the length-constrained reading is an added assumption |
| instance data `x`, `d_S`, `d_D`, graph (10 edges), two circuits, reduction vacuous, admissibility under both rules, domain, ratio `9/8` | **fact** | **verified computation** (independent script) |
| both witness flows satisfy `Admissible` with terminal usage free | **fact** | **verified computation** + **kernel-checked** (`*_flow_throughput_general`) |
| `I_s` holds for `(S, (0,1,4))`, full enumeration, no interleaved pair | **fact** | **verified computation** + **kernel-checked** (`SourceFaithfulIs.InformationFeasible`) |
| `d_D` is the unique maximizer over the whole §6.1 domain | **fact** | **kernel-checked** (`lik_le_likD_of_domain`, `lik_lt_likD_of_ne`) |
| both throughput vectors are in the §6.2 flow universe (zero-terminal and terminal-allowed) | **fact** | **kernel-checked** (`FlowThroughput`, `FlowThroughputGeneral`) |
| the refuted cell (bidirected, variable-length, per-occurrence) is settled negatively | **fact** | **kernel-checked** (`truth_not_maximizer_in_flow_universe`, `truth_not_maximizer_in_general_flow_universe`) |
| same-length per-occurrence cell: no beats in the stated scope | **fact** about the scope | **bounded evidence**; the cell itself is settled by #212 outside this scope |
| fixed-`N` vs actual-binomial ambiguity does not change this pair's verdict | **fact** | **verified computation** (check `(V)`) |
| the reverse lift (flow universe → spelled circuit) is not valid in general | **inference** | clause list quoted from `AssemblyP1/Section62BidirectedFlow.lean:361`; a concrete non-spelled flow is #214's open item |
| single-strand/oriented reading of this witness | **open** | inverted, not refuted |
| whether §6.2 intends the per-vertex or the per-occurrence rule | **open** | **recorded, not resolved** (§4.2 item 1) |
| whether §6.1's binomial size is `N` or the candidate's length | **open** | **recorded, not resolved** (§4.2 item 2); immaterial for this pair |
| which MB09 object the 2016 sentence denotes | **open**, unchanged | — |

---

## 11. Reproduce

```sh
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py            # 60 checks
python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py --census   # bounded census
lake build AssemblyP1.Section62VarlenPerOccurrence
```

The Python script prints every intermediate graph edge, bridge witness and
objective factor, and exits non-zero on any failure; all arithmetic is exact
(`fractions.Fraction`). The census is run only under `--census` and takes about
20 s on a laptop.

### 11.1 Executed verification log (re-verification round, 2026-10-09)

What was actually run on branch `agent/board-213-5fff16` in
`/workspace/assemblyp1-finite-213`, with its observed outcome. No step is
recorded from an earlier round without having been re-run.

| command | outcome |
|---|---|
| `python3 scripts/check-research-docs.py` | pass |
| `python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py` | pass — `ALL AUDIT CHECKS PASS (60 checks)` |
| `python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py --census` | exit `0`; the six rows of §9 reproduced exactly, same-length beats still `0` in every row |
| `rm` of the module's `.olean`/`.ilean`/`.trace`/`.c`/`.setup.json`, then `lake build AssemblyP1.Section62VarlenPerOccurrence` | rebuilds the module from source in 8.7 s, `Build completed successfully` — the certificate is not resting on a stale artifact |
| `lean` probe `import AssemblyP1.Section62VarlenPerOccurrence` + `#print axioms` on **all 35** theorems | every theorem reports `depends on axioms: [propext, Classical.choice, Quot.sound]`, exit `0` |
| `leanchecker AssemblyP1.Section62VarlenPerOccurrence` (kernel replay of the module's own `.olean`) | exit `0`, no diagnostic output |
| `lake build AssemblyP1.BBTTripleBridge` | still fails with source-level type errors (now also at lines 152 and 153), confirming the §12 blocker |

Two operational notes for whoever re-runs this. `lake env` on this host triggers
the workspace's *default* target — the glob over every `AssemblyP1.*` submodule —
so `lake env lean`/`lake env leanchecker` hang rather than answer; the probe and
the replay above were therefore run against `<toolchain>/bin/lean` and
`<toolchain>/bin/leanchecker` with `LEAN_PATH` assembled by hand from
`.lake/build/lib/lean` and each `.lake/packages/*/.lake/build/lib/lean`. And
`leanchecker` resolves *module names* from `LEAN_PATH`, so it must be given
`AssemblyP1.Section62VarlenPerOccurrence`, not the `.olean` path (the latter
fails with `Could not resolve module`).

---

## 12. Recorded blockers observed while auditing (not caused by this issue)

On this worktree at `cc0aa8a` (= `origin/main`), a **full** `lake build` fails in
modules that this issue does not touch, both with and without my change
(re-verified in this refresh by `lake build AssemblyP1` in the registered
worktree, log kept in `/tmp`):

- `AssemblyP1/BBTTripleBridge.lean` — genuine source-level type errors
  (e.g. line 81 declares `cyc_congr {x y : ℕ} (h : x % G = y)` where the
  `Fin.ext` application needs `x % G = y % G`; further mismatches at lines
  85, 97, 100, 101, …), introduced when the file was split for bounded
  elaboration in `42ebed7`;
- `AssemblyP1/Issue94OrbitSearch.lean` — the compiler is killed (exit `137`,
  OOM) while elaborating it on this host.

The build stops at those two, so the modules behind them
(`AssemblyP1.Issue94Transposition`, `AssemblyP1.Issue94WitnessPair`, and the root
aggregator `AssemblyP1.lean`) are not reached on this host; the earlier audit run
observed the same OOM signature in them under more memory pressure.

Consequence: the root aggregator `AssemblyP1.lean` cannot currently be built
here, so the module registration and the `#print axioms` block added for this
issue are verified by an equivalent standalone probe
(`import AssemblyP1.Section62VarlenPerOccurrence` + the same fourteen
`#print axioms` lines, each reporting only
`[propext, Classical.choice, Quot.sound]`) and by `lake env leanchecker`, not by
a root build. These failures are pre-existing and are reported here so that the
parent does not attribute them to this leaf.

---

## 13. Relation to the repository's existing results

| existing claim | location | status after this audit |
|---|---|---|
| variable-length per-occurrence case resolved negatively, ratio `9/8` | `docs/bridging-se62-flow-ml-counterexample.md` §3, §7 | **confirmed** independently; strengthened by the flow-universe and global-optimality certificates |
| the sequence-level support/`d ≥ x` certificate is not §6.2 feasibility | same, §2 | unchanged and correct |
| same-length cell refuted under the per-vertex rule (`AAATAT→AAAAAT`) | `docs/section62-same-length-bidirected-counterexample.md` | unchanged; **not** implied by this witness |
| same-length per-occurrence cell open, bounded zero | same, §3, §7 | the *scope* result is corroborated by this audit's census (§9); the cell itself is claimed settled by #212 outside that scope — **#212's evidence, not re-verified here** |
| `4^k` vs molecule-class index fork resolved to molecule classes given §6.2 | `docs/source-notes/mb09-se61-index-orientation-resolution.md` | unchanged; the audited witness is stated for that reading only |

---

## 14. Coordination on shared definitions with issue #212

Per the issue charter, this leaf coordinates **only on shared definitions** with
the same-length per-occurrence issue #212; it does not do that issue's work.
What was compared, and the outcome:

| shared object | #213 (this leaf) | #212 (sibling) | aligned? |
|---|---|---|---|
| per-occurrence rule | `PerOccurrenceAdmissible d := ∀ c, obs c ≤ d c` (over the `8` `{A,T}` classes) | `PerOccurrenceFeasible d x := ∀ c, x c ≤ d c` (over the `64` DNA classes) | **yes** — same predicate, different class universe; for unobserved classes both readings are vacuous |
| support equality kept separate from the per-occurrence bound | `SeqSupportLB d x := (∀ c, 0 < d c ↔ 0 < x c) ∧ ∀ c, x c ≤ d c` | `SupportEquality` proved alongside `PerOccurrenceFeasible` | **yes** — same decomposition |
| the source rule | `PerVertexAdmissible d := ∀ v ∈ readVerts, 1 ≤ d (repCode v)` | per-vertex lower bound `1` inside `Feasible62` | **yes** |
| §6.1 objective | `marginal x d c = C(3, x c) (d c / 5)^{x c} (1 - d c / 5)^{3 - x c}` | literal §6.1 product of binomial marginals with external `N` | **yes** — same shape, `N = 5` vs `N = 8` |
| labelling of the per-occurrence rule | **project-level strengthening, not source fact** (§4.1) | **project-level strengthening, not source fact** (their module docstring) | **yes** |
| flow feasibility object | `Feasible62` (zero terminal usage) / `Admissible` (terminal-free reading) | `Feasible62` via `AssemblyP1.Section62Flow` | **yes** — same shared predicate |

No definitional disagreement was found, so no change was needed on either side.
The one substantive difference is *scope only*: #213's witness and census live on
the two-letter `{A,T}` alphabet with `G ≤ 6`, while #212's witness lives on the
four-letter DNA alphabet at `G = 8`. Anything the parent matrix wants to say
about the *size* or *alphabet* regime must therefore distinguish the two.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.1–§3.4, §5.2, §6.1–§6.2,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, Eq. (1) and §5.
