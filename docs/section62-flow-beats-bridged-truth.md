# A bridged, Section 6.2-feasible truth beaten by a non-spellable Section 6.2 flow (issue #36)

_Status: independent from-scratch reconstruction + mathematical argument + bounded
exhaustive exact-rational computation. 2026-09-20. All claims are classified as
**source fact**, **modeling decision**, **mathematical argument**, **verified
computation**, or **open**. This note does not settle the source-ambiguous
Shomorony et al. open question; it closes the concrete residue recorded in
[`section62-bidirected-flow-feasibility.md`](../section62-bidirected-flow-feasibility.md)
§6 (branch artifact) as “a *spellable* truth can be beaten by a Section 6.2 flow
that is not any single molecule.”_

_Reproduction: `python3 scripts/se62_flow_beats_bridged_truth.py`
(self-contained, exact `fractions.Fraction`, deterministic, ~2.5 min; exits
non-zero on any failed assertion)._

_Relationship to prior work. The unmerged branch `analysis/issue36-nonspellable-broader`
(commit `6b22d48`) contains witnesses for the same residue. This note was written
without reading that branch's script; it re-derives the witnesses and, as a
by-product, shows that the branch's “the phenomenon is `o_min = 1` only” remark
is an artifact of its overlap-graph convention, not a property of the bidirected
model. The exhaustive `per-occurrence`, representative-graph counts below match
that branch's table row for row, which is independent confirmation of its
arithmetic._

---

## 0. Answer at a glance

1. **The residue is positive.** There exist bridged (`I_s`) truths `S` whose own
   window spectrum `d_S` is a feasible Medvedev–Brudno §6.2 flow, and a second
   feasible §6.2 flow `d` that (i) is **not the window spectrum of any single
   molecule** and (ii) strictly improves the §6.1 separable binomial objective.
   Three witnesses are re-derived here (§3–§4).

2. **Every non-spellable beat found in scope comes from a truth with a
   non-vacuous triple repeat**, so the phenomenon is not an artifact of trivial
   bridging (i.e. coverage alone).

3. **The winning flow in each witness is small and hand-checkable.** The smallest
   beat in the searched scope is `S = 00101` (`G = 5`, `L = 3`), with
   `d = {001:1, 010:2, 100:1}`, objective ratio `3/2`. The witness with a
   genuine length-3 triple repeat is `S = 000001` (`G = 6`, `L = 4`), ratio
   `1024/625` under the literal lower-bound-1 reading.

4. **The `o_min` dependence is a convention, not a theorem.** On the
   repository's representative-overlap graph the non-spellable beats exist only
   at `o_min = 1`; on the faithful orientation-folded bidirected relation they
   persist for every `o_min < L`. The source says “bidirected”, so the folded
   relation is the closer reading; see §5.

5. **Flows are not sequences.** No claim here is about a maximum-likelihood
   *sequence*: `d` is a non-contiguous assembly, exactly the object §6.2
   optimizes. The sequence-level question of
   [`section-6-2-feasible-set-membership.md`](../section-6-2-feasible-set-membership.md)
   §5 is untouched.

---

## 1. Source object and exact model

**Source facts** (Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.3, §6.1–6.2, PMC3154397;
quotes as recorded with SHA-256 hashes in
[`source-notes/shomorony-mb-formulation-provenance.md`](../source-notes/shomorony-mb-formulation-provenance.md)
§4 and [`section62-bidirected-flow-feasibility.md`](../section62-bidirected-flow-feasibility.md)
§1):

- §6.2 builds the “transitively reduced **bidirected** overlap graph” whose
  “**vertices … are the reads**”.
- “Each vertex has a lower bound of `1` … All other lower bounds are `0` and all
  upper bounds are infinity.”
- “By Observation 7, the `d_i`'s … actually correspond to the value of the flow
  through vertex `i`”, with “convex cost functions for the vertices”.
- “Since any flow can be decomposed into a collection of walks, our flow
  represents a **(non-contiguous) assembly** of the genome.”
- §6.1 optimizes the separable binomial
  `∏_w C(n,x_w) (d_w/N)^{x_w} (1 − d_w/N)^{n−x_w}` with the externally known
  genome length `N`, where `x` is the observed read-type count vector and
  `n = Σ_w x_w` is the number of reads.

**Modeling decisions** (each is a deliberate interpretation, kept explicit):

1. **Read molecules.** A read is a DNA molecule, i.e. an unordered
   reverse-complement pair. On a binary alphabet the involution is `0 ↔ 1`; a
   vertex is a molecule class `{w, rc(w)}`. (Whether the final published
   statement quotients reverse complements is itself a source ambiguity; the
   repository analyses both. All witnesses below are stated for the double-
   stranded reading.)
2. **Edges.** Two molecule classes `U, V` are joined by a bidirected overlap iff
   *some orientation* of `U` overlaps *some orientation* of `V` with length at
   least `o_min`. The relation is symmetric (reverse-complement the overlap
   equation), so the directed graph used below contains both directions; the
   circulation test is then the standard conservative orientation of the
   underlying undirected bidirected graph. This is the **folded** relation.
   A strictly smaller **representative** relation fixes the canonical
   representative `min(w, rc(w))` and requires direct suffix–prefix overlap of
   representatives; it is the convention used by the earlier repository §6.2
   notes.
3. **Transitive reduction.** The source says the graph is transitively reduced.
   The representative relation is reduced by junction containment (drop `u→v`
   when a read `w` spans the junction, `ov(u,w)+ov(w,v) ≥ L+ov(u,v)`). The
   reduction convention on a bidirected graph is a separate open modeling choice;
   the folded results below are therefore stated on the **unreduced** folded
   relation, and the representative results use the repository's reduction.
4. **Truth admissibility.** A truth `S` is an admissible §6.2 candidate iff its
   own window spectrum `d_S` is a feasible flow on the observed vertices. Since
   every observed read is a window of `S`, this forces
   `supp(d_S) = supp(x)`; `d_S` is always realizable by `S`'s cyclic window walk.
   The source lower bound is `1`, so the literal reading adds nothing. The
   repository's Observation-7 argument adds the per-occurrence bound
   `d_S(w) ≥ x_w`; both are searched.
5. **Competitor class.** All integer circulations with `1 ≤ d_w ≤ N`; the upper
   bound is the §6.1 binomial domain. Spellability is checked separately: a
   molecule with spectrum `d` must have length `Σ d_w`, so enumerating
   `Σ`-words of that length is complete.

**Bridging `I_s`** (Shomorony et al.): coverage, every triple repeat all-bridged,
and every interleaved pair bridged on at least one copy. Implemented from
scratch in the script; `I_s` is checked directly on each witness.

---

## 2. The two objective computations

For a competitor `d` and truth spectrum `d_S`, all binomial coefficients cancel
and

```text
L(d)/L(d_S) = ∏_w [(d_w/N)^{x_w} (1 − d_w/N)^{n−x_w}]
            / [(dS_w/N)^{x_w} (1 − dS_w/N)^{n−x_w}],
```

with every factor evaluated over the observed support; exact `Fraction`s.
Ratios below are all `> 1`, so `d` strictly beats the truth.

---

## 3. Witnesses (verified computation; exact rationals)

### W1 — `G = 6`, `L = 3`, non-vacuous triple repeats

```text
S         = 000101,  G = 6,  L = 3,  starts = (0, 1, 3, 5),  n = 4 < G
d_S       = {000:1, 001:1, 010:3, 100:1}      (S's window spectrum)
x         = {000:1, 001:1, 010:1, 100:1}
d         = {000:1, 001:1, 010:2, 100:1}      (a feasible flow)
nonspell  sum(d) = 5; no length-5 binary molecule has spectrum d
I_s       holds; triple repeats {0}×{0,1,2}, (0,1,4), (0,2,4), (1,2,4)
          are all bridged
ratio     L(d)/L(d_S) = 128/81 = 1.5802…
```

`S` has a non-vacuous triple repeat (the symbol `0` occurs at positions
`0,1,2,4`, and every length-1 triple is all-bridged by the reads at starts
`(0,1,3,5)`). `d_S ≥ x`, so the truth is feasible under **both** the literal and
the per-occurrence reading. The beating flow is `d = d_S` with
`010` reduced from `3` to `2`, i.e. it moves the copy count of the most
over-represented molecule toward the coordinate optimum `N x_w/n = 6/4 = 1.5`.
The realization uses the tandem self-loop `010 → 010` (the molecule `010` can
follow itself through its reverse complement `101` with a proper overlap), which
is a legitimate circulation edge; the truth's own cyclic window walk uses it too.

### W2 — `G = 6`, `L = 4`, self-loop-free and coverage-only bridging

```text
S         = 000111,  G = 6,  L = 4,  starts = (0, 1, 3, 4),  n = 4 < G
d_S       = {0001:2, 0011:1, 1000:2, 1100:1}
x         = {0001:1, 0011:1, 1000:1, 1100:1}
d         = {0001:2, 0011:2, 1000:2, 1100:2}
nonspell  sum(d) = 8; no length-8 binary molecule has spectrum d
ratio     L(d)/L(d_S) = 16384/15625 = 1.048576
```

This is the unmerged branch's headline witness, re-derived independently. `S`
has no triple repeat and no interleaved pair, so `I_s` reduces to coverage; the
graph has no self-loops. In the representative-reduced graph the edges are
`{0001→0011, 0001→1000, 0011→1100, 1000→0001, 1100→0011, 1100→1000}`, and `d`
is the sum of the three cycles

```text
0001 → 0011 → 1100 → 1000 → 0001
0001 → 1000 → 0001
0011 → 1100 → 0011
```

(one unit each), a non-contiguous assembly with throughput `2` at each vertex.

### W2MIN — smallest beat in the searched scope

```text
S         = 00101,  G = 5,  L = 3,  starts = (0, 2, 4),  n = 3 < G
d_S       = {001:1, 010:3, 100:1}
x         = {001:1, 010:1, 100:1}
d         = {001:1, 010:2, 100:1}
nonspell  sum(d) = 4
ratio     L(d)/L(d_S) = 3/2
```

Realized by the cycle `001 → 010 → 100 → 001` plus the tandem self-loop
`010 → 010`.

### W3 — `G = 6`, `L = 4`, a genuine length-3 triple repeat, literal reading

```text
S         = 000001,  G = 6,  L = 4,  starts = (0, 2, 3, 3, 4, 5),  n = 6 = G
d_S       = {0000:2, 0001:1, 0010:1, 0100:1, 1000:1}
x         = {0000:1, 0001:1, 0010:2, 0100:1, 1000:1}
d         = {0000:1, 0001:1, 0010:2, 0100:2, 1000:1}
I_s       holds; triple repeats include the length-3 class (000 at {0,1,2})
nonspell  sum(d) = 7
ratio     L(d)/L(d_S) = 1024/625 = 1.6384
```

Here `d_S(0010) = 1 < x(0010) = 2`: the observed count of read `0010` exceeds
its copy number in the truth, which the literal lower-bound-1 model permits
(reads are sampled with replacement) but the per-occurrence reading forbids.
`S` has a genuine length-3 triple repeat, all of whose copies are bridged, so
`I_s` is non-vacuous in the strongest sense. The same literal-reading phenomenon
is abundant in the scope table below.

---

## 4. Exhaustive bounded scopes

Binary alphabet, revcomp `0↔1`; every truth `S`, every start multiset with
`n` from `⌈G/L⌉` to `G`, and every throughput vector `1 ≤ d_w ≤ G`; truth must
satisfy `I_s` and (for `per_occ`) `d_S ≥ x`. Counts are exact (not capped):
`instances / spellable beats / non-spellable beats` (all non-spellable beats in
the shown rows have triple-repeat truths).

| graph | `G` | `L` | `o_min` | reading | instances | spellable | **non-spellable** |
|---|---|---|---|---|---|---|---|
| representative-reduced | 5 | 3 | 1 | per-occurrence | 552 | 30 | **20** |
| representative-reduced | 5 | 3 | 2 | per-occurrence | 362 | 0 | **0** |
| representative-reduced | 6 | 3 | 1 | per-occurrence | 2504 | 72 | **96** |
| representative-reduced | 6 | 3 | 2 | per-occurrence | 1204 | 0 | **0** |
| folded (unreduced) | 5 | 3 | 1 | per-occurrence | 552 | 30 | **230** |
| folded (unreduced) | 5 | 3 | 2 | per-occurrence | 552 | 30 | **230** |
| folded (unreduced) | 6 | 3 | 1 | per-occurrence | 2504 | 84 | **528** |
| folded (unreduced) | 6 | 3 | 2 | per-occurrence | 2504 | 84 | **528** |
| folded (unreduced) | 5 | 4 | 1 | per-occurrence | 482 | 0 | **0** |
| representative-reduced | 5 | 3 | 1 | literal | 782 | 350 | **400** |
| representative-reduced | 6 | 3 | 1 | literal | 2768 | 1116 | **936** |
| folded (unreduced) | 5 | 3 | 1 | literal | 782 | 400 | **2990** |
| folded (unreduced) | 6 | 3 | 1 | literal | 2768 | 1416 | **8952** |

The two `representative-reduced, per-occurrence` rows reproduce the unmerged
branch's recorded counts `(552, 30, 20)` and `(2504, 72, 96)` exactly, from an
independent implementation.

**Observations.**

- Non-spellable beats exist and are common; the residue is not a measure-zero
  accident.
- In these scopes, **all** non-spellable beats arise from truths with a triple
  repeat, and all have `n < G`.
- On the representative graph the non-spellable beats vanish at `o_min = 2`; on
  the folded relation they do not (rows for `o_min = 1, 2` are identical because
  for these small `L = 3` instances the folded relation already saturates below
  `o_min = 2`).
- `G = 5, L = 4` has zero beats in scope.

This is computational evidence, bounded by the printed scope and the binary
alphabet; it is not a proof of absence beyond it, nor of the behavior for larger
`G`, larger alphabets, or `n > G`.

---

## 5. The `o_min` sensitivity, and why it is a convention

For each witness the script classifies `o_min ∈ {1, …, L−1}`:

```text
W1  (000101, G=6, L=3):  rep-reduced o_min=1 only;  folded all o_min < L
W2  (000111, G=6, L=4):  rep-reduced o_min=1 only;  folded all o_min < L
W2MIN (00101, G=5, L=3): rep-reduced o_min=1 only;  folded all o_min < L
```

The representative relation fixes one orientation per molecule and therefore
**misses genuine overlaps between reverse-complement orientations**. The folded
relation does not. Since §6.2 explicitly builds a *bidirected* graph on *DNA
molecules* (unordered revcomp pairs), the folded relation is the closer reading;
the earlier “the non-spellable phenomenon is `o_min = 1` only” statement is an
artifact of the representative convention. The exact transitive reduction of the
folded graph remains a separate open modeling question (§6).

---

## 6. What is and is not established

| statement | status |
|---|---|
| §6.2 optimizes over flows / non-contiguous assemblies; vertex lower bound `1`; objective is the §6.1 binomial with external `N` | **source fact** |
| A truth `S` is an admissible candidate iff `d_S` is a feasible flow; forces `supp(d_S)=supp(x)` | **mathematical argument** |
| W1/W2/W2MIN/W3 are `I_s`-bridged, their truths are feasible flows, and their competitors are feasible, non-spellable flows with ratio `>1` | **verified computation** (exact rationals) |
| W1/W2/W2MIN truths are per-occurrence feasible; W3 is literal-only | **verified computation** |
| Every non-spellable beat in the printed scopes has a triple-repeat truth | **verified computation**, bounded |
| Representative-graph `per-occurrence` counts match the unmerged branch | **verified computation** (independent reproduction) |
| On the folded bidirected relation the beats persist for all `o_min < L` | **verified computation + modeling argument** |
| Transitive reduction of the folded bidirected graph | **open** (separate convention) |
| Whether the 2016 sentence intends the §6.2 flow problem at all, and its strand/`o_min` conventions | **open** (issue #36 source ambiguity) |

**What is not conflated.** `d` is a flow (a collection of walks), not a
molecule. The witness shows a maximum-likelihood *assembly* can differ from the
truth; it does **not** show that a maximum-likelihood *sequence* differs from the
truth, which is the literal 2016 open question. The sequence-level feasible set
is smaller (support equality plus multiplicity bounds on a single molecule), and
this note makes no claim about it.

---

## 7. Reproduce

```sh
python3 scripts/se62_flow_beats_bridged_truth.py          # full, ~2.5 min
python3 scripts/se62_flow_beats_bridged_truth.py --quick  # witness + 4 scopes, ~10 s
```

The script verifies the four witnesses, prints the `o_min` sensitivity table,
runs the exhaustive scopes, and exits non-zero on any failed assertion. All
arithmetic is exact `fractions.Fraction`.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.3, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, §2, §5.
