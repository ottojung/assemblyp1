# A genuine non-spellable §6.2 bidirected-flow counterexample, and why the earlier folded-graph witnesses fail

_Status: source reading + mathematical argument + exact-rational certificate,
2026-09-20. All claims are labelled **source fact**, **modeling decision**,
**mathematical proof**, **verified computation**, or **open**. This note does
not settle which Medvedev–Brudno object the Shomorony et al. (2016) sentence
intends._

_Reproduction: `python3 scripts/verify_bidirected_nonspellable_counterexample.py`
(self-contained, exact `fractions.Fraction`, deterministic, under a minute;
exits non-zero on any failed assertion)._

_Relation to prior work. This note resolves, in the positive, the residue left
open by `analysis/issue36-nonspellable-flow`
(`docs/section62-nonspellable-flow-counterexample.md` §5) and by
`analysis/se62-bidirected-flow-fidelity-audit-0920` §6: whether a
**non-spellable** §6.2 flow can strictly beat a truth-feasible bridged genome
on the source's graph. It also corrects the positive claims of the unmerged
branch `agent/issue36-literal-flow-search-0920` and of
`analysis/issue36-nonspellable-broader`, whose witnesses die once strand
orientation and the `o_min`-density of traceability are modelled faithfully._

---

## 0. Verdict at a glance

1. **The earlier non-spellable witnesses are folded-graph artifacts.**
   `W1` (`S=000101`) and `W2MIN` (`S=00101`) are feasible only on the
   *unreduced* overlap graph at `o_min = 1`; their winning edge is removed by
   Myers transitive reduction and is absent at `o_min = 2`. `W2`
   (`S=000111`) survives reduction, but it is the observable throughput of a
   spelled molecule with skipped windows (`0001100011`). None of them is a
   genuine non-spellable Section 6.2 flow. [mathematical proof + verified
   computation, §5]

2. **There is a genuine non-spellable flow counterexample.**
   ```
   alphabet          {0, 1},  reverse-complement involution 0 <-> 1
   truth             S = 001011        (G = 6, circular)
   read length       L = 4
   realized starts   (0, 1, 3, 3, 3, 4)   (n = 6 reads)
   external size     N = |S| = 6
   o_min             2  (= L - 2 < L - 1)
   observed          x = {0010:1, 0101:1, 0110:3, 1100:1}
   truth flow        d_S = {0010:2, 0101:1, 0110:2, 1100:1}
   competitor flow   d  = x              (per-type lower bound 1)
   ```
   `I_s` holds with a **non-vacuous** triple repeat *and* a non-vacuous
   interleaved pair; `d_S` is realized by `S`'s own cyclic window walk on the
   transitively reduced oriented graph; `d` is an admissible integer
   circulation with the explicit six-edge certificate of §3.3; and
   ```
   L_{6.1}(d) / L_{6.1}(d_S) = 2278125 / 1048576  ~ 2.1726  >  1.
   ```
   Moreover `d` is **not the window spectrum of any circular molecule**: no
   spelled molecule beats `d_S` at all (§4). So the winning Section 6.2
   candidate is a genuinely non-contiguous assembly, not merely a spelled
   sequence. [mathematical proof + verified computation]

3. **What fails in the folded models.** The unmerged positive results treated a
   read *molecule* as a single graph vertex and allowed a molecule-level
   self-loop to contribute one unit of throughput. Under the source-faithful
   **orientation-resolved** graph (one node per strand, as Myers/bidirected
   overlaps require), a molecule-level self-loop realized through a reverse-
   complement flip traverses *two* orientation nodes and contributes two units
   of molecule throughput (or requires a same-strand overlap that may be below
   `o_min`). This discrepancy is exactly what creates the phantom witnesses.
   [mathematical argument + verified computation, §5]

4. **`o_min < L - 1` matters twice.** It enlarges the flow class (unobserved
   windows can be skipped), which lets a non-spellable flow be *padded* into a
   spelled molecule whenever the observed windows are `(L - o_min)`-dense. The
   witness above is designed so that no padding can beat the truth while the
   unpadded circulation can; it sits at `o_min = L - 2`. [mathematical
   argument]

---

## 1. The source objects

### 1.1 Section 6.2, source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397
(quotations as recorded in
[`docs/source-notes/mb09-section62-source-semantics-verification.md`](source-notes/mb09-section62-source-semantics-verification.md)):

- the graph is the **transitively reduced bidirected read-overlap graph**, whose
  vertices are the reads, "which are DNA molecules";
- a DNA molecule is an unordered reverse-complement pair of strands (§3.1), so a
  read and its reverse complement are **one** vertex;
- overlap edges are all bidirected overlaps of length at least `o_min`; balance
  is the signed incidence `pos - neg = b` (§3.4);
- **each read vertex has lower bound `1`**, all other lower bounds are `0`, all
  upper bounds are `infinity`; the vertex bound is realized on the §5.2 split
  edge `v^- -> v^+`;
- the objective is the §6.1 **separable binomial** with the external genome
  length `N`, `c_i(d_i) = -x_i log d_i - (n - x_i) log(N - d_i)`;
- the returned object is an integer flow, explicitly a "**(non-contiguous)
  assembly**"; Observation 7 identifies the flow through a read vertex with the
  number of times the read appears as a submolecule of the molecule spelled by
  the walk. [source fact]

The paper's own experiments use reads of length `25` and `o_min = 17..21`
(§8.2), i.e. `o_min < L - 1 = 24`; the source regime therefore permits a
spelled molecule to contain length-`L` windows that are **not** observed reads.
[source fact]

### 1.2 Modeling decisions used here

1. **Orientation-resolved graph.** The bidirected overlap graph is rendered in
   the standard skew-symmetric way: nodes are the `2 |V|` strands of the
   observed molecule classes `V`, and `a -> b` is a directed edge iff the
   longest proper suffix-prefix overlap `ov(a,b)` is at least `o_min`. This is
   the faithful rendering of the four §3.3 orientation cases; a molecule-level
   self-loop is a directed 2-cycle through the two strands. [modeling decision,
   forced by the source's molecule semantics]
2. **Transitive reduction.** `a -> b` is removed when some strand `c` with
   `c != a,b` satisfies `ov(a,c) >= ov(a,b) + 1` and
   `ov(a,c) + ov(c,b) >= ov(a,b) + L` (Myers junction containment). This
   preserves the set of spelled molecules; overlap-`(L-1)` edges are never
   removed (no shorter overlap can spell them). [modeling decision]
3. **Traceability.** A circular molecule `D` is *traceable* on `V` iff walking
   `D`'s length-`L` windows and keeping the observed ones, every cyclic gap
   between consecutive observed windows is at most `L - o_min` and the
   corresponding reduced edge exists. Its throughput is `spec_L(D)|_V`
   (Observation 7). This is the corrected `o_min`-parameterized criterion of
   `analysis/se62-independent-reconstruction`. [mathematical fact]
4. **Lower bound.** The source's lower bound `1` is per observed read
   *molecule/type*, following the presence-once wording and the role of `x` as a
   sampling count with replacement. The per-occurrence strengthening
   `d_w >= x_w` is a strictly stronger variant. [modeling decision, per
   `docs/source-notes/mb09-section62-source-semantics-verification.md` §2.1]

---

## 2. The witness

Alphabet `{0,1}` with reverse complement `0 <-> 1`; the molecule class of a
word is `min(w, rc(w))`.

```text
truth S = 001011   (G = 6)
read length L = 4
starts = (0, 1, 3, 3, 3, 4)     n = 6
N = G = 6
o_min = 2
```

Length-4 circular windows of `S` and their molecule classes:

| start | window | class |
|---|---|---|
| 0 | `0010` | `0010` |
| 1 | `0101` | `0101` |
| 2 | `1011` | `0010` (`rc(1011)=0010`) |
| 3 | `0110` | `0110` |
| 4 | `1100` | `1100` |
| 5 | `1001` | `0110` (`rc(1001)=0110`) |

Hence `d_S = {0010:2, 0101:1, 0110:2, 1100:1}` and, from the realized starts,
`x = {0010:1, 0101:1, 0110:3, 1100:1}`. Every position of `S` is an observed
window, so the truth's cyclic window walk is traceable and realizes `d_S`; the
`d_S(w) >= 1` lower bound holds per type. [verified computation]

### 2.1 The `I_s` certificate

- **Coverage.** Starts `0,1,3,4` cover positions `{0,1,2,3} ∪ {1,2,3,4} ∪
  {3,4,5,0} ∪ {4,5,0,1} = Z_6`. [verified computation]
- **Triple repeats.** `S` has two maximal triple repeats of length `1`:
  the symbol `0` at positions `{0,1,3}` and the symbol `1` at positions
  `{2,4,5}` (each has `>1` distinct flank on each side). Every copy is bridged
  by a realized read; the script prints the actual bridging reads.
  [verified computation]
- **Interleaved pair.** The maximal repeat pairs of length `2` are `(1,3)`
  (word `01`) and `(2,5)` (word `10`); their four starts `1,2,3,5` alternate
  `A,B,A,B` cyclically, and copy `1` of the first pair is bridged. So the
  interleaving conjunct is satisfied non-vacuously. [verified computation]

So `I_s` holds and none of its conjuncts is vacuous for this truth — unlike the
coverage-only witnesses elsewhere in the repository.

### 2.2 The competitor flow

`d = x = {0010:1, 0101:1, 0110:3, 1100:1}` satisfies `d_w >= 1` and
`d_w <= N = 6`. On the transitively reduced oriented graph at `o_min = 2`,
`molecule_feasible(d)` is true; the explicit certificate produced by the script
is

```text
orientation throughput: {0101:1, 0110:2, 1011:1, 1001:1, 1100:1}

edge flow (all edges survive Myers reduction):
   0101 -> 0101   f=1   ov=2      (self-loop)
   0110 -> 1011   f=1   ov=2
   1011 -> 0110   f=1   ov=3
   0110 -> 1100   f=1   ov=3
   1100 -> 1001   f=1   ov=3
   1001 -> 0110   f=1   ov=2
```

The orientation throughputs map back to molecule throughput
`d(0010) = 0 + 1 = 1` (via strand `1011`), `d(0110) = 2 + 1 = 3` (via strands
`0110` and `1001`), `d(0101) = 1`, `d(1100) = 1`. The flow decomposes into the
self-loop `0101->0101`, the 2-cycle `0110<->1011`, and the 3-cycle
`0110->1100->1001->0110`. It is therefore a legitimate non-contiguous
Section 6.2 assembly. [verified computation]

### 2.3 The strict likelihood improvement

With `n = 6`, `N = 6` and the literal §6.1 product of per-type binomials over
the observed classes,

```text
for 0010 (x=1): g(1)/g(2) = (3125/46656)/(32/729) = 3125/2048
for 0110 (x=3): g(3)/g(2) = (1/64)/(8/729)          = 729/512
for 0101, 1100 (x=1, d_* = d_S = 1):                  1
L(d)/L(d_S) = (3125/2048)*(729/512) = 2278125/1048576 ~ 2.1726 > 1,
```

where `g(d) = (d/6)^{x_w}(1 - d/6)^{6-x_w}`. [mathematical proof + verified
computation]

---

## 3. Non-spellability: a complete finite proof

**Claim.** No circular molecule `D` (over `{0,1}`, any length) has a traceable
throughput whose §6.1 objective exceeds `d_S`'s.

_Proof._ Suppose a traceable molecule `D` beats `d_S`, with throughput `thr`.
Then `thr_w` is an integer in `[1, N] = [1,6]` for each `w in V` (the §6.1
objective domain) and `binom_obj(thr) > binom_obj(d_S)`. An exhaustive check of
the `6^4 = 1296` vectors in `[1,6]^V` shows that exactly six vectors beat `d_S`
and that all six have total visit count `sum(thr) <= 7`. (The six are
`{1,1,2,1}`, `{1,1,3,1}`, `{1,1,3,2}`, `{1,1,4,1}`, `{1,2,3,1}`, `{2,1,3,1}` in
the order of `V`.) A traceable molecule with total visits `s` has at most
`(L - o_min - 1) * s = s` unobserved windows, hence length at most `2s <= 14`.
An exhaustive enumeration of all `2^1 + ... + 2^14` binary molecules of length
at most `14` confirms that the maximum objective among traceable molecules is
attained only by `S = 001011` itself, at ratio `1`. Contradiction. ∎

[verified computation: the script asserts both the `sum <= 7` bound and the
length-`14` enumeration.]

Thus the improving candidate `d = x` is a genuine §6.2 flow that is **not**
the observable throughput of any spelled molecule: the non-spellable part of
the §6.2 candidate class is strictly necessary for this counterexample.

---

## 4. Why the earlier "non-spellable" witnesses fail

All three witnesses below come from the unmerged branch
`agent/issue36-literal-flow-search-0920` (also present in
`analysis/issue36-nonspellable-broader`), which modelled the graph on
*molecule classes* and allowed a molecule-level self-loop.

### 4.1 `W1 = 000101` and `W2MIN = 00101` die under transitive reduction

For `W1` (`S=000101`, `L=3`, starts `(0,1,3,5)`,
`d={000:1,001:1,010:2,100:1}`) the script finds:

```text
o_min=1, raw (unreduced):   feasible
o_min=1, reduced:           infeasible
o_min=2:                    infeasible (raw and reduced)
```

Its circulation uses a tandem repetition of molecule `010`. In the folded model
this is a self-loop of weight one; in the orientation-resolved model it is the
2-cycle `010 <-> 101` (overlaps `2`), which either overshoots the demanded
throughput (a unit 2-cycle contributes two visits to the molecule `010`) or
requires the same-strand overlap `ov(010,010) = 1`, which is transitively
reducible and below `o_min = 2`. `W2MIN` fails identically: its winning edge
`100 -> 001` (overlap `1`) is spelled through `010`
(`ov(100,010) + ov(010,001) = 2 + 2 >= 3 + 1`) and is removed.

### 4.2 `W2 = 000111` survives reduction but is observably spellable

For `W2` (`S=000111`, `L=4`, starts `(0,1,3,4)`,
`d = {0001:2,0011:2,1000:2,1100:2}`) the flow is feasible on the reduced graph
at `o_min = 1, 2`. But the molecule

```text
D = 0001100011   (length 10)
```

is traceable at `o_min = 2` with observed throughput exactly `d` (windows
`0001,0011,0110,1100,1000,0001,0011,0110,1100,1000`; every gap between observed
windows is at most `2`). So `W2` is a *spelled* Section 6.2 candidate once the
source's `o_min < L - 1` regime is respected, not a non-spellable one.

### 4.3 The general lesson

Under `o_min < L - 1`, the §6.2 feasible set is **not** the window-spectrum
set: an observed window may be skipped using a shorter overlap. A
non-contiguous circulation can therefore often be *padded* with unobserved
windows into a single spelled molecule with the same observable throughput. The
witness of §2 is built so that padding is impossible while the unpadded
circulation still beats the truth: at `o_min = 2` every improving spelled
molecule is ruled out by §3, and at `o_min = 1` padded spellings do beat the
truth.

---

## 5. Relation to existing repository results

| Statement | Location | Status after this note |
|---|---|---|
| KKT characterization and infinite spelled bridging-insufficiency family | `docs/section62-kkt-and-bridging-family.md` (branch `analysis/issue36-se62-source-semantics-verify-0920`) | unchanged; the family's competitor is a spelled molecule, so it refutes the bridging-to-optimality implication independently of non-spellability |
| §6.2 candidates are flows (non-contiguous assemblies), lower bound `1` per read vertex | `docs/source-notes/mb09-section62-source-semantics-verification.md` | used here |
| Sequence-level criterion = support containment + `(L-o_min)`-density | branch `analysis/se62-independent-reconstruction` | adopted as the traceability test |
| Repository has no source-faithful bidirected model; counterexamples are directed sub-cases | branch `analysis/se62-bidirected-flow-fidelity-audit-0920` | this note supplies the missing orientation-resolved model and a genuine non-spellable witness in it |
| Per-occurrence string-graph search found no beating **non-spellable** flow (`G <= 7`, `L = 3`, single strand) | branch `analysis/issue36-nonspellable-flow` | consistent, but that zero is a single-strand/`L=3` artifact; the witness here is `L = 4`, orientation-resolved |
| Folded-graph non-spellable beats `W1/W2/W2MIN` | branch `agent/issue36-literal-flow-search-0920` | refuted as non-spellable witnesses for the reasons of §4 |

[source fact / mathematical proof / verified computation as marked in each row]

---

## 6. Epistemic status

| Claim | Status |
|---|---|
| §6.2 graph is the transitively reduced bidirected read-overlap graph; lower bound `1`; objective §6.1 binomial with external `N`; output may be non-contiguous | source fact (PMC3154397 §6.1–6.2) |
| Orientation-resolved rendering (strand nodes, self-loop = 2-cycle) is the faithful reading | modeling decision, forced by §3.1/§3.3/§3.4 |
| `S=001011`: `I_s` holds with non-vacuous triple and interleaved conjuncts | verified computation |
| `d_S` and `d = x` are admissible §6.2 flows at `o_min = 2` on the reduced graph | verified computation + explicit circulation certificate |
| `L_{6.1}(d)/L_{6.1}(d_S) = 2278125/1048576 > 1` | mathematical proof + verified computation |
| No circular molecule beats `d_S` for this instance (complete finite proof) | mathematical proof + verified computation (§3) |
| `W1`, `W2MIN` die under transitive reduction / at `o_min = 2` | verified computation |
| `W2` is observably spellable (`D = 0001100011`) | verified computation |
| Which MB09 layer / strand convention / tie semantics the 2016 sentence intends | **open** (source ambiguity) |
| Whether a non-spellable improvement exists for every `G` / large alphabets / per-occurrence lower bound | **open** |

---

## 7. Reproduce

```sh
python3 scripts/verify_bidirected_nonspellable_counterexample.py
```

The script is self-contained (standard library only), uses exact
`fractions.Fraction` arithmetic throughout, prints a PASS/FAIL line per claim
including the explicit circulation, and exits non-zero on any failure.

---

## 8. Open questions

1. **Generalize the witness.** The instance sits at `o_min = L - 2` and `G = 6`.
   Is there a proved infinite family of non-spellable beating flows, analogous
   to the KKT spelled family? What is the smallest alphabet/`G`?
2. **Characterize spellability.** When is a §6.2 circulation realizable (up to
   throughput) by a single traceable molecule? The witness shows the classes
   differ; a clean criterion would sharpen the positive side (KKT note §8).
3. **Per-occurrence reading.** The witness is vacuous under `d_w >= x_w`
   (`d_S(0110) = 2 < x(0110) = 3`). Is the per-occurrence statement true, or is
   there a non-spellable witness there too?
4. **Kernel-check the flow certificate.** The finite arithmetic of §2 is
   Lean-checkable; the flow-feasibility and non-spellability quantifiers over
   molecules of length at most `14` are decidable finite statements.

---

## 9. Sources

1. P. Medvedev, M. Brudno. *Maximum Likelihood Genome Assembly.* J. Comput.
   Biol. 16(8):1101–1116, 2009. DOI
   [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047);
   [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
2. I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse. *Information-optimal
   genome assembly via sparse read-overlap graphs.* Bioinformatics 32(17):
   i494–i502, 2016. DOI
   [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
3. E. W. Myers. *The fragment assembly string graph.* Bioinformatics
   21(Suppl. 2):ii79–ii85, 2005.
