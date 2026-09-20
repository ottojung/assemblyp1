# Exact §6.1 optimum for the smallest non-vacuous §6.2 bridging witness, and how it reconciles with the parallel minimality work

_Status: independent reconstruction + derivation + exact computation, 2026-09-20,
for issue #36. This note reproduces the smallest **non-vacuous** source-faithful
witness and closes the optimality question for it with an exact global argument
rather than a bounded search. It was written before reading the parallel
`analysis/issue36-se62-minimality-audit-0920` branch (`157cd88`) and the
`8b22bdb` cycle-obstruction note; §5 reconciles the three._

_Reproduction:_ `python3 scripts/verify_se62_smallest_flow_witness.py`
(self-contained, exact `fractions.Fraction`/integer arithmetic, deterministic,
~4 s, exits non-zero on any failed assertion).

_Every claim below is labelled **source fact**, **derivation**, **computation**,
**open**, or **reconciliation**. The note decides only the §6.2-restricted flow
question; it does not decide which MB09 layer the 2016 Shomorony sentence
denotes (see
[`source-notes/se62-feasibility-necessity-determination.md`](source-notes/se62-feasibility-necessity-determination.md))._

---

## 0. Result at a glance

Fix the Medvedev–Brudno §6.2 object as reconstructed in §1. Then:

1. **A bridging, flow-feasible truth is beaten by another admissible flow.**
   The smallest witness with **non-vacuous** bridging is at `G = 4`:

   ```text
   truth      S = AAAT (0001),  G = 4,  L = 3,  N = 4,  o_min in {1, 2}
   reads      starts (0,0,1,2,3)            (one start repeated; n = 5 > G)
   observed   x = { AAA:2, AAT:1, ATA:1, TAA:1 },  n = 5
   truth flow d_S = { AAA:1, AAT:1, ATA:1, TAA:1 }   (admissible)
   competitor d*  = { AAA:2, AAT:1, ATA:1, TAA:1 }   (admissible)
   spelled by D   = TAAAA (10000)
   ratio      L(d*)/L(d_S) = 32/27 > 1
   ```

   [computation; the witness is also checked at `o_min = 1` and `2`]

2. **The determination is complete, not a bounded search.** For this
   `(N, n, x) = (4, 5, (2,1,1,1))`, the objective
   `∏_w (d_w/N)^{x_w}(1 − d_w/N)^{n−x_w}` is **componentwise** maximised on
   `[1, N]` at exactly `d* = (2,1,1,1)`, and `d*` is feasible (realised by the
   spelled molecule `TAAAA`). Hence **no admissible flow whatsoever** can beat
   `d*`, at any `o_min` and for any feasible set. This is the specialisation to
   `S = AAAT` of the separability/cycle framework of `8b22bdb`
   ([`se62-ml-cycle-obstruction.md`](se62-ml-cycle-obstruction.md)). [derivation]

3. **Smallest is `G = 4` (with `n > G`), among non-vacuous witnesses.** `G = 3`
   at `L = 3` has no witness (proved, §4); `G = 4` at `L = 3` has none with
   distinct starts (`n ≤ G`). The first witnesses appear at `n = 5` and `n = 6`
   for the single molecule class `{AAAT, ATTT}`. [derivation + computation]

4. **Context.** If the free choice `L = 2` is admitted, even smaller
   **coverage-only** witnesses exist (`G = 3`, `S = AAT`, ratio `2`, and
   `G = 4`, `L = 2`, `S = AATT`, ratio `9/8`); these are vacuous for bridging
   and were recorded independently in the parallel minimality audit. The
   `G = 5` `AAATT` (ratio `9/8`) and `AATAT` (ratio `243/128`) witnesses are not
   smallest but are valid. [reconciliation, §5]

---

## 1. The source object

**Source facts** (Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §3.3–3.4, §5.2,
§6.1–6.2, [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/)):

- **§3.1 molecules.** A read is a DNA molecule, an unordered reverse-complement
  pair; on `{A,T}` the involution is `A ↔ T`. A vertex is a molecule class.
- **§3.3 bidirected overlaps.** A bidirected edge joins the reads with a
  positive/negative incidence at each end, and its length is the underlying
  string-overlap length.
- **§3.4 flow.** At every vertex, positive-incident flow minus negative-incident
  flow equals the vertex balance `b(v)`.
- **§6.2 graph.** Vertices are the reads; edges are *all* bidirected overlaps of
  length at least `o_min`; the graph is transitively reduced as in Myers (2005).
- **§6.2 bounds.** Every read vertex has lower bound `1`; all other lower bounds
  are `0`; all upper bounds are `∞`; supersource/supersink edges carry a
  prohibitive cost; “our flow represents a (non-contiguous) assembly”.
- **§6.1 objective.** The separable binomial with the **external** true genome
  length `N = |S|`:
  `L(d) = ∏_w (d_w/N)^{x_w}(1 − d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`.
- **Observation 7.** The flow through a read vertex equals the number of times
  the read appears as a submolecule of the spelled molecule; a spelled molecule
  therefore induces an admissible flow.

**Bridging `I_s`** (Shomorony, Kim, Courtade & Tse, *Bioinformatics* 32(17)
(2016) i494–i502, Eq. (1), after Bresler, Bresler & Tse (2013)): coverage,
every maximal triple repeat all-bridged, every maximal interleaved repeat pair
bridged; strict copy-bridging `read [r, r+L) bridges copy [t, t+ℓ)` iff
`r < t` and `t + ℓ < r + L` (repository normalization,
[`bridging-source-semantics.md`](bridging-source-semantics.md)).

**Modeling choices** (kept explicit):

- **Folded bidirected relation.** Two molecule classes are joined when *some*
  orientation of one overlaps *some* orientation of the other; the graph keeps
  both incidence directions. Since §6.2 is explicitly on DNA molecules, this is
  the closer reading than fixing one canonical representative per molecule.
  (The edge and reduction conventions are pinned independently in `bd50067`,
  [`source-notes/se62-edge-and-transitive-reduction-rules.md`](source-notes/se62-edge-and-transitive-reduction-rules.md).)
- **Reduction.** At `o_min = L−1 = 2` no length-2 edge can be transitive over
  `L = 3`, so the reduction is vacuous and the determination is independent of
  the Myers-vs-literal reduction convention. At `o_min = 1` the witness is
  verified directly there as well (its edges have length `2`).
- **Candidate class.** Integral flows with balance `0` (closed flows, i.e. the
  circuit/genome object). Source/sink flows are permitted by the source but
  carry its prohibitive cost; the witness and its competitor are both **single
  circuits**, so no source/sink cost is incurred and the comparison is direct.

---

## 2. Exact feasible-flow object and its completeness

For a fixed read graph and observed `x`, the script enumerates **all** integral
circulations `f ≥ 0` with balance `0` at every read vertex, vertex throughput
`d_w ∈ [1, N]`, and support exactly `x`. Completeness rests on two bounds
[derivation]:

- `f_e ≤ N`: each bidirected edge has an incidence at some vertex, and that
  vertex's throughput `d_w` is at least `f_e` (a loop contributes `2f_e`);
- `Σ_e f_e ≤ V·N`: each bidirected edge has exactly two incidences and
  `pos(v) = neg(v) = d_w(v)` under balance `0`, so
  `Σ_v 2 d_w(v) = Σ_e 2 f_e`.

The DFS is pruned by the reachable balance interval, so the enumeration is
exact. A truth `S` is declared **flow-feasible** only when its window spectrum
`d_S` is among the enumerated flows.

---

## 3. The smallest non-vacuous witness, checked end to end

Let `S = 0001` (`AAAT`), `G = N = 4`, `L = 3`, `o_min ∈ {1,2}`, and sample the
five reads at starts `(0,0,1,2,3)` (independently, uniformly, **with
replacement**, as in the source model). Then:

```text
windows of S (cyclic) : 000, 001, 010, 100
x                     : 000×2, 001×1, 010×1, 100×1
d_S                   : 000,001,010,100 each once        (admissible circuit)
```

**`I_s` holds, non-vacuously (strict predicate).** [computation]
Coverage is immediate. `S` has exactly one maximal triple repeat, the run of
`0` at copies `{0,1,2}` (left flanks `1,0,0`, right flanks `0,0,1`). It is
all-bridged by the reads at starts `3` (bridges copy `0` on the lift),
`0` (bridges copy `1`) and `1` (bridges copy `2`). There is no interleaved
repeat pair, so the interleaving conjunct is vacuous.

**The competitor is an admissible flow and a spelled molecule.**
`D = TAAAA = 10000` has cyclic windows `100, 000, 000, 001, 010`, i.e.
`d_D = {000:2, 001:1, 010:1, 100:1} = d*`. Every window is an observed read
type and consecutive overlaps have length `2 ≥ o_min`, so by Observation 7
`d*` is admissible. [computation]

**It strictly wins.** Only the `000` coordinate changes:

```text
(d*_000/4)^2 (1 − d*_000/4)^3      (2/4)^2 (2/4)^3
──────────────────────────────  =  ───────────────── = 32/27 > 1.
(d_S_000/4)^2 (1 − d_S_000/4)^3    (1/4)^2 (3/4)^3
```

[computation]

**No flow can do better (complete).** The real target for the `000` coordinate
is `N x_000/n = 8/5`, so the integer maximiser on `[1,4]` is `2`; for the other
three coordinates the target is `4/5 < 1`, so the integer maximiser is `1`.
Hence `d* = (2,1,1,1)` componentwise maximises every factor — and therefore
the product — over `[1,N]^V`, and it is feasible. So `d*` is the exact global
§6.1 optimum over all admissible flows. This is the `8b22bdb` separability
argument instantiated at `S = AAAT`; the one-step `d*_w = N x_w/n` criterion is
the same primitive. [derivation]

The exhaustive run confirms this and also finds the analogous `n = 6` witness
(`ratio 64/27`) and the mirror class `{ATTT}`.

---

## 4. Minimality within `L = 3`

**`G = 3`, `L = 3` has no witness (proof).** [derivation] The binary length-3
molecule classes are `{AAA}`, `{AAT, ATT}`, `{TTT}`. For the homopolymer classes
the only observed type is the truth type and the likelihood is maximised at the
truth. For `S = AAT` the window spectrum is `(AAT, ATA, TAA) = (1,1,1)` with
`N = 3`; the feasible flows are `(1,1,1)`, `(2,2,2)`, `(3,3,3)`, `(1,3,1)`,
`(3,1,3)`. On any sample observing all three types, `(3,·,·)` forms have zero
likelihood, and the ratio of `(2,2,2)` to `(1,1,1)` is
`∏_w 2^{2x_w − n} = 2^{−n} < 1`. So no flow beats the truth. The script also
checks every start multiset with `n ≤ 8` exhaustively.

**`G = 4`, `L = 3`, distinct starts: no witness.** Exhaustive over all rotation
classes, all `n ≤ G`, and all distinct start sets. [computation]

**`G = 4`, `L = 3`, `n > G`: witnesses, first at `n = 5`.** Exhaustive over all
start multisets with `n ≤ G + 2`. [computation]

Therefore the smallest non-vacuous §6.2 witness is `G = 4`, and it requires
sampling **with replacement** (`n > G`).

---

## 5. Reconciliation with prior and parallel artifacts

| Artifact | Relation |
|---|---|
| [`independent-se62-bidirected-model.md`](independent-se62-bidirected-model.md) (this branch) | Its bounded neighbourhood search restricted to **distinct** starts (`n ≤ 4`), so it reported `G = 5`. This note **extends** it: allowing repeated starts lowers the smallest non-vacuous witness to `G = 4`; the `AAATT`/`AATAT` witnesses and `9/8`/`243/128` ratios are reproduced. |
| `157cd88` (`analysis/issue36-se62-minimality-audit-0920:docs/source-notes/issue36-se62-minimality-audit-2026-09-20.md`) | **Independent, parallel confirmation.** Its "Witness C" is exactly the `G = 4`, `L = 3`, `S = AAAT`, `n = 5`, ratio `32/27` instance found here (its competitor spelling `AAAAT` is a rotation of `TAAAA`). It additionally records the smaller **coverage-only** `L = 2` witnesses A (`G = 4`, ratio `9/8`) and B (`G = 3`, ratio `2`). Its own scope statement calls its minimality table bounded evidence; the componentwise argument in §3 above closes the optimality of Witness C exactly, so `8b22bdb`'s cycle primitive rather than a search decides it. |
| `8b22bdb` ([`se62-ml-cycle-obstruction.md`](se62-ml-cycle-obstruction.md)) | Supplies the general separability/elementary-cycle framework and the one-step criterion. The present note is a worked instance (the smallest non-vacuous one) of that framework. |
| `8028c27` ([`section62-arbitrary-flow-witness-and-search.md`](section62-arbitrary-flow-witness-and-search.md)) | Bounded search for arbitrary (possibly non-spellable) flows; reports only two non-spellable optima in scope, both needing a repeated read at `o_min = 1`. Consistent with §6 below. |
| unmerged `analysis/issue36-nonspellable-*` branches | Their non-spellable `AATAT` flow `(AAT:1, ATA:2, TAA:1)` is **infeasible** on the maximal-overlap (`o_min = 2`) transitively reduced graph (checked in the script), and the best flow for `AATAT` there is the spellable `(2,2,2)` at `243/128`. So the "smallest non-spellable" claim is a modeling-convention statement, not one at `o_min = L−1`; it does not lower the smallest source-faithful witness. |
| `bd50067`, `400f6b4`, `f1f44ec` | Independent pins of the edge/reduction rules, the source bridging reconstruction, and the integrated-`AAATT` audit; their graphs agree with the one used here. |

**Convention note.** The unmerged non-spellable branch's own table already
records `representative-reduced, o_min = 2` as having zero non-spellable beats;
this note is consistent with that row and isolates the `o_min`/reduction
convention as the entire source of the difference.

---

## 6. What this does and does not settle

**Does.** It exhibits a source-faithful, non-vacuously bridging, flow-feasible
truth (`AAAT`) whose admissible §6.2 flow is beaten by another admissible flow,
with an exact global-optimum argument (not a bounded search), and pins the
smallest such witness at `G = 4` (requiring `n > G`) within `L = 3`.

**Does not.** It does not decide which MB09 layer the 2016 Shomorony sentence
denotes, the tie semantics, the single-strand reading, or the sequence-level
question. It does not claim novelty of Witness C (independently found in
`157cd88`) or of the separability framework (`8b22bdb`). The result is a
flow/assembly-level statement, exactly the object §6.2 optimises.

---

## 7. Epistemic status

| Claim | Class |
|---|---|
| §6.2 vertices/edges/lower bounds, Myers reduction, §6.1 external-`N` binomial, Observation 7 | **source fact** |
| Strict bridging predicate `r < t ∧ t+ℓ < r+L` | **modeling normalization** |
| Exact feasible-flow enumeration is complete (`f_e ≤ N`, `Σf_e ≤ VN`) | **derivation** |
| `S = AAAT`, `o_min ∈ {1,2}`, starts `(0,0,1,2,3)` is a witness with ratio `32/27` | **computation** (`Fraction`) |
| `d* = (2,1,1,1)` is the global §6.1 optimum over all admissible flows for that instance | **derivation** (specialisation of `8b22bdb`) |
| `G = 3` at `L = 3` has no witness; `G = 4` at `L = 3` needs `n > G` | **derivation + computation** |
| Unmerged non-spellable `(1,2,1)` for `AATAT` is infeasible at `o_min = 2` | **computation** |
| Which 2016 referent, tie semantics, sequence-level question | **open** |

---

## 8. Reproduce

```sh
python3 scripts/verify_se62_smallest_flow_witness.py
```

The script reconstructs the bidirected graph, verifies `I_s`, enumerates the
exact circulation polytope, checks the `G = 3` proof facts, the `G = 4` witness
at both `o_min` values, the `G = 5` witnesses, the minimality scope, and the
non-spellable reconciliation, then exits zero.

Primary sources: Medvedev & Brudno (2009), *J. Comput. Biol.* 16(8) 1101–1116,
§3.1, §3.3–3.4, §5.2, §6.1–6.2, PMC3154397; Myers, *The fragment assembly
string graph*, *Bioinformatics* 21(Suppl 2) (2005) ii79–ii85; Shomorony, Kim,
Courtade & Tse (2016), *Bioinformatics* 32(17) i494–i502, Eq. (1); Bresler,
Bresler & Tse (2013), *BMC Bioinformatics* 14(Suppl 5):S18.
