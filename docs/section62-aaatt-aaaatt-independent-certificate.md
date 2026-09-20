# Independent §6.2 certificate for the `AAATT → AAAATT` witness: feasible, `9/8`, with a named scope blocker

_Status: independent primary-source reconstruction + exact finite computation,
2026-09-20. Written from the Medvedev–Brudno (2009) primary text and built up
from the §3.1–3.4, §5.2, §6.1–6.2 definitions; it does not import or reproduce
any other repository predicate or script. All claims are labelled **source
fact**, **mathematical proof**, **verified computation**, **modeling/source
dependency**, or **open**._

_Reproduction:_ `python3 scripts/verify_se62_aaatt_aaaatt_certificate.py`
(exact integers / `fractions.Fraction`, deterministic, exits non-zero on any
failed assertion).

---

## 0. Verdict at a glance

Under the MB09 molecule reading — reads are reverse-complement classes; edges
are all bidirected overlaps of length `≥ o_min`; transitive reduction removes an
overlap spelled by two proper overlaps; every read vertex has lower bound `1`,
edge lower bounds `0`, upper bounds `∞` — the `AAATT → AAAATT` witness is
**confirmed, not falsified**:

| item | result |
|---|---|
| truth `S = AAATT` induces a closed §6.2 circuit | **yes** |
| competitor `D = AAAATT` induces a closed §6.2 circuit | **yes** |
| induced throughputs | `d_S = {AAA:1, AAT:2, TAA:2}`, `d_D = {AAA:2, AAT:2, TAA:2}` |
| §6.1 ratio with `N=5`, `n=3`, `x={AAA:1,AAT:1,TAA:1}` | `L(D)/L(S) = 9/8 > 1` |
| survives `o_min ∈ {1,2}` | **yes** |
| PR #39 prose spectrum `(2,2,1)`/"`d_S={AAA:2,AAT:2,TAA:1}`" | **wrong** |
| the witness's scope | **revcomp-molecule classes only** (see §6) |

No falsifier was found inside the source-faithful reading. The one genuine
dependency is recorded in §6: under MB09's *literal* §6.1 "`4^k` oriented
`k`-mers" reading, the truth's window set is not contained in the observed
oriented support, so the witness does not exist. This is a scope blocker, not a
refutation of the molecule-class claim.

[mathematical proof + verified computation]

---

## 1. Source facts used

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/) (body text
retrieved 2026-09-20).

- **§3.1** "A DNA molecule is an unordered pair of strings … that are reverse
  complements of each other"; a `k`-molecule is represented **once** (see also
  §4.1, "each `k`-molecule is represented only once"). On `{A,T}` the involution
  is `A ↔ T`. [source fact]
- **§3.2** A bidirected edge carries a positive/negative incidence at each
  endpoint; a link has `I(x,e) ∈ {+1,−1}`; a loop has `I(x,e) ∈ {+2,−2,0}`. A
  walk requires `e_{i−1}` and `e_i` to have **opposite** orientations at every
  interior vertex. [source fact]
- **§3.3** `e` is a bidirected overlap in exactly one of four strand cases:
  `(p,p) ⇒ (+x,−y)`, `(p,n) ⇒ (+x,+y)`, `(n,p) ⇒ (−x,−y)`,
  `(n,n) ⇒ (−x,+y)`; "the length of this bidirected overlap is the length of the
  underlying string overlap." [source fact]
- **§3.4** A flow satisfies `l(e) ≤ f(e) ≤ u(e)` and
  `Σ_e I(v,e) f(e) = b(v)` at every vertex. [source fact]
- **§5.2** Splitting `v → v⁻ → v⁺` turns a vertex bound/cost into an edge
  bound/cost; the split-edge flow is the read's copy count. [source fact]
- **§6.1** Objective (binomial approximation, external known `N`):
  `∏_w (d_w/N)^{x_w} (1 − d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`. [source fact]
- **§6.2** "The vertices of this graph are the reads, and the edges are all
  possible bidirected overlaps of length at least `o_min` … We then perform
  transitive edge reduction, where we remove any overlap that is spelled by two
  shorter overlaps. This procedure is identical to the one described in Myers
  (2005)." "Each vertex has a lower bound of 1 … All other lower bounds are 0
  and all upper bounds are infinity"; supersource/sink edges carry prohibitive
  cost; the original genome is a **circuit**. [source fact]
- **Observation 7.** The number of times a walk `W` visits `r` equals the number
  of times `r` appears as a submolecule of the molecule spelled by `W`.
  [source fact]

The Myers reading of "spelled by two shorter overlaps" (two **proper**
overlaps, composing as `l = l₁ + l₂ − L` with `l₁,l₂ > l`) is the one named by
the source; for `L = 3` only length-`1` overlaps can be removed. [source fact +
mathematical proof]

---

## 2. Model reconstruction (all from the definitions above)

- **Reverse-complement molecule classes.** Vertices are classes
  `mol(w) = min(w, rc(w))` with `A↔T`. Positive strand = canonical
  representative; negative strand = its reverse complement.
- **Overlap edge rule.** For each ordered molecule pair `(x,y)` (including
  `x=y`) and each length `l ∈ [o_min, L−1]`, add a bidirected edge for every
  strand case `(sx,sy)` with `suffix_l(strand_sx(x)) = prefix_l(strand_sy(y))`,
  carrying incidences per the §3.3 table. The graph is a multigraph and loops
  are permitted (§3.2).
- **Transitive reduction (Myers).** Remove edge `e` iff some observed molecule
  `z` supplies a two-step path `x → z → y` with proper sub-overlap lengths
  `l₁,l₂ < L`, interior incidences opposing, boundary incidences equal to `e`'s,
  and `l = l₁ + l₂ − L`.
- **Flow.** A closed integral circulation on the reduced graph; vertex
  throughput `d_m =` split-edge flow; `l(vertex)=1`, `l(edge)=0`, `u=∞`; no
  supersource/sink usage.
- **Observation 7** ties `d_m` to the occurrence count of molecule `m` in the
  spelled molecule.

The implementation is `scripts/verify_se62_aaatt_aaaatt_certificate.py`
(`build_graph`, `transitive_reduction`, `certify_walk`).

---

## 3. Instance and induced sequence

Alphabet `{A,T}`, read length `L = 3`, external `N = 5`. Truth
`S = AAATT`, observed starts `(0,1,4)`, so `n = 3`; competitor `D = AAAATT`.

Cyclic length-3 windows and molecule classes:

```text
S = AAATT :  AAA(0) AAT(1) ATT(2) TTA(3) TAA(4)
             AAA     AAT     AAT     TAA     TAA
D = AAAATT:  AAA AAA AAT ATT TTA TAA
             AAA AAA AAT AAT TAA TAA
```

The walks were reconstructed from their window visits alone (append the new
last character of each successive window). The spelled strings are
`AAATTAA` (reduction `AAATT`) and `AAAATTAA` (reduction `AAAATT`), confirming
the induced circular sequences. [verified computation]

Observed read multiset from starts `(0,1,4)`:
`x = {AAA:1, AAT:1, TAA:1}`. Both `d_S ≥ x` (per-occurrence) and the §6.2
per-vertex lower bound `d ≥ 1` hold. [verified computation]

---

## 4. Graph, reduction, and the two circuits

| threshold | raw §3.3 edges | removed by Myers | surviving |
|---|---|---|---|
| `o_min = 2` | 10 | 0 | 10 |
| `o_min = 1` | 28 | 16 (all length 1) | 12 |

At `o_min = 1` the only surviving length-1 edges are the two directions of the
`AAT — TAA` link (spelled 5-mers `AATAA`/`TTATT`, middle windows `ATA`/`TAT`,
which are unobserved molecule classes); every other length-1 edge is removed.
Length-2 edges are never removable for `L = 3` because
`l ≤ (L−1)+(L−1)−L = L−2 = 1`. [mathematical proof + verified computation]

**Truth circuit** (visits `AAA, AAT, AAT, TAA, TAA`):

```text
AAA --(p,p)-> AAT --(p,n)-> AAT --(n,n)-> TAA --(n,p)-> TAA --(p,p)-> AAA
inc   (+,-)        (+,+) loop     (-,+)         (-,-) loop       (+,-)
```

Interior visits have opposite arriving/departing incidences (e.g. at the first
`AAT`: arrive `−1`, depart `+1`). The two same-vertex steps are genuine §3.2
loops with `I = +2` (at `AAT`) and `I = −2` (at `TAA`). Balance
`Σ I(v,e) f(e) = 0` holds at every vertex; `AAA` is visited once, `AAT` and
`TAA` twice, so `d_S = {AAA:1, AAT:2, TAA:2}`.

**Competitor circuit** (visits `AAA, AAA, AAT, AAT, TAA, TAA`):

```text
AAA --(p,p)-> AAA --(p,p)-> AAT --(p,n)-> AAT --(n,n)-> TAA --(n,p)-> TAA --(p,p)-> AAA
```

with the extra `AAA` step being the incidence-`0` `AAA` loop; balance holds and
`d_D = {AAA:2, AAT:2, TAA:2}`.

No edge used by either circuit is removed by the transitive reduction, at
either threshold. [mathematical proof + verified computation]

---

## 5. The `9/8` ratio

Only the `AAA` coordinate changes (`1 → 2`) with `x_AAA = 1`, `n = 3`, `N = 5`:

```text
L(D)/L(S) = [(2/5)(3/5)^2] / [(1/5)(4/5)^2] = 18/16 = 9/8 > 1.
```

[mathematical proof + verified computation]

---

## 6. Falsification attempts, and the one real scope blocker

Checks run adversarially before accepting the claim:

1. **Orientation / walk condition.** Each transition is a real §3.3 edge with
   the stated strand case, and incidences oppose at every interior visit. Passes.
2. **Loops.** The `AAT`/`TAA` self-transitions are `±2` loops, not degenerate
   links; balance still closes. Passes.
3. **Reduction interference.** No used edge is reducible. Passes at both
   `o_min`.
4. **Lower bound.** Per-vertex `1` holds; the stronger per-occurrence
   `d_w ≥ x_w` also holds, so the witness is robust to that convention. Passes.
5. **Prose spectrum.** The PR #39 prose `(2,2,1)` / `{AAA:2,AAT:2,TAA:1}` is not
   produced by either molecule; the occurrences are `(1,2,2)` and `(2,2,2)`.
   Rejected as prose error.
6. **Scope blocker (not a falsifier inside the molecule reading).** Under
   MB09's literal §6.1 index set "there are `4^k` such variables" — i.e.
   *oriented* `k`-mers rather than revcomp classes — the truth's oriented window
   set `{AAA, AAT, ATT, TTA, TAA}` is **not** contained in the observed oriented
   support `{AAA, AAT, TAA}`: `ATT` and `TTA` are unobserved. The witness
   therefore exists only under the §3.1/§4.1 molecule-class reading, which is
   itself in tension with §6.1's `4^k` count. This is a **modeling/source
   dependency**, consistent with the repository's recorded read-type ambiguity.

[verified computation + modeling/source dependency]

---

## 7. Relation to existing artifacts

- The unmerged reconstruction `docs/section62-aaatt-bidirected-reconstruction.md`
  (branch `analysis/issue36-se62-aaatt-bidirected-reconstruction-0920`) and the
  audit `docs/source-notes/mb09-se62-definitions-independent-audit.md` (branch
  `agent/mb09-se62-definitions-audit-0920`) reach the same graph and spectra by
  separate implementations; this note is a third, independent reconstruction and
  agrees.
- The correction `d_S = (1,2,2)` (not `(2,2,1)`) also follows from the
  conservation lemma `d_AAT = d_TAA` in
  [`section62-aaatt-reduced-flow-cone-and-spectra.md`](section62-aaatt-reduced-flow-cone-and-spectra.md),
  which this certificate reproduces at the walk level: the truth's `AAT` and
  `TAA` counts are each `2`.
- The `FeasibleType` Lean predicate is not used here; the check is at the actual
  bidirected graph/flow level.
- This concerns the `AAATT → AAAATT` (spellable competitor) witness. The
  different, current-frontier non-spellable arbitrary-flow witness on this
  branch (`d* = (3,1,1)` for starts `(0,0,1,4)`) is a separate §6.2 object and
  is not certified by this note.

---

## 8. Epistemic summary

| claim | status |
|---|---|
| §3.1–3.4, §5.2, §6.1–6.2 definitions as used | **source fact** |
| `AAATT` and `AAAATT` are valid closed §6.2 circuits with `d_S=(1,2,2)`, `d_D=(2,2,2)` | **mathematical proof + verified computation** |
| transitive reduction removes none of the used edges at `o_min ∈ {1,2}` | **mathematical proof + verified computation** |
| `L(D)/L(S) = 9/8` | **mathematical proof + verified computation** |
| PR #39 prose `(2,2,1)` | **rejected** |
| witness requires revcomp molecule classes (fails under literal oriented `4^k`) | **modeling/source dependency** |
| global optimality / unbounded families | **open** (unchanged) |

Sources: Medvedev & Brudno (2009), *J. Comput. Biol.* 16(8) 1101–1116,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/); Myers (2005),
*The fragment assembly string graph*, *Bioinformatics* 21(Suppl 2) ii79–ii85.
