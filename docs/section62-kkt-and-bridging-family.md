# KKT structure of the §6.2 fixed-`N` binomial objective on its actual flow polytope, and an infinite bridging-insufficiency family

_Status: independent mathematical analysis with proofs + exact-rational
verification, 2026-09-20. Not a Lean result. All claims are classified as
**source fact**, **mathematical proof**, **verified computation**, or **open**.
This note was produced independently of the concurrent §6.2 search packets; it
does not summarize them._

_Reproduction: `python3 scripts/se62_kkt_family_independent.py`
(self-contained, no third-party packages, exact `fractions.Fraction`,
deterministic, under a minute). It exits non-zero on any failed assertion._

_Scope. This note fixes the object as the actual Medvedev–Brudno §6.2
optimisation: an integer flow (possibly a non-contiguous assembly) on the
read-overlap graph, scored by the literal §6.1 separable binomial with the
external genome length `N`. It asks when a truth-induced feasible flow is a
global optimum, and whether the bridging hypothesis `I_s` can force this. It
does not decide which Medvedev–Brudno layer the 2016 sentence intends._

---

## 0. Results at a glance

1. **The §6.2 objective is a sum of Bernoulli I-divergences.** On the observed
   read-molecule vertices,
   `log P(d) = const − n · Σ_w KL(q_w ‖ p_w)`, with `q_w = x_w/n` and
   `p_w = d_w/N`. Maximising §6.2 is therefore an I-projection of the observed
   frequency vector `q` onto the normalized flow polytope. [mathematical proof,
   §2]

2. **Exact optimality characterization (Theorem 1).** A truth-induced feasible
   flow `d_S` is a global optimum iff no feasible displacement `v = d − d_S`
   (`d ∈ F`) has `Σ_w h_w v_w > 0`, where
   `h_w = (N x_w − n d_S,w) / (d_S,w (N − d_S,w))` is the derivative of the
   log-objective at `d_S`. This is the KKT condition of the (separable, concave)
   objective over the (integer) flow set; it is exact, not a relaxation.
   [mathematical proof, §4]

3. **The §6.2 flow set is the integer cycle cone of the overlap graph,** so it
   is closed under adding directed-cycle incidence vectors; a single directed
   cycle `C` with `Σ_{w∈C} h_w > 0` defeats the truth (Theorem 2), and so does
   the decrement of an over-observed vertex that stays feasible (Corollary 1).
   [mathematical proof, §5]

4. **Bridging does not force optimality — infinite family (Theorem 3).** For
   every `G ≥ 6`, `L = G − 2`,
   ```
   truth       S = 0^(G-1) 1        (length G, a single circular molecule)
   competitor  D = 0^(G-2) 1        (length G-1, spelled and read-tiled)
   reads       the G-1 windows of D, placed in S, one per type
   N = G, single strand, every o_min in [1, L-1]
   ```
   satisfies `I_s`, has both `S` and `D` as admissible §6.2 flows (per-occurrence
   and per-type), and the competitor strictly improves the literal fixed-`N`
   binomial by the closed form
   ```
   P(D)/P(S) = (1/2) · ((G-1)/(G-2))^(G-2) ∈ (1, e/2],
   ```
   with `P(D)/P(S) > 1` for every `G ≥ 4` (the ratio bound holds for all
   `G ≥ 4`; `I_s` is proved for `G ≥ 6`). [mathematical proof, §6–§7]

5. **Consequence for the published question.** Since `I_s` holds in the family
   and the winning competitor is a *spelled molecule* (not merely a non-spellable
   flow), bridging cannot force §6.2 optimality even under the most favourable
   reading of the competitor class. The mechanism is transparent: the objective
   target is `d*_w = N x_w / n`, `I_s` constrains only the *support/repeat*
   structure, and a repeat makes `d_S,w` exceed `d*_w`. [mathematical proof +
   verified computation, §7–§8]

---

## 1. The §6.2 object (source facts)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397.
Quotations used below are those already transcribed in
`docs/section62-bidirected-flow-feasibility.md` §1 and
`docs/section62-actual-flow-feasibility.md` §1:

- Vertices are the observed reads (DNA molecules); edges are bidirected overlaps
  of length `≥ o_min`; every read vertex has lower bound `1`; all upper bounds
  are infinite.
- The objective at a vertex is the §6.1 separable binomial cost
  `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)` with the external known
  genome length `N`; the domain is `0 ≤ d_i ≤ N`.
- "Since any flow can be decomposed into a collection of walks, our flow
  represents a (non-contiguous) assembly of the genome."

**Model fixed in this note.** Single-strand reading (reverse complements not
identified); vertices are the observed read *types* `O = supp(x)`; the candidate
object is an integer circulation of the overlap graph on `O` (self-loops
allowed), classified by its vertex-throughput vector `d ∈ Z_{≥0}^{O}`; the
lower bound is `d_w ≥ 1` (per-type) and, where stated, `d_w ≥ x_w`
(per-occurrence). The objective is the literal §6.1 product of per-type
binomials. Under the bidirected reading the graph only gains edges, so every
feasible flow below remains feasible; the family is therefore reading-robust.

---

## 2. The objective is a sum of Bernoulli I-divergences

Let `n = Σ_w x_w` and extend `x_w = 0` for vertices with no observation. The
literal §6.1 log-objective is

```text
log P(d) = Σ_w [ x_w log(d_w/N) + (n − x_w) log(1 − d_w/N) ] + const,
```

which on the observed vertices is

```text
log P(d) = const − n · Σ_w KL(q_w ‖ p_w),    q_w := x_w/n,   p_w := d_w/N,
```

with the Bernoulli divergence
`KL(q‖p) = q log(q/p) + (1−q) log((1−q)/(1−p))`.
A candidate with `0 < d_w < N` for all observed `w` thus maximises §6.2 exactly
when `p = d/N` is the I-projection of `q = x/n` onto the normalized flow
polytope `P = {d/N : d ∈ F}`. The unconstrained per-coordinate maximiser is
`d*_w = N x_w / n` (for `0 < x_w < n`), with endpoint cases `x_w = 0 ⇒ d_w = 0`
and `x_w = n ⇒ d_w = N`. [mathematical proof; standard Bernoulli calculus]

---

## 3. The feasible flow polytope is a cycle cone

**Lemma 1 (cycle cone).** A nonnegative integer vector `d` on `O` is the
vertex-throughput vector of an integer circulation of a digraph `G` on `O` iff
`d` lies in the integer cone generated by the incidence vectors `1_C` of the
directed cycles `C` of `G` (a self-loop counts as a directed cycle of length 1).
Adding any directed-cycle incidence vector to a feasible throughput vector again
gives a feasible throughput vector.

_Proof._ "Only if": any integral circulation decomposes into directed cycles
with nonnegative integer multiplicities, and the throughput is the sum of the
cycle incidence vectors. "If": a nonnegative integer combination of cycles is
itself an integral circulation. Closure under addition is immediate. ∎

[mathematical proof; standard circulation decomposition]

The overlap graph `G(R)` has a directed edge `u → v` iff the reads
`u, v` have a suffix–prefix overlap of length `≥ o_min` (including `u = v` when
a read self-overlaps). The full §6.2 set is
`F = { d ∈ Z_{≥0}^{O} : d ∈ cycle cone, d_w ≥ 1 }`, optionally intersect
`{d_w ≥ x_w}` and `{d_w ≤ N}`.

---

## 4. Exact KKT characterization of optimality

**Theorem 1 (normal-cone/KKT characterization).** Fix `S`, `x`, `n`, `N`, and
the flow set `F`. Let `d_S ∈ F` be the truth-induced throughput. Define
`h_w := (N x_w − n d_S,w) / (d_S,w (N − d_S,w))` for `0 < d_S,w < N` (endpoint
values understood by the corresponding one-sided derivative). Then

```text
d_S is a global maximiser of log P over F
  ⟺  for every v = d − d_S with d ∈ F:   Σ_w h_w v_w ≤ 0.
```

_Proof._ `log P` is separable and strictly concave on the box `0 < d_w < N`
(each `d ↦ a log d + b log(N−d)` is strictly concave). For any `d ∈ F`, the
segment `d_S + t(d − d_S)`, `t ∈ [0,1]`, stays in the convex box. Concavity gives
`log P(d) ≤ log P(d_S) + ∇log P(d_S)·(d − d_S) = log P(d_S) + Σ_w h_w v_w`.
Hence `Σ_w h_w v_w ≤ 0` for all feasible `d` makes `d_S` optimal; conversely if
some `d` has `Σ_w h_w v_w > 0`, then `log P(d) > log P(d_S)`. ∎

[mathematical proof]

**Remark.** The condition is finite and exact because `F` is a finite set of
integer vectors. It is the *true* KKT condition for the discrete flow problem;
no continuous relaxation or normal-cone approximation is used. (Earlier
repository notes stated a normal-cone condition on the circular-genome Eulerian
polytope; that is a different feasible set, and its normal cone was corrected in
`mathematics/fixed-length-likelihood-duality-and-flow.md` §5. Theorem 1 here is
about the actual §6.2 flow set.)

**Interpretation.** `h_w > 0` means vertex `w` is *under-observed*
(`d_S,w < d*_w = N x_w / n`), so adding flow through `w` helps; `h_w < 0` means
*w over-observed*.

---

## 5. Cycle descent and the decrement obstruction

**Theorem 2 (cycle descent).** If `G(R)` contains a directed cycle `C` such that
`Σ_{w∈C} h_w > 0` and `d_S + 1_C` still satisfies `d_w ≤ N`, then `d_S` is not
a global optimum.

_Proof._ By Lemma 1, `1_C` is feasible and `d_S + 1_C ∈ F`; apply Theorem 1 with
`v = 1_C`. ∎

[mathematical proof]

**Corollary 1 (decrement obstruction).** If some observed vertex `w` has
`d_S,w > d*_w = N x_w/n`, `d_S,w ≥ 2`, and `d_S − e_w ∈ F` (i.e. `d_S` remains a
feasible flow after removing one copy of `w`), then `d_S` is not a global
optimum; its likelihood is strictly smaller than that of `d_S − e_w`.

_Proof._ Here `v = d_S − e_w − d_S = −e_w`; `h_w < 0`; hence
`Σ h v = h_w·(−1) = |h_w| > 0`. Apply Theorem 1. ∎

[mathematical proof]

Corollary 1 is the operational form of the mechanism: **an over-observed vertex
that can be thinned while staying a feasible §6.2 flow defeats the truth.**
`I_s` is a lower-bound-style (spanning) hypothesis and does not prevent this.
The family of §6 realises exactly this.

---

## 6. The infinite family

**Theorem 3 (bridging-insufficiency family).** For every integer `G ≥ 6` set
`L = G − 2`, `N = G`, and

```text
truth       S = 0^(G-1) 1              (circular, length G)
competitor  D = 0^(G-2) 1              (circular, length G-1)
reads       the windows of D, one per distinct type, placed in S
```

Precisely, the observed types are `0^L` and the `L` words
`w_j = 0^(L-1-j) 1 0^j` (`j = 0,…,L-1`), each with multiplicity one
(`n = G-1`), placed at start positions
`P = {0} ∪ {2, 3, …, G-1} ⊂ Z_G`. Then:

1. `I_s` holds (coverage; all triple repeats all-bridged; no interleaved pair).
2. The truth-induced flow `d_S = spec_L(S)|_O` (`= 1` on every observed type
   except `0^L`, where it is `2`) is a feasible §6.2 flow, and so is the
   read-tiled competitor `d_D = spec_L(D)|_O = x` (`= 1` on every type).
   Both are feasible for every `o_min ∈ [1, L−1]`, for the single-strand and
   bidirected readings, and under both the per-type and per-occurrence lower
   bounds.
3. The exact fixed-`N` §6.1 binomial ratio is

```text
P(D)/P(S) = (1/2) · ((G-1)/(G-2))^(G-2)  >  1,
```

   which is increasing in `G` with limit `e/2 ≈ 1.35914`; in particular it
   exceeds `1` for every `G ≥ 4`.
4. The KKT derivative of Corollary 1 at the over-observed vertex `0^L` is the
   `G`-independent value

```text
h_{0^L} = (G·1 − (G−1)·2) / (2·(G−2)) = −1/2  <  0,
```

   and `v = d_D − d_S = −e_{0^L}`, so `Σ h_w v_w = +1/2 > 0`: the truth is not
   even a local optimum.

_Proof._

*Observed structure.* `D = 0^{G-2}1` has one all-zero window
`0^L` (at start 0) and `L` windows containing its single `1`, each once; hence
`n = 1 + L = G − 1` and `x_w = 1` for all `w ∈ O`. `S = 0^{G-1}1` has the same
window set, with `0^L` occurring twice (starts 0 and 1) and every other window
once; its placement in `S` is exactly the set `P = {0} ∪ {2,…,G−1}` (the crossing
windows have start `2+j` for `j=0,…,L−1`).

*Coverage.* Read `[0,L)` covers positions `0…G−3`; read `[2,2+L)=[2,G)` covers
`2…G−1`; read `[G−1, G−1+L)` covers `G−1,0,1,…,G−4` cyclically. Their union is
all of `Z_G`.

*Repeats.* Every word of `S` containing the unique symbol `1` occurs once, so
every repeat word is `0^ell` for some `ell ∈ [1, G−2]`, with copies at
`0,1,…,G−1−ell`. For a copy at `t`, the preceding symbol is `1` iff `t = 0` and
the following symbol is `1` iff `t = G−1−ell`. Hence a maximal repeat *pair* is
exactly `{0, G−1−ell}`; any two maximal pairs share the copy `0`, so no
interleaved pair exists. A maximal *triple* must contain the two extremal copies
`0` and `G−1−ell` and one interior copy `m ∈ [1, G−2−ell]`; this forces
`ell ≤ G−3`.

*Bridging every triple copy.* For a copy at `t`, a read bridges it when it
contains both `t−1 (mod G)` and `t+ell (mod G)`. Because `ell ≤ G−3 = L−1`,
the cyclic distance between these two positions is at most `L`, so some
length-`L` window contains both; choosing the window whose start lies in `P`
(possible by the cases below) gives a read in the realised collection:
- `t = 0`: positions `G−1` and `ell`; use start `G−1` if `ell ≤ G−4`, else
  (i.e. `ell = G−3`) start `G−3`.
- `t = G−1−ell`: positions `G−2−ell` and `G−1`; use start `G−2−ell` if
  `G−2−ell ≥ 2`, start `G−1` if `G−2−ell = 1` (`ell = G−3`).
- interior `t = m`, positions `m−1` and `m+ell`:
  if `m−1 ≠ 1` and `ell ≤ G−4`, start `m−1` works (it covers `m−1` and
  `m+ell`, since `(m−1)+L = m+G−3 > m+ell`); this handles `m = 1`
  (`ell ≤ G−4`) and all `m ≥ 3`; if `m = 2` and `ell ≤ G−5`, start `0`
  covers `1` and `2+ell ≤ G−3`; if `m = 2` and `ell = G−4`, start `G−2`
  covers `1` and `G−2`; the sole remaining interior case is `ell = G−3`,
  `m = 1`, with positions `0` and `G−2`, and start `G−2` covers both.
  Every used start lies in `P`.
So every copy of every maximal triple is bridged. This proves `I_s`.

*Feasibility.* The cyclic window sequence of `S` is a closed walk in `G(R)` with
consecutive overlaps `L−1`; its vertex throughput is `d_S`. The cyclic window
sequence of `D` likewise gives `d_D = x`. Consecutive-window overlaps of length
`L−1` are present for every `o_min ≤ L−1`, and a length-`(L−1)` overlap cannot be
transitively reduced (no shorter overlaps exist for `o_min = L−1`; smaller
`o_min` only adds edges). Both vectors dominate the lower bounds `1` and satisfy
`d_w ≤ N = G`, so both lie in `F` under either lower-bound convention.

*Ratio.* All observed types have `x_w = 1`; `n − x_w = G−2`. Only the vertex
`0^L` differs between `d_S` (`2`) and `d_D` (`1`):

```text
P(D)/P(S) = [ (1/G)(1−1/G)^(G-2) ] / [ (2/G)(1−2/G)^(G-2) ]
          = (1/2) · ((G−1)/(G−2))^(G-2).
```

Since `(1 + 1/(G−2))^(G−2)` is increasing in `G` and equals `2` at `G = 3`, the
product exceeds `1/2 · 2 = 1` for every `G ≥ 4`; its limit is `e/2`.

*KKT derivative.* Immediate from Corollary 1. ∎

**Theorem 3 is a proof-level negative answer to the §6.2-restricted question**
"does `I_s` plus truth-feasibility force the truth to be a §6.2 optimum?" for
all `G ≥ 6`, with no finite-search caveat. The `G = 6, L = 4` member is exactly
the single instance found earlier by bounded search
(`docs/section62-nonspellable-flow-counterexample-broadened.md` §2, witness 1,
ratio `625/512`); Theorem 3 places it in a proved infinite family and identifies
its mechanism.

---

## 7. Why bridging cannot force optimality

The family makes the structural reason precise:

1. The §6.2 objective is separable with per-vertex target `d*_w = N x_w / n`.
   Only the *counts* `d_w` matter, not the repeat structure as such.
2. `I_s` constrains the *support* (which reads occur, coverage) and requires
   repeated words to be spanned by reads. It is a lower-bound/spanning condition:
   it can force `d_w ≥ 1`, but it cannot force `d_w ≤ d*_w`.
3. A repeat makes the truth's occurrence count at some vertex exceed the
   read-tiled count, while `I_s` is *satisfied more easily* by long repeats
   (the run `0^{G-1}`). When `n < N`, `d*_w = (N/n) x_w > x_w`, so the target
   sits between the collapsed count and the repeated count; the objective then
   prefers the collapsed competitor. The KKT derivative `h_{0^L} = −1/2` is
   `G`-independent.
4. Because the flow set is a cycle cone (Lemma 1), removing a copy along the
   truth's own circuit is a feasible displacement, so the competitor is a
   legitimate §6.2 object — indeed a single spelled molecule, not merely a
   non-contiguous flow.

---

## 8. What *would* force optimality (positive side)

Theorem 1 is a complete criterion; here are the clean sufficient conditions it
yields, for use by any positive attempt:

1. **Right multiplicity.** If `d_S,w = d*_w = N x_w/n` for every observed `w`
   (possible only when `N = G` and the spectrum is proportional to the sample,
   e.g. the read-tiled `n = N` slice `d_S = x`), then `h ≡ 0` and `d_S` is the
   unique §6.2 optimum. This recovers the `n = N` collapse of the conditional
   conservation note as a KKT corollary, without invoking conservation.
2. **Rigid graph.** If `F = {d_S}` (e.g. all reads distinct and the overlap graph
   is a single Hamiltonian cycle in the repeat-free case), optimality is
   vacuous.
3. **No improving cycle.** If every directed cycle `C` of `G(R)` has
   `Σ_{w∈C} h_w ≤ 0` and every feasible decrement has non-positive derivative,
   then `d_S` is optimal. This is the checkable normal-cone condition.

None of these follows from `I_s` alone, by Theorem 3.

---

## 9. Relation to existing repository work

- The KKT reduction `L(D|x) ∝ Σ x_i log d_i` and the cycle-lattice description
  of circular competitors are in
  `mathematics/fixed-length-likelihood-duality-and-flow.md`; that note's
  normal-cone test concerns the circular-genome Eulerian polytope. Theorem 1
  here is for the actual §6.2 flow set and is a different, discrete condition.
- The `n = N` collapse appears as Theorem 3 of the conditional-conservation note
  (`docs/section62-conditional-conservation-lemma.md`); §8.1 above rederives it
  as the `h ≡ 0` case of Theorem 1.
- The broader non-spellable search note
  (`docs/section62-nonspellable-flow-counterexample-broadened.md`) reported the
  `G = 6, L = 4` single-strand witness as a bounded-search finding. Theorem 3
  proves the family for all `G ≥ 6` and shows the competitor is a spelled
  molecule, so no non-spellable flow is needed.
- The source model and quotes match
  `docs/section62-bidirected-flow-feasibility.md` §1 and
  `docs/section62-actual-flow-feasibility.md` §1.

---

## 10. Epistemic status

| Claim | Status |
|---|---|
| §6.2 candidates are flows; objective is §6.1 binomial with external `N` | source fact (PMC3154397 §6.1–6.2) |
| Objective = `const − n Σ_w KL(q_w‖p_w)` | mathematical proof (§2) |
| Flow set = integer cycle cone (Lemma 1) | mathematical proof (§3) |
| KKT/no-feasible-improvement characterization (Theorem 1) | mathematical proof (§4) |
| Cycle-descent (Theorem 2) and decrement obstruction (Corollary 1) | mathematical proof (§5) |
| Family `S=0^(G-1)1`, `D=0^(G-2)1` satisfies `I_s` for all `G ≥ 6` | mathematical proof (§6) |
| `d_S`, `d_D` feasible §6.2 flows for every `o_min ∈ [1,L-1]` | mathematical proof + verified computation (§6) |
| Exact ratio `(1/2)((G-1)/(G-2))^(G-2) > 1` for `G ≥ 4` | mathematical proof + verified computation `G ≤ 15` |
| `I_s` holds, `d_S ∈ F`, competitor strictly better for `G ≥ 6` | mathematical proof + verified computation `G ≤ 60` |
| `I_s` + truth-feasibility cannot force §6.2 optimality | mathematical proof (§6) |
| Which MB09 layer / reverse-complement convention / `o_min` the 2016 sentence intends | **open** (source ambiguity) |
| Positive §6.2 statement outside `F={d_S}` and `h ≡ 0` | **open** |

---

## 11. Reproduce

```sh
python3 scripts/se62_kkt_family_independent.py
```

The script checks, with exact `fractions.Fraction` arithmetic: the KKT
derivative sign against the exact ratio; the family identity for `G = 4…60`; the
`I_s` predicate (independent implementation); flow feasibility of `d_S` and
`d_D` by an integral max-flow transportation test for every `o_min ∈ [1,L−1]`;
and `I_s` for `G = 6…60`. It exits non-zero on any failed assertion. (The
independent `I_s` predicate was additionally cross-checked against the
repository predicate `check_I_s` on `G = 6…12` during development; that
comparison needs the branch artifact and is not part of the durable script.)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397.
Bridging/hypothesis semantics: Guy Bresler, Ma'ayan Bresler, David Tse,
*Optimal assembly for high throughput shotgun sequencing*, BMC Bioinformatics
14(Suppl 5):S18, 2013; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade,
David N. C. Tse, *Information-optimal genome assembly via sparse read-overlap
graphs*, Bioinformatics 32(17) (2016) i494–i502.
