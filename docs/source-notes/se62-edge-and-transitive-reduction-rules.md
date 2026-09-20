# Exact §6.2 overlap-edge and transitive-reduction rules, and corrections to the repository's two implementations

_Status: independent primary-source pinning + exact finite computation,
2026-09-20, for issue #36. All claims are labelled **source fact**,
**source-supported inference**, **mathematical proof**, **verified
computation**, **repository fact**, or **open**._

_Reproduction:_ `python3 scripts/verify_se62_edge_and_reduction_rules.py`
(integer arithmetic only, deterministic, exits non-zero on any failed
assertion).

_Scope._ This note pins only the two rules the §6.2 object is built from:
(1) which bidirected overlap edges exist, and (2) which edges transitive
reduction removes. It does **not** re-derive the copy-count cone or the
`AAATT -> AAAATT` witness; those are
[`../section62-aaatt-reduced-flow-cone-and-spectra.md`](../section62-aaatt-reduced-flow-cone-and-spectra.md)
(cone + spectra) and
[`../section62-bidirected-lowerbound1-determination.md`](../section62-bidirected-lowerbound1-determination.md)
(determination). This note supplies the rule-level justification those packets
used and corrects one repository implementation that does not implement the
rule.

---

## 0. Verdict at a glance

1. **Edge rule (§3.3).** An overlap edge exists for each of the four strand
   cases of §3.3 and each valid proper overlap length `l in [o_min, L-1]`. The
   literal MB09 sentence "all possible bidirected overlaps of length at least
   `o_min`" admits **every** such length; Myers' string graph keeps only the
   **maximal** overlap between a pair of reads. For `{AAA, AAT, TAA}`,
   `L = 3`, the two conventions give the **same transitively reduced graph**
   (§3.3). [source fact + verified computation]

2. **Reduction rule (§6.2 + Myers 2005).** An edge `e` of overlap length `l`
   is removed iff some observed read `z` gives a two-step path `x -> z -> y`
   whose two overlaps are **proper** (`l1, l2 < L`), whose boundary incidences
   equal `e`'s, whose interior incidences oppose, and whose lengths compose as
   `l = l1 + l2 - L`. Equivalently the removed (transitive) edge has a strictly
   **shorter** overlap than both sub-overlaps: `l1, l2 > l`, which is automatic
   from the identity when `l2 <= L-1`. "Spelled by two shorter overlaps" means
   *two proper overlaps* ("shorter" than a whole read), **not** overlaps
   shorter than the removed edge. [source fact + source-supported inference +
   mathematical proof]

3. **Consequences for `L = 3`.** Only `l <= L-2 = 1` can be transitive; no
   length-2 edge is ever removed. At `o_min = 2` there are **zero**
   reductions, so the length-2 witnesses are reduction-robust for every
   `o_min`. At `o_min = 1`, exactly the two directions of the length-1 edge
   `AAT -- TAA` survive (middle window `ATA`/`TAT`, not an observed read); the
   other 16 length-1 edges are removed. [mathematical proof + verified
   computation]

4. **Correction (repository fact).**
   `scripts/independent_se62_bidirected_model.py:215` tests
   `e1.length < e.length and e2.length < e.length`. Together with
   `l = l1 + l2 - L` and proper overlaps this is **unsatisfiable** (it forces
   `l >= L+2 > L-1`), so the function removes nothing for any input. It is a
   no-op, not "the literal reading" its note
   ([`../independent-se62-bidirected-model.md`](../independent-se62-bidirected-model.md)
   §1, lines 97-101) claims. The primary witness is unaffected (it uses
   `o_min = 2`, where the true reduction is also empty), but the `o_min = 1`
   graph printed by that script is **unreduced**. [repository fact +
   mathematical proof + verified computation]

5. **Counting clarification.** `{AAA, AAT, TAA}` at `o_min = 2` has **10
   ordered** §3.3 edges: 3 non-loop pairs each in 2 directions, plus 4 loops
   (`AAA` twice-positive with incidence `0`, `AAA` twice-negative with
   incidence `0`, `AAT` `+2`, `TAA` `-2`). These are **7** undirected edges if
   the two incidence-`0` `AAA` loops are counted separately, or **6** if only
   endpoint pairs are counted. The three repository counts "10", "7", and "6"
   are therefore not contradictory. [verified computation]

---

## 1. Primary sources

- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* **16**(8) (2009) 1101-1116, §3.1-3.4, §6.2, §8.2,
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/)
  (body text re-read 2026-09-20).
- Eugene W. Myers, *The fragment assembly string graph*, *Bioinformatics*
  **21**(Suppl 2) (2005) ii79-ii85,
  DOI [10.1093/bioinformatics/bti1114](https://doi.org/10.1093/bioinformatics/bti1114).
- Jared T. Simpson, Richard Durbin, *Efficient construction of an assembly
  string graph using the FM-index*, *Bioinformatics* **26**(12) (2010)
  i367-i373, §2.3, §3.2,
  [PMC2881401](https://pmc.ncbi.nlm.nih.gov/articles/PMC2881401/). The 2010
  paper restates Myers' transitive-edge definition explicitly and attributes
  the procedure to Myers (2005); Myers' own PDF is access-protected, so the
  precise definition below is cited from the restatement.

### 1.1 §3.3, verbatim four cases

> "Let `x` and `y` be two `k`-molecules represented by vertices ... Then `e` is
> a bidirected overlap if one of the following holds
>
> - `e` is positive-incident to `x` and negative-incident to `y` and `p(x)`
>   overlaps `p(y)`;
> - `e` is positive-incident to `x` and positive-incident to `y` and `p(x)`
>   overlaps `n(y)`;
> - `e` is negative-incident to `x` and negative-incident to `y` and `n(x)`
>   overlaps `p(y)`;
> - `e` is negative-incident to `x` and positive-incident to `y` and `n(x)`
>   overlaps `n(y)`.
>
> The length of this bidirected overlap is the length of the underlying string
> overlap."

[source fact]

### 1.2 §6.2, verbatim graph and reduction rule

> "The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. The vertices of this graph are the reads, and the
> edges are all possible bidirected overlaps of length at least `omin`, where
> `omin` is a parameter to our algorithm. We then perform transitive edge
> reduction, where we remove any overlap that is spelled by two shorter
> overlaps. This procedure is identical to the one described in Myers (2005),
> and we refer to the resulting graph as the transitively reduced bidirected
> overlap graph."

[source fact]

### 1.3 §8.2, the paper's own `o_min` regime

> "The reads generated were always of length 25 ... The minimum overlap length
> (`omin`) was varied from 17 to 21."

Hence `o_min < L-1 = 24` in the source's experiments. [source fact]

### 1.4 Myers' transitive edge, as restated by Simpson-Durbin 2010 §2.3

> "Consider a read `X` that overlaps reads `Y` and `Z`, which mutually overlap.
> ... If `Y` and `Z` overlap the same end of `X`, i.e `type_xy = type_xz`, then
> ... there is a valid path that visits each of the three reads in succession.
> Let `X -> Y -> Z` be such a path. The string corresponding to this path is a
> valid assembly of the three reads which is identical to the string
> corresponding to the path `X -> Z`. In this case, we say that the edge
> `X <-> Z` is transitive. We will refer to non-transitive edges as
> irreducible."

and

> "As the graph does not have contained reads, the length of the overlap
> between `X <-> Y` is necessarily larger than the overlap between `X <-> Z`.
> ... the length of `label_xy` is shorter than `label_xz`, and `label_xz` can
> be seen as the concatenation of `label_xy` and `label_yz`."

Also §3.2: "In rare cases, multiple valid overlaps may occur between a pair of
reads. ... duplicated or intersecting intervals that represent sub-maximal
overlaps can be removed ... the set of maximal overlaps." [source fact]

### 1.5 Contained-read removal is vacuous for §6.2

Myers' string graph also drops *contained* reads (a read that is a substring of
another). MB09 §6.2's reduction sentence speaks only of edge removal. Since the
source's reads all have the same length `L` (1.3), no read is a strict
substring of another, so the containment step is vacuous and MB09's
"transitive edge reduction" is exactly the edge rule of §2. [source fact +
mathematical proof]

---

## 2. The exact rules

### 2.1 Edge rule

With `p(x)`, `n(x) = rc(p(x))` the two strands of molecule `x`, and "`A`
overlaps `B`" meaning a nonempty proper suffix of `A` equals a prefix of `B`,
the §3.3 cases map strands to incidences as

| strand of `x` | strand of `y` | incidence at `x` | incidence at `y` |
|---|---|---|---|
| `p` | `p` | `+` | `-` |
| `p` | `n` | `+` | `+` |
| `n` | `p` | `-` | `-` |
| `n` | `n` | `-` | `+` |

For each case and each overlap length `l` with `o_min <= l <= L-1`, add a
bidirected edge of length `l`. A self-loop gets incidence `+2` (`p/n` with
`x = y`), `-2` (`n/p`), or `0` (same-strand), per §3.2. [source fact]

The literal MB09 phrase "all possible ... of length at least `o_min`" admits
every valid length; Myers'/Simpson-Durbin's string graph keeps only the
**maximal** overlap per read pair (1.4). Both are labelled readings; for the
`{AAA, AAT, TAA}` instance they yield the same reduced graph (§3.3).

### 2.2 Reduction rule, and why "shorter" means proper

Place the left read at `[0,L)`, the intermediate read at `[L-l1, 2L-l1)`, and
the right read at `[2L-l1-l2, 3L-l1-l2)`. The `x`-`y` overlap is then

```text
l = L - (2L - l1 - l2) = l1 + l2 - L ,
```

and it exists only when `l > 0`, i.e. `l1 + l2 > L`. Because `l2 <= L-1`,

```text
l = l1 + l2 - L <= l1 - 1 < l1 ,
```

so `l < l1` and symmetrically `l < l2`: the two sub-overlaps are **longer**
than the removed edge. This is Simpson-Durbin's `type_xy = type_xz` /
"irreducible label is a prefix of the transitive label" condition (1.4). It
also shows that the phrase "two shorter overlaps" in MB09 §6.2 must mean *two
proper overlaps* (shorter than a read), since the alternative reading —
sub-overlaps shorter than the removed edge — contradicts `l = l1 + l2 - L` and
`l2 <= L-1`.

The reduction must also match **boundary incidences**: the composed path
`x -> z -> y` fixes an incidence at `x` and at `y`, and only removes `e` when
those equal `e`'s incidences; interior incidences at `z` must oppose
(§3.2 walk condition). Dropping the boundary check over-reduces: e.g.
`AAT(n) -> AAA(n) -> TAA(n)` composes to the `(n,n)` length-1 `AAT--TAA` edge,
not to the `(p,p)` one, even though both have the same endpoints and length.
[mathematical proof]

Finally, Myers' algorithm removes an edge using a path whose edges are not
themselves removed; for `L = 3` the reducing path always consists of length-2
edges, which are never removed, so no ordering subtlety arises. [source fact +
mathematical proof]

### 2.3 The `L = 3` bound

Since `l1, l2 <= L-1`, the composition identity gives
`l <= (L-1) + (L-1) - L = L-2`. For `L = 3`, `l <= 1`: only length-1 overlaps
are transitive, and no length-2 (maximal) edge is ever removed. This is exactly
Lemma 1 of
[`../section62-aaatt-reduced-flow-cone-and-spectra.md`](../section62-aaatt-reduced-flow-cone-and-spectra.md),
re-derived here from §3.3. [mathematical proof]

---

## 3. Tests against the repository

`scripts/verify_se62_edge_and_reduction_rules.py` rebuilds §3.3 from scratch
and checks the following.

| check | result |
|---|---|
| §3.3 ordered edges, `L=3`, `o_min=2` | 10 |
| §3.3 ordered edges, `L=3`, `o_min=1` | 28 (10 length-2, 18 length-1) |
| maximal-overlap-only edges, `o_min=1` | 20 |
| reducible at `o_min=2` | 0 |
| reducible at `o_min=1` | 16, all length-1 |
| length-1 survivors at `o_min=1` | the 2 directions of `AAT--TAA` |
| reduced graph, maximal-only vs all-length | identical |
| hits of the `l1<l and l2<l` predicate | 0 (unsatisfiable) |
| content predicate vs incidence rule | agree on all 18 length-1 edges |

[verified computation]

### 3.1 `scripts/independent_se62_bidirected_model.py` (vacuous reduction)

`transitive_reduction` (lines 179-227) tests at line 215

```python
if e1.length < e.length and e2.length < e.length \
        and e1.length + e2.length - L == e.length:
```

For proper overlaps, `l1, l2 < l` with `l = l1 + l2 - L` forces
`l >= L + 2 > L - 1`, a contradiction; the branch can never be taken. The
function therefore returns `kept = edges, removed = []` for every input, and
its assertion "a maximal-overlap edge was removed ... // no" is vacuous. The
accompanying note
([`../independent-se62-bidirected-model.md`](../independent-se62-bidirected-model.md)
§1, lines 97-101) calls this "the **literal** reading" and says no
maximal-overlap edge is ever removed. The conclusion is correct for length-2
edges but for the wrong reason (`l <= L-2`), and the function does not
implement the source-supported Myers reading at all; at `o_min = 1` the
printed 12-edge graph is the unreduced graph. The primary `o_min = 2`
certificate is unaffected. [repository fact + mathematical proof + verified
computation]

### 3.2 `scripts/verify_se62_aaatt_flow_cone.py` (correct reduction)

`reducible` (lines 96-108) removes a length-1 edge iff the middle window
`mol_class(mol[1:4])` of its spelled 5-mer is an observed read. This is the
content form of the §2.2 rule: when the middle window is an observed read, the
two length-2 overlaps exist by construction with the required strands, and the
boundary strands (hence incidences) are those of the original edge. The
independent script confirms it agrees with the incidence-based rule on all 18
length-1 edges. The `kept1 == 2` assertion and the survivor identity are
correct. [verified computation]

### 3.3 Counting reconciliation

The definitions audit reports "10 edges" at `o_min = 2`
(`docs/source-notes/mb09-se62-definitions-independent-audit.md`, branch
artifact), the independent model reports "7 undirected edges"
(`../independent-se62-bidirected-model.md` §2), and the cone note reports
"10 directed port edges (equivalently 6 undirected)"
(`../section62-aaatt-reduced-flow-cone-and-spectra.md` §2). These are the same
graph counted three ways: 10 ordered §3.3 edges, 7 if the two incidence-`0`
`AAA` loops are distinguished as undirected edges, 6 if loops are grouped by
endpoint pair only. None is an error. [verified computation]

---

## 4. Corrections recorded

1. **`scripts/independent_se62_bidirected_model.py`.** The
   `transitive_reduction` predicate `e1.length < e.length and
   e2.length < e.length` is unsatisfiable for proper overlaps; the function is
   a no-op. The source-supported rule is §2.2 (composition through an observed
   read, proper sub-overlaps, matching boundary incidences). At `o_min = 2`
   the difference is invisible; at `o_min = 1` it is the difference between
   the unreduced graph and the 12-edge reduced graph of
   `verify_se62_aaatt_flow_cone.py`. Cross-linked from
   `../independent-se62-bidirected-model.md`.
2. **Phrase "spelled by two shorter overlaps".** Read as *two proper
   overlaps*, not as *overlaps shorter than the removed edge*; the latter is
   impossible (§2.2). This resolves the "one genuinely ambiguous phrase" noted
   in `../section62-aaatt-reduced-flow-cone-and-spectra.md` §1 in favour of the
   Myers/Simpson-Durbin reading, with the reason now explicit.
3. **Edge-set convention.** MB09's literal "all possible overlaps of length at
   least `o_min`" admits sub-maximal overlap lengths; Myers' string graph keeps
   only maximal overlaps. The two reduced graphs coincide for the `AAATT`
   instance but are not equal in general. Any theorem that quantifies over
   "the §6.2 graph" must name which convention it uses.
4. **Contained reads.** Myers' contained-read removal is vacuous for MB09
   §6.2 because all reads have equal length; MB09's reduction sentence invokes
   only the edge rule (§1.5).

---

## 5. Epistemic summary

| claim | status |
|---|---|
| §3.3 four strand cases and incidence table | **source fact** (PMC3154397 §3.3) |
| §6.2 edges = all bidirected overlaps of length `>= o_min`; transitive edge reduction "identical to Myers (2005)" | **source fact** (PMC3154397 §6.2) |
| `o_min < L-1` in the source's experiments (`L=25`, `o_min in 17..21`) | **source fact** (PMC3154397 §8.2) |
| Myers transitive edge = shorter overlap inferred from a longer two-step path, `l1,l2 > l` | **source fact** (Simpson-Durbin 2010 §2.3, restating Myers 2005) |
| composition identity `l = l1+l2-L`; boundary-incidence matching; `l <= L-2` | **mathematical proof** |
| "shorter overlaps" = proper overlaps, not shorter than the removed edge | **source-supported inference + mathematical proof** |
| `L=3`: only length-1 edges reducible; `o_min=2` has zero reductions | **mathematical proof + verified computation** |
| `o_min=1` length-1 survivors = the 2 directions of `AAT--TAA` | **verified computation** |
| maximal-only vs all-length reduced graph identical for `{AAA,AAT,TAA}` | **verified computation**, instance-specific |
| `independent_se62_bidirected_model.py:215` predicate is unsatisfiable / no-op | **repository fact + mathematical proof + verified computation** |
| `verify_se62_aaatt_flow_cone.py` reduction matches the exact rule | **verified computation** |
| which convention (maximal vs all-length; `o_min`; `4^k` vs molecule classes) the 2016 open question intends | **open** (unchanged; see the referent notes) |

Cross-references:
[`reverse-complement-strand-convention.md`](reverse-complement-strand-convention.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`../section62-aaatt-reduced-flow-cone-and-spectra.md`](../section62-aaatt-reduced-flow-cone-and-spectra.md),
[`../section62-bidirected-lowerbound1-determination.md`](../section62-bidirected-lowerbound1-determination.md),
[`../independent-se62-bidirected-model.md`](../independent-se62-bidirected-model.md).
Branch artifact (not on this branch): `docs/source-notes/mb09-se62-definitions-independent-audit.md`.
