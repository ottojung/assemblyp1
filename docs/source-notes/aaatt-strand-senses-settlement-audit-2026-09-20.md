# Adversarial settlement audit of the `AAATT → AAAATT` witness: the two senses of strand-contingency

_Status: independent adversarial audit for issue #36, 2026-09-20, written on
`main` at `488beda` (after the PR #40 content, merge commit `6256d46`). Scope:
try to falsify the claim that the merged `AAATT → AAAATT` witness “settles the
published open problem.” Claims are labelled **source fact**, **mathematical
fact**, **verified computation**, **kernel-checked**, **interpretation**, or
**open**. This note does not select a referent for the 2016 phrase and makes no
new settlement claim._

_Companion artifacts on `main`:
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)
(the witness),
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)
(the §6.2 construction),
`AssemblyP1/Section62BridgingCounterexample.lean` (the kernel check). It is
compatible with the unmerged claim-boundary and convention audits of the same
witness; where it differs from their wording it is about the word “strand,” not
about the verdict._

## 0. Verdict

**The claim “`AAATT → AAAATT` settles the published Shomorony et al. (2016) open
problem” is false, and no artifact on `main` makes it.** The witness refutes a
single named conjunction of conventions (§3 below), as its own §8 states. The
adversarial work here found no flaw in the witness’s finite arithmetic, its `I_s`
certificate, or its §6.2 graph/flow certificate, and it adds two clarifications
the merged note does not spell out:

1. the merged note’s “strand reading” boundary is about two different things —
   the *sequence-level §6.1 objective*, where the instance is **not**
   strand-contingent, and *§6.2 spellability*, where the reverse-complement
   read-molecule collapse **is** load-bearing; and
2. the kernel-checked interleaving veto is genuine, not vacuous: the hand-rolled
   `pairB`/`hasInterleavingB` detector agrees with an independent alternation
   definition on every binary genome of length `4…8`.

The load-bearing residual axes are therefore candidate length (free vs fixed
`G`), the sequence-vs-flow referent, the sample-size regime, and tie/equivalence
semantics — **not** the exact-vs-binomial objective and not the strand axis at
the sequence level. [interpretation]

## 1. Independently re-derived (concur with `main`)

Instance as on `main`: truth `S = AAATT` (`G = 5`), `L = 3`, realized starts
`(0,1,4)`, `n = 3`, external `N = 5`; observed molecule classes
`x = {AAA:1, AAT:1, TAA:1}`; truth spectrum `d_S = {AAA:1, AAT:2, TAA:2}`;
competitor `D = AAAATT` (`|D| = 6`), `d_D = {AAA:2, AAT:2, TAA:2}`. Re-running
[`../../scripts/verify_se62_bridging_flow_counterexample.py`](../../scripts/verify_se62_bridging_flow_counterexample.py)
and
[`../../scripts/verify_se62_mb09_bidirected_graph.py`](../../scripts/verify_se62_mb09_bidirected_graph.py)
reproduces the `I_s` certificate, the `9/8` ratio, the 10-edge bidirected graph,
and both spelled circuits. [verified computation]

The §6.2 transitive reduction is vacuous on the employed edges: every employed
edge has the maximal proper overlap `L−1 = 2`, and a length-`l` outer overlap
spelled through one middle read has length `l₁ + l₂ − L`, so lengths `l₁,l₂ < l`
can spell `l = 2` only if `l₁ + l₂ = 5`, impossible for `l₁,l₂ ≤ 1`; no proper
overlap longer than `2` exists for the Myers reading. Both readings therefore
retain the witness edges. [mathematical fact]

## 2. New check: the interleaving veto is non-vacuous

`main` proves `¬ HasInterleaving` by `decide` on the hand-rolled Boolean
`hasInterleavingB` (over `pairB` and `beforeB`). A Boolean that always returned
`false` would also prove `¬ HasInterleaving`, so the certificate is only
meaningful if the detector fires on positive instances. Porting
`pairB`/`hasInterleavingB` verbatim and comparing against an independent
definition — two maximal repeat pairs with exactly one of the second pair’s
starts in the open arc between the first pair’s starts — gives **exact
agreement over every binary genome of length `4` through `8`**, including `24`
genomes with a genuine interleaving at `G = 6`. The detector is non-vacuous and
the `AAATT` interleaving veto is sound. [verified computation]

(The census is a finite check of the detector, not evidence about any other
claim.)

## 3. The two senses of “strand-contingency”

The merged note’s §0 boundary 2, §4 point 1, and §6 read together suggest the
`9/8` mechanism “needs the reverse-complement collapse.” That is true for one
property and false for another; separating them removes an apparent tension
with the independent audit that reports the same instance at ratio `125/108`
under strand indexing.

**(a) Sequence-level §6.1 objective — not strand-contingent.** If read types are
the oriented length-`L` strings (Shomorony’s single strand, and MB09 §6.1’s
literal `4^k`), then `x`, `d_S`, `d_D` are
`{AAA:1,AAT:1,TAA:1}`, `{AAA:1,AAT:1,ATT:1,TTA:1,TAA:1}`, and
`{AAA:2,AAT:1,ATT:1,TTA:1,TAA:1}`. The external-`N` binomial gives
`L(D)/L(S) = (54/125)/(48/125) = 9/8`, and the exact candidate-intrinsic
multinomial gives `(1/27)/(4/125) = 125/108`. Both exceed `1`. Only the observed
type `AAA` changes (`1 → 2`); the extra unobserved truth types `ATT`, `TTA`
cancel between `S` and `D` because `D` contains them once too. So for the
sequence-level objectives the **same instance refutes the truth-is-ML conclusion
with or without the reverse-complement collapse**. [verified computation]

**(b) §6.2 spellability — strand-contingent.** The §6.2 competitor must be a walk
on the overlap graph whose vertices are the observed reads. The `D` walk needs
the windows `ATT` and `TTA`; collapsed to molecule classes they are the observed
vertices `AAT` and `TAA`, but as oriented reads they are absent from the graph
(the observed reads are only `AAA, AAT, TAA`). Hence the **§6.2** witness — the
part that removes the flow-feasibility escape — does need the molecule-class
collapse, exactly as the merged note says. [mathematical fact]

**Reconciliation.** The merged note is about the §6.2 reading, so its strand
boundary is correct in context; the “strand” caveat should be read as *“the
§6.2 spelled-circuit witness needs the read-molecule collapse,”* not as *“the
likelihood inequality fails under single strands.”* Conversely, an oriented
`9/8`/`125/108` computation does not make the instance §6.2-feasible. Neither
reading is selected by the sources. [interpretation]

## 4. What actually remains load-bearing

| Axis | Status for this witness |
|---|---|
| Objective (exact vs external-`N` binomial) | **not load-bearing** at sequence level: both give a strict win (`125/108`, `9/8`) |
| Strand / read-type collapse | **not load-bearing** at sequence level; **load-bearing** only for §6.2 spellability (§3) |
| Candidate length | **load-bearing**: the competitor has `|D| = 6 ≠ G = 5`; the fixed-`G` sub-case is left to the separate same-length witnesses ([`fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md), [`fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md)) |
| Sequence vs flow referent | **load-bearing/interpretive**: the 2016 sentence is sequence-valued; MB09 §6.2 returns a “(non-contiguous) assembly” needing a heuristic flow→sequence step ([`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md), [`shomorony-ml-reference.md`](shomorony-ml-reference.md)) |
| Sample-size regime | **load-bearing**: per-instance finite `n = 3` vs high-coverage, where the fixed-length truth becomes the eventual unique maximizer |
| Conclusion / tie | **not load-bearing** for this witness (`9/8` is strict, refuting both schemas), but open for other readings ([`ml-tie-semantics.md`](../literature/ml-tie-semantics.md)) |
| Kernel status | the §6.2 graph/flow certificate is verified computationally, not kernel-checked; only the sequence-level certificate and ratio are kernel-checked |

## 5. Consequence for the settlement question

Because the load-bearing axes include candidate length and the
sequence-vs-flow referent, and because the accepted 2016 text selects neither,
the published open problem is **not** settled by this witness. What the witness
does establish, in the precise panel of §3(b) plus unrestricted candidate length
and a finite read set, is that §6.2 flow feasibility plus `I_s` does not rescue
ML-optimality of the truth. That is a genuine but scoped negative result, and it
should be cited with its panel, never as “`AAATT` settles Shomorony 2016.”
[interpretation]

## 6. Reproduce

```sh
python3 scripts/verify_se62_bridging_flow_counterexample.py
python3 scripts/verify_se62_mb09_bidirected_graph.py
lake build AssemblyP1.Section62BridgingCounterexample
```

The oriented-objective ratios of §3(a) are reproduced by the exact-`Fraction`
computation

```python
from fractions import Fraction as F
from functools import reduce
from math import comb

S, D, L, starts, N = tuple('AAATT'), tuple('AAAATT'), 3, (0, 1, 4), 5
win = lambda s: [tuple(s[(i + j) % len(s)] for j in range(L))
                 for i in range(len(s))]
x, dS, dD = {}, {}, {}
for r in starts:
    x[win(S)[r]] = x.get(win(S)[r], 0) + 1
for w in win(S):
    dS[w] = dS.get(w, 0) + 1
for w in win(D):
    dD[w] = dD.get(w, 0) + 1
types = set(x) | set(dS) | set(dD)
exact = lambda d, n: reduce(
    lambda a, t: a * F(d.get(t, 0), n) ** x.get(t, 0), types, F(1))
binom = lambda d: reduce(
    lambda a, t: a * F(comb(3, x.get(t, 0)))
      * F(d.get(t, 0), 5) ** x.get(t, 0)
      * F(5 - d.get(t, 0), 5) ** (3 - x.get(t, 0)), types, F(1))
print('exact    ', exact(dD, 6) / exact(dS, 5))  # 125/108
print('binomial ', binom(dD) / binom(dS))          # 9/8
```

The interleaving-detector census of §2 is a finite exhaustive comparison over
`{A,B}^G` for `G = 4,…,8` (agreement in every case; `24` positives at `G = 6`).

## 7. Locators

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  “Information-optimal genome assembly via sparse read-overlap graphs,”
  *Bioinformatics* 32(17) (2016) i494–i502, §2, Eq. (1), Theorem 1, §5,
  DOI `10.1093/bioinformatics/btw450`.
- Paul Medvedev, Michael Brudno, “Maximum Likelihood Genome Assembly,”
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §3.3–3.4, §5.2, §6.1–6.2,
  §7, PMC3154397.
- Repository merge `6256d46` (PR #40) and its files
  [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
  [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md),
  `AssemblyP1/Section62BridgingCounterexample.lean`,
  `scripts/verify_se62_bridging_flow_counterexample.py`,
  `scripts/verify_se62_mb09_bidirected_graph.py`.
