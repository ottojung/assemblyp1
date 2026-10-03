# Case 1 of the section 5 split: the census filter is buggy, and the sharp
# statement of the residual

Front `94f01` (recovery of the case-1 front), branch `board/94-replacement`.
Companion report: `/workspace/BOARD94-CASE1-0320.md`.

## What case 1 is

§5 of `/workspace/BOARD94-BADNESS-0153.md` leaves three cases; §9 of
`/workspace/BOARD94-CASE3-0300.md` discharged case 3 (a two-periodic genome has
no bad `θ`, §8 of `AssemblyP1/BBTReplacementInvariant.lean`) and named **case
1** as the next target: *exactly one constituent preceding-blocked, the other
unblocked*, with the suggestion that the blocked pair's maximal backward step
`p` should land its maximal repeat **onto** the unblocked pair's, "or at least
interleave with it after at most one further backward step".

In the repository's language the suggestion is

```text
(prevPos^[p] c = a ∧ prevPos^[p] d = b) ∨ (prevPos^[p] c = b ∧ prevPos^[p] d = a) ∨
Interleaved (mkGenome S) a b (prevPos^[p] c) (prevPos^[p] d)
```

with `BackAgrees hG S c d p ∧ ¬ BackAgrees hG S c d (p+1)` making `p` the
*maximal* backward step of the blocked pair. The third disjunct would close the
case: it exhibits an interleaved pair of maximal repeats, both of length
`≥ L−1` (`L−1` for the unblocked pair at its own starts, `L−1+p` for the blocked
one at its shifted starts), i.e. the second disjunct of `LongObstruction`.

## The census filter of front `94a04` is wrong

`scratch/backstep_census.py` (front `94a04`, §4 of
`/workspace/BOARD94-BADNESS-0153.md`) filters on "no long obstruction" with

```python
while e < G - 1 and len({S[(t[0] + i) % G] for i in range(e + 1)}) == 1 and ... :
    e += 1
if e >= K and len({S[(t[0] - 1) % G], S[(t[1] - 1) % G], S[(t[2] - 1) % G]}) > 1:
    return False        # i.e. "not P2"
```

`{S[(t[k] + i) % G] for i in range(e+1)}` is the set of symbols **inside one
window**, not a comparison of the three windows position by position, so the
triple-repeat clause essentially never fires and the filter **admits genomes
that do have a maximal triple repeat of length `≥ L−1`**. Every
"`¬ LongObstruction` genomes" column of that table, and the reading of the
`(p1, p2)` distribution that goes with it, is therefore unreliable. The
`crux_commonBackStep_obstruction` theorem the census was offered as evidence for
is kernel-checked and is unaffected; only the census's supporting claims are.

The corrected predicate is `scratch/case1_fixed.py`, transcribed from
`LongObstruction`, `Genome.IsRepeat`, `Genome.IsTripleRepeat` and `Interleaved`
in the Lean sources, with threshold `L−1`.

## What the corrected census shows

All binary circular words, `4 ≤ G ≤ 10`, all `2 ≤ L ≤ G+1`, all case-1
quadruples with `vtx a ≠ vtx c`, no fibre-cardinality restriction. `p` is the
maximal backward step of the blocked pair and `P = (c−p, d−p)`.

| relation between `{a,b}` and `P` | on `¬ LongObstruction` genomes | unrestricted |
| --- | --- | --- |
| `P = {a,b}` (exact landing) | 2680 | 50960 |
| `P` shares one start with `{a,b}` | 0 | 91008 |
| `P` disjoint and interleaved | 0 | 188232 |
| `P` disjoint, not interleaved | **0** | **0** |

So on every unblocked genome in range the landing is **exact**, which is
strictly stronger than §9's "coincide or interleave"; and `¬ LongObstruction`
does real work, since without it the landing fails in 188 232 configurations
(those are exactly the obstructions). The distribution of `p` on unblocked
genomes is `{1: 2432-ish, 2, 3}` (never larger than 3 up to `G = 9`).

**This is evidence, not proof**: a Python enumeration whose correspondence to
the Lean definitions is not machine-checked, with range ending at `G = 10`.

## The kernel-checked correction to the record

Using the buggy filter produces an apparent **refutation** of §9: `G = 7`,
`L = 3`, `S = 0100101`, `(a,b,c,d) = (0,3,6,1)`, `p = 3`, where the blocked
pair's maximal repeat sits at `(3,5)`, which neither coincides with `(0,3)`
nor interleaves with it — it *shares* the start `3`.

**The kernel refutes that refutation.** `decide` proves
`triple_0100101`: `0100101` has a maximal triple repeat of length `3 ≥ L−1 = 2`
at starts `0, 3, 5` (windows `010, 010, 010`; preceding symbols `1, 0, 1`;
following symbols `0, 1, 1`), so `LongObstruction hG7c 3 S7c`
(`longObstruction_0100101`). That genome is not a case-1 configuration at all.

| declaration | axiom set |
| --- | --- |
| `AssemblyP1.BBTReplacement.triple_0100101` | `[propext]` |
| `AssemblyP1.BBTReplacement.longObstruction_0100101` | `[propext]` |
| `AssemblyP1.BBTReplacement.case1_landing` | none (a `def`) |

## The residual

`case1_landing` (§9 of the module) is the sharp version of §9's case-1 claim,
with the interleaving disjunct deleted. It is stated as a `Prop` and **not
proved**: no `axiom`, no `sorry`, no `admit`. `case1_landing` implies §5.4 in
case 1 (with the `Preceding`-hypotheses of the configuration being hypotheses
of the shape, not assumed conclusions; the only genome-side hypothesis used is
`¬ LongObstruction`, which is a hypothesis of the regime).

Two things a successor should know before re-attacking the proof:

* the finite instances at `G = 5`, `G = 6` are within reach of `decide` **only**
  if the genome is enumerated (`∀ w : Fin G → Bool`, `S := bitW w`) or held as a
  variable with all hypotheses bundled in one binder and the goal closed by
  `decide +revert`; the cost is dominated by the `∃` over `(e₁,e₂,x,y,z,u)` in
  the second disjunct, which does not fit this host's 300 s bound at `G = 5`;
* `Interleaved` (the `Genome` version) has **no `Decidable` instance** and
  instance search cannot build one, so a `decide` goal containing it must have
  `Interleaved` replaced by `BBTChords.InterleavedStarts` (which has one) — the
  trick `BBTReplacementInvariant.lean` §6.3 already uses. `P2` and
  `LongObstruction` themselves need `unfold P2 mkGenome; decide`, or
  `P2.imp_Ukkonen` plus `longObstruction_iff_not_Ukkonen` for a `¬ LongObstruction`
  goal.