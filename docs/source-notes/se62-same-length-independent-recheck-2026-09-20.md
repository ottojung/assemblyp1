# Independent adversarial recheck: the `AAATAT → AAAAAT` same-length §6.2 witness

_Status: independent from-scratch recomputation + source re-read, 2026-09-20.
Verifies the integrated witness on `main` (`8182e1b`, PR #43) without using the
repository verifier or Lean module as an oracle. Conclusion: **no correction is
needed**; the witness is correct on the panel its own note names
(reverse-complement molecule classes, per-vertex lower bound). This note records
the recomputation and pins the exact source-model boundary at which the witness
would fail._

## 1. What was rechecked, and how

Everything below was recomputed with a self-contained script sharing no code
with `scripts/verify_samelength_se62_counterexample.py`. The Lean module was
independently rebuilt from `origin/main` and its axiom set printed.

| item | independent result |
|---|---|
| observed molecule spectrum `x` | `{AAA:2, AAT:1, ATA:1, TAA:1}` |
| truth spectrum `d_S` | `{AAA:1, AAT:1, ATA:3, TAA:1}` |
| competitor spectrum `d_D` | `{AAA:3, AAT:1, ATA:1, TAA:1}` |
| `I_s` coverage | holds |
| maximal triple repeats | four length-`1` triples of `A@{0,1,2,4}`, all copies bridged |
| interleaved pair | `A@{0,2}` with `A@{1,4}`, alternating, both copies bridged (non-vacuous) |
| bidirected overlap graph at `o_min = L−1 = 2` | 16 edges |
| `S` and `D` spelled circuits | every step a real edge, support equality, per-vertex flow `≥1`, zero balance, no supersource/sink |
| transitive reduction | removes no employed edge (all employed overlaps have length `2`) |
| `D` vs `S` under dihedral equivalence | inequivalent (not a rotation or reverse-complement rotation) |
| exact same-length multinomial ratio | `∏_w (d_D/d_S)^{x_w} = 3^2 · 1 · 3^{−1} = 3` |
| literal §6.1 fixed-`N` binomial ratio (`N = 6`, `n = 5`) | `(243/125)·(625/243) = 5` |
| Lean build | `lake build AssemblyP1.SameLengthSection62Counterexample` succeeds |
| Lean axioms | `propext`, `Classical.choice`, `Quot.sound` only |

The §6.1 ratio is robust to the choice of the candidate-normalizing length: if
the binomial uses `N = n = 5` instead of the source's fixed genome length `6`,
the ratio is `6 > 1`, and the exact multinomial ratio is `3` regardless of `N`
because the two candidates have equal length. So the competitor beats the truth
under the exact multinomial, the fixed-`N` binomial, and that alternative
normalization.

## 2. Source-model boundary (what would defeat it)

The witness is load-bearing only on a specific conjunction, and each escaping
axis is real:

1. **Reverse-complement aggregation.** `d_S(ATA) = 3` requires collapsing
   `TAT = ATA`. MB09 §3.1/§4.1 define reads as DNA molecules (unordered
   reverse-complement pairs) represented once, and §6.2 identifies the `d_i`
   with *vertex* flows of a graph whose vertices are reads. A single flow
   variable per molecule vertex cannot carry independent oriented counts, so
   the §6.2 objective is molecular. Under the literal §6.1 sentence "There are
   `4^k` such variables" the truth's support
   (`{AAA, AAT, ATA, TAT, TAA}`) strictly contains the observed oriented support
   (`{AAA, AAT, TAT, TAA}`), the truth is not a support-feasible candidate, and
   the witness does not apply. `main`'s own `docs/section62-same-length-bidirected-counterexample.md`
   §1.1 records this fork; the unmerged aggregation decision
   (`analysis/se62-revcomp-index-decision-0920`) does not change the `main`
   claim, which is already hedged to the molecule reading.
2. **Per-occurrence lower bound.** Requiring `d_D(w) ≥ x_w` makes the truth
   `d_S(AAA) = 1 < x_AAA = 2` inadmissible, so the hypothesis is unsatisfiable
   for this instance rather than refuted. The source states a lower bound of
   **one per read vertex** (§6.2), i.e. per distinct molecule; the per-occurrence
   condition is a strengthening, not the §6.2 definition.
3. **Single-strand / Shomorony-only panel.** Shomorony et al. (2016) work with a
   single circular string `s` and cyclic-shift equivalence, with reverse
   complements only as §4.1 preprocessing. Under that panel the collapse is not
   available and the witness is a cross-source construction, as the note says.

No mismatch beyond these is present. In particular the graph/orientation
bookkeeping in the Python verifier is partly automatic for any sequence walk
(consecutive windows share the same strand and the incidence signs at an
interior vertex are necessarily opposite), but that is harmless: the
substantive feasibility content is support equality plus real-edge existence,
both re-derived above by hand.

## 3. Verdict

For `S = AAATAT`, `D = AAAAAT`, starts `(0,0,1,3,5)`, `L = 3`, `N = 6`, the
finite instance satisfies the source-faithful `I_s`, both molecules are
admissible §6.2 spelled circuits with the per-vertex lower bound, `D` is
dihedrally inequivalent to `S`, and `D` strictly improves both same-length
objectives (exact `3`, §6.1 binomial `5`). The integrated `main` witness is
independently confirmed. Its scope limits are exactly the three axes in §2,
which the witness note already states.

Primary sources: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2, PMC3154397;
Shomorony, Kim, Courtade, Tse, *Information-optimal genome assembly via sparse
read-overlap graphs*, *Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), §5.
