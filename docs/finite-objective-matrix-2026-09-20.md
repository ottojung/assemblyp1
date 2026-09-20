# Finite-model objective matrix for the AssemblyP1 ML frontier

_Status: reconciliation/audit note, 2026-09-20, on branch
`agent/finite-objective-matrix-0920`, based on `origin/main` at `8b2f0fc` with
the same-length §6.2 correction from `audit/se62-witness-sufficiency-0920`
(`b54f083`) applied. Every claim is labelled **source fact**,
**source-supported inference**, **mathematical fact**, **verified
computation**, **kernel-checked**, **bounded computation**, or **open**._

_Reproduce all arithmetic below with_

```sh
python3 scripts/verify_finite_objective_matrix.py
```

_which is self-contained, exact (`fractions.Fraction`), deterministic, shares no
code with the repository's other searches, and exits non-zero on any failed
assertion._

---

## 0. Purpose and result at a glance

The 2016 Shomorony et al. sentence names a "maximum-likelihood formulation"
without fixing the objective, the read-type convention, or the candidate class.
This note crosses the three axes the repository has actually sourced and lists,
for each of the eight cells, which integrated (merged, kernel-checked) witness
genuinely refutes it and which cells remain open.

1. **Six of the eight cells are refuted by integrated witnesses.**
   [verified computation + kernel-checked]
2. **The two open cells are exactly the `oriented read types × §6.2
   spelled/flow candidate` cells** (one per objective). They are open because
   every integrated §6.2 witness needs the MB09 reverse-complement collapse, and
   under strict oriented indexing the surviving same-length competitor's
   likelihood is `0`, not `> 1`. [verified computation]
3. **Those two open cells are not source-faithful formulations.** MB09 §6.2
   builds its graph on reads "which are DNA molecules" and identifies `d_i`
   with the flow through a read-molecule vertex; an *oriented* `4^k`-indexed
   §6.2 graph contradicts that construction. Restricting to source-faithful
   panels, the finite formulation set is closed negatively. [source fact +
   source-supported inference]
4. **Three `main` statements still assert that the §6.2 reading "is not
   refuted" / that no witness is §6.2-feasible.** Those statements predate the
   PR #43 same-length witness and are stale; the corrections are itemized in
   §5. They are also independently corrected by the unmerged branch
   `audit/se62-witness-sufficiency-0920` (`b54f083`), which this branch
   includes. [repository fact]

---

## 1. The three axes, fixed from the sources

| Axis | Value | Source anchor | Status |
|---|---|---|---|
| objective | exact MB09 §6.1 global read-count multinomial, candidate-intrinsic `N(D) = Σ_i d_i` | MB09 §6.1; `mb-formulation-referent-reconciliation.md` §2.1 | source fact |
| objective | MB09 §6.1 separable fixed-`N` product of binomial marginals, external known `N` | MB09 §6.1; `mb-formulation-referent-reconciliation.md` §2.2 | source fact |
| strand | oriented length-`L` reads (Shomorony circular-string model; cyclic-shift equivalence) | Shomorony §2; `equivalence-and-tie-wellposedness.md` §2.1 | source fact |
| strand | reverse-complement `k`-molecule classes (MB09 reads are DNA molecules, each represented once; dihedral equivalence) | MB09 §3.1, §4.1, §6.2; `mb09-se61-index-orientation-resolution.md` | source fact + source-supported inference |
| candidate | circular sequences on the objective's domain (no support condition) | MB09 §6.1; `mb09-se61-se62-candidate-semantics-audit` §5.1 | source fact |
| candidate | MB09 §6.2 spelled circuits (support equality `supp(spec_L(D)) = supp(x)`, per-vertex lower bound `1`) | MB09 §6.2, Observation 7; `section62-mb09-bidirected-graph-audit.md` | source fact + source-supported inference |

Two conventions are deliberately *not* free axes, because the sources couple
them:

- **Reverse-complement equivalence is forced iff the molecule read types are
  used**; oriented read types force only cyclic shift. The strand axis and the
  genome-equivalence axis are one coupled choice. [mathematical fact;
  `equivalence-and-tie-wellposedness.md` Fact 4]
- **A strictly-better competitor is equivalence-proof.** All integrated
  witnesses below are strict-inequality witnesses, so they refute both the
  maximizer schema and the unique-up-to-equivalence schema for every genome
  equivalence and every tie convention. Equivalence and ties therefore do not
  affect the matrix. [mathematical fact;
  `conclusion-semantics-strict-witness-robustness.md`]

The **per-occurrence strengthening** `d_w ≥ x_w` is *not* the §6.2 lower bound
(the source bound is per vertex `1`); it is a repository variant and is tracked
separately in §4. [source fact + source-supported inference; MB09 §6.2]

---

## 2. The integrated witnesses

All four are merged on `main`, kernel-checked in Lean, and satisfy the
Shomorony `I_s` bridging hypothesis with a non-vacuous all-bridged triple
repeat. `R` denotes the literal fixed-`N` product of binomial marginals; `E`
denotes the candidate-intrinsic exact multinomial.

| Witness | Lean module | Objective | Lengths | oriented `R` / `E` | molecule `R` / `E` | §6.2 spelled? |
|---|---|---|---|---|---|---|
| W1 `AAABB → AAAAB` | `FixedLengthExactCounterexample` | `E` | `5→5` | `1125/512` / `2` | n/a (abstract alphabet) | no |
| W2 `AAACC → AAAAC` | `FixedLengthBinomialCounterexample` | `R` | `5→5` | `1125/512` / `2` | `1125/512` / `2` | no |
| W3 `AAATT → AAAATT` | `Section62BridgingCounterexample` | `R` | `5→6` | `9/8` / `125/108` | `9/8` / `125/108` | **yes** |
| W4 `AAATAT → AAAAAT` | `SameLengthSection62Counterexample` | `R`, `E` | `6→6` | `0` / `0` | `5` / `3` | **yes** |

Notes on the table:

- `W1` uses the abstract two-symbol alphabet `{A,B}` with `B` self-complement;
  it is listed for the exact oriented panel only and is an alphabet rename of
  the real-DNA `W2` instance. [verified computation]
- `W2`'s ratios are strand-independent because none of its positive- or
  zero-count types is a reverse complement of another; the literal full-product
  ratio `1125/512` therefore holds under either strand panel. The ratio is what
  the retained zero-count factors add over the exact ratio `2`.
  [verified computation]
- `W3`'s exact ratio is `125/108 > 1` because the candidates have different
  lengths (`5` vs `6`); the binomial ratio `9/8` is the one quoted on `main`.
  [verified computation]
- `W4` **inverts** under strict oriented indexing: the observed oriented type
  `TAT` is absent from `D = AAAAAT`, so `D`'s oriented likelihood factor is
  `(0/N)^1 = 0`. Its molecule-class ratios are `5` (binomial) and `3` (exact).
  [verified computation; `mb09-se61-index-orientation-resolution.md` §4]

Ratios are `L(D)/L(S)`; `> 1` means the competitor strictly beats the truth.

---

## 3. The matrix

Cell status: **Neg** = refuted by at least one integrated witness admissible in
that cell; **Open** = no integrated witness (bounded-zero evidence only);
**N/S** = the cell is not a source-faithful formulation.

| # | Objective | Strand | Candidate | Status | Witness / evidence |
|---|---|---|---|---|---|
| 1 | exact `N(D)` | oriented | sequence | **Neg** | `W2` `E` ratio `2` (also `W1`, `W3`) |
| 2 | exact `N(D)` | oriented | §6.2 spelled/flow | **Open / N/S** | no integrated oriented spelled witness; bounded zero (PR #47, main control row) |
| 3 | exact `N(D)` | molecule | sequence | **Neg** | `W4` `E` ratio `3` (also `W3` `125/108`, `W2` `2`) |
| 4 | exact `N(D)` | molecule | §6.2 spelled/flow | **Neg** | `W4` `E` ratio `3`; `W3` `E` ratio `125/108` |
| 5 | fixed-`N` binomial | oriented | sequence | **Neg** | `W2` `R` ratio `1125/512` (also `W3` `9/8`) |
| 6 | fixed-`N` binomial | oriented | §6.2 spelled/flow | **Open / N/S** | no integrated oriented spelled witness; bounded zero |
| 7 | fixed-`N` binomial | molecule | sequence | **Neg** | `W4` `R` ratio `5` (also `W3` `9/8`, `W2` `1125/512`) |
| 8 | fixed-`N` binomial | molecule | §6.2 spelled/flow | **Neg** | `W4` `R` ratio `5`; `W3` `R` ratio `9/8` |

[verified computation + kernel-checked]

### 3.1 Why cells 4 and 8 are genuinely refuted

A spelled circuit is a special §6.2 flow, and both `S` and `D` are admissible
spelled circuits. Since the competitor strictly beats the truth, the truth is
not a maximizer over the larger §6.2 flow feasible set either (negative results
transfer upward along candidate-set inclusion). [mathematical fact;
`same-length-witnesses-candidate-set-inclusion.md` §3;
`section62-mb09-bidirected-graph-audit.md`]

### 3.2 Why cells 2 and 6 are open, and why they are not source-faithful

Every integrated §6.2 witness uses the reverse-complement collapse
(`ATT ~ AAT`, `TTA ~ TAA`, `TAT ~ ATA`) to make the truth and competitor
support-equal. Under strict oriented indexing:

- `W4`'s competitor loses the observed `TAT` and its likelihood is `0`, so it
  cannot refute the cell; and
- the truth is not support-equal to the observation under oriented indexing
  either.

No integrated witness is an oriented spelled-circuit counterexample, and the
bounded searches on `main` and on PR #47
(`analysis/uniform-strand-search-2026-09-20`,
`docs/source-notes/uniform-strand-convention-search-2026-09-20.md`) find zero
same-length beats under single-strand plus support equality. That evidence is
**bounded**, not a proof of absence. [bounded computation]

The cells are also **not source-faithful**: MB09 §6.2's vertices are read DNA
molecules represented once, and `d_i` is the flow through a molecule vertex; a
`4^k`-oriented §6.2 graph would make a read and its reverse complement distinct
vertices, contradicting §1.1, §3.1, §4.1, and §6.2 of MB09.
[source fact + source-supported inference;
`mb09-se61-index-orientation-resolution.md` §3]

### 3.3 What is *not* in the matrix

- **Source referent.** No primary source selects exact vs binomial vs §6.2 vs
  the broad principle. The matrix describes what each formulation is; it does
  not choose one. [source gap; `mb-formulation-referent-reconciliation.md` §5]
- **Regime.** The sentence is per read set; the integrated witnesses are
  low-coverage per-instance phenomena (`n < N`). The high-coverage/fixed-length
  asymptotic behaviour is a separate source fork. [open;
  `se62-witness-sufficiency-reconciliation-2026-09-20.md` §3.3]
- **Per-occurrence strengthening `d_w ≥ x_w`.** Not the source §6.2 bound; open
  in scope under that reading (bounded zero). [source fact + bounded
  computation; `section62-same-length-bidirected-counterexample.md` §1.1, §3]
- **Ties/equivalence.** Cannot affect the strict witnesses. [mathematical fact]

---

## 4. Unresolved cells

| Cell | Source-faithful? | Why open |
|---|---|---|
| exact `N(D)` × oriented × §6.2 spelled/flow | **no** (oriented §6.2 contradicts MB09 §6.2) | no integrated witness; bounded zero; `W4` inverts here |
| fixed-`N` binomial × oriented × §6.2 spelled/flow | **no** | same |

The **source-faithful finite matrix** (molecule strand, or sequence-level
oriented) is therefore closed negatively for every objective/candidate pair
that the sources actually raise. The only remaining definite finite peers are
the two oriented §6.2 cells, which are mathematical variants rather than MB09
readings. [interpretation]

---

## 5. Stale-overclaim register and corrections

The following `main` statements predate the PR #40/#43 §6.2 witnesses and are
now false or misleading. They are corrected on this branch (and independently
on `audit/se62-witness-sufficiency-0920`, `b54f083`).

1. **`docs/source-notes/mb-formulation-referent-reconciliation.md`** §0 item 5
   ("neither touches reading 3") and §7 row (3) ("**Not refuted.** No witness
   has both the truth and the competitor in the sequence-level §6.2 feasible
   set"). **Stale.** The same-length witness `AAATAT → AAAAAT` has both `S` and
   `D` as admissible §6.2 spelled circuits and strictly beats the truth; since a
   spelled circuit is a special flow, reading (3) fails at the per-instance
   level. What remains true is that no *source* selects reading (3) and that the
   source supplies no flow→sequence bridge.
2. **`docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`** §7
   table row "No current witness has both truth and competitor sequence-level
   §6.2-feasible". **Stale** for the source per-vertex reading; true only under
   the per-occurrence strengthening. (The §5 body already carries the
   correction; the table row was not updated.)
3. **`docs/source-notes/shomorony-mb-formulation-provenance.md`** §7
   ("the §6.2 feasibility work remains essential rather than optional") and §8
   item 4. **Superseded**: §6.2 feasibility is no longer an unexamined
   alternative that could rescue the implication.

No source fact, witness value, or exact ratio changes in these corrections.

The consolidated correction note is
[`docs/source-notes/se62-witness-sufficiency-reconciliation-2026-09-20.md`](source-notes/se62-witness-sufficiency-reconciliation-2026-09-20.md),
included here from `b54f083`.

---

## 6. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The three axes and their source anchors are as in §1 | source facts | MB09 §3.1, §4.1, §6.1–6.2; Shomorony §2; the cited notes |
| W1–W4 are integrated, kernel-checked, and satisfy `I_s` | kernel-checked + verified computation | Lean modules listed in §2 |
| Ratios in §2 (oriented/molecule, `R`/`E`) | verified computation | `scripts/verify_finite_objective_matrix.py` |
| Six of eight cells are refuted | mathematical fact + verified computation | §3, candidate-set inclusion |
| Cells 2 and 6 are open and not source-faithful | bounded computation + source fact | §3.2; PR #47; `mb09-se61-index-orientation-resolution.md` §3 |
| Strict witnesses are equivalence-proof | mathematical fact | `conclusion-semantics-strict-witness-robustness.md` |
| The three `main` statements in §5 are stale | repository fact | §5; `b54f083` |

---

## 7. Cross-references

- Objective/referent: `source-notes/mb-formulation-referent-reconciliation.md`,
  `source-notes/shomorony-mb-formulation-provenance.md`,
  `source-notes/medvedev-brudno-candidate-class.md`.
- Strand/index: `source-notes/mb09-se61-index-orientation-resolution.md`,
  `source-notes/equivalence-and-tie-wellposedness.md`.
- Candidate class/§6.2: `section62-mb09-bidirected-graph-audit.md`,
  `section62-same-length-bidirected-counterexample.md`,
  `source-notes/same-length-witnesses-candidate-set-inclusion.md`.
- Witnesses: `fixed-length-exact-counterexample.md`,
  `fixed-length-binomial-counterexample.md`,
  `bridging-se62-flow-ml-counterexample.md`.
- Same-length correction: `source-notes/se62-witness-sufficiency-reconciliation-2026-09-20.md`.
- Oriented-strand bounded frontier (unmerged): PR #47,
  `analysis/uniform-strand-search-2026-09-20`.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`;
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`, §3.1,
§4.1, §6.1–6.2; Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for
high throughput shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18
(2013), DOI `10.1186/1471-2105-14-S5-S18`.
