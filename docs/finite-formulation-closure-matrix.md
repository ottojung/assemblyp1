# Proposition-level closure matrix for the finite-data formulations (issue #45 entry)

_Status: synthesis/reconciliation note, 2026-09-20, on branch
`analysis/finite-closure-matrix-0920`, based on `origin/main` at `8b2f0fc`.
It builds the closure matrix requested for issue #45, names the single most
important remaining cell, and records what settling it would require. It does
not modify intent records, does not select a source referent by fiat, and does
not introduce formulations merely because they can be enumerated
combinatorially. Every claim is labelled **source fact**, **source-supported
inference**, **kernel-checked**, **verified computation**, **interpretation**,
**modeling fact**, or **open**._

## 0. Purpose and entry condition

Issue #45 has the entry condition:

> the relevant source-faithful finite formulations and their live
> disambiguations have been responsibly settled negatively.

This note makes the current degree of completion explicit proposition by
proposition, so the orchestrator can judge whether that entry condition is met
and, if not, which single cell is load-bearing.

## 1. What this matrix is and is not

It is a table of the **materially plausible finite-data formulations that
`origin/main` actually supports**, one row per formulation, with the source
axes as columns. It is **not** a combinatorial product of every axis value:
only readings that a cited source or a documented repository source-fork
actually raises are listed. The excluded axis values are named in §5.

The axes are exactly those requested: **objective**, **strand / read-type
convention**, **candidate class**, **known length**, **equivalence / ties**,
**bridging hypotheses**, and **counterexample / proof status**. Two further
axes that `origin/main` documents as source forks are carried as annotations:
the **regime** (per-instance vs high-coverage) and the **conclusion schema**
(truth-is-a-maximizer vs every-maximizer-is-truth-up-to-equivalence).

## 2. Fixed axis values (source anchors)

| Axis | Values that a source raises | Anchor |
|---|---|---|
| objective | exact global read-count multinomial, candidate-intrinsic `N(D)`; §6.1 separable product of binomial marginals with external `N`; §6.2 bidirected flow optimization; a broad "ML formulation" family | `mb-formulation-referent-reconciliation.md` §2, §5 |
| strand / read type | oriented single-strand length-`L` substrings; reverse-complement `k`-molecule classes | `shomorony-ml-reference.md`; `mb09-se61-index-orientation-resolution.md` |
| candidate class | all nonempty circular sequences (any length); circular sequences of the true length `G`; §6.2 `F_flow(R)` (integral flows; spelled single molecules are the sequence-level sub-case) | `medvedev-brudno-candidate-class.md` §3; `section62-mb09-bidirected-graph-audit.md`; branch audit `mb09-se62-relations-independent-audit-2026-09-20.md` §6 |
| known length | candidate-intrinsic `N(D)`; external known `N` in the objective; competitor restricted to `|D| = N` | `medvedev-brudno-candidate-class.md` §1–§2; `shomorony-mb-formulation-provenance.md` §6.3 |
| equivalence / ties | cyclic shift; dihedral (`+` reverse complement); maximizer-only (`W`) vs unique-up-to-`≈` (`S`); no source tie rule | `equivalence-and-tie-wellposedness.md`; `conclusion-semantics-determination.md` §2 |
| bridging hypotheses | Shomorony `I_s`: coverage + all-bridged triple repeats + bridged interleaved pairs (Bresler–Bresler–Tse) | `bridging-se62-flow-ml-counterexample.md` §1.1 |
| regime (annotation) | per-instance for every `R ∈ I_s` (literal); high-coverage / `n → ∞` | `issue36-finite-vs-asymptotic-regime.md` (branch-only, not on main) |
| conclusion (annotation) | `W`: `∀ candidate, L(candidate) ≤ L(truth)`; `S`: `W ∧` tied ⟹ equivalent | `ml-formalization-contract.md`; `ml-tie-semantics.md` |

## 3. The matrix

`Neg` = closed negatively with a kernel-checked strict (equivalence-proof)
finite witness; `Open` = no counterexample and no proof; `N/A` = not a definite
finite proposition.

| ID | Objective | Strand | Candidate class | Known length | Equiv. / ties | Bridging | Status |
|---|---|---|---|---|---|---|---|
| F1 | exact multinomial, `N(D)` | oriented | all circular seqs. | intrinsic `N(D)`, free | cyclic shift; `W`/`S` | `I_s` | **Neg** (`AAABB→AAAAB`, ratio `2`; also `ACGT→ACACGT`) |
| F2 | §6.1 binomial, external `N` | oriented | all circular seqs. (on the objective's domain `d_i < N`) | external fixed `N`; length not constrained | cyclic shift; `W`/`S` | `I_s` | **Neg** (`AAACC→AAAAC`, ratio `1125/512`) |
| F3 | §6.1 binomial, external `N` | molecule (rev-comp class) | §6.2 spelled single molecule (`F_flow` sub-case) | free; same-length sub-case closed too | dihedral; `W`/`S` | `I_s` | **Neg** (var-len `AAATT→AAAATT`, `9/8`; same-len `AAATAT→AAAAAT`, `5`, exact `3`) |
| F4 | §6.1 binomial, external `N` | molecule | literal `F_flow(R)` (non-contiguous integral flows) | unconstrained | dihedral; `W`/`S` | `I_s` | **Neg on main by inclusion** (F3 competitor is a spelled circuit, a special flow); a genuinely non-spellable witness exists only off-main |
| F5 | §6.1 / §6.2 objective under **strict oriented `4^k` indexing** (single-strand panel) | oriented single strand | §6.2-style spelled/flow objects on the oriented overlap graph, or oriented circular seqs. | free | cyclic shift only | `I_s` | **Open** — bounded zero; main's §6.2 witnesses *invert* here |
| F6 | §6.2 with **per-occurrence** lower bound `d_w ≥ x_w` | molecule | spelled molecules with `d ≥ x` | free; same-length open | dihedral | `I_s` | **Open** — bounded zero; **not** the source condition (a repository strengthening) |
| F7 | broad "maximum-likelihood formulation" family | unspecified | unspecified | unspecified | unspecified | `I_s` | **N/A** — no definite finite proposition to refute |

### 3.1 What each `Neg` row rests on (kernel vs script)

- **F1** — `AssemblyP1.FixedLengthExactCounterexample` kernel-checks `AAABB →
  AAAAB` (exact ratio `2`); candidate-set inclusion (`same-length-witnesses-
  candidate-set-inclusion.md` §3) carries it to arbitrary length because both
  words have length `G`; `AssemblyP1.ExactVariantECounterexample` covers the
  variable-length `ACGT → ACACGT` instance. Strict, hence equivalence-proof
  (`conclusion-semantics-strict-witness-robustness.md` §3).
- **F2** — `AssemblyP1.FixedLengthBinomialCounterexample` kernel-checks
  `AAACC → AAAAC`, ratio `1125/512`, on the literal full type space; same-length,
  so inclusion transfers.
- **F3** — `AssemblyP1.SameLengthSection62Counterexample` kernel-checks
  `AAATAT → AAAAAT` (`lik obs dS < lik obs dD`, `exactLik` ratio `3`) and
  `AssemblyP1.Section62BridgingCounterexample` kernel-checks `AAATT → AAAATT`
  (`9/8`). The explicit §6.2 bidirected-graph / transitive-reduction / balance /
  supersource-sink checks are verified computation (`section62-mb09-bidirected-
  graph-audit.md`), not kernel-checked. Both competitors are spelled circuits,
  i.e. special §6.2 flows.
- **F4** — follows from F3 by `spelled ⊆ F_flow`; the branch audit
  `mb09-se62-relations-independent-audit-2026-09-20.md` §6 (not on `main`)
  records that a genuinely non-spellable flow is *not* needed for the
  refutation but that the candidate-set-inclusion transfer into `F_flow(R)`
  must use a witness that is itself flow-feasible (F3's are).

### 3.2 What the annotations do to the status

- **Conclusion schema.** F1–F4 are strict-inequality witnesses, so they refute
  `W` and therefore `S` for every genome equivalence and every tie convention
  (`equivalence-and-tie-wellposedness.md` Fact 5;
  `conclusion-semantics-strict-witness-robustness.md` §3). The conclusion
  schema is therefore **not** a blocker.
- **Regime.** `issue36-finite-vs-asymptotic-regime.md` (branch-only) shows the
  sentence is literally per-instance and that F1–F3 are low-coverage phenomena:
  under fixed candidate length the truth's `L`-spectrum is a.s. the unique
  large-`n` maximizer, while `S^k` ties the exact multinomial for every sample.
  The matrix rows are therefore per-instance; the regime is a separate source
  choice, not a cell of the finite proposition.

## 4. Which cells remain open

Filtering §5's exclusions, the only definite finite peers not closed are F5 and
F6, plus the non-finite F7.

| Open cell | Materially source-supported? | Why still open |
|---|---|---|
| F5 strict oriented indexing | yes, by the literal §6.1 text ("There are `4^k` such variables") and Shomorony's oriented model | bounded-zero only; the §6.2 witnesses depend on reverse-complement collapse and *invert* (`D`'s oriented factor is `0`) under oriented indexing |
| F6 per-occurrence `d ≥ x` | **no** — main states it is strictly stronger than the source's per-vertex lower bound `1` | bounded-zero; not the §6.2 definition |
| F7 broad principle | yes, as the safest literal reading of the sentence | no objective is fixed, so no witness can refute it |

## 5. Excluded axis values (to avoid an invented product)

- **Identity-indexed overlap-graph vertices** (one vertex per read identity
  rather than per molecule) are a repository variant that contradicts §6.2's
  `d_i =` vertex-flow identification; the branch audit `mb09-se62-relations-
  independent-audit-2026-09-20.md` §6 (not on `main`) excludes them from the
  source-faithful set.
- **Reverse-complement equivalence under oriented read types** is not
  source-supported; `equivalence-and-tie-wellposedness.md` Fact 4 makes the
  read type and the equivalence one coupled choice, not a free cross-product.
- **Coarser genome equivalences** identifying different-composition words have
  no source support (`conclusion-semantics-determination.md` §2.4).
- **Per-occurrence lower bound** is not the source condition (F6), so it is not
  a source-faithful peer, though it is recorded because main calls it open.

## 6. The single most important remaining cell

**F5 — the strict oriented (`4^k`) / single-strand indexing of the §6.1–§6.2
objective.** It is the only definite, materially source-grounded finite
formulation that is neither closed negatively nor excluded as non-source.

Reasons it is load-bearing for issue #45:

1. **It is the literal §6.1 text.** MB09 §6.1 writes "There are `4^k` such
   variables"; `4^k` is the oriented `k`-mer count, not the reverse-complement
   class count `(4^k + p_k)/2`. `mb09-se61-index-orientation-resolution.md` §1.2
   records this as a source fact and §3 resolves the fork in favour of molecule
   classes only as a **source-supported inference** (from §6.2's `d_i =` vertex
   flow). The source-internal tension is still in main's unresolved register
   (`conclusion-semantics-determination.md` §3 item 5).
2. **Main's §6.2 closure does not transfer.** The F3/F4 witnesses exist only
   through reverse-complement collapse (`ATT ~ AAT`, `TTA ~ TAA`, `TAT ~ ATA`);
   under strict oriented indexing the competitor loses an observed window and
   its likelihood factor is `0` (`mb09-se61-index-orientation-resolution.md`
   §4). The bounded zero at `G ≤ 6, L = 3` is evidence, not a proof of absence
   (`bridging-se62-flow-ml-counterexample.md` §7, §10).
3. **It is coupled to the equivalence axis.** If F5 is the panel, the genome
   equivalence is cyclic-shift-only; if the molecule panel is, it is dihedral.
   The read-type convention and the equivalence are one choice
   (`equivalence-and-tie-wellposedness.md` Fact 4), so F5 cannot be dismissed
   as a technicality while the equivalence is also undecided.
4. **It is a finite proposition.** Unlike F7, F5 can in principle be settled by
   a kernel-checked strict witness or by a proof; #45's entry condition speaks
   of finite formulations.

**Second-order caveat (not the named cell, but it gates the matrix).** F7, the
broad "maximum-likelihood formulation" family, is the strongest *literal*
textual fit of the 2016 sentence (`shomorony-mb-formulation-provenance.md`
§6.5) and is not a definite finite proposition. No further counterexample can
close it. If #45's entry condition is read as requiring F7 to be settled, then
the true blocker is a **source-level referent commitment** (best operational fit:
reading (2), already closed by F2), not a mathematical cell. This note
recommends that F7 be treated as outside the finite-formulation set, and that the
entry judgement rest on the definite rows F1–F6, of which only F5 remains.

## 7. What settling F5 would require

Either:

1. a kernel-checkable strict §6.2 (or §6.1) witness whose truth and competitor
   both remain admissible under strict oriented indexing — which must overcome
   the fact that the molecule-class mechanism that powers F3/F4 disappears; or
2. a source argument that strict oriented indexing cannot be the panel for
   *any* §6.2 reading (strengthening `mb09-se61-index-orientation-resolution.md`
   from source-supported inference to a forced reading), which would retire F5
   and make the definite finite set closed.

F6 can be retired independently by recording that it is a repository
strengthening, not a source reading (already stated on main).

## 8. Evidence not yet on `main` that bears on this matrix

Recorded here so the orchestrator does not mistake `main`'s state for the
frontier. None of the following is on `origin/main` at `8b2f0fc`:

- `analysis/issue36-nonspellable-flow-cex-0920` claims a genuinely
  non-spellable `F_flow` witness (`S = 001011`, `L = 4`, ratio
  `2278125/1048576`), which would strengthen F4 but is not needed for its
  refutation.
- `analysis/uniform-strand-search-2026-09-20` records the single-strand
  bounded-zero search (F5's evidence).
- `analysis/issue36-finite-vs-asymptotic-regime-0920` records the regime fork
  and the high-coverage positive behaviour.
- `analysis/issue36-se62-necessity` / `se62-feasibility-necessity-
  determination.md` argues §6.2 feasibility is not necessary to settle the 2016
  question; if accepted, it would remove F3–F6 from the entry-condition set and
  narrow the finite matrix to F1–F2 (both closed), which would satisfy #45's
  entry condition for the definite readings.

## 9. Epistemic classification

| Claim | Status |
|---|---|
| F1, F2, F3 are closed negatively by kernel-checked strict witnesses | kernel-checked (modules in §3.1) |
| F4 closes on `main` by `spelled ⊆ F_flow` from F3 | modeling fact + mathematical fact |
| F3/F4's §6.2 graph/flow certificates are verified computation, not kernel-checked | verified computation |
| F5 is open with bounded-zero evidence only | open (main `bridging-se62-flow-ml-counterexample.md` §7, §10) |
| F6 is open but is not the source condition | open + source fact |
| F7 is not a definite finite proposition | source gap / interpretation |
| Strict witnesses are equivalence-proof | mathematical fact (`conclusion-semantics-strict-witness-robustness.md` §3) |
| F5 is the single most important remaining definite finite cell | interpretation (this note, §6) |
| The regime and the referent remain live source forks | source gap (`conclusion-semantics-determination.md` §3; branch-only regime note) |

## 10. Cross-references

- Referent/objective: `source-notes/mb-formulation-referent-reconciliation.md`,
  `source-notes/shomorony-mb-formulation-provenance.md`,
  `source-notes/medvedev-brudno-candidate-class.md`.
- Read-type / index fork: `source-notes/mb09-se61-index-orientation-
  resolution.md`, `source-notes/equivalence-and-tie-wellposedness.md`.
- Conclusion schema: `source-notes/conclusion-semantics-determination.md`,
  `source-notes/conclusion-semantics-strict-witness-robustness.md`,
  `literature/ml-tie-semantics.md`.
- Witnesses: `fixed-length-exact-counterexample.md`,
  `fixed-length-binomial-counterexample.md`,
  `section62-same-length-bidirected-counterexample.md`,
  `bridging-se62-flow-ml-counterexample.md`, `exact-variant-e-counterexample.md`.
- §6.2 structure: `section62-mb09-bidirected-graph-audit.md`;
  branch `audit/mb09-se62-relations-2026-09-20`
  `source-notes/mb09-se62-relations-independent-audit-2026-09-20.md`.
- Issue #45: `docs/intent-records/project.md` `$id-9018427365142097`.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`;
Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`; Guy
Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high throughput
shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18 (2013), DOI
`10.1186/1471-2105-14-S5-S18`; Mohammadreza Ghodsi, *Constructing a genome
assembly that has the maximum likelihood*, arXiv:1302.4391v3.
