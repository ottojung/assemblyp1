# §6.2 observed-vertex graph objective and the full MB09 §6.1 4^k molecule-class product (#284)

_Status: modeling note for issue #284, 2026-10-14. This note records the
relationship between the §6.2 observed-vertex graph objective and the full
MB09 §6.1 molecule-class product, including the unseen count-zero factors. It
does not prove a new theorem; it documents the adapter that #261/#262 need.

## 1. The two objectives

**MB09 §6.1 product-binomial objective.** For a candidate `D` with complete
molecule-class spectrum `d` (one coordinate per `k`-molecule class), external
genome size `N`, total reads `n`, and observed counts `x`, the separable
binomial approximation is

```text
L_6.1(D | x) = ∏_c C(n, x_c) · (d_c / N)^x_c · (1 − d_c/N)^(n − x_c)
```

The product ranges over the DNA molecule classes `c` (for a `k`-mer read length
`k` over the four-base alphabet). MB09 §6.1 writes `4^k` for the number of these
variables; that is the *oriented* k-mer count, while the unordered
reverse-complement molecule classes of §3.1 number `(4^k + f_k)/2` (about half).
This note uses the **RC-class reading as an explicit modeling decision**, with the
cardinality tension recorded in `section62-global-circular-and-unseen-factor-284.md`
§3; the two readings give different universes and objectives. Classes with `x_c = 0` and
`d_c = 0` contribute the factor `C(n,0)·(0/N)^0·(1−0/N)^n = 1`; these are the
**unseen count-zero factors**. They are retained in the literal product
(`lik` in `AssemblyP1/Section62BridgingCounterexample.lean`,
`Section62NonSpelledFlow.lean`) and eliminated only by the proved reduction
`lik_eq_relevant_prod`, which is valid because each eliminated factor is `1`
(`marginal_eq_one_of_zero`).

**MB09 §6.2 flow objective.** The §6.2 graph is built on the **observed** read
molecule classes: "the vertices of this graph are the reads". The flow feasible
set (`Feasible62`, `Admissible`) quantifies over flows on this observed-vertex
graph, and the throughput vector `d` is indexed by the observed classes. The
§6.2 objective therefore **omits the unseen classes**: a candidate whose
complete spectrum has support outside the observed classes is not representable
as a throughput vector on the observed-vertex graph.

## 2. The full-spectrum adapter

To relate the §6.2 flow objective to the full §6.1 product, an explicit
**full-spectrum adapter** is needed. The adapter extends a §6.2 throughput
vector `d` (indexed by observed classes) to a complete spectrum `d̂` (indexed
by all `4^k` classes) by setting the unseen coordinates to zero:

```text
d̂(c) = d(c)  if c is an observed molecule class
d̂(c) = 0     if c is unseen
```

Under this adapter, the §6.1 product over the full spectrum reduces to the
product over the observed classes, because every unseen class contributes the
count-zero factor `1`. The adapter is the identity on the observed coordinates
and zero on the unseen coordinates; it is **not** a claim that the §6.2 flow
"knows" about the unseen classes, only that the §6.1 objective evaluated on the
adapter spectrum equals the §6.1 objective restricted to the observed classes.

The adapter is **not** automatic: the §6.2 graph objective and the §6.1
product-binomial objective are different objects (a flow feasible set vs. a
likelihood), and the repository's modeling contract
(`docs/ml-formalization-contract.md`, Variant F) requires an explicit
interpretation from a flow to an assembly object before any correspondence is
claimed. The adapter supplies the spectrum-level half of that interpretation.

## 3. What is and is not established

| Claim | Status |
|---|---|
| The §6.1 product ranges over all k-molecule classes, including unseen count-zero factors | **source fact** for the product form (MB09 §6.1); the **RC-class versus oriented-`4^k` index is an explicit repository modeling decision**, not a source fact; formalized for the binary toy (`lik`, `marginal_eq_one_of_zero`, `lik_eq_relevant_prod`) |
| The §6.2 graph objective omits unseen classes | **source fact** (MB09 §6.2: "the vertices of this graph are the reads") |
| The full-spectrum adapter (zero-extension) makes the §6.1 product reduce to the observed-class product | **mathematical proof** (each unseen factor is `1`) |
| A §6.2 feasible flow's adapter spectrum is a §6.1 maximizer | **open** (needs the flow-to-assembly interpretation and the ML maximality classification of #261/#262) |
| The spelling-preserving transitive reduction preserves the §6.2 graph language, including closed (circular) walks | **kernel-checked** (`Section62SpellingReductionCandidate`, `Section62GlobalSpellingPreservation`) for open walks; **new in this branch** (`Section62GlobalCircularCorrespondence`) for the circular seam, total spelled length `G = Σ (readLen − e.len)` (covers `G < readLen`), and reverse-complement intermediates |

## 4. References

- Medvedev–Brudno (2009), §6.1–§6.2,
  <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
- `docs/ml-formalization-contract.md` (Variant F: flow feasible set vs.
  candidate universe).
- `docs/section62-mb09-bidirected-graph-audit.md` (the §6.2 construction).
