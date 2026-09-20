# Bridging conditions do not force the truth-induced §6.2 flow to be maximum-likelihood: a sequence-level counterexample

_Status: source reading + mathematical argument + exact-rational certificate,
2026-09-20. Independent of the computational-search and source-audit packets.
All claims are labelled **source fact**, **mathematical argument**,
**verified computation**, **conjecture**, or **open**._

_Reproduction: `python3 scripts/verify_se62_bridging_flow_counterexample.py`
(self-contained, exact `fractions.Fraction`, deterministic, under a second;
exits non-zero on any assertion failure)._

_Relation to prior work: this note resolves, in the negative, the
per-occurrence variable-length case left **open** by the issue-#36 branch
`analysis/issue36-nonspellable-broader`
(`docs/section62-fixed-length-bidirected-counterexample.md` §7.1 and
`docs/section62-bidirected-flow-feasibility.md` §6). It does not settle which
Medvedev–Brudno object the 2016 sentence intends._

---

## 0. Verdict at a glance

The well-posed source-faithful statement

> **(P)** `I_s` holds **and** the truth-induced flow is an admissible MB09 §6.2
> candidate ⇒ the truth-induced flow maximizes the §6.1 objective over the
> §6.2 feasible set,

is **false** under the Section 6.2 reading in which vertices are read molecules
(bidirected / reverse-complement reading) and the lower bound `1` is
per-occurrence.

The witness is

```text
alphabet          {A, T}, reverse-complement involution A <-> T
truth             S = AAATT          (G = 5)
read length       L = 3
realized starts   (0, 1, 4)          (n = 3 reads)
external size     N = |S| = 5
observed          x = { AAA:1, AAT:1, TAA:1 }        (read-molecule classes)
truth spectrum    d_S = { AAA:2, AAT:2, TAA:1 }      (|S| = 5)
competitor        D = AAAATT         (|D| = 6)
competitor spec   d_D = { AAA:2, AAT:2, TAA:2 }      (|D| = 6)
```

`I_s` holds; both `S` and `D` are sequence-level §6.2 feasible (their window
supports both equal `supp(x)`, and both dominate `x` per occurrence); each is a
spelled cyclic molecule, hence a §6.2 circuit; and the literal §6.1
product-of-binomial-marginals objective with external `N = 5` satisfies

```text
L_{6.1}(D) / L_{6.1}(S) = 9/8 > 1.
```

So bridging does **not** force the truth-induced flow to be ML under this
reading. [mathematical argument + verified computation]

Two boundaries are emphasized:

1. **Candidate length.** `|D| = 6 ≠ N = 5`. Section 6.2 does not constrain the
   candidate-flow length; `N` enters only as the binomial denominator and the
   domain bound `d_i ≤ N` (both satisfied: `max d = 2 < 5`). If one *adds* the
   fixed-length restriction `|D| = N`, this witness does not apply and that
   sub-case is left **open** here (and was open in the cited branch).
2. **Strand reading.** The witness uses the involution `A ↔ T`. Under the
   single-strand reading the bounded search found no non-degenerate witness in
   the searched scope (§6); the mechanism in §4 needs the reverse-complement
   collapse.

---

## 1. The source objects, stated separately

### 1.1 Shomorony `I_s` (source fact)

Shomorony, Kim, Courtade, Tse (2016), Eq. (1) (as reconstructed in
`docs/bridging-source-semantics.md`), attributed to Bresler–Bresler–Tse (2013):

`R ∈ I_s` iff

1. `R` covers the circular truth `S` (every position lies in some read);
2. every **triple repeat** of `S` is **all-bridged**; and
3. every **interleaved repeat pair** of `S` has at least one constituent copy
   **bridged**.

A copy at `t` of a repeat of length `l` is bridged by a read occupying
`[r, r+L)` iff `r < t` and `t + l < r + L` on the integer lift. These are
properties of `(S, R)` only; they mention no competitor. [source fact]

The 2016 sentence at issue is: “Understanding whether bridging conditions can
be used to guarantee that the maximum-likelihood sequence is the true sequence
is currently an open question.” The paper gives no section, equation, or
formula for “the maximum-likelihood formulation of the AP (Medvedev and Brudno,
2009)”; that phrase’s denotation is a recorded source ambiguity
(`docs/source-notes/shomorony-mb-formulation-provenance.md`). [source fact]

### 1.2 Medvedev–Brudno §6.1 objective (source fact)

Medvedev–Brudno (2009), §6.1, PMC3154397: for a circular candidate `D`,
`d_i` = number of occurrences of `k`-molecule `i` in `D`, observed counts `x_i`
among `n` reads, and external known genome size `N`, the tractable objective is
the product of the per-type binomial marginals

```text
∏_i  C(n, x_i) (d_i / N)^{x_i} (1 − d_i / N)^{n − x_i},      0 ≤ d_i ≤ N.
```

The paper explicitly replaces the candidate-intrinsic length `N(D)` by the
external `N` and assumes the genome size is known. [source fact]

### 1.3 Medvedev–Brudno §6.2 feasible objects (source fact)

Medvedev–Brudno (2009), §6.2: the candidate object is a convex min-cost
**bidirected flow** on the transitively reduced read-overlap graph, whose

- vertices are the reads, which “are DNA molecules”;
- every read vertex has lower bound `1`, all other lower bounds `0`, all upper
  bounds infinity;
- flow represents “a (non-contiguous) assembly of the genome”; and
- Observation 7 identifies the flow through a read vertex with the number of
  times that read occurs in the assembled molecule.

[source fact]

---

## 2. The well-posed statement (P) and the sequence-level feasibility criterion

Because §6.2’s candidates are *flows*, the truth is a candidate only if its
window walk is a legal flow. The branch analysis
`docs/section62-bidirected-flow-feasibility.md` §2 derives (from Observation 7
and the consecutive-window overlap, and the fact that transitive reduction
preserves spelled molecules) the criterion:

> A circular molecule `D` is **sequence-level §6.2 feasible** with respect to the
> observed read-molecule multiset `x` iff
> **(1)** `supp(spec_L(D)) = supp(x)`, and
> **(2)** `d_D(w) ≥ x_w` for every observed type `w` (per-occurrence lower bound).

The proof is short: necessity is Observation 7 plus the lower bound `1` at each
read occurrence; sufficiency is the cyclic window walk, whose consecutive
windows overlap in `L−1` symbols. [mathematical argument; citation, not
re-derived here]

With that criterion, the precise statement under test is:

> **(P)** For every finite instance `(S, R)` with `R ∈ I_s` for which the truth
> `S` is sequence-level §6.2 feasible, and every sequence-level §6.2 feasible
> `D`, `L_{6.1}(D) ≤ L_{6.1}(S)`.

Statement (P) is the natural formalization of “bridging guarantees the
maximum-likelihood sequence is the true sequence” once the §6.2 flow layer is
fixed. [modeling choice]

---

## 3. The counterexample, verified

Take the alphabet `{A, T}` with involution `A ↔ T`; a window’s **molecule
class** is the lexicographically smaller of the word and its reverse
complement.

```text
S = AAATT,  L = 3,  starts = (0, 1, 4)
```

Circular windows of `S` (length-5, positions `0..4`):

| start | window | molecule class |
|---|---|---|
| 0 | `AAA` | `AAA` |
| 1 | `AAT` | `AAT` |
| 2 | `ATT` | `AAT` |
| 3 | `TTT` | `AAA` |
| 4 | `TAA` | `TAA` |

So `d_S = {AAA:2, AAT:2, TAA:1}` and the realized reads at `(0,1,4)` give
`x = {AAA:1, AAT:1, TAA:1}`. [verified computation]

### 3.1 `I_s` holds

- **Coverage.** Starts `0,1,4` cover positions `{0,1,2} ∪ {1,2,3} ∪ {4,0,1} =
  {0,1,2,3,4}`. [verified computation]
- **Triple repeat.** `S` has one maximal triple repeat: length-1 `A` at
  positions `{0,1,2}` (preceding symbols `T,A,A` not all equal; following
  symbols `A,A,T` not all equal). Each copy is bridged by a realized read:
  copy `0` by the read at `4` (covers `4,0,1`), copy `1` by the read at `0`
  (covers `1,2,3`), copy `2` by the read at `1`. [verified computation]
- **Interleaved repeats.** The maximal repeat pairs are the `A` copies and the
  length-2 pair `AA@(0,1)`; no two have four cyclically alternating starts, so
  the interleaving conjunct is vacuous. [verified computation]

### 3.2 Both `S` and `D` are sequence-level §6.2 feasible

For `D = AAAATT` (length 6):

| start | window | molecule class |
|---|---|---|
| 0 | `AAA` | `AAA` |
| 1 | `AAA` | `AAA` |
| 2 | `AAT` | `AAT` |
| 3 | `ATT` | `AAT` |
| 4 | `TTA` | `TAA` |
| 5 | `TAA` | `TAA` |

So `d_D = {AAA:2, AAT:2, TAA:2}`. Hence `supp(spec_3(S)) = supp(spec_3(D)) =
supp(x) = {AAA, AAT, TAA}`, and `d_S(w), d_D(w) ≥ x_w` for each observed `w`.
Both `S` and `D` are spelled by their cyclic length-3 window walks
(consecutive windows overlap in `L−1 = 2` symbols), each visiting all three
observed read-molecule vertices. [verified computation]

Note the collapse that makes the truth feasible: `ATT ~ AAT` and `TTT ~ AAA`
under `A ↔ T`, so `S`’s spectrum support is exactly the three observed classes
even though `S` also contains the (non-observed as such) words `ATT`, `TTT`.

### 3.3 The competitor strictly wins

Under the literal §6.1 product, with `n = 3`, `N = 5`:

```text
w = AAA, x_w = 1:  φ(D)/φ(S) = [(2/5)(3/5)^2] / [(1/5)(4/5)^2] = (18/125)/(16/125) = 9/8
w = AAT, x_w = 1:  d_D = d_S = 2                              ⇒ factor 1
w = TAA, x_w = 1:  d_D = d_S = 2                              ⇒ factor 1
```

Both spectra have the same support as `x`, so no unobserved type has positive
multiplicity in either molecule and all zero-count factors are `1` for both.
Hence the **full** literal §6.1 ratio (zero-count factors retained) is

```text
L_{6.1}(D) / L_{6.1}(S) = 9/8 > 1.
```

[mathematical argument + verified computation]

Therefore `S` is not a §6.1 maximizer over the §6.2 feasible set, and (P) is
false. The competitor is a single spelled molecule, which is a special case of
a §6.2 flow; so the refutation is stronger than one using a genuinely
non-contiguous assembly.

### 3.4 Kernel check (Lean)

The finite instance is kernel-checked in
`AssemblyP1/Section62BridgingCounterexample.lean`, whose main theorem

```text
AssemblyP1.Section62BridgingCounterexample.se62_bridging_flow_counterexample
  : SourceCertificate ∧ Feasible dS obs ∧ Feasible dD obs ∧ lik obs dS < lik obs dD
```

proves, for the concrete data above: the `I_s` certificate (`Covers`,
`TripleAllBridged`, and `¬ HasInterleaving`, the last by explicit finite
enumeration), sequence-level §6.2 feasibility of both `S` and `D` (support
equality plus per-occurrence lower bounds over the `Fin 8` molecule-class
space), and the strict likelihood inequality. The `§6.1` product is reduced to
the three-element class support and evaluated with `norm_num`; the file contains
no `sorry`, `axiom`, `admit`, or `native_decide`, and the main theorem depends
only on the three standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). [verified computation, kernel-checked]

---

## 4. Why it works (mechanism)

The mechanism is structural and uses only source-level features:

1. **Reverse complementarity creates multiplicity.** A molecule can contain
   more copies of a read *molecule class* than the number of times that class
   was sampled, because a window and the reverse complement of another window
   coincide. Here `ATT ~ AAT` and `TTT ~ AAA`.
2. **Per-occurrence lower bounds under `n < N`.** With `n = 3 < N = 5` reads,
   per-occurrence feasibility does not force `d_S = x` (that collapse needs
   `n = N = G`; see `docs/section62-conditional-conservation-lemma.md` §2). Here
   `S` is feasible (`d_S ≥ x`) with genuine slack in `AAT` and `TAA`.
3. **Support equality permits reallocation.** Since feasibility is support
   equality plus lower bounds, `D` may move units of multiplicity onto an
   observed type with `x_w > 0` while keeping the same support. Increasing
   `d(AAA)` from `1` to `2` multiplies that type’s §6.1 factor by `9/8`, and the
   other two types are unchanged.

The same mechanism, at `G = 6`, gives further witnesses (e.g. `S = AAATAT`,
`D = AAAATAT`, ratio `128/125`); the `G = 5` instance is the smallest with a
clean integer ratio. [verified computation, bounded]

---

## 5. Relation to existing repository results

| Existing claim | Location | Status after this note |
|---|---|---|
| Fixed-length §6.2 statement false under bidirected **per-type** lower bound (`S = AAATAT`, `D = AAAAAT`, ratio 3) | issue-#36 branch `analysis/issue36-nonspellable-broader`, `docs/section62-fixed-length-bidirected-counterexample.md` | unchanged |
| §6.2 statement **open under per-occurrence**, bounded zero counterexamples | same, §7.1 | **resolved negatively** in the variable-length case by §3 here |
| No sequence-level §6.2 counterexample over 85 572 instances | `docs/section62-bidirected-flow-feasibility.md` §5 | explained: that search fixed `n = |S| = N`; the collapse there is the `n = N` slice, not bridging |
| `I_s` unused in the `n = N` slice collapse | `docs/section62-conditional-conservation-lemma.md` §2, Theorem 3 | consistent: §3 here uses `n ≠ N` |
| Per-occurrence, `I_s`, truth-feasible `AAATT → AAAATT`, ratio 9/8 | `docs/section62-conditional-conservation-lemma.md` §5 (branch commit `03a695e`) | same numerical witness; this note adds the **§6.2 sequence-level** reading, the spelled-circuit checks, and the resolution of the branch’s open item |

The important correction to the branch’s bounded search is analytic, not
computational: for a **per-occurrence** feasible truth one necessarily has
`Σ_w x_w = n ≤ Σ_w d_S(w) = G`, so `n ≤ G`; the interesting regime is
`n < N = G`, which the 85 572-instance search (`n = |S| = N`) did not enter.
The `n = |S| = N` zero count is a theorem (the separable §6.1 objective is
coordinate-wise maximized at `d = x` when `n = N`), not evidence about
bridging. [mathematical argument]

---

## 6. Bounded search context

A small exact enumerator (`scripts/…`; the note’s companion checks the
witness only) was run over the `n < N` regime:

- **Bidirected reading.** Counterexamples exist at `G = 5, L = 3` (minimum
  ratio `9/8`, the §3 witness) and at `G = 6, L = 3` (e.g. `128/125`).
- **Single-strand reading.** No non-constant-truth counterexample was found for
  `G ≤ 6`, `L = 3`, `n < N`, candidate length up to `G + 2`, within the binomial
  domain `d ≤ N`. (Constant truths such as `AAAAA` give apparent witnesses but
  their competitors violate `d ≤ N`, so they are not admissible.) [verified
  computation, bounded; **not** a proof of absence]

The single-strand bounded zero is evidence only and is stated as such.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| Shomorony `I_s` definition and the 2016 open-question sentence | source fact (Shomorony et al. 2016, Eq. (1), §5) |
| MB §6.1 objective and §6.2 bidirected flow | source fact (MB09 §6.1–6.2, PMC3154397) |
| Sequence-level §6.2 feasibility = support equality ∧ per-occurrence lower bound | mathematical argument (branch derivation, Observation 7) |
| `S = AAATT`, `D = AAAATT`: `I_s`; truth and competitor §6.2-feasible; spelled circuits | **kernel-checked** (`AssemblyP1.Section62BridgingCounterexample`), plus verified computation (exact rationals) |
| Literal §6.1 ratio `9/8 > 1` | mathematical argument + **kernel-checked** (`AssemblyP1.Section62BridgingCounterexample`) |
| Statement (P) is false under the bidirected per-occurrence reading | follows |
| Statement (P) under the single-strand reading | **open** (bounded zero evidence) |
| Statement (P) under the fixed-length restriction `|D| = N` | **open** (bounded zero evidence in the branch) |
| Which §6.1/§6.2 object and strand convention the 2016 sentence intends | source ambiguity, unchanged |

---

## 8. What this does and does not settle

**Does.** It shows that under the §6.2 reading in which the truth-induced flow
is an admissible candidate and reads are reverse-complement molecules, `I_s`
does not imply ML-optimality of the truth. This settles the “per-occurrence
variable-length” item left open by the issue-#36 branch, and it removes the
last structural hope that the §6.2 polytope plus bridging alone could force the
truth to be ML.

**Does not.** It does not settle which Medvedev–Brudno object the 2016 sentence
denotes, nor the strand/conclusion conventions (maximizer vs uniqueness up to
equivalence), nor the single-strand and fixed-length sub-cases. Those remain
source/model questions, not consequences of this witness.

---

## 9. Reproduce

```sh
python3 scripts/verify_se62_bridging_flow_counterexample.py
lake build AssemblyP1.Section62BridgingCounterexample
```

The Python script re-derives `x`, `d_S`, `d_D`, the `I_s` certificate, both
sequence-level feasibility claims, both spelled-circuit checks, and the exact
`9/8` ratio; it exits non-zero on any failure and uses only exact
`fractions.Fraction` arithmetic. The Lean module kernel-checks the finite
`I_s` certificate, the two feasibility claims, and the strict likelihood
inequality (see §3.4).

---

## 10. Open questions

1. **Single-strand reading.** Is (P) true in the single-strand per-occurrence
   variable-length regime? The bounded search is consistent with “true” for
   `G ≤ 6`, `L = 3`, but this is not a proof.
2. **Fixed length.** Is (P) true when candidates are restricted to `|D| = N`?
   The branch’s bounded per-occurrence search found zero; the `n < N` regime was
   not systematically covered.
3. **Poincaré / certificate form.** Is there a clean invariant (e.g. a
   potential on the bidirected overlap graph) that characterizes when the
   truth-induced flow is the §6.1 optimum, beyond the complete-spectrum case?
   [conjecture]
