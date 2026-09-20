# A same-length Section 6.2 bridging counterexample: `AAATAT → AAAAAT`

_Status: independent from-scratch computation + source reading + kernel-checked
finite certificate, 2026-09-20. All claims are labelled **source fact**,
**mathematical argument**, **verified computation**, **kernel-checked**, or
**open**. This note does not settle which Medvedev–Brudno (2009) object the
Shomorony et al. (2016) sentence intends; it closes the fixed-length /
same-length residue of the §6.2 flow-restricted statement under the source's
per-vertex lower bound._

_Reproduction:_

```sh
python3 scripts/verify_samelength_se62_counterexample.py           # witness
python3 scripts/verify_samelength_se62_counterexample.py --search  # + bounded search
lake build AssemblyP1.SameLengthSection62Counterexample
```

_The Python script is self-contained, exact (`fractions.Fraction`),
deterministic, and exits non-zero on any failed assertion. The Lean module
contains no `sorry`, `axiom`, `admit`, or `native_decide`; its main theorem
depends only on `propext`, `Classical.choice`, and `Quot.sound`._

---

## 0. Verdict at a glance

The well-posed same-length statement

> **(P_fix)** `I_s` holds **and** the truth-induced flow is an admissible MB09
> §6.2 candidate **and** the competing candidate is a single spelled molecule
> `D` with `|D| = |S|` ⇒ the truth-induced flow maximizes the §6.1 objective,

is **false** under the source's §6.2 reading (vertices are read DNA molecules,
vertex lower bound `1`, spelled circuit). The witness is

```text
alphabet          {A, T}, reverse-complement involution A <-> T
truth             S = AAATAT          (G = 6)
read length       L = 3
realized starts   (0, 0, 1, 3, 5)     (n = 5 reads; start 0 sampled twice)
external size     N = |S| = 6
observed          x = { AAA:2, AAT:1, ATA:1, TAA:1 }
truth spectrum    d_S = { AAA:1, AAT:1, ATA:3, TAA:1 }
competitor        D = AAAAAT          (|D| = 6, SAME LENGTH)
competitor spec   d_D = { AAA:3, AAT:1, ATA:1, TAA:1 }
```

`I_s` holds; both `S` and `D` induce admissible §6.2 bidirected circuits on the
transitively reduced read-overlap graph (support equality, vertex lower bound
`1`, edge lower bounds `0`, zero read-vertex balance, no supersource/sink); and
both same-length objectives strictly improve:

```text
exact candidate-intrinsic multinomial    L_exact(D)/L_exact(S) = 3
literal §6.1 fixed-N product of binomials L_6.1(D)/L_6.1(S)    = 5
```

Unlike the merged `AAATT → AAAATT` witness, the competitor here has the **same
length** as the truth (`|D| = |S| = 6`). [verified computation + kernel-checked]

---

## 1. Source semantics

### 1.1 Medvedev–Brudno §6.2 (source fact)

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2,
PMC3154397.

- §3.1: "A DNA molecule is an unordered pair of strings (also called strands)
  that are reverse complements of each other."
- §4.1: "each `k`-molecule is represented only once."
- §6.2: vertices are the reads, "which are DNA molecules"; "each vertex has a
  lower bound of `1` since it represents a read that must be present in the
  genome at least once"; the genome is a circuit, while a general feasible flow
  is a "(non-contiguous) assembly".
- Observation 7: the number of visits of a walk to a read vertex equals the
  number of times that read appears as a submolecule of the spelled molecule.

Consequently (**source-supported inference**): a duplicated observed molecule
is a *single* vertex, the observed multiplicity `x_w` enters only the §6.1
likelihood, and the lower bound is **per vertex** — a spelled candidate must
contain every observed read molecule at least once. For a spelled molecule this
is exactly **support equality**: `supp(spec_L(D)) = supp(x)`.

**Recorded source tension.** §6.1 also writes "There are `4^k` such variables",
i.e. its index set is *oriented* `k`-mers, while the same sentence calls the
variable a `k`-molecule and `d_i` "the number of times the `k`-molecule `i`
appears in `D`". This note (like the merged
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md))
uses the bidirected / molecule-class index set, which is the one §6.2 forces;
under a strict oriented single-strand indexing the truth's support would not
match `x` and this witness would not apply. The oriented reading is a separate,
unresolved source fork; the single-strand control row in §3 records the bounded
zero for it.

The repository must keep the readings distinct. Requiring in addition
`d_D(w) ≥ x_w` for every observed type (the *per-occurrence* strengthening) is
strictly stronger than the source's per-vertex lower bound, and is **not** the
§6.2 definition. Under that strengthening the truth of this witness is not a
candidate at all (`d_S(AAA) = 1 < x_AAA = 2`), and the fixed-length residue
remains **open** in the searched scope. See
[`source-notes/same-length-witnesses-candidate-set-inclusion.md`](source-notes/same-length-witnesses-candidate-set-inclusion.md)
for the reading split and
[`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md)
for the graph/flow definitions.

### 1.2 Shomorony `I_s` (source fact)

Shomorony, Kim, Courtade, Tse (2016), Eq. (1), attributed to Bresler, Bresler &
Tse (2013): a read realization `R ∈ I_s` iff it covers the circular truth,
every triple repeat is all-bridged, and every interleaved repeat pair is
bridged. A copy at `t` of a repeat of length `ℓ` is bridged by a read occupying
`[r, r+L)` iff `r < t` and `t + ℓ < r + L`. A pair of interleaved repeats is
bridged iff at least one of the two repeats is bridged, i.e. at least one of the
four selected copies is bridged. These are recorded and sourced in
[`bridging-source-semantics.md`](bridging-source-semantics.md).

---

## 2. Independent verification

The witness was found and checked by a from-scratch script that shares no code
with the repository's existing searches. It:

1. recomputes the windows, molecule classes, `x`, `d_S`, `d_D`;
2. re-checks `I_s` (coverage, all-bridged triple repeats, bridged interleaved
   pairs);
3. builds the explicit bidirected overlap graph on the observed molecules at
   `o_min = L−1 = 2` (MB09 §3.3 four strand-overlap cases), enumerating every
   edge with its incidence signs;
4. verifies that the cyclic window walks of both `S` and `D` are genuine
   bidirected circuits: every step is a real edge, consecutive edges have
   opposite orientations at every interior vertex, every read vertex has flow
   `≥ 1`, all read-vertex balances are `0`, and no supersource/supersink edge is
   used;
5. checks that neither the literal "spelled by two shorter overlaps" nor the
   Myers longer-overlap transitive reduction removes any employed edge (every
   employed edge has overlap `L−1 = 2`, irreducible);
6. evaluates both same-length objectives exactly.

The script exits non-zero on any failure.

### 2.1 Correcting the earlier bridging prose

An earlier unmerged note
(`integration/issue36-final:docs/section62-fixed-length-bidirected-counterexample.md`)
claimed the interleaving conjunct was vacuous for this truth. That is wrong:
the maximal repeat pairs `A@{0,2}` and `A@{1,4}` have four cyclically
alternating starts, so the pair is interleaved. The condition still holds,
because **both** pairs have bridged copies (reads at starts `5`, `0`, `1`, `3`
bridge the `A` copies `0`, `1`, `2`, `4` respectively). The 4608-witness search
on that branch enforced `I_s` mechanically, so its census is unaffected; only
the prose justification was wrong. This note and the verification script pin
the correct fact. [verified computation]

### 2.2 Kernel check (Lean)

`AssemblyP1/SameLengthSection62Counterexample.lean` kernel-checks, for this
concrete data:

```text
SameLengthSection62Counterexample.samelength_se62_counterexample
  : SourceCertificate ∧ SeqSupport dS obs ∧ SeqSupport dD obs
      ∧ lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3
```

Here `SourceCertificate` is the `I_s` certificate (coverage, all-bridged
maximal triple repeats, bridged interleaved pairs, each decided by explicit
finite enumeration over `Fin 6`), `SeqSupport` is the §6.2 spelled-circuit
feasibility predicate (support equality / per-vertex lower bound `1`), `lik` is
the literal §6.1 product of binomial marginals with `N = 6`, `n = 5`, and
`exactLik` is the same-length exact multinomial up to cancelled constants. The
main theorem depends only on the three standard Lean axioms.

The grid-level certificate (explicit graph, transitive reduction, incidences,
balance, supersource/sink) is checked by the Python script, not reproduced in
Lean, exactly as in the merged
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md).

---

## 3. Bounded exhaustive search

`scripts/verify_samelength_se62_counterexample.py --search` runs an exhaustive
search over a stated scope. A read realization is a multiplicity vector over
starts (each entry `0..maxmul`); `I_s` must hold; the truth's own walk must be
admissible (support equality); a competitor is a length-`G` molecule with the
same support that strictly improves either objective.

| reading / lower bound | `G` | `L` | `maxmul` | instances | same-length beats |
|---|---|---|---|---|---|
| bidirected, per-vertex (`supp` equality) | 5 | 3 | 3 | 2070 | **0** |
| bidirected, per-vertex | **6** | **3** | 3 | 10854 | **45** |
| bidirected, per-vertex | 7 | 3 | 3 | 17226 | **0** |
| bidirected, per-vertex | 6 | 4 | 3 | 10611 | **0** |
| single-strand, per-vertex | 6 | 3 | 2 | 2420 | **0** |
| bidirected, per-occurrence (`d ≥ x`) | 6 | 3 | 2 | 667 | **0** |

Every same-length beat in scope is the rotation/complement orbit of the single
pair `AAATAT → AAAAAT`; with `maxmul = 4` the exact-multinomial ratios take the
values `{3, 9, 27}` (binomial `{5, 25, 125}`), matching the multiplicities. The
zero rows are computational evidence bounded by the stated scope, **not** a
proof of absence. The single-strand and per-occurrence rows are controls: both
remove the mechanism (reverse-complement collapse; candidate reuse of a
duplicated observation), consistent with the merged note's
[`§6`](bridging-se62-flow-ml-counterexample.md) bounded-search record.
[verified computation, bounded]

---

## 4. Relation to existing repository results

| Existing claim | Location | Status after this note |
|---|---|---|
| Fixed-length `\|D\|=N` sub-case **open** (bounded zero evidence) | `main`, [`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md) §10.2 | **refuted under the source per-vertex reading** by the same-length witness; open under the per-occurrence strengthening |
| Variable-length `AAATT → AAAATT`, ratio `9/8` | `main`, same note | unchanged; this witness has equal lengths and does not need the variable-length candidate |
| No current witness has both truth and competitor sequence-level §6.2-feasible | `main`, [`source-notes/same-length-witnesses-candidate-set-inclusion.md`](source-notes/same-length-witnesses-candidate-set-inclusion.md) §5 | **false under the per-vertex reading**: this same-length pair is sequence-level §6.2-feasible for both molecules; true under the per-occurrence strengthening |
| Fixed-length binomial/exact witnesses `AAACC → AAAAC`, `AAABB → AAAAB`, … | `main`, [`fixed-length-binomial-counterexample.md`](fixed-length-binomial-counterexample.md), [`fixed-length-exact-counterexample.md`](fixed-length-exact-counterexample.md) | unchanged; those target the sequence-level exact/binomial objectives without §6.2 graph feasibility |
| Unmerged fixed-length §6.2 witness `AAATAT → AAAAAT` (per-type) | `integration/issue36-final` | independently reproduced and kernel-checked here; the interleaving-vacuity prose corrected in §2.1 |

---

## 5. Why it works

The mechanism uses only source-level features:

1. **Reverse complementarity creates multiplicity.** A molecule can contain more
   copies of a read *molecule class* than the number of distinct times that
   class was sampled: here `TAT ~ ATA`, so `d_S(ATA) = 3`.
2. **Per-vertex lower bound is support equality.** Under the source reading, any
   molecule sharing the support is admissible regardless of how multiplicity is
   distributed; the truth `d_S(AAA) = 1` is admissible even though `AAA` was
   sampled twice.
3. **The objective can then be improved at the same length.** Since the
   candidate and the truth have the same length, their spectra have equal total
   mass; moving one unit of multiplicity from the over-represented `ATA` to the
   observed-heavy `AAA` raises the exact factor from `1·3` to `3·1` and the §6.1
   product accordingly. (`n = 5 < N = 6` is what makes the observation-heavy
   coordinate strictly improve.)

---

## 6. What this does and does not settle

**Does.** It shows that under the MB09 §6.2 reading in which the truth-induced
flow is an admissible candidate and reads are reverse-complement molecules, the
**same-length** implication fails: a spelled competitor `D` with `|D| = |S|`
strictly improves both relevant objectives. This closes the fixed-length residue
left open on `main`.

**Does not.** It does not settle which Medvedev–Brudno object the 2016 sentence
intends; it does not address the per-occurrence strengthening (still open in
scope) or the single-strand reading (zero in scope); and it does not address the
tie/equivalence semantics. The genuinely non-spellable §6.2 flow case is treated
elsewhere (`agent/issue36-literal-flow-search-0920`).

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| §6.2 object, per-vertex lower bound `1`, reads are molecule classes, `k`-molecules represented once | **source fact** (MB09 §3.1, §4.1, §6.2, Observation 7) |
| per-vertex lower bound is the source condition; per-occurrence `d ≥ x` is a strengthening | **source-supported inference** |
| spelled-circuit §6.2 feasibility = support equality (for a spelled molecule) | **mathematical argument** (Observation 7) |
| `S = AAATAT`, `D = AAAAAT` witness: `I_s`, both §6.2 circuits, same length, exact ratio `3`, binomial ratio `5` | **verified computation** + **kernel-checked** |
| interleaving conjunct is non-vacuous and satisfied (earlier prose wrong) | **verified computation** |
| same-length beats exist only at `(G,L) = (6,3)` in the stated scope | **verified computation**, bounded |
| `(P_fix)` is false under the source per-vertex reading | **follows** |
| `(P_fix)` under the per-occurrence strengthening | **open** (bounded zero evidence) |
| `(P_fix)` under single-strand | **open** (bounded zero evidence) |
| which §6.1/§6.2 object the 2016 sentence intends | **source interpretation, unresolved** |

---

## 8. Reproduce

```sh
python3 scripts/verify_samelength_se62_counterexample.py
python3 scripts/verify_samelength_se62_counterexample.py --search
lake build AssemblyP1.SameLengthSection62Counterexample
```

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2,
PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1) and §5.
