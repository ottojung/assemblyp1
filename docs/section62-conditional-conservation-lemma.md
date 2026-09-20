# The conditional conservation lemma under the actual MB09 §6.2 flow constraints (issue #36)

_Status: source reading + mathematical proofs + exact-rational verification,
2026-09-20. Independent reconstruction; does not rely on earlier branch
summaries. All claims are labelled **source fact**, **mathematical proof**,
**verified computation**, **refuted**, or **open**. This note resolves the
"conditional conservation lemma" raised in the issue #36 status comments; it
does not settle the source-ambiguous Shomorony et al. open question._

_Reproduction: `python3 scripts/verify_issue36_conservation_lemma.py`
(self-contained, exact `fractions.Fraction`, deterministic, under a second;
exits non-zero on any assertion failure)._

---

## 0. Verdict at a glance

The "conditional conservation lemma" (issue #36 status comments) is:

> Under the per-occurrence §6.2 reading, if the experiment has
> `n = N = |S| = G` reads, where `N` is the externally known genome size, and
> the truth is feasible (`d_S(w) ≥ x_w` on every observed type), then
> `Σ_w d_S(w) = G = Σ_w x_w` forces `d_S = x`; hence every same-length feasible
> competitor satisfies `d_D = x = d_S`, so no same-length likelihood improvement
> is possible. The residual question was whether MB09's *actual* bidirected-flow
> variables/conservation laws really give that total-count identity.

Verdict, in four parts:

1. **The arithmetic core is TRUE.** In the slice `n = N`, per-occurrence
   feasibility of a length-`N` fully-observed truth forces `d_S = x`, and no
   length-`N` molecule can strictly beat it. [mathematical proof, §2]
2. **It is weaker than what the actual §6.2 constraints give.** Because the
   §6.1 separable binomial is coordinate-wise maximised at `d_w = N x_w / n`,
   when `N = n` its global maximiser over the *entire* §6.2 integer-flow class
   — non-spellable flows, candidate length free, unobserved types included — is
   exactly `x`. So the truth is the unique §6.2 optimum in that slice; no
   conservation and no same-length restriction is needed. [mathematical proof,
   §3]
3. **The "conservation" premise is NOT a §6.2 flow constraint, and the
   flow-level reading is refuted.** The §6.2 constraints are vertex lower bound
   `1`, edge/vertex conservation, and `d_w ≤ N` (binomial domain); there is no
   identity `Σ_w d_w = N` or `= n`. Explicit feasible circulations satisfy
   `Σ_w d_w ≠ N`: `S = ACGT, L = 2, N = 4` admits the value-`2` circulation with
   `Σ_w d_w = 8`, and the issue-#36 witness `S = AAATAT` admits a feasible flow
   with `Σ_w d_w = 5 ≠ N = 6` that beats its truth. [mathematical proof +
   verified computation, §4]
4. **Outside the slice the lemma is FALSE.** With `n ≠ N`, per-occurrence
   feasibility does not force `d_S = x` and a feasible, `I_s`-satisfying truth
   can be strictly beaten: `S = AAATT, G = 5, L = 3, n = 3, N = 5`,
   `D = AAAATT`, §6.1 binomial ratio `9/8`. [verified computation, §5]

The bridging hypothesis `I_s` is used nowhere in parts 1–3; the collapse is a
property of the parameter slice `n = N` and the objective, not of bridging.

---

## 1. The source object and the exact question

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2 (PMC3154397).

**Source facts (§6.1).**

- `D` is a circular genome of length `N(D)`; `d_i` is the number of times the
  `k`-molecule `i` appears in `D`; `n` is the number of reads.
- The exact joint law is multinomial with `p_i = d_i / N(D)`. The paper replaces
  `N(D)` by the externally known true genome length `N` and approximates the
  multinomial by the product of the per-type binomials
  `∏_i C(n, x_i) (d_i/N)^{x_i} (1 − d_i/N)^{n − x_i}`.
- The cost optimised is separable: `c_i(d_i) = −x_i log d_i − (n − x_i) log(N − d_i)`.
  The domain requires `0 ≤ d_i ≤ N`.
- "For our experiments, we assume that the genome size is known" — `N` is the
  known genome *length*, entering the binomial *denominator* and the domain
  bound; it is **not** added as a conservation or total-flow constraint.

**Source facts (§6.2).** The candidate object is a convex min-cost **biflow** on
the transitively reduced bidirected read-overlap graph: vertices are the reads
(DNA molecules), every read vertex has lower bound `1`, all other lower bounds
are `0`, all upper bounds are infinity, and the flow "represents a
(non-contiguous) assembly of the genome". A flow may be a collection of walks;
it is not required to be spelled by a single molecule, and its total vertex
throughput is not constrained.

The question is whether these actual constraints make the conditional
conservation lemma true, and how the known genome size `N` enters.

---

## 2. The arithmetic core: the slice `n = N` collapses the truth

Throughout, `x` is the observed read molecule-count vector, `n = Σ_w x_w`, `N`
is the external genome length, and the (per-occurrence) truth-feasibility
condition is

```text
(1)  supp(d_S) = supp(x)     and     d_S(w) ≥ x_w   for all observed w.
```

**Lemma 1 (per-coordinate §6.1 maximum).** For integers `0 ≤ x ≤ n ≤ N` define
`φ_{x,n,N}(d) = (d/N)^x (1 − d/N)^{n−x}` on `[0, N]`.

- if `0 < x < n`, `log φ` is strictly concave with unique maximiser `d = N x / n`;
- if `x = 0`, `φ` is nonincreasing, maximised at `d = 0`;
- if `x = n`, `φ` is nondecreasing, maximised at `d = N`.

In particular if `n = N` and `0 < x < N`, the integer maximiser is exactly
`d = x`.

_Proof._ `d/dd log φ = x/d − (n−x)/(N−d)`, which vanishes iff
`x(N−d) = (n−x)d` iff `d = N x/n`. The second derivative is
`−x/d² − (n−x)/(N−d)² < 0`, so `log φ` is strictly concave and the stationary
point is the unique maximum. The endpoint cases are immediate; for `n = N` the
stationary point is `N x/N = x`, an integer. ∎

**Lemma 2 (collapse).** If `n = N = G`, `supp(d_S) = supp(x)`, and
`d_S(w) ≥ x_w`, then `d_S = x`.

_Proof._ A length-`G` circular molecule has exactly `G` length-`L` windows
counted with multiplicity, so `Σ_w d_S(w) = G`. Also `Σ_w x_w = n = G`. Hence
`Σ_w (d_S(w) − x_w) = 0` with each summand `≥ 0`, so every summand is `0`. ∎

**Corollary 2′ (same-length no-improvement).** In the hypotheses of Lemma 2, any
length-`N` molecule `D` with `supp(d_D) = supp(x)` and `d_D ≥ x` has
`d_D = x = d_S`, hence binomial ratio exactly `1`. This is precisely the
"conditional conservation lemma" in the slice. [mathematical proof]

Lemma 2 uses only the *molecule* identity `Σ_w d_S(w) = G`; it is not a flow
conservation statement. §4 shows that identity does not survive at the flow
level.

---

## 3. Strengthening: the truth is the global §6.2 optimum in the slice

The §6.1 objective is separable. Therefore the per-coordinate bound of Lemma 1
applies to *every* integer vector `d` in the box, without reference to
spellability, bidirected edges, or conservation.

**Theorem 3 (flow-level slice optimum).** Fix the observed counts `x` and the
external genome length `N = n`. Let the §6.1 objective be extended over all
molecule classes (observed and unobserved), with `0 ≤ d_i ≤ N` and `d_i = 0` for
`i` outside `supp(x)` when the class cannot be produced. Then for every
nonnegative integer vector `d`,

```text
(2)  ∏_i φ_{x_i,n,N}(d_i)  ≤  ∏_i φ_{x_i,n,N}(x_i),
```

with equality iff `d_i = x_i` for `x_i > 0` and `d_i = 0` for `x_i = 0`.

Consequently **every feasible §6.2 flow** — spellable or not, of any length or
total throughput — has objective at most that of `x`. If the truth is an
admissible §6.2 assembly whose molecule spectrum is `x`, then `x` is the unique
§6.2-optimal spectrum and the truth attains it (any other optimum spectrum must
equal `x`; individual assemblies spelling `x` may still be multiple).

_Proof._ The product is coordinate-wise. For `x_i > 0`, Lemma 1 with `n = N`
gives `φ(d_i) ≤ φ(x_i)` with equality iff `d_i = x_i`. For `x_i = 0`
(unobserved), `φ_{0,n,N}(d_i) = (1 − d_i/N)^n ≤ 1 = φ(0)` with equality iff
`d_i = 0`. Multiply. Feasible flows are a subset of the box, so the bound
applies to them. ∎

**Handling of the four delicate points.**

- **Unobserved types.** If the literal full `4^k` product is used, their factors
  are maximised at `d_i = 0`, so including them cannot help any assembly. If the
  §6.2 objective is taken over observed vertices only, they are absent
  altogether. Either way the bound holds. This also covers walks with
  sub-`(L−1)` overlaps that spell molecules containing unobserved windows: such
  mass strictly lowers the objective.
- **Bidirected edges.** Bidirectedness only changes *which* `d` are realisable;
  it never enlarges the box `0 ≤ d_i ≤ N`. The bound is therefore independent of
  the edge structure, transitive reduction, and `o_min`.
- **Reverse complements.** With the molecule reading a vertex is an unordered
  reverse-complement pair, and `d_w` counts occurrences of that class;
  `Σ_w d_w = N` still holds for a length-`N` molecule. Lemmas 1–2 and Theorem 3
  are per-class statements and are unchanged.
- **Flow variables.** The proof never uses conservation; `d` ranges over the
  whole box, which contains the flow-realizable set. In particular it does not
  assume `Σ_i d_i = N` or `= n`.

Theorem 3 is strictly stronger than the conditional conservation lemma: it drops
the same-length restriction and the truth-flow-premise `Σ d_S = G`, and it
applies to non-spellable flows.

---

## 4. Refutation of the flow-level reading of the premise

Theorem 3 does **not** validate the phrase "the flow constraints give the
total-count identity". They do not. The §6.2 constraints are conservation plus
`d_v ≥ 1` and `d_v ≤ N`; no total is fixed. Two exact certificates:

**Certificate A (`S = ACGT`, `L = 2`, `N = n = G = 4`, single-strand).** The
four observed reads are distinct and the read-overlap graph is the 4-cycle
`AC → CG → GT → TA → AC` (proper overlaps of length `L−1 = 1`). Assigning flow
`2` to every edge is a circulation satisfying every lower bound; the induced
vertex throughput is `d = (2,2,2,2)`, so

```text
Σ_w d_w = 8 ≠ N = 4,
```

yet it is a legal §6.2 flow. It is strictly worse than the truth:
`φ_{1,4,4}(1) = 27/256` per type versus `φ_{1,4,4}(2) = 1/16`, so the truth's
objective `(27/256)^4` exceeds the flow's `(1/16)^4`. This instance therefore
**refutes** the claim that §6.2 flows satisfy `Σ_w d_w = N`, while confirming
that Theorem 3 still pins the optimum.

**Certificate B (`S = AAATAT`, `L = 3`, reverse-complement `A↔T`, per-type
lower bound; issue-#36 witness).** Observed molecules
`x = {AAA:2, AAT:1, ATA:1, TAA:1}` (`n = 5`), external `N = 6`, truth spectrum
`d_S = {AAA:1, AAT:1, ATA:3, TAA:1}` (`Σ = 6 = N`). The read-tiled genome
`D = AAATA` has spectrum exactly `x`, is a legal closed-walk flow, and has

```text
Σ_w d_D(w) = 5 ≠ N = 6,
```

while beating the truth by the §6.1 binomial ratio `1280/243`. Thus a feasible
§6.2 flow with the "wrong" total throughput can strictly dominate a truth whose
own total equals `N`. This is the concrete sense in which the conservation
premise is not operative.

Both certificates are checked by the companion script. [mathematical proof +
verified computation]

---

## 5. The lemma is false outside the slice

Medvedev–Brudno §6.1 treats `n` (number of reads) and `N` (known genome length)
as independent parameters. The slice `n = N` is special; the recorded
zero-counterexample searches fix it, and their zero is explained by Theorem 3,
not by bridging.

**Counterexample (per-occurrence, `I_s`, feasible truth, `n ≠ N`).** On a
two-symbol alphabet with the reverse-complement involution `A ↔ B`:

```text
G = 5, L = 3, N = 5, n = 3 reads
truth        S = AAATT
starts       (0, 1, 4)
observed     x = {AAA:1, AAT:1, TAA:1}
truth spec   d_S = {AAA:1, AAT:2, TAA:2}
competitor   D = AAAATT (length 6)
competitor   d_D = {AAA:2, AAT:2, TAA:2}
```

`I_s` holds (coverage plus the single triple repeat `A` at positions `{0,1,2}`
all-bridged); `supp(d_S) = supp(d_D) = supp(x)` and `d_S, d_D ≥ x`, so both are
per-occurrence feasible. The literal §6.1 binomial satisfies

```text
B_62(D) / B_62(S) = 9/8 > 1.
```

Here `n = 3 < N = G = 5`, so Lemma 2 does not apply and the truth is not
read-tiled (`d_S ≠ x`). This refutes any extension of the conditional
conservation lemma beyond its stated slice. [verified computation; exact
rationals]

The companion script also records the slice collapse exhaustively: over 6 618
small `n = N = G` feasible-truth instances (binary, `G ≤ 6`, `L = 2`, both
readings), `d_S = x` held in every case, with no counterexample.

---

## 6. Summary table

| statement | status |
|---|---|
| §6.2 candidates are bidirected flows; objective is the §6.1 separable binomial with external `N`; no total-flow constraint | **source fact** |
| Lemma 1: per-coordinate maximum `d = N x / n`, equal to `x` when `n = N` | **mathematical proof** |
| Lemma 2: `n = N = G` + truth feasibility ⇒ `d_S = x` | **mathematical proof** |
| Theorem 3: in the slice `n = N`, `x` is the unique optimal spectrum over the *entire* §6.2 flow class (non-spellable included, any length, unobserved types handled), so a truth with spectrum `x` is optimal | **mathematical proof** |
| `Σ_w d_w = N` is a §6.2 flow constraint | **refuted** (Certificates A, B) |
| Conditional conservation lemma outside `n = N` | **refuted** (`AAATT`, ratio `9/8`) |
| `I_s` plays any role in the slice collapse | **no** (unused in Lemmas 1–2) |
| Recorded zero in the `n = N = G` search scope | **explained/proved** by Theorem 3 |
| Which MB09 layer the 2016 sentence intends | **open** (source ambiguity, issue #36) |
| Generic `n ≠ N` per-occurrence fixed-length statement | **open** |

---

## 7. Relation to existing repository work

This note is an independent reconstruction. The issue #36 status comments
proposed the conditional conservation lemma as an unproved candidate. An
unmerged branch analysis (`mathematics/section62-peroccurrence-search-degeneracy.md`,
branch `analysis/se62-peroccurrence-slice-obstruction`) proves the arithmetic
collapse for **molecules**. The contribution here is the flow-level Theorem 3
(no spellability, length, or total-throughput restriction; unobserved types
handled in the full product), the two explicit circulation certificates
refuting the total-count identity, and the generic-regime counterexample —
together with a self-contained verifier that does not import any branch module.
No prior summary is relied upon.

---

## 8. Reproduce

```sh
python3 scripts/verify_issue36_conservation_lemma.py
```

The script checks `[A]` the per-coordinate maximum (`N ≤ 9`, all `n ≤ N`,
`0 ≤ x ≤ n`, plus the exact stationary point), `[B]` the two flow-total
certificates, `[C]` the `AAATT` counterexample (including `I_s`), and `[D]` the
slice collapse. All arithmetic is exact `fractions.Fraction`.

---

## 9. Epistemic status

| claim | status |
|---|---|
| §6.1/§6.2 quotes and model | source fact (PMC3154397 §6.1–6.2) |
| Lemma 1 (per-coordinate maximum) | mathematical proof |
| Lemma 2 (slice collapse) | mathematical proof |
| Theorem 3 (flow-level slice optimum) | mathematical proof |
| Certificates A, B (`Σ d ≠ N` feasible) | mathematical proof + verified computation |
| `AAATT` generic counterexample | verified computation (exact rationals) |
| Slice collapse exhaustive instance count | verified computation, bounded |

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502.
