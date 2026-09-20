# Why the section 6.2 sequence-level search finds no per-occurrence counterexample

_Status: mathematical analysis with proofs, plus a bounded exhaustive exact-rational
computation and two explicit counterexamples. 2026-09-20. Independent of the
search that produced the recorded zero. Does not settle the source-ambiguous
Shomorony et al. open question._

_Reproduction: `python3 scripts/verify_se62_peroccurrence_slice.py` (all
assertions pass; exact `fractions.Fraction`; about one minute on the development
host)._

---

## 0. Answer at a glance

1. **The recorded zero is a theorem about a degenerate parameter slice, not an
   obstruction from bridging.** The search in
   `docs/section62-bidirected-flow-feasibility.md` §5 fixes the number of reads
   `n` equal to the external binomial denominator `N` equal to the true genome
   length `G`. In that slice, per-occurrence feasibility of the truth *forces*
   `d_S = x` (the truth is read-tiled), and the literal §6.1 binomial is
   coordinatewise maximized at `d_w = N x_w / n = x_w`. Hence **no** candidate of
   any length can strictly beat the truth; the search's zero is proved, and the
   bounded enumeration was unnecessary. The bridging hypothesis `I_s` is not used.

2. **Bridging is not the cause.** The collapse and the no-improvement inequality
   hold for every sampled multiset `x` with `n = |S|`, with or without `I_s`.

3. **The slice is not the generic model.** In Medvedev–Brudno §6.1/§6.2 the
   number of reads `n` is independent of the (externally supplied) true genome
   length `N`; the search sets both to `G`. Outside the slice, sequence-level
   §6.2 per-occurrence counterexamples exist with `I_s` and a feasible truth.

4. **Explicit counterexamples.** Under the reverse-complement reading (`A ↔ T`)
   the observed multiset can itself be realizable as a genome; the resulting
   read-tiled competitor beats the (non-read-tiled) truth. Minimal witness:

   ```
   G = 5, L = 3, n = 3 reads, external N = 5
   truth       S = AAATT            (per-occurrence feasible, I_s holds)
   observed    x = {AAA:1, AAT:1, TAA:1}
   competitor  D = AAAATT (length 6), spectrum {AAA:2, AAT:2, TAA:2}
   §6.1 binomial ratio L(D)/L(S) = 9/8 > 1
   ```

   and a read-tiled witness at `G = 6`:

   ```
   G = 6, L = 3, n = 4 reads, external N = 6
   truth       S = AAATAT
   observed    x = {AAA:1, AAT:1, ATA:1, TAA:1}
   competitor  D = AAAT (length 4), d_D = x exactly
   §6.1 binomial ratio L(D)/L(S) = 125/81 > 1
   ```

5. **What the zero does buy.** It is a complete proof for the slice
   `n = N = G`, which is exactly the regime in which the truth is read-tiled.
   It provides no evidence about the generic `n < G` regime and should not be
   cited as such.

---

## 1. Setup and the section 6.1 objective

Fix an alphabet (or molecule-class alphabet) `Σ` and read length `L ≥ 2`. A
circular truth `S` of length `G` has occurrence vector `d_S(w) =` number of
length-`L` windows of `S` in type/class `w`, so

```text
(1)  d_S ∈ Z_{≥0}^{E},   Σ_w d_S(w) = G,   B d_S = 0,
```

where `B` is the de Bruijn degree-balance matrix. A sample is a multiset of
reads with occurrence counts `x`, `n := Σ_w x_w`.

The literal Medvedev–Brudno §6.1 separable binomial, with external true genome
length `N` and `n` reads, is

```text
(2)  B_62(d) = ∏_w C(n, x_w) (d_w / N)^{x_w} (1 − d_w / N)^{n − x_w},
      domain  0 ≤ d_w ≤ N.
```

The `C(n, x_w)` and the factor `N^{-n}` are observation-only and cancel in any
comparison. `N` is a probability denominator (the true genome length); it is not
a candidate-length constraint (`docs/audit-binomial-marginals-issue32.md` §4).

**Per-occurrence sequence-level §6.2 feasibility** of a circular molecule `D`
(Medvedev–Brudno Observation 7; derivation in
`docs/section-6-2-feasible-set-membership.md` §2) is

```text
(3)  supp(d_D) = supp(x)   and   d_D(w) ≥ x_w  for all w,
```

plus `D` realizable (so `Σ_w d_D(w) = |D|`).

---

## 2. The per-coordinate maximum

Write `φ_{x,n,N}(d) := (d/N)^x (1 − d/N)^{n − x}` for `0 ≤ d ≤ N`.

**Lemma 1 (per-coordinate maximizer).** For integers `0 ≤ x ≤ n`:

- `log φ` has derivative `x/d − (n − x)/(N − d)`, so for `0 < x < n` the unique
  maximizer of `φ` on `[0, N]` is `d* = N x / n`;
- if `x = 0`, `φ` is nonincreasing with maximum at `d = 0`;
- if `x = n`, `φ` is nondecreasing with maximum at `d = N = N x / n`.

In particular, for `n = N`, `φ` is uniquely maximized at `d = x` whenever
`0 < x < n`.

_Proof._ The second derivative of `log φ` is `−x/d² − (n−x)/(N−d)² < 0`, so
`log φ` is strictly concave on `(0,N)` and the stationary point is the unique
maximum; the endpoint claims are immediate. `□`

The verification script checks the stationary point with exact rationals and the
maximum by exhaustive enumeration for `N ≤ 8`, and confirms that
`φ_{x,n,N}(d) ≤ φ_{x,n,N}(Nx/n)`.

## 3. The slice `n = N = G` collapses the truth to read-tiling

**Lemma 2 (read-tiling collapse).** Suppose `n = N = G`, `supp(d_S) = supp(x)`,
and `d_S(w) ≥ x_w` for all `w`. Then `d_S = x`.

_Proof._ By support equality, `Σ_w d_S(w) = Σ_{w ∈ supp x} d_S(w) = G`. Also
`Σ_w x_w = n = G`. Hence `Σ_w (d_S(w) − x_w) = 0` with every summand `≥ 0`
(componentwise on the support, and both are zero off it), so all summands are
`0`. `□`

**Theorem 3 (no strict counterexample in the slice).** Suppose `n = N = G`,
`supp(d_S) = supp(x)`, and the truth is per-occurrence feasible. Then for every
molecule `D` with `supp(d_D) = supp(x)`, `d_D(w) ≥ x_w`, and `d_D(w) ≤ N`,

```text
B_62(D) / B_62(S)
  = ∏_{w ∈ supp x} φ_{x_w, N, N}(d_D(w)) / φ_{x_w, N, N}(x_w)
  ≤ 1,
```

with equality iff `d_D = d_S`. In particular the truth is the **unique**
§6.1-binomial maximizer over the sequence-level §6.2 per-occurrence feasible set;
there is no strict counterexample, for any candidate length.

_Proof._ By Lemma 2, `d_S(w) = x_w` on `supp x`. Observation-only factors cancel.
For each `w ∈ supp x` we have `0 < x_w ≤ n = N`. If `x_w < N`, Lemma 1 with
`n = N` gives `φ_{x_w,N,N}(d_D(w)) ≤ φ_{x_w,N,N}(x_w)`, strictly unless
`d_D(w) = x_w`. If `x_w = N`, then `d_D(w) ≥ x_w = N` and `d_D(w) ≤ N` force
`d_D(w) = x_w` with ratio `1`. Multiplying gives the claim; equality in every
factor is `d_D = x = d_S`. `□`

**Corollary 4 (fixed-length exact sub-case).** If in addition `|D| = G`, then
`d_D(w) ≥ x_w` and `Σ_w d_D(w) = G = Σ_w x_w` force `d_D = x = d_S`; the exact
fixed-length multinomial ratio is exactly `1`. So the `N = G` rows of the
fixed-length search of `docs/section62-fixed-length-bidirected-counterexample.md`
are degenerate in the same way.

**Remark (bridging is irrelevant).** Neither Lemma 2 nor Theorem 3 uses the
bridging predicate `I_s`; the hypotheses are only `n = |S|` and truth
feasibility. The recorded zero is therefore a statement about the parameter
slice, not about bridging.

## 4. Why this explains the recorded zero

The search in `docs/section62-bidirected-flow-feasibility.md` §5 calls
`search(G, L, σ, N_reads = G, maxD, comp)` and evaluates the literal §6.1
binomial with external `N = |S| = G`, `n = Σ x = G` reads. It keeps exactly the
instances for which the truth is per-occurrence feasible with `supp(d_S) = supp x`
(guarded by `frozenset(x) == suppS` and `spS.get(w,0) >= c`). Theorem 3 applies
to every such instance under both the single-strand and reverse-complement
readings and for every candidate length up to the search bound. The assertion
`cex == 0` is a theorem, not merely a computation; the 85 572 enumerated
instances only exhibit special cases of it.

The same theorem covers the `N = G` rows of the separate fixed-length search.
Its `N < G` rows are **not** covered: there `n < G`, so Lemma 2 fails and the
truth need not be read-tiled.

## 5. The slice is not the generic model: counterexamples outside it

Medvedev–Brudno §6.1 has two independent quantities: `N`, the (known, external)
true genome length, and `n`, the number of sampled reads. The recorded search
identifies them with `G`. In the ordinary low-coverage regime `n < G`, and then
per-occurrence feasibility does **not** force `d_S = x`: the truth may carry more
occurrences than observed on some types.

In that regime the *read-tiled dominance* mechanism of
`docs/read-tiled-counterexample.md` Theorem 1 becomes available. If the observed
multiset `x` is itself realizable as a circular genome `D` with `d_D = x` (so
`|D| = n`), then `D` is per-occurrence feasible, and its likelihood relative to
the truth is governed by the divergence between the empirical distribution and
the truth's window distribution. When `d_S ≠ x` and `d_S` is not proportional to
`x`, the read-tiled `D` can beat the truth.

The verification script exhibits two exact instances (reverse-complement reading
`A ↔ T`), both with `I_s`, a per-occurrence feasible truth, and per-occurrence
feasible competitors:

| `G` | `L` | `n` | `N` | truth `S` | observed `x` | competitor `D` | ratio |
|----|----|----|----|-----------|--------------|----------------|-------|
| 5 | 3 | 3 | 5 | `AAATT` | `{AAA:1, AAT:1, TAA:1}` | `AAAATT` | `9/8` |
| 6 | 3 | 4 | 6 | `AAATAT` | `{AAA:1, AAT:1, ATA:1, TAA:1}` | `AAAT` (read-tiled) | `125/81` |

For the second row `D = AAAT` has `d_D = x` exactly and `|D| = n = 4 < G`, so it
cannot occur as a fixed-length length-`G` candidate: the read-tiled mechanism
**requires** `|D| = n`, which is incompatible with `|D| = G` when `n < G`.

A bounded exhaustive generic-regime sweep (script section C, per-occurrence
lower bound, `I_s`, truth feasible, variable length `≤ 2G`) finds such
counterexamples at `G = 5, 6` under the reverse-complement reading. Under the
single-strand reading it finds none for `G ≤ 8`, `L ∈ {2,3}`; that zero is not
explained by Theorem 3 and remains computational evidence (bounded).

## 6. Sharpened statement of what remains open

- **Variable-length, per-occurrence, generic `n < G`.** There is no obstruction:
  explicit `I_s` counterexamples exist (§5). The question is only how the
  counterexample count depends on `(G, L, σ, n)` and the reading.
- **Fixed-length `|D| = G`, per-occurrence, generic `n < G`.** Theorem 3 does not
  apply, and the read-tiled mechanism is unavailable because it needs `|D| = n`.
  The bounded zero of
  `docs/section62-fixed-length-bidirected-counterexample.md` (`G ≤ 7`, `L ≤ 4`)
  is therefore a genuinely different statement and is neither proved nor refuted
  here. This is the most interesting remaining positive candidate.
- **The `n = N = G` slice.** Resolved negatively for the per-occurrence reading:
  the truth is the unique maximizer. (Under the per-occurrence reading the
  recorded zero is a theorem; under the per-type reading `d_S = x` is not forced,
  which is why the per-type reading admits the `G = 6` witnesses recorded
  elsewhere.)

## 7. Relation to existing repository artifacts

| artifact | claim | status after this note |
|---|---|---|
| `docs/section62-bidirected-flow-feasibility.md` §5 | 85 572 instances, 0 sequence-level §6.2 counterexamples | **proved** for the searched slice `n = N = G` by Theorem 3; not evidence for the generic regime |
| `docs/section62-fixed-length-bidirected-counterexample.md` §1, §3 | per-occurrence fixed-length: 0 for `G ≤ 7`, `L ≤ 4` | `N = G` rows are degenerate (Cor. 4); `N < G` rows remain open |
| `docs/read-tiled-counterexample.md` Thm 1, Cor. 1a | read-tiled dominance; if truth is read-tiled every read-tiled candidate ties | **re-used**: under `n = N = G` truth-feasibility *is* read-tiling (Lemma 2), which is exactly the equality case |
| `mathematics/fixed-length-likelihood-duality-and-flow.md` Thm 5/6 | positivity-aware per-type water-filling | consistent; the §6.1 per-coordinate max here is the binomial analogue |

## 8. Epistemic status

| claim | status |
|---|---|
| §6.1 objective and external `N` reading | source fact (PMC3154397 §6.1; `docs/audit-binomial-marginals-issue32.md`) |
| Per-occurrence sequence-level feasibility criterion `supp = supp x ∧ d_D ≥ x` | mathematical argument (`docs/section-6-2-feasible-set-membership.md` §2) |
| Lemma 1 (per-coordinate maximum at `d = Nx/n`; at `x` if `n = N`) | **proof** |
| Lemma 2 (`n = N = G` ∧ truth feasible ⇒ `d_S = x`) | **proof** |
| Theorem 3 (no strict counterexample in the slice; unique maximizer) | **proof** |
| Corollary 4 (fixed-length exact `N = G` degenerate) | **proof** |
| Reported search used `n = N_reads = G` | source fact (script call `search(..., N=G, ...)`) |
| `AAATT → AAAATT` and `AAATAT → AAAT` are sequence-level §6.2 per-occurrence counterexamples with `I_s` | **verified computation + hand check** (`scripts/verify_se62_peroccurrence_slice.py` [C]) |
| Generic-regime counterexamples at `G = 5, 6` (revcomp) | **verified computation**, bounded |
| Single-strand generic-regime zero for `G ≤ 8`, `L ≤ 3` | **verified computation**, bounded (not explained here) |
| Fixed-length per-occurrence `N < G` statement | **open** |

## 9. Reproduce

```sh
python3 scripts/verify_se62_peroccurrence_slice.py
```

Section `[A]` checks Lemma 1, `[B]` checks Lemmas 2–3 exhaustively over 12 130
`n = N = G` instances (`G ≤ 6`, `L ≤ 4`, binary/ternary, both readings), and
`[C]` checks the two explicit generic-regime counterexamples. All arithmetic is
exact `fractions.Fraction`; the script exits non-zero on any regression.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397; Ilan
Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502.

Cross-references: `docs/section62-bidirected-flow-feasibility.md`,
`docs/section-6-2-feasible-set-membership.md`,
`docs/section62-fixed-length-bidirected-counterexample.md`,
`docs/read-tiled-counterexample.md`,
`mathematics/fixed-length-likelihood-duality-and-flow.md`.
