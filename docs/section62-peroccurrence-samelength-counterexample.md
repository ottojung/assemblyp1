# A same-length per-occurrence (`d ≥ x`) bridging counterexample beyond the searched scope

_Status: independent from-scratch computation + source reading, 2026-09-20.
All claims are labelled **source fact**, **mathematical argument**,
**verified computation**, or **open**. This is **adjacent exploration, not
source intent**: it does not settle which Medvedev–Brudno (2009) object the
Shomorony et al. (2016) sentence intends, nor the single-strand convention. It
resolves one bounded open item recorded on `main`._

_Reproduction:_

```sh
python3 scripts/verify_peroccurrence_samelength_counterexample.py           # witness + family
python3 scripts/verify_peroccurrence_samelength_counterexample.py --search  # + bounded census
```

_The script is self-contained, exact (`fractions.Fraction`), deterministic, and
exits non-zero on any failed assertion. It uses the strict extension predicate
recorded in [`bridging-source-semantics.md`](bridging-source-semantics.md)
(`r < t` and `t + ℓ < r + L`), not the exploratory flank-coverage test that
appears in some of the repository's Python searches._

---

## 0. Answer at a glance

`main`'s [`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md)
records the strengthened candidate rule

> `d_D(w) ≥ x_w` for every observed type `w` (the *per-occurrence* reading of
> MB09 §6.2's per-vertex lower bound),

and lists the fixed-length same-length statement **(P_fix)** under that
strengthening as **open** (bounded zero evidence; binary alphabet, `G = 6`,
`L = 3`, 667 instances). The unmerged issue-#36 branch extended that bounded
zero to `G ≤ 7`, `L ≤ 4`, `σ ≤ 3`.

**That open item is false.** A counterexample exists at

```text
alphabet          {A, B, C}, reverse-complement A <-> B, C fixed
read length       L = 3
truth             S = ABABACAC              (G = 8)
competitor        D = ABACACAC              (G = 8, SAME LENGTH)
read starts       T = (1, 3, 5, 7)  plus one ACA read at position 4 or 6
observed          x = { ABA:1, BAC:1, ACA:2, CAC:1, ABC:1 }   (n = 6 < G)
truth spectrum    d_S = { ABA:3, BAC:1, ACA:2, CAC:1, ABC:1 }
competitor spec   d_D = { ABA:1, BAC:1, ACA:3, CAC:2, ABC:1 }
exact same-length multinomial ratio  L_exact(D)/L_exact(S) = 3/2 > 1
```

`I_s` holds for the read set under the **strict** source bridging predicate;
both `S` and `D` satisfy per-occurrence feasibility (support equality and
`d ≥ x`); `D` is neither a cyclic shift nor the reverse complement of `S`.
[verified computation]

The phenomenon is not isolated: a parametric family works at `G = 8, 9, 10`
and stops exactly when `I_s` fails (an unbridgeable length-`(L−1)` triple
repeat appears), so `I_s` is genuinely active. The single-strand reading
remains open; without `I_s` it is already false, so `I_s` is essential there.
[verified computation + mathematical argument]

---

## 1. Setup and the precise statement refuted

### 1.1 The two ingredients (source facts)

- **MB09 §6.2 / §6.1.** For a spelled molecule `D`, Observation 7 makes
  sequence-level §6.2 feasibility exactly *support equality* between the
  length-`L` window molecule classes of `D` and the observed read molecules.
  The source's per-vertex lower bound is `1`; the *per-occurrence
  strengthening* asks in addition `d_D(w) ≥ x_w` for every observed type.
- **Shomorony `I_s`.** A read realization covers the circular truth, every
  triple repeat is all-bridged, and every interleaved repeat pair is bridged.
  A copy at `t` of length `ℓ` is bridged by a read start `r` iff
  `r = t − d (mod G)` for some `1 ≤ d ≤ L − ℓ − 1` (Bresler et al.). This is the
  strict predicate; the exploratory "read covers both flanks" predicate is
  weaker and is **not** used here.[^1]

[^1]: Some exploratory scripts in the repository use a "read covers both
flanking positions" test, which can over-report bridging when `L ≥ G − ℓ`.
This note uses instead the strict source predicate `r < t ∧ t + ℓ < r + L`
recorded in [`bridging-source-semantics.md`](bridging-source-semantics.md);
equivalently `r = t − d (mod G)` for some `1 ≤ d ≤ L − ℓ − 1`. The witness's
`I_s` certificate is checked against that strict predicate. For
`G = 8, L = 3` the two agree on the copies that occur in this witness.

The strengthened statement (P_fix) restricted to this reading is:

> **(P_fix, per-occurrence).** If `I_s` holds for a read realization of the
> circular truth `S`, and the truth is per-occurrence feasible, then no
> spelled molecule `D` with `|D| = |S|`, `supp(spec_L(D)) = supp(x)`, and
> `d_D(w) ≥ x_w` strictly improves the same-length exact multinomial.

### 1.2 The objective

With `|D| = |S| = G` the exact candidate-intrinsic multinomial is

```text
L_exact(D) / L_exact(S) = prod_w ( d_D(w) / d_S(w) )^{ x_w } .
```

Per-occurrence feasibility of the truth gives `x_w ≤ d_S(w)`; feasibility of
the candidate gives `x_w ≤ d_D(w)`. For a sample with `n = Σ x_w < G` neither
spectrum is forced to equal `x`, so multiplicity can be redistributed subject
to the two spectra sharing one support and one total mass `G`.

---

## 2. Exact verification of the witness

The companion script recomputes, from scratch, all windows and molecule
classes, the strict `I_s` certificate, both per-occurrence certificates, and
the exact rational ratio. The concrete data (`A = 0, B = 1, C = 2`,
`A ↔ B`, `C` fixed):

```text
truth windows        ABA, BAB, ABA, BAC, ACA, CAC, ACA, CAB
molecule classes     ABA, ABA, ABA, BAC, ACA, CAC, ACA, ABC
d_S                  ABA:3, BAC:1, ACA:2, CAC:1, ABC:1        (sum 8)
competitor windows   ABA, BAC, ACA, CAC, ACA, CAC, ACA, CAB
molecule classes     ABA, BAC, ACA, CAC, ACA, CAC, ACA, ABC
d_D                  ABA:1, BAC:1, ACA:3, CAC:2, ABC:1        (sum 8)
observed             ABA:1, BAC:1, ACA:2, CAC:1, ABC:1        (n = 6)
```

- **Support equality** holds for `x`, `d_S`, `d_D` simultaneously.
- **Per-occurrence** holds on both sides: `d_S(ACA) = 2 = x_ACA`,
  `d_D(ACA) = 3 ≥ 2`, and every other coordinate is at least its `x`-value.
- **`I_s`.** The distinct read starts `{1, 3, 5, 7}` cover all eight positions;
  the triple-repeat copies are all bridged by these reads, and the interleaved
  conjunct is satisfied; adding the extra `ACA` read preserves `I_s`
  (monotonicity). [verified computation]
- **Ratio.**
  `(1/3)·(1/1)·(3/2)^2·(2/1)·(1/1) = (1/3)·(9/4)·2 = 3/2 > 1`.
- `D` is not in the cyclic-shift / reverse-complement orbit of `S`.

---

## 3. Why the witness works

The mechanism is exactly the one the bounded searches missed by stopping at
`G ≤ 7`:

1. **Reverse complementarity creates a class with multiplicity.** In the
   bidirected reading `BAB` and `ABA` are one molecule class, so
   `d_S(ABA) = 3` although the raw word `ABA` occurs only twice.
2. **Per-occurrence feasibility is not read-tiling when `n < G`.** Here
   `n = 6 < G = 8`, so `d_S ≥ x` leaves slack (`d_S(ACA) = 2 = x_ACA`,
   `d_S(ABA) = 3 > 1`).
3. **Support equality permits reallocation at fixed length.** `D` moves two
   units of class-multiplicity off `ABA` (from `3` to `1`) and onto `ACA`
   (`2` to `3`) and `CAC` (`1` to `2`), keeping the support and the total mass
   `G = 8`. The observed weights reward this: the ratio
   `prod_w (d_D(w)/d_S(w))^{x_w}` has factors `(1/3)^1` on `ABA`,
   `(3/2)^2` on `ACA`, and `(2/1)^1` on `CAC`, with every other factor `1`;
   their product is `3/2`.

The sample is realizable: the raw word `ACA` occurs at positions `4` and `6`
of the truth, so two `ACA` reads are legal, and the extra reads do not break
`I_s`. [verified computation]

---

## 4. A parametric family, and the `I_s` stopper

Define

```text
S_k = A^k · ABABACAC ,   D_k = A^k · ABACACAC ,   L = 3 ,   G = 8 + k .
```

The script verifies, for `k = 0, 1, 2` (`G = 8, 9, 10`), an `I_s` read set and
a per-occurrence sample `x` with exact ratio `3/2`:

| `k` | `G` | `S` | `D` | `n` |
|---|---|---|---|---|
| 0 | 8 | `ABABACAC` | `ABACACAC` | 6 |
| 1 | 9 | `AABABACAC` | `AABACACAC` | 7 |
| 2 | 10 | `AAABABACAC` | `AAABACACAC` | 8 |

The family **stops at `k = 3`**: `S_3 = AAAABABACAC` then contains three
occurrences of the length-`(L−1) = 2` word `AA` with varying context, an
unbridgeable Bresler triple repeat, so `S_3` admits **no** `I_s` read set and
the statement's hypothesis is vacuous there. This is direct evidence that the
search's zeros are not an artifact of ignoring `I_s`: `I_s` is the condition
that bounds the run and removes the larger members of the family.
[verified computation + mathematical argument]

---

## 5. Bounded census (strict `I_s`, per-occurrence, fixed length)

`--search` runs the same efficient per-(truth, candidate) test over the
recorded scope and beyond. It counts distinct `(S, D)` pairs for which some
`I_s` realization and some per-occurrence sample make the exact ratio exceed
`1`.

| reading | `G` | `L` | `σ` | beats |
|---|---|---|---|---|
| single-strand | 6, 7, 8 | 3 | 2 | 0 |
| bidirected | 6, 7, 8 | 3 | 2 | 0 |
| single-strand | 6, 7, 8 | 3 | 3 | 0 |
| bidirected | 6, 7 | 3 | 3 | 0 |
| bidirected | **8** | **3** | **3** | **256** |
| single-strand | 8 | 4 | 3 | 0 |
| bidirected | 8 | 4 | 3 | 0 |

All 256 beats at `(G, L, σ) = (8, 3, 3)` bidirected are the
rotation / reverse-complement orbit of `ABABACAC → ABACACAC` (16 distinct
truths of one orbit, every ratio `3/2`). The zeros below and beside this cell
are bounded computational evidence, **not** proofs of absence.
[verified computation, bounded]

One-off sweeps (not re-run by `--search` for runtime reasons) extend the
single-strand control zeros to `G = 13` binary at `L = 3`, `G = 12` binary at
`L = 2, 4`, and `G = 9, 10`, `σ = 3` at `L = 3, 4`; the bidirected
per-occurrence phenomenon also appears at `(G, L, σ) = (9, 3, 3)` and
`(8, 3, 4)`.

---

## 6. Single-strand status

The single-strand reading is **not** refuted by this witness: under it the raw
supports of `S` and `D` differ (`BAB` versus `CAB`), so `D` is not a
support-equal candidate. The extended bounded zeros above leave it **open**.

It is worth recording *why* the problem is nontrivial on that branch: `I_s` is
essential. Without it the single-strand fixed-length per-occurrence rule is
already false, e.g. `S = AAAAAAAB`, `D = AAAABAAB` (`G = 8`, `L = 3`) have the
same support and the sample `x = {AAA:1, AAB:1, ABA:1, BAA:1}` gives exact
ratio `16/5 > 1`; but `S` contains an unbridgeable length-`2` triple repeat and
so does **not** satisfy `I_s`. Any proof on the single-strand branch must use
the repeat-bridging conjunct in an essential way. [verified computation +
mathematical argument]

---

## 7. What this does and does not settle

**Does.** It shows that the per-occurrence strengthening does **not** rescue
the same-length implication under the bidirected (molecule-class) reading: a
support-equal, per-occurrence-feasible spelled competitor of the *same length*
strictly improves the exact multinomial, with `I_s` holding non-vacuously. It
therefore closes the bounded open row "(P_fix) under the per-occurrence
strengthening" of
[`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md)
§3/§7 and §10.2 of
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md).

**Does not.** It does not settle which MB09 object the 2016 sentence intends,
the strand convention, the tie/equivalence semantics, or the source-level
question. It does not refute the single-strand per-occurrence statement, which
remains open; it does not address the non-spellable §6.2 flow class; and it
does not claim the sequence-level support/lower-bound certificate is the §6.2
definition (it is a strengthening).

The witness is currently **verified computation**, not kernel-checked. A
kernel-checked Lean certificate of the `G = 8` finite instance (strict `I_s`
over `Fin 8`, support equality, per-occurrence lower bounds, exact ratio
`3/2`) is a natural bounded follow-up in the style of
[`../AssemblyP1/SameLengthSection62Counterexample.lean`](../AssemblyP1/SameLengthSection62Counterexample.lean).

---

## 8. Epistemic status

| claim | status |
|---|---|
| MB09 §6.2 per-vertex lower bound `1`; per-occurrence `d ≥ x` is a strengthening | **source fact / source-supported inference** (MB09 §6.2; [`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md)) |
| `I_s` definition; strict copy-bridging predicate | **source fact** (Shomorony et al. 2016 Eq. (1); Bresler et al. 2013; [`bridging-source-semantics.md`](bridging-source-semantics.md)) |
| exact same-length ratio `prod_w (d_D(w)/d_S(w))^{x_w}` | **mathematical argument** (MB09 §6.1) |
| `S = ABABACAC`, `D = ABACACAC` witness: strict `I_s`, both per-occurrence, support equality, ratio `3/2`, not equivalent | **verified computation** |
| parametric family `A^k ABABACAC → A^k ABACACAC` for `k = 0,1,2`, stopper at `k = 3` | **verified computation + mathematical argument** |
| 256 beats at `(G,L,σ) = (8,3,3)` bidirected; zeros in the census table | **verified computation, bounded** |
| single-strand without `I_s`: `AAAAAAAB → AAAABAAB`, ratio `16/5` | **verified computation** |
| (P_fix) per-occurrence bidirected is false beyond the recorded scope | **follows** |
| (P_fix) single-strand per-occurrence | **open** (extended bounded zero) |
| which MB09 object / strand the 2016 sentence intends | **source ambiguity, unchanged** |

---

## 9. Reproduce

```sh
python3 scripts/verify_peroccurrence_samelength_counterexample.py
python3 scripts/verify_peroccurrence_samelength_counterexample.py --search
```

The default run verifies the `G = 8` witness, the `G = 9, 10` family members,
the `k = 3` `I_s` stopper, and the `I_s`-essential single-strand control. The
`--search` run reproduces the census table (about four minutes on the
development host). All arithmetic is exact `fractions.Fraction`.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §6.1–6.2, PMC3154397;
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, Eq. (1), §5; Guy Bresler, Ma'ayan
Bresler, David Tse, *Optimal assembly for high throughput shotgun sequencing*,
*BMC Bioinformatics* 14(Suppl 5):S18, 2013, Figure 5 (PMC3706340).

Cross-references:
[`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md),
[`bridging-se62-flow-ml-counterexample.md`](bridging-se62-flow-ml-counterexample.md),
[`section62-mb09-bidirected-graph-audit.md`](section62-mb09-bidirected-graph-audit.md),
[`source-notes/same-length-witnesses-candidate-set-inclusion.md`](source-notes/same-length-witnesses-candidate-set-inclusion.md),
[`bridging-source-semantics.md`](bridging-source-semantics.md).
