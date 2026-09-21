# Issue #48: intrinsic candidate checks do not rescue finite-data ML

_Status: bounded exhaustive computation + two exact unbounded families +
adversarial recheck of the known variable-length witnesses, obtained with an
**independent** implementation from
[`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md)
(concurrent packet; see §6). Not a Lean result. It answers the **finite-data
question of issue #48** for the literal candidate-dependent-length exact
multinomial objective (Medvedev–Brudno 2009, §6.1), with the strict source
bridging predicate `I_s` on the truth. It does not change any source-faithful
theorem or the Lean boundary._

_Reproduction: `python3 scripts/issue48_intrinsic_candidate_search.py`
(exact `fractions.Fraction`/integer arithmetic, deterministic)._

---

## 0. Verdict

Issue #48 asks whether replacing the external *true-length* axiom by
**candidate-intrinsic admissibility checks** makes the truth
maximum-likelihood from a finite, `I_s`-feasible read realization.

**No.** Under both natural readings of the intrinsic check the answer is
negative, and the failure is not borderline:

| intrinsic candidate class | smallest surviving finite counterexample | ratio unbounded in `N`? |
|---|---|---|
| `P_weak` = primitive ∧ spectrum-resolvable | `N=2, G=4, n=3`: `AABB → AAB`, ratio `16/9` | yes, `AABC → ABC`, ratio `(4/3)^N` |
| `P_strong` = `P_weak` ∧ read-length repetition-free | `N=2, G=4, n=3`: `AABB → AAB`, ratio `16/9` | yes (non-vacuous truth): `ABACABC → ABAC`, ratio `(7/4)^k·(7/8)^2` |

Both classes are strictly weaker than the *fixed-length* strong theorem's
candidate class in the length dimension (intrinsic checks do not know `G`), and
the obstruction is the same one already isolated for the unrestricted exact
objective: finite read multiplicities/support, not structural
non-identifiability. In the unbounded families **both** genomes are primitive
and spectrum-resolvable; in `P_strong` the competitor is additionally
read-length repetition-free.

**Interpretation of "unbounded".** The families of §3 give, for every finite
`N`, a valid `I_s` realization on which the ratio equals `(G/n)^N`. These
realizations put all reads on a proper subset of the `G` start positions, so
under i.i.d. uniform sampling from the `G` starts their probability is
exponentially small in `N`. They therefore show that **no uniform-in-`N`
likelihood-ratio bound** can repair the finite statement, but they do **not**
refute a population/infinite-read repair that samples from the true uniform
law (issue #45): in that limit the empirical spectrum tends to `d_S/G` and the
proportional-sample theorem makes the truth optimal. The finite negative and
the population positive are compatible; the repair must be probabilistic
(typicality), not a worst-case bound over realizations.

**Compatibility caveat (important).** `P_strong` violates the issue's own
requirement that the intrinsic predicate should admit an `I_s`-feasible truth:
the truth `ABACABC` satisfies `I_s` non-vacuously but is **not**
read-length repetition-free (its `2`-mer `AB` occurs twice at `L=3`). So
`P_strong` is an over-strong *variant*, reported for completeness, not the
faithful repair. The faithful repair is `P_weak`.

---

## 1. Definitions (exact, candidate-intrinsic)

Let `D` be a circular candidate genome of length `n` over an alphabet, `L` the
read length, `d_D` its length-`L` window-count spectrum.

- **primitive(D).** `D ≠ C^k` for every `k ≥ 2` and shorter circular `C`.
- **SR(D, L) — spectrum-resolvable.** `D` is the *unique* circular genome of
  length `n` with its `L`-mer spectrum, up to rotation (Ukkonen/Pevzner
  `q`-gram identifiability; computed in the script by exhaustively grouping all
  length-`n` genomes by spectrum, hence exact on the searched ranges).
- **RRF(D, L) — read-length repetition-free.** No `(L−1)`-mer of `D` occurs
  twice. By Lemma 1 of `mathematics/bridging-and-spectrum-uniqueness.md`
  (`scripts/bridging_spectrum_uniqueness.py`) this is equivalent to "every
  maximal repeat of `D` has length `≤ L−2`", i.e. Bresler's *all repeats
  bridged* condition applied to `D` alone.
- **`P_weak`** `= primitive ∧ SR`;  **`P_strong`** `= primitive ∧ SR ∧ RRF`.

Truth hypothesis `I_s` is the strict source predicate of
`docs/copy-bridging-predicate-correction.md` and
[`docs/audit-aaatat-single-strand-bridging-2026-09-21.md`](audit-aaatat-single-strand-bridging-2026-09-21.md):
coverage, every triple repeat all-bridged, every interleaved maximal-repeat
pair bridged, with a copy at `t` of length `ℓ` bridged iff a read starts in
`{ (t−d) mod G : 1 ≤ d ≤ L−ℓ−1 }`.

Objective is the candidate-dependent-length exact multinomial of
Medvedev–Brudno §6.1; the observation-only coefficient cancels and

```text
L(D|x)/L(S|x) = ∏_{w: x_w>0} ( G·d_D(w) / (n·d_S(w)) )^{x_w} ,
```

taken as `0` if some observed `w` has `d_D(w) = 0`.

All computations use `fractions.Fraction`.

---

## 2. Adversarial recheck of the known variable-length witnesses

Script section A. `SR` is computed exactly for each instance.

| truth `S` | `L` | starts | obs | competitor `D` | `n` | `I_s` | prim(D) | SR(D) | RRF(D) | ratio | survives |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `ACGT` | 2 | `(0,0,2)` | `{AC:2,GT:1}` | `ACACGT` | 6 | ✅ | ✅ | ✅ | ❌ | `32/27` | `P_weak` |
| `ACGT` | 2 | `(0,0,0,0)` | `{AC:4}` | `ACACAC` | 6 | ❌ coverage | ❌ | ✅ | ❌ | `16` | neither (non-primitive) |
| `AACGT` | 2 | `(0,0,0,0)` | `{AA:4}` | `AAAA` | 4 | ❌ coverage | ❌ | ✅ | ❌ | `625` | neither (non-primitive) |
| `ABACABC` | 3 | `(1,1,1,3,6)` | `{BAC:3,CAB:2}` | `ABAC` | 4 | ✅ | ✅ | ✅ | ✅ | `16807/4096` | **both** |
| `ABACABC` | 3 | `(1,1,1,3,6)` | `{BAC:3,CAB:2}` | `ACABACB` | 7 | ✅ | ✅ | ✅ | ❌ | `2` | `P_weak` (fixed length) |

Findings.

1. The **kernel-checked** witness `ACGT → ACACGT`
   ([`docs/exact-variant-e-counterexample.md`](exact-variant-e-counterexample.md))
   **survives `P_weak`**: both genomes are primitive and spectrum-resolvable.
   It does not survive `P_strong` because `ACACGT` has the `1`-mer `A` twice.
2. The `ACACAC` and `AAAA` competitors are killed by **primitiveness** (they are
   whole repetitions) *and* the universality samples were already known to fail
   `I_s` **coverage** (`docs/unrestricted-length-proportional-reduction.md`
   §5.2). So the "repeat-obstruction" competitors the issue hoped to reject are
   indeed rejected — but the checks do not touch the surviving witnesses.
3. The `ABACABC → ABAC` **unrestricted-length** witness survives **both**
   classes; `ABAC` is primitive, spectrum-resolvable and read-length
   repetition-free.
4. The fixed-length `ACABACB` competitor is a same-length tie-free competitor
   with ratio `2`; it is not in the variable-length story except as a
   comparison, and it fails `RRF`.

The precise reason `P_strong` fails is *not* that it excludes all witnesses —
`ABAC` passes it. It is that even repetition-free candidates retain a
length-shrinkage/frequency lever.

---

## 3. Two exact unbounded families

### 3.1 `P_weak`, vacuous-`I_s` truth: `AABC → ABC`

`S = AABC` (`G=4`), `L=3`, is primitive, spectrum-resolvable, and
read-length repetition-free; it is repeat-free at read length `3` (all four
`3`-mers distinct), so `I_s` is satisfied vacuously for any covering read set.
`W = {ABC, BCA}` are two consecutive windows that cover the circle, each with
`d_S = 1`. The candidate `D = ABC` (`n=3`) is primitive, spectrum-resolvable
and `RRF`, and contains both.

For latent starts `(1, 2, 2, …, 2)` (one `ABC`, rest `BCA`) coverage holds and

```text
L(D|x)/L(S|x) = (G/n)^N = (4/3)^N → ∞ .
```

Script section C1 verifies `N = 2,4,8` exactly: `16/9`, `256/81`,
`65536/6561`.

### 3.2 `P_strong`, non-vacuous-`I_s` truth: `ABACABC → ABAC`

`S = ABACABC` (`G=7`), `L=3`, satisfies `I_s` **non-vacuously** (bridged
length-`1` triple repeat and bridged interleaved repeat pair; audited in
`docs/audit-aaatat-single-strand-bridging-2026-09-21.md` for the same
mechanism). For latent starts `(1,1,…,1,3,6)` (k copies at start `1`):

```text
obs = { BAC: k, CAB: 2 },   d_S = { BAC: 1, CAB: 2 },
D = ABAC (n=4),             d_D = { BAC: 1, CAB: 1 },
L(D|x)/L(S|x) = (7/4)^k · (7/8)^2 → ∞ .
```

`ABAC` is primitive, spectrum-resolvable and `RRF`. Script section C2 verifies
`k = 1,2,3,5,9` exactly: `343/256`, `2401/1024`, `16807/4096`,
`823543/65536`, `1977326743/16777216`.

Both families use only realizations of the shotgun model (reads are length-`L`
windows at latent start positions), satisfy the strict source `I_s`, and use
competitors admitted by the respective intrinsic class.

---

## 4. Smallest surviving counterexamples (bounded exhaustive search)

Script section B enumerates, for `L=3`, alphabet `{A,B,C}`, truth lengths
`L < G ≤ 6`, read multisets up to `N=4` (combinations with replacement of
latent starts), candidate lengths up to `n=6`, under the strict `I_s`
predicate. "smallest" is `(N, G, n)` lexicographic. The search is exhaustive in
the stated finite range.

| predicate | `n` range | truth restriction | smallest witness |
|---|---|---|---|
| `P_weak` | `n ≥ L` | any | `N=2, G=4, n=3`: `S=AABB`, starts `(0,3)`, obs `{AAB,BAA}`, `D=AAB`, ratio `16/9` |
| `P_weak` | `n > L` | any | `N=2, G=5, n=4`: `S=AABBC`, starts `(0,3)`, obs `{AAB,BCA}`, `D=AABC`, ratio `25/16` |
| `P_weak` | `n ≥ L` | non-vacuous `I_s` | `N=3, G=4, n=5`: `S=AAAB`, starts `(0,1,3)`, obs `{AAA,AAB,BAA}`, `D=AAAAB`, ratio `128/125` |
| `P_strong` | `n ≥ L` | any | `N=2, G=4, n=3`: `S=AABB`, starts `(0,3)`, obs `{AAB,BAA}`, `D=AAB`, ratio `16/9` |
| `P_strong` | `n > L` | any | `N=2, G=5, n=4`: `S=AABBC`, starts `(0,3)`, obs `{AAB,BCA}`, `D=AABC`, ratio `25/16` |
| `P_strong` | `n ≥ L` | non-vacuous `I_s` | `N=3, G=6, n=5`: `S=AABACC`, starts `(0,2,5)`, obs `{AAB,BAC,CAA}`, `D=AABAC`, ratio `216/125` |

(Each listed row is the lexicographically smallest; the script prints the same
operational detail for every configuration. The row for `P_strong` with
`n ≥ L` and any truth coincides with `P_weak` because the smallest instance
already uses an `RRF` competitor.)

The global minimum over `L ∈ {2,3}` is the `L=2` instance `S=AAB → D=AB`
(`G=3`, `n=2`, starts `(1,2)`, obs `{AB,BA}`), ratio `9/4`, and its truth
`AAB` is primitive and `RRF` at `L=2`; this is the same instance reported as
row 1 of the concurrent packet. Reproduce with
`--L 2 --alpha 4 --Gmax 5 --Nmax 4 --nmax 6`.

The non-vacuous `P_weak` instance `S=AAAB → D=AAAAB` is the `k=1` member of the
family behind `docs/bridging-consequences-lemmas.md` Theorem 1; scaling the
`AAAA` count gives `(8/5)^k·(16/25) → ∞` there, but `AAAAB` is not `RRF`
(it has two `AA` `2`-mers), which is exactly why §3.2 supplies an `RRF`
variant.

---

## 5. Why the intrinsic checks fail, structurally

Let `W` be the observed read-type support of a finite `I_s`-feasible
realization, `G = |S|`, `n = |D|`.

- **Multiplicity/support, not length, is the lever.** If `x ∝ d_S` the truth is
  optimal over all candidate lengths (Theorem 1 of
  `docs/unrestricted-length-proportional-reduction.md`). Every surviving
  witness therefore has a non-proportional `x`; the issue's "finite
  multiplicity fluctuations" are sufficient to break ML optimality.
- **`RRF` only forces `d_D(w)=1` on the support**, replacing
  frequency amplification by the factor `G/n`. Whenever the observed types can
  be covered by an `RRF` candidate with `n < G` and `d_S(w)=1`, that factor
  exceeds `1` per read and the ratio is `(G/n)^N`, unbounded. The intrinsic
  checks never compare `n` with `G`, because the assembler is not allowed to
  know `G`; this is precisely the axiom that issue #48 tries to relax.
- **`I_s` does not imply `RRF`.** `ABACABC` is `I_s`-feasible but not `RRF`, so
  `P_strong` excludes the truth from its own candidate class and cannot be the
  faithful repair. `SR` does not have this defect on the tested witnesses:
  every `I_s`-admissible truth here is spectrum-resolvable (consistent with
  Conjecture 4 of `mathematics/bridging-and-spectrum-uniqueness.md`).

A natural necessary condition for any intrinsic repair to work is therefore
not a repeat/admissibility predicate at all but a candidate-intrinsic **length
bound** tied to the data (e.g. flow/overlap-graph feasibility, Variant F), or
the move to a population/infinite-read regime (issue #45).

---

## 6. Reconciliation with the concurrent issue-#48 packet

A concurrent worker produced
[`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md)
with `scripts/verify_issue48_intrinsic_admissibility.py`. This section reconciles
the two packets proposition-by-proposition.

- **Agreement on the answer.** Both conclude the finite repaired statement is
  false with free candidate length, under the literal MB09 §6.1 objective,
  strict single-strand `I_s`, and a strict likelihood gap (so tie/equivalence
  conventions are irrelevant).
- **Independent agreement on witnesses.** Their named witnesses
  `AABB → AAB` (`16/9`), `AABBC → AABC` (`25/16`) and `ABACABC → ABAC`
  (`16807/4096`) are reproduced by this packet's independent implementation,
  which computes spectrum-resolvability by exhaustive spectrum grouping and
  strict `I_s` from the start-interval predicate (`python3
  scripts/issue48_intrinsic_candidate_search.py`, section A/B).
- **Predicate naming.** Their `STRONG` is this note's `RRF` (no repeated
  `(L−1)`-mer); their `WEAK` is the candidate-intrinsic `I_s` shadow at the full
  read set. This note's primary class `P_weak = primitive ∧ SR` is **strictly
  weaker** than their `primitive ∧ WEAK` whenever `WEAK ⇒ SR` (Conjecture 4 of
  `mathematics/bridging-and-spectrum-uniqueness.md`): `AAAAB` is `SR` (unique
  spectrum realization) but not `WEAK`. On the searched witnesses the two
  classes agree, so the refutations corroborate rather than conflict. The
  literal "unresolvable at read length `L`" reading is `SR`, which is why this
  packet uses it as the headline class.
- **Materially new in this packet.** (i) The two families of §3 give an exact
  closed-form ratio `(G/n)^N` and therefore show that the finite failure has
  **no uniform-in-`N` bound**; (ii) the compatibility defect of `RRF`/`STRONG`
  (`ABACABC` is `I_s`-feasible but not `RRF`, so the strong predicate excludes
  the truth) is stated explicitly.
- **Shared caution (corrected here).** The concurrent packet's §7 suggests the
  natural next repair is the population regime (#45). This packet agrees that
  the **residual obstruction is finite sampling**, and adds the qualifier that
  the §3 divergences occur on exponentially improbable realizations; an
  i.i.d.-uniform population limit concentrates on the proportional spectrum,
  where the truth is optimal. So the population and finite statements are
  compatible, and the needed strengthening is probabilistic typicality, not a
  stronger candidate predicate.

Primary sources and the source-faithful theorem boundary are identical in both
packets; nothing here overrides a tracked source-faithful result.

---

## 7. Relation to the other repairs

- **Issue #45 (data regime).** The §3 families show there is no uniform-in-`N`
  likelihood-ratio bound, so a population repair cannot be justified by a
  worst-case finite bound; it must be a typicality/probability statement. Under
  i.i.d. uniform sampling the proportional-sample theorem already gives the
  truth optimality in the limit, so this is consistent with a positive
  population result.
- **Issue #46 (synthesis).** This note is a negative resolution of the
  finite-data model-repair branch: the intrinsic candidate checks alone are
  insufficient; the true-length restriction (or an equivalent data-derived
  length bound) remains necessary for the positive same-length theorem.

---

## 8. Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| Exact definitions of `primitive`, `SR`, `RRF`, strict `I_s`, ratio | mathematical definitions | §1; script |
| `ACGT → ACACGT` survives `P_weak`; both primitive and `SR` | verified computation (exact) | §2 |
| `ACACAC`, `AAAA` are non-primitive and their samples fail `I_s` coverage | verified computation | §2 |
| `ABACABC → ABAC` survives `P_weak` and `P_strong` | verified computation (exact) | §2 |
| `AABC → ABC` family has ratio exactly `(4/3)^N` | mathematical proof + verified computation | §3.1 |
| `ABACABC → ABAC` family has ratio exactly `(7/4)^k·(7/8)^2` | mathematical proof + verified computation | §3.2 |
| Smallest surviving instances in the stated finite ranges | bounded exhaustive computation | §4 |
| `I_s` does not imply `RRF` (`ABACABC`); `SR` admits the tested `I_s` truths | verified computation + source fact | §5 |
| No uniform-in-`N` likelihood-ratio bound exists for `P_weak`/`P_strong` | mathematical proof + verified computation | §3 |
| Divergent realizations have probability `→ 0`; population limit is compatible with the finite negative | mathematical fact (support restriction) | §0, §7 |
| Independent agreement with the concurrent issue-#48 packet on the witness set | cross-check | §6 |

---

## 9. Reproduction

```bash
python3 scripts/issue48_intrinsic_candidate_search.py
# optional, slower exhaustive minimality ranges:
python3 scripts/issue48_intrinsic_candidate_search.py --Gmax 6 --Nmax 4 --nmax 6
```

The script is self-contained: it re-implements circular windows, repeats,
triple repeats, interleaving, the strict source bridging predicate, the exact
multinomial ratio, `SR` (by exhaustive spectrum grouping), `RRF` and
primitiveness. It does not import the exploratory search scripts.

Independent supporting computations already in the repository:
`scripts/bridging_spectrum_uniqueness.py` (spectrum fibres, `RRF`), and
`scripts/verify_variable_length_reduction.py` (the `ABACABC` lift and the
proportional reduction).

Primary sources: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) §6.1; Shomorony, Kim, Courtade, Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502 Eq. (1); Bresler, Bresler, Tse,
*Optimal assembly for high throughput shotgun sequencing*,
*BMC Bioinformatics* 14(Suppl 5):S18 (2013).
