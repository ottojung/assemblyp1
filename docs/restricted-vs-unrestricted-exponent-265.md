# The uniform exact-ML exponent over restricted and unrestricted genome universes (#265)

Status: 2026-10-19. Owner: agent `d6d175111bbf`. Base: `main` @ `5975442`.
Scope: research note + exact verifier. It touches no slide, paper, or CI file.

This note answers the three bounded research questions recorded as the
genuinely open #265 items about the uniform exact-ML error exponent:

1. is the exponent `1/(8 B^4)` of Theorem `thm:p2-uniform-rate`
   (`paper/sections/05-population.tex`) tight for the primitive-P2 class, or
   can it be improved?
2. does a uniform positive separation / exponential exact-ML error rate extend
   to the **unrestricted** genome universe (candidates of arbitrary positive
   length)?
3. if finite-`n` exact-ML recovery does not hold uniformly over all lengths,
   what is the precise obstruction and the minimal extra assumption that
   restores it?

The two headline verdicts are:

- **(2) is definitively false.** Over a candidate universe that is not
  length-bounded, exact read-law collisions exist (`AB` and `ABAB` have the
  *same* oriented circular read law at every read length), so the truth's own
  read law lies in the candidate read-law family and the exact-ML error
  probability is `1` for every `n`. No exponential decay, uniform or otherwise,
  is possible. The theorem's hypothesis that every competitor have a read law
  distinct from the truth is exactly what fails.
- **(1) the exponent is not tight.** The theorem's `1/(8 B^4)` is a valid but
  loose lower bound on the true worst-case separation. Complete enumeration of
  the primitive-P2 class at `B = 4, 6, 8, 16` gives exact worst-case
  separations `0.1340, 0.0871, 0.0646, 0.0318`, exceeding the theorem's bound
  by factors `274, 903, 2116, 16648`. The extremal pairs are one-symbol
  insertions with separation `Theta(1/B)`, so the sharp exponent is
  conjecturally `1`, not `4`; the theorem is loose by `Theta(B^3)`.

This note is deliberately careful about epistemic class. The finite exact
computations below are reproducible by an exact-arithmetic script; the
asymptotic exponent statement is a **conjecture** with an explicitly named
missing lemma; no new claim here is kernel-checked, and no external standard
statistics is upgraded to Lean.

## Model and definitions (exact, matching the Lean names)

Fix a finite alphabet `alpha` with `q = |alpha|` and read length `L >= 2`.
A circular genome `S` has length `G_S = |S| >= 1` and symbols indexed on the
circle. A read of length `L` at start `r` is the circular window
`S.window L r` (`AssemblyP1.SourceFaithfulIs.Genome.window`). The oriented
uniform-start read law is

```
circularReadPMF S L w = #{r : Fin |S| : S.window L r = w} / |S|
```

(`AssemblyP1.FiniteReadRecoveryGenome.circularReadPMF`). Two read laws `p, q`
have Hellinger affinity `rho(p,q) = sum_w sqrt(p(w) q(w)) in [0,1]`, with
`rho = 1` iff `p = q`; the exact product likelihood of i.i.d. reads
`R_1,...,R_n` is `L_D = prod_i p_D(R_i)`, and ties count as errors. The
wrong-selection event is `exists D : L_D >= L_S`
(`AssemblyP1.FiniteReadRecovery.wrongEvent`).

Primitivity is "not a nontrivial whole-genome repetition"
(`AssemblyP1.PopulationReduction.IsPrimitive`). The structural predicate `P2`
(`AssemblyP1.P2`) forbids maximal triple repeats of length `>= L-1` and
interleaved maximal repeat pairs with both constituents of length `>= L-1`.
The admissible class is `AdmClass = IsPrimitive and P2`
(`AssemblyP1.PopulationUniqueness.AdmClass`). The kernel-checked length bound is

```
G <= B,     B = 2 q^(L-1)
```

(`AssemblyP1.PrimitiveP2FiniteClass.primitive_P2_len_le`), so the primitive-P2
class is finite. Theorem `thm:p2-uniform-rate` proves, for a primitive-P2 truth
`S` and its non-rotational primitive-P2 competitors,

```
1 - rho(p_S, p_D) >= 1/(8 (G_S G_D)^2) >= 1/(8 B^4),
Pr_S{ exists D : L_D >= L_S } <= N_C exp(-n/(8 B^4)),   N_C <= sum_{g=1}^B q^g.
```

Kernel endpoints: `readLaw_separation`, `one_sub_hellinger_ge_of_gap`,
`hellinger_le_of_length_bound`, `exp_error_bound_of_length_bound`,
`primitiveP2_exponential_error_bound`, `primitiveP2_ML_confidence_explicit`
(`AssemblyP1/PrimitiveP2UniformSeparation.lean`).

## (2) The unrestricted universe: uniform exponential decay fails

### Proposition (repetition read-law collision)

Let `S` be a circular genome of length `G >= 1`, let `m >= 2`, and let `D` be
the `m`-fold repetition of `S`, i.e. `|D| = mG` and `D_i = S_{i mod G}`. Then
for **every** read length `L`,

```
circularReadPMF D L = circularReadPMF S L.
```

*Proof.* For any start `t : Fin (mG)` and offset `d : Fin L`,
`D.window L t d = D_{t+d} = S_{(t+d) mod G} = S.window L (t mod G) d`, so
`D.window L t = S.window L (t mod G)`. Thus the map `t |-> D.window L t` on
`Fin (mG)` is the `m`-to-one lift of `r |-> S.window L r` on `Fin G`. Counting
multiplicities,

```
circularReadPMF D L w = #{t : Fin(mG) : D.window L t = w}/(mG)
                      = m * #{r : Fin G : S.window L r = w}/(mG)
                      = circularReadPMF S L w.  QED
```

**Instance.** `S = AB` (`G = 2`) and `D = ABAB` (`m = 2`) are distinct circular
genomes of different lengths (so not rotations of one another) with identical
oriented read laws at every `L`. Checked exactly for `L = 1..6` in
`scripts/verify_exponent_265.py`.

### Corollary (error probability is 1 for every n)

Fix any candidate universe `U` that contains both `S` and its `m`-fold
repetition `D`, and let the candidate read-law family be
`{circularReadPMF C L : C in U}` (the `readLawFamily` of
`AssemblyP1.FiniteReadRecoveryGenome`, which deduplicates equal laws). Then the
truth's own read law is a member of the family (via `D`), so the wrong event
`exists q in family : L_q >= L_S` holds on every sample, and

```
Pr_S{ exists D in U, D not rotation-equivalent to S : L_D >= L_S } = 1
```

for every `n`. Consequently there is no bound of the form
`N_C exp(-c n)` with `c > 0` over `U`, and no `n -> infinity` consistency
either: the truth is never the unique maximizer.

This is not in tension with Theorem `thm:p2-uniform-rate`: that theorem assumes
`hne : forall D in C, circularReadPMF S L != circularReadPMF D L`, which the
unrestricted universe violates. It is also distinct from the finite-`n`
exact-ML *characterization* front (#255): the collision is a law-level
non-identifiability, not a finite-sample fluctuation, and it already holds at
`n = infinity`.

### Vanishing separation even among primitive competitors

If one insists that competitors be primitive (so the exact collision is
excluded), a uniform positive separation still fails. For the primitive-P2
truth `S = AB` and the primitive competitors `D_m = (AB)^m A` (length `2m+1`),

```
p_S(AB) = p_S(BA) = 1/2,
p_{D_m}(AB) = p_{D_m}(BA) = m/(2m+1),   p_{D_m}(AA) = 1/(2m+1),
```

so `sum_w |p_S - p_{D_m}| = 1/(2m+1) -> 0` and
`1 - rho(p_S, p_{D_m}) -> 0` (computed: `0.1835` at `m=1` down to `0.0299` at
`m=8`). Hence `inf_D (1 - rho(p_S, p_D)) = 0` over the primitive universe of
unbounded lengths, and no uniform rate constant `c > 0` exists.

## (1) The primitive-P2 exponent `1/(8 B^4)` is not tight

Because the primitive-P2 class is finite and the verifier enumerates it
completely, the *exact* worst-case separation is computable:

```
gamma(B) = min over valid (S,D) of (1 - rho(p_S, p_D)),
```

where `(S,D)` ranges over primitive-P2 genomes with `D` not a rotation of `S`
and `p_D != p_S`, and `B = 2 q^(L-1)`.

| `q` | `L` | `B` | class size | extremal `S` | extremal `D` | `gamma` | `1/(8 B^4)` | ratio | `gamma * B` |
|----:|----:|----:|-----------:|:-------------|:-------------|--------:|------------:|------:|------------:|
| 2 | 2 | 4 | 14 | `001` | `0011` | 0.133974596 | 4.8828e-4 | 274.4 | 0.5359 |
| 3 | 2 | 6 | 237 | `00112` | `001122` | 0.087129071 | 9.6451e-5 | 903.4 | 0.5228 |
| 2 | 3 | 8 | 90 | `0010011` | `00100111` | 0.064585653 | 3.0518e-5 | 2116 | 0.5167 |
| 2 | 4 | 16 | 1750 | `000101100010111` | `0001011000101111` | 0.031754163 | 1.9073e-6 | 16648 | 0.5081 |

(The exact `q=2, L=2` value is `1 - sqrt(3)/2`; the class size and the extremal
pair are exactly what the verifier reports.)

Observations, all exact:

- **The bound is loose.** `gamma(B)` exceeds `1/(8 B^4)` in every enumerated
  class, by a factor that grows from `274` at `B = 4` to `16648` at `B = 16`.
- **The extremal pair is always a one-symbol insertion** `D = S + (last symbol
  of S)` of lengths `B-1` and `B`. Its read laws differ by `Theta(1/G)` in
  total variation, and the affinity loss is first order, so
  `1 - rho = Theta(1/G) = Theta(1/B)` — not `Theta(1/B^4)`.
- **`gamma(B) * B` is essentially constant** (`0.536, 0.523, 0.517, 0.508`),
  i.e. `gamma(B) = Theta(1/B)` empirically.
- The theorem's exponent ratio therefore grows like `B^3` (`274, 903, 2116,
  16648` against `4 B^3 = 256, 864, 2048, 16384`).

For completeness, the exact large-deviation (Chernoff) exponent of the extremal
pair is also `Theta(1/B)`: `C(p_S, p_{D_extremal}) * B = 1.151, 1.094, 1.068,
1.033`, and `C >= -ln rho_* >= gamma`. So the theorem's `1/(8 B^4)` is loose by
`Theta(B^3)` relative to the true exponent as well, not merely relative to the
Hellinger separation.

### Conjectured sharp statement and the missing lemma

**Conjecture.** There are absolute constants `0 < c_1 <= c_2 < infinity` with

```
c_1 / B  <=  min_{(S,D)} (1 - rho(p_S, p_D))  <=  c_2 / B
```

over primitive-P2 pairs of lengths `<= B`, so the sharp uniform Hellinger
exponent of exact-ML error is `Theta(1/B)` (and the Chernoff exponent is
`Theta(1/B)`), improving `1/(8 B^4)` by `Theta(B^3)`.

The missing lemma has two halves; either would be a kernel-checkable advance:

1. **Lower bound.** For every pair of primitive-P2 genomes with lengths
   `G_S, G_D <= B` and distinct read laws,
   `1 - rho(p_S, p_D) >= c_1 / B` for an absolute `c_1 > 0`. The existing
   proof only extracts `1/(8 (G_S G_D)^2)` from a single pointwise gap; the
   one-symbol-insertion extremals show that the pointwise gap `1/(G_S G_D)` is
   itself far from tight when the lengths are nearly equal (there the
   numerator is `G (c_S - c_D) + O(1)`, so the gap is `Theta(1/G)`), and a
   sharper argument must exploit that.
2. **Upper bound / construction.** A parametric family of primitive-P2
   one-symbol-insertion pairs at every `B` with `1 - rho <= c_2 / B`. The
   verifier exhibits such pairs at `B = 4, 6, 8, 16` by exhaustive search, but
   no general construction is proved here.

Until (1) is proved, the exact non-tightness statements in the table are
finite-class facts, not an asymptotic theorem.

## (3) Precise obstruction and minimal restoring assumptions

Over the unrestricted genome universe (arbitrary positive candidate lengths)
the uniform exponential exact-ML rate fails for three independent reasons, and
the primitive-P2 restriction removes exactly these:

1. **Non-identifiability (read-law collisions).** Periodic multiples
   (`D = S^m`) share the truth's read law, so the wrong event is certain and
   the error is `1` for every `n`. *Necessary assumption:* competitors must be
   read-law-distinct from the truth (identifiability **modulo read law**, not
   merely modulo rotation). The primitive-P2 class gives this up to rotation
   via population uniqueness.
2. **Vanishing separation.** Even with distinct laws, unbounded lengths let
   `inf_D (1 - rho(p_S, p_D)) = 0` (the `(AB)^m A` family). *Necessary
   assumption:* a uniform separation margin, equivalently a length bound (the
   `B` of `primitive_P2_len_le`); without it no positive rate constant exists.
3. **Infinite candidate family.** An unbounded universe has infinitely many
   candidates, so the union-bound prefactor `N_C` is not finite. *Sufficient
   assumption:* a finite (or entropy-controlled) candidate family; the length
   bound `B` makes the primitive-P2 class finite.

**Minimal restoring assumption.** A length bound on the candidate class
(equivalently, uniform discreteness of the candidate read laws) plus exclusion
of read-law duplicates. The primitive-P2 restriction supplies all three
conditions simultaneously; nothing weaker is known to suffice, and conditions
1 and 2 are each individually necessary (the propositions above are
counterexamples to each in isolation).

If only *pointwise* recovery for a fixed finite class is wanted, the
finite-candidate Proposition `prop:strong-consistency` (paper §5) already
suffices and needs no length bound; it is the *uniform* rate over an unbounded
universe that is impossible.

## What is not claimed

- No new kernel-checked theorem. The repetition-collision proposition is proved
  by hand and checked exactly by `scripts/verify_exponent_265.py`; the
  primitive-P2 separation values are exact finite computations by the same
  script; the asymptotic exponent statement is a conjecture.
- No change to Theorem `thm:p2-uniform-rate`'s validity. It remains correct and
  kernel-checked; this note only shows its exponent is conservative.
- No claim about the MB09 §6.1 product-binomial surrogate or the §6.2 flow
  model, and no duplication of the #255 finite-ML characterization front.
- No claim that the exact Chernoff/large-deviation exponent is kernel-checked;
  the Chernoff facts are the external standard results already recorded in
  `docs/chernoff-exponent-finite-recovery-265.md`.

## Sources

- Kernel: `AssemblyP1/PrimitiveP2UniformSeparation.lean`
  (`readLaw_separation`, `one_sub_hellinger_ge_of_gap`,
  `hellinger_le_of_length_bound`, `exp_error_bound_of_length_bound`,
  `primitiveP2_exponential_error_bound`, `primitiveP2_ML_confidence_explicit`,
  `readLawFamily_card_le`);
  `AssemblyP1/FiniteReadRecoveryGenome.lean` (`circularReadPMF`,
  `readLawFamily`, `circular_wrong_le_sum`);
  `AssemblyP1/PrimitiveP2FiniteClass.lean` (`primitive_P2_len_le`, `maxLen`,
  `nonRotationalCandidates`, `primitiveP2Class_finite`);
  `AssemblyP1/PopulationUniqueness.lean` (`AdmClass`, population uniqueness);
  `AssemblyP1/P2.lean`, `AssemblyP1/SourceFaithfulIs.lean`,
  `AssemblyP1/PopulationReduction.lean` (`IsPrimitive`).
- Paper: `paper/sections/05-population.tex` (Theorem `thm:p2-uniform-rate`,
  Theorem `thm:finite-recovery`, Proposition `prop:strong-consistency`,
  Corollary `cor:p2-finite-recovery`); `paper/sections/03-open-question.tex`
  (Remark `rem:sample-complexity`, Corollary `cor:explicit-sample-size`).
- Companion notes: `docs/chernoff-exponent-finite-recovery-265.md`,
  `docs/sample-complexity-265.md`, `docs/minimax-finite-recovery-265.md`,
  `docs/audit-265-centering-2026-10-15.md`.
- Standard statistics (cited, **not** kernel-checked): Cover & Thomas (2006),
  *Elements of Information Theory*, §11.9 (Chernoff information); Tsybakov
  (2009), *Introduction to Nonparametric Estimation*, Ch. 2 (Hellinger /
  total variation and the large-deviation exponent); Le Cam (1986) for the
  two-point method.
- Verifier: `scripts/verify_exponent_265.py` (exact rational read laws; exact
  collision and class enumeration; run with `python3
  scripts/verify_exponent_265.py`, exit `0`).
