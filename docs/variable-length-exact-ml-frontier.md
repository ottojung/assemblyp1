# Variable-length exact ML on the fixed-length witness: strengthening, not restoration

_Status: mathematical proof + exact-rational computation + a kernel-checked
finite Lean theorem. 2026-09-20. Independent of the Section 6.2 flow-feasible
set. This note does not settle which maximum-likelihood layer the published
Shomorony et al. open question intends; it analyzes the literal
Medvedev–Brudno §6.1 exact objective with candidate-dependent length._

Primary sources and repository anchors:

- P. Medvedev and M. Brudno, “Maximum Likelihood Genome Assembly,”
  *J. Comput. Biol.* 16(8), 2009, 1101–1116, §6.1, DOI
  [10.1089/cmb.2009.0047](https://doi.org/10.1089/cmb.2009.0047), full text
  [PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/).
- `docs/source-notes/medvedev-brudno-candidate-class.md`: the §6.1 objective
  uses the candidate's own length `N(D)`; no fixed competitor length is imposed
  there, unlike the later separable/binomial approximation which replaces
  `N(D)` by an external constant `N`.
- `docs/fixed-length-exact-counterexample.md` and
  `AssemblyP1/FixedLengthExactCounterexample.lean`: the kernel-checked
  fixed-length witness `S = AAABB`, `L = 3`.
- `docs/exact-variant-e-counterexample.md` and
  `AssemblyP1/ExactVariantECounterexample.lean`: the repeat-free unrestricted
  witness `S = ACGT`, `L = 2`.

## 0. Question and answer

**Question.** The repository kernel-checks a *fixed-length* exact counterexample
on the source-faithful instance `S = AAABB`, `L = 3`. If the candidate genome
length is allowed to vary — as the literal §6.1 objective prescribes — does the
true genome become maximum likelihood, or does the counterexample survive or
strengthen?

**Answer.** Variable length cannot restore the truth, and on the source-faithful
instance it strictly strengthens the counterexample. Two independent reasons:

1. **Superset (logical).** The unrestricted candidate class contains every
   fixed-length candidate, and the objective is evaluated identically on the
   common candidates. Hence a fixed-length witness that beats the truth is also
   an unrestricted-length witness. Restoration is impossible.
2. **Strict strengthening (quantitative).** For `S = AAABB`, `L = 3`, the best
   same-length competitor has exact ratio `2`, while the best unrestricted
   competitor has exact ratio `500/243 ≈ 2.0576`, attained at lengths
   `9, 18, 27, …`. The variable-length maximizer is a nontrivial plateau.

A secondary exploratory `L = 2` instance shows a stronger degeneracy: the
unrestricted optimum can fail to exist (only a supremum is approached), making
the literal “maximum-likelihood sequence” ill-posed for that observation.

## 1. Assumptions and candidate class (kept exact)

- Alphabet `Σ`; read length `L ≥ 1`.
- True circular genome `S` of length `G = |S|`; its `L`-mer spectrum
  `d_S : Σ^L → ℤ_{≥0}` with `Σ_i d_S(i) = G`.
- `N` error-free reads with observed type counts `x = (x_i)`, `Σ_i x_i = N`.
- **Exact §6.1 objective** for a nonempty circular candidate `D` of length
  `n = |D|` and spectrum `d_D`:

  ```text
  L_exact(D | x) = N! / (∏_i x_i!) · ∏_i ( d_D(i) / n )^{x_i} ,
  ```

  with the product over all types and `0^0 = 1`. The observation-only
  coefficient cancels in ratios, so

  ```text
  L_exact(D|x) / L_exact(S|x) = ∏_{i: x_i>0} ( G · d_D(i) / ( n · d_S(i) ) )^{x_i} ,
  ```

  taken as `0` when some observed type has `d_D(i) = 0`.
- **Candidate class (unrestricted exact Variant E):** every nonempty circular
  genome `D` of any length `n ≥ 1` over `Σ`. This is the literal §6.1 class;
  fixed length `n = G` is a *named restriction* used elsewhere in the
  repository, not a default. Genome realizability of a count vector `(d_i)` is
  an extra constraint: a length-`n` circular word corresponds exactly to a
  connected Eulerian multigraph on `(L-1)`-mer vertices with `n` edges.
- **Not assumed:** any length prior, tie-break, or restriction to the §6.2
  flow-feasible set. Ties are handled only by exhibiting strict witnesses.

## 2. Variable length cannot restore the truth

**Lemma (lifting).** If the truth `S` is not an exact-ML maximizer among
candidates of length `G`, it is not an exact-ML maximizer over the unrestricted
candidate class.

**Proof.** The unrestricted class contains every length-`G` circular genome, and
`L_exact(·|x)` is defined the same way on them. A strict fixed-length competitor
is therefore a strict unrestricted competitor. ∎

**Consequence.** Every fixed-length exact counterexample is automatically an
unrestricted-length exact counterexample. In particular the witness of
`docs/fixed-length-exact-counterexample.md` already refutes any hope that
“letting the length vary” repairs bridging-forces-ML. The remaining question is
only how much variable length *strengthens* the failure, addressed next.

## 3. Source-faithful instance `S = AAABB`: exact unrestricted optimum

Instance: `S = AAABB` (`G = 5`), `L = 3`, realized starts `0, 1, 4`, observed
types `{AAA, AAB, BAA}` each with multiplicity one. Its spectrum is
`d_S(AAA) = d_S(AAB) = d_S(BAA) = 1`; the fixed-length witness `AAAAB` has
ratio `2`.

**Theorem (unrestricted optimum `500/243`).** For this observation, for every
nonempty circular candidate `D` of any length over any alphabet,

```text
L_exact(D|x) / L_exact(S|x)  ≤  500/243 = 2.057613168… ,
```

and the bound is attained, for example by `D_1 = AAABAAAAB` (length `9`) and by
`D_k = (A^3 B A^4 B)^k` (length `9k`) for every `k ≥ 1`.

**Proof.** Write `n = |D|`, `α = d_D(AAA)`, `β = d_D(AAB)`, `γ = d_D(BAA)`.
Only observed types contribute, so

```text
R(D) = 125 · α β γ / n³ .
```

1. *Projection to two symbols.* Delete from `D` every symbol other than `A` and
   `B`. Projection is injective and order-preserving on positions and maps each
   occurrence of `AAA`, `AAB`, `BAA` to an occurrence of the same type, so
   `α, β, γ` do not decrease while `n` does not increase. Hence `R` does not
   decrease and it suffices to bound binary circular words.
2. *Run identities.* For a binary circular word containing both symbols, let
   `x` be the number of maximal `A`-runs of length `≥ 2`. Each such run is
   followed by a `B` and preceded by a `B`, so exactly one `AAB` is the last two
   `A`s of the run and exactly one `BAA` is the first two `A`s. Hence
   `β = γ = x`. If `L₂` is the number of `A`s in runs of length `≥ 2`, then
   `α = L₂ − 2x`.
3. *Length lower bound.* Let `s` be the number of `A`-runs of length `1`. There
   are `x + s` `A`-runs and equally many `B`-runs, each of length `≥ 1`, so the
   number of `B`s is at least `x + s`, while the number of `A`s is
   `L₂ + s = α + 2x + s`. Therefore

   ```text
   n ≥ (α + 2x + s) + (x + s) = α + 3x + 2s ≥ α + 3x .
   ```

4. *Optimization.* By weighted AM–GM, subject to `α + 3x ≤ n`,

   ```text
   α x² ≤ (n/3)·(2n/9)² = 4n³/243 ,
   ```

   with equality exactly when `α = n/3`, `x = 2n/9` (feasible for `n = 9k`).
   Hence

   ```text
   R(D) = 125 · α x² / n³ ≤ 125 · 4/243 = 500/243 .
   ```

   Equality is realized by `D_k = (A^3 B A^4 B)^k`: each block contributes
   `α = 3`, `x = β = γ = 2` over length `9`, so `R = 125·12/729 = 500/243`. ∎

### 3.1 Consequences

- **Strict strengthening.** The same-length optimum is `2`; the unrestricted
  optimum is `500/243 > 2`. Variable length buys a strictly larger winning
  margin, so it does not restore the truth.
- **Plateau / non-uniqueness.** `500/243` is attained at every length `9k` and
  by many words at each such length; the maximizer is highly non-unique.
- **Bounded, no escape to infinity.** Each factor satisfies
  `d_D(i)/n ≤ 1`, so the likelihood part is `≤ 1` for every candidate. The
  ratio is bounded and, here, attained.
- **Fixed-length check.** Exhaustion of all `4^5` length-`5` circular genomes
  gives maximum ratio exactly `2`, confirming the strengthening is due to
  variable length, not a different witness.

## 4. Kernel-checked finite consequence

`AssemblyP1/VariableLengthExactCounterexample.lean` kernel-checks the concrete
strict witness for this instance under the unrestricted candidate class:

- `truth = AAABB` (length `5`), `competitor = AAABAAAAB` (length `9`);
- exact likelihoods `6/125` and `8/81`, ratio `500/243 > 1`;
- the same non-vacuous `I_s` certificate as the fixed-length witness: coverage
  of the truth by the reads at starts `0, 1, 4`, plus a maximal length-1 triple
  repeat all of whose copies are bridged.

The theorem `variable_length_exact_counterexample` concludes
`SourceHypotheses truth ∧ ¬ IsMaximumLikelihood truth`, where
`IsMaximumLikelihood` quantifies over every nonempty circular genome of any
length. This complements `AssemblyP1/ExactVariantECounterexample.lean`, whose
truth `ACGT` has only *vacuous* bridging obligations: the failure persists even
with a non-vacuous triple repeat.

The Lean file does **not** formalize the sharper `500/243` optimum; that
optimality proof is §3, and is numerically supported by the script below.

## 5. Exploratory `L = 2` instance: the optimum may not exist

For the older, non-source-faithful `L = 2` candidate instance
`S = AACAGG` with sample `{AA: 5, CA: 1, GG: 1}`, the fixed-length witness
`AAAGGC` has ratio `32`. Under unrestricted length the ratio is unbounded above
by `32`: exhaustive connected-Eulerian search over all candidates of length
`n ≤ 21` gives, for example, `1024/3 ≈ 341.3` at `n = 18`, and the exact
supremum is

```text
6⁷ · (5/7)⁵ · (1/7) · (1/14) = 437400000/823543 ≈ 531.1198 .
```

**Sketch (non-attainment).** The relevant connector structure has
`d_D(AA) = a`, `d_D(GG) = g`, `d_D(CA) = c`, `d_D(AC) = c − 1`,
`d_D(GC) = d_D(AG) = 1`, with `n = a + g + 2c + 1` and ratio
`6⁷ a⁵ c g / n⁷`. Balance at `C` gives `n ≥ a + g + 2c`; equality forces all
remaining edges to be `AC`, disconnecting the `GG` self-loop, so connectivity
upgrades it to `n ≥ a + g + 2c + 1`. Weighted AM–GM with weights `5 : 1 : 1`
over `(a, g, 2c)` then yields the strict bound above, while the family
`M(a, g, c)` approaches it as `n → ∞`. Hence no finite candidate attains the
supremum: the unrestricted exact-ML maximum does not exist for this
observation.

This instance is exploratory because `AACAGG` fails the all-bridged
triple-repeat clause of the source `I_s` conditions; it is included only to
exhibit a second, different degeneracy of the literal §6.1 objective.

## 6. Relation to the fixed-length result and to the open question

- Against the **fixed-length** witness, the answer is: variable length does not
  restore the truth; it strictly strengthens the counterexample (`2 → 500/243`).
- Against the **unrestricted exact** layer, this note confirms and quantifies
  the failure already witnessed on `ACGT`, now with non-vacuous bridging and an
  exact optimum.
- This note does **not** decide whether the published 2016 open question intends
  the exact §6.1 objective, the separable/binomial approximation, or the §6.2
  flow-feasible set. The §6.2 set is deliberately not used or analyzed here.
- This note does not address tie-breaking or reverse-complement equivalence.

## 7. Reproducibility

```bash
python3 scripts/verify_variable_length_frontier.py
```

Uses only the standard library and exact rational arithmetic, re-derives
`L`-mer spectra from first principles, imports no repository search code, and
asserts every displayed value, including: the fixed-length maximum `2`;
the binary exhaustive maximum `500/243` for all circular words of length
`≤ 22`; the ternary maximum for lengths `≤ 9`; the run identities and the
length bound `n ≥ α + 3x` over all binary words of length `≤ 18`; the family
`D_k`; the `L = 2` exhaustive maxima for lengths `13 ≤ n ≤ 21`; the structural
bound `n ≥ a + g + 2c + 1`; and the growth family approaching the supremum.
The default run takes a few minutes, dominated by the matrix enumeration.

```bash
lake build AssemblyP1.VariableLengthExactCounterexample
```

kernel-checks the finite unrestricted counterexample with the non-vacuous
bridging certificate.

## 8. Epistemic classification

| Claim | Class | Where |
|-------|-------|-------|
| Lifting: fixed-length witness ⇒ unrestricted witness | Mathematical proof | §2 |
| `S = AAABB` unrestricted optimum is exactly `500/243`, attained at lengths `9k` | Mathematical proof | §3 |
| Fixed-length maximum for `S = AAABB` is exactly `2` | Exhaustive exact computation (`4^5`) + kernel-checked witness | §3.1 |
| Binary/ternary exhaustive and run-identity checks | Exact bounded computation | §7 |
| Non-vacuous `I_s` witness refuted under unrestricted length | **Kernel-checked** (Lean) | §4 |
| `L = 2` `AACAGG` supremum `437400000/823543` not attained; no maximum | Mathematical proof (sketch in §5) + exact bounded search | §5 |
| Which ML layer the 2016 sentence intends | Unresolved (source ambiguity) | §6 |

## 9. Non-claims

This note does not settle the published open question, does not claim the
fixed-length, binomial-approximation, or §6.2 flow-feasible targets, and does
not claim that `500/243` is optimal when the alphabet is restricted by any
constraint beyond “nonempty circular genome of any length.” The `L = 2`
non-attainment proof is sketched and confirmed numerically; its full
formalization is not part of this note.
