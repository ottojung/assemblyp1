# Circular-genome ranking inversion: exact iid ML vs MB09 §6.1 product-binomial (board issue #259)

_Status: the single-read ranking-inversion witness was kernel-checked in
`AssemblyP1/Section62BinomialRealGenomeInversion.lean` (merged in PR #224).
This follow-up (branch `agent/811bcb6e1e7c-issue259-inversion-theorem`) adds
the missing packaging: both likelihood expressions stated over exact rationals,
an explicit non-vacuity theorem, and a single `ranking_inversion` theorem whose
statement carries the connectedness / equal-fixed-N / single-read hypotheses.
All theorems audit to `{propext, Classical.choice, Quot.sound}` (counts and
non-vacuity need only `propext`).  Independent exact-rational Python
verification in `scripts/verify_real_genome_inversion_259.py` (wired into the
CI `research-docs` job).  This note records a scoped finite witness; it does
not close the general §6.1 sample-uniform maximality classification._

## 1. The witness

Alphabet `{0,1}`, read length `L = 2`, fixed external `N = 100`.  Two genuine
connected circular words:

```
A = 0^51 1^49          oriented 2-mer spectrum (00,01,10,11) = (50,1,1,48)
B = 0^50 1^18 (01)^16  oriented 2-mer spectrum (00,01,10,11) = (49,17,17,17)
```

Sample: a single observed read `00`, i.e. `n = 1` with count vector
`x = (1,0,0,0)` over the oriented alphabet `(00,01,10,11)`.

## 2. The two objectives at n = 1

**Exact joint iid read law** (multinomial point probability):

```
P_A(00) = 1!/(1!0!0!0!) · (50/100)^1 (1/100)^0 (1/100)^0 (48/100)^0 = 50/100 = 1/2
P_B(00) = 49/100
```

so exact ML prefers **A**.

**MB09 §6.1 full-alphabet product of marginal binomials**, retaining every
zero-count coordinate:

```
Lt_A = Binom(1;1,50/100) · Binom(1;0,1/100) · Binom(1;0,1/100) · Binom(1;0,48/100)
     = (50/100)(99/100)^2(52/100) = 127413/500000 = 0.254826
Lt_B = (49/100)(83/100)^3 = 28017563/100000000 = 0.28017563
```

so the §6.1 surrogate prefers **B**: the rankings invert, even though both
candidates have the same fixed external length `N = 100` and are legitimate
circular genomes.

## 3. Lean artifacts

In `AssemblyP1/Section62BinomialRealGenomeInversion.lean`:

* `genomeA`, `genomeB` — the concrete words; `genomeA_len`, `genomeB_len`
  fix `N = 100`.
* `circularTwoCount` — oriented circular window count over all `N` cyclic
  starts; `genomeA_counts`, `genomeB_counts` give the four spectra.
* `circularConnected` — strong connectivity of the 2-mer letter graph
  (`01` and `10` both occur); `witness_nonvacuous` proves both candidates are
  connected, equal-length, full-alphabet circular words.
* `exact_joint_likelihood_A` (`1/2`), `exact_joint_likelihood_B` (`49/100`),
  `surrogate_likelihood_A` (`127413/500000`), `surrogate_likelihood_B`
  (`28017563/100000000`) — the four values as exact rationals.
* `exact_joint_ranks_A`, `surrogate_ranks_B` — the two strict rankings.
* `ranking_inversion` — the packaged statement: non-vacuity hypotheses
  (connected circular words, equal fixed `N = 100`, single read `00`,
  full-alphabet §6.1 product with all zero-count coordinates) conjoined with
  the ranking disagreement.

## 4. Scope and cautions

* This is **not** a Bayesian/ML counterexample: the exact iid ML correctly
  favors `A`.  It separates the §6.1 product-binomial surrogate from the exact
  joint read law as optimization criteria.
* These `L = 2` candidates are **not primitive-P2** (the known length bound
  excludes them), so this witness does **not** refute the primitive-P2
  positive theorems; it is a general §6.1 / #259 source-model comparison.
* The §6.1 sample-uniform maximality question remains distinct from the exact
  joint read law; the `n ≥ 1` all-`00`-reads version of this inversion is in
  `AssemblyP1/Section62BinomialPowerMonotonicity.lean` (see
  `binomial-power-monotonicity-259.md`), and the covered-sample maximality
  classification is in `covered-binomial-maximality-259.md`.
