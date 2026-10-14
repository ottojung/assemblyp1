# Finite-sample exact-ML success is not monotone in the read count

**Research status:** kernel-checked in Lean against the project's actual
genome / read / likelihood definitions; independently cross-checked by exact
rational arithmetic.  Part of Antonina #281 (integration on top of PR #199,
the #270 finite-read recovery theorem).

## Statement

Fix the binary alphabet `{A,C}` and read length `L = 2`, and the two circular
genomes

```
  truth     S = AAC    (length 3)
  candidate D = AAAC   (length 4)
```

under uniform-start, oriented, error-free sampling.  The uniform-start read
laws are

```
  p_S : AA -> 1/3,  AC -> 1/3,  CA -> 1/3,  CC -> 0
  p_D : AA -> 1/2,  AC -> 1/4,  CA -> 1/4,  CC -> 0
```

so the two distributions are distinct and the Hellinger affinity is
`rho(p_S, p_D) = (1 + sqrt 2) / sqrt 6 ~= 0.9856 < 1`; the exponential
finite-read recovery bound of `AssemblyP1.FiniteReadRecovery` therefore
applies.

Let `succ(n)` be the probability, under `p_S`, that the truth *strictly*
beats `D` in the exact iid product likelihood on `n` reads.  Then

```
  succ(1) = 2/3,   succ(2) = 4/9,   succ(1) > succ(2),
```

so the exact finite-sample ML success probability is **not monotone** in `n`,
even though it tends to `1` as `n -> infinity`.

## Why there are no ties

On a tuple with `a` copies of `AA` and no `CC`, the exact likelihood ratio is

```
  L_D / L_S = 3^n / 2^(2n - a),
```

so `L_D > L_S` iff `a > n * log2(4/3)`.  Since `log2(4/3)` is irrational,
`n * log2(4/3)` is never an integer, so the strict and non-strict success
events coincide for every `n`.  Tuples containing `CC` have probability zero
under `p_S` and do not contribute.

## Formal Lean endpoints

Source: `AssemblyP1/NonmonotonicityWitness281.lean`; independent audit:
`AssemblyP1/NonmonotonicityWitness281Audit.lean`.

- `AssemblyP1.NonmonotonicityWitness281.readLaw_truth_enc4`
- `AssemblyP1.NonmonotonicityWitness281.readLaw_competitor_enc4`
- `AssemblyP1.NonmonotonicityWitness281.succ_one`
- `AssemblyP1.NonmonotonicityWitness281.succ_two`
- `AssemblyP1.NonmonotonicityWitness281.err_one`
- `AssemblyP1.NonmonotonicityWitness281.err_two`
- `AssemblyP1.NonmonotonicityWitness281.success_not_monotone`

All endpoints depend only on `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry`, `admit`, or new axiom.

The read law `readLaw G L` is the uniform-start oriented circular law built
from `AssemblyP1.SourceFaithfulIs.Genome.window`, i.e. the same law as
`AssemblyP1.FiniteReadRecoveryGenome.circularReadPMF`.  The likelihood and
event probability are `AssemblyP1.FiniteReadRecovery.tupleLikelihood` and
`AssemblyP1.FiniteReadRecovery.eventProb`.  The two-genome tuple spaces are
enumerated by `decide` over the finite function types, so the probability
values are computed rather than assumed.

## Independent computation

`scripts/verify_nonmonotonicity_witness_281.py` recomputes `succ(n)` in exact
rational arithmetic in two independent ways --- exhaustive enumeration of all
read tuples and the binomial reduction on the `AA` count --- for `n = 0..6`,
and asserts `succ(1) > succ(2)`, `succ(3) > succ(4)`, `succ(5) > succ(6)`.

## Scope and remaining limits

- This is a two-genome finite candidate class.  It is a finite-sample
  qualitative fact, not a structural classification.
- It does not contradict the exponential error bound: that bound is about the
  eventual rate, and here the affinity is close to one
  (`~0.9856`), so the bound is weak at small `n`.
- It does not address the unbounded primitive-P2 candidate class; a uniform
  exponential rate there requires a separate finite restriction (Antonina
  #270).
