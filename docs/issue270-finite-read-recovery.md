# Finite-read maximum-likelihood reliability: a positive exponential guarantee

**Research status:** The generic finite-PMF proof AND its uniform-start,
oriented circular-genome read-law adapter are locally checked in Lean with
independent axiom audits and kernel checking.  The primitive-P2
distribution-identifiability/orbit bridge and extension to an unbounded
candidate family remain OPEN (Antonina #270); the whole issue is not closed.

## Statement

Let W be a finite read alphabet and let p be the true probability mass function
on W.  Let Θ be a finite family of *incorrect, distributionally distinguishable*
probability mass functions q.  Observe n iid reads with law p, scoring a
candidate q by the exact likelihood L_q(r) = product of q(r_j).

Define the Hellinger/Bhattacharyya affinity
ρ(p,q) = sum over w in W of sqrt(p(w) q(w)).
Nonnegative normalized probability laws satisfy 0 ≤ ρ ≤ 1, with equality ρ = 1
if and only if p=q.  Consequently all incorrect q in a finite identifiable
family satisfy a uniform bound ρ(p,q) ≤ ρ_max < 1.

**Theorem (finite-family exact-ML recovery).** The probability, under the true
law p, that at least one q in Θ *ties or beats* p's exact sample likelihood is
at most

    sum(q in Θ) ρ(p,q)^n ≤ |Θ| * ρ_max^n.

Thus wrong-selection probability tends to zero exponentially; for every
δ>0 some N ensures the failure probability is at most δ at all n≥N.
Ties are counted as potential failure, so arbitrary ML tie-breaking is covered.

The proof is elementary and *does not divide by any probabilities*.
For each observed tuple r, on L_q(r)≥L_p(r) one has
L_p(r) ≤ sqrt(L_p(r)*L_q(r)).  Summing and exploiting iid
factorization gives the pairwise affinity^n bound. A finite union bound
supplies the complete family estimate.

## Formal Lean endpoints

- AssemblyP1.FiniteReadRecovery.hellinger_sq_identity
- AssemblyP1.FiniteReadRecovery.hellinger_le_one
- AssemblyP1.FiniteReadRecovery.hellinger_lt_one_iff_ne
- AssemblyP1.FiniteReadRecovery.eventProb_pairwise
- AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_sum
- AssemblyP1.FiniteReadRecovery.eventProb_wrong_le_card
- AssemblyP1.FiniteReadRecovery.eventProb_wrong_tendsto_zero
- AssemblyP1.FiniteReadRecovery.exists_n_for_confidence
- AssemblyP1.FiniteReadRecovery.il_confidence_99

Source: AssemblyP1/FiniteReadRecovery.lean.  Independent audit:
AssemblyP1/FiniteReadRecoveryAudit.lean.  These give a positive,
quantitative reliability result in the exact iid model, not only a
population or negative-counterexample statement.

## Genome-model instantiation (kernel checked)

The additional module `AssemblyP1/FiniteReadRecoveryGenome.lean` works with
the ACTUAL `SourceFaithfulIs.Genome.window` circular word model.  It proves:

- `circularReadPMF_isPmf`: choosing each of the genome's G cyclic starting
  positions with probability 1/G produces a normalized, nonnegative pmf
  on the finite universe of oriented length-L words.
- `circularReadPMF_eq_count`: p_D(w) equals the cardinality of cyclic
  occurrence starts that spell w divided by G, preserving repeated read
  strings, origin-crossing reads, and read lengths L>G (periodic wrapping).
- `circular_pairwise_bound`: the pairwise exact-ML Hellinger bound for
  two actual circular genomes, even of different lengths.
- `readLawFamily_all_pmf`, `circular_wrong_le_sum`,
  `circular_wrong_le_card`, `circular_wrong_tendsto_zero`,
  `circular_exists_n_for_confidence`: the finite CANDIDATE GENOME family
  versions of the union-bound, uniform-rho, asymptotic and confidence
  guarantees.  The strict rho_max<1 hypothesis is EXPLICIT, not
  silently asserted for all genome pairs.

These adapter results are independently audited by
`AssemblyP1/FiniteReadRecoveryGenomeAudit.lean`, with a separate kernel
checker.  They are quantitative positive reconstruction guarantees already
phrased in the genome universe under the stated separation condition.

## Remaining structural research

1. Prove that the read law descends to the intended rotation quotient;
   a reverse-complement quotient additionally requires an RC-invariant
   observation model, not merely a declared equivalence relation.
2. Instantiate the kernel-checked primitive-P2 population uniqueness
   theorem to show distinct candidate orbits give distinct read laws
   for the exact same oriented-length-L model, with admissibility
   assumptions and length bounds explicit.  This would produce
   rho_max<1 for a finite family of *wrong* orbits rather than requiring
   the bound as an input.
3. The unrestricted circular-genome candidate class of unbounded lengths
   is NOT finite and is not covered by a uniform rate absent further
   arguments.  Neither the exact PMF theorem nor the generic union bound
   proves a guarantee for that unrestricted class.

The binomial product surrogate of Medvedev--Brudno 2009 is a different
likelihood model; this theorem does not establish its finite-sample
maximality or consistency.  Nor does it use the truth-dependent
Not-So-Greedy information-feasibility event.

### Provenance

The inequality is the standard Bhattacharyya/Hellinger pairwise affinity
bound for finite hypothesis testing, with a finite union bound.  The
contribution here is the explicit Lean implementation, audit, and
carefully scoped connection to genome assembly.  This is not presented
as a new statistical inequality.
