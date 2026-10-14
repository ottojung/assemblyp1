# Finite-read maximum-likelihood reliability: a positive exponential guarantee

**Research status:** The generic finite-PMF proof, its normalized cyclic
read-law adapter, and now the primitive-P2 structural distinguishability
bridge have Lean theorem implementations and explicit axiom audits.  The
full finite-candidate primitive-P2 statistical recovery statement is
`AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence`.
The infinite/unbounded-genome uniform-rate question and extensions to
RC-collapsed observations or MB09's binomial surrogate remain OPEN;
those models are NOT corollaries of this oriented iid result.

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

## Primitive-P2 structural separation — kernel theorem

The directly checked `FiniteReadRecoveryP2Bridge.lean` identifies the
exact uniform-start read law with `PopulationUniqueness.popSpectrum`
**definitionally** (same cyclic occurrences divided by genome length).
Its `equal_read_laws_imply_rotation`,
`hellinger_lt_one_of_primitiveP2_not_rotation`,
`finite_primitiveP2_family_affinity_gap`, and
`finite_primitiveP2_family_confidence` use the explicit external
Eulerian obstruction from the older
`PopulationUniqueness.population_unique_ML_up_to_rotation` theorem.

The final `FiniteReadRecoveryP2Complete.lean` calls the already
kernel-checked `Issue94Complete.population_unique_ML` theorem and
**does not assume an Eulerian obstruction** as an extra argument. Its
endpoints establish:

- Equal oriented read laws for two admissible primitive-P2 genomes
  (possibly different lengths) force equal genome length and rotation
  equivalence.
- Therefore any admissible nonrotational competitor has read-law
  Hellinger affinity strictly below one.
- Any **finite** set of such competitors has a common upper affinity
  `rho_max<1`, including the empty case.
- For any `δ>0`, an exact iid uniformly sampled read count N exists
  after which the probability that ANY wrong nonrotational candidate
  ties or beats the true ML likelihood is at most δ for every n≥N.

The two companion `*Audit.lean` modules print kernel axioms for
each main endpoint. This is a *positive* genome-level finite-sample
recovery guarantee from structural P2 alone, without any
truth-dependent feasibility event and without separate statistical
distinguishability hypotheses.

## Remaining scope limits, not implied by this theorem

1. The formal rotation conclusion already uses
   `PopulationReduction.RotEquiv` and the right
   `SourceFaithfulIs.Genome.window` circular sampling model;
   it does NOT automatically extend to reverse-complement-collapsed
   molecules unless the observation law is made RC invariant.
2. The primitive-P2 candidate family is allowed to contain different
   positive genome lengths, but the set of *candidates being compared*
   must be FINITE. An unrestricted unbounded candidate family is
   infinite, and obtaining uniform rates there requires a new argument.
3. The positive convergence theorem is probabilistic. It does NOT
   assert that the true genome is a finite-sample ML maximizer for
   every data realization: the strict counterexamples still exist.
4. The MB09 §6.1 product-binomial approximation is not the exact iid
   read model here. Its §6.2 flow/maximizer equivalence remains open.

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
