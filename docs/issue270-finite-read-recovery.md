# Finite-read maximum-likelihood reliability: a positive exponential guarantee

**Research status:** Generic finite-PMF proof complete and locally checked in Lean,
including an independent axiom-audit module.  The *genome-indexed sampling
adapter* and any extension to an unbounded competitor family remain OPEN
(see Antonina #270).  Do not claim the full issue is complete.

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

## Genome-model scope and further work

For oriented error-free reads, circular-genome sampling at a uniform
random start is intended to induce p_D(w) =
(cyclic occurrences of w in D) / length(D).  The project proves a
primitive-P2 population uniqueness theorem for certain candidate
classes, but the generic finite-PMF Lean theorem does not yet provide a
kernel-checked genome-indexed corollary.  The following remain open:

1. Formalize the exact circular-window read law as a normalized pmf on
   a finite common alphabet for truth and all competing genome lengths,
   including cyclic seam windows and lengths below read length if allowed.
2. Prove the read law descends to the intended rotation quotient; a
   reverse-complement quotient additionally requires an RC-invariant
   observation model, not just a declared equivalence relation.
3. Instantiate the primitive-P2 population uniqueness theorem to show
   distinct candidate orbits give distinct read laws, with assumptions
   on L and admissible candidate classes made explicit.
4. State the genuinely FINITE candidate restriction.  The unrestricted
   family of circular genomes of unbounded lengths is not finite and
   is not covered by the uniform rate without extra arguments.

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
