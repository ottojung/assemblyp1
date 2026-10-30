# Cubic rather than quartic uniform finite-read recovery exponent

**Status:** a mathematical proof combining previously kernel-checked
primitive-P2 multiplicity and finite-read union-bound lemmas with elementary
inequalities. The improved end-to-end rate is **not yet a Lean declaration**.
Source task: GitHub issue #423.

## Theorem

Fix an alphabet size q>=2, an oriented read length L>=2, and the
primitive-P2 candidate class C at L. Every genome length is <=
B = 2q^(L-1) by the formalized P2 length-bound theorem. For any two
nonrotation-equivalent S,D in C, their oriented read laws p and r satisfy

    1 - rho(p,r) >= 1/(16 B^3).

Thus ordinary exact maximum likelihood over C satisfies the uniform
finite-iid error bound

    P_S(error after n reads) <= N_C exp(-n/(16 B^3)),

where N_C is the same bound on competing rotation classes as in the
existing Lean theorem (at most sum_{G=1}^B q^G). In particular it
suffices that n >= 16 B^3 log(N_C/epsilon) for error <= epsilon.

This improves the earlier kernel-checked 1/(8 B^4) gap but does NOT
establish the conjectural order 1/B.

## Proof

Let G=|S| and H=|D|, both <=B. At each oriented L-word w the laws
have the integer-count form p(w)=c(w)/G and r(w)=d(w)/H.

We first show c(w),d(w)<=2. If L<=G, the prefix of each L-mer
occurrence is an (L-1)-mer occurrence. The kernel-checked
AssemblyP1.P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive
bounds each such (L-1)-mer count by 2 under the primitive-P2
hypotheses. If L>G, two equal length-L circular windows at different
starts would already have equal length-G initial windows and hence
make the genome invariant under a nontrivial shift, contrary to
primitivity. The same argument applies to D.

By oriented P2 population uniqueness, nonrotation-equivalent S,D
have distinct laws. The kernel-checked
PrimitiveP2UniformSeparation.readLaw_separation therefore yields
some w with delta=|p(w)-r(w)| >=1/(GH), since the nonzero
cross-multiplied integer count difference has magnitude >=1.

For this coordinate p+r>0, and by Cauchy/AM-QM,

    (sqrt(p)+sqrt(r))^2 <= 2(p+r)
    p+r <= 2/G + 2/H = 2(G+H)/(GH).

Hence the Hellinger identity gives

    1-rho = (1/2) sum_v (sqrt(p(v))-sqrt(r(v)))^2
          >= delta^2/[4(p(w)+r(w))]
          >= 1/[8GH(G+H)]
          >= 1/[16B^3].

Finally rho^n <= exp(-n/(16B^3)), so the existing finite-class
likelihood-ratio union bound gives the advertised estimator error rate.

## Evidence and proof boundary

The independent exact regression
scripts/verify_p2_cubic_rate.py exhaustively checks rational
integer-count profiles c,d in {0,1,2}^5, normalized by their
respective sums, against every inequality above, including distinct
normalized profiles with unequal denominator lengths. It does not
assert that arbitrary count profiles spell genomes; they verify the
algebraic step, not the combinatorial P2 count cap.

The cap, oriented population uniqueness and old Hellinger union bound
already have Lean proofs. The short-genome L>G argument and improved
numeric inequality have a complete paper-level proof here; they are
targets for new direct Lean endpoints. This theorem does not cover
unrestricted candidates or reverse-complement molecules.
