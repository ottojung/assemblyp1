# Primitive-P2 ambiguity after collapsing reverse-complement read classes

**Evidence:** general mathematical proof, independent finite exact verifier for
read lengths 2 through 12; **not yet Lean formalized**.

## The defined observation model

For a circular genome of length G and reads of length L>=2, choose a start
uniformly and observe the oriented circular read. Erase orientation, keeping
its unordered reverse-complement class [w] = {w, RC(w)}. The probability of
a class sums the occurrence counts of its **distinct** oriented words;
palindromic reverse complements are counted only once.

## Theorem

For every L>=2 over DNA, the length-2L circular genomes

    S_L = A^L C T^(L-1)
    D_L = A^L G T^(L-1)

are both primitive and satisfy the source-faithful maximal-repeat P2
predicate at read length L. They are neither rotationally nor dihedrally
equivalent. Their *oriented* read laws differ, but their length-L
reverse-complement **class** read laws coincide.

## Proof

Only the unique C (respectively G) differs. Every length-L read avoiding
that position is identical in the two genomes. The reads that contain C
in S_L are exactly

    A^j C T^(L-1-j), j=0,...,L-1,

one for each j. Its reverse complement is

    A^(L-1-j) G T^j,

which is exactly one of the G-containing reads in D_L. Thus each altered
read is replaced by a read in its same reverse-complement class and the
class-count multisets are identical.

They cannot be rotations because S_L has a C and no G, while D_L has G
and no C. RC(S_L) has maximum A-run length L-1 and D_L has A-run length
L, so they are not RC rotations. The sole C/G in each genome precludes a
nontrivial periodic power, hence both are primitive.

To prove P2 in the *exact* sense of AssemblyP1/P2.lean and
AssemblyP1/SourceFaithfulIs.lean, we establish the stronger property:
the only duplicated circular word of any length k >= L-1 and k < 2L
is A^(L-1), occurring precisely at starts 0,1. Indeed a window
containing the unique C/G cannot be duplicated. Every other window is
a substring of the single C/G-free linear stretch T^(L-1) A^L. In that
stretch a mixed T^a A^b window is uniquely determined by its position
relative to the sole T-to-A junction, a pure T^k window with k>=L-1
appears at most once, and a pure A^k window is repeated only for
k=L-1. Thus no triple occurrence of a long word exists, and there
cannot be two long maximal repeat pairs with four interleaved starts.
The two P2 clauses follow, including selected-occurrence maximality.

At L=3 the example is AAACTT versus AAAGTT. The common molecule-class
histogram has AAA/TTT:1, AAC/GTT:1, AAG/CTT:1, ACT/AGT:1,
TAA/TTA:2.

Run: python3 scripts/verify_rc_p2_ambiguity.py.
The verifier checks the exact maximal-pair, maximal-triple and cyclic
interleaving definitions rather than a weaker generic repeat heuristic.

**Scope limitation:** This refutes primitive-P2 uniqueness for this
explicit strand-collapsed read-class model, not the established *oriented*
P2 population uniqueness theorem. The relation of this observation model
to the full physical reverse-complement MB09 sampling and bidirected-flow
likelihood is a separate open question (#422). Do not claim that historical
source-model implication without a verified transport theorem.
