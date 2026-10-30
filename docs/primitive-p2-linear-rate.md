# Linear primitive-P2 oriented Hellinger separation

**Status: a general mathematical proof, not yet a separate Lean kernel theorem.**
The finite regression uses exact integer-ratio bookkeeping and independent
floating-point Hellinger cross-checks. The mathematical proof is analytic.

## Theorem

For a fixed finite alphabet of size q, oriented read length L>=2 and the
complete primitive-P2 candidate class, let B=2q^(L-1). Any two
nonrotational candidates S and D have distinct oriented read laws p and r
and satisfy

    1 - rho(p,r) >= 1/(64 B).

Consequently exact ML over this restricted candidate class has error

    P_S(error after n iid reads) <= N_C exp(-n/(64B)),

where N_C is the same number of competing read laws as in the existing
Lean theorem; N_C <= sum_{g=1}^B q^g. Read count
n >= 64 B log(N_C/epsilon) suffices for error <= epsilon.

This establishes the conjectured uniform lower-bound exponent.
A matching de Bruijn upper family below proves that the worst-case
separation exponent is exactly 1, even for each fixed q>=2 as L
grows. The best leading constant remains open. These results are
paper-proved, not yet separately Lean formalized.

## Proof

Let G=|S|, H=|D| <= B. The oriented L-mer spectrum counts c_w and d_w
are integers in {0,1,2}. To see the upper bound 2 when L<=G,
each L-window occurrence has a prefix (L-1)-window occurrence;
AssemblyP1.P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive is
a **kernel-checked** cap for each prefix under primitive P2.
When L>G, equality of two L-windows at distinct circular starts would
imply equality of their first G characters and therefore a nontrivial
rotational period, contradicting primitivity. So counts are <=1 then.

The probability masses are p_w=c_w/G, r_w=d_w/H, and both sum to 1.
Oriented population uniqueness for primitive-P2 genomes ensures p!=r
for nonrotational S,D.

**Case 1: differing supports.** If one count is zero and the other
positive, its contribution to the Hellinger identity
1-rho = (1/2) sum_w (sqrt(p_w)-sqrt(r_w))^2
is at least 1/(2G) or 1/(2H), hence >=1/(2B).

**Case 2: identical supports.** Let r_w=d_w/c_w on positive support.
Each r_w is one of {1/2,1,2}. The r_w cannot all be identical:
if d_w = r c_w for every positive coordinate, summing gives H=rG
and therefore r_w(probabilities)=p_w for every w, contrary to p!=r.
Choose two indices i,j with distinct integer ratios, and put
a=sqrt(H/G), u_i=sqrt(d_i/c_i), u_j=sqrt(d_j/c_j).
Allowed square-root ratios are {1/sqrt(2),1,sqrt(2)}, whose
pairwise distances are at least 1-1/sqrt(2) > 1/4.
The Hellinger identity now reads

    1-rho = (1/(2H)) sum_w c_w (a - sqrt(d_w/c_w))^2.

Since c_i,c_j >=1, this is at least

    [(a-u_i)^2+(a-u_j)^2]/(2H)
    >= (u_i-u_j)^2/(4H)
    > 1/(64H) >= 1/(64B).

Here the middle inequality follows from
(x^2+y^2)>=((x-y)^2)/2.
The strict irrational bound follows for instance from
1/sqrt(2)<3/4, equivalent after squaring to 1/2<9/16.
Thus the uniform bound holds in both cases.

The existing Hellinger likelihood-ratio inequality
P_S(L_D>=L_S) <= rho(p,r)^n, the inequality
(1-t)^n <= exp(-nt), and the finite-family union bound
give the claimed error rate.

## Matching de Bruijn family: optimal exponent 1

Fix any alphabet size q>=2 and put k=L-1, G=q^k, B=2G.
Let S be a cyclic de Bruijn word of order k: every k-mer occurs
at exactly one circular start. Such words exist by taking an
Euler circuit in the strongly connected q-regular directed graph
of (k-1)-mer vertices and k-mer edges.

Rotate S to start with its unique k-mer A^k. Its maximal A run
has exactly k symbols (otherwise A^k would occur twice).
Let D insert one extra A at the start of that run.

Viewed as a cyclic sequence of k-mer vertices, D visits A^k
twice consecutively and all other k-mers once. This inserts
exactly one new (k+1)-mer, A^(k+1), and preserves all existing
length-L read multiplicities. Every L-mer in S is distinct,
since all its k-prefixes are distinct; A^L was absent.
Thus D has the G old L-mers and one new L-mer, each exactly once.

Both circles are primitive, since their k-mer spectra contain
a count of one (in a nontrivial power all such counts are
divisible by the repetition factor). Both satisfy the exact
P2 clauses: S has no repeated k-mer, and D has only one
repeated k-mer at two adjacent starts; no long triple repeat
or two interleaved long repeat pairs are possible. All L-mers
of D are unique, so there are no longer repeats either.
Their lengths G,G+1 differ, so they are nonrotational.

The laws are uniform on G and G+1 distinct read types,
respectively, with the shorter support contained in the longer.
Therefore

    rho(p_S,p_D)=sqrt(G/(G+1)),
    1-rho=1-sqrt(G/(G+1)) <= 1/(2G) = 1/B.

The inequality follows by rationalizing the difference:
1-rho=1/[sqrt(G+1)*(sqrt(G+1)+sqrt(G))].
Together with the general lower bound 1/(64B), this
proves that the worst-case Hellinger gap is Theta(1/B),
even for each fixed alphabet q as read length L grows.
The best constant is still unknown.

Run scripts/verify_p2_debruijn_sharpness.py for independent
finite construction checks (q=2,3,4; several k values);
the general existence proof is the Eulerian argument above.

## Proof boundaries and reproduction

The old P2 multiplicity cap and population uniqueness are Lean-checked.
The new finite-ratio angular argument and the L>G case are fully proved
here and in the paper, but not yet a Lean declaration.

Run python3 scripts/verify_p2_linear_rate.py to independently enumerate
58,260 pairs of distinct normalized count profiles (counts in {0,1,2},
five word types), check the exact support/ratio dichotomy and numerically
validate the universal 1/(64B) bound. Finite enumeration is **not** a
replacement for the general proof and does not imply arbitrary profiles
spell circular genomes.

The theorem is for oriented exact iid read observations and primitive-P2
candidate genomes. It does not include unrestricted ML, strand-collapsed
observations or MB09's physical flow surrogate.
