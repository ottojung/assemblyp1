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

This **proves the order-1/B lower bound conjectured** in the existing
paper's sharpness discussion. The precise best constant remains open;
the previous 1/(8B^4) bound was kernel-checked, while this new estimate
is currently paper-proved.

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
