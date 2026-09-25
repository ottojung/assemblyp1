# Exact same-length complete-spectrum fibre count

## Scope and status

This note records a human-readable combinatorial theorem for the oriented complete-spectrum model used in the same-length part of issue #83. It is a **mathematical proof**, not a source claim and not yet a Lean theorem.

Let (c:E	omathbb N) be a nonzero balanced edge-type capacity vector whose positive support is strongly connected. Edge types are directed edges; copies of the same edge type are indistinguishable. A spelling is a cyclic Eulerian edge-type word using type (e) exactly (c(e)) times, and spellings are identified by cyclic rotation.

Write
[
  g=gcd_{e:c(e)>0}c(e),qquad c=g c_0,
]
so (c_0) is gcd-one. For (hge1), put (c_h=h c_0).

The result below gives the exact number of cyclic spelling orbits at (c), including the periodic case (g>1). For a realizable complete (L)-mer spectrum, these are exactly the same-length circular genomes realizing that spectrum, modulo rotation.

## Weighted BEST quantity

For a support vertex (r), let
[
  d_u(h)=sum_{e:u	o *}c_h(e).
]
Let (	au_r(c_h)) be the directed weighted Matrix-Tree sum of in-arborescences rooted at (r), with edge type (e) having weight (c_h(e)). Self-loops do not participate in an arborescence (although they do contribute to (d_u(h)) and to the factorial denominator below).

Define
[
  B_h=
  	au_r(c_h)
  rac{prod_u(d_u(h)-1)!}
       {prod_e c_h(e)!}.
]

Although (B_h) need not be an integer, it is independent of the chosen support root (r) in the balanced strongly connected case.

### Why (B_h) is the stabilizer-weighted orbit count

Temporarily label every individual copy of every edge type. Let (T_r) be the labelled linear Euler tours whose initial boundary vertex is (r), allowing an arbitrary first labelled outgoing edge there. Directed BEST gives
[
 |T_r|=d_r(h),	au_r(c_h)prod_u(d_u(h)-1)!.
]

Now forget the copy labels. For a cyclic edge-type spelling orbit (W), let (s(W)) be its rotational stabilizer size, equivalently its repetition exponent. The orbit has (d_r(h)/s(W)) distinct linearizations whose initial boundary vertex is (r). Each such type-linearization has
[
 F_h=prod_e c_h(e)!
]
labellings of repeated edge-type occurrences. Therefore
[
 |T_r|
 =d_r(h)F_hsum_{[W]}rac1{s(W)}.
]
Cancelling (d_r(h)) and (F_h) yields
[
 B_h=sum_{[W]	ext{ at }c_h}rac1{s(W)}.
]
This is the convention-sensitive step: there is no additional factor of total length, root outdegree, or stabilizer.

## Removing rotational stabilizers

Let (P_h) be the number of **primitive** cyclic spelling orbits at capacity vector (c_h). Every cyclic word has a unique primitive root. An orbit at level (h) whose primitive root is at level (jmid h) is the (h/j)-fold repetition of that primitive orbit, so its stabilizer has size (h/j). Hence
[
 B_h=rac1hsum_{jmid h}jP_j.
]

Möbius inversion gives the exact primitive count
[
 P_h
 =rac1hsum_{jmid h}mu(h/j),jB_j
 =sum_{dmid h}rac{mu(d)}d B_{h/d}.
]

Finally, every orbit at level (g) has a unique primitive root at one divisor level, so the exact unweighted number of cyclic spelling orbits at the original capacity vector (c=g c_0) is
[
 oxed{N(c)=sum_{hmid g}P_h}.
]

Consequently the same-length complete-spectrum fibre is a singleton modulo rotation exactly when (N(c)=1).

When (g=1), every spelling is primitive and the formula collapses to
[
 N(c)=B_1=
 	au_r(c)rac{prod_u(d_u-1)!}{prod_e c(e)!}.
]

## Checks and evidence

The factor conventions have been checked against small examples that distinguish the possible normalizations.

* One vertex with two loop types of capacities ((2,2)): (B=3/2). Möbius inversion gives one primitive orbit at level 1 and one at level 2, hence two level-2 necklaces: the periodic (ABAB) orbit and the primitive (AABB) orbit.
* Two vertices with only (AB=BA=2): (	au_A=2), so (B=1/2), matching the unique orbit (ABAB) with stabilizer 2.
* With (AA=BB=1) and (AB=BA=2), gcd is one and the formula gives two cyclic spelling orbits.

As independent computational evidence, exact enumeration over every binary circular word of length (1) through (9), for complete spectra with (L=2) and (L=3), agreed with the formula for every capacity vector encountered. The evaluator used exact arithmetic and a directed Matrix-Tree determinant; self-loops were excluded from the arborescence Laplacian contribution.

The finite enumeration is evidence rather than proof. The proof is the BEST double-counting identity plus unique primitive-root decomposition and ordinary divisor Möbius inversion above.

## Boundary of the result

This theorem answers the **same-length, oriented, complete-spectrum** counting problem modulo cyclic rotation. It does not by itself settle which Medvedev–Brudno candidate universe Shomorony et al. intended, reverse-complement-collapsed read types, finite sampled-read likelihood, or the bridge from Shomorony's information-feasibility condition to a particular maximum-likelihood conclusion. Those source/model questions remain explicit elsewhere in the repository.
