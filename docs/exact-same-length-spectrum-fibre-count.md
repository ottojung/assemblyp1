# Exact same-length complete-spectrum fibre count

> **Superseded in part by `docs/exact-fibre-count-theorem-219.md`.**  This
> front-94e7 note records the original derivation of the weighted BEST /
> divisor-Möbius fibre count.  The board-#219 note sharpens it: it pins the
> self-loop, root, and complexity conventions, adds the positive
> totient/Burnside form of the orbit count (its Theorem 2), and adds a
> Möbius-free singleton criterion (its Theorem 3).  The derivation below is
> unchanged and remains the proof of Theorem 1 of the #219 note.

## Scope and status

This note records a human-readable combinatorial theorem for the oriented complete-spectrum model used in the same-length part of issue #83. It is a **mathematical proof**, not a source claim and not yet a Lean theorem.

**ATTRIBUTION (board 94, front 94e7; see `docs/best-tw1-attribution-94.md`).**
The decomposition used here --- split on the width parameter `t_w`, identify
out-degree as the critical parameter, and attack the `t_w = 1` case by a
conditional BEST-theorem count --- is a **board construction**.  It is
**not** imported from Pevzner 1995 or from Bresler--Bresler--Tse.  A two-sided
retrieval on this board established that Pevzner 1995 (Algorithmica
13:77--105) has no counting statement of any kind and no `BEST` / `arboresc` /
`spanning` / `matrix-tree` / `determinant` / out-degree / `repeat` / `spectrum`
/ `K-mer` / `condens` vocabulary, and that BBT (BMC Bioinformatics
14(Suppl 5):S18, 2013) has no arborescence and no spanning-tree count.

**CORRECTION (board 94, doc front 94d1).**  The same text formerly cited BBT as
"Algorithmica 13:1--19, 2006", said BBT "has no proof of its own Theorem 3",
and concluded that "**the citation chain is broken**".  All three are struck.
BBT is Bresler, Bresler & Tse, *Optimal assembly for high throughput shotgun
sequencing*, BMC Bioinformatics **14**(Suppl 5):S18, 2013.  The 13-page
published rendering has no appendix, but says so itself ("All proofs can be
found in the appendix"), and the arXiv:1301.0068 v3 source carries one:
`appendix_short.tex:157-169` contains a **complete proof of Theorem 3**, and
that proof contains no count, no determinant and no spanning tree.  BBT cites
Pevzner 1995 correctly; the narrower real defect is that the single step it
imports, `Lemma [Pevzner \cite{Pev95}] l:Pev95`, is **stated but proved nowhere
in the chain**.  **Whether `l:Pev95` is true is NOT ESTABLISHED.**  This does not
weaken the point of this section, which is unaffected: the `t_w = 1` count used
below is still the board's own construction and is still not imported from
either paper.  The BEST theorem itself is cited in the next paragraph from its
own sources, which is where the count below comes from.

Let c : E → ℕ be a nonzero balanced edge-type capacity vector whose positive support is strongly connected. Edge types are directed edges; copies of the same edge type are indistinguishable. A spelling is a cyclic Eulerian edge-type word using type e exactly c(e) times, and spellings are identified by cyclic rotation.

Write

    g = gcd { c(e) : c(e) > 0 },    c = g c₀,

so c₀ is gcd-one. For h ≥ 1, put c_h = h c₀.

The result below gives the exact number of cyclic spelling orbits at c, including the periodic case g > 1. For a realizable complete L-mer spectrum, these are exactly the same-length circular genomes realizing that spectrum, modulo rotation.

## Weighted BEST quantity

**Sources for the theorem used here.**  The count of Eulerian orderings by
in-degree-multiplied-out-degree times a spanning-arborescence number is the
**BEST theorem**: van Aardenne-Ehrenfest and de Bruijn, *Indag. Math.* (1951)
for the in-degree-multiplied-out-degree form, or Tutte, *A spanning tree
expansion of the determinant*, LMS Lect. Notes **83** (1975), for the
matrix-tree form used below.  Neither Pevzner 1995 nor BBT states it, and
neither should be cited for it.

For a support vertex r, let

    d_u(h) = Σ_{e : u → *} c_h(e).

Let τ_r(c_h) be the directed weighted Matrix-Tree sum of in-arborescences rooted at r, with edge type e having weight c_h(e). Self-loops do not participate in an arborescence, although they do contribute to d_u(h) and to the factorial denominator below.

Define

    B_h = τ_r(c_h) · ∏_u (d_u(h) - 1)! / ∏_e c_h(e)!.

Although B_h need not be an integer, it is independent of the chosen support root r in the balanced strongly connected case.

### Why B_h is the stabilizer-weighted orbit count

Temporarily label every individual copy of every edge type. Let T_r be the labelled linear Euler tours whose initial boundary vertex is r, allowing an arbitrary first labelled outgoing edge there. Directed BEST gives

    |T_r| = d_r(h) · τ_r(c_h) · ∏_u (d_u(h) - 1)!.

Now forget the copy labels. For a cyclic edge-type spelling orbit W, let s(W) be its rotational stabilizer size, equivalently its repetition exponent. The orbit has d_r(h) / s(W) distinct linearizations whose initial boundary vertex is r. Each such type-linearization has

    F_h = ∏_e c_h(e)!

labellings of repeated edge-type occurrences. Therefore

    |T_r| = d_r(h) F_h · Σ_[W] 1 / s(W).

Cancelling d_r(h) and F_h yields

    B_h = Σ_[W] 1 / s(W),

where the sum ranges over spelling orbits at c_h. This is the convention-sensitive step: there is no additional factor of total length, root outdegree, or stabilizer.

## Removing rotational stabilizers

Let P_h be the number of **primitive** cyclic spelling orbits at capacity vector c_h. Every cyclic word has a unique primitive root. An orbit at level h whose primitive root is at level j, with j | h, is the (h/j)-fold repetition of that primitive orbit, so its stabilizer has size h/j. Hence

    B_h = (1/h) Σ_{j | h} j P_j.

Möbius inversion gives the exact primitive count

    P_h = (1/h) Σ_{j | h} μ(h/j) j B_j
        = Σ_{d | h} (μ(d)/d) B_{h/d}.

Finally, every orbit at level g has a unique primitive root at one divisor level, so the exact unweighted number of cyclic spelling orbits at the original capacity vector c = g c₀ is

    N(c) = Σ_{h | g} P_h.

Consequently the same-length complete-spectrum fibre is a singleton modulo rotation exactly when N(c) = 1.

When g = 1, every spelling is primitive and the formula collapses to

    N(c) = B₁ = τ_r(c) · ∏_u (d_u - 1)! / ∏_e c(e)!.

## Checks and evidence

The factor conventions have been checked against small examples that distinguish the possible normalizations.

* One vertex with two loop types of capacities (2,2): B = 3/2. Möbius inversion gives one primitive orbit at level 1 and one at level 2, hence two level-2 necklaces: the periodic ABAB orbit and the primitive AABB orbit.
* Two vertices with only AB = BA = 2: τ_A = 2, so B = 1/2, matching the unique orbit ABAB with stabilizer 2.
* With AA = BB = 1 and AB = BA = 2, gcd is one and the formula gives two cyclic spelling orbits.

As independent computational evidence, exact enumeration over every binary circular word of length 1 through 9, for complete spectra with L = 2 and L = 3, agreed with the formula for every capacity vector encountered. The evaluator used exact arithmetic and a directed Matrix-Tree determinant; self-loops were excluded from the arborescence Laplacian contribution.

The finite enumeration is evidence rather than proof. The proof is the BEST double-counting identity (van Aardenne-Ehrenfest--de Bruijn 1951, or Tutte 1975) plus unique primitive-root decomposition and ordinary divisor Möbius inversion above. The **reduction** from that identity to a fibre count is the board's own, per `docs/best-tw1-attribution-94.md`.

## Boundary of the result

This theorem answers the **same-length, oriented, complete-spectrum** counting problem modulo cyclic rotation. It does not by itself settle which Medvedev–Brudno candidate universe Shomorony et al. intended, reverse-complement-collapsed read types, finite sampled-read likelihood, or the bridge from Shomorony's information-feasibility condition to a particular maximum-likelihood conclusion. Those source/model questions remain explicit elsewhere in the repository.
