# Exact same-length complete-spectrum fibre count and singleton criterion

## Status and attribution

This note is the precise, self-contained theorem document for the
same-length part of GitHub issue #83 (Antonina board #219).  It consolidates
and sharpens the earlier note `docs/exact-same-length-spectrum-fibre-count.md`
(front 94e7), adds the two shortcuts derived on board #219, and pins the
conventions that note left implicit: self-loops, the gcd-`>1` stabilizer, the
root convention, and complexity.

**Attribution.**  The weighted Matrix-Tree/BEST quantity and the reduction to
a fibre count are the **board's own construction**, not imported from Pevzner
1995 or Bresler–Bresler–Tse; see `docs/best-tw1-attribution-94.md`.  The BEST
theorem itself is classical: van Aardenne-Ehrenfest & de Bruijn, *Indag. Math.*
(1951), or Tutte, *A spanning tree expansion of the determinant*, LMS Lect.
Notes **83** (1975).  The two shortcuts below (a Möbius-free singleton
criterion and a positive totient/Burnside form of the orbit count) are
**project-specific deductions** from the board's own results
(`docs/scalar-primitive-spellings-83.md` and the earlier note); they are not
claimed as cited theorems and no paper is cited as their source.  The
classical identity `Σ_{d|n} μ(d)/d = φ(n)/n` is standard number theory.

**Closest prior art.**  The `g = 1`, multiplicity-one-edge corner of Theorem 1
is Shomorony–Kamath–Xia–Courtade–Tse, ISIT 2016, Appendix C, Corollary 1; see
§11.  We do not claim that quotient, and we do not claim its singleton-edge
hypothesis is necessary.

**Epistemic status.**  Theorems 1–3 are **mathematical proofs**.  The
computational checks in §10 are **independent execution evidence** (bounded
enumeration), not proofs; their completeness is not claimed beyond the stated
ranges.  The divisor-sum core is additionally **kernel-checked** in
`AssemblyP1/FibreCountArithmetic.lean` (§10).  Nothing here is a source claim
about Shomorony et al. or Medvedev–Brudno; see §12 for the boundary to the
published open problem and §11 for the prior-art boundary.

---

## 1. Setup: edge-type capacities and cyclic spellings

Let `E` be a set of **edge types**, `V` a set of **vertices**, and
`tail head : E → V`.  A **capacity** is a map `c : E → ℕ`.  Its **support**
is `supp(c) = {e : 0 < c e}`.  The capacity is

* **balanced** if for every vertex `u`,
  `Σ_{e : head e = u} c e = Σ_{e : tail e = u} c e`;
* **strongly connected** if the digraph `(V, supp(c))` is strongly connected;
* **gcd-one** if `gcd{c e : 0 < c e} = 1`.

A **cyclic edge-type spelling** of `c` is a cyclic word over `E` using each
edge type `e` exactly `c e` times, such that consecutive types are
incidence-compatible (`head e_i = tail e_{i+1}`) cyclically.  Two spellings
are identified when they differ by a **cyclic rotation**; parallel copies of
the same edge type are indistinguishable (this is automatic, since the word
is over `E`).

> **Realization.**  For a circular word `S` of length `G` and read length
> `L`, the complete `L`-spectrum `specCount S` is a balanced capacity over the
> `L`-mer edge types (`tail e = e[:-1]`, `head e = e[1:]`), and its support is
> strongly connected whenever `G ≥ 1` (the window sequence is a closed trail
> using every support edge).  The same-length complete-spectrum fibre of `S`
> modulo rotation is exactly the set of cyclic edge-type spelling orbits of
> `specCount S`.

Throughout, fix a nonzero balanced `c` with strongly connected support, and
write

    g = gcd{c e : 0 < c e},        c = g · c₀      (c₀ gcd-one).

For `h ≥ 1` put `c_h = h · c₀`.

## 2. The weighted BEST quantity

For a vertex `r`, let `d_u = Σ_{e : tail e = u} c₀ e` be the **out-degree** at
`u` for the gcd-one vector `c₀` (self-loops included, since a self-loop has
`tail e = u`).  Let `τ_r` be the **weighted in-arborescence count**: the sum
over spanning in-arborescences `T` rooted at `r` (every `u ≠ r` has exactly
one outgoing edge in `T`, and following edges leads to `r`) of
`∏_{e ∈ T} c₀ e`.

> **Self-loop convention (precise).**  A self-loop never lies in an
> arborescence: for `u ≠ r` a self-loop does not advance toward `r`, and `r`
> itself has no outgoing arborescence edge.  Hence self-loops are **excluded**
> from `τ_r` (the Laplacian diagonal is out-degree *excluding* self-loops;
> see §7).  Self-loops **do** contribute to `d_u` and hence to
> `(d_u − 1)!`, and `c e!` in the denominator.  Getting this wrong changes
> the count; the audit in §10 pins it by the `AA = AB = BA = 1` test.

Define the **weighted BEST quantity** at level `h`:

    B_h = τ_r(c_h) · ∏_u (d_u(h) − 1)! / ∏_e c_h(e)!,

where `d_u(h) = h · d_u` is the out-degree at `c_h` and `τ_r(c_h)` is the
arborescence count with edge weights `c_h`.  Although `B_h` need not be an
integer, **it is independent of the chosen root `r`** (§7).

## 3. Theorem 1 — exact orbit count (divisor/Möbius)

> **Theorem 1.**  The number of cyclic edge-type spelling orbits of `c` is
>
>     N(c) = Σ_{h | g} P_h,
>     P_h  = Σ_{d | h} (μ(d)/d) · B_{h/d} = (1/h) Σ_{j | h} μ(h/j) · j · B_j,
>
> where `P_h` is the number of **primitive** (non-proper-power) orbits at
> level `h` and `μ` is the Möbius function.

The proof is the BEST double-counting identity of §6 plus unique
primitive-root decomposition and ordinary divisor Möbius inversion.  When
`g = 1` every spelling is primitive and the formula collapses to
`N(c) = B₁ = τ_r(c) · ∏_u (d_u − 1)! / ∏_e c e!`.

## 4. Theorem 2 — exact orbit count (Burnside/totient)

Rearranging the divisor sums of Theorem 1 gives a **positive** formula with no
Möbius inversion.

> **Theorem 2.**  The number of cyclic edge-type spelling orbits of `c` is
>
>     N(c) = Σ_{k | g} φ(g/k)/(g/k) · B_k = (1/g) Σ_{k | g} k · φ(g/k) · B_k,
>
> where `φ` is Euler's totient.

*Proof.*  Substituting `P_h = Σ_{d|h} (μ(d)/d) B_{h/d}` into
`N = Σ_{h|g} P_h` and reindexing with `k = h/d`, then `j = h/k`:

    N = Σ_{k | g} B_k · Σ_{j | (g/k)} μ(j)/j = Σ_{k | g} B_k · φ(g/k)/(g/k),

using `Σ_{j|n} μ(j)/j = φ(n)/n`.  □

This is a Burnside-style weighted necklace identity: the totient sum
replaces the primitive-count inversion.  It is a **derived identity** from
Theorem 1, not a separately cited theorem.

## 5. Theorem 3 — singleton criterion without Möbius

The yes/no question "is the same-length fibre a singleton modulo rotation?"
does not require the divisor/Möbius sums.  It is decided by a three-way
branch on the support.

> **Theorem 3 (singleton criterion).**  The same-length fibre of `c` is a
> singleton modulo rotation **iff** one of the following holds:
>
> 1. **Nonbranching** — no vertex has two distinct outgoing edge types.  Then
>    `N(c) = 1` for every `g`.
> 2. **Branching, `g = 1`, and `τ_r(c) · ∏_u (d_u − 1)! = ∏_e c e!`.**
>
> If the support branches and `g > 1`, then `N(c) ≥ 2` (never a singleton).

*Proof.*  
**(1)**  If no vertex has two distinct outgoing edge types, strong
connectivity forces the support to be a directed cycle (a single vertex with
a self-loop in the one-vertex case); balance forces all positive capacities
to be equal, so `c = g · 𝟙` where `𝟙` is the all-ones cycle.  Every cyclic
spelling follows the same cycle, so there is exactly one orbit: `N(c) = 1`.

**(Branching, `g > 1`)**  By the branching theorem of
`docs/scalar-primitive-spellings-83.md`, a branching balanced strongly
connected support admits a **primitive** cyclic spelling of `m·c₀` for every
`m ≥ 2`; taking `m = g` gives a primitive spelling `W_prim` of `c`.  Since
`c₀` is balanced and strongly connected, Veblen's theorem gives an Eulerian
circuit `W₀` of `c₀`; then `W₀^g` is a spelling of `g·c₀ = c` and is a
**proper `g`-th power** (as `g ≥ 2`).  A rotation of a proper power is a
proper power, and a rotation of a primitive word is primitive, so `W_prim`
and `W₀^g` lie in distinct orbits.  Hence `N(c) ≥ 2`.

**(Branching, `g = 1`)**  Here `N(c) = B₁ = τ_r(c) · ∏_u (d_u − 1)! / ∏_e c e!`
(Theorem 1), which equals `1` iff `τ_r(c) · ∏_u (d_u − 1)! = ∏_e c e!`.  □

> **Corollary (identifiability boundary, same-length).**  In the oriented
> complete-spectrum model, a circular word is uniquely determined up to
> rotation by its complete `L`-spectrum iff its spectrum capacity satisfies
> Theorem 3.  This is decidable in polynomial time (§9) and does **not**
> require the divisor/Möbius sums.

## 6. Proof of Theorem 1 (BEST double-counting and Möbius inversion)

**Step 1 — labelled tours.**  Temporarily label every individual copy of
every edge type.  Let `T_r` be the labelled linear Euler tours whose initial
boundary vertex is `r`, with an arbitrary first labelled outgoing edge there.
The directed BEST theorem (van Aardenne-Ehrenfest–de Bruijn 1951; Tutte 1975)
gives

    |T_r| = d_r · τ_r(c_h) · ∏_u (d_u(h) − 1)!,

where `d_r = d_r(h)` is the out-degree at `r` for `c_h`.  (Each of the `d_r`
choices of first edge contributes equally; the arborescence and factorial
factors order the remaining choices.)

**Step 2 — forget labels.**  For a cyclic spelling orbit `W` at `c_h`, let
`s(W)` be its rotational stabilizer size (equivalently its repetition
exponent).  The orbit has `d_r / s(W)` distinct linearizations whose initial
boundary vertex is `r` (the `d_r` edge-positions leaving `r`, modulo the
`s(W)` rotations fixing the word).  Each such type-linearization has
`F_h = ∏_e c_h(e)!` labellings of repeated edge-type occurrences.  Hence

    |T_r| = d_r · F_h · Σ_{[W]} 1/s(W),

and cancelling `d_r` and `F_h`:

    B_h = τ_r(c_h) · ∏_u (d_u(h) − 1)! / ∏_e c_h(e)! = Σ_{[W]} 1/s(W).

This is the convention-sensitive step: there is no extra factor of total
length, root outdegree, or stabilizer.

**Step 3 — Möbius inversion.**  Every cyclic word has a unique primitive
root.  An orbit at level `h` whose primitive root is at level `j | h` is the
`(h/j)`-fold repetition of that primitive orbit, so `s(W) = h/j`.  With `P_h`
the number of primitive orbits at level `h`,

    B_h = Σ_{j | h} P_j · (j/h) = (1/h) Σ_{j | h} j · P_j.

Writing `Q_j = j · P_j`, this is `h · B_h = Σ_{j | h} Q_j`; Möbius
inversion gives `Q_h = Σ_{j | h} μ(h/j) · j · B_j`, i.e.

    P_h = (1/h) Σ_{j | h} μ(h/j) · j · B_j = Σ_{d | h} (μ(d)/d) · B_{h/d}.

**Step 4 — total.**  Every orbit at level `g` has a unique primitive root at
one divisor level, so

    N(c) = Σ_{h | g} P_h.

□

## 7. Root independence and the Laplacian

> **Proposition (root independence).**  For a balanced strongly connected
> capacity, `τ_r` is independent of the root `r`.

*Proof.*  Build the Laplacian `L` with `L[u][v] = −c(edges u→v)` for
`u ≠ v` and `L[u][u] =` out-degree **excluding** self-loops.  Balance makes
every row sum zero; balance also makes every column sum zero (in-degree =
out-degree, and self-loops contribute equally to both).  A square matrix with
zero row and column sums has all cofactors equal, and the directed
Matrix-Tree theorem identifies `τ_r` with the `r`-th cofactor.  □

Consequently `B_h`, `P_h`, and `N(c)` are all root-independent.  The audit
(§10) verifies root independence on every spectrum enumerated.

## 8. Self-loop conventions (summary)

| Quantity | Self-loops counted? | Where |
| --- | --- | --- |
| out-degree `d_u` (factorial `(d_u−1)!`) | **yes** | numerator |
| denominator `∏ c e!` | **yes** | denominator |
| arborescence `τ_r` (Laplacian) | **no** | excluded from tree and Laplacian diagonal |

A self-loop contributes to `d_u` and `c e!` but never to `τ_r`.  The `AA = AB
= BA = 1` test in §10 distinguishes this from the incorrect convention
(including self-loops in the Laplacian diagonal), which gives `τ_B = 2`
instead of `1` and the wrong fibre count.

## 9. Complexity

Let `G` be the length of the genome whose complete `L`-spectrum is `c`; then
`Σ_e c e = G`, so `|E| ≤ G` and the capacity vector is an object of size
`Θ(G)`.  Let `n = |V|` be the number of support vertices and `v = n`.

* **One determinant suffices for all levels.**  Every directed in-arborescence
  on the `v` support vertices has exactly `v − 1` non-loop arcs, so uniformly
  scaling every weight by `h` multiplies each tree weight by `h^{v−1}`:
  `τ_r(h·c₀) = h^{v−1} · τ_r(c₀)`.  Hence one weighted Matrix-Tree cofactor on
  `c₀` gives every `B_h` via
  `B_h = h^{v−1} τ_r(c₀) · ∏_u (h·d_u − 1)! / ∏_e (h·c₀ e)!`,
  with the one-vertex loop-only case (`v − 1 = 0`, `τ = 1`) included.
* **Assemble and invert once:** Laplacian `O(|E|)`; determinant of a
  `(v−1)×(v−1)` integer matrix by Bareiss, `O(v³)` arithmetic operations;
  factorials `O(|V| + |E|)`.
* **Theorem 1 / 2 (exact `N(c)`):** `d(g)` divisor levels, where `d(g)` is the
  number of divisors of `g`; `O(d(g)·(v³ + |V| + |E|))` arithmetic operations.
* **Theorem 3 (singleton yes/no):** no divisor sum — one determinant `O(v³)`,
  a branching scan `O(|V|+|E|)`, and a gcd `O(|E|·log max c e)`.  Polynomial
  time in `G`.
* **Bit-complexity caveat.**  The arithmetic is on big integers: the capacities
  and the factorial/numerator products have `Θ(G log G)` bits (the count `N(c)`
  can itself be exponentially large, so the output has `Ω(G log G)` bits).  The
  bounds above count arithmetic operations and are polynomial in the
  **explicitly given** genome length `G`.  They do **not** assert polynomial
  time in a succinct binary encoding of the multiplicities alone: if the input
  is only a binary encoding of the capacity vector, `G = Σ_e c e` is exponential
  in the input length, and the factorials already force super-polynomial work.
* **Brute-force audit (§10):** `O(2^G · G · L)` per read length `L`; bounded
  evidence only.

## 10. Computational evidence (independent audit)

`scripts/audit_fibre_count_219.py` re-derives every claim from scratch and
checks them against brute-force enumeration:

* **Enumeration.**  Every binary circular word of length `1..9`, for `L = 2`
  and `L = 3`.  The fibre size per spectrum = number of distinct rotation
  classes.  88 spectra at `L = 2`, 119 at `L = 3`.
* **Theorem 1 (Möbius).**  `N(c)` matches brute force on **all** spectra
  (0 mismatches).
* **Theorem 2 (totient).**  `N(c)` matches brute force on **all** spectra
  (0 mismatches).
* **Theorem 3 (singleton criterion).**  The three-way branch agrees with the
  brute-force fibre size on **all** spectra (0 mismatches).
* **Primitive counts `P_h`.**  Match brute-force primitive necklaces at every
  level `h | g` (0 mismatches).
* **Root independence.**  `τ_r` equal across all roots on every spectrum
  (0 mismatches).
* **Hand-computed convention tests** (the earlier note's checks plus the
  shortcuts' edge cases): one-vertex loops `(2,2)` → `B = 3/2`, `N = 2`;
  `AB = BA = 2` → `B = 1/2`, `N = 1`; `AA = BB = 1, AB = BA = 2` → `N = 2`;
  `AA = AB = BA = 1` → `τ_A = τ_B = 1`, `N = 1`; nonbranching single loop
  and directed `3`-cycle → `N = 1`; branching `+ gcd = 2` → `N ≥ 2`;
  branching `+ gcd = 1` `AABB` → `N = 1`.

Specific words: `AABB` (gcd-1 branching) → `N = 1`; `AAAB` (the P2-converse
witness) → `N = 1`; `AAABAB` (the variable-length competitor, gcd-2
branching) → `N = 2`; `ABABABAB` (periodic, nonbranching) → `N = 1`.

The finite enumeration is **evidence, not proof**; its completeness is not
claimed beyond length `9`.  The proofs are §6 (Theorem 1), §4 (Theorem 2),
and §5 (Theorem 3).

**Reproduction note.**  The script was re-run directly as
`python3 scripts/audit_fibre_count_219.py` (not through `/bin/sh`, whose
`PIPESTATUS` is a bash-only construct), yielding true exit code `0` and the
`AUDIT PASSED` banner: all 9 hand-computed convention tests, and 88 (`L=2`) +
119 (`L=3`) spectra, with zero mismatches on `N` (Möbius and totient), primitive
counts, root independence, and the singleton criterion.  This matches the
independent repro recorded on board #219.

**Lean kernel check.**  The number-theoretic core is formalized in
`AssemblyP1/FibreCountArithmetic.lean` (Theorems `sum_divisors_divisors`,
`sum_moebius_div_eq_totient`, `fibre_mobius_inversion`, `fibre_totient`).
`lake build --wfail AssemblyP1.FibreCountArithmetic` succeeds, and
`#print axioms` reports each theorem depends only on
`propext, Classical.choice, Quot.sound` (no `sorryAx`, no new axioms).  The
BEST/graph content is external (classical BEST plus the kernel-checked
branching construction in `AssemblyP1/ScalarPrimitiveSpellings.lean`).

## 11. Primary prior art: Shomorony et al. (ISIT 2016), Appendix C, Corollary 1

The closest published result is a special case of the `g = 1` part of
Theorem 1, and must be cited as such.

> **Shomorony, Kamath, Xia, Courtade & Tse, *Partial DNA Assembly: A
> Rate-Distortion Perspective*, ISIT 2016 (arXiv:1605.01941), Appendix C,
> Corollary 1.**  If an Eulerian directed multigraph `G = (V, E)` contains an
> edge of multiplicity `1`, then the number `ec(G)` of Eulerian cycles distinct
> up to edge multiplicity is
>
>     ec(G) = T_G · ∏_v (d_out(v) − 1)! / ∏_{(u,v)} m(u,v)!,
>
> where `T_G` is the number of arborescences and `m(u,v)` the multiplicity of
> the edge `(u,v)` (each parallel copy counted separately in `T_G`).  Their
> proof roots the tour at the multiplicity-one edge, which kills the rotational
> stabilizer and makes the `∏ m(u,v)!` quotient exact.

**This is exactly our `g = 1`, singleton-edge case.**  In the de Bruijn /
`k`-mer multigraph an `L`-mer edge type `e` determines its vertex pair
`(tail e, head e)`, so `m(u,v) = c e`; a labelled arborescence choosing one of
the `c e` copies is the weighted count `τ_r(c) = T_G`; and
`∏_e c e! = ∏_{(u,v)} m(u,v)!`.  With `g = 1` every spelling is primitive
(`s(W) = 1`), so `B₁ = τ_r(c)∏_u(d_u−1)!/∏_e c e!` coincides with Corollary 1.
The two notions of equivalence also coincide: "Eulerian cycles distinct up to
edge multiplicity" is the same as our cyclic edge-type spelling orbits.

**Where the board's result strictly extends it.**  We do **not** claim
Corollary 1, and we do not claim its hypothesis is necessary.

1. **The singleton-edge hypothesis is dropped at `g = 1`.**  A multiplicity-one
   edge guarantees `gcd = 1`, but the converse fails, and Theorem 1 at `g = 1`
   needs no singleton.  For example, one vertex with two loop types of
   capacities `(2, 3)` has `gcd = 1` and no multiplicity-one edge; it is
   branching, and `N = B₁ = 4!/(2!·3!) = 2` (the two binary necklaces `AABBB`
   and `ABABB`).  Corollary 1 does not apply to it.
2. **Arbitrary gcd `> 1`.**  Corollary 1 is silent when some multiplicity
   exceeds one and the counts share a common factor: it counts `g = 1`
   Eulerian cycles and does not model the nonprimitive/periodic spellings that
   appear at level `g`.  Theorems 1–2 add the primitive-root decomposition and
   its divisor-Möbius (equivalently positive totient) stabilizer sum.
3. **Different mechanism for removing stabilizers.**  Corollary 1 uses a
   singleton edge as a distinguished root.  Our `B_h` is instead the
   stabilizer-weighted count `Σ_{[W]} 1/s(W)`, and the Möbius/totient step
   removes the stabilizers arithmetically.  That is precisely what lets the
   singleton hypothesis be dropped and the `g > 1` case be covered.

The board's construction was derived independently (see the attribution note
in the "Status and attribution" section above); the overlap with the
literature is the `g = 1`, singleton-edge corner, which is Corollary 1's.  No
priority over Corollary 1 is claimed.

## 12. Relationship to issues #92, #83, #217 and the open problem

**Source facts vs project-level strengthenings.**  The model of §1 (oriented
circular genome, complete `L`-spectrum as a balanced capacity, same-length
fibre modulo rotation) is a faithful reading of the *oriented* branch of the
2016 sources, and the Shomorony et al. multigraph together with its `ec`
equivalence is a source fact (§11).  Everything stated here *about that
model* — Theorems 1–3, the nonbranching/branching split, and the exact count —
is a **project-level mathematical theorem** for a stipulated model, not a claim
extracted from any paper.  Agreement among project notes or agents does not
promote any of it to a source claim.

* **GitHub #92 (closed).**  `docs/scalar-primitive-spellings-83.md` and
  `AssemblyP1/ScalarPrimitiveSpellings.lean` prove the **variable-length**
  primitive classification for the same oriented primitive complete-spectrum
  model: *in that model* a primitive truth is identifiable among
  variable-length primitive candidates from its normalized complete spectrum
  iff its spectrum support is nonbranching (`identifiable_iff_nonbranching`).
  This is a **project-level theorem about a stipulated model**, conditional on
  the oriented/primitive/normalized-spectrum reading; it is not a statement
  about which Medvedev–Brudno or Shomorony candidate universe was intended.
  Theorem 3 here is the **same-length** yes/no analogue; the branching half of
  both rests on the same two-excursion/`A^m B^m` primitive-spelling
  construction (kernel-checked in `AssemblyP1/ScalarPrimitiveSpellings.lean`).
  The two are complementary: #92 fixes the fibre across lengths, Theorem 3
  fixes it at one length.
* **GitHub #83 (closed as "not planned"; migrated to Antonina #219).**  The
  close is **migration, not mathematical completion**.  The four packets of
  #83 are: (1) same-length exact criterion — Theorems 1–3; (2) graph
  theoretic simplification — the nonbranching/branching split of Theorem 3;
  (3) variable-length normalized-spectrum fibres — #92; (4) uniform finite-data
  recovery — **still open**, see below.
* **Packet 4 (uniform finite-data recovery).**  This note does **not** settle
  what structural property, if any, is necessary for unique ML recovery over
  *every* admissible sufficiently informative realization.  The exact fibre
  count is a population/complete-spectrum statement; it does not address
  finite-sample ML uniqueness uniformly over realizations.  Preserved as
  open.
* **Antonina #217.**  That board is a *source-interpretation* matrix for the
  **finite-data** bridging⇒ML question: its rows are source facts and
  interpretation choices (objective, candidate class, strand, bridging, flow,
  maximizer/ties).  The same-length complete-spectrum fibre here is a
  **population-level, complete-spectrum** identifiability statement; it is the
  core that several #217 rows *condition on*, not a row of that matrix.  The
  correct reconciliation is at the interpretation level: our Theorems 1–3 fix
  the fibre of a stipulated oriented complete-spectrum model, while #217 fixes
  which model(s) the 2016 sources support.  They must not be conflated, and
  neither implies the other.  The referent, candidate-universe, and
  tie-semantics ambiguities documented in `docs/open-problem.md` remain open
  and are not settled by any counting theorem here.
* **Boundary.**  Theorems 1–3 answer the same-length, oriented,
  complete-spectrum counting problem modulo rotation for arbitrary positive
  capacity gcd.  They do not by themselves settle which Medvedev–Brudno
  candidate universe Shomorony et al. intended, reverse-complement-collapsed
  read types, finite sampled-read likelihood, or the bridge from Shomorony's
  information-feasibility condition to a particular ML conclusion.  Those
  source/model questions remain explicit elsewhere in the repository.
