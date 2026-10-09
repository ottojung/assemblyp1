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

**Epistemic status.**  Theorems 1–3 are **mathematical proofs**.  The
computational checks in §10 are **independent execution evidence** (bounded
enumeration), not proofs; their completeness is not claimed beyond the stated
ranges.  Nothing here is a source claim about Shomorony et al. or
Medvedev–Brudno; see §11 for the boundary to the published open problem.

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

* **One level** `B_k`: assemble the Laplacian `O(|E|)`; determinant of an
  `(n−1)×(n−1)` integer matrix by Bareiss `O(n³)` bit operations; factorials
  `O(|V| + |E|)`.  Here `n = |V|`, the number of support vertices.
* **Theorem 1 / 2 (exact `N(c)`):** `d(g)` levels, where `d(g)` is the number
  of divisors of `g`; total `O(d(g)·n³)` arithmetic operations (plus big-integer
  costs, since capacities and factorials grow).
* **Theorem 3 (singleton yes/no):** no divisor sum — one determinant `O(n³)`,
  a branching scan `O(|V|+|E|)`, and a gcd `O(|E|·log max)`.  Polynomial time.
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

## 11. Relationship to issues #92, #83, #217 and the open problem

* **GitHub #92 (closed).**  `docs/scalar-primitive-spellings-83.md` and
  `AssemblyP1/ScalarPrimitiveSpellings.lean` settle the **variable-length**
  primitive question: a primitive truth is identifiable among
  variable-length primitive candidates from its normalized complete spectrum
  iff its spectrum support is nonbranching (`identifiable_iff_nonbranching`).
  Theorem 3 here is the **same-length** yes/no analogue; the branching half
  of both rests on the same two-excursion/`A^m B^m` primitive-spelling
  construction.  The two results are complementary: #92 fixes the length
  spectrum modulo rotation across lengths, Theorem 3 fixes it at one length.
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
* **Antonina #217.**  The source-supported interpretation matrix there
  concerns the *finite-data* bridging⇒ML question (objective, candidate
  class, strand, ties).  The same-length complete-spectrum fibre here is the
  population-level identifiability core that several #217 rows condition on;
  the two should be reconciled at the interpretation level, not conflated.
  The referent, candidate-universe, and tie-semantics ambiguities documented
  in `docs/open-problem.md` remain open and are not settled by any counting
  theorem.
* **Boundary.**  Theorems 1–3 answer the same-length, oriented,
  complete-spectrum counting problem modulo rotation for arbitrary positive
  capacity gcd.  They do not by themselves settle which Medvedev–Brudno
  candidate universe Shomorony et al. intended, reverse-complement-collapsed
  read types, finite sampled-read likelihood, or the bridge from Shomorony's
  information-feasibility condition to a particular ML conclusion.  Those
  source/model questions remain explicit elsewhere in the repository.
