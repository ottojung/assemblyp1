# P2 population identifiability: no proportional spectra for distinct primitive P2 genomes

_Status: independent mathematical note with an exact-arithmetic verifier
(`scripts/p2_population_proportional_attack.py`). It answers the issue-#48 /
issue-#45 population question for the oriented (single-strand) panel:

> Can two distinct, primitive, `P2`-admissible circular genomes have
> **proportional** `L`-mer spectra?

The answer is **no**. Two independent ingredients establish it:

1. **Cross-length exclusion** (`c = 1`): proved here (Lemma L\*, Theorem P),
   unconditional, using primitivity and the triple-repeat half of `P2`.
2. **Equal-length uniqueness**: the classical circular `q`-gram
   characterization (Ukkonen 1992; Pevzner 1995; Bresler–Bresler–Tse 2013,
   Theorem 3 at `K = L−1`), which is the definitional match of `P2` to
   Ukkonen's condition. This is a **source theorem** under the circular
   Eulerian-cycle reading, not an independent proof here.

The script's exhaustive searches are *bounded finite evidence* corroborating
both; they are not the proof. This note does **not** claim to settle the 2016
finite-sample open problem of `docs/open-problem.md`; it characterizes the
population/infinite-read fibre only, and does not assert that the population
regime is the primary repair of issue #48.

_This note is independent of the concurrent branch artifacts
`docs/population-identifiability-intrinsic-genomes.md`,
`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`,
and `docs/issue48-population-independent-verification-2026-09-21.md` (named,
not linked, because they are not on `main`). It re-derives the cross-length
argument and independently re-checks the finite ranges with different code,
including a BEST-theorem route and the parallel-edge subtlety recorded in §5.3._

---

## 0. Direct answer

Fix a read length `L ≥ 2`. For a circular genome `D` of length `n`, its
length-`L` spectrum is

```text
d_D(w) = #{ cyclic starts t : D[t..t+L) = w },
```

and its population read law is `p_D(w) = d_D(w)/n`. Two genomes have the same
population law iff their spectra are **proportional**, `d_T = c · d_S` with
`c > 0` rational (then `|T| = c |S|`).

**Theorem (P2 population identifiability, oriented panel).** Let `S, T` be
primitive `P2`-admissible circular genomes at read length `L`, and suppose
`d_T = c · d_S` for some rational `c > 0`. Then `c = 1` and `T` is a cyclic
shift of `S`.

Consequently **distinct** (non-rotational) primitive `P2` genomes never have
proportional `L`-mer spectra. The two halves have different hypothesis
strengths:

* the cross-length half needs **both** sides `TRF` (equivalently `c > 1` fails
  as soon as both are primitive `TRF`);
* the equal-length half needs `P2` on **one** side only: `P2(S)` alone forces
  every same-spectrum word to be a rotation of `S` (primitivity is not needed
  for this half). Hence, once `c = 1`, `T` is a rotation and automatically
  primitive `P2`.

---

## 1. Definitions and conventions

**Circular words.** `D = D[0..n)` with all indices cyclic; `rot(D,i)` is the
cyclic shift; `D ~ D'` means equal up to rotation. `D` is **primitive** if it
is not a nontrivial power `C^k`, `k ≥ 2`, of a shorter circular word.

**Bresler repeat vocabulary** (Bresler–Bresler–Tse 2013; the vocabulary
Shomorony et al. 2016 Eq. (1) inherits, see
[`docs/bridging-source-semantics.md`](bridging-source-semantics.md)).

* A **maximal repeat pair** of length `ℓ` is a pair of positions `t₁ ≠ t₂`
  with `D[t₁..t₁+ℓ) = D[t₂..t₂+ℓ)`, `D[t₁−1] ≠ D[t₂−1]`, and
  `D[t₁+ℓ] ≠ D[t₂+ℓ]`.
* A **triple repeat** of length `ℓ` is three positions whose length-`ℓ`
  windows are equal and for which not all three preceding symbols agree and
  not all three following symbols agree.
* A pair of maximal repeats `(t₁,t₃)`, `(t₂,t₄)` is **interleaved** if
  `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃`; its **length** is the length of
  the shorter constituent.

**Candidate-intrinsic predicates at read length `L`.**

* `TRF(D,L)`: no triple repeat of length `≥ L−1`.
* `ILF(D,L)`: no interleaved pair of maximal repeats whose shorter
  constituent has length `≥ L−1`.
* `P2(D,L) = WEAK(D,L) := TRF(D,L) ∧ ILF(D,L)`.
* `STRONG(D,L) :=` no `(L−1)`-mer of `D` occurs twice; `STRONG ⇒ P2`.

`P2` is the candidate-intrinsic shadow of the source read-feasibility condition
`I_s` at the full read set (the "full-read reduction", derived on the concurrent
branch artifacts named above): a length-`ℓ` copy is bridgeable strictly on both
sides by a length-`L` read iff `ℓ ≤ L−2`, so the full read set satisfies `I_s`
iff no triple/interleaved obstruction of length `≥ L−1` exists, i.e. iff `P2`.
The present note studies the spectrum fibre `D ↦ d_D`, which is prior to any
likelihood, tie, or read-sampling rule, so no `I_s` realization is needed.

**Proportionality.** `d_T = c·d_S` with `c ∈ ℚ_{>0}`; this forces equal support
and `|T| = c|S|`. The case `|T| = |S|` is `c = 1`, i.e. equal `L`-mer
multisets.

**Panel.** Oriented single-strand reads; genome equivalence is cyclic shift.
The reverse-complement/molecule panel is a genuine boundary (§4.4).

---

## 2. Cross-length exclusion (`c = 1`)

### Lemma L\* (multiplicity cap)

**Lemma L\*.** If `D` is primitive and `TRF(D,L)`, then every `(L−1)`-mer of
`D` occurs at most twice.

**Proof.** Suppose an `(L−1)`-mer `v` occurs at three distinct starts
`t₁,t₂,t₃`. Let `ℓ ≥ L−1` be the length of the maximal common right extension
of the three copies (extend right while the three next symbols agree); then the
three length-`ℓ` windows are equal and their symbols at `tᵢ+ℓ` are not all
equal.

Now extend left: let `j*` be the largest `j ≥ 0` such that the three windows
`D[tᵢ−j, tᵢ+ℓ)` of length `ℓ+j` are all equal. Such a `j*` exists. If the
common extension wrapped all the way around (`ℓ+j* = n`), then the three equal
length-`n` windows at the distinct starts `t₁,t₂,t₃` would exhibit a common
rotational symmetry, i.e. `D` would be invariant under rotation by `δ = t₂−t₁
(mod n)` with `0 < δ < n`; then the primitive period `g = gcd(δ,n)` divides `n`
and is `< n`, so `D` would be a nontrivial power — contradicting primitivity.
Hence `ℓ+j* < n`.

At `j*` the three equal windows have length `ℓ+j* ≥ ℓ ≥ L−1`; their following
symbols are not all equal by maximality of `ℓ`, and their preceding symbols are
not all equal by maximality of `j*`. That is a Bresler triple repeat of length
`≥ L−1`, contradicting `TRF(D,L)`. ∎

_Epistemic class: mathematical proof._

### Theorem P (cross-length exclusion)

**Theorem P.** Let `S, T` be primitive circular words with `TRF(S,L)` and
`TRF(T,L)`. If `d_T = c·d_S` for a rational `c > 0`, then `c = 1` and
`|T| = |S|`. (A fortiori with `P2` in place of `TRF`.)

**Proof.** `d_T = c·d_S` on `L`-mers forces equal `L`-mer support, and hence
equal `(L−1)`-mer support, because an `(L−1)`-mer occurs in `D` iff some `L`-mer
with that prefix (equivalently, suffix) occurs in `D`. For an `(L−1)`-mer `v`
let `a_v, b_v` be its multiplicities in `S, T`. Summing `d_T = c·d_S` over the
`L`-mers with prefix `v` (each occurrence of `v` is the prefix of exactly one
`L`-mer) gives `b_v = c·a_v`.

Assume `c > 1`. By Lemma L\*, `a_v ≤ 2` and `b_v ≤ 2` for every `v`. For every
`v` in the common support, `a_v ≥ 1`, so `b_v = c·a_v ≥ c > 1`, hence
`b_v = 2` and `c·a_v = 2`, i.e. `c = 2/a_v`. As `c` is independent of `v` and
`a_v ∈ {1,2}`, all `a_v` are equal; if `a_v = 2` then `c = 1`, contradicting
`c > 1`. So `a_v = 1` and `b_v = 2 = c` for every `v`.

Thus every `(L−1)`-mer of `S` occurs exactly once; then every `L`-mer of `S`
occurs exactly once too (a repeated `L`-mer would repeat its `(L−1)`-prefix).
The de Bruijn support of `S` therefore has exactly one distinct incoming and one
distinct outgoing edge at every vertex. Since `S` is one closed walk, that
support is a single directed cycle, and `S` is that cycle word (up to rotation).
`T` has the same edge multiset with each edge doubled; in its de Bruijn graph
every vertex again has a unique distinct outgoing edge, so every Eulerian
circuit follows the cycle in its cyclic order and returns to the start after one
lap. Hence `T` is the cycle word traversed twice, i.e. a nontrivial power of `S`
up to rotation — contradicting primitivity of `T`. Therefore `c = 1`. ∎

_Epistemic class: mathematical proof. Corroborated (not needed) by the finite
scans of §5._

**Corollary P.** For primitive `TRF`-admissible `S`, any primitive
`TRF`-admissible `T` with the same population law has `|T| = |S|` and
`d_T = d_S`.

**Remark (one-sidedness).** Theorem P genuinely needs `TRF` on **both** sides:
with `S = AAAB`, `T = AAAABAAB` (`L = 3`), `S` is primitive `P2`, `T` is
primitive but not `TRF`, and `d_T = 2·d_S`. So the cross-length half is not
one-sided. The equal-length half below is.

---

## 3. Equal-length uniqueness (the classical `q`-gram characterization)

It remains to treat `|T| = |S|` and `d_T = d_S`. There, `S` and `T` are two
Eulerian circuits of the same de Bruijn multigraph: vertices `(L−1)`-mers,
edges `L`-mers with multiplicity `d_S`. The needed statement is:

> If `P2(S,L)` holds, then the `L`-mer spectrum of `S` determines `S` up to
> cyclic shift.

This is the `K = L−1` instance of the **circular `q`-gram characterization**.
Under the same maximal-repeat definitions, `P2` is *definitionally* Ukkonen's
condition at `K = L−1`: `TRF` negates "triple repeat of length `≥ K`" and `ILF`
negates "interleaved repeats of length `≥ K`" (BBT define the pair length as the
shorter constituent). Bresler–Bresler–Tse 2013, Theorem 3 — "if there are no
triple or interleaved repeats of length at least `K`, then there is a unique
Eulerian cycle `C` in the `K`-mer graph `G` (built from the `(K+1)`-spectrum)
and `C` corresponds to `s`" — with `K = L−1` gives:

**Theorem Q (source theorem; Ukkonen 1992 / Pevzner 1995 / BBT 2013 Thm 3 at
`K = L−1`).** If `S` is `P2`-admissible at `L`, then any circular word `T` with
the same length and the same `L`-mer spectrum is a cyclic shift of `S`.
Primitivity is not needed for this step.

The residual qualifications are those already recorded on the concurrent
source-fidelity branch artifact: (i) a **circular reading** is required — BBT
state a unique Eulerian *cycle*, and the repository's model is circular with
cyclic-shift equivalence; read linearly it would be the boundary-fixed version,
whose rotation-quotient is the circular statement; (ii) BBT conclude uniqueness
in the *condensed* sequence graph, whereas the raw `K`-mer graph statement gives
the same sequence-level uniqueness because condensed non-branching paths are
traversed by force.

**Combining Theorem P and Theorem Q.** Under the hypotheses of the main
theorem, `c = 1` (Theorem P), so `|T| = |S|` and `d_T = d_S`, and `P2(S)` gives
`T ~ S` (Theorem Q). This proves the main theorem. Note that `P2` on the `T`
side is then automatic.

---

## 4. Sharpness of the hypotheses

### 4.1 Primitivity cannot be dropped (cross length)
`S = AAB` (`L = 3`) is primitive `P2`; `T = AABAAB = S²` is `P2` but not
primitive, has `d_T = 2·d_S`, and is not a rotation of `S`. (`AB` / `ABAB` at
`L = 2` is the shorter instance.)

### 4.2 Candidate-side admissibility cannot be dropped (cross length)
`S = AAAB` (`L = 3`) is primitive `P2`; `T = AAAABAAB` is primitive but not
`TRF` (hence not `P2`), has `d_T = 2·d_S`, and is not a rotation of `S`. This is
also the witness that cross-length `TRF` is not one-sided.

### 4.3 `TRF` alone is not enough at equal length
`S = AABABB`, `T = AABBAB` (`L = 3`) are primitive, `TRF`, have equal
same-length spectra, and are not rotations, but both fail `ILF`. So the
interleaved clause is genuinely used in Theorem Q.

### 4.4 Panel boundary: molecule / reverse-complement
On the double-strand (`k`-molecule) panel the read type is the
reverse-complement class and genome equivalence is dihedral. There the
positive answer **fails**: `S = AACAGT`, `T = AACTGT` (`L = 3`) are both
primitive `STRONG` (all `2`-mers distinct) with equal molecule-class
population laws, yet dihedrally inequivalent. The oriented panel is part of
the theorem, not an afterthought.

### 4.5 `P2` is not necessary at equal length
`AAAAB` (`L = 3`) is not `TRF` (triple repeat `AA` of length `2 > L−2`) yet has
a unique spectrum realization; Theorem Q is a sufficiency (one-way)
implication.

---

## 5. Independent computation

`python3 scripts/p2_population_proportional_attack.py` (self-contained, exact
integer arithmetic; currently ~5 min). It re-derives all predicates from
scratch, enumerates one Lyndon representative per rotation class (Duval), and
groups by spectrum.

### 5.1 Exhaustive scans (finite evidence)

| Scan | Range | Admissible words | Collisions |
|---|---|---|---|
| equal-length `P2` | `{A,B}`, `n ≤ 20`, `L ≤ 5` | 6 083 | **0** |
| equal-length `P2` | `{A,B,C}`, `n ≤ 14`, `L ≤ 4` | 325 338 | **0** |
| cross-length `TRF` | `{A,B}`, `n ≤ 16`, `L ≤ 5` | 4 791 | **0** |
| cross-length `TRF` | `{A,B,C}`, `n ≤ 11`, `L ≤ 4` | 30 790 | **0** |
| cross-length `P2` | `{A,B}`, `n ≤ 16`, `L ≤ 5` | 2 316 | **0** |
| one-sided `P2` (all primitive words grouped) | `{A,B}`, `n ≤ 20`, `L ≤ 5` | — | **0** |
| one-sided `P2` | `{A,B,C}`, `n ≤ 13`, `L ≤ 4` | — | **0** |
| random `P2`, `n ∈ [10,40]`, `q ∈ [2,4]`, `L ≤ 7` | 20 000 trials | 418 samples | **0** |

The "one-sided" rows group **all** primitive words (whether `P2` or not) by
same-length spectrum and report any group containing a `P2` word and a
non-rotational other word. Zero rows corroborate Theorem Q's one-sided form:
`P2(S)` alone already determines `S`.

### 5.2 BEST-theorem cross-check
The script also computes the number of cyclic Eulerian circuits of the de
Bruijn multigraph by the BEST theorem (`t_root · ∏_v (outdeg(v)−1)!`, with
`t_root` an exact integer arborescence determinant via Bareiss). This is an
independent route to equal-length ambiguity.

### 5.3 A convention subtlety the cross-check exposes
Best/BEST counts **parallel edge copies as distinct**, so a raw circuit count
`> 1` does **not** imply a second spelled word. Example: `S = AABAB` (`L = 3`)
is primitive `P2`, has Eulerian-circuit count `2` (two parallel `ABA` edges),
but the only spelled word is `AABAB` itself; `CABABB` (`L = 3`) has a repeated
`(L−1)`-mer with differing flanks and circuit count `1`. Any claim of the form
"`P2(S)` ⇒ the de Bruijn graph has a unique Eulerian cycle" is therefore false
as stated for the raw multigraph; the correct statement is uniqueness of the
spelled word / of the Eulerian cycle of the *condensed* graph, which is what
Theorem Q asserts.

### 5.4 What the computation does and does not show
The scans are bounded, so they are evidence, not proof, beyond their ranges.
The unbounded content is Lemma L\* and Theorem P (proved in §2) and Theorem Q
(a published theorem quoted in §3). No finite search substitutes for these.

---

## 6. Epistemic summary

| Claim | Status | Basis |
|---|---|---|
| Lemma L\*: primitive `TRF` ⇒ `(L−1)`-multiplicity `≤ 2` | **Proven** | maximal-extension triple-repeat argument (§2) |
| Theorem P: primitive `TRF` both sides + proportional ⇒ `c = 1` | **Proven** | Lemma L\* + forced Eulerian circuit (§2) |
| Theorem Q: `P2(S)` ⇒ `L`-spectrum determines `S` up to rotation | **Source theorem** | Ukkonen 1992; Pevzner 1995; BBT 2013 Thm 3 at `K = L−1`, circular reading (§3) |
| Main theorem: distinct primitive `P2` genomes have no proportional spectra | **Proven** (P + Q) | §2 + §3 |
| Equal-length uniqueness is one-sided in `S` | **Source theorem** + bounded check | §3, §5.1 |
| Primitivity necessary (cross length) | **Refuted without it** | `AAB` / `AABAAB`, `L = 3` |
| Candidate admissibility necessary (cross length) | **Refuted without it** | `AAAB` / `AAAABAAB`, `L = 3` |
| `TRF` insufficient at equal length | **Refuted** | `AABABB` / `AABBAB`, `L = 3` |
| Molecule-panel transfer | **False** | `AACAGT` / `AACTGT`, `L = 3` |
| Raw de Bruijn graph unique Eulerian cycle under `P2` | **False as stated** | `AABAB`, parallel-edge BEST count `2` (§5.3) |
| Population regime repairs the finite-sample #48 question | **Not claimed** | §7 |

---

## 7. Non-claims

* No claim about the finite-sample maximum-likelihood objective or the
  free-length normalization attacked in issue #48. This note is about the
  fibre of `D ↦ d_D` (the population/infinite-read law); it is compatible with,
  and does not repair, the finite negative result.
* No claim that the population regime is the primary route to the 2016
  question of `docs/open-problem.md`.
* No claim about non-uniform or non-i.i.d. sampling.
* No claim about the reverse-complement/molecule panel except the explicit
  counterexample of §4.4.
* The equal-length half is a cited published theorem under the circular
  reading; the repository's own contribution here is the independent
  cross-length proof, the sharpness analysis, the one-sided observation, and
  the bounded exact verification.

---

## 8. Reproduction

```text
python3 scripts/p2_population_proportional_attack.py
```

Prints the eight scans of §5.1 (with the sharpness witnesses of §4 and the
BEST subtlety of §5.3) and exits non-zero on any failed assertion.

## 9. Sources and anchors

| Item | Source / anchor |
|---|---|
| Circular true genome, error-free uniform reads, cyclically-shift reconstruction | Shomorony, Kim, Courtade, Tse, *Bioinformatics* 32(17):i494–i502, 2016, Eq. (1); [`docs/open-problem.md`](open-problem.md) |
| Repeat / triple repeat / interleaved / maximality | Bresler, Bresler, Tse, *BMC Bioinformatics* 14(Suppl 5):S18, 2013; [`docs/bridging-source-semantics.md`](bridging-source-semantics.md) |
| Circular `q`-gram characterization | Ukkonen, *Theoret. Comput. Sci.* 92(1):191–211, 1992; Pevzner, *Algorithmica* 13(1–2):77–105, 1995; Bresler–Bresler–Tse 2013, Theorem 3 (maximal repeats, `K = L−1`) |
| Dense-read / spectrum identifiability framing | [`docs/literature-status.md`](literature-status.md) §7 |
| Likelihood depends on candidate only through length and `L`-mer spectrum | Medvedev, Brudno, *J. Comput. Biol.* 16(8), 2009, §6.1; [`docs/ml-formalization-contract.md`](ml-formalization-contract.md) |
| Issue #48 (intrinsic candidate checks) / #45 (population analogue) | GitHub issues; concurrent branch artifacts `docs/issue48-intrinsic-candidate-checks.md`, `docs/population-identifiability-intrinsic-genomes.md`, `docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`, `docs/issue48-population-independent-verification-2026-09-21.md` (not on `main`) |
| Verifier | `scripts/p2_population_proportional_attack.py` |
