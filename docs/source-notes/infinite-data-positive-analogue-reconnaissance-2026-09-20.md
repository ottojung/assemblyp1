# Infinite-data positive analogue: reconnaissance for issue #45

_Status: reconnaissance only, 2026-09-20, based on `origin/main` at `8b2f0fc`.
This note does **not** assume issue #45's entry condition, does **not** declare
any finite source-faithful formulation settled, and does **not** claim a proof of
the published problem. It identifies the finite-sample failure mechanism on
current `main`, isolates the repeat/read-length boundary the bridging hypotheses
are calibrated to, and records candidate population/infinite-read positive
statements with a clean theorem and proof skeleton. Every claim is labelled
**source fact**, **mathematical proof**, **conjecture**, **computed**,
**modeling decision**, or **open**._

_Reproduction of the evaluator used below: `python3 scripts/verify_population_recon.py`._

_Artifact provenance. References to `docs/*.md` on `origin/main`, and to
`docs/source-notes/*` on `origin/main`, resolve on `main`. References to
`mathematics/*`, to `docs/unrestricted-length-proportional-reduction.md`, to
`docs/literature/substring-spectrum-identifiability-2026-09-20.md`, and to
`docs/source-notes/issue36-finite-vs-asymptotic-regime.md` are **branch-only**
artifacts (not on `main`); they are cited only for orientation, and every
load-bearing statement in this note is re-derived from `main` sources or proved
here, so the note does not depend on them._

---

## 0. Reconnaissance summary

1. **The finite failure is statistical, not a bridging failure.** On `main` the
   negative settlement rests on finite witnesses (`AAABB → AAAAB`, `AAATAT →
   AAAAAT`, ...) in which the winning competitor duplicates contexts for an
   overrepresented empirical read type and/or omits observed types
   ([`fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md),
   [`section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)).
   The bridging hypothesis `I_s` constrains the repeat structure of the truth and
   the reconstructibility of the realized reads; it never constrains the
   competitor spectrum, so it cannot control finite empirical skew
   ([`mathematics/deterministic-vs-likelihood-separation.md`](../../mathematics/deterministic-vs-likelihood-separation.md) §2).
2. **Passing to the population removes exactly that skew.** With reads i.i.d.
   uniform on the `G` circular starts, the empirical spectrum converges to the
   truth's spectrum, and the population exact-multinomial objective is uniquely
   maximized over fixed-length candidates by the truth's spectrum, by a
   weighted-KL / Gibbs argument (Theorem 1). This part is unconditional in `S`.
3. **What survives the limit is not statistical: the candidate-length tie and
   the spectrum-to-sequence gap.** The exact candidate-intrinsic objective has
   the exact tandem invariance `L(S^k) = L(S)` at every finite `n` and in the
   limit; and a unique optimal spectrum need not determine the sequence unless
   the repeat/read-length boundary is controlled. So a repaired theorem must fix
   the candidate length and use a combinatorial identifiability hypothesis.
4. **The bridging conditions are exactly the combinatorial half.** The `(L−1)`
   threshold is sharp: a length-`L` read can bridge only repeats of length
   `≤ L−2`, and the spectrum-ambiguity obstructions are interleaved/triple
   repeats of `(L−1)`-mers. Hence `I_s` is calibrated to the boundary and its
   only role in the repair is to convert "optimal spectrum" into "true sequence
   up to cyclic shift."
5. **Cleanest theorem shape.**
   `population consistency (unconditional in S) + spectrum uniqueness
   (combinatorial hypothesis) ⇒ truth is the unique exact-ML sequence up to
   cyclic shift, a.s. eventually`.
   Under the stronger `I_s^all` ("all maximal repeats bridged") the combinatorial
   half is elementary and proved here; under the source `I_s` it is Conjecture 4,
   which the classical Ukkonen–Pevzner characterization suggests is known rather
   than new (§6).
6. **Reframing.** Bridging does not cause ML optimality; concentration does.
   Bridging is what upgrades statistical spectrum-consistency into sequence
   recovery. The source sentence's per-instance quantifier over `R ∈ I_s` is a
   different statement from the population quantifier, so the repair is an
   analogue, not the literal sentence.

---

## 1. What current `main` settles, and what it leaves open

**Source fact.** The 2016 sentence has no sample-size, coverage, or limiting
qualifier; `I_s` is a set of realized read sets (Shomorony et al., Eq. (1),
p. i497; open question p. i501). `main`'s relevant determinations:

- Conclusion semantics are not fixed by the sentence: maximizer-only versus
  unique-up-to-equivalence, the genome equivalence, the candidate length, and
  ties are source gaps
  ([`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)).
- Cyclic shift is forced into the equivalence for the strong schema; reverse
  complement is coupled to the read-type space (oriented versus `k`-molecule
  classes) ([`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)).
- Given the §6.2 reading, the operative objective is molecule-class-indexed, and
  the same-length witness `AAATAT → AAAAAT` strictly beats the truth under both
  the §6.1 binomial and same-length exact objectives
  ([`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md),
  [`section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)).
- No located literature resolves the exact 2016 question
  ([`literature-status.md`](../literature-status.md)).

**Branch fact.** The finite-sample / high-coverage regime fork was recorded on an
unmerged branch (`audit/mb09-se62-relations-2026-09-20`,
`docs/source-notes/issue36-finite-vs-asymptotic-regime.md`); it is not on `main`.
Its core mathematical content (the Gibbs/KL limit) is re-derived independently
here and reconciled with `main`'s newer conclusion-semantics notes.

**Open.** Which Medvedev–Brudno layer the sentence denotes; the candidate length;
the read-type space; maximizer-versus-uniqueness. The population statements below
are therefore stated per layer, not as "the" answer.

---

## 2. The finite-sample failure mechanism, decomposed

Fix the truth `S` (circular, length `G`), read length `L ≤ G`, type space `T`
(oriented length-`L` words, or reverse-complement classes), truth spectrum
`d_S : T → ℤ_{≥0}`, `Σ_t d_S(t) = G`. For an observed count vector `x` (fixed
length `G`), the exact ordering objective is

```text
ℓ(D | x) = Σ_t x(t) log( d_D(t) / G ).
```

The repository witnesses exhibit three logically distinct mechanisms:

- **(M1) empirical skew.** `x` is not proportional to `d_S`, and a competitor
  whose spectrum better matches the skewed frequencies wins. The clean
  characterization is the normal-cone/proportionality theorem: for an interior
  spectrum, `d_S` is optimal iff `x ∝ d_S`
  ([`mathematics/bridging-to-ml-reductions.md`](../../mathematics/bridging-to-ml-reductions.md) §4;
  [`docs/unrestricted-length-proportional-reduction.md`](../unrestricted-length-proportional-reduction.md) Thm 1).
  Witnesses: the `2^k` amplification family
  ([`fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md) §"Parametric family")
  and the `AAATAT` same-length witness.
- **(M2) support omission.** A competitor omits an observed type; at finite `n`
  the omitted type may be unobserved. As `n` grows, any type with `d_S(t) > 0` is
  observed and the competitor's likelihood becomes `0`. Both `AAABB → AAAAB`
  (omits `ABB`, `BBA`) and `AAATAT → AAAAAT` are of this shape.
- **(M3) candidate-class and length effects.** The exact candidate-intrinsic
  objective satisfies the exact tandem invariance `L(D^k | x) = L(D | x)` for
  every `k ≥ 1` and every sample, because `d_{D^k}/(k|D|) = d_D/|D|`. This is not
  a sampling effect: it persists in the population limit. The §6.2 per-vertex
  lower bound (a spelled candidate must contain every observed molecule at least
  once) is likewise a candidate-class restriction, not a fluctuation.

**Diagnosis.** M1 and M2 are large-deviation events of the sampling process and
vanish as `n → ∞`; M3 does not. A valid population analogue must therefore
(i) concentrate the sample and (ii) fix the candidate length / candidate class.

---

## 3. The repeat/read-length boundary

This is the exact sense in which bridging is calibrated to read length.

- A length-`ℓ` copy at `t` is bridged by a read `[r, r+L)` iff, on an integer lift,
  `r < t` and `t + ℓ < r + L`, i.e. `L ≥ ℓ + 2`. Hence a length-`L` read can
  bridge a copy only if `ℓ ≤ L − 2`; a copy of length `L − 1` or longer can never
  be bridged by any read of length `L`. [source fact + mathematical proof;
  [`bridging-source-semantics.md`](../bridging-source-semantics.md)]
- With the full read set, `S` admits some `R ∈ I_s` iff every triple repeat has
  length `≤ L − 2` and every interleaved maximal-repeat pair has a constituent of
  length `≤ L − 2` ("`I_s`-admissible"). The stronger "all maximal repeats
  bridged" condition `I_s^all` is equivalent to "no `(L−1)`-mer occurs twice,"
  which implies every length-`L` window occurs at most once
  ([`mathematics/bridging-and-spectrum-uniqueness.md`](../../mathematics/bridging-and-spectrum-uniqueness.md)
  §1–2, Lemma 1). [mathematical proof]
- On the spectrum side, the exact objective depends on a fixed-length candidate
  only through `d_D`. Spectrum ambiguity is governed by interleaved and triple
  repeats of `(L−1)`-mers — exactly the boundary objects — by the classical
  Ukkonen–Pevzner characterization, restated as Çelikkanat et al. (2024)
  Theorem 3.1 ([`literature/substring-spectrum-identifiability-2026-09-20.md`](../literature/substring-spectrum-identifiability-2026-09-20.md)).
  [source fact + analysis]

**Boundary statement.** Repeats of length `≤ L − 2` are bridgeable and do not
create spectrum ambiguity; repeats of length `≥ L − 1` are unbridgeable and are
precisely the spectrum-ambiguity boundary. `I_s` is the source's attempt to
exclude the latter. It is sharp at `L − 1`, and it is unrelated to the empirical
skew M1/M2. This is the structural reason the finite problem fails while a
population analogue succeeds.

---

## 4. Candidate positive statements and proof skeleton

Throughout, assume `S` is primitive (least period `G`), `L ≥ 2`, `G ≥ L`, and the
population model is source §2: reads i.i.d. uniform over the `G` circular starts.
`T` is finite. Two read-type panels are kept separate (oriented versus molecule
classes); the theorems below are panel-agnostic until the equivalence is named.

### 4.1 Primary deterministic population theorem (fixed candidate length)

**Definition (population objective).** With `p(t) := d_S(t)/G` and a length-`G`
candidate `D`, set

```text
ℓ_pop(D) := Σ_{t: p(t)>0} p(t) log( d_D(t) / G ),
```

with `ℓ_pop(D) := −∞` if some `t` has `p(t) > 0 = d_D(t)`.

**Theorem 1 (population spectrum consistency; mathematical proof).** For every
length-`G` circular candidate `D`, `ℓ_pop(D) ≤ ℓ_pop(S)`, with equality if and
only if `d_D = d_S`.

_Proof skeleton._
1. Let `q_D(t) := d_D(t)/G`; both `p` and `q_D` are probability vectors on `T`.
   Then `ℓ_pop(D) = Σ_t p(t) log q_D(t)`, and `ℓ_pop(S) = Σ_t p(t) log p(t)`.
2. Hence `ℓ_pop(S) − ℓ_pop(D) = Σ_t p(t) log(p(t)/q_D(t)) = KL(p ‖ q_D) ≥ 0`,
   by Gibbs' inequality, with equality iff `q_D = p` on `supp(p)`.
3. `Σ_t q_D(t) = Σ_t p(t) = 1` and `q_D ≥ 0`, so `q_D = p` on `supp(p)` forces
   `q_D = p` everywhere, i.e. `d_D = d_S`. ∎

The candidate spectra are exactly the integer vectors with `Σ_t d(t) = G` that
are realizable, a finite set; no Eulerian-polytope convexity is needed for
Theorem 1, only that realization is a subset of the simplex.

**Corollary 1 (empirical consistency; mathematical proof).** Let `X^{(n)}` be
i.i.d. counts from `p` and define `ℓ_n(D) := (1/n) log L_exact(D | X^{(n)})`
(fixed length `G`; the observation-only multinomial coefficient is
candidate-independent). Then almost surely there is `n_0` such that for all
`n ≥ n_0` and every length-`G` candidate `D`,

```text
ℓ_n(D) ≤ ℓ_n(S),   with equality iff d_D = d_S.
```

_Proof skeleton._
1. For each realizable spectrum vector `d`,
   `Σ_t (X_t/n) log(d(t)/G) → Σ_t p(t) log(d(t)/G)` a.s. (finite sum, LLN), and
   `(1/n) log(n! / ∏_t X_t!) → H(p)` (Stirling), so `ℓ_n → −KL(p ‖ q_D)`.
   The limit equals `0` iff `d = d_S` by Theorem 1.
2. Uniformize over the finite set of realizable length-`G` spectra: intersect the
   finitely many a.s. convergence events and the finitely many events
   "`X_t ≥ 1` eventually" for `p(t) > 0`; the intersection is a.s. and gives the
   claimed `n_0`. Candidates with a zero on an observed type have `ℓ_n = −∞`
   eventually a.s. ∎

### 4.2 Sequence-level theorem (adds the combinatorial half)

**Hypothesis SU (spectrum uniqueness).** For the truth `S`, every length-`G`
circular `D` with `d_D = d_S` satisfies `D ≈ S`, where `≈` is the panel's genome
equivalence (cyclic shift, or dihedral under the molecule panel).

**Theorem 2 (population sequence recovery, conditional on SU; mathematical
proof).** Under SU, almost surely for all sufficiently large `n`, every
fixed-length exact-ML maximizer is `≈ S`; equivalently the unique ML spectrum is
the truth's and its unique spelling is the truth up to `≈`.

_Proof._ A maximizer's spectrum equals `d_S` by Corollary 1; SU identifies it
with `S`. ∎

**Theorem 3 (elementary SU under `I_s^all`; mathematical proof).** If no
`(L−1)`-mer of `S` occurs twice, then `d_D = d_S` implies `D ≈ S` over oriented
read types; under the molecule panel replace `≈` by dihedral.

_Proof skeleton._ In the `L`-mer de Bruijn multigraph, an edge is a type in the
spectrum. No repeated `(L−1)`-mer means every vertex (an `(L−1)`-mer) has
in-degree and out-degree at most `1`, so the multigraph is a disjoint union of
node-disjoint directed paths and cycles. An Eulerian closed walk covering all
edges is therefore forced up to rotation; the spelled genomes `D` and `S` are
both such walks, hence rotate into each other. (Molecule panel: apply the
reverse-complement relabelling, which preserves the class spectrum.) ∎

This is the unconditional, fully elementary half; it uses `I_s^all`, which is
strictly stronger than the source `I_s`.

### 4.3 Source-hypothesis version (conditional on Conjecture 4)

**Hypothesis SU_I** (repository Conjecture 4; equivalently the circular
Ukkonen–Pevzner / Pevzner-1995 statement): if `S` is `I_s`-admissible then any
same-length `D` with `d_D = d_S` is a cyclic shift of `S`
([`mathematics/bridging-and-spectrum-uniqueness.md`](../../mathematics/bridging-and-spectrum-uniqueness.md) §5).

**Theorem 4.** Under SU_I, Theorem 2 holds with the source `I_s` hypothesis.
[mathematical proof, conditional on SU_I] SU_I is a conjecture with 123,906
exhaustive admissible cases and 1,655 randomized cases, zero counterexamples;
the spectrum-identifiability search note argues it is the circular case of a
known classical theorem, so its status is "likely known, not yet kernel-checked
and not yet pinned to a circular primary statement." [conjecture + analysis]

### 4.4 The high-coverage a.s.-eventual `I_s` tail

For the source `I_s` per-instance clue to be respected, note that with i.i.d.
sampling every start position is visited infinitely often almost surely.
Therefore a.s. eventually `R^{(n)}` contains the full read set as a sub-multiset;
since `I_s`-admissibility is exactly "the full read set lies in `I_s`," it follows
that a.s. eventually `R^{(n)} ∈ I_s`. Combined with Corollary 1 and SU_I this
gives the "repaired per-instance" form:

**Corollary 2 (a.s.-eventual repair of the per-instance reading; mathematical
proof, conditional on SU_I).** Almost surely there is `n_0` such that for all
`n ≥ n_0`: `R^{(n)} ∈ I_s` and every fixed-length exact-ML maximizer is `S` up
to cyclic shift. [conditional]

This is a positive population analogue of the (refuted) per-instance implication
`R ∈ I_s ⇒ truth is ML`. It does not contradict the finite witnesses: they are
finite-`n` events excluded by the a.s.-eventual quantifier.

### 4.5 Other likelihood layers (sketch, not proved here)

- **Fixed-`N` binomial approximation.** With external `N = G`, the per-type limit
  term `p log q_D + (1−p) log(1−q_D)` is uniquely maximized per type at
  `q_D = p`, and `Σ_t d_D(t) = N` forces `N(D) = G`; the population consistency
  and the sequence-level conclusion are unchanged. [mathematical proof sketch]
- **§6.2 flow layer.** The source-faithful §6.2 objective is the separable cost
  on read-molecule vertices with per-vertex lower bound `1`. In the population
  limit the observed support equals `supp(d_S)`, so the lower bound becomes
  vacuous for the truth; the truth-induced circuit is the population-optimal
  admissible circuit. But §6.2 outputs a "(non-contiguous) assembly," not a
  sequence, so the clean positive statement is about the flow, not the spelled
  sequence. Turning it into a sequence-level statement requires the same SU step
  plus a flow-to-sequence correspondence that the source does not provide. [open]

---

## 5. What this says about the role of bridging

**Decomposition (mathematical proof).** Theorem 1 and Corollary 1 hold for every
truth `S`, with no repeat or bridging hypothesis. The only place `I_s` enters the
repaired theorem is SU (or `I_s^all`), i.e. the combinatorial identification
`d_D = d_S ⇒ D ≈ S`.

Consequently:

1. The statistical half of the issue-#45 intuition is true but is not supplied
   by bridging.
2. The bridging hypothesis is necessary and sufficient (given the classical
   spectrum theorem) for the combinatorial half at the `(L−1)` boundary.
3. "Bridging guarantees ML optimality" is false as a causal claim; the correct
   repaired statement is "concentration guarantees spectrum consistency, and
   bridging upgrades spectrum consistency to sequence recovery."

This is a strictly cleaner picture than the finite formulation, and it exposes
why the finite problem failed: the finite witnesses test the statistical half
while the hypothesis controls only the combinatorial half.

---

## 6. Dependencies on unresolved finite/source semantics

Every item below must be resolved (or explicitly parameterized) before any
population theorem can be described as source-faithful.

- **D1. Which ML layer** the sentence denotes (exact candidate-intrinsic
  multinomial, fixed-`N` binomial, §6.2 flow, or a broad principle). Theorems 1–4
  are proved for the exact fixed-length layer; §4.5 covers the others only
  partially. [source gap]
- **D2. Candidate length.** Fixed length `G` is required for Theorems 1–4. With
  free length, tandem invariance `L(D^k) = L(D)` makes the strong uniqueness
  conclusion false in the population limit as well (M3). [source gap]
- **D3. Read-type space.** Oriented types give `≈ =` cyclic shift; molecule
  classes give `≈ =` dihedral. This changes the final clause, not the KL
  argument. [source gap / §6.1 `4^k` versus `(4^k+p_k)/2` internal tension]
- **D4. Conclusion schema.** Theorem 2 delivers unique-up-to-`≈`; the
  maximizer-only schema follows a fortiori. Which one the sentence means is
  unresolved. [source gap]
- **D5. Spectrum-uniqueness hypothesis.** `I_s^all` version is proved
  (Theorem 3). Source `I_s` version is SU_I/Conjecture 4: strong finite evidence,
  likely the circular Ukkonen–Pevzner theorem, but no circular primary statement
  and no kernel check yet. The exact `(L−1)` versus `(L−2)` threshold and the
  circular boundary condition must be verified against a primary source. [conjecture]
- **D6. Quantifier.** The source sentence is per-instance over `R ∈ I_s`
  (Regime F), which is refuted by the finite witnesses. Theorem 2/Corollary 2 are
  a.s.-eventual (Regime H), a different quantification. Calling the repair an
  "analogue" rather than the source statement is essential. [interpretation]
- **D7. §6.2 candidate class.** Per-vertex lower bound `1` versus the
  per-occurrence strengthening; and whether spelled circuits or general feasible
  flows are the candidate objects. Affects §4.5 and the AAATAT-type witnesses
  (the strict-oriented `4^k` control inverts the witness). [source gap /
  source-supported inference]
- **D8. Ties.** Rotations always tie exactly; the equivalence must contain
  cyclic shift for the strong schema, independently of any hypothesis. [mathematical proof]
- **D9. Population model.** I.i.d. uniform reads is source §2. Uniformity is used
  only for `X_t/n → p`; any sampling model with the same consistency would do.
  The population idealization is not itself in the source. [modeling decision]
- **D10. Primitivity/periodicity.** Non-primitive `S` degenerates the repeat
  definitions and the rotation orbit; all statements assume primitive `S` and
  `L ≥ 2`, `G ≥ L`. [modeling decision]

---

## 7. Evaluators run

`scripts/verify_population_recon.py` (self-contained, exact, deterministic,
exits non-zero on failure) checks, over small instances:

- **A. Population consistency.** For every truth in the enumerated small range,
  the exact population objective over all realizable fixed-length spectra is
  maximized exactly by `d_S`. [computed; consistent with Theorem 1]
- **B. Sharp `L−1` boundary.** For every `S` with no repeated `(L−1)`-mer, every
  same-length candidate with equal `L`-mer spectrum is a rotation of `S`, over
  alphabets of size 2 and 3. [computed; consistent with Theorem 3]
- **C. Proportional-sample repair.** On the repository `AAABB` witness
  (`G = 5`, `L = 3`), the proportional count vector `x = d_S` makes the truth the
  unique ML maximizer over same-length candidates, whereas the repository's
  skewed sample is the known counterexample. [computed]

These are bounded checks (small `G`, small alphabets), not proofs of the general
statements; the general statements are Theorems 1–3 with the proof skeletons
above.

---

## 8. Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| Finite failure decomposes as M1 (skew), M2 (support omission), M3 (length/class) | mathematical proof + source facts | §2, witness arithmetic on `main` |
| `I_s` cannot constrain the competitor spectrum (asymmetry) | mathematical proof | `deterministic-vs-likelihood-separation.md` §2; §2 here |
| Theorem 1: population fixed-length objective uniquely maximized at `d_S` | mathematical proof | Gibbs/KL, §4.1 |
| Corollary 1: a.s.-eventual empirical consistency, uniform over fixed-length candidates | mathematical proof | LLN + finiteness, §4.1 |
| Theorem 2: sequence recovery given SU | mathematical proof | §4.2 |
| Theorem 3: `I_s^all` ⟹ SU, elementary | mathematical proof | de Bruijn graph in/out degree ≤ 1, §4.2 |
| Theorem 4 / SU_I: source `I_s` version | conjecture (likely known classical) | Conjecture 4 = circular Ukkonen–Pevzner; 123,906 + 1,655 cases, 0 cex |
| Corollary 2: a.s.-eventual `R^{(n)} ∈ I_s` and recovery | mathematical proof, conditional on SU_I | §4.4 |
| Fixed-`N` binomial shares the population conclusion | mathematical proof sketch | §4.5 |
| §6.2 population flow statement | open | §4.5 |
| Boundary is sharp at `L−1` | mathematical proof + source fact | §3 |
| Evaluators A–C | computed (bounded) | §7 |
| Which layer/length/read-type/schema the sentence denotes | source gap | D1–D4 |

---

## 9. Handoff

**Portfolio changes.** Adds one explored approach to the issue-#45 frontier:
"population consistency + spectrum uniqueness" as the repaired positive analogue,
with the finite failure decomposed into a statistical half (concentration) and a
combinatorial half (bridging at the `(L−1)` boundary).

**Evaluators run.** `scripts/verify_population_recon.py` (checks A–C, passed).

**Approaches promoted.** (1) Prove the elementary `I_s^all` sequence theorem
(Theorem 3) in Lean as a bounded target. (2) Pin a circular primary statement of
the Ukkonen–Pevzner characterization to upgrade SU_I from conjecture to source
theorem. (3) Formalize Corollary 1's finite candidate enumeration for a fixed
small instance as an exact evaluator.

**Approaches revised/subsumed.** The unmerged finite-vs-asymptotic note's Regime
H content is independently reproduced and reconciled with `main` here; nothing
in it is overturned.

**Blocked.** The source-faithful population theorem is blocked on D1 (ML layer),
D2 (length), D3 (read-type space), and D5 (SU_I); none can be chosen by fiat.

**Best current frontier.** Prove Theorem 3 + a finite instance of Corollary 1 in
Lean; independently verify the circular Ukkonen–Pevzner threshold at `L−1`.

**Non-claims.** This note does not assert the issue-#45 entry condition, does not
settle any finite source-faithful formulation, does not select an ML layer, and
does not claim the published open problem is resolved.
