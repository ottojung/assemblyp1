# Direct circular proof of `P2 ⇒ L`-spectrum uniqueness, and its exact primitive hypothesis

_Status: mathematical proof (primitive case) + one clean combinatorial lemma + an
independent exact verifier. Not a Lean result. This note attacks the equal-length
half of the population-identification packet for issue #48 / issue #45 **directly on
the circular model**, without using the "unique Eulerian cycle of the condensed
`K`-mer graph / Bresler–Bresler–Tse Theorem 3" citation as a black box. It is
compatible with, and independent of, the concurrent P2 proportional-spectrum
counterexample search: no counterexample is found, and the emphasis here is proof._

_Reproduction: `python3 scripts/verify_circular_p2_spectrum_uniqueness.py`
(self-contained, exact integer/combinatorial arithmetic; exits non-zero on any
failed assertion)._

---

## 0. Direct answer

The equal-length spectrum uniqueness step

> **Theorem Q (primitive form).** Let `L ≥ 2` and let `S` be a **primitive** circular
> word of length `G ≥ L` satisfying `P2(S,L)` (`TRF ∧ ILF`: no Bresler triple repeat
> and no interleaved pair of maximal repeats of length `≥ L−1`). If `T` is a circular
> word of the same length `G` with the same length-`L` spectrum `d_T = d_S`, then `T`
> is a cyclic shift of `S`.

is proved here from scratch. The proof

1. reduces the two words to the **same** de Bruijn multigraph `D` (vertices
   `(L−1)`-mers, edges `L`-mers with multiplicity) in which `S` and `T` are Eulerian
   circuits;
2. encodes the two circuits by permutations `σ_S, σ_T` of the `G` edge occurrences
   and studies `ρ = σ_T σ_S^{-1}`; one checks `ρ` preserves each out-star `Out(v)`,
   and, under primitive + `TRF`, `|Out(v)| ≤ 2`, so `ρ` is an involution;
3. uses a purely combinatorial **Matching/Cycle Lemma**: a nontrivial involution
   `ρ` with `ρσ` a single cycle must have a **crossing** chord matching;
4. reads a crossing as **interleaved occurrences** of two `(L−1)`-mers, hence an
   `ILF` violation — contradiction. So `ρ = id`, i.e. `σ_T = σ_S`, i.e. `T` is a
   rotation of `S`.

The only hypothesis the direct argument uses beyond `P2` is **primitiveness**, and it
uses it exactly once: to get `|Out(v)| ≤ 2` (Lemma L\* below) and to make maximal
extensions proper. The stronger claim sometimes stated in the concurrent population
packet — that the equal-length half needs **no** primitivity — is *not* obtained by
this argument; the non-primitive case is isolated in §7 as the exact residual
(finitely verified, not proved here). The intended use (the population theorem, whose
hypotheses include primitive genomes on both sides) only needs the primitive form.

No counterexample was found. Independent searches over one representative per circular
class give no `P2` word with a same-length, same-spectrum, non-rotational mate for
binary words of length `≤ 22` (`L = 2..6`) or ternary words of length `≤ 13`
(`L = 2..5`); see §8.

---

## 1. Statement and conventions

**Circular words.** `W = W[0..n)` with all indices cyclic; `rot(W,i)` is the cyclic
shift; `W ~ W'` means equal up to cyclic shift. `W` is **primitive** if it is not a
nontrivial power `C^m`, `m ≥ 2`.

**Spectrum.** `d_W(w) = #{ cyclic starts t : W[t..t+L) = w }` for length-`L` words `w`.
The spectrum is the complete data of the exact Medvedev–Brudno §6.1 objective up to the
observation-only multinomial coefficient, so equal-`L`-spectrum same-length words tie
for **every** sample; this note is about the fibre of `D ↦ d_D`, prior to any
likelihood or tie rule.

**De Bruijn multigraph `D`.** Vertices are the `(L−1)`-mers occurring in `S`. For each
`L`-mer occurring with multiplicity `m`, one has `m` parallel directed **edge
occurrences** from its `(L−1)`-prefix to its `(L−1)`-suffix. Write `tail(e)`, `head(e)`
for these, and `Out(v)` for the multiset of edges with `tail(e) = v`. There are exactly
`G` edge occurrences, one per circular start of `S`.

**Bresler repeat vocabulary (inherited by Shomorony et al. 2016).**

* a **maximal repeat pair** of length `ℓ` is a pair of starts `t₁ ≠ t₂` with
  `W[t₁..t₁+ℓ) = W[t₂..t₂+ℓ)`, `W[t₁−1] ≠ W[t₂−1]`, `W[t₁+ℓ] ≠ W[t₂+ℓ]`;
* a **triple repeat** of length `ℓ` is three starts with equal length-`ℓ` windows and
  *not all* three preceding symbols equal and *not all* three following symbols equal;
* an **interleaved pair** is a pair of maximal repeat pairs with four distinct starts
  alternating `t₁ < t₂ < t₃ < t₄` (or `t₂ < t₁ < t₄ < t₃`); its length is the shorter
  constituent.

**Predicates.**

* `TRF(W,L)`: no triple repeat of length `≥ L−1`.
* `ILF(W,L)`: no interleaved pair of maximal repeats both of length `≥ L−1`.
* `P2(W,L) = WEAK(W,L) := TRF(W,L) ∧ ILF(W,L)`.

`P2` is the full-read-set shadow of the source condition `I_s` (the "full-read
reduction"): a length-`ℓ` copy is strictly bridged on both sides by a length-`L` read
iff `ℓ ≤ L−2`, so the full read set lies in `I_s` iff there is no triple or interleaved
obstruction of length `≥ L−1`. This note uses only the combinatorial predicates and
makes no claim about likelihoods or sampling.

---

## 2. Reduction to transition permutations

Let `T` have the same length `G` and the same `L`-spectrum. Then `D` (built from `d_S`)
is also the de Bruijn multigraph of `T`, with the *same* edge multiset; `S` and `T` are
Eulerian circuits of `D` using each edge occurrence exactly once. Identify the edge
occurrences by their `L`-mer type in any fixed way (there are `G` of them, matched by
multiplicity).

Index them by `i ∈ Z_G` so that `S = e_0 e_1 … e_{G−1}` (cyclic). Define

```text
σ_S(e_i) = e_{i+1}                       (the successor permutation of S),
σ_T(e)   = the T-successor of e.
```

Both `σ_S, σ_T ∈ Sym(E)` are single `G`-cycles (each circuit is one closed walk using
all `G` edge occurrences). Define `ρ = σ_T σ_S^{-1}`.

**Lemma R (out-star preservation).** `tail(ρ(e)) = tail(e)` for every `e`; hence `ρ`
preserves every `Out(v)` and `ρ = ⊔_v ρ_v` with `ρ_v ∈ Sym(Out(v))`.

**Proof.** `ρ(e_i) = σ_T(σ_S^{-1}(e_i)) = σ_T(e_{i−1})`, and
`tail(σ_T(e_{i−1})) = head(e_{i−1}) = tail(e_i)`. ∎

**Lemma T⇔rotation.** `T` is a rotation of `S` iff `σ_T = σ_S`, i.e. iff `ρ = id`.

**Proof.** If `σ_T = σ_S` under the chosen occurrence identification, the cyclic type
sequences coincide, so `T ~ S`. Conversely if `T = rot(S,k)`, the identification that
matches each occurrence of `T` with its `rot(S,k)` preimage makes the two successor
permutations equal. (For `G = 1` the statement is vacuous; take `G ≥ 2`.) ∎

So it suffices to prove: **`P2(S) ∧ primitive(S)` forces `ρ = id`.**

---

## 3. Lemma L\* (multiplicity cap)

**Lemma L\*.** If `W` is primitive and `TRF(W,L)`, then every `(L−1)`-mer of `W`
occurs at most twice. Equivalently `|Out(v)| ≤ 2` for every vertex `v`.

**Proof.** Suppose an `(L−1)`-mer `v` occurs at three distinct starts `t₁,t₂,t₃`.
Extend the three copies to the right while their next symbols all agree; this gives
three equal length-`ℓ` windows with `ℓ ≥ L−1`, and (unless the extension wraps the whole
circle) their following symbols are not all equal at maximality. If the right extension
wraps fully, extend left instead; in all cases, extend maximally on both sides while
the three windows stay equal. If the common extension covers the whole circle
(`ℓ + j = n`), the three equal windows of length `n` at distinct starts exhibit a
nontrivial rotational symmetry of `W`, so `W` is a nontrivial power, contradicting
primitivity. Hence the common extension is proper, and at maximality the three copies
have *not all* preceding symbols equal and *not all* following symbols equal: a Bresler
triple repeat of length `ℓ + j ≥ L−1`, contradicting `TRF`. ∎

_(The same statement is in the population packet as "Lemma L\*"; the proof is included
here so the direct argument is self-contained. The wrap case is exactly where
primitivity enters.)_

---

## 4. The Matching/Cycle Lemma

**Lemma M.** Let `σ = (0 1 … n−1)` be the cyclic shift on `[n]`, `n ≥ 2`. Let `ρ` be a
product of `s ≥ 1` disjoint transpositions (with the remaining points fixed). If the
chord matching `{(a,b) : ρ(a)=b}` has **no crossing** on the circle — i.e. there are no
two pairs `a<c<b<d` — then `τ = ρ σ` is **not** a single `n`-cycle.

**Proof.** Order the `2s` moved points cyclically, and choose a matched pair `(a,b)`
with no other moved point on the clockwise arc from `a` to `b` (exists: take a pair
minimizing the number of moved points strictly inside its arc; non-crossing puts any
inside points in matched pairs inside, contradicting minimality). So the clockwise arc
`a, f₁, f₂, …, f_t, b` has only fixed points `f_j` strictly between `a` and `b`, and
`σ(a) = a+1`.

Now compute the `τ`-orbit of `a`. If `t = 0`, then `σ(a) = b`, so
`τ(a) = ρ(σ(a)) = ρ(b) = a`: a fixed point, so `τ` has a fixed point and is not a
single `n`-cycle (for `n ≥ 2`). If `t ≥ 1`, then `a+1 = f₁` is fixed, so
`τ(a) = ρ(f₁) = f₁`; inductively `τ(f_j) = ρ(f_{j+1}) = f_{j+1}` for `j < t`, and
`τ(f_t) = ρ(σ(f_t)) = ρ(b) = a`. Thus the whole arc `{a} ∪ {f₁,…,f_t}` is one `τ`-cycle.
It does not contain `b`, so `τ` has at least two cycles (the remaining points are
non-empty). Hence `τ` is not a single cycle. ∎

_Verified exhaustively for `n ≤ 8` over all involutions in §8 check A (147 nontrivial
single-cycle cases, all crossing)._

---

## 5. Proof of Theorem Q (primitive form)

Let `S` be primitive, `P2(S,L)`, and let `T` be same-length with `d_T = d_S`. Keep the
notation of §2, so `σ_S, σ_T` are single `G`-cycles and `ρ = σ_T σ_S^{-1}` preserves
`Out(v)` (Lemma R).

By Lemma L\*, `|Out(v)| ≤ 2` for every `v`; hence each `ρ_v` is either the identity or
the transposition of the two elements of `Out(v)`. Therefore `ρ` is an involution, a
product of disjoint transpositions, each swapping the two outgoing edges at some vertex
`v`.

If `ρ = id`, Lemma T⇔rotation gives `T ~ S`. Suppose, for contradiction, `ρ ≠ id`.
Apply Lemma M with `n = G` and `σ = σ_S`: since `τ = ρ σ_S = σ_T` is a single
`G`-cycle, the matching of `ρ` has a crossing. A crossing is two pairs with (after
relabelling) starts `a < c < b < d` where `(a,b)` are the two occurrences of some
`(L−1)`-mer `v` (they are paired in `Out(v)`) and `(c,d)` the two occurrences of some
other `(L−1)`-mer `w`. Extend the two occurrences of `v` maximally left and right: by
primitivity the common extension is proper (it cannot wrap the circle, else `S` would
carry a nontrivial rotational symmetry), giving a maximal repeat pair of length
`≥ L−1` with the same two starts `a,b`; do the same for `w`, giving a maximal repeat
pair with starts `c,d`. The four starts still satisfy `a < c < b < d`, so they form an
**interleaved pair of maximal repeats both of length `≥ L−1`**, i.e. `ILF(S,L)` fails,
contradicting `P2`. Hence `ρ = id` and `T ~ S`. ∎

**Corollary (used by the population packet).** If `S` is primitive `P2` and `T` is
primitive `P2` with `d_T = c·d_S`, then `c = 1` and `T ~ S`, because the cross-length
half (primitive + `TRF` on both sides) forces `c = 1`. This is the equal-length input
of the population identification; the present note supplies its direct circular proof.

---

## 6. Why this is a genuinely circular proof, not the boundary shortcut

The earlier repository reconciliation anchored `P2 ⇒` spectrum uniqueness on
Bresler–Bresler–Tse Theorem 3 (the `K`-mer graph / condensed graph statement) with a
"circular Eulerian-cycle reading". That is a correct source theorem, but it is a
*citation*; a reader could object that the circular statement is being *assumed* by
reading a linear/condensed theorem circularly. The argument above is different in kind:

* it never leaves the circular model: `S` and `T` are circular words, their spectra are
  circular-window multiplicities, and the de Bruijn graph is a finite multigraph whose
  Eulerian circuits are exactly the circular words with that spectrum;
* it never appeals to a uniqueness theorem for the condensed graph or to a linear
  boundary statement;
* the only external input is Lemma M, a self-contained statement about involutions and
  cyclic shifts, proved in §4 and verified exhaustively.

What the direct proof *does* expose is that the classical theorem's simplicity hides a
real hypothesis: primitivity (or, more precisely, the `|Out(v)| ≤ 2` conclusion of
Lemma L\*). The source theorem is true for all input words, but the elementary proof
above reaches the primitive case directly and needs a genuinely separate argument for
the periodic case.

---

## 7. The exact residual: non-primitive `S`

Lemma L\* is false without primitivity: `W = (AB)^3` (`L = 3`) has every `(L−1)`-mer
occurring three times, all with equal flanks, so `TRF` (indeed `P2`) holds, yet
`|Out(v)| = 3`. In the proof of Theorem Q the involution structure of `ρ` — and hence
Lemma M — then no longer applies, and the maximal-extension step can wrap.

Concretely, the missing case is:

> **Residual (non-primitive equal-length).** `S = C^m`, `C` primitive, `m ≥ 2`,
> `P2(S,L)`, and `d_T = d_S`, `|T| = |S|` ⟹ `T ~ S`.

This is **not proved here**. It is consistent with all finite searches (§8): periodic
`P2` words such as `(AAB)^2` or `(AABB)^2` (both `P2` at `L = 3`) have spectrum-unique
neighbours in the searched ranges. Two candidate routes:

1. **Reduce to the primitive case.** Show `d_T = m·d_C` forces `T = C'^m` for a
   primitive `C'`, then apply Theorem Q to `C, C'` (this needs `P2(C')`/`TRF(C')` and
   is not immediate, since a triple repeat of `C` can become flanks-equal after
   powering).
2. **Generalize Lemma M to arbitrary `ρ`.** Replace the involution matching by the
   cycle structure of `ρ` along the `σ_S`-orbit; the non-crossing involutive case above
   is the `|Out(v)| ≤ 2` slice. A general "cycle-type vs. crossing" statement would
   settle the residual directly. This is the precise combinatorial gap.

**Consequence for the concurrent packet.** The sentence "primitivity is not needed for
this step" in `docs/issue48-p2-population-proportional-identification.md` (branch
`agent/p2-population-proportional-0921`) is not established by the direct proof; the
direct proof uses primitivity through Lemma L\*. The population theorem's hypotheses
include primitivity, so this does not affect its main claim, but the one-sided
"no primitivity" remark should be treated as finitely verified, not proved.

---

## 8. Computational verification

`scripts/verify_circular_p2_spectrum_uniqueness.py` is self-contained and exact. It
checks:

* **A. Matching/Cycle Lemma.** For all `n ≤ 8`, every nontrivial involution `ρ` with
  `ρσ` a single `n`-cycle has a crossing (147 cases); every non-crossing nontrivial
  `ρ` gives a `ρσ` with `≥ 2` cycles.
* **B. Finite one-sided statement.** One representative per circular class (Lyndon
  words for aperiodic classes, powers of Lyndon words for periodic classes), grouped by
  exact length-`L` spectrum: binary length `≤ 18`, `L = 2..6`; ternary length `≤ 11`,
  `L = 2..5`. `29 195` nontrivial spectrum fibres were inspected; **none** contains a
  `P2` word together with a non-rotational mate. (An additional one-off run reached
  binary length `22` and ternary length `13` with the same result.)
* **C. Proof mechanism.** For every same-length same-spectrum non-rotational pair
  `(S,T)` with `S` primitive and `(L−1)`-multiplicity `≤ 2`, it recomputes
  `ρ = σ_T σ_S^{-1}` and verifies that `ρ` preserves each `Out(v)`, is a nontrivial
  involution, has a crossing, and that `S` is not `P2`. `266` pairs analysed.

Run:

```text
python3 scripts/verify_circular_p2_spectrum_uniqueness.py
```

It prints `all checks passed` and exits non-zero on any violation.

---

## 9. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Lemma R (out-star preservation of `ρ`) | **Proven** | §2 |
| Lemma T⇔rotation (`T ~ S` iff `ρ = id`) | **Proven** | §2 |
| Lemma L\* (primitive + `TRF` ⇒ `(L−1)`-multiplicity `≤ 2`) | **Proven** | §3 |
| Lemma M (nontrivial single-cycle involution product ⇒ crossing) | **Proven** | §4; exhaustive `n ≤ 8` (check A) |
| **Theorem Q, primitive form**: `P2 + primitive ⇒ L`-spectrum unique up to rotation | **Proven** | §5 |
| Corollary: primitive `P2` proportional spectra ⇒ `c=1`, rotation | **Proven** (uses cross-length Lemma/Theorem P of the population packet) | §5 |
| Non-primitive equal-length residual | **Open here**; finitely verified | §7, §8 |
| "Primitivity not needed" claim of the concurrent packet | **Not established by this proof** | §7 |
| No counterexample over the searched ranges | **Exact computation** | §8 |

---

## 10. Sources and repository anchors

| Item | Source / anchor |
|---|---|
| Circular genome, error-free uniform reads, cyclic-shift equivalence | Shomorony–Kim–Courtade–Tse, *Bioinformatics* 32(17):i494–i502, 2016; `docs/open-problem.md` |
| `P2`/`WEAK`, `TRF`, `ILF`; full-read reduction | `docs/issue48-intrinsic-admissibility-counterexample.md`; `docs/issue48-intrinsic-candidate-checks.md`; `mathematics/bridging-and-spectrum-uniqueness.md` (`I_s`-admissibility) |
| Repeat / triple-repeat / interleaved / maximality definitions | Bresler–Bresler–Tse, *BMC Bioinformatics* 14(Suppl 5):S18, 2013; `docs/bridging-source-semantics.md` |
| Exact `L`-spectrum dependence of the Medvedev–Brudno §6.1 objective | `docs/ml-formalization-contract.md` |
| Population packet (cross-length half + equal-length usage) | `docs/issue48-p2-population-proportional-identification.md` (branch `agent/p2-population-proportional-0921`); `docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md` (branch `agent/issue48-circqgram-source-0921`) |
| Verifier | `scripts/verify_circular_p2_spectrum_uniqueness.py` |
