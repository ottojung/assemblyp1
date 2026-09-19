# Bridging conditions and the two ML schemas: scale invariance, repeat-length corrections, and Variant F gaps

_Status: mathematical analysis with exact-rational computational checks. Not a Lean result. All claims are classified by epistemic class and stated with their assumptions._

_Reproduction: `python3 scripts/bridging_schema_checks.py` (all four checks pass; exact rational arithmetic)._

This note records four independent findings about what the source-faithful bridging
hypotheses `I_s` (Shomorony et al. 2016, Eq. (1); inherited from Bresler et al. 2013)
do and do not imply for maximum-likelihood assembly. Two are positive structural
facts, two correct claims currently made elsewhere in the repository.

Terminology follows the repository's existing one:

- `L` = read length; `G` = true circular genome length; `x` = observed read-type counts;
- `d_D(w)` = number of length-`L` circular windows of candidate `D` equal to type `w`;
- exact multinomial ordering (`Variant E`, Medvedev–Brudno §6.1) uses
  `L_exact(D | x) ∝ ∏_w (d_D(w) / |D|)^{x_w}`;
- the two conclusion schemas are `truthIsML` (truth is a maximizer) and
  `allMaximizersAreTruth` (uniqueness up to genome equivalence);
- `I_s` = coverage ∧ all-bridged triple repeats ∧ bridged interleaved pairs.

---

## 1. Finding A (new): the exact multinomial is invariant under tandem repetition, so Variant E never forces uniqueness

**Proposition A (tandem-repetition invariance).**
Let `D` be a nonempty circular genome of length `M`, and for `k ≥ 1` let `D^k`
denote its `k`-fold tandem repetition, i.e. the length-`kM` circular genome
`(D^k)_t = D_{t mod M}`. For every read length `L` and every read-type count
vector `x`, the exact multinomial likelihood satisfies

```
L_exact(D^k | x) = L_exact(D | x).
```

**Proof.** Because `D^k` is `M`-periodic, for every start `t ∈ [0, kM)` the
length-`L` circular window of `D^k` at `t` equals the window of `D` at
`t mod M` (indices agree modulo `M`). Hence each window type `w` satisfies
`d_{D^k}(w) = k · d_D(w)`, and `|D^k| = kM`. Therefore
`d_{D^k}(w)/|D^k| = d_D(w)/M` for every `w`, and the observation-only
multinomial coefficient is unchanged. ∎

**Corollary A1 (uniqueness fails for variable-length exact ML, for every truth).**
Under Variant E with the candidate universe of *all nonempty circular genomes*,
for every truth `S` and every observation `x`, the candidate `S^k` satisfies
`L_exact(S^k | x) = L_exact(S | x)` for all `k ≥ 1`. For `k ≥ 2`, `|S^k| = k|S|`,
so `S^k` is not a cyclic shift of `S`. Consequently:

1. `S` is never the unique maximizer up to cyclic shift;
2. when `S` is a maximizer, the maximizer set is infinite (closed under tandem
   repetition).

This holds with **no bridging hypothesis at all** and for every read sample. It is
therefore a structural obstruction to the `allMaximizersAreTruth` schema under the
literal §6.1 exact objective, independent of the repeat-bridging question.

**Corollary A2 (fixed length is what excludes the tie).** If candidates are
restricted to length `G` (the fixed-length sub-problem), tandem repetitions are not
admissible and Corollary A1 does not apply. Fixed-length uniqueness can hold
(e.g. repeat-free `S` with the complete spectrum observed, §4); fixed-length
*maximizer* status can still fail (kernel-checked in
`AssemblyP1/FixedLengthExactCounterexample.lean`).

_Epistemic class: mathematical proof._

**Remark (source scope).** Corollary A1 does not require `I_s`; it is a property
of the Medvedev–Brudno exact objective itself. It shows the exact likelihood is
scale-invariant and therefore does not identify a genome's length from the read
distribution alone.

---

## 2. Finding B (correction): `I_s` does **not** bound maximal repeat length

Several repository notes state, as a consequence of `I_s`:

> every maximal repeat in `S` has length `l ≤ L − 2`,

and derive further bounds on `d_S` from it. Concretely:

- `docs/bridging-consequences-lemmas.md:264` (Lemma, "Bridging bounds repeat length");
- `docs/bridging-consequences-analysis.md:79`;
- `mathematics/bridging-combinatorial-implications-for-fixed-length.md:33,116`;
- `mathematics/deterministic-vs-likelihood-separation.md:125`.

**Proposition B (correct repeat-length content of `I_s`).** Under `I_s`:

1. every **triple repeat** has length `l ≤ L − 2` (each of its copies must be
   bridged, and no read of length `L` can bridge a copy of length `l ≥ L − 1`);
2. every **interleaved repeat pair** has at least one constituent repeat of length
   `l ≤ L − 2` (a bridged pair needs at least one bridgeable constituent);
3. there is **no** bound on the length of a maximal repeat that is neither a triple
   repeat nor part of an interleaved pair.

**Witness.** `S = ABCABD` (`G = 6`), `L = 3`, `R` = the six reads at all six start
positions. Then:

- coverage holds; `S` is repeat-free for length-`3` windows;
- `S` has exactly one maximal repeat pair, `"AB"` at positions `0` and `3`, of
  length `2 = L − 1`, and it is **not** bridged (positions `5` and `2` cannot lie
  in one length-`3` read);
- `S` has no triple repeat and no interleaved pair, so no clause of `I_s` requires
  this copy to be bridged;
- hence `I_s` holds while the maximal repeat length is `L − 1 > L − 2`.

The check is reproduced by `scripts/bridging_schema_checks.py` (check B).

**Consequences.**

- The claimed bound `d_S(i) ≤ G − 3` (`mathematics/bridging-combinatorial-implications-for-fixed-length.md:126`,
  `mathematics/bridging-consequences-lemmas.md:98-103`) does not follow from `I_s`;
  it is at best a bound on the repeat multiplicity contributed by triple/interleaved
  structure.
- Arguments that rely on `I_s` forcing a "spread-out" spectrum must be restated:
  `I_s` constrains the length only of *triple* and *interleaved* repeats, not of
  isolated pairwise repeats.

This correction does not affect the repository's negative counterexamples, which use
either repeat-free truths or an all-bridged triple repeat
(`AAABB`), i.e. exactly the repeat structure that `I_s` does control.

_Epistemic class: mathematical proof plus explicit computational witness._

---

## 3. Finding C (correction): the Variant F "singleton theorem" is false as stated

`docs/bridging-flow-feasibility-lemma.md` Theorem 1 (and its duplicate
`variant-f-bridge-constraint-analysis.md` Theorem 1) asserts:

> Let `S` be repeat-free with `L ≥ 3` and let `R` satisfy `I_s` (reducing to
> coverage) with all reads distinct. Then the overlap graph `G(R)` is a directed
> cycle and `F_flow(R) = {S}`.

**Proposition C (the missing hypothesis).** The claim is false; the correct
hypothesis is that `R` *tiles* `S`, i.e. that the realized reads can appear, with
overlaps, in a single closed walk spelling `S`. Coverage does not imply this.

**Witness.** `S = ACGTG` (`G = 5`), `L = 3`, starts `{0, 1, 3}`, so the reads are
`ACG`, `CGT`, `TGA`. They are distinct `L`-mer types from distinct starts, the
truth is repeat-free, and the reads cover all five positions. In the overlap graph
(`u → v` iff `u[1:] = v[:-1]`):

```
ACG → CGT,   and TGA has no incoming or outgoing edge.
```

Thus `TGA` is isolated; no closed walk visits every read occurrence, so `F_flow(R)`
is empty (in particular `S ∉ F_flow(R)`). The proof's step 3 assumes that reads at
consecutive start positions are both present, which coverage does not guarantee.
The check is reproduced by `scripts/bridging_schema_checks.py` (check C).

**Consequences.**

1. The advertised "only positive anchor" for Variant F does not exist as stated;
   any positive Variant F result must add the tiling hypothesis `S ∈ F_flow(R)`
   (or an equivalent).
2. Once that hypothesis is added, an over-sampling obstruction appears: see
   Proposition D below. For repeat-free `S`, `S ∈ F_flow(R)` forces `R` to be
   exactly one copy of each window; any repeated read makes the truth itself
   infeasible, and then "is the ML sequence the true sequence?" is ill-posed.
3. The companion "amplification obstacle" (repeated reads yield a flow-feasible
   competitor that *strictly* beats the truth) is also overstated for the
   variable-length exact objective: the natural flow-feasible amplification of the
   truth is the tandem `S^k`, which by Proposition A **ties** the truth rather than
   beating it.

_Epistemic class: mathematical proof plus explicit computational witness._

---

## 4. Finding D (new positive partial result): repeat-free Variant F with the truth feasible makes the truth an exact maximizer, but not unique

To make Variant F precise, use the following **modeling decision** (stated
explicitly, since the repository's versions differ and the Medvedev–Brudno §6.2
object is not literally a circular-genome likelihood):

> **Per-occurrence flow candidate set `F*(R)`.** A circular genome `D` is
> flow-feasible for a read multiset `R` iff every length-`L` window of `D` occurs
> as a read type in `R`, and `d_D(w) ≥ x_w` for every type `w` (each observed read
> occurrence is visited at least once). `F*(R)` is the set of such `D`.

This is the candidate set induced by the lower-bound-one-per-read-vertex reading of
Medvedev–Brudno §6.2. Under the alternative "distinct read types only" reading the
condition `d_D(w) ≥ x_w` is replaced by `supp(D) = supp(R)`; the two definitions
agree when every observed count is `1`, which is exactly the repeat-free
full-spectrum case of Proposition D, so the proposition is unaffected by that
choice.

**Proposition D (repeat-free flow-feasible ML).** Let `S` be repeat-free (all `G`
length-`L` windows distinct) and suppose `S ∈ F*(R)`. Then:

1. `x_w ∈ {0, 1}` for every `w`, and `x_w = 1` for every window `w` of `S`;
   equivalently `R` is exactly one copy of each of the `G` windows of `S`.
2. For every `D ∈ F*(R)`, `L_exact(D | x) ≤ L_exact(S | x)`. Hence `S` is an
   exact ML maximizer.
3. `D ∈ F*(R)` ties with `S` if and only if `|D| = kG` and `d_D(w) = k` for all
   `w ∈ supp(S)`, i.e. `d_D = k · d_S`. Such `D` exist for every `k ≥ 1` (for
   instance `S^k`).

**Proof.** `S ∈ F*` requires `supp(S) ⊆ supp(R)` and `d_S(w) = 1 ≥ x_w`, so
`x_w ≤ 1`; since every read is a window of `S`, `supp(R) ⊆ supp(S)`, so
`supp(R) = supp(S)` and `x_w = 1` on it. This is (1).
For (2): any `D ∈ F*` has `supp(D) ⊆ supp(R) = supp(S)` and `d_D(w) ≥ 1` for all
`w ∈ supp(S)`. Let `M = |D| = Σ_{w ∈ supp(S)} d_D(w)`. By AM–GM,
`∏_{w} d_D(w) ≤ (M/G)^G`, with equality iff all `d_D(w) = M/G`. Therefore

```
L_exact(D|x) = ∏_w (d_D(w)/M)^{x_w} = ∏_w d_D(w) / M^G
             ≤ (M/G)^G / M^G = 1/G^G = L_exact(S|x).
```

For (3): equality holds iff `d_D(w) = M/G` for all `w ∈ supp(S)`, so `k := M/G` is
a positive integer and `d_D = k·d_S`; conversely a candidate with `d_D = k·d_S` has
all windows in `supp(S) = supp(R)` and `d_D(w) = k ≥ 1 = x_w`, hence lies in
`F*(R)` and ties. ∎

**Computational corroboration.** For `S = AABB`, `L = 2`, with one copy of each
window observed (`AA`, `AB`, `BB`, `BA`), exhaustive enumeration of candidates up
to length `12` shows `max L_exact = L_exact(S) = 1/256`, with the maximizer set
exactly the genomes whose spectrum is `k · d_S` (`k = 1, 2, 3`); see
`scripts/bridging_schema_checks.py` (check D).

**Interpretation.** Under `F*`, the repeat-free ML question has a clean answer for
the `truthIsML` schema (yes, conditionally on `S ∈ F*(R)`) but not for the
`allMaximizersAreTruth` schema (no, by the `k·d_S` tie class, consistent with
Proposition A). The hypothesis `S ∈ F*(R)` is strong: it fails whenever any read
type is sampled more often than it occurs in `S`, which happens with positive
probability under i.i.d. sampling. Hence Variant F is a positive-result route only
in the (atypical) full-spectrum, no-oversampling regime.

_Epistemic class: mathematical proof (conditional on the stated `F*` model) plus
computational corroboration._

---

## 5. What this changes, and what remains open

| Claim | Previous repository status | Status after this note |
|-------|---------------------------|------------------------|
| `I_s` ⇒ every maximal repeat has length ≤ L−2 | Asserted in several notes | **Corrected (false as stated)** — holds only for triple/interleaved structure (Prop. B) |
| Variant F singleton theorem | Advertised positive anchor | **Corrected (false as stated)** — needs `S ∈ F_flow(R)` (Prop. C) |
| Amplification over repeated reads strictly beats truth | Asserted (`docs/bridging-flow-feasibility-lemma.md:134-141`; `mathematics/bridging-combinatorial-implications-for-fixed-length.md:188-192`) | **Overstated** — the flow-feasible amplified candidate is `S^k`, which ties (Prop. A) |
| Uniqueness under variable-length exact ML | Open/implicit | **Refuted for all truths and samples** by tandem invariance (Prop. A) |
| Repeat-free Variant F ⇒ truth is a maximizer | Open | **Proved conditionally** on `S ∈ F*(R)`; ties are `k·d_S` (Prop. D) |
| Fixed-length Variant E | Refuted (kernel-checked) | Unchanged |
| Unrestricted exact Variant E (`truthIsML`) | Refuted (kernel-checked) | Unchanged |
| `I_s` ⇒ deterministic uniqueness of reconstruction | Source result (Bresler) | Unchanged; consistent with the exhaustive check that no `I_s`-satisfying truth in the tested range has a non-equivalent same-length spectrum realization |

**Open questions.**

1. Does Proposition D extend from repeat-free `S` to truths with bridged repeats,
   under `F*`? The tie/AM–GM argument uses `d_S(w) = 1` and `supp(S) = supp(R)`;
   with repeats, `x_w ≥ 1` is not forced and the constraint set is richer.
2. Can the per-occurrence (`F*`) and support-only readings of Medvedev–Brudno §6.2
   be separated from the primary source? The candidate sets differ, and the
   answer to the Variant F question can depend on which is intended.
3. Does the published open problem intend a candidate universe that makes the
   truth flow-feasible at all? If not, Variant F is not a well-posed reading of
   "the maximum-likelihood sequence is the true sequence."

## 6. Cross-references

| Fact | Repository anchor |
|------|-------------------|
| `I_s` definition | `docs/bridging-source-semantics.md:53-61` |
| Exact multinomial, candidate-dependent length | `docs/source-notes/medvedev-brudno-candidate-class.md:16-44` |
| §6.2 flow object is not a circular-genome likelihood | `docs/source-notes/medvedev-brudno-candidate-class.md:71-94` |
| Two conclusion schemas | `docs/literature/ml-tie-semantics.md:33-40`; `AssemblyP1/Model.lean:25-50` |
| Kernel-checked fixed-length counterexample | `AssemblyP1/FixedLengthExactCounterexample.lean` |
| Kernel-checked unrestricted-length counterexample | `AssemblyP1/ExactVariantECounterexample.lean` |
| Repeat-length claim being corrected | `docs/bridging-consequences-lemmas.md:264`; `mathematics/bridging-combinatorial-implications-for-fixed-length.md:126` |
| Singleton theorem being corrected | `docs/bridging-flow-feasibility-lemma.md` §2; `docs/variant-f-bridge-constraint-analysis.md` §3 |
| Reproducible checks | `scripts/bridging_schema_checks.py` |
