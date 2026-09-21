# Bridging conditions and uniqueness of Eulerian reconstruction: combinatorial consequences

_Status: mathematical analysis with exact-rational/exhaustive computational evidence. Not a Lean result. Every claim is classified by epistemic class._

> **Addendum 2026-09-21 (source-fidelity resolution of Conjecture 4).** Conjecture 4 below is the `K = L−1` instance of the published **Bresler–Bresler–Tse 2013, Theorem 3** (`K`-mer graph from the `(K+1)`-spectrum; unique Eulerian cycle iff there is no triple or interleaved repeat of length `≥ K`), read with the same *maximal-repeat* / three-copy-maximality definitions that Shomorony et al. (2016) inherit (the definitions quoted in `docs/bridging-source-semantics.md`). Under those definitions `I_s`-admissibility at the full read set is literally "no triple or interleaved repeat of length `≥ K`, `K = L−1`", so the implication is a **source theorem**, not a conjecture. The `123 906`-instance exhaustive check and the randomized check (re-run 2026-09-21, `scripts/bridging_spectrum_uniqueness.py`, 0 ambiguous) are corroboration. Residual limits (circular Eulerian-cycle reading; condensed-graph nuance) and the exact citations are in `docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`. The converse remains false (`AAAAB`).

_Reproduction: `python3 scripts/bridging_spectrum_uniqueness.py` (checks A–D; exhaustive ranges plus randomized)._

_This note deliberately studies the **combinatorial** (candidate-identity) consequences of the bridging hypotheses **independently of the likelihood counterexamples**. It does not use or contest the existing Variant-E/Variant-F likelihood examples, and none of its conclusions depend on them._

---

## 0. Summary

The source-faithful condition `I_s` (Shomorony et al. 2016, Eq. (1), inherited from Bresler et al. 2013) is
**not** the condition "all repeats are bridged". It only controls *triple repeats* and *interleaved pairs*. The
consequences for candidate genomes are:

1. **The genuinely strong condition** `I_s^all` ("every maximal repeat occurrence pair is bridged") is
   *equivalent* to "no `(L−1)`-mer occurs twice" and forces every length-`L` window to occur at most once
   (Lemma 1).
2. **Source `I_s` is strictly weaker**: `S = AABAB` (`G = 5`, `L = 3`) satisfies `I_s` yet its length-`L`
   window `ABA` occurs twice (Proposition 2). So `I_s` neither bounds maximal-repeat length nor bounds
   `L`-mer multiplicity. This sharpens the correction in
   `docs/bridging-schemas-and-flow-feasibility-gaps.md` §2.
3. **The `L`-mer spectrum does not determine a genome**, with explicit repeat-free witnesses
   (`AABAC`/`AACAB`, `AABABB`/`AABBAB`, `AAABAAB`/`AAABBAAB`): equal spectrum, same length, not cyclic
   shifts (Proposition 3). Those witnesses are *not* `I_s`-admissible.
4. **Source theorem (Bresler–Bresler–Tse 2013, Thm 3 at `K = L−1`; formerly Conjecture 4):**
   `I_s`-admissibility *does* force the `L`-mer spectrum to determine the genome up to cyclic shift.
   Exhaustive check over `123 906` `I_s`-admissible primitive genomes in five parameter configurations,
   plus `1 655` randomized admissible genomes up to `G = 18`, found **zero** ambiguous spectra; this
   corroborates the source theorem (see the addendum at the head of this note).
5. **Candidate-class verdict:** bridging can imply uniqueness only for candidate classes that either
   (i) are the deterministic read-consistent class (source theorem), or (ii) restrict candidates to a fixed
   `L`-mer spectrum (Conjecture 4). It can never imply uniqueness for any class containing the tandem
   multiples `k · d_S`, `k ≥ 2`, by tandem invariance (Proposition 5).

The identity/uniqueness question is separate from the likelihood-maximizer question: the former is about the
fibres of `D ↦ d_D`, the latter about the objective `∏ d_D(w)^{x_w}`.

---

## 1. Definitions (source-faithful, exact assumptions)

Throughout, `Σ` is an alphabet, `S` a circular genome of length `G ≥ 1`, `L` a read length with `2 ≤ L ≤ G`,
and all indices are cyclic. Write `win_L(S, t) = S[t..t+L)` for the length-`L` window at start `t`, and

```
d_S(w) = #{ t ∈ Z_G : win_L(S,t) = w }        (the L-mer spectrum)
```

**Read set.** A *read set* `R` is a finite multiset of start positions `r ∈ Z_G` (the observed reads are then
the windows `win_L(S,r)`). The *full read set* is one read at every start.

**Bridging.** A length-`ℓ` occurrence at `t` is *bridged by* a read `r` iff, on an integer lift of the circle,
`r < t` and `t + ℓ < r + L`; i.e. the read strictly extends the occurrence on both sides.

**Maximal repeat pair.** Two distinct starts `t₁ ≠ t₂` with `win_ℓ(S,t₁) = win_ℓ(S,t₂)` such that the pair
cannot be extended on the left or on the right (the preceding symbols differ and the following symbols
differ). Degenerate fully-wrapping (periodic) pairs are not used as witnesses below.

**Triple repeat.** Three starts with equal length-`ℓ` windows whose preceding symbols are not all equal and
whose following symbols are not all equal (Bresler's three-copy maximality).

**Interleaved pair.** Two maximal repeat pairs with four distinct starts that alternate in cyclic order
(Bresler's `t₁ < t₂ < t₃ < t₄` up to rotation).

**`I_s`.** `R ∈ I_s` iff `R` covers `S`, every triple repeat of `S` is *all-bridged* (every selected copy is
bridged by `R`), and every interleaved pair is *bridged* (at least one constituent repeat is bridged). See
`docs/bridging-source-semantics.md:51-61`.

**Full-read reduction.** With the full read set, a length-`ℓ` copy is bridged iff `ℓ ≤ L − 2` (there is an
integer `r` with `r ≤ t−1` and `r+L ≥ t+ℓ+1` iff `ℓ ≤ L−2`). Hence

> `S` admits *some* `R ∈ I_s` (equivalently, the full read set lies in `I_s`) iff
> (i) every triple repeat has length `≤ L−2`, and
> (ii) every interleaved maximal-repeat pair has a constituent of length `≤ L−2`.

Call such `S` **`I_s`-admissible**. Because bridging is monotone in `R`, `I_s`-admissibility is the weakest
form of the hypothesis.

**Strong condition `I_s^all`.** Every maximal repeat occurrence pair of `S` is bridged.

---

## 2. Lemma 1 (`I_s^all` ⇔ read-length repetition-free)

**Lemma 1.** The following are equivalent:

1. every maximal repeat pair of `S` is bridged (with respect to the full read set);
2. every maximal repeat of `S` has length `≤ L − 2`;
3. no `(L−1)`-mer occurs twice in `S` (i.e. `d^{(L-1)}_S(u) ≤ 1` for all `u`).

In particular `d_S(w) ≤ 1` for every length-`L` window `w`.

**Proof.**
(1 ⇔ 2) A length-`ℓ` copy is bridgeable iff `ℓ ≤ L − 2` (§1). All copies of one maximal repeat share the same
length, so "the pair is bridged" ⇔ "its length is `≤ L−2`"; apply to every maximal repeat pair.

(2 ⇒ 3) If an `(L−1)`-mer `u` occurs at `t₁ ≠ t₂`, extend the two occurrences maximally to the right and then
to the left. The result is a maximal repeat pair (or a periodic pair) of length `≥ L−1`, contradicting (2).
(3 ⇒ 2) A maximal repeat of length `ℓ ≥ L−1` has its length-`(L−1)` prefix occurring at both copies, so its
`(L−1)`-mer occurs twice, contradicting (3).

The final assertion follows from (3) applied to the `(L−1)`-prefix of any repeated `L`-mer. ∎

_Epistemic class: mathematical proof._

**Remark.** Lemma 1 is the correct formalization of "all repeats being bridged". It is much stronger than the
source `I_s`, which is the next point.

---

## 3. Proposition 2 (source `I_s` is strictly weaker)

**Proposition 2.** There is a primitive `I_s`-admissible genome with a repeated length-`L` window.

**Witness.** `S = AABAB`, `G = 5`, `L = 3`, `Σ = {A,B}`:

```
windows      : AAB, ABA, BAB, ABA, BAA
spectrum     : {AAB:1, ABA:2, BAB:1, BAA:1}     so d_S(ABA) = 2
triple repeat: {A at starts 0,1,3} of length 1 ≤ L−2 = 1
max repeat   : ABA at starts {1,3} of length 3 = L  (unbridged, and not required to be)
interleaved  : none (the only maximal pairs {0,1} and {1,3} share a start)
```

By §1, the full read set lies in `I_s`, so `S` is `I_s`-admissible, yet `d_S(ABA) = 2`. The maximal repeat
`ABA` of length `L` is unbridged, and `I_s` does not require it to be bridged because it is neither a triple
repeat nor part of an interleaved pair.

A second, repeat-free-family witness is `ABCABD` (`G = 6`, `L = 3`), which is `I_s`-admissible while having
an unbridged maximal repeat `AB` of length `L−1 = 2`; this is the witness already used in
`docs/bridging-schemas-and-flow-feasibility-gaps.md` §2.

_Epistemic class: mathematical proof plus explicit verified witness._

**Consequences (corrections of earlier repository claims).**

| Earlier claim | Location | Status |
|---|---|---|
| `I_s` ⇒ every maximal repeat has length `≤ L−2` | `docs/bridging-consequences-lemmas.md:264`; `mathematics/bridging-combinatorial-implications-for-fixed-length.md:116` | **False**; only `I_s^all` gives this (Lemma 1) |
| `I_s` ⇒ `d_S(i) ≤ G−3` | `mathematics/bridging-combinatorial-implications-for-fixed-length.md:126` | **Not implied** by `I_s` |
| `I_s` forces a "spread-out" `L`-mer spectrum | `docs/bridging-consequences-analysis.md:210` | **Only under `I_s^all`**; `I_s` allows `d_S(w) ≥ 2` (Prop. 2) |

These earlier notes overstated what bridging controls. The corrected statement separates the all-bridged
condition (`I_s^all`) from the actual source condition (`I_s`).

---

## 4. Proposition 3 (the `L`-mer spectrum does not determine the genome)

**Proposition 3.** For each row below, the two circular genomes have the same length and the same `L`-mer
spectrum, are not cyclic shifts, and are `I_s`-inadmissible.

| `L` | `S₁` | `S₂` | `S₁` spectrum | inadmissibility witness |
|---|---|---|---|---|
| 2 | `AABAC` | `AACAB` | `{AA:1,AB:1,BA:1,AC:1,CA:1}` | triple repeat `A` at `{0,1,3}`, length 1 > L−2 = 0 |
| 3 | `AABABB` | `AABBAB` | `{AAB:1,ABA:1,BAB:1,ABB:1,BBA:1,BAA:1}` | interleaved pair `(1,3,ℓ=2)`,`(2,5,ℓ=2)`, both length > L−2 = 1 |
| 4 | `AAABAABB` | `AAABBAAB` | 8 distinct 4-mers | interleaved pair `(1,4,ℓ=3)`,`(3,7,ℓ=3)`, both length > L−2 = 2 |

The `L`-mer spectrum is the complete data of the exact-multinomial objective up to the observation-only
multinomial coefficient `n!/∏x_i!` (Medvedev–Brudno §6.1). Therefore, for any fixed-length exhaustive
candidate class, two genomes with the same spectrum receive **exactly the same likelihood for every sample**.
This is a likelihood-independent tie: no sample can distinguish them. In particular the `allMaximizersAreTruth`
schema fails for the spectrum candidate class, independently of the open conjecture below.

_Epistemic class: mathematical proof plus explicit verified witness._

---

## 5. Conjecture 4 (`I_s` ⇒ spectrum uniqueness)

**Conjecture 4.** If `S` is `I_s`-admissible, then any circular genome `D` of the same length `G` with the same
`L`-mer spectrum is a cyclic shift of `S`.

Equivalently: for `I_s`-admissible `S`, the fibre of `D ↦ d_D` through `d_S` is exactly the cyclic-shift class
of `S`.

**Computational evidence** (`scripts/bridging_spectrum_uniqueness.py`, check C/D):

| alphabet | `L` | `G` range | admissible primitive genomes | with ambiguous spectrum |
|---|---|---|---|---|
| `{A,B}` | 3 | 3–15 | 86 | 0 |
| `{A,B}` | 4 | 4–14 | 1 552 | 0 |
| `{A,B,C}` | 3 | 3–10 | 26 430 | 0 |
| `{A,B,C}` | 4 | 4–9 | 25 914 | 0 |
| `{A,B,C,D}` | 3 | 3–8 | 69 924 | 0 |
| **total** | | | **123 906** | **0** |

Randomized check: `1 655` admissible genomes over alphabets of size 4–5, lengths `8 ≤ G ≤ 18`, read lengths
`3 ≤ L ≤ 6`; zero with a second non-equivalent spectrum realization. (The randomized routine enumerates
Eulerian circuits of the de Bruijn multigraph, so it does not enumerate genomes.)

**Heuristic reduction.** A second genome with the same spectrum is a second Eulerian circuit of the de Bruijn
multigraph whose edges are the `L`-mers of `S` (with multiplicity). Two Eulerian circuits differ by switches
at vertices `v` (an `(L−1)`-mer) that have at least two distinct outgoing edges; a switch that genuinely
changes the cyclic sequence (rather than rotating two cycles sharing a single articulation vertex) yields two
distinct cycles that separate at one occurrence of `v` and rejoin at another. Those two occurrences of `v`
together with the differing right extensions give either a triple repeat (three occurrences of the maximal
repeat containing `v`) or an interleaved pair, with constituent lengths `≥ L−1`. `I_s` requires exactly those
structures to be bridged, i.e. to have length `≤ L−2` — a contradiction. This is the same mechanism as
Bresler et al.'s MultiBridging reconstruction theorem, applied to the de Bruijn graph instead of the
read-overlap graph. The reduction is not a proof: the cited step "an ambiguous circuit pair produces an
unbridged triple/interleaved structure" is precisely the unproved reverse direction.

**Converse is false.** `I_s`-inadmissibility does not imply an ambiguous spectrum; e.g. `AAAAB` (`G=5`,
`L=3`) is inadmissible (triple repeat `AA`, length 2 > L−2 = 1) but has a unique spectrum realization. So
Conjecture 4 is a sufficiency statement, not an equivalence.

_Epistemic class: **source theorem** (Bresler–Bresler–Tse 2013, Thm 3 at `K = L−1`) under the circular Eulerian-cycle reading, with exhaustive finite corroboration and the heuristic reduction as an independent intuition. See the addendum at the head of this note._

---

## 6. Candidate classes and what bridging can imply

Let `S` be `I_s`-admissible with true spectrum `d_S`. The relevant source-faithful candidate classes are:

| Class | Definition | Does `I_s` imply uniqueness (up to cyclic shift)? | Basis |
|---|---|---|---|
| `C_det(R)` | genomes compatible with the realized read collection `R` (the reconstruction class) | **Yes** | source theorem: Not-So-Greedy recovers `S` from `R` (Bresler/Shomorony) |
| `C_spec` | `{D : d_D = d_S}` (same `L`-mer spectrum) | **Yes, conjecturally** (Conjecture 4) | §5 evidence |
| `C_G` | all length-`G` circular genomes | **No** | `C_G` admits spectra `d_D ≠ d_S`; even a singleton `C_spec` fibre does not make `S` the unique maximizer, since the maximizer may lie on another fibre |
| `C_free` | all circular genomes, any length | **No** | tandem invariance: `d_{S^k} = k·d_S` gives an exact tie (`S^k ≠ S`, `|S^k| > |S|`) |
| `C_{flow}(R)` | per-occurrence flow-feasible genomes (Medvedev–Brudno §6.2) | **No** | `S^k ∈ C_{flow}(R)` ties `S` by tandem invariance |

The decisive structural fact is **tandem invariance** (proved in
`docs/bridging-schemas-and-flow-feasibility-gaps.md`, Prop. A): for every genome `D`, every `k ≥ 1`, and every
sample, the exact multinomial likelihood satisfies `L_exact(D^k | x) = L_exact(D | x)`. Hence **any candidate
class closed under `D ↦ D^k`, `k ≥ 2`, violates the `allMaximizersAreTruth` schema with no bridging hypothesis
at all.** Therefore:

> Bridging can imply uniqueness only for candidate classes that do **not** contain the tandem multiples
> `k·d_S`, i.e. essentially classes that fix the spectrum (`C_spec`) or that are defined by read-consistency
> (`C_det`).

For the actual ML question, this limits the positive role of bridging to: *if the ML maximizer's spectrum
equals `d_S`, then under Conjecture 4 the maximizing sequence is `S` up to shift.* Bridging does not by itself
put `d_S` at the top of the objective (that is the separate, already-refuted-in-general maximality question).

_Epistemic class: definitions plus the cited source theorem and Prop. A (tandem invariance); the `C_spec` row
is Conjecture 4._

---

## 7. Dead ends preserved

Recorded so they are not re-attempted as if open:

1. **"Bridging bounds repeat length."** False for source `I_s` (Prop. 2). Only `I_s^all` bounds maximal-repeat
   length (Lemma 1). Any future argument must state which condition it uses.
2. **"Bridging forces a spread-out spectrum, hence cannot help ML."** Only true for `I_s^all`; source `I_s`
   permits a repeated `L`-mer (`AABAB`), so this route does not refute the source hypothesis.
3. **"Variant F singleton theorem."** False as stated (needs `S ∈ F_flow(R)`, i.e. tiling); see
   `docs/bridging-schemas-and-flow-feasibility-gaps.md` §3. This note's `C_spec` conjecture does not repair
   that theorem; it is a different object.
4. **"Repeated reads let a flow-feasible competitor strictly beat the truth."** Overstated for the
   variable-length exact objective: the natural amplified candidate is a tandem `S^k`, which ties. See the
   same note §3 and Prop. A.
5. **"`I_s` ⇔ spectrum uniqueness."** False as an equivalence; `AAAAB` is a counterexample to the converse
   (inadmissible, yet spectrum-unique). Only sufficiency (Conjecture 4) is supported.

---

## 8. What a proof of Conjecture 4 would need

A self-contained proof would establish: if a circular genome `S` has two distinct-occurrence length-`(L−1)`
windows with different right extensions, or a triple repeat of length `≥ L−1`, or an interleaved pair with
both lengths `≥ L−1`, then the de Bruijn multigraph of `S` has two Eulerian circuits giving non-equivalent
genomes. This is a purely graph-theoretic statement about Eulerian circuits and is a plausible Lean target
once isolated; it is *not* needed for the likelihood branch and is stated here as a bounded research packet.

---

## 9. Source citations

| Fact | Source | Repository anchor |
|---|---|---|
| `I_s` definition (coverage, all-bridged triple, bridged interleaved) | Shomorony et al. 2016 Eq. (1); Bresler et al. 2013 | `docs/bridging-source-semantics.md:51-61` |
| Bridging = strict extension on both sides | Bresler et al. 2013; Shomorony et al. §3/Fig. 6 | `docs/bridging-source-semantics.md:20-28` |
| Maximal repeat / triple-repeat maximality | Bresler et al. 2013 | `docs/bridging-source-semantics.md:12-16` |
| Interleaving as cyclic alternation | Bresler et al. 2013 | `docs/bridging-source-semantics.md:38-41` |
| Exact multinomial objective `∝ ∏ d_D(w)^{x_w}` | Medvedev–Brudno §6.1 | `docs/source-notes/ml-objective-candidate-class-resolution.md:98-140` |
| Deterministic reconstruction under `I_s` (Not-So-Greedy) | Shomorony et al. 2016 §3 | `docs/open-problem.md:24` |
| Tandem invariance | proved in repository | `docs/bridging-schemas-and-flow-feasibility-gaps.md:24-64` |
| Prior repeat-length correction | repository | `docs/bridging-schemas-and-flow-feasibility-gaps.md:73-122` |

## 10. Epistemic summary

| Claim | Status | Evidence |
|---|---|---|
| Lemma 1: `I_s^all` ⇔ no `(L−1)`-mer repeats ⇒ no `L`-mer repeats | **Proven** | maximal-extension argument |
| Prop. 2: source `I_s` permits repeated `L`-mers | **Proven** | witness `AABAB`, script check A |
| Prop. 3: spectra do not determine genomes | **Proven** | explicit pairs, script check B |
| Conjecture 4 (now BBT Thm 3 at `K=L−1`): `I_s` ⇒ spectrum determines genome | **Source theorem** (circular reading) | Bresler–Bresler–Tse 2013 Thm 3; 123 906 exhaustive + 1 655 random corroboration |
| Converse of Conjecture 4 | **Refuted** | `AAAAB` |
| `C_det` uniqueness under `I_s` | **Source theorem** | Bresler/Shomorony |
| `C_free`/`C_{flow}` uniqueness fails | **Proven** | tandem invariance |
