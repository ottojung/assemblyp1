# Circular `q`-gram identifiability and the `L−1`/`L−2` threshold

_Status: source-fidelity note, 2026-09-21. It pins the exact primary statement of the
circular `q`-gram identifiability criterion and the exact threshold at which it meets the
Shomorony et al. (2016) bridging hypothesis `I_s`; it then resolves the previously
"unpinned" `P2`/`WEAK` ⇒ spectrum-uniqueness step by identifying it as the `K = L−1`
instance of a published theorem (Bresler–Bresler–Tse 2013, Theorem 3) under the same
maximal-repeat definitions Shomorony et al. inherit. It makes **no** claim about the
statistical finite-sample open question of `docs/open-problem.md`._

_All sources used are English-language primary literature. This note deliberately does
**not** rely on any Russian-language statement or translation; the accepted English
statements of Ukkonen (1992), Pevzner (1995), and Bresler–Bresler–Tse (2013) are
sufficient and are quoted below. Where a claim is our reconciliation it is labelled
**analysis**._

---

## 0. Direct answer

Two thresholds coincide, and this coincidence is the whole content of the bridge:

1. **Obstruction threshold.** The classical Ukkonen–Pevzner SBH characterization, in the
   accepted restatement of Bresler–Bresler–Tse (2013, Theorem 3; `K`-mer graph, `K = L−1`),
   says the length-`L` spectrum determines the genome up to an Eulerian cycle **iff** there
   is no triple repeat or interleaved pair of maximal repeats of length at least `K`. With
   `K = L−1`, the obstructing length is `ℓ ≥ L−1`.

2. **Bridging threshold.** A length-`ℓ` copy is *bridgeable* by a length-`L` read on the
   full read set iff `ℓ ≤ L−2` (strict two-sided extension). Equivalently, a copy is
   **unbridgeable** iff `ℓ ≥ L−1`.

Hence `I_s`'s full-read shadow `WEAK` (repository notation; also written `P2`) — "no
Bresler triple repeat of length `≥ L−1`, and no interleaved pair of maximal repeats with
both constituents of length `≥ L−1`" — is **literally** Bresler–Bresler–Tse's "no triple
or interleaved repeats of length at least `K`, `K = L−1`". Therefore the inference

> `P2`/`WEAK`(`S,L`) ⇒ the `L`-mer spectrum determines `S` up to cyclic shift

is a **published theorem**, not an unpinned conjecture, provided the circular
Eulerian-cycle reading is accepted. The repository's Conjecture 4
(`mathematics/bridging-and-spectrum-uniqueness.md` §5) should be reclassified from
"conjecture" to "instance of Bresler–Bresler–Tse 2013, Theorem 3 (`K = L−1`)". The
earlier caution in
`docs/literature/substring-spectrum-identifiability-2026-09-20.md` ("needs an explicit
circular-statement check") is discharged by the published Theorem 3.

What is **not** resolved here: the finite random-sample ML question. Spectrum
identifiability controls fibres of the spectrum map; it does not put `d_S` on top of the
finite-sample objective (see `docs/literature-status.md` §7 and the finite-section notes).

---

## 1. Primary sources and their exact statements

### 1.1 Bresler–Bresler–Tse 2013 (the accepted maximal-repeat restatement)

G. Bresler, M. Bresler, D. Tse, "Optimal assembly for high throughput shotgun
sequencing," *BMC Bioinformatics* 14(Suppl 5):S18, 2013.
DOI <https://doi.org/10.1186/1471-2105-14-S5-S18>; PMC3706340; arXiv:1301.0068.

**Definitions (verbatim, "Ukkonen's condition" paragraph).**

> "A *repeat* of length `ℓ` is a subsequence appearing twice, at some positions
> `t₁, t₂` (so `s^ℓ_{t₁} = s^ℓ_{t₂}`) that is maximal (i.e. `s(t₁ − 1) ≠ s(t₂ − 1)` and
> `s(t₁ + ℓ) ≠ s(t₂ + ℓ)`). Similarly, a *triple repeat* of length `ℓ` is a subsequence
> appearing three times, at positions `t₁, t₂, t₃`, such that `s^ℓ_{t₁} = s^ℓ_{t₂} = s^ℓ_{t₃}`,
> and such that neither of `s(t₁ − 1) = s(t₂ − 1) = s(t₃ − 1)` nor
> `s(t₁ + ℓ) = s(t₂ + ℓ) = s(t₃ + ℓ)` holds."

> "A pair of repeats, one at positions `t₁, t₃` with `t₁ < t₃` and the second at positions
> `t₂, t₄` with `t₂ < t₄`, is *interleaved* if `t₁ < t₂ < t₃ < t₄` or
> `t₂ < t₁ < t₄ < t₃`. The length of a pair of interleaved repeats is defined to be the
> length of the shorter of the two repeats."

**Ukkonen's condition (verbatim).**

> "if there are *interleaved repeats* or *triple repeats* in the sequence of length at
> least `L − 1`, then the likelihood of observing the reads is the same for more than one
> possible DNA sequence and hence correct reconstruction is not possible."

> "Ukkonen's condition implies a lower bound on the read length,
> `L > L_crit := max{ℓ_interleaved, ℓ_triple} + 1`."

**Theorem 1 (necessity, general reads; verbatim).**

> "Given a DNA sequence `s` and a set of reads, if there is a pair of interleaved repeats
> or a triple repeat whose copies are all unbridged, then there is another sequence `s'` of
> the same length under which the likelihood of observing the reads is the same."

**Theorem 3 (sufficiency from the spectrum; verbatim).**

> "Let `G₀` be the `K`-mer graph constructed from the `(K + 1)`-spectrum `S_{K+1}` of `s`,
> and let `G` be the condensed sequence graph obtained from `G₀`. If Ukkonen's condition is
> satisfied, i.e. there are no triple or interleaved repeats of length at least `K`, then
> there is a unique Eulerian cycle `C` in `G` and `C` corresponds to `s`."

**Bridging threshold (verbatim, Fig. 5 caption).**

> "A subsequence `s^ℓ_t` is bridged if and only if there exists at least one read which
> covers at least one base on both sides of the subsequence, i.e. the read arrives in the
> preceding length `L − ℓ − 1` interval."

Theorem 3 is stated with `K` arbitrary; the SBH/dense identification of interest is
`K+1 = L`, i.e. **`K = L−1`**, because the `(K+1)`-spectrum is then exactly the `L`-mer
spectrum of `docs/literature-status.md` §7. The same paper adds the converse in the SBH
setting in the arXiv v3 (its "Background" subsection): with `K = L−1` and edge
multiplicities known, the `K`-mer graph has a unique Eulerian cycle **iff** there are no
unbridged interleaved repeats or unbridged triple repeats. (The published BMC text states
the forward direction as Theorem 3; the converse is the classical Pevzner statement it
cites.)

### 1.2 Ukkonen 1992 and Pevzner 1995 (the classical lineage)

- E. Ukkonen, "Approximate string-matching with `q`-grams and maximal matches,"
  *Theoretical Computer Science* 92(1):191–211, 1992.
  DOI <https://doi.org/10.1016/0304-3975(92)90143-4>. Introduces the `q`-gram profile and
  conjectures the transformation characterization of sequences with equal `q`-gram
  profile.
- P. A. Pevzner, "DNA physical mapping and alternating Eulerian cycles in colored graphs,"
  *Algorithmica* 13(1–2):77–105, 1995. DOI <https://doi.org/10.1007/BF01188582>. Proves
  the characterization and, for Sequencing by Hybridization, an algorithm matching
  Ukkonen's condition; this is the "optimal algorithm matching Ukkonen's condition"
  cited as [18] by Bresler–Bresler–Tse.

Bresler–Bresler–Tse describe their result as "the shotgun sequencing analogue of
Ukkonen–Pevzner's necessary and sufficient conditions for Sequencing by Hybridization."
For source fidelity we anchor the *circular, maximal-repeat* form on the accepted
Bresler–Bresler–Tse statement, and record Ukkonen/Pevzner as the origin (their own
formulation is the linear SBH one).

### 1.3 Çelikkanat–Masegosa–Nielsen 2024 (a *different* restatement — not the anchor)

A. Çelikkanat, A. R. Masegosa, T. D. Nielsen, "Revisiting K-mer Profile for Effective and
Scalable Genome Representation Learning," NeurIPS 2024; arXiv:2411.02125.

Their Theorem 3.1 characterizes when a **linear** read `r` of length `ℓ` is the unique
sequence with its `k`-mer profile, via three conditions. Conditions (2) and (3) are stated
on raw `(k−1)`-mer **occurrences** with explicit disequality clauses; condition (1) is a
linear prefix–suffix boundary condition.

**Analysis (convention mismatch).** Çelikkanat et al.'s conditions are (i) *linear* — their
condition (1) has no circular analogue — and (ii) phrased on *arbitrary* `(k−1)`-mer
occurrences, not on the *maximal* repeats that Bresler–Bresler–Tse and Shomorony et al.
use. The two restatements do share the obstruction threshold `k−1 = L−1`, but they are not
interchangeable predicates. The repository's earlier reconciliation
(`docs/literature/substring-spectrum-identifiability-2026-09-20.md`) anchored on
Çelikkanat et al.; that is the procedural origin of the "unpinned" feel. The correct
anchor for the repository's maximal-repeat `I_s`/`WEAK` is Bresler–Bresler–Tse Theorem 3.

### 1.4 Ota–Manada 2023 (a circular-specific, but different, criterion)

T. Ota, A. Manada, "A Reconstruction of Circular Binary String Using Substrings and
Minimal Absent Words," *IEICE Trans. Fundamentals* E107.A(3), 2024 (presented ISITA 2022).
DOI <https://doi.org/10.1587/transfun.2023TAP0015>.

This gives a necessary and sufficient condition for reconstructing a **given** circular
**binary** string from substrings of length `k` *with frequencies* plus minimal absent
words, via a weighted-automaton condition (their Theorem 1). It is a distinct, more
compression-oriented criterion (it can use `k` shorter than the classical obstruction
threshold) and is restricted to binary alphabets; it is recorded here as the closest
circular-specific primary treatment located, but it is **not** the criterion the
repository's `I_s` instantiation needs.

---

## 2. The `L−1`/`L−2` threshold, both sides

**Bridgeability lemma (full read set; mathematical proof).** For a circular genome and
reads of length `L`, a length-`ℓ` occurrence `[t, t+ℓ)` (on an integer lift) is bridged by
some read iff `ℓ ≤ L−2`.

*Proof.* A read is an interval `[r, r+L)`. It bridges `[t, t+ℓ)` iff `r < t` and
`t+ℓ < r+L`. Such an integer `r` exists iff `t+ℓ+1−L ≤ t−1`, i.e. `ℓ+2 ≤ L`, i.e.
`ℓ ≤ L−2`. ∎

This reproduces Bresler–Bresler–Tse's Fig. 5 caption ("the read arrives in the preceding
length `L−ℓ−1` interval": a nonempty interval requires `L−ℓ−1 ≥ 1`). Combining with
§1.1:

| length `ℓ` of a repeat copy | bridgeable at full read set? | Ukkonen obstruction (with `K = L−1`)? |
|---|---|---|
| `ℓ ≤ L−2` | yes | no |
| `ℓ ≥ L−1` | no | yes |

So "unbridgeable" and "Ukkonen-obstructing" are the **same length condition**, seen from
the two sides. Bresler–Bresler–Tse state it directly: "repeats of length at least `L−1`
(these are always unbridged)."

**Off-by-one vigilance (analysis).** Secondary expositions occasionally invert this. A
widely used course note states Pevzner's theorem as "if `L > max(ℓ_interleaved, ℓ_triple)`
then the de Bruijn graph has a unique Eulerian path," but its own worked examples put an
interleaved/triple repeat of length `L−1` in the ambiguous case and call the condition
`L−1 > ℓ_interleaved`. The consistent, source-supported statement is the
Bresler–Bresler–Tse one: `L > max{ℓ_interleaved, ℓ_triple} + 1`, i.e. safety iff
`ℓ ≤ L−2`. We record this explicitly because an `L−1`-vs-`L−2` slip would silently change
`WEAK` and hence Conjecture 4.

---

## 3. `P2`/`WEAK` is Ukkonen's condition at `K = L−1` (resolution)

Repository notation (as in `docs/synthesis-finite-rows-and-repairs-2026-09-21.md` §1 and
`docs/population-identifiability-intrinsic-genomes.md` §1):

- `TRF(D,L)`: no Bresler triple repeat of `D` has length `≥ L−1`.
- `ILF(D,L)`: no interleaved maximal-repeat pair of `D` has both constituents of length
  `≥ L−1`.
- `WEAK(D,L) = TRF ∧ ILF` (also written `P2`).
- `I_s`-admissibility of the truth = `WEAK(S,L)` at the full read set (repository
  full-read reduction, `mathematics/bridging-and-spectrum-uniqueness.md` §1).

**Proposition (analysis; definitional identity).** `WEAK(D,L)` holds **iff** `D` has no
triple repeat or interleaved pair of maximal repeats of length at least `K = L−1` in the
sense of Bresler–Bresler–Tse §1.1.

*Proof.* `TRF` is exactly the negation of "there is a triple repeat of length `≥ L−1`"
under the identical three-copy maximality definition. `ILF` says no interleaved pair has
*both* maximal repeats of length `≥ L−1`; Bresler–Bresler–Tse define the pair's length to
be the shorter constituent, so "interleaved repeats of length at least `K`" means the
shorter `≥ K`, i.e. both `≥ K`. These are the same condition. ∎

**Consequence (source theorem, given the circular reading).** Substituting `K = L−1` into
Bresler–Bresler–Tse Theorem 3: if `WEAK(S,L)` holds, then the `(L−1)`-mer graph built from
the `L`-spectrum has a unique Eulerian cycle, which spells `S`. Hence any circular genome
of the same length with the same `L`-mer multiset is a cyclic shift of `S`. This is the
repository's **Conjecture 4**, now a published theorem instance.

Therefore the previously conditional step in
`docs/population-identifiability-intrinsic-genomes.md` §5 ("Claim (conditional on the
classical circular characterization)") can be stated unconditionally for the
maximal-repeat predicate `WEAK`, and the `P2 ⇒ spectrum-uniqueness` inference is
**resolved (source theorem)**.

### 3.1 What was actually unpinned, precisely

Not the mathematics of the obstruction, but the *convention bridge*: the repository had
been matching its Bresler-maximal-repeat predicate against Çelikkanat et al.'s
non-maximal linear predicate, and therefore could only claim a heuristic correspondence.
Matching it instead against Bresler–Bresler–Tse, whose repeat definitions Shomorony et al.
explicitly inherit (`docs/bridging-source-semantics.md`), makes the correspondence the
definitional identity above.

### 3.2 Residual limits (kept explicit)

1. **Circular reading.** Bresler–Bresler–Tse state Theorem 3 in terms of a unique
   *Eulerian cycle* of a `K`-mer graph. The repository's model is circular
   (`docs/open-problem.md`; Shomorony et al. 2016) and its equivalence is cyclic shift,
   which is the natural reading. If one instead read Theorem 3 as a *linear* statement, it
   would be the boundary-fixed version; the circular conclusion is the rotation-quotient
   of that. Either way `WEAK ⇒` spectrum determines `S` up to rotation. This is a reading
   of an accepted source, not an independent proof.
2. **Condensed graph.** Theorem 3 concludes uniqueness in the *condensed* sequence graph
   `G`; the raw `K`-mer graph statement is the one quoted in the arXiv v3 ("unique
   Eulerian cycle in the `K`-mer graph ... if and only if ..."). Sequence-level uniqueness
   is what we need and is what both statements give.
3. **Primary wording of Ukkonen/Pevzner.** Their original papers are the linear SBH /
   colored-graph formulations; the circular maximal-repeat form we use is
   Bresler–Bresler–Tse's accepted restatement. We do not claim the exact original wording.
4. **The converse is false** (already recorded): `I_s`-inadmissibility does not imply an
   ambiguous spectrum (`AAAAB`), so Conjecture 4 is an implication, not an equivalence.
5. **Finite sample.** None of this touches the finite-data ML question: it is a statement
   about the fibre of `D ↦ d_D`, prior to any tie or sampling rule.

---

## 4. Effect on the repository

1. **Reclassify Conjecture 4.**
   `mathematics/bridging-and-spectrum-uniqueness.md` §5 should record that the
   `I_s`-admissible / `WEAK` case is the `K = L−1` instance of Bresler–Bresler–Tse 2013,
   Theorem 3 (with the circular reading), replacing "Conjecture (with strong evidence)".
   The 123 906-genome exhaustive check and the randomized check
   (`scripts/bridging_spectrum_uniqueness.py`; re-run 2026-09-21, 0 ambiguous) are then
   corroboration of a source theorem, not its only support.
2. **De-condition the population equal-length step.**
   `docs/population-identifiability-intrinsic-genomes.md` §5/§10: the equal-length
   residue `d_T = d_S ⇒ T` a rotation of `S` becomes a source theorem for primitive
   `WEAK` genomes (primitivity is not needed for this step; it is needed for the
   cross-length Theorem P).
3. **Correct the anchor.**
   `docs/literature/substring-spectrum-identifiability-2026-09-20.md` is superseded on
   this point: use Bresler–Bresler–Tse Theorem 3 (maximal repeats, `K=L−1`), not
   Çelikkanat et al. Theorem 3.1. Çelikkanat et al. remains a valid *linear, non-maximal*
   restatement at the same threshold.
4. **No Lean-boundary change** is forced; this is a source-classification correction and a
   resolution of an inference, not a new kernel statement.

---

## 5. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| BBT repeat / triple-repeat / interleaved definitions (maximal, shorter-length convention) | **Source fact (quoted)** | Bresler–Bresler–Tse 2013, "Ukkonen's condition" paragraph |
| BBT Ukkonen's condition, `L_crit = max{ℓ}+1`, Theorem 1, Theorem 3 | **Source fact (quoted)** | Bresler–Bresler–Tse 2013 |
| Bridging threshold `ℓ ≤ L−2` at the full read set | **Proven** (bridgeability lemma) | strict two-sided extension; matches BBT Fig. 5 caption |
| `WEAK(P2) ⇔` no triple/interleaved maximal repeat of length `≥ K=L−1` | **Analysis (definitional identity)** | §3; same conventions as BBT/Shomorony |
| `WEAK ⇒` `L`-spectrum determines `S` up to rotation | **Source theorem + analysis** | BBT Thm 3 at `K=L−1`; circular Eulerian-cycle reading |
| Çelikkanat et al. Thm 3.1 is a linear, non-maximal restatement; not the anchor | **Source fact + analysis** | Çelikkanat et al. §3.1; condition (1) has no circular analogue |
| Ota–Manada 2023 circular criterion is a different (binary, MAW-based) criterion | **Source fact (abstract/Thm 1)** | IEICE E107.A(3) |
| Finite-sample ML (the 2016 open question) | **Not addressed** | out of scope; see `docs/literature-status.md` |

## 6. References

1. E. Ukkonen. *Approximate string-matching with `q`-grams and maximal matches.*
   Theoret. Comput. Sci. 92(1):191–211, 1992.
   <https://doi.org/10.1016/0304-3975(92)90143-4>
2. P. A. Pevzner. *DNA physical mapping and alternating Eulerian cycles in colored
   graphs.* Algorithmica 13(1–2):77–105, 1995.
   <https://doi.org/10.1007/BF01188582>
3. G. Bresler, M. Bresler, D. Tse. *Optimal assembly for high throughput shotgun
   sequencing.* BMC Bioinformatics 14(Suppl 5):S18, 2013.
   <https://doi.org/10.1186/1471-2105-14-S5-S18>; PMC3706340; arXiv:1301.0068.
4. I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse. *Information-optimal genome
   assembly via sparse read-overlap graphs.* Bioinformatics 32(17):i494–i502, 2016.
   <https://doi.org/10.1093/bioinformatics/btw450>
5. A. Çelikkanat, A. R. Masegosa, T. D. Nielsen. *Revisiting K-mer Profile for Effective
   and Scalable Genome Representation Learning.* NeurIPS 2024; arXiv:2411.02125.
   <https://arxiv.org/abs/2411.02125>
6. T. Ota, A. Manada. *A Reconstruction of Circular Binary String Using Substrings and
   Minimal Absent Words.* IEICE Trans. Fundamentals E107.A(3), 2024.
   <https://doi.org/10.1587/transfun.2023TAP0015>

## 7. Repository anchors

- `mathematics/bridging-and-spectrum-uniqueness.md` (§1 full-read reduction, §5 Conjecture 4)
- `docs/population-identifiability-intrinsic-genomes.md` (§1 predicates, §5 equal-length residue)
- `docs/synthesis-finite-rows-and-repairs-2026-09-21.md` (§1 `P1`/`P2`/`I_s`, §2.3, §4)
- `docs/bridging-source-semantics.md` (Bresler maximality, strict bridging)
- `docs/literature/substring-spectrum-identifiability-2026-09-20.md` (superseded anchor on this point)
- `scripts/bridging_spectrum_uniqueness.py` (finite corroboration; 123 906 admissible, 0 ambiguous)
