# Transferring `I_s` from oriented single-strand reads to double-strand data

_Status: independent mathematical analysis + exact computation + a bounded Lean
evaluator, for issue #215 (leaf of #217), 2026-10-09. Every claim below is
labelled **source fact**, **source-supported inference**, **modeling decision**,
**mathematical proof**, **verified computation**, **bounded computation**, or
**open**. Nothing here selects which reading the 2016 sentence denotes; the
purpose of this note is to show that the readings are *not* interchangeable and
to state precisely what each of them requires._

_Reproduce:_

```sh
python3 scripts/verify_oriented_molecule_bridging.py           # quick scopes
python3 scripts/verify_oriented_molecule_bridging.py --full    # wider scopes
```

_The script is self-contained, exact (integers and `fractions.Fraction`),
deterministic, shares no code with other repository scripts, and exits non-zero
on any failed assertion. The Lean facts are in
`AssemblyP1/DoubleStrandBridgingTransfer.lean` (kernel-checked, no `sorry`, no
new axioms)._

---

## 0. Answer at a glance

1. **There are at least three source-justified ways to combine Shomorony's
   bridging condition with double-strand read data, and they are pairwise
   inequivalent.** (V1) keep the read *placements* and collapse only the recorded
   read type; (V2) record molecule classes only and require the observation to
   admit an `I_s`-satisfying placement assignment; (V3) use Bresler, Bresler and
   Tse's (2013) explicit 2G remap. V1 and V2 are the same model up to what the
   observer records; V3 is a different model, not a relabelling. [modeling
   decision + verified computation]

2. **The integrated `AAATAT → AAAAAT` witness is a genuine counterexample under
   V1/V2 and is inadmissible under V3.** Under V1/V2 its read realization
   `{0,1,3,5}` is `I_s`-feasible (this is already kernel-checked on `main`:
   `AssemblyP1.SameLengthSection62Counterexample.truth_source_certificate`) and
   `D = AAAAAT` beats it (`3` exact, `5` binomial). Under V3 the doubling produces
   the length-`12` circle `AAATATATATTT`, which carries the **maximal triple
   repeat `ATATA` of length `4` at starts `2, 4, 6`**, and
   `bridgesCopy_length` (`e + 2 ≤ L`) forbids any length-`3` read from bridging
   any copy of it. So `InformationFeasible` fails on the doubled genome for
   *every* read set. [kernel-checked result;
   `AssemblyP1/DoubleStrandBridgingTransfer.doubled_not_information_feasible`]

3. **Bridging is not a function of molecule data.** The witness observation
   `x = {AAA:2, AAT:1, ATA:1, TAA:1}` has exactly three placement multisets
   consistent with it; one is `I_s`-feasible and two are not. Any molecule
   version of `I_s` must therefore choose a semantics for the unobserved
   placements, and the choice is material. [verified computation]

4. **The molecule and doubled-strand models are different models even before
   bridging is considered.** The doubled genome's read types are not the
   class-collapsed read types of the original genome: the exact identity is
   `spec_{S·ρ(S)}(w) = lint_S(w) + lint_S(ρ(w)) + j_S(w)`, with `j_S` the seam
   (junction) windows, and `j_S ≠ 0` in general. For `S = AAGG`, `L = 3` the
   doubled genome produces the molecule class `{GGC, GCC}` that `S`'s own
   molecule spectrum does not contain at all. [mathematical proof + verified
   computation]

5. **The oriented rigidity theorem does not transpose to molecule classes, and
   the obstruction is exactly the mechanism of the witness.** Under `I_s` the
   oriented `spec_3(AAATAT)` is the unique positive circulation on its oriented
   support, while the same computation on the class-support condition admits
   `12` circulations projecting to `≥ 2` molecule spectra. Five tempting
   class-level repairs were tested and **all five are refuted** inside the
   searched scope; one further repair survives the scope but has no proof.
   [mathematical proof on `main` for the oriented half; bounded computation for
   the molecule half]

**Consequence for #217.** The row "oriented `I_s` + MB09 molecule objective:
false (`AAATAT → AAAAAT`)" is settled and kernel-checked. The row "oriented `I_s`
+ Bresler double-strand 2G remap" is **not** settled by that witness: the
witness is inadmissible there, and the bounded search on `main` found no
counterexample in its scope. The published sentence's strand convention remains
**open** on the sources, as recorded in
`docs/source-notes/uniform-strand-convention-search-2026-09-20.md` §6.

---

## 1. The three models, stated exactly

Throughout, `Σ` is a finite alphabet with an involutive complement `comp`
(`A ↔ T`, `C ↔ G`) and `ρ(w) = comp(w_{e-1}) ⋯ comp(w_0)` is reverse complement.

### 1.1 Shomorony et al. (2016): oriented single-strand

**Source facts.** The theory is a circular string `s` of length `G` with
error-free length-`L` reads sampled independently and uniformly from the `G`
circular starts (§2); reverse complements appear only as experimental
preprocessing; the information-feasible set `I_s` of Eq. (1) is
Bresler et al.'s condition, whose repeat definitions include maximality
(`docs/bridging-source-semantics.md`). Bridging is a relation between a read
*placement* and a repeat copy: a read interval `[r, r+L)` straddles a lifted copy
interval `[t, t+ℓ)` iff `r < t` and `t + ℓ < r + L`.

So the observation object of this model is a placement multiset
`R = (t_1, …, t_N)` together with the oriented window types
`w_i = S[t_i … t_i + L)`. Both a `Genome`-level formalization
(`AssemblyP1.SourceFaithfulIs`, `InformationFeasible`) and the likelihood
machinery consume this.

### 1.2 Medvedev–Brudno (2009): reverse-complement molecules

**Source facts.** §1.1 ("a read is actually a DNA molecule … it is impossible to
know from which of the two strands the sequence is read"), §3.1 (a `k`-molecule is
the unordered reverse-complement pair), §4.1 ("each `k`-molecule is represented
only once"), §6.2 (graph vertices are the reads as molecules; `d_i` is the vertex
flow; per-vertex lower bound `1`). The reading that `4^k` in §6.1 is an oriented
count conflicting with the molecular §6.2 graph, and that the operative index set
is therefore observed molecule classes, is recorded in
`docs/source-notes/mb09-se61-index-orientation-resolution.md`.

So the observation object of this model is the molecule class count vector
`x`, with `x_c = #{i : c(w_i) = c}` for classes `c`.

### 1.3 Bridging versions

| | read object | bridging relation | candidate |
|---|---|---|---|
| **V1** placement-retaining | placements `(t_i, w_i)` *and* classes `c(w_i)` | Bresler/Shomorony on the placements | same-length circular word, `supp(m_D) = supp(x)` |
| **V2** class-compatible | classes `c(w_i)` only | "∃ a placement assignment consistent with `x` that is `I_s`-feasible" | same |
| **V3** Bresler 2G remap | `2N` doubled reads on the circle `S·ρ(S)` | Bresler/Shomorony on the doubled circle | the doubled circle `D·ρ(D)` |

V1 is the hybrid reading the existing witness uses; it is honest **only if
stated**: it is Shomorony's hypothesis side with Medvedev–Brudno's likelihood
side. That is a modeling decision of this repository, not a fact of either paper,
and `docs/maximum-likelihood-models-for-genome-assembly.md` §3.3 already
requires exactly this disclosure. V4 (no bridging at all, i.e. MB09 §6.2's flow
lower bounds replacing the placement conditions) is also available; under V4 the
published sentence has no bridging hypothesis to transfer, so it is not a
candidate reading of the sentence and is not analysed further.

---

## 2. The observation map `Φ` and the placement liftings `Ψ`

**Definition (observation map).** For a genome `S`, read length `L` and a
realized placement multiset `R`, `Φ(R)_c = #{i : c(S[t_i … t_i+L)) = c}`.
`Φ` forgets the placements, the orientations, and hence also which strand each
read came from.

**Definition (placement lifting).** For a molecule observation `x`, let
`Ψ_S(x) = {R : Φ(R) = x}`, a product of the per-class placement sets
`P_S(c) = {t : c(S[t … t+L)) = c}`, with `|P_S(c)| = m_S(c)`.

### 2.1 Bridging is not `Φ`-invariant (verified computation)

For the witness, `Ψ_S(x)` has exactly three elements:

```text
lifting {0,0,1,2,5}: I_s = False     (copy 4 of the maximal triple repeat A@{1,2,4}
                                      needs a read at start 3; there is none)
lifting {0,0,1,3,5}: I_s = True      (the realized one)
lifting {0,0,1,4,5}: I_s = False
```

So there is no function `B` of the molecule observation alone that agrees with
Shomorony's placement bridging on all read sets. Formally:

> **Proposition 2.1.** `Φ` does not descend to a well-defined map on `I_s`
> status: there exist `R ≠ R'` with `Φ(R) = Φ(R')`, `R ∈ I_s` and `R' ∉ I_s`.

The three liftings above are the proof (the read at start `0` is sampled twice,
which is why the multiset, not the set, matters for `Φ`).

### 2.2 What V2 means and why it is weaker than V1

`I_s^{V2}(x) :⇔ ∃ R ∈ Ψ_S(x), R ∈ I_s`, i.e. `x ∈ Φ(I_s)`. For the witness,
`x ∈ Φ(I_s)` because its own lifting is `I_s`-feasible. But V2 is *strictly*
weaker than V1 in the sense that matters for a hypothesis: an observation `x`
may satisfy V2 while the reads that were actually taken do not satisfy `I_s`.
The molecule model records only classes, so V2 is the honest version of the
bridging hypothesis for that model — and it is a hypothesis about the existence
of unobserved information. This is a genuine weakeness of the V1/V2 reading, not
a technicality: nothing in MB09's data determines `Ψ_S(x)`.

The ∀-variant ("every lifting of `x` is `I_s`-feasible") is materially stronger
and, for any observation with a class occurring in more than one place, tends to
be vacuous; it is not analysed further and should not be silently adopted.

---

## 3. The Bresler 2G remap (V3), and why the witness dies there

**Source fact.** Bresler et al. (2013), "Discussions and extensions":
"DNA is double-stranded and consists of a length-`G` sequence `u` and its reverse
complement `u~`. Each read is either sampled from `u` or `u~`. This more
realistic scenario can be mapped into our single-strand model by defining `s` as
the length-`2G` concatenation of `u` and `u~`, transforming each read into itself
and its reverse complement so that there are `2N` reads. Generalized Ukkonen's
conditions hold verbatim for this problem …"

**Modeling decision (V3).** Genome `Ŝ = S · ρ(S)` (circular, length `2G`); read
set = the `2N` reads obtained by doubling; `I_s` applied to `Ŝ` with those
reads; candidate = doubled circle `D · ρ(D)` of length `2G`.

### 3.1 Where the doubled reads sit

Three structural facts about the doubled circle `Ŝ = S · ρ(S)`:

1. Every **non-wrapping** window of `S` is a window of `Ŝ` at the same absolute
   start (verified exhaustively for binary `2 ≤ G ≤ 8`, `L = 3`).
2. The circle `Ŝ` is anti-palindromic — `Ŝ[i] = comp(Ŝ[2G - 1 - i])` — hence the
   reflection identity `window_Ŝ(2G - b - L) = ρ(window_Ŝ(b))` holds for **every**
   absolute start `b`. So the reverse complement of any read sitting at `b` sits at
   `2G - b - L`.
3. A **wrapping** window of `S` (start `t > G - L`) is *not in general* a window
   of `Ŝ`: in the exhaustive binary scope only `380` of `1016` wrapping windows
   also occur in the doubled genome. This is a genuine wrinkle of the remap: the
   doubled genome's seam reads are artifacts of the reduction, and some reads of
   the original circle have no seat in `Ŝ`.

For the witness (`G = 6`, `L = 3`) the realized read strings and their reverse
complements are

```text
read strings              : AAA, AAT, TAT, TAA   (from starts 0, 1, 3, 5)
reverse complements       : TTT, ATT, ATA, TTA
absolute starts in Ŝ      : {0, 1, 3, 11} ∪ {9, 8, 6, 10}
doubled read starts       : {0, 1, 3, 6, 8, 9, 10, 11}
```

The read `TAA` (start `5`, wrapping in `S`) does occur in `Ŝ`, at absolute start
`11`, because this particular genome ends with the complement of its first base;
its partner `TTA` sits at `10`. Each of these placements is verified to be a
genuine occurrence of the read string, and the partner rule `2G - b - L` is
kernel-checked (`DoubleStrandBridgingTransfer.partner_placements`). Under the
maximally generous placement of the doubled read strings, coverage of `Ŝ`
holds. The verdict of §3.2 is placement-independent, so it does not depend on
this generosity.

The doubled read set's molecule class counts are **exactly twice** the
single-strand observation `x = {AAA:2, AAT:1, ATA:1, TAA:1}`, i.e.
`{AAA:4, AAT:2, ATA:2, TAA:2}`. This is a general fact, not an accident:

> **Lemma 3.1 (strand-invariance of the recorded class).** For any read `w`,
> `c(w) = c(ρ(w))`. Hence every realized read contributes its class twice under
> the Bresler doubling, and the doubled observation is `2x`. [mathematical
> proof; verified computation]

So the two double-strand conventions agree on *what is recorded*; they disagree
on the object the bridging conditions live on.

### 3.2 The doubled genome of `AAATAT` is not `I_s`-feasible

`Ŝ = AAATATATATTT`. Its maximal triple repeats of length `≥ L - 1 = 2` are
`AT@{2,4,8}`, `AT@{2,6,8}`, `AT@{3,5,11}`, `AT@{3,7,11}`, `AT@{5,7,11}` and
`ATATA@{2,4,6}`. The length-`4` repeat is maximal in the source's three-copy
sense: the preceding symbols are `A, T, T` and the following symbols are
`A, A, T`, so no extension is possible.

> **Theorem 3.2 (kernel-checked).** No read set of length `3` can bridge the
> length-`4` triple repeat `ATATA@{2,4,6}` of `Ŝ`, because
> `bridgesCopy_length` gives `e + 2 ≤ L` for any bridged copy and `4 + 2 > 3`.
> Hence `InformationFeasible Ŝ 3 R` fails for every `R : Finset (Fin 12)`.
>
> `AssemblyP1.DoubleStrandBridgingTransfer.doubled_not_information_feasible`

(Under the *maximally generous* string reading of where a read may be placed,
coverage of `Ŝ` by the doubled read set does hold; the failure comes from the
triple-repeat clause, and it is placement-independent.)

**Verdict.** Under V3 the `AAATAT → AAAAAT` witness is inadmissible: it is
neither a counterexample nor evidence for the double-strand reading. The
repository's existing statement that this witness "checks Shomorony's
single-strand `I_s` while evaluating an MB09 reverse-complement molecular
likelihood/flow representation"
(`docs/maximum-likelihood-models-for-genome-assembly.md` §3.3) is thereby
sharpened: the molecular likelihood goes with the *hybrid* hypothesis, not with
the double-strand one.

### 3.3 How often is the remap feasible at all? (bounded computation)

Using the verified equivalence "a maximal triple repeat of length `≥ L - 1`
exists iff some length-`(L - 1)` window occurs at least three times" (valid for
primitive genomes by Lemma B of `docs/source-notes/oriented-se62-rigidity-theorem.md`;
**not** valid in general for periodic genomes, where maximality blocks the
repeat — both directions were re-checked exhaustively in the script):

| `G` | binary words `u` | doubled genome free of triple repeats of length `≥ 2` |
|---|---|---|
| 2 | 4 | 4 |
| 3 | 8 | 8 |
| 4 | 16 | 8 |
| 5 | 32 | 2 |
| 6 | 64 | 4 |
| 7 | 128 | 2 |
| 8 | 256 | 4 (`--full`) |
| 9 | 512 | 2 (`--full`) |
| 10 | 1024 | 4 (`--full`) |

So the remapped `I_s` is satisfiable only on a sparse minority of `u`, at a
density far below the original single-strand `I_s`: in the same `L = 3` binary
scope, `162` of `496` genomes (`4 ≤ G ≤ 8`) pass the triple-repeat clause of
`I_s` on themselves, while only `28` of `252` doubled genomes (`2 ≤ G ≤ 7`) pass
it on the doubled circle. The remap is therefore not a harmless
rephrasing; it is a materially stronger hypothesis engine.

---

## 4. Why the oriented rigidity theorem does not transpose

`docs/source-notes/oriented-se62-rigidity-theorem.md` proves: if `R ∈ I_s`, then
`spec_L(S)` is the unique positive circulation of total `G` on `X_S`. Its proof
runs on the oriented window graph and its key counting step is
`A(w) ≤ occ(prefix_{L-1}(w)) ≤ 2`, where `≤ 2` comes from `I_s` via the
triple-repeat clause. Three things go wrong under the molecule coarsening
`κ : spec ↦ m`, `κ(spec)_c = Σ_{u ∈ c} spec(u)`.

### 4.1 The counting step transfers with a factor `2`

`I_s` bounds every oriented `(L - 1)` window by `2`, hence every molecule class
of `(L - 1)`-mers by `4` in general (`spec(u) + spec(ρ(u)) ≤ 2 + 2`), and every
`L`-mer class by `4` as well. The bound `4` is sharp and reachable under `I_s`:
`S = AAATTT`, `L = 3`, has class `{AA,TT}` of `2`-mers with multiplicity `4` and
no long triple repeat. The rigidity proof needs `2`, not `4`. [verified
computation]

### 4.2 Balance does not descend to class counts

Summing the de Bruijn balance equations over a class `n = {v, ρ(v)}` of
`(L - 1)`-mers mixes `d_u` with `d_{ρ(u)}` inside each `L`-mer class: the summed
condition at `n` is

```text
Σ_u spec(u)·[class(prefix u) = n]  =  Σ_u spec(u)·[class(suffix u) = n],
```

where the sums run over words, and each `L`-mer class contributes its two
constituent words separately with their own multiplicities. The left- and
right-hand sides therefore depend on the **within-class split**
`spec(u)` versus `spec(ρ(u))`, which the molecule spectrum
`m(c) = Σ_{u ∈ c} spec(u)` does not record. So the balance equations have no
transcription as conditions on class counts. Dually, the *naive* class-level
balance one might write instead — sum over classes `c` whose endpoint classes
contain `n` — is automatic for every class vector, because each class
`c = {u, ρu}` has the same multiset of constituent prefix classes
`{class(prefix u), class(suffix u)}` and of suffix classes
`{class(suffix u), class(prefix u)}`. Either way the oriented balance constraint,
which is what the rigidity proof actually uses, disappears at the class level.
[mathematical proof]

### 4.3 The class condition is strictly coarser, and the witness sits in the gap

For the witness instance the two outer-approximated candidate sets are:

```text
oriented support supp(spec_3(S)) = {AAA, AAT, ATA, TAT, TAA}: 1 balanced positive
    vector of total 6 — spec_3(S) itself (the rigidity theorem, reproduced).
class support V = {AAA, AAT, {ATA,TAT}, {TAA,TTA}}             : 12 balanced positive
    vectors of total 6, projecting to 2 distinct molecule spectra:
    d_S = {AAA:1, AAT:1, ATA:3, TAA:1}   and   d_D = {AAA:3, AAT:1, ATA:1, TAA:1}.
```

So the mechanism is exactly the coarsening: `D = AAAAAT` has a *different
oriented support* (`TAT` is absent, so `D` is not even an oriented spelled
candidate) while its class support coincides. That is what lets it be a §6.2
spelled candidate and beat the truth. The truth's own oriented rigidity is not
contradicted; it is simply *not applicable* to the molecule candidate set.
[verified computation; the `I_s` and the ratios are kernel-checked on `main`]

### 4.4 Census and the repair hypotheses (bounded computation)

Scope: binary genomes, `L = 3`, `4 ≤ G ≤ 8` (`--full`: `G ≤ 10`), restricted to
genomes with no triple repeat of length `≥ L - 1`, i.e. those that pass the
triple-repeat clause of `I_s`. For each, the molecule candidate set is the set of
molecule spectra of balanced integer vectors of total `G` whose class support
equals the truth's (an outer approximation of the spelled-candidate set, so a
singleton implies rigidity).

| quantity | count |
|---|---|
| genomes in scope | 162 |
| molecule-non-rigid (candidate set has `≥ 2` spectra) | **86** |
| oriented-non-rigid (rigidity theorem violated) | **0** |
| smallest molecule-non-rigid | `AAATAT` (`G = 6`) |

Refuted repairs (all project-level hypotheses, none from the sources):

| hypothesis | satisfied by | still non-rigid |
|---|---|---|
| every `(L - 1)`-mer class `≤ 2` | 54 | 12 (`AAATAT` …) |
| every `L`-mer class `≤ 2` | 90 | 44 (`AAATATT` …) |
| truth spectrum class-symmetric (`d_u = d_{ρ(u)}`) | 48 | 16 (`AAATATTT` …) |
| every `L`-mer class multiplicity even | 64 | 16 |
| every `(L - 1)`-mer class multiplicity even | 76 | 44 |
| **every `(L - 1)`-mer class and every `L`-mer class `≤ 2`** | 30 | **0** (not refuted in scope) |

At `L = 4` (`4 ≤ G ≤ 6`, `--full`) the scope contains `84` genomes and **no**
molecule-non-rigid one, so the phenomenon is `(G, L)`-scattered, which is
consistent with the bounded molecule searches on `main` (`docs/source-notes/uniform-strand-convention-search-2026-09-20.md` §4:
witnesses at `(6,3)` and `(8,3)`, zeros at `(5,3)`, `(7,3)`, `(6,4)`).

**Status.** The last repair is a conjecture with bounded evidence only. The
oriented rigidity proof does not port (§4.1–4.2), so there is no proof even for
that stronger hypothesis, and `AAATAT` shows that `I_s` alone is not enough.

---

## 5. What each reading additionally requires, and the effect

| reading | required extra assumptions | effect on the 2016 question |
|---|---|---|
| **V1/V2** | (i) read placements retained or their existence asserted; (ii) molecule read types; (iii) `supp(m_D) = supp(x)` (per-vertex lower bound `1`); (iv) `|D| = G`. | Counterexample exists and is kernel-checked. If (iii) is strengthened to per-occurrence `d ≥ x`, the witness becomes **vacuous** (the truth itself fails: `d_S(AAA) = 1 < x(AAA) = 2`) — the strengthened statement is **open**, not refuted. |
| **V3** | genome doubled, reads doubled to `2N`, `I_s` on the length-`2G` circle, candidates doubled. | The `AAATAT` witness is inadmissible (Theorem 3.2). No counterexample is known; `docs/source-notes/uniform-strand-convention-search-2026-09-20.md` §5 records a bounded zero for `G ≤ 6` under Variant E. Open. |
| **V4** | no bridging hypothesis at all (MB09 §6.2 flow alone). | The published sentence's bridging condition is not part of the model, so V4 is not a reading of the sentence. |

Note that (iv) is not supplied by MB09's known-`N` parameter;
`docs/maximum-likelihood-models-for-genome-assembly.md` §2 already records this
distinction, and it is needed here as well.

---

## 6. Explicit non-equivalences (audited witnesses)

1. **Class vs oriented support.** `supp(spec_3(AAATAT)) = {AAA, AAT, ATA, TAT,
   TAA}` but `supp(spec_3(AAAAAT)) = {AAA, AAT, ATA, TAA}`; the class supports
   coincide. The class condition is strictly coarser.
2. **Asymmetric within-class counts.** `spec_3(AAATAT)(ATA) = 2`,
   `spec_3(AAATAT)(TAT) = 1`, class `{ATA,TAT}` = `3`. Any argument that needs
   `d_u = d_{ρ(u)}` is false on this instance.
3. **Molecule model vs doubled model (spectra).**
   `spec_{S·ρ(S)}(w) = lint_S(w) + lint_S(ρ(w)) + j_S(w)` with `j_S` the seam
   windows; verified exhaustively for binary `2 ≤ G ≤ 8`, `L = 3`, together with
   the class symmetry `spec_{Ŝ}(w) = spec_{Ŝ}(ρ(w))`.
   The two double-strand conventions induce the same read-type distribution iff
   `j_S(w) = wrap_S(w) + wrap_S(ρ(w))` for every `w`; this holds for `254` of
   `508` binary words in the scope. Witness of failure: `S = AAGG`, `L = 3`,
   produces the class `{GGC, GCC}` from the seam, which is absent from `S`'s
   molecule spectrum.
4. **Bridging is not `Φ`-invariant** (Proposition 2.1).
5. **Rigidity is not `κ`-stable**: `AAATAT` is oriented-rigid and molecule-
   non-rigid.
6. **V1 vs V3 on the same witness**: `I_s` holds on `S` (kernel-checked on
   `main`) and fails on `Ŝ` (kernel-checked here).

---

## 7. Epistemic classification

| claim | status |
|---|---|
| Shomorony's model is oriented single-strand; `I_s` is Bresler's condition with maximal repeats; bridging is placement-based | **source fact** |
| Bresler et al. 2013 double-strand remap: `s = u·u~`, doubled reads, "conditions hold verbatim" | **source fact** |
| MB09 read types are reverse-complement molecules with per-vertex lower bound `1` | **source fact** |
| V1/V2/V3 as stated definitions, and that the read-placement map is `Ψ` | **modeling decision** |
| `Φ` does not determine `I_s` status; the three liftings | **verified computation** (exact, deterministic) |
| `spec_{Ŝ}(w) = lint_S(w) + lint_S(ρ(w)) + j_S(w)`; class symmetry of `spec_Ŝ` | **mathematical proof** + **verified computation** (exhaustive in scope) |
| `c(w) = c(ρ(w))`, so the doubled observation is `2x` | **mathematical proof** + **verified computation** |
| `AAATAT` molecule witness: `I_s`, supports, ratios `3` and `5`, per-occurrence vacuity | **kernel-checked result** on `main` + **verified computation** |
| Bresler-doubled instance is not `I_s`-feasible for any read set | **kernel-checked result** (`AssemblyP1/DoubleStrandBridgingTransfer`) |
| oriented rigidity on its own support; non-rigidity under the class condition | **mathematical proof** (oriented, on `main`) + **verified computation** (molecule) |
| census numbers, repair refutations, remap feasibility densities | **bounded computation** (scope stated) |
| "every `(L - 1)`-mer class and every `L`-mer class `≤ 2` restores molecule rigidity" | **conjecture**, bounded evidence only |
| which strand convention the 2016 sentence intends | **open** |

## 8. Sources and repository cross-references

Primary. Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2–§5, Eq. (1), DOI
`10.1093/bioinformatics/btw450`. Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §1.1,
§3.1, §4.1, §6.1–6.2, §8.2, PMC3154397. Guy Bresler, Ma'ayan Bresler, David Tse,
*Optimal assembly for high throughput shotgun sequencing*, *BMC
Bioinformatics* 14(Suppl 5):S18 (2013), "Discussions and extensions",
PMC3706340.

Repository (on `main` unless noted):
[`../open-problem.md`](../open-problem.md),
[`../bridging-source-semantics.md`](../bridging-source-semantics.md),
[`../maximum-likelihood-models-for-genome-assembly.md`](../maximum-likelihood-models-for-genome-assembly.md),
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
[`../ml-formalization-contract.md`](../ml-formalization-contract.md),
[`uniform-strand-convention-search-2026-09-20.md`](uniform-strand-convention-search-2026-09-20.md),
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md),
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md),
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md),
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md),
`scripts/verify_oriented_molecule_bridging.py`,
`AssemblyP1/SourceFaithfulIs.lean`,
`AssemblyP1/SameLengthSection62Counterexample.lean`,
`AssemblyP1/DoubleStrandBridgingTransfer.lean`.

This note does not settle the Shomorony et al. (2016) open question and does not
select a strand convention. It establishes that the conventions are inequivalent,
that the existing counterexample belongs to exactly one of them, and what each of
the remaining ones requires.
