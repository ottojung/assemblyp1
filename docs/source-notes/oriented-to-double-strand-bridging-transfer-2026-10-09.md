# Transferring `I_s` from oriented single-strand reads to double-strand data

_Status: independent mathematical analysis + exact computation + a bounded Lean
evaluator, for issue #215 (leaf of #217), 2026-10-09; audited and corrected on
the same date (see §9). Every claim below is
labelled **source fact**, **source-supported inference**, **modeling decision**,
**mathematical proof**, **verified computation**, **bounded computation**, or
**open**. Nothing here selects which reading the 2016 sentence denotes; the
purpose of this note is to show that the readings are *not* interchangeable and
to state precisely what each of them requires._

_Reproduce:_

```sh
python3 scripts/verify_oriented_molecule_bridging.py            # quick scopes
python3 scripts/verify_oriented_molecule_bridging.py --full     # wider scopes
python3 scripts/audit_215_transfer_reconciliation.py            # independent audit
python3 scripts/verify_two_disjoint_circles_duplex.py           # V5 model (§10)
```

_The scripts are self-contained, exact (integers and `fractions.Fraction`),
deterministic, and share no code with each other or with other repository
scripts; each exits non-zero on any failed assertion. The second one re-derives
every number in this note from scratch on a different data representation. The
Lean facts are in
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
   `AssemblyP1.SameLengthSection62Counterexample.truth_information_feasible`,
   which discharges the **authoritative** shared predicate
   `AssemblyP1.SourceFaithfulIs.InformationFeasible`) and
   `D = AAAAAT` beats it (`3` exact, `5` binomial). Under V3 the doubling produces
   the length-`12` circle `AAATATATATTT`, which carries the **maximal triple
   repeat `ATAT` of length `4` at starts `2, 4, 6`**, and
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

6. **A third model (V5), two disjoint circles, is spelled out in §10.** It
   represents the duplex as `(S, rc(S))`, with the exact spectrum
   `spec_duplex(w) = spec_S(w) + spec_S(rc(w))` (no seam terms) and the exact
   read-placement map `t ↦ (G-t-L) mod G`. Its **circle-by-circle** reading is
   *exactly compatible* with the oriented single-strand reduction (the `rc`
   symmetry), so R1/R2/R3 are resolved by construction; its **duplex-as-a-whole**
   reading is ill-defined and strictly stronger (mixed triple repeats). Under
   circle-by-circle the `AAATAT → AAAAAT` witness survives (kernel-checked);
   under duplex-as-a-whole it is inadmissible. V5 is **not** MB09 and **not** the
   Bresler remap; it is a distinct, disclosed modeling decision. [kernel-checked
   + verified computation; §10]

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
   of `Ŝ` at its natural seat: in the exhaustive binary scope only `380` of
   `1016` wrapping windows still occur at the seat `G + t` of the doubled genome
   (and `936` occur somewhere, but `80` occur nowhere). This is a genuine wrinkle
   of the remap: the doubled genome's seam reads are artifacts of the reduction,
   and some reads of the original circle have no seat in `Ŝ`.

For the witness (`G = 6`, `L = 3`) the realized read strings and their reverse
complements are

```text
read strings              : AAA, AAT, TAT, TAA   (starts 0, 1, 3, 5 in S)
reverse complements       : TTT, ATT, ATA, TTA
seats in Ŝ (absolute)     : {0, 1, 3, 11} ∪ {9, 8, 6, 10}
doubled read starts       : {0, 1, 3, 6, 8, 9, 10, 11}
```

Three of the four reads are non-wrapping in `S` and sit at their own start; the
read `TAA` at start `5` wraps (`5 > G - L = 3`), so its seat is the absolute
start `11` of `Ŝ`, where it genuinely occurs, because this genome ends with the
complement of its first base. The partner of the read at absolute seat `b` is at
`2G - b - L`, which is the seat rule `π(b) = 12 - b - 3 (mod 12)`; in particular
the partner of `11` is `10`, **not** `2G - 5 - L = 4`, because `b` is the seat in
`Ŝ` and not the start in `S`. Every one of these placements is verified to be a
genuine occurrence of its read string, and the componentwise partner identity
`window(b')(d) = comp(window(b)(L - 1 - d))` for all `d : Fin 3` is
kernel-checked (`DoubleStrandBridgingTransfer.partner_windows`). Under the
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

> **A structural caveat on V3 as a reduction.** Bresler's sentence transforms
> "each read into itself and its reverse complement". That is only a map from
> read realizations to read realizations if every read of the original circle
> has a seat in `S · ρ(S)`. In the exhaustive binary scope only `380` of `1016`
> wrapping windows keep their natural seat `G + t` in the doubled genome;
> counting occurrence anywhere, `936` of the `1016` do occur in `S · ρ(S)`, and
> **`80` do not occur at all**. So Bresler's "conditions hold verbatim" cannot
> be read literally for a *circular* genome: the remap both loses some realized
> reads and invents seam reads. This is a property of the reduction, not of the
> `AAATAT` instance (for which the wrapping read does have a seat). It is one of
> the reasons V1/V2 and V3 are not interchangeable. [verified computation,
> exhaustive in scope]

### 3.2 The doubled genome of `AAATAT` is not `I_s`-feasible

`Ŝ = AAATATATATTT`. Its maximal triple repeats of length `≥ L - 1 = 2` are
`AT@{2,4,8}`, `AT@{2,6,8}`, `TA@{3,5,11}`, `TA@{3,7,11}`, `TA@{5,7,11}` and
`ATAT@{2,4,6}`. The length-`4` repeat is maximal in the source's three-copy
sense: the preceding symbols are `A, T, T` and the following symbols are
`A, A, T`, so no extension is possible. (Its three copies together read
`ATATATAT` over the positions `2..9`.)

> **Theorem 3.2 (kernel-checked).** No read set of length `3` can bridge the
> length-`4` triple repeat `ATAT@{2,4,6}` of `Ŝ`, because
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
[verified computation; the `I_s` (via `truth_information_feasible`, the
  authoritative `SourceFaithfulIs.InformationFeasible`) and the ratios are
  kernel-checked on `main`]

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
| every `L`-mer class multiplicity even | 60 | 16 |

**Scope discipline for this table.** Every cell above is the *quick* scope
`4 ≤ G ≤ 8`. The audit found the shipped cell `64` for "every `L`-mer class
multiplicity even" was the *`--full`* number (`4 ≤ G ≤ 10`, where the scope is
`174` genomes, `92` molecule-non-rigid, `h1 = 54`, `h2 = 90`, `h3 = 50`,
`h5 = 64`, `h6 = 78`, `h7 = 30`) pasted into an otherwise quick-scope row; the
quick-scope value is `60`, which is what the cell now says. The `h7` row is `30`
in *both* scopes, and it is the only row not refuted in either.
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
| **V3** | genome doubled, reads doubled to `2N`, `I_s` on the length-`2G` circle, candidates doubled; **and**, for the doubling to be a reduction at all, (R1) read-seat preservation for wrapping reads, (R2) seam–wrap agreement `j_S(w) = wrap_S(w) + wrap_S(ρ(w))`, (R3) feasibility of `I_s` on the length-`2G` circle. | The `AAATAT` witness is inadmissible (Theorem 3.2). No counterexample is known; `docs/source-notes/uniform-strand-convention-search-2026-09-20.md` §5 records a bounded zero for `G ≤ 6` under Variant E. **Open, not refuted** — the row is not settled in either direction by this witness. |
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
   `main` by `truth_information_feasible`) and fails on `Ŝ` (kernel-checked here
   by `doubled_not_information_feasible`).

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
| `AAATAT` molecule witness: `I_s`, supports, ratios `3` and `5`, per-occurrence vacuity | **kernel-checked result** on `main` (`SameLengthSection62Counterexample.truth_information_feasible`, the authoritative `SourceFaithfulIs.InformationFeasible`) + **verified computation** |
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
`scripts/audit_215_transfer_reconciliation.py`,
`scripts/verify_two_disjoint_circles_duplex.py`,
`AssemblyP1/SourceFaithfulIs.lean`,
`AssemblyP1/SameLengthSection62Counterexample.lean`,
`AssemblyP1/DoubleStrandBridgingTransfer.lean`,
`AssemblyP1/TwoDisjointCirclesDuplex.lean`.

This note does not settle the Shomorony et al. (2016) open question and does not
select a strand convention. It establishes that the conventions are inequivalent,
that the existing counterexample belongs to exactly one of them, and what each of
the remaining ones requires.

---

## 9. Independent audit of this appendix, and the residual

A second, code-independent pass (issue #215, second owner) re-derived every
number here with `scripts/audit_215_transfer_reconciliation.py`, which shares no
code with `scripts/verify_oriented_molecule_bridging.py`, and audited the kernel
module. All substantive conclusions survived. Five defects were found and are
corrected above; they are recorded here because each is the kind of defect that
makes an *audited* witness list unusable, and none of them changes a verdict.

1. **Four of the six long triple repeats of `Ŝ` were printed with the wrong
   word.** The shipped list said `AT@{3,5,11}`, `AT@{3,7,11}`, `AT@{5,7,11}` and
   `ATATA@{2,4,6}`; the computed length-`e` windows are `TA@{3,5,11}`,
   `TA@{3,7,11}`, `TA@{5,7,11}` and `ATAT@{2,4,6}`. The last one is impossible
   as written: `ATATA` has length `5` and cannot be the length-`4` window. The
   kernel-checked theorem (`doubled_triple_repeat`, `doubled_agree_*`) never
   names the word, so it was unaffected; only the prose was wrong.
2. **The `I_s` kernel-check was credited to the wrong theorem.** The appendix
   cited `SameLengthSection62Counterexample.truth_source_certificate`, which
   discharges the module-local `SourceCertificate`, i.e. the **deprecated
   endpoint-only** bridging predicate `bridgedCopy` (`inRead` on `t-1` and on
   `t+e`), explicitly superseded in `SourceFaithfulIs.lean` ("that was the
   definition used up to this commit") and retained in that module as
   "supporting evidence only". The authoritative kernel-check on `main` is
   `truth_information_feasible`, which proves
   `SourceFaithfulIs.InformationFeasible truthGenome 3 {0,1,3,5}` at full
   strength. The attribution now names the authoritative theorem. On this
   instance the two predicates happen to agree, so the verdict is unchanged —
   but the strength the appendix attributed to the citation was not the strength
   the cited theorem has.
3. **`380 of 1016` was ambiguous.** The shipped code checks the natural seat
   `G + t`, not occurrence anywhere. The two numbers are different (`380` vs
   `936`), and `80` wrapping windows occur nowhere in the doubled genome. §3.1
   now states all three.
4. **One cell of the §4.4 repair table was scope-mixed.** "every `L`-mer class
   multiplicity even" was printed as `64 | 16`; the shipped script computes
   `60 | 16` in the table's declared quick scope (`4 ≤ G ≤ 8`) and `64 | 16` in
   the `--full` scope (`4 ≤ G ≤ 10`), so the `64` was a full-scope number sitting
   in an otherwise quick-scope row. Corrected to `60 | 16`, with the full-scope
   figure recorded so the row is no longer ambiguous. All other cells and the
   `162 / 86 / 30 / 0` totals were reproduced exactly in both scopes by the
   independent audit (which reports `174 / 92` for `--full`).
5. **The kernel-checked partner statement covered fewer components than its
   docstring claimed.** `partner_placements` compared `window 3 b 0` with
   `comp (window 3 b' 2)`, i.e. **4 of the 12** symbol components of the four
   partner windows, while the module docstring said it "kernel-checks the
   read-partner placements that Bresler's doubling induces". It is replaced by
   `partner_windows`, which proves the componentwise identity for every
   `d : Fin 3`, plus `partner_starts` recording the seat rule. No definition was
   changed and no theorem was weakened.

### 9.1 Is V3 exactly compatible with V1/V2?

No. **The two double-strand conventions are not exactly compatible**, and the
gap is a conjunction of three independent requirements, each of which is
necessary and none of which is automatic:

- **(R1) read-seat preservation.** Bresler's doubling maps a read realization to
  a read realization only if every realized read of the circular genome has a
  seat in `S · ρ(S)`. For wrapping reads this fails in general: `636` of `1016`
  lose their natural seat, `80` have no seat at all.
- **(R2) seam–wrap agreement.** The two conventions induce the same read-type
  distribution iff `j_S(w) = wrap_S(w) + wrap_S(ρ(w))` for every `w`, where
  `j_S` counts the seam windows and `wrap_S` the wrapping windows of `S`. This
  holds for `254` of `508` binary words in the exhaustive scope (`2 ≤ G ≤ 8`,
  `L = 3`), and fails with the witnessed counterexample `S = AAGG`, whose seam
  creates the class `{GGC, GCC}` that `S`'s own molecule spectrum does not
  contain (§6, item 3).
- **(R3) feasibility on the doubled circle.** Even with (R1) and (R2),
  `InformationFeasible` must hold on the length-`2G` circle, which is a strictly
  stronger hypothesis engine than on the length-`G` circle: `28` of `252` doubled
  binary genomes (`2 ≤ G ≤ 7`, `L = 3`) are free of triple repeats of length
  `≥ L - 1`, against `162` of `496` original genomes (`4 ≤ G ≤ 8`) that pass
  the triple-repeat clause on themselves (§3.3).

**Effect on the conclusion.** Under V1/V2 the `AAATAT → AAAAAT` witness is a
genuine, kernel-checked counterexample, and the per-occurrence strengthening
`d ≥ x` makes it vacuous without refuting the schema (the truth itself fails
`d_S(AAA) = 1 < x(AAA) = 2`). Under V3 the same witness is **inadmissible**
(Theorem 3.2) and the row is **not** settled by it: V3 is satisfied on a sparse
minority of genomes, no counterexample is known there, and the published
question therefore remains **open** under V3 rather than refuted. Under V4 there
is no bridging hypothesis to transfer, so V4 is not a reading of the published
sentence. The strand convention of the 2016 sentence remains **open** on the
sources, and no reading may be promoted by agreement between agents.

---

## 10. The two-disjoint-circles duplex model (V5): an algebraic alternative to the Bresler remap

_Status: independent mathematical analysis + exact computation + a bounded
kernel-checked evaluator, for issue #215 (leaf of #217), 2026-10-09.  This
section responds to the research-assistant board notes of 2026-10-09T07:05Z
(the V5 direction) and 2026-10-09T07:43Z (the predicate-soundness audit).  Every
claim is labelled as in §7.  Nothing here selects a strand convention or claims
the 2016 sentence; V5 is a **third model**, distinct from V1/V2 and V3._

_Reproduce:_

```sh
python3 scripts/verify_two_disjoint_circles_duplex.py
```

_The Lean facts are in `AssemblyP1/TwoDisjointCirclesDuplex.lean`
(kernel-checked, no `sorry`, no new axioms; axioms `propext, Classical.choice,
Quot.sound` only)._

### 10.0 The model, stated exactly

**Definition (two-disjoint-circles duplex).** Fix a circular genome `S` of
length `G` over an alphabet `Σ` with involutive complement `comp`, and write
`rc(S)` for the reverse-complement circle, `rc(S)[i] = comp(S[(G-1-i) mod G])`.
The **V5 duplex** is the pair `(S, rc(S))` of *disjoint* circles, each of length
`G`, with `2G` positions in total.  There is no seam, no concatenation, and no
artificial length-`2G` circle.

**Definition (duplex spectrum).**  For an oriented `L`-mer `w`,

```text
spec_duplex(w) = spec_S(w) + spec_rcS(w) = spec_S(w) + spec_S(rc(w)).
```

**Proposition 10.0 (exactness of the V5 spectrum).**  `spec_rcS(w) = spec_S(rc(w))`,
so `spec_duplex(w) = spec_S(w) + spec_S(rc(w))`, and
`Σ_w spec_duplex(w) = 2G`.  There are **no seam terms**, in contrast with V3's
`spec_{S·ρ(S)}(w) = lint_S(w) + lint_S(ρ(w)) + j_S(w)` of §6.
[mathematical proof; verified computation: exhaustive binary `2 ≤ G ≤ 8`, `L = 3`,
`508/508` genomes, and total `2G` in every case.]

**Definition (read-placement map).**  A read realized at `S`-start `t` (the
window `S[t … t+L)`) has its reverse-complement partner realized at
`rc(S)`-start `(G - t - L) mod G`:

```text
window_rcS((G - t - L) mod G) = rc(window_S(t)).
```

**Proposition 10.1 (exactness of the read-placement map).**  For **every**
`t : Fin G`, including wrapping reads, the `rc(S)`-window at the partner start is
the reverse complement of the `S`-window at `t`.  [mathematical proof; verified
computation: exhaustive `508/508`; kernel-checked for the witness by
`TwoDisjointCirclesDuplex.partner_window_rc`.]

The exactness is because the two circles are disjoint and each has its own
origin, so there is no seam to cross.  This removes V3's **R1** (read-seat
preservation) and **R2** (seam–wrap agreement) failures **by construction**:
every read has an exact seat on its own circle, and its partner has an exact seat
on the other circle.

**Definition (doubled read set).**  For a realized read multiset `R` on `S`, the
V5 duplex read set is `R` on `S` together with the partner reads
`{(G - t - L) mod G : t ∈ R}` on `rc(S)`: `2N` reads in total (multiplicities
included).  This is the same *recorded* molecule data as V3's doubled read set
(§3, Lemma 3.1), placed on two circles instead of one.

### 10.1 The witness under V5

Instance: `S = AAATAT` (`G = 6`), `L = 3`, realized starts `[0, 0, 1, 3, 5]`
(start `0` sampled twice), `rc(S) = ATATTT`.  The distinct `S` read set is
`{0, 1, 3, 5}`; the partner `rc(S)` read set is `{0, 2, 3, 4}`.

There are two readings of `I_s` on the duplex.

**(a) Circle-by-circle.**  `I_s` is applied to each strand separately:

```text
I_s on S     with {0, 1, 3, 5}  :  TRUE   (kernel-checked on main:
                                            SameLengthSection62Counterexample.truth_information_feasible)
I_s on rc(S) with {0, 2, 3, 4}  :  TRUE   (kernel-checked here:
                                            TwoDisjointCirclesDuplex.rcS_information_feasible)
```

So under the circle-by-circle reading the witness **hypothesis side holds** on the
duplex.  [kernel-checked result]

**(b) Duplex-as-a-whole.**  `I_s` is applied to the duplex as a single object of
`2G` positions.  This reading is **not well-defined**: two disjoint circles have
no natural cyclic order, so the interleaving condition of `I_s` (cyclic
alternation of four selected starts, §1.1) has no canonical transcription.
Even *ignoring* interleaving, it is strictly stronger: the duplex carries
**mixed triple repeats** (three positions with equal windows, not all on the same
circle).  The `AAATAT` duplex has `24` mixed triple repeats, of which **six** have
length `≥ L - 1 = 2` and are therefore **unbridgeable** by any length-`3` read
(`bridgesCopy_length`: `e + 2 ≤ L`):

| length `e` | word | copies (circle, start) | preceding | following |
|---|---|---|---|---|
| 2 | `AT` | `(rcS,0), (rcS,2), (S,2)` | `T, T, A` | `A, T, A` |
| 2 | `AT` | `(rcS,2), (S,2), (S,4)` | `T, A, T` | `T, A, A` |
| 2 | `TA` | `(rcS,1), (rcS,5), (S,5)` | `A, T, A` | `T, T, A` |
| 2 | `TA` | `(rcS,5), (S,3), (S,5)` | `T, A, A` | `T, T, A` |
| 3 | `ATA` | `(rcS,0), (S,2), (S,4)` | `T, A, T` | `T, T, A` |
| 3 | `TAT` | `(rcS,1), (rcS,5), (S,3)` | `A, T, A` | `T, A, A` |

Every row is a maximal triple repeat in the source's three-copy sense (the
preceding symbols are not all equal and the following symbols are not all equal),
kernel-checked by `mixed_triple_repeat_2a … _3b`.  Hence under the
duplex-as-a-whole reading the witness **hypothesis side fails** for *every* read
set.  [kernel-checked result + verified computation]

**Verdict.**  The two readings **diverge on the same witness**:
`TwoDisjointCirclesDuplex.two_readings_diverge` kernel-checks that
`I_s` holds circle-by-circle and that a length-`2` mixed triple repeat exists
(hence fails duplex-as-a-whole).  Under the circle-by-circle reading the
`AAATAT → AAAAAT` witness is a genuine counterexample; under the
duplex-as-a-whole reading it is inadmissible.  The circle-by-circle reading is
the well-defined one (§10.2).

### 10.2 Exact compatibility with the oriented single-strand reduction

**Theorem 10.2 (the `rc` symmetry).**  The `rc` map on the circle,
`ρ(i) = (G-1-i) mod G`, is a bijection `S ↔ rc(S)` that reverses the circular
order.  It induces:

* the **read-partner** map `τ_L(t) = (G - t - L) mod G` on length-`L` reads;
* the **copy-partner** map `τ_e(t) = (G - t - e) mod G` on length-`e` copies.

Both are the same underlying position map `ρ`; `ρ` maps a length-`e` window to
the `rc` of a length-`e` window, and because it reverses the order it **preserves
strict interval containment** — i.e. it preserves the bridging relation
`r < t'` and `t' + e < r + L`.  It also swaps the preceding and following
symbols up to `comp`, and the three-copy maximality condition of `IsTripleRepeat`
is symmetric under that swap.  Hence, with `R' = τ_L(R)` the partner read set,

```text
I_s on rc(S) with R'   ⟺   I_s on S with R.
```

[mathematical proof; verified computation on `4800` random instances, binary
`4 ≤ G ≤ 7`, `L = 3`, no counterexample.]

**Corollary 10.3 (exact compatibility).**  Under the circle-by-circle reading,
`I_s` on the V5 duplex is

```text
I_s on S with R   ∧   I_s on rc(S) with τ_L(R)   ⟺   I_s on S with R.
```

So the circle-by-circle V5 model is **exactly compatible** with the oriented
single-strand reduction: it adds no hypothesis beyond `I_s` on `S` itself.  In
particular it removes **R3** as a separate requirement — there is no length-`2G`
circle, so feasibility reduces to `I_s` on the two length-`G` circles, and the
`rc` half is automatic.  [mathematical proof + verified computation]

**Non-compatibility of the other reading.**  The duplex-as-a-whole reading is
*not* compatible: it adds the mixed-triple-repeat conditions of §10.1(b), which
are absent from the single-strand model.  The **additional required hypotheses**
for duplex-as-a-whole compatibility are therefore (i) no mixed triple repeat of
length `≥ L - 1` (or all such bridged), and (ii) a convention for cross-circle
interleaving.  Neither is supplied by the sources.

### 10.3 The candidate set and the effect on the likelihood ratio

Under V5 the candidate is the duplex `(D, rc(D))` for a length-`G` circle `D`; its
duplex spectrum is `spec_D(w) + spec_D(rc(w))` (no seam terms) and its molecule
spectrum is `2·m_D`.  Under V3 the candidate is the length-`2G` circle `D·rc(D)`;
its spectrum is `lint_D(w) + lint_D(rc(w)) + j_D(w)` and its molecule spectrum is
`m_{D·rc(D)}`.

**Effect on the candidate set.**  V5 candidates are length-`G` circles (the same
length universe as the single-strand model), whereas V3 candidates are
length-`2G` circles.  The two candidate spectra differ by
`j_D(w)` versus `wrap_D(w) + wrap_D(rc(D))(w)`, and coincide exactly when **R2**
holds.  In the exhaustive binary scope (`2 ≤ G ≤ 8`, `L = 3`) they coincide for
`254/508` genomes — exactly one half, and exactly half at each `G`:

```text
G = 2: 2/4   G = 3: 4/8   G = 4: 8/16   G = 5: 16/32
G = 6: 32/64  G = 7: 64/128  G = 8: 128/256
```

[verified computation, exhaustive in scope]

**The witness.**  For `D = AAAAAT`, R2 holds, so the V5 and V3 candidate spectra
**coincide**: `{AAA:3, AAT:1, ATA:1, ATT:1, TAA:1, TAT:1, TTA:1, TTT:3}`, with
molecule spectrum `{AAA,TTT}:6, {AAT,ATT}:2, {ATA,TAT}:2, {TAA,TTA}:2`.  The
truth duplex molecule spectrum is exactly `2 × m_S =
{AAA,TTT}:2, {AAT,ATT}:2, {ATA,TAT}:6, {TAA,TTA}:2`.  The factor `2` cancels
between two candidates, so the likelihood ratio is the same as under V1/V2:
**`3`** (exact candidate-intrinsic multinomial) and **`5`** (literal §6.1
fixed-`N` binomial).  [verified computation; the V1/V2 ratios are kernel-checked
on `main`]

**Verdict.**  Under V5 circle-by-circle the witness is a genuine counterexample:
the hypothesis side holds (§10.1a) and `D` beats `S` (§10.3).

### 10.4 Source-faithfulness: V5 vs MB09 vs the Bresler remap

**MB09 counting.**  MB09's read types are unordered reverse-complement
`k`-molecules (§3.1), represented only once (§4.1), so the molecule count sums
`S`-locus occurrences over the **distinct** words of the class: a palindrome
class `{w}` (`w = rc(w)`) is counted **once** (`spec_S(w)`), a non-palindrome
class `{w, rc(w)}` twice (`spec_S(w) + spec_S(rc(w))`).  For odd `L` there are no
palindromes; for even `L` there are (`L = 2`: `AT, TA`; `L = 4`: four).  The V5
duplex molecule spectrum counts windows on **both** strands, so it is exactly
`2 × m_S` for every class, **palindromes included** (each strand contributes one
window).  The factor `2` cancels between two candidates, so the likelihood ratio
is unchanged.  [mathematical proof; verified computation for `L = 2, 3, 4`,
binary scope]  For the witness `L = 3` there are **no** palindromes, so this
subtlety does not touch it.

**V5 is not MB09.**  MB09 uses a single circular genome with
reverse-complement-collapsed read types; V5 uses two disjoint circles.  The
molecule *classes* coincide and the multiplicities are exactly doubled, but the
underlying object is different.

**V5 is not the Bresler remap.**  Bresler maps the duplex to the single
length-`2G` circle `S·rc(S)`; V5 keeps two disjoint circles of length `G`.  The
spectra differ by the seam terms (§10.3), and the candidate sets differ
accordingly.

**The circle-by-circle reading is a modeling decision.**  Neither MB09 nor
Bresler says to apply `I_s` to each strand separately; Bresler explicitly maps to
a single length-`2G` circle.  The circle-by-circle reading is a new choice,
motivated by the two-disjoint-circles representation.  It is exactly compatible
with the single-strand reduction (Corollary 10.3), but it is a **modeling
decision, not a source fact**.  If V5 were presented as "the MB09 model" or "the
Bresler model", it would be a silent hybrid-model identification; presented as a
distinct model with its own assumptions, it is a legitimate algebraic
alternative.  It does **not** settle the 2016 sentence and does **not** settle
V3.

### 10.5 Explicit non-equivalences (audited witnesses)

1. **V5 circle-by-circle vs V5 duplex-as-a-whole.**  The same witness gives
   `I_s = true` circle-by-circle and `I_s = false` duplex-as-a-whole, via the six
   unbridgeable mixed triple repeats of §10.1(b).  The reading of `I_s` on the
   disjoint union is material.
2. **V5 vs V3 spectra.**  `spec_duplex(w) = spec_S(w) + spec_S(rc(w))` (no seam)
   versus `spec_{S·rc(S)}(w) = lint_S(w) + lint_S(rc(w)) + j_S(w)` (seam).  They
   coincide iff R2 holds: `254/508` binary genomes, exactly half.
3. **V5 vs MB09 spectra.**  The V5 duplex molecule spectrum is `2·m_S`, not
   `m_S`.  The factor `2` cancels in the ratio, but the spectra differ.
4. **V5 vs V3 candidate sets.**  V5 candidates are length-`G` circles; V3
   candidates are length-`2G` circles; their spectra differ by the seam terms on
   half the scope.
5. **V5 vs V1/V2 on the hypothesis side.**  V1/V2 keep the read *placements* and
   collapse only the recorded type; V5 circle-by-circle keeps the placements on
   `S` and asserts the `rc` half automatically.  The two agree on the witness
   (§10.1a), but V5 makes the `rc` half a theorem rather than an assertion.
6. **V5 vs V3 on the same witness.**  V5 circle-by-circle: `I_s` holds; V3:
   `I_s` fails (Theorem 3.2).  The witness is a counterexample under V5
   circle-by-circle and inadmissible under V3.

### 10.6 A predicate-soundness note (the corrected mixed-triple test)

The first draft of the mixed-triple evaluator compared a **fixed three** symbol
positions for every repeat length `e`.  That is unsound: for `e = 2` it demands
equal `3`-mers (so *no* length-`2` repeat could ever satisfy it, and the six
length-`2` witnesses above were falsely refuted by `by decide`), and for `e ≥ 4`
it would compare only the first three positions and therefore **under-check**.
The corrected predicate `windowsAgree` compares **exactly `e`** positions
(`(List.range e).all`), with the bounds `1 ≤ e < G` and the exact flanking
maximality retained.  After the fix the six mixed triple repeats were
**re-enumerated from scratch** (`scripts/verify_two_disjoint_circles_duplex.py`
§2) and then kernel-checked.  Two controls pin the fix:

* `not_triple_repeat_control` — `e = 2`, three positions whose length-`2`
  windows do **not** agree on their second symbol → predicate `false` (not
  vacuous);
* `triple_repeat_3_nonvacuous` — `e = 3`, two length-`3` windows agree → `true`
  (the predicate does not collapse to a length-`1` test).

No expected value was patched and no axiom/`sorry` was introduced.  The V5
spectrum identity of §10.0 is independent of this predicate and was unaffected.
[verified computation + kernel-checked result]

### 10.7 Epistemic classification

| claim | status |
|---|---|
| `spec_duplex(w) = spec_S(w) + spec_S(rc(w))`, total `2G`, no seam terms | **mathematical proof** + **verified computation** (exhaustive in scope) |
| read-placement map `t ↦ (G-t-L) mod G` is exact for all `t`, including wrapping | **mathematical proof** + **verified computation** (exhaustive) + **kernel-checked** (`partner_window_rc`) |
| circle-by-circle reading holds on the witness (`I_s` on `rc(S)` with partner reads) | **kernel-checked** (`rcS_information_feasible`) |
| circle-by-circle reading is exactly compatible with the single-strand reduction | **mathematical proof** + **verified computation** (`4800` random instances) |
| duplex-as-a-whole reading fails on the witness (six unbridgeable mixed triple repeats) | **kernel-checked** (`mixed_triple_repeat_2a … _3b`) + **verified computation** |
| the two readings diverge on the same witness | **kernel-checked** (`two_readings_diverge`) |
| V5 and V3 candidate spectra coincide iff R2; `254/508` in scope | **verified computation** (exhaustive in scope) |
| witness is a counterexample under V5 circle-by-circle (ratios `3`, `5`) | **verified computation** + kernel-checked V1/V2 ratios on `main` |
| V5 duplex molecule spectrum is `2·m_S`, palindromes included | **mathematical proof** + **verified computation** (`L = 2, 3, 4`) |
| V5 is not MB09 and not the Bresler remap; circle-by-circle `I_s` is a modeling decision | **modeling decision** (disclosed) |
| which strand convention the 2016 sentence intends | **open** |

### 10.8 Relation to parent #217

V5 is a **third row**, not a refinement of V3.  It does **not** settle the 2016
sentence and does **not** settle the V3 row.  Its contribution to #217 is:
(i) a clean algebraic alternative in which R1/R2/R3 are resolved by construction
under the circle-by-circle reading; (ii) an exact-compatibility theorem for that
reading; (iii) a kernel-checked demonstration that the *other* reading
(duplex-as-a-whole) is both ill-defined and strictly stronger; and (iv) a
kernel-checked witness that the `AAATAT → AAAAAT` counterexample survives under
V5 circle-by-circle while remaining inadmissible under V3.  No verdict may be
aggregated across V3 and V5 without naming the reading.
