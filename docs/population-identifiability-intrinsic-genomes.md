# Population/infinite-read identifiability for intrinsic-admissible primitive genomes

_Status: independent mathematical characterization with an exact-arithmetic
verifier. It settles the **cross-length** part (equal normalized `L`-spectra
force equal length) and then the equal-length part via the classical circular
`q`-gram characterization, here pinned to Bresler–Bresler–Tse 2013, Theorem 3
at `K = L−1`; it records the sharpness of the hypotheses and one
strand-convention boundary. It is **not** a claim that the population regime is
the primary repair of the 2016 question; see §8._

_Reproduction: `python3 scripts/verify_population_identifiability.py`
(self-contained, deterministic, exact `fractions.Fraction`/integer arithmetic,
exits non-zero on failure)._

_This note is independent of, and consistent with, the finite-data packets
[`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md)
and [`issue48-intrinsic-candidate-checks.md`](issue48-intrinsic-candidate-checks.md).
It studies the **optional population question** posed there and in issue #48,
without assuming it is the roadmap's primary repair._

---

## 0. Direct answer

Fix a read length `L ≥ 2`. For a circular genome `D` of length `n`, the
**population read distribution** is

```text
p_D(w) = d_D(w) / n,     d_D(w) = # cyclic occurrences of the length-L word w in D.
```

This is the infinite-read (i.i.d. uniform start) law: it is what the empirical
read distribution converges to, and it is the normalized `L`-mer spectrum.

Let a candidate be **intrinsically admissible** when it satisfies the
candidate-intrinsic shadow of the source read-feasibility condition `I_s`
(called `WEAK` below), and **primitive** when it is not a nontrivial power of a
shorter circular word.

Then:

1. **No, equal population distributions do not force equivalence in general**,
   not even with intrinsic admissibility, unless primitivity is required, and
   not even with primitivity unless *both* sides are intrinsically admissible.
   Exact counterexamples in §6.
2. **Yes, under both hypotheses, on the oriented single-strand panel.** If
   `S, T` are primitive and `WEAK`-admissible and `p_T = p_S`, then
   `|T| = |S|` (proved here, Lemma L* + Theorem P). The remaining equal-length
   step `d_T = d_S ⇒ T` is a cyclic shift of `S` is exactly the classical
   circular `q`-gram characterization (the repo's Conjecture 4, a.k.a. circular
   Ukkonen 1992 / Pevzner 1995) and is stated conditionally. Under the stronger
   hypothesis `STRONG` both steps are unconditional (the de Bruijn support is a
   simple cycle).
3. **Boundary, molecule / reverse-complement panel:** `p_T = p_S` does **not**
   force genome equivalence even for primitive `STRONG` (hence `WEAK`) genomes of
   equal length. Exact counterexample `AACAGT` / `AACTGT` at `L = 3` (§7). So
   the positive answer is tied to the oriented read-type panel.

The exact structural hypothesis is therefore:

> **primitive ∧ intrinsic read-length admissibility, on a read-type panel whose
> selected genome equivalence matches the panel** (cyclic shift for oriented
> reads).

The cross-length exclusion needs only the triple-repeat half of the intrinsic
condition; the equal-length residue needs the interleaved half as well (§3–§5).

---

## 1. Model, definitions, conventions

**Source model (facts used).** Shomorony, Kim, Courtade, Tse 2016 Eq. (1) has a
circular true genome `s` of length `G`, error-free reads of common length `L`
placed at the `G` circular starts, and reconstruction up to cyclic shift
(single-strand oriented panel). The repeat / triple-repeat / interleaving /
bridging vocabulary is Bresler, Bresler, Tse 2013, as recorded in
[`bridging-source-semantics.md`](bridging-source-semantics.md). The likelihood of
Medvedev–Brudno 2009 §6.1 depends on a candidate only through its multiset of
length-`L` windows (its `L`-mer spectrum); see
[`ml-formalization-contract.md`](ml-formalization-contract.md).

**Intrinsic predicates on a single circular word `D` (and `L`).**

- `TRF(D, L)` (**triple-repeat-free**): no Bresler triple repeat of `D` has
  length `≥ L−1` (equivalently, every triple repeat has length `≤ L−2`).
- `ILF(D, L)` (**interleaving-free**): no interleaved maximal-repeat pair of `D`
  has both constituent repeats of length `≥ L−1`.
- `WEAK(D, L) = TRF(D, L) ∧ ILF(D, L)`: the candidate-intrinsic shadow of the
  source condition `I_s` at the full read set. A copy of length `ℓ` is
  bridgeable by a length-`L` read (strictly on both sides) only if `ℓ ≤ L−2`, so
  "the full read set lies in `I_s`" is exactly `TRF ∧ ILF`.
- `STRONG(D, L)`: no `(L−1)`-mer of `D` occurs twice.
- `primitive(D)`: `D ≠ C^k` for every `k ≥ 2` and shorter circular `C`.

Implications: `STRONG ⇒ TRF` and `STRONG ⇒ ILF` (a long triple or interleaved
obstruction forces a repeated `(L−1)`-mer), hence `STRONG ⇒ WEAK`. The
cross-length theorem below needs only `TRF`; the equal-length residue needs the
full `WEAK`.

**Normalized spectrum.** Two words have the same population read distribution
iff `d_T(w)/|T| = d_S(w)/|S|` for every `w`, equivalently `d_T = c · d_S` for
some rational `c > 0`. This forces equal support (so, in particular, equal
`(L−1)`-mer support) and `|T| = c |S|`. The relation `c = 1` is the
equal-length, equal-`L`-mer-spectrum case.

**Equivalence.** Oriented panel: cyclic shift. Molecule panel (`k`-molecule
classes): cyclic shift together with reverse complement (dihedral). The panel is
part of the claim, not an afterthought (§7).

**Tie semantics.** A strict likelihood gap is not needed here: this note is
about a *combinatorial injectivity* statement (the fibres of `D ↦ p_D`), which
is prior to any tie rule.

---

## 2. Why identifiability is the right population question

**Proposition 1 (population consistency; mathematical proof).** Fix a candidate
length `G`. Let `p = d_S/G`. For every length-`G` circular candidate `D` with
`q_D = d_D/G`,

```text
ell_pop(D) := Σ_w p(w) log q_D(w)
           = -H(p) - KL(p ‖ q_D) ≤ -H(p) = ell_pop(S),
```

with equality iff `d_D = d_S` (Gibbs' inequality; `ell_pop(D) = -∞` if a
`p`-positive type is absent from `D`).

Consequently the infinite-read maximum-likelihood *spectrum* is the true
spectrum. The only remaining question is whether the optimal spectrum
determines the genome among the permitted candidates, i.e. whether `D ↦ p_D` is
injective up to genome equivalence on the candidate class. That is the question
answered in §4–§5. (The observation-only multinomial coefficient is
candidate-independent and is dropped; the fixed-`N` binomial approximation
shares the same per-type maximization `q_D = p`.)

Nothing in Proposition 1 uses bridging: concentration makes the true spectrum
optimal, and the repeat/admissibility hypothesis is exactly what upgrades
"optimal spectrum" to "true sequence". This mirrors the decomposition already
recorded for issue #45.

---

## 3. Lemma L* (the key structural bound)

**Lemma L*.** If `D` is primitive and `TRF`-admissible at read length `L`, then
every `(L−1)`-mer of `D` occurs at most twice. (A fortiori for `WEAK`.)

**Proof.** Suppose an `(L−1)`-mer `v` occurs at three distinct starts
`t₁, t₂, t₃`. Let `ℓ ≥ L−1` be the length of the maximal common right extension
of the three copies (extend to the right while the three next symbols agree).
Then the three windows of length `ℓ` at `tᵢ` are equal, and the symbols at
`tᵢ + ℓ` are not all equal.

Now extend to the left: let `j*` be the largest `j ≥ 0` such that the three
windows `D[tᵢ − j, tᵢ + ℓ)` of length `ℓ + j` are all equal. Such a `j*` exists
and satisfies `ℓ + j* < n`: if the common extension reached length `n`, then
three equal windows of length `n` at distinct starts would give `D` a nontrivial
period, contradicting primitivity. Moreover `ℓ + j* ≥ L−1`.

At `j*`, the three equal windows have length `ℓ + j* ≥ L−1`; their **following**
symbols (at `tᵢ + ℓ`) are not all equal by maximality of `ℓ`, and their
**preceding** symbols (at `tᵢ − j* − 1`) are not all equal because `j*` is
maximal on the left. This is a Bresler triple repeat of length `≥ L−1`, i.e. of
length `> L−2`, contradicting `TRF(D, L)`. ∎

_Epistemic class: mathematical proof. Exhaustively verified for the stated
ranges by section B of the verifier (max observed `(L−1)`-mer multiplicity
among primitive `TRF` words is exactly `2`, and `2` is attained, e.g. `AA` in
`AAAB` at `L = 3`). This lemma is the candidate-intrinsic reason the normalized
spectrum cannot scale: it caps the `(L−1)`-mer multiplicities at `2`, which is
incompatible with a scale factor `c > 1` unless the word is a power. Only the
triple-repeat half of the intrinsic condition is used._

---

## 4. Theorem P (cross-length exclusion)

**Theorem P.** Let `S, T` be primitive circular words, both `TRF`-admissible at
read length `L`, with `d_T = c · d_S` for a rational `c > 0`. Then `c = 1`; in
particular `|T| = |S|`. (A fortiori with `WEAK` in place of `TRF`.)

**Proof.** Assume `c > 1`. Write `a_v, b_v` for the multiplicity of an
`(L−1)`-mer `v` in `S`, `T`, so `b_v = c a_v`. By Lemma L*, `a_v ≤ 2` and
`b_v ≤ 2`. For every `v` in the common support, `a_v ≥ 1`, so
`a_v = b_v / c ≤ 2 / c < 2`, hence `a_v = 1` and `b_v = c`. Since `b_v` is a
positive integer `≤ 2` and `c > 1`, we get `c = 2`, and every `(L−1)`-mer of `S`
occurs exactly once.

A word in which every `(L−1)`-mer occurs exactly once has every `L`-mer also
occurring exactly once (a repeated `L`-mer would repeat its `(L−1)`-prefix), and
its `(L−1)`-mer de Bruijn support has in-degree and out-degree `1` at every
vertex. Because `S` is one closed walk, that support is a single directed cycle,
so `S` is the unique Eulerian circuit, i.e. the cycle word up to rotation.
`T` traverses the same support with every edge doubled in parallel; every vertex
still has a **unique distinct outgoing edge**, so the Eulerian circuit is forced
and `T` is the corresponding power of that cycle word up to rotation — a
nontrivial power, contradicting primitivity of `T`. Hence `c = 1`. ∎

_Epistemic class: mathematical proof. Independently verified by section C1 of
the verifier: `46 517` primitive `TRF` words (alphabets `{A,B}`, `{A,B,C}`,
`{A,B,C,D}`; stated ranges) have **no cross-length proportional collision**.
This is evidence for the bounded ranges, but the proof above is unconditional.
Note that `TRF` alone does allow same-length spectral ties (e.g.
`AABABB`/`AABBAB` at `L=3`, which fail `ILF`), so `TRF` is exactly enough for the
cross-length step and not for the equal-length one._

**Corollary (cross-length part of the positive answer).** For primitive
`TRF`-admissible `S`, any primitive `TRF`-admissible `T` with the same
population read distribution has the same length and the same `L`-mer spectrum.

---

## 5. The equal-length residue: classical characterization

Theorem P reduces the population question to the case `|T| = |S|`,
`d_T = d_S`. There, `p_T = p_S` is just equality of `L`-mer multisets, and the
statement "the `L`-mer multiset determines an admissible word up to cyclic
shift" is the repository's **Conjecture 4**
(`mathematics/bridging-and-spectrum-uniqueness.md` §5). It is the `K = L−1`
instance of the classical Ukkonen 1992 / Pevzner 1995 `q`-gram characterization
in the accepted maximal-repeat restatement of **Bresler–Bresler–Tse 2013,
Theorem 3** (`K`-mer graph from the `(K+1)`-spectrum; unique Eulerian cycle iff
there is no triple or interleaved repeat of length `≥ K`). Bresler–Bresler–Tse
define repeats as *maximal* and the length of a pair of interleaved repeats as
the shorter constituent, so `WEAK = TRF ∧ ILF` is literally "no triple or
interleaved repeat of length `≥ L−1`"; the circular reading is cyclic-shift
equivalence. See
`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`.

Status of this step: **source theorem** (Bresler–Bresler–Tse 2013, Thm 3 at
`K = L−1`), modulo the circular Eulerian-cycle reading and the condensed-graph
nuance recorded in that note. The earlier anchor on Çelikkanat et al. (2024,
Theorem 3.1) was a linear, non-maximal restatement and is not used here; the
`123 906`-instance exhaustive check (re-run 2026-09-21, 0 ambiguous) is
corroboration. Primitivity is not required for this equal-length step; it is
needed only for the cross-length Theorem P. The equal-length conclusion is
therefore unconditional; the cross-length conclusion was already unconditional.

Here the interleaved half `ILF` is genuinely needed: the same-length pair
`AABABB` / `AABBAB` (`L = 3`) is primitive and `TRF` (no long triple repeat) but
not `ILF`, has the same `L`-mer spectrum, and the two are not rotations. So
`TRF` alone does not force equal-length uniqueness, while `WEAK = TRF ∧ ILF`
is exactly the classical obstruction-exclusion hypothesis.

**Claim (source theorem; Bresler–Bresler–Tse 2013, Thm 3 at `K = L−1`).** For
primitive `WEAK`-admissible circular genomes on the oriented panel, equal
population read distributions imply cyclic-shift equivalence.

---

## 6. The hypotheses are sharp

Each hypothesis of §4/§5 is necessary; the verifier checks all three exactly
(section D).

1. **Primitivity cannot be dropped, even with `WEAK` on both sides.**
   `S = AAB` (`L = 3`) is primitive and `WEAK`; `T = S² = AABAAB` is still
   `WEAK` and has the same population law, but is a nontrivial power and not a
   rotation of `S`. (Shorter: `AB` / `ABAB` at `L = 2`.) So `WEAK` alone does
   not exclude the tandem/scale ambiguity.
2. **Candidate-side admissibility cannot be dropped.** The primitive `WEAK`
   truth `S = AAAB` (`L = 3`) and the **primitive but not `TRF`** (hence not
   `WEAK`) `T = AAAABAAB` have the same population law and are not rotations.
   (Shorter: `AAB` / `AAABAB` at `L = 2`.) The scale factor here is `2` and the
   obstruction is a triple repeat of length `L−1`; Lemma L* is exactly what
   fails for `T`. A separate reminder that population and finite-support
   failures differ: `S = AAAB` / `T = AAABAB` (`L = 3`) are both primitive
   `WEAK` but have *different* population laws (extra type and doubled `ABA`),
   yet the shorter `T` wins a skewed finite sample — a finite-support effect,
   not a population non-identifiability.
3. **`STRONG` makes the whole statement unconditional.** If `S` has no
   repeated `(L−1)`-mer then its de Bruijn support is a simple directed cycle
   (one incoming and one outgoing distinct edge per vertex), `S` is that cycle
   word, every proportional partner is that cycle traversed an integer number
   of times, and primitivity forces the multiplier `1`. So for primitive
   `STRONG` `S`, `p_T = p_S` implies `T` is a cyclic shift of `S` with no appeal
   to the classical equal-length characterization (section F). The classical
   residue is only needed for the weaker `WEAK` hypothesis, where the support
   may branch.

---

## 7. Strand-convention boundary: the molecule panel

On the oriented panel the read type is the exact `L`-mer. On the
double-strand / `k`-molecule panel the read type is the reverse-complement
class, and genome equivalence becomes dihedral. The positive answer of §5 does
**not** transfer.

**Exact counterexample.** `S = AACAGT`, `T = AACTGT`, `L = 3`. Both are
primitive and `STRONG` (all `2`-mers distinct). Their molecule-class length-`3`
distributions are equal (each of the six classes has weight `1/6`), yet `T` is
neither a cyclic shift nor a reverse-complement rotation of `S` (which itself is
not reverse-complement symmetric). Hence on the molecule panel even
primitive `STRONG` equal-length genomes with the same population read
distribution need not be equivalent. This is a same-length phenomenon, and it
shows the panel's equivalence/characterization is a genuinely separate input.

_Epistemic class: exact verification (section E). This is independent evidence
for the boundary already noted in the issue-#48 comments, reproduced here with
the exact words and the exact class spectrum._

---

## 8. Relation to issues #48 and #45; non-claims

- **#48 (finite-data model repair).** The finite packets show the truth need not
  be ML under free candidate length, because the free-length normalization
  rewards a shorter candidate — a cross-spectrum effect. The population result
  here is **compatible** with that negative: it says the obstruction is removed
  only when the data are the population law, and even then only after fixing the
  candidate class by primitivity + intrinsic admissibility. It does **not**
  repair the finite statement.
- **#45 (population / infinite-read analogue).** This note characterizes the
  identifiability half of the population analogue. It is deliberately presented
  as an independent characterization, **not** as the roadmap's primary repair:
  issue #48's entry condition for #45 must be decided by the finite picture, and
  nothing here asserts it.
- **Non-claims.** No claim about the fixed-`N` binomial objective beyond
  Proposition 1; no claim about the §6.2 flow-feasible candidate class; no claim
  about non-uniform or non-i.i.d. sampling. The equal-length step is attributed
  to Bresler–Bresler–Tse 2013, Theorem 3 (`K = L−1`) under the circular
  Eulerian-cycle reading; the source-fidelity discussion and residual limits are
  in `docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`.
- **Concurrent-work reconciliation (named branch artifacts, not links).** The
  independent synthesis packet `docs/synthesis-finite-rows-and-repairs-2026-09-21.md`
  states the same population consistency (its Lemma 4.1) and the same cross-length
  conclusion ("population ties ⇔ proportional spectra; cross-length `c>1`
  impossible for primitive `P2`"), attributing the latter to the issue-#48
  Theorem P. This note independently re-proves it and sharpens the hypothesis to
  `TRF` (the interleaved clause is not needed for the cross-length step), adds
  the sharpness counterexamples and the molecule-panel boundary, and makes no
  claim about the finite-data branch. The independent packet
  `docs/source-notes/candidate-intrinsic-admissibility.md` reaches the
  finite-support conclusion that `S=AAAB`, `D=AAABAB` (`L=3`) is not excluded by
  intrinsic checks; that pair is **not** a population collision (its spectra are
  not proportional), consistent with Theorem P.

---

## 9. Computational evidence and reproduction

`scripts/verify_population_identifiability.py`, exact arithmetic:

| Section | Check | Scope | Result |
|---|---|---|---|
| A | population objective maximized at `d_S` | `|Σ|≤3`, `G ≤ 6` | pass |
| B | Lemma L*: `(L−1)`-multiplicity `≤ 2` under `TRF` | `{A,B}` `n ≤ 15`, `L ≤ 5`; `{A,B,C}` `n ≤ 11`, `L ≤ 4` | max `= 2` |
| C1 | no cross-length proportional collision, primitive `TRF` | `46 517` words over alphabets 2–4 | 0 collisions |
| C2 | no same-length collision, primitive `WEAK` | `26 991` words, `26 991` spectra | 0 collisions |
| D | primitivity and candidate admissibility both necessary | explicit exact witnesses | pass |
| E | molecule panel `AACAGT`/`AACTGT` | exact rationals | same law, dihedrally inequivalent |
| F | `STRONG` truth ⇒ proportional partners are powers | `{A,B}` `n ≤ 10`, `L ≤ 3` | pass |

The exhaustive ranges are bounded, so B/C1/C2 are finite evidence; Lemma L*
and Theorem P are proved above, and A and F are proved (Proposition 1; §6.3).

---

## 10. Epistemic summary

| Claim | Status | Basis |
|---|---|---|
| Proposition 1: infinite-read spectrum optimum is `d_S` | **Proven** | Gibbs/KL |
| Lemma L*: primitive `TRF` ⇒ `(L−1)`-multiplicity `≤ 2` | **Proven** + bounded check | maximal-extension triple-repeat argument |
| Theorem P: primitive `TRF` + proportional spectra ⇒ `c = 1` | **Proven** + bounded check | Lemma L* + forced Eulerian circuit |
| Equal length ⇒ cyclic shift (oriented) | **Source theorem** (circular Eulerian-cycle reading) | Bresler–Bresler–Tse 2013, Thm 3 at `K=L−1` (maximal-repeat convention); `docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md` |
| `TRF` alone is not enough for equal length | **Refuted** | `AABABB` / `AABBAB`, `L=3` (fail `ILF`) |
| Primitivity necessary | **Refuted without it** | `AAB` / `AABAAB`, `L=3` |
| Candidate admissibility necessary | **Refuted without it** | `AAAB` / `AAAABAAB`, `L=3` |
| Molecule-panel positive transfer | **False** | `AACAGT` / `AACTGT`, `L=3` |
| Population is the primary repair | **Not claimed** | §8 |

---

## 11. Sources and anchors

| Item | Source / anchor |
|---|---|
| `I_s` (coverage, all-bridged triples, bridged interleaved); circular truth; cyclic-shift target | Shomorony, Kim, Courtade, Tse, *Bioinformatics* 32(17):i494–i502, 2016, Eq. (1); [`bridging-source-semantics.md`](bridging-source-semantics.md) |
| Repeat / triple repeat / interleaving / maximality / strict bridging | Bresler, Bresler, Tse, *BMC Bioinformatics* 14(Suppl 5):S18, 2013 |
| Likelihood depends on candidate through length and `L`-mer spectrum | Medvedev, Brudno, *J. Comput. Biol.* 16(8), 2009, §6.1; [`ml-formalization-contract.md`](ml-formalization-contract.md) |
| Circular `q`-gram characterization (used here) | Bresler, Bresler, Tse, *BMC Bioinformatics* 14(Suppl 5):S18, 2013, Thm 3 (maximal repeats; `K = L−1`); origin: Ukkonen, *Theoret. Comput. Sci.* 92(1):191–211, 1992; Pevzner, *Algorithmica* 13(1–2):77–105, 1995; linear restatement: Çelikkanat, Masegosa, Nielsen, NeurIPS 2024, Thm 3.1 (arXiv:2411.02125). See [`docs/literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md) |
| Full-read reduction (`I_s` shadow = `WEAK`) | repository derivation; [`issue48-intrinsic-admissibility-counterexample.md`](issue48-intrinsic-admissibility-counterexample.md) §3 |
| Issue #48 (intrinsic candidate checks; optional population question) | GitHub issue #48; [`issue48-intrinsic-candidate-checks.md`](issue48-intrinsic-candidate-checks.md) |
| Issue #45 (population / infinite-read repair) | GitHub issue #45 |
| Verifier | `scripts/verify_population_identifiability.py` |
