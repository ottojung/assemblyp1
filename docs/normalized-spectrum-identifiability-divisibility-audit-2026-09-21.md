# Normalized-spectrum identifiability: a divisibility/Eulerian audit

_Status: independent derivation and edge-case audit for issue #45, 2026-09-21.
It re-derives the normalized-spectrum identifiability theorem from the one-sided
ordinary circular `q`-gram uniqueness statement plus primitivity, checking the
divisibility and Eulerian-spelling steps in detail; it gives a new pure-
divisibility proof of the cross-length half via a gcd lemma; and it audits the
edge cases (periodicity, `L`, alphabet, disconnected support, parallel edges).
It corrects one claim in a concurrent packet. It is a statement about the fibre
of `D ↦ p_D`; it does **not** settle the finite-sample 2016 question of
[`open-problem.md`](open-problem.md)._

_Reproduce: `python3 scripts/verify_normalized_spectrum_divisibility.py`
(≈ 2 s) and `... --full` (≈ 30 s). Exact integer / `fractions.Fraction`
arithmetic, deterministic, self-contained, exits non-zero on failure._

_Independence. This note shares no code with
`scripts/verify_population_identifiability.py`,
`scripts/verify_population_independent.py`, or
`scripts/bridging_spectrum_uniqueness.py`. The gcd lemma of §3.3 and the
scaling audit of §4.2 are new here; the cross-length proof of §3.2–§3.4 is a
different (purely divisibility-theoretic) proof from the Eulerian-support proof
already recorded on this branch._

---

## 0. Verdict

Fix a finite alphabet `Σ` and read length `L ≥ 2`. For a circular word `D` let
`d_D(w)` be the number of cyclic starts whose length-`L` window is `w`, and
`p_D(w) = d_D(w)/|D|` the normalized `L`-mer spectrum (population read law).

**Theorem (normalized-spectrum identifiability, minimal hypotheses).** If
`S` is primitive and `WEAK(S,L)`, and `T` is primitive and `TRF(T,L)`, then

```text
p_T = p_S   ==>   |T| = |S|, d_T = d_S, and T is a cyclic shift of S.
```

`TRF` = no Bresler triple repeat of length `≥ L−1`; `ILF` = no interleaved pair
of maximal repeats whose shorter constituent has length `≥ L−1`;
`WEAK = TRF ∧ ILF`. When the candidate class is restricted to length `|S|`,
primitivity and `TRF` on the rival are not needed.

**The claim is true.** No flaw and no counterexample was found. The derivation
splits into exactly two independent statements:

1. **Scale rigidity** (no proportional mate): supplied by `TRF` + primitivity.
   §3 proves this by pure divisibility after a new gcd lemma. This is where
   every divisibility step lives.
2. **Equal-length injectivity**: supplied by ordinary circular `q`-gram
   uniqueness when `S` is `WEAK` (a one-sided source theorem, §2). This is
   where the Eulerian/spelling content lives.

The two pieces are logically independent, and this is the cleanest statement of
what issue #45 leaves open: nothing, once the ordinary circular characterization
is accepted for the reference word.

---

## 1. Setup and definitions

A circular word `D` has length `n = |D| ≥ 1`; all indices are cyclic. `win_L(D,i)`
is the length-`L` window at start `i`, and

```text
d_D(w) = #{ i ∈ Z_n : win_L(D,i) = w },   p_D(w) = d_D(w)/n.
```

Summing gives `Σ_w d_D(w) = n`. `D` is **primitive** if `D ≠ C^k` for every
`k ≥ 2` and shorter circular `C`; primitivity is rotation-invariant.

Bresler repeat vocabulary (as in
[`bridging-source-semantics.md`](bridging-source-semantics.md) and quoted in
[`literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md)):

* a maximal repeat pair of length `ℓ` is a pair of starts `t₁ ≠ t₂` whose
  length-`ℓ` windows agree, with `D[t₁−1] ≠ D[t₂−1]` and `D[t₁+ℓ] ≠ D[t₂+ℓ]`;
* a triple repeat of length `ℓ` is three starts with equal length-`ℓ` windows,
  the three preceding symbols **not** all equal, and the three following
  symbols **not** all equal;
* an interleaved pair is two maximal repeat pairs whose four starts alternate
  (`t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃`); its length is the shorter
  constituent.

`TRF(D,L)`: no triple repeat of length `≥ L−1`. `ILF(D,L)`: no interleaved pair
of maximal repeats of length `≥ L−1`. `WEAK = TRF ∧ ILF`; `STRONG`: no
`(L−1)`-mer occurs twice (`STRONG ⇒ WEAK`).

Two normalized spectra agree iff `d_T(w)/|T| = d_S(w)/|S|` for all `w`, i.e.

```text
d_T = c · d_S,   c = |T| / |S| ∈ ℚ_{>0}.                    (∗)
```

The oriented panel has cyclic-shift equivalence; the molecule panel has
dihedral equivalence and is a genuine boundary (§5.4).

---

## 2. The one-sided ordinary circular `q`-gram uniqueness statement

Everything combinatorial that this note does **not** prove is the following
published statement (COU).

> **COU.** If `S` is `WEAK`-admissible at read length `L`, then every circular
> word `T` with `|T| = |S|` and `d_T = d_S` is a cyclic shift of `S`.

This is Bresler–Bresler–Tse 2013, Theorem 3 at `K = L−1`, under the circular
Eulerian-cycle reading; see
[`literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md)
for the exact quoted statement and the residual reading qualifications. Two
features matter here and are used below:

1. **One-sidedness.** Only the reference word `S` must satisfy Ukkonen's
   condition; the rival `T` need not. The theorem says the condensed `(L−1)`-mer
   graph built from `S`'s `L`-spectrum has a unique Eulerian cycle, which spells
   `S`; any same-spectrum same-length `T` is another Eulerian cycle in the same
   graph, hence the same cycle. This is the form of the repository's Conjecture 4
   and of BBT Theorem 3.
2. **Circularity.** BBT state the conclusion as a unique **Eulerian cycle**
   (condensed `K`-mer graph) corresponding to `s`, not as a unique Eulerian
   path. The linearization `X = S · prefix_{L−1}(S)` has
   `prefix_{L−1}(X) = suffix_{L−1}(X)`, so it deliberately manufactures a linear
   boundary obstruction; the linear restatements (Çelikkanat et al. 2024,
   Theorem 3.1) are therefore not a substitute for COU. BBT's own statement is
   the cyclic/Eulerian-cycle one.

`COU` is recorded here as a source theorem modulo the circular reading; the
finite checks of §6 corroborate its use but do not prove it. The status is the
same as on the existing packets and is not upgraded here.

---

## 3. Scale rigidity by pure divisibility

### 3.1 Counting facts

For a circular word `D`, let `mult_D(v)` be the number of occurrences of the
`(L−1)`-mer `v`. Then (both sides count starts whose predecessor window is `v`)

```text
mult_D(v) = Σ_{w : prefix_{L−1}(w) = v} d_D(w),           (Fact 1)
```

and the de Bruijn multigraph of `D` (vertices `(L−1)`-mers, edges `L`-mers) is
balanced at every vertex: out-degree `= in-degree = mult_D(v)`. This balance is
what makes the scaling in §4 legitimate.

### 3.2 Lemma L\* (multiplicity cap)

> **Lemma L\*.** If `D` is primitive and `TRF(D,L)`, then every `(L−1)`-mer
> occurs at most twice.

_Proof._ Suppose `v` occurs at three distinct starts `t₁,t₂,t₃`. Extend the
three copies maximally to the right to a common length `ℓ ≥ L−1`; the three
following symbols are not all equal. The extension cannot reach length `n`: three
equal length-`n` windows at distinct starts make `D` invariant under the nonzero
rotation `t₂ − t₁`, hence a nontrivial power, contradicting primitivity. Extend
maximally to the left to `j* ≥ 0`, i.e. the three windows of length `ℓ + j` at
`tᵢ − j` are equal for `j ≤ j*` and their preceding symbols are not all equal;
again `ℓ + j* < n` by the same period argument. So the three equal windows of
length `ℓ + j* ≥ L−1` have both flanks non-degenerate: a Bresler triple repeat
of length `≥ L−1`, contradicting `TRF`. ∎

The bound is attained (`AA` twice in `AAAB`, `L = 3`); primitivity is essential
(a power `(AB)^m` has `AB` `m` times). Only `TRF` is used.

### 3.3 The gcd lemma

> **Lemma (gcd).** If `D` is primitive and `TRF(D,L)`, then the gcd of the
> positive `L`-mer multiplicities `d_D(w)` is `1`.

_Proof._ Let `g = gcd_w d_D(w)` and suppose `g > 1`, so `d_D = g·e` with `e` a
nonnegative integer vector having `Σ_w e_w = n/g`. By (Fact 1) and Lemma L\*,
for every support vertex `v`

```text
0 < mult_D(v) = g · Σ_{prefix_{w}=v} e_w  ≤  2.            (†)
```

If `g ≥ 3`, (†) is impossible since the middle quantity is a positive multiple
of `g`. Hence `g = 2`, and then (†) forces `mult_D(v) = 2` and
`Σ_{prefix_w=v} e_w = 1` for every support `v`; in particular every positive
`e_w` equals `1`. So each support vertex has a **unique** outgoing support edge,
and by balance a unique incoming one.

Now the window sequence `W_i = win_L(D,i)` satisfies `W_{i+1} = f(W_i)` where
`f(w)` is the unique support `L`-mer with prefix `suffix(w)`; `f` is a bijection
of the support. Since `D`'s window walk visits every support `L`-mer (with
multiplicity `d_D`, i.e. `2` for all of them), the orbit of `f` must be the whole
support. Its cycle length is the number `|support| = Σ_w e_w = n/2`, so
`W_{i+n/2} = W_i`: `D` is the square of the word spelled by one turn of the
cycle, a contradiction to primitivity. Hence `g = 1`. ∎

_Remark._ This lemma was not recorded on the sibling packets. It says a
primitive `TRF` genome has **spectrally coprime** window counts, so it cannot
secretly be a uniform `k`-fold cover. It gives an alternative, purely
arithmetic route to Theorem P (below). The independent checks in §6 confirm
`gcd = 1` on `≈ 35 600` primitive-`TRF` instances with zero exceptions (and on
`≈ 455 000` in the wider scratch run of the same predicate).

### 3.4 Cross-length exclusion

> **Theorem P.** Let `S,T` be primitive `TRF` circular words with
> `d_T = c · d_S` for a rational `c > 0`. Then `c = 1`.

_Proof._ Write `c = a/b` in lowest terms. Then `b · d_T = a · d_S`, so
`gcd(a,b) = 1` gives `b | d_S(w)` for every `w`. By the gcd lemma on `S`,
`gcd_w d_S(w) = 1`, hence `b = 1`, i.e. `c = a` is a positive integer. Then
`a | d_T(w)` for every `w`, and the gcd lemma on `T` gives `a = 1`. ∎

This is a purely arithmetic proof; it uses only Lemma L\* and (Fact 1). It may
be compared with the Eulerian-support proof on the sibling packets (which
concludes `c = 2` and then that the rival is forced to be a square). The two
proofs are both valid but not equally strong:

* the Eulerian-support proof needs primitivity and `TRF` only on the
  **larger-spectrum side** (for `c > 1`, the side `T`), because it works from
  that side's multiplicity cap alone;
* the divisibility proof above is symmetric and needs the gcd lemma on **both**
  sides.

So the divisibility route is the conceptually simplest but the Eulerian route
is the sharper one; the combined theorem uses only the latter's hypothesis on
the candidate (`TRF` on `T`, §4.1).

---

## 4. The normalized-spectrum theorem

### 4.1 Assembling the theorem

> **Theorem.** Let `S` be primitive `WEAK` and `T` primitive `TRF` with
> `p_T = p_S`. Then `|T| = |S|`, `d_T = d_S`, and `T` is a cyclic shift of `S`.

_Proof._ `p_T = p_S` is (∗). Theorem P (§3.4, using `WEAK ⇒ TRF` on `S`) gives
`c = 1`, hence `|T| = |S|` and `d_T = d_S`. COU (§2) with reference `S` gives
that `T` is a cyclic shift of `S`. ∎

For the same-length candidate class, `c = 1` is automatic and `T =` rotation of
`S` follows from COU directly, with no primitivity or `TRF` on `T`; §5.5 records
that these hypotheses are sharp.

### 4.2 The scaling/divisibility audit (issue-#45 reduction)

The reduction circulated in issue #45 runs in the other direction, deriving
primitivity's effect through COU rather than through Lemma L\*. It is worth
auditing because it is the statement that was flagged as possibly defective.

Let `|T|/|S| = a/b` in lowest terms. From (∗), `b · d_T = a · d_S`; since
`gcd(a,b) = 1`, `b | d_S`. Set `e = d_S / b`, an integer vector with

```text
support(e) = support(d_S)   and   Σ_w e_w = |S|/b.
```

Because `d_S` is balanced (Fact 1) and scaling preserves balance, `e` is
balanced on the same support; the support of a single circular word's window
walk is connected. Hence `e` is the `L`-mer spectrum of some circular word `T₀`
(an Eulerian circuit of the de Bruijn multigraph spells it). Then

```text
d_{T₀^b} = b · e = d_S   and   |T₀^b| = b · |S|/b = |S|.
```

By COU with reference `S`, `T₀^b` is a cyclic shift of `S`, so `S` is a `b`-th
power; primitivity of `S` forces `b = 1`. Now `c = a` is an integer and
`d_T = a·d_S`. Applying the same argument with the roles of `S` and `T`
exchanged (and `e' = d_T/a`) gives `a = 1`. Hence `|T| = |S|`, `d_T = d_S`, and
COU gives `T ~ S`.

Every step was checked independently in §6 [E]: for each reduced vector arising
from a primitive word, `spell(e)` returned a word with the exact spectrum `e`,
and `T₀^b` matched `d_S` in both spectrum and length.

**Correction to the record.** The concurrent packet
`docs/source-notes/population-ml-theorem-independent-derivation.md` (branch
`agent/population-ml-theorem-independent-0921`) §4 writes that the
scaling argument above "silently needs the *one-sided* statement" that any word
with the same spectrum as the admissible `S` is a rotation of `S`, because
`T₀^b` need not be admissible. That is not a defect: the one-sided statement is
exactly COU as proved/used on this branch, and it *is* the form in which the
repository's Conjecture 4 and BBT Theorem 3 are stated. The direct Lemma L\*
proof in that packet is a genuine strengthening (it relaxes the rival from
`WEAK` to `TRF`), but it does not repair a gap in the scaling argument. Both
routes are valid.

---

## 5. Edge cases

### 5.1 `L = 1` is genuinely excluded

At `L = 1` the notion `(L−1) = 0`-mer is degenerate and COU is false. Counter-
example: `S = ABC` and `T = ACB` are primitive, have the same `1`-mer
spectrum (`{A:1,B:1,C:1}`), and are not rotations. The theorem is therefore
stated for `L ≥ 2`; this matches the source model, where reads are length
`L ≥ 2`. (The independent check [G] verifies the counterexample.)

### 5.2 Periodicity / primitivity

Primitivity is essential in both directions, and the failure is purely a
primitivity failure when the shorter word is `STRONG`. Take `U = AAB` (`L = 3`),
which is primitive `STRONG` (the `2`-mers `AA, AB, BA` are distinct); then
`U² = AABAAB` is `WEAK` (its `(L−1)`-multiplicities are all `2` and it has no
non-periodic maximal interleaved obstruction) yet not primitive, and
`p_{U²} = p_U`. So neither `S = U²` nor `T = U²` is allowed: primitivity cannot
be dropped on either side even with `WEAK` on both. The gcd lemma's `g = 2`
branch is exactly the case in which the word is a square.

The `TRF ⟺ (L−1)-multiplicity ≤ 2` equivalence (Lemma L\*) also needs
primitivity: for periodic `AAA` at `L = 2` the maximal triple is vacuous while
the `1`-mer `A` occurs three times. Check [A] confirms the equivalence for all
primitive words in range.

### 5.3 Alphabet

Nothing in §§3–4 uses the alphabet beyond finiteness. For `|Σ| = 1` the only
primitive word is the single letter, and the theorem holds vacuously/trivially.
The witnesses of §5.5 use `|Σ| ≥ 2`; the gcd lemma and Theorem P are alphabet-
independent.

### 5.4 `L > |D|` (read longer than the genome)

If `L ≥ n` the length-`L` window at a start determines the whole circular word,
so COU holds trivially and `TRF`/`ILF` are vacuous. The scaling argument still
applies. No collision exists. (Check [D] includes `L` down to `2` for `n` as
small as `1`; no cross-length collision.)

### 5.5 Sharpness of the hypotheses

| hypothesis dropped | `S` | `T` | `L` | why it fails |
|---|---|---|---|---|
| `T` or `S` primitivity | `AAB` | `AABAAB = S²` | 3 | `p_T = p_S`; here `T` is a square, and by symmetry `S` may be the square; both sides are `WEAK`, so this is a pure primitivity failure |
| `TRF(T)` | `AAAB` | `AAAABAAB` | 3 | `p_T = p_S`, `T` primitive but not `TRF` |
| `WEAK(S)` (only `TRF(S)`) | `AABABB` | `AABBAB` | 3 | equal spectrum, both primitive `TRF`, not `ILF`, not rotations |
| candidate length fixed to `|S|` | — | — | — | then `TRF`/primitivity on `T` are not needed (§4.1) |

All four rows are verified exactly in check [G].

### 5.6 Disconnected support, parallel edges, and the BEST caveat

The Eulerian-spelling step in §4.2 is used only for the **scaled-down** vector
`e = d_S/b` whose support equals the support of `d_S`, which is connected
because it is the support of the single closed window walk of `S`. So the
spelling always succeeds; check [E] confirms it on every reduced vector in
range. A general nonnegative integer vector can of course have disconnected
support and then need not be spellable — that case cannot arise here.

Parallel edges are harmless for spelling but must be handled at the level of
**spelled words**, not raw Eulerian cycles: the raw de Bruijn multigraph can
have more than one Eulerian circuit that spells the same word (`AABAB`, `L = 3`,
two parallel `ABA` edges). COU is a statement about the spelled sequence, and
the repository's `P2 ⇒ spectrum-uniqueness` claim must be read that way; the
BEST-count caveat already recorded on
`docs/issue48-p2-population-proportional-identification.md` (branch
`agent/p2-population-proportional-0921`) §5.3 is correct.

### 5.7 Molecule / reverse-complement panel

On the molecule panel the read type is the reverse-complement class and
equivalence is dihedral; the positive theorem fails even for primitive `STRONG`
equal-length words (`AACAGT` / `AACTGT`, `L = 3`, verified in [G]). The oriented
panel is part of the theorem, not an afterthought.

---

## 6. Independent computation

`scripts/verify_normalized_spectrum_divisibility.py`; exact arithmetic.

| Check | What it verifies | default / `--full` | result |
|---|---|---|---|
| A | Bresler-triple `TRF` ⇔ primitive `(L−1)`-multiplicity `≤ 2` | 2 881 / 7 706 instances | 0 mismatches |
| B | Lemma L\*: primitive `TRF` ⇒ `(L−1)`-mult `≤ 2` | max = 2 | 0 violations |
| C | gcd lemma: primitive `TRF` ⇒ `gcd(d_D) = 1` | 5 596 / 35 622 instances | 0 exceptions |
| D | Theorem P: no cross-length proportional primitive-`TRF` pair | — | 0 collisions |
| E | scaling: `e = d_S/b` spellable, `T₀^b` matches | 308 / 3 174 reduced vectors | 0 failures |
| F | one-sided COU: no same-length group with a `WEAK` member and a non-rotation member | — | 0 groups |
| G | sharpness and boundary witnesses (`L=1`, periodicity, `TRF`/`ILF`, molecule) | exact | all pass |

Ranges: default `{A,B}` `n ≤ 12, L ≤ 4`; `{A,B,C}` `n ≤ 9, L ≤ 4`; `--full`
`{A,B}` `n ≤ 16, L ≤ 5`; `{A,B,C}` `n ≤ 11, L ≤ 4`. Check A is additionally
range-capped to expose the direct Bresler predicate. The finite scans are
evidence within their ranges; Lemmas L\*, gcd, and Theorem P are proved in §3,
and the equal-length step is COU (§2).

---

## 7. What is settled, and what is not

* **Settled (mathematical proof):** Lemma L\*, the gcd lemma, Theorem P, and
  therefore scale rigidity for primitive `TRF` genomes.
* **Settled conditional on COU (source theorem, circular reading):** the
  normalized-spectrum identifiability theorem (primitive `WEAK` truth, primitive
  `TRF` candidate) and, a fortiori, the same-length version.
* **Corrected in the record:** the issue-#45 scaling reduction is valid as
  stated; the "one-sidedness gap" attributed to it on the concurrent packet is
  not a gap, because COU is one-sided in the reference word.
* **Not claimed:** anything about the finite-sample Medvedev–Brudno objective
  and the 2016 open question; the `§6.2` flow-feasible candidate class; the
  molecule panel beyond the stated counterexample; or non-i.i.d. sampling.

---

## 8. Sources and anchors

| Item | Anchor |
|---|---|
| Circular truth, uniform oriented reads, cyclic-shift target, Eq. (1) | Shomorony, Kim, Courtade, Tse, *Bioinformatics* 32(17):i494–i502, 2016; [`open-problem.md`](open-problem.md) |
| Repeat / triple / interleaved maximal definitions; strict bridging; `L−1`/`L−2` threshold | Bresler, Bresler, Tse, *BMC Bioinformatics* 14(Suppl 5):S18, 2013; [`bridging-source-semantics.md`](bridging-source-semantics.md) |
| COU: circular `q`-gram criterion at `K = L−1`, one-sided, circular reading | [`literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md`](literature/circular-qgram-identifiability-and-Is-threshold-2026-09-21.md); origin Ukkonen 1992, Pevzner 1995 |
| Sibling cross-length packets (Lemma L\*, Eulerian-support proof, sharpness, molecule boundary) | [`population-identifiability-intrinsic-genomes.md`](population-identifiability-intrinsic-genomes.md); [`issue48-population-independent-verification-2026-09-21.md`](issue48-population-independent-verification-2026-09-21.md) |
| Concurrent packets named but not on this branch | `docs/source-notes/population-ml-theorem-independent-derivation.md` (branch `agent/population-ml-theorem-independent-0921`); `docs/issue48-p2-population-proportional-identification.md` (branch `agent/p2-population-proportional-0921`) |
| Verifier | `scripts/verify_normalized_spectrum_divisibility.py` |
