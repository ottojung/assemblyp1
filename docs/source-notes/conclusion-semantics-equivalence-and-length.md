# Conclusion semantics: equivalence strength and candidate-length assumptions

_Status: independent conclusion-semantics determination for issue #36, 2026-09-21.
It independently re-retrieved the primary sources (hashes in §1) and extends the
existing determination in
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)
and
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
on the two axes that turn out to be under-determined there: the **strength of the
genome equivalence** required by the strong schema, and the **candidate-length
assumption**. It does not settle which Medvedev–Brudno likelihood layer the 2016
sentence intends, and it does not settle the statistical bridging→ML question.
Every claim is labelled **source fact**, **mathematical fact**,
**source-supported inference**, **verified computation**, **interpretation**, or
**source gap**.

_Reproduction of the new computations: `python3 scripts/verify_conclusion_equiv_length_spectral.py`
(exact `fractions.Fraction`/integer arithmetic, deterministic)._

## 0. Determination

1. **Maximizer vs uniqueness is not determined by the sentence.** [source gap]
   The 2016 sentence states no tie-break, uniqueness theorem, or equivalence
   relation; both repository schemas (`MaximizerSchema`, `UniqueSchema`) remain
   literal readings. This re-confirms
   [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md).

2. **The equivalence is stronger than "cyclic shift" or "dihedral".**
   [mathematical fact + verified computation] The exact §6.1 likelihood depends
   on a candidate only through `(N(D), its L-mer spectrum)`, so same-length
   same-spectrum candidates tie for **every** sample. There are same-length
   same-spectrum candidates that are related by neither a cyclic shift nor a
   reverse-complement dihedral move. Hence the strong schema requires the genome
   equivalence to collapse L-mer-spectrum fibers; cyclic shift alone, and
   dihedral alone, are **insufficient in general**. On the *source-admissible*
   domain this gap is, conjecturally, closed by the classical
   Ukkonen–Pevzner characterization (spectrum determines the sequence iff
   there is no interleaved/triple `(L−1)`-mer obstruction), which is exactly the
   structure `I_s` controls.

3. **Candidate length is decisive, and free length kills the strong schema.**
   [source gap + mathematical fact] The sentence does not fix competitor
   length (MB09 §6.1 uses the candidate-intrinsic `N(D)`; §6.1's approximation
   fixes an external `N`; Ghodsi fixes the length by assumption). If candidate
   length is *free*, the exact likelihood is exactly invariant under tandem
   repetition `D ↦ D^k`, so every truth `S` is tied by `S²` (different length,
   not equivalent), and the strong schema is **false for every truth and every
   length-preserving equivalence, with no bridging hypothesis at all**. So the
   only universally coherent reading of the free-length literal exact
   multinomial is the **weak** schema (truth is a maximizer). The strong schema
   requires a fixed/same-length candidate class *and* the spectral rigidity of
   point 2.

4. **Consequence for the open question.** The published "guarantee that the
   maximum-likelihood sequence is the true sequence" can only be read as the
   strong schema on a fixed-length candidate class with a spectrum-collapsing
   equivalence; read existentially (truth is *a* maximizer) it is the weak
   schema. A hypothetical positive settlement therefore owes, in addition to
   the statistical optimality statement, either a fixed-length declaration or a
   spectrum-rigidity theorem; a negative settlement by a *strict* competitor
   needs neither.

## 1. Independent source verification

The three primary sources were re-retrieved this run and are byte-identical to
the ledger used by the existing determination (SHA-256 recomputed):

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., accepted typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Medvedev–Brudno (2009), published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |
| Ghodsi, arXiv:1302.4391v3 | `https://arxiv.org/pdf/1302.4391` | `6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c` |

The load-bearing quotations were independently re-located in the extracted
text of these artifacts:

- **Shomorony et al. Discussion (accepted typeset p. i501).** “Understanding
  whether bridging conditions can be used to guarantee that the
  maximum-likelihood sequence is the true sequence is currently an open
  question.” The surrounding paragraph contrasts information-feasible
  reconstruction with optimization formulations and **supplies no tie,
  uniqueness, or equivalence clause**. [source fact]
- **Medvedev–Brudno §6.1.** “Let `D` be a circular genome of length `N(D)`, and
  let `d_i` denote the number of times the `k`-molecule `i` appears in `D`. …
  the probability that the outcome of a single trial is `i` is simply
  `d_i/N(D)`. … There are `4^k` such variables”; the likelihood is
  `n!/∏x_i! · ∏(d_i/N(D))^{x_i}`. Competitors are **not** restricted to the true
  length. [source fact]
- **Medvedev–Brudno §6.1 approximation.** “[I]n the binomial approximation the
  length of the genome `N(D)` is a constant … we can replace it by `N`, which is
  the length of the actual genome … we assume that the genome size is known.”
  [source fact]
- **Ghodsi §2.** “We have to assume that the length of the genome being
  assembled (denoted by `L`) is known.” **Ghodsi §3.** “the resulting Eulerian
  graph may have many tours, all of which will have equal likelihood. Therefore
  any final solution … is, by itself, only one of many possible solutions.”
  [source fact]

## 2. Axis: equivalence strength (new mathematical content)

### 2.1 The likelihood is a function of the spectrum

For a circular candidate `D` of length `N(D)`, MB09 §6.1 gives each read type
`w` probability `occ(D,w)/N(D)`, so for an observed count vector `x`,

```text
L(D; x) = (n! / ∏_w x_w!) · ∏_w (occ(D,w)/N(D))^{x_w}.
```

Everything except the observation-only coefficient depends on `D` through
`(N(D), occ(D,·))`. [mathematical fact]

**Lemma (spectral fibers).** If `D, D′` have `N(D)=N(D′)` and
`occ(D,·)=occ(D′,·)`, then `L(D;x)=L(D′;x)` for every observation `x`. Hence a
same-length same-spectrum mate of the truth is a tied maximizer whenever the
truth is a maximizer. [mathematical fact]

### 2.2 Cyclic shift and dihedral are not enough in general

Lemma 2.1 shows the strong schema `S = W ∧ (∀D, L(D)=L(S) → D ≈ S)` requires
`≈` to relate every same-length same-spectrum mate of the truth. The existing
determination proves cyclic shift is *necessary*; the following shows it is not
*sufficient* as a general equivalence, and neither is reverse-complement
dihedral. [mathematical fact + verified computation]

Explicit minimal mates (same length, same `L`-mer spectrum, not cyclic shifts,
and not related by the reverse-complement involution `A↔B` with `C` fixed):

| `Σ` | `L` | `G` | candidate 1 | candidate 2 |
|---|---|---|---|---|
| {A,B} | 3 | 6 | `AABABB` | `AABBAB` |
| {A,B} | 3 | 8 | `AAAABAAB` | `AAABAAAB` |
| {A,B} | 4 | 8 | `AAABAABB` | `AAABBAAB` |
| {A,B,C} | 3 | 7 | `AAABAAC` | `AAACAAB` |

The binary-order-3 de Bruijn pair `AAABABBB` / `AAABBBAB` is a further mate (all
eight 3-mers once); both are non-rotation and non-dihedral. All rows were
checked exactly by the reproduction script. [verified computation]

### 2.3 The source-admissible domain closes the gap — via a classical theorem

The repository's bridging analysis (see
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md)
and the candidate-class discussion) isolates the condition that `I_s` excludes
precisely the *interleaved-pair* and *triple-repeat* obstructions of length
`≥ L−1`. Those obstructions are exactly the classical failure of `L`-mer-spectrum
identifiability: **Ukkonen (1992) conjectured and Pevzner (1995) proved** that
two strings have the same `q`-gram profile iff they are connected by
transpositions and rotations, equivalently iff they are Euler trails of the
same de Bruijn multigraph; a post-2016 statement is Çelikkanat–Masegosa–Nielsen,
NeurIPS 2024, Thm 3.1 (arXiv:2411.02125), whose conditions (2) and (3) are the
interleaved- and triple-`(q−1)`-mer obstructions. [source fact as to the
classical theorem; source-supported inference as to the `I_s` correspondence]

**Consequence.** On the `I_s`-admissible domain, the spectrum fiber is
conjecturally exactly the cyclic-shift (or dihedral) class, so the source's
“up to cyclic shifts” reading is adequate *there*. Two caveats remain explicit:
[source gap]
1. the exact `L−1` vs `L−2` threshold and the circular indexing of the classical
   characterization still need a primary-statement check;
2. the correspondence “`I_s`-admissible ⇔ no classical obstruction” is the
   repository's analysis, not a quoted source sentence.

**Audit update (2026-09-21).** A primary-source audit
([`../literature/circular-p2-ukkonen-pevzner-audit-2026-09-21.md`](../literature/circular-p2-ukkonen-pevzner-audit-2026-09-21.md))
confirms both caveats as open. Ukkonen (1992) is **linear** and states the
completeness question as an open problem (p. 194); Pevzner (1995) proved the
linear classification, but its exact wording/theorem is paywalled; and the
`Rotation` blocking pattern is precisely the linear prefix–suffix boundary
artifact with no separate circular analogue. No located source states a circular
Ukkonen–Pevzner multiset classification or the implication
“`I_s`-admissible ⇒ spectrum unique”. The defensible circular frame is the
`L`-mer-multiset ↔ Eulerian-circuit correspondence (Arratia et al. 2000) plus
unique-Eulerian-circuit certificates, with the `I_s` step carried as a
repository lemma, not cited. See the audit note; this row remains
**source-supported inference / open**, not a source theorem.

## 3. Axis: candidate length (new mathematical content)

- **Free length.** For every circular `D` and `k ≥ 2`, the tandem repeat `D^k`
  has `N(D^k)=k·N(D)` and `occ(D^k,w)=k·occ(D,w)`, so `occ/N` — and hence the
  exact likelihood — is **unchanged**: `L(D^k;x)=L(D;x)` for all `x`.
  [mathematical fact] Therefore, if the candidate universe contains `D^k`, the
  truth `S` is exactly tied by `S²`, a distinct, longer, non-equivalent
  candidate. The strong schema is then **false for every truth and every
  length-preserving equivalence, with no bridging hypothesis**. This is the
  sharp statement behind the repository's tandem-invariance observation.
- **Fixed length.** Restricting candidates to `|D|=G` removes the tandem tie;
  the strong schema is no longer refuted on general grounds, but now requires
  (i) the spectral rigidity of §2.3 and (ii) truth to strictly beat every
  candidate on a *different* spectrum. Fixed length is the best operational fit
  to the contemporaneous literature (Ghodsi’s known-length assumption) but is
  not stated by the 2016 sentence. [source gap + interpretation]

## 4. Relation to the existing determination

This note does not replace
[`conclusion-semantics-determination.md`](conclusion-semantics-determination.md);
it sharpens two of its rows:

| Axis | Prior row | Sharpened here |
|---|---|---|
| equivalence | “cyclic shift forced; rc iff molecule” | plus: same-spectrum mates are tied, so strong schema needs a spectrum-collapsing `≈`; cyclic/dihedral suffice only under the (conjectural/classical) rigidity on `I_s`-admissible truths |
| candidate length | “not determined; fixed is best fit” | plus: **free length makes the strong schema false universally** by tandem invariance, independent of bridging |

Point 2 of the existing note (“cyclic shift is forced”) is unchanged and remains
correct: it is the *necessary* half.

## 5. Consequence for witnesses

[mathematical fact] A **strictly** better competitor refutes both schemas under
any equivalence and any length convention, so the integrated strict witnesses
remain equivalence-proof. A merely **tied** competitor is decisive only against
`≈`-panels that fail to relate it to the truth — which, by §2, is a much larger
set of panels than “cyclic shift only” versus “dihedral”: any tie by a
same-spectrum non-mate defeats `≈` unless `≈` collapses the whole fiber.

## 6. Latent predicate issue in exploratory scripts (independent check)

While re-verifying the integrated strict witnesses under the source-faithful
bridging predicate (read start in `{(t−d) mod G : 1 ≤ d ≤ L−l−1}`), the
exploratory Python predicate used in several tracked and untracked scripts —
testing only that the read covers the two flank positions `(t−1) mod G` and
`(t+l) mod G` — was found to over-report bridging when a read reaches both
flanks via the complementary arc. [verified computation] On the two integrated
strict witnesses (`S=AAATAT`, `G=6`, `L=3`, starts `(0,0,1,3,5)`; and the
variable-length `AAATT` witness) the loose and strict predicates **agree**, and
both witnesses remain `I_s`-true. A detailed root-cause analysis and the
discrepancy scope exist as a concurrent working-tree note
(`docs/copy-bridging-predicate-correction.md`, not yet integrated); no
kernel-checked Lean witness and no tracked main document uses the loose
predicate in a load-bearing way.

## 7. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| 2016 sentence states no tie/uniqueness/equivalence clause | source fact | accepted PDF, Discussion p. i501 |
| MB09 §6.1 uses candidate-intrinsic `N(D)` and does not fix length | source fact | JCB 16(8) §6.1 |
| Ghodsi fixes a known length; notes many equal-likelihood tours | source fact | arXiv:1302.4391v3 §2, §3 |
| Exact likelihood depends on `D` only through `(N(D), spectrum)` | mathematical fact | §2.1 |
| Same-length same-spectrum candidates tie for every sample | mathematical fact | §2.1 |
| Non-rotation, non-dihedral same-spectrum mates exist | verified computation | §2.2, script |
| Strong schema requires a spectrum-collapsing equivalence | mathematical fact | §2.1–2.2 |
| Ukkonen–Pevzner characterization of equal `q`-gram profiles | source fact (as stated by Çelikkanat et al. 2024) | §2.3 |
| `I_s`-admissible ⇒ spectrum unique up to shift | source-supported inference / open | §2.3 caveats |
| Exact likelihood is exactly invariant under tandem repetition | mathematical fact | §3 |
| Free candidate length ⇒ strong schema false for every truth | mathematical fact | §3 |
| Which schema, read-type space, length the sentence intends | source gap | §§0, 3 |

## 8. Primary and supporting references

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  *Information-optimal genome assembly via sparse read-overlap graphs*,
  *Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`.
- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`.
- Mohammadreza Ghodsi, *Constructing a genome assembly that has the maximum
  likelihood*, arXiv:1302.4391v3 [cs.CE].
- Esko Ukkonen, *Approximate string-matching with q-grams and maximal matches*,
  *Theoret. Comput. Sci.* 92(1) (1992) 191–211,
  DOI `10.1016/0304-3975(92)90143-4`.
- Pavel A. Pevzner, *DNA physical mapping and alternating Eulerian cycles in
  colored graphs*, *Algorithmica* 13(1–2) (1995) 77–105,
  DOI `10.1007/BF01188582`.
- Abdulkadir Çelikkanat, Andrés R. Masegosa, Thomas D. Nielsen, *Revisiting
  K-mer Profile for Effective and Scalable Genome Representation Learning*,
  NeurIPS 2024; arXiv:2411.02125.
