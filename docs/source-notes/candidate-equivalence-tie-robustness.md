# Candidate-genome equivalence and tie semantics: robustness of the strict-improvement witnesses

_Status: primary-source re-check + pure-logic argument + independent finite
computation + kernel check, 2026-09-20, for issue #36. All claims are labelled
**source fact**, **source-internal tension**, **mathematical argument**,
**verified computation**, **kernel-checked**, **repository fact**, or
**open**. This note does not settle the published Shomorony et al. question; it
audits whether the candidate-genome-equivalence and tie conventions could
invalidate the repository's integrated strict-improvement counterexamples._

_Reproduction:_

```sh
python3 scripts/audit_equivalence_tie_robustness.py
lake build AssemblyP1.EquivalenceTieRobustness
```

## 0. Answer at a glance

The candidate-genome-equivalence convention (cyclic shift, reverse complement,
or dihedral) **cannot invalidate any existing strict-improvement witness**,
and neither can the maximizer-versus-unique-maximizer choice:

| convention | effect on a witness with `L(D) > L(S)` |
|---|---|
| cyclic-shift equivalence | none: the maximizer predicate never mentions it |
| reverse-complement / dihedral equivalence | none, provided the objective is invariant on classes (true for the molecule-class objectives; not defined for the oriented/abstract ones) |
| truth-is-a-maximizer vs all-maximizers-are-truth | none: a strict improvement refutes both, and refutes "some maximizer is equivalent to truth" as well |
| quotienting the candidate set | none: an invariant objective cannot give `L(D) > L(S)` when `D ~ S`, so a strict winner is necessarily a genuinely new class |

The conventions that genuinely matter for the witnesses are **not** equivalence
or tie semantics but **admissibility**: which read types exist (oriented versus
reverse-complement molecules) and which candidates are in the feasible set.
Those are model-fidelity questions, tracked separately.

## 1. Primary-source facts about equivalence

### 1.1 Shomorony et al. 2016 (the paper posing the question)

Source: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
“Information-optimal genome assembly via sparse read-overlap graphs,”
*Bioinformatics* 32(17), 2016, i494–i502, DOI
`10.1093/bioinformatics/btw450`; accepted typeset PDF hash `ec17b16f…`.

- §2 treats `s` as a single circular sequence, `s[t + G] = s[t]`.
- §3 states the reconstruction target “up to cyclic shifts”, repeated in
  Theorem 1 and Corollary 1. **Cyclic shift is the only genome equivalence the
  theory invokes.** [source fact]
- §4.1 handles the second strand by *preprocessing*: “before running
  NOT-SO-GREEDY, we preprocess the set of reads to include each read and its
  reverse complement.” The double-stranded implementation keeps **two**
  orientation nodes per read, i.e. it does not quotient a read by its reverse
  complement. [source fact]
- §5 (the open question) adds no tie rule, no uniqueness claim, and no
  equivalence relation under which uniqueness is meant. [source fact; see
  `docs/literature/ml-tie-semantics.md`]

### 1.2 Medvedev–Brudno 2009 (the cited likelihood formulation)

Source: Paul Medvedev, Michael Brudno, “Maximum Likelihood Genome Assembly,”
*J. Comput. Biol.* 16(8), 2009, 1101–1116, DOI `10.1089/cmb.2009.0047`,
PMC3154397.

- §3.1: “A DNA molecule is an unordered pair of strings (also called strands)
  that are reverse complements of each other”; a `k`-molecule is such a pair of
  length `k`. §4.1: “each `k`-molecule is represented only once.” Hence the
  string-level object is defined only up to reverse complement. [source fact]
- §6.1 defines the candidate `D` as a **circular** genome of length `N(D)`.
  Together with §3.1, the natural string-level identity is therefore **at least
  dihedral**. [source-supported inference, not a quoted string-equivalence
  claim; MB09 states no equivalence theorem]
- §6.1 also writes “There are `4^k` such variables” while calling the indexed
  variable a `k`-molecule. The molecule-class count is `(4^k + p_k)/2`, not
  `4^k`. This is a genuine **source-internal tension**: the `4^k` count fits
  *oriented* `k`-mers, the vocabulary fits reverse-complement classes.
  [source fact]
- MB09 states no maximizer, uniqueness, cyclic-shift, or equivalence claim for
  the §6.1/§6.2 optimum. [source fact]

### 1.3 Consequence for a well-posed quotient

A quotient of candidate genomes by an equivalence is only sound for an
objective that is constant on classes. The spectrum-based objectives used by the
integrated witnesses are constant on the cyclic-shift orbit, and the
molecule-class objectives are additionally constant on the reverse-complement
orbit, so both quotients are well-defined there. An *oriented* objective is
**not** reverse-complement invariant, so reverse-complement equivalence is not
even available for the oriented witnesses. [mathematical argument; verified
computationally in §3]

## 2. The logical separation (kernel-checked)

`AssemblyP1/EquivalenceTieRobustness.lean` proves, for the abstract
`AssemblyModel`, the following. Let `S` be the truth and `D` a candidate with
`M.likelihood S R < M.likelihood D R`.

1. **Maximizer schema is equivalence-free.**
   `M.IsMaximumLikelihood S R` is a `∀ candidate` statement about
   `M.likelihood` only; it contains no occurrence of `M.genomeEquiv`. Hence
   `¬ M.IsMaximumLikelihood S R` holds regardless of the equivalence.
   [kernel-checked, `strict_improvement_refutes_maximizer`]
2. **Strict improvement refutes every uniqueness schema.**
   `M.IsUniqueMaximumLikelihoodUpToEquiv S R` is definitionally the
   conjunction of the maximizer schema with a tie clause. The same strict
   improvement refutes the conjunction for *every* relation `R` used to identify
   ties, not merely the model's own `genomeEquiv`.
   [kernel-checked, `strict_improvement_refutes_unique_any_equiv`; the
   decomposition is `unique_iff_maximizer_and_ties`]
3. **Tie-based uniqueness refutations are equivalence-relative.**
   The uniqueness clause is monotone in the equivalence relation: a finer
   relation implies the schema for every coarser one. Contrapositively, a
   refutation that rests on a *tie* between merely non-`R`-equivalent genomes
   can be destroyed by coarsening `R` (e.g. adding reverse-complement
   identification to cyclic shift). [kernel-checked, `unique_up_to_mono`]

Point 3 is why the repository's integrated witnesses are all
strict-improvement rather than tie-only: strict improvement is stable under
every equivalence refinement or coarsening, while a tie-only uniqueness
counterexample is not.

### 2.1 Raw labelled words versus quotient classes

The finite witnesses are stated over labelled linear arrays
(`Genome := Fin n → Base`) and compare explicit representatives; they do not
build `genomeEquiv` quotients. [repository fact] This is harmless for negative
results: if the representative `D` strictly beats the representative `S`, then
the class of `S` is not a maximizer over classes (any class containing a
strictly better representative is strictly better, and `D`'s class is such a
class). The kernel lemmas above quantify over all `M.Genome`, which includes
the raw representatives; the quotient statement is the corollary. [mathematical
argument]

## 3. Per-witness audit (verified computation)

`scripts/audit_equivalence_tie_robustness.py` independently recomputes each
integrated witness with exact `fractions.Fraction` arithmetic and checks (i) the
strict improvement, (ii) that the competitor lies outside the truth's
cyclic-shift orbit and, where a DNA complement is defined, outside its dihedral
orbit, and (iii) that the objective is constant on that orbit.

| witness (main) | `S` | `D` | `\|S\|,\|D\|` | objective | `L(D)/L(S)` | quotient checked | verdict |
|---|---|---|---|---|---|---|---|
| `ExactVariantECounterexample` (#24) | `ACGT` | `ACACGT` | 4, 6 | exact multinomial, intrinsic `N(D)` | `32/27` | cyclic shift (oriented; revcomp not a symmetry) | strict, non-equivalent |
| `FixedLengthExactCounterexample` (#31) | `AAABB` | `AAAAB` | 5, 5 | exact multinomial, fixed length | `2` | cyclic shift (abstract alphabet, no complement) | strict, non-equivalent |
| `FixedLengthBinomialCounterexample` (#32) | `AAACC` | `AAAAC` | 5, 5 | §6.1 product of binomial marginals, `N=5` | `1125/512` | cyclic shift (abstract alphabet) | strict, non-equivalent |
| `Section62BridgingCounterexample` (#36) | `AAATT` | `AAAATT` | 5, 6 | §6.1 molecule-class binomials, `N=5` | `9/8` | dihedral | strict, non-equivalent |
| `SameLengthSection62Counterexample` (#43) | `AAATAT` | `AAAAAT` | 6, 6 | §6.1 molecule-class binomials, `N=6` | `5` | dihedral | strict, non-equivalent |

The script also reproduces the full-type-space §6.1 ratio `1125/512` for #32 and
the documented `9/8` and `5` ratios. It exits non-zero on any failure.
[verified computation]

No integrated witness is tie-based; all five refute the maximizer schema
outright. Consequently they refute the uniqueness schema for every candidate
equivalence, by §2.

## 4. What the conventions can and cannot do

**Cannot.** No choice of cyclic-shift, reverse-complement, or dihedral
equivalence, and no choice between the maximizer and unique-maximizer
conclusions, can turn an integrated strict-improvement witness into a
non-witness. The inequalities are strict and the maximizer predicate is
equivalence-free.

**Can.** Equivalence and tie conventions do constrain the *positive* direction
and tie-only refutations:

1. A positive theorem (“bridging makes the truth *the* ML assembly”) is only as
   strong as the equivalence it quotients by; the published sentence does not
   fix that equivalence. [open, see `docs/literature/ml-tie-semantics.md`]
2. A tie-only uniqueness counterexample must exhibit two non-equivalent
   maximizers; its validity depends on the equivalence relation being at least
   as fine as required, and coarsening the relation can destroy it (§2.3).
3. Whether reverse-complement equivalence is even available depends on the
   read-type model: it is natural for MB09 molecule-class objectives
   (`Section62BridgingCounterexample`, `SameLengthSection62Counterexample`) but
   not for the oriented objective of `ExactVariantECounterexample`, and it is
   undefined for the abstract `B`-alphabet witnesses. This is an admissibility /
   source-model choice, not an equivalence choice.

The only conventions that could actually remove a strict witness are therefore
**admissibility** conventions: restricting the candidate universe so that `D`
is not a candidate, or collapsing read types so that the objective changes.
Those are exactly the source-model forks already recorded in
`docs/source-notes/medvedev-brudno-candidate-class.md`,
`docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`, and the
branch note `docs/source-notes/reverse-complement-strand-convention.md`
(unmerged). They are disjoint from the equivalence/tie question audited here.

## 5. Epistemic status

| claim | status |
|---|---|
| Shomorony 2016: circular truth, target “up to cyclic shifts”; revcomp only as §4.1 preprocessing with two orientation nodes; no tie rule | source fact |
| MB09: reads/`k`-molecules are unordered reverse-complement pairs represented once; §6.1 candidate is a circular genome of length `N(D)`; no maximizer/uniqueness/equivalence claim | source fact |
| MB09 §6.1 `4^k` variable count conflicts with the `k`-molecule vocabulary | source-internal tension |
| MB09 string-level identity is at least dihedral | source-supported inference |
| The maximizer schema is equivalence-free; a strict improvement refutes the maximizer and every uniqueness-up-to-`R` schema | kernel-checked |
| Uniqueness up to equivalence is monotone in the relation; tie-only refutations are equivalence-relative | kernel-checked |
| Each of the five integrated witnesses is strict and outside the relevant shift/dihedral orbit, with an orbit-invariant objective | verified computation |
| No integrated witness is invalidated by any candidate-equivalence or tie convention | follows from the above |
| Which read-type/strand/candidate model the 2016 sentence intends | open, tracked elsewhere |

## 6. Sources

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
  *Information-optimal genome assembly via sparse read-overlap graphs*,
  *Bioinformatics* 32(17) (2016) i494–i502, §2, §3, §4.1, §5.
- Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
  *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2, Observation
  7, PMC3154397.
- Guy Bresler, Ma'ayan Bresler, David Tse, *Optimal assembly for high throughput
  shotgun sequencing*, *BMC Bioinformatics* 14(Suppl 5):S18 (2013), for the
  `I_s` repeat/interleaving/bridging definitions (as recorded in
  `docs/bridging-source-semantics.md`).

Repository cross-references: `docs/literature/ml-tie-semantics.md`,
`docs/source-notes/same-length-witnesses-candidate-set-inclusion.md`,
`docs/source-notes/medvedev-brudno-candidate-class.md`,
`AssemblyP1/Model.lean`, `AssemblyP1/EquivalenceTieRobustness.lean`,
`scripts/audit_equivalence_tie_robustness.py`. Unmerged branch artifact:
`docs/source-notes/reverse-complement-strand-convention.md`.
