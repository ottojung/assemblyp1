# Which candidate universe does the 2016 maximum-likelihood open question reference?

_Status: focused source-fidelity resolution, 2026-09-21, written against
`origin/main` at `f60ca5f` and the unmerged source-liveness note on this branch
([`oriented-same-length-se62-source-liveness.md`](oriented-same-length-se62-source-liveness.md),
commit `d9ede64`). It answers two linked questions with primary sources: (a)
which candidate universe the accepted 2016 sentence references, and (b) whether
the conjunct **oriented single-strand + same candidate length + MB09 §6.2** is
source-live. It does not select between the exact multinomial and the fixed-`N`
binomial, does not settle the published question, and does not revise any
witness. Every claim is labelled **source fact**, **source-supported
inference**, **mathematical fact**, **verified computation**, **interpretation**,
or **source gap**._

## 0. Determination

1. **The candidate-universe axis is resolvable, and resolves to free-length
   circular sequences.** Across the two sequence-level readings of the cited
   Medvedev–Brudno likelihood (exact multinomial; fixed-`N` product of
   binomials), the class of candidate *objects* is the same: circular sequences
   `D` of arbitrary nonempty length, scored by their own `length-L` window
   counts. MB09 states no constraint tying competing candidates to a common
   length. [source fact + source-supported inference; §3]
2. **The `oriented`/molecule distinction is not a candidate-universe axis.** It
   is an *index/read-type* axis that lives on the objective and on the genome
   equivalence, not on the set of candidate objects. Phrasing the question as
   "oriented circular sequences vs. something else" conflates two axes. [source
   fact + interpretation; §4]
3. **MB09 §6.2 is a different candidate universe — a flow class — and is not a
   sequence-level referent.** Its feasible objects are flows in a read-derived
   bidirected graph, explicitly a "(non-contiguous) assembly," and a sequence is
   recovered only by the §7 heuristic. [source fact; §3.3]
4. **`oriented + same-length + §6.2` is not source-live.** Each conjunct is
   individually motivated by *a* source, but no primary text selects their
   intersection, and the conjuncts are pairwise in tension (oriented vs
   molecular; same-length vs intrinsic `N(D)` and vs the absence of any total-
   flow equation). [interpretation; §5]
5. **New sharpening: same-length does not even repair well-posedness.** The
   best *non-source* rationale for adding same-length — that "the
   maximum-likelihood sequence" presupposes uniqueness, which is false under
   free length by tandem invariance — does not work, because the §6.1 objective
   factors through the `length-L` spectrum and there are same-length, non-
   dihedrally-equivalent circular sequences with identical spectra. Fixing the
   length restores neither uniqueness nor a unique "the ML sequence." [mathematical
   fact + verified computation; §6]
6. Consequently the strongest source-live statement the accepted sentence
   supports is a sequence-level statement about **free-length circular
   candidates**, and the open question is settled negatively there for both
   sequence-level objectives by existing kernel-checked witnesses; the
   same-length/§6.2 conjunction is a control, not a disambiguation. [source
   analysis + repository fact; §7]

## 1. Primary sources re-verified this run

| Artifact | Locator | SHA-256 | Match to `main`? |
|---|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` | yes |
| Shomorony et al., earlier author-hosted preprint | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` | yes |
| Medvedev–Brudno (2009) full text | `https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/` | HTML body (display equations `M26`–`M33`) | HTML hash non-reproducible; text re-read |

The accepted PDF and the preprint were downloaded and read this run; the
quotations below were extracted from those bytes, not copied from repository
notes. The Medvedev–Brudno §6.1–6.2, §7, and §8.2 passages were re-read from the
PMC full text this run. The publisher supplement remains HTTP 403 (source gap);
this note adds no supplement evidence.

## 2. The accepted sentence: what it says and does not say (source facts)

Accepted article, Discussion (printed p. i501), verbatim from the retrieved PDF:

> "Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence `s`, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). … The
> maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on the
> contrary, seems to be robust to these issues, and thus a good candidate for
> the 'correct' formulation. Understanding whether bridging conditions can be
> used to guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question."

And, immediately before it:

> "… understanding whether, in information-feasible instances of the AP, the
> output of NOT-SO-GREEDY coincides with the solution of a combinatorial
> optimization problem."

Source facts:

1. The compared objects are **sequences**: "this sequence" is the NOT-SO-GREEDY
   reconstruction, and the question is about "the maximum-likelihood sequence."
2. The comparison is at the level of **formulations** (parsimony-based vs
   maximum-likelihood), not algorithms.
3. The sentence carries **no section, equation, figure, or page pointer** into
   Medvedev–Brudno; the bibliography entry is paper-level only.
4. A full-text read finds no `multinomial`/`binomial`, no likelihood formula, and
   no candidate-length/tie discussion in the accepted main text.

These four facts are the entire accepted-text evidence about the referent.
Everything that selects a Medvedev–Brudno object is inference.

## 3. The candidate-universe axis is resolvable

### 3.1 MB09 §6.1 exact objective: free candidate length

Source fact, MB09 §6.1:

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … the probability that the
> outcome of a single trial is `i` is simply `d_i/N(D)`. … There are `4^k` such
> variables … the joint distribution is exactly the multinomial distribution."

The candidate's own length is an argument of the objective (`N(D)`); the
multinomial constraint is `N(D) = Σ_i d_i`, tying a candidate to *its own* count
vector. No sentence constrains two competing candidates to share a length. The
candidate universe is therefore **all nonempty circular sequences**, each with
its own intrinsic length. [source fact]

The repo's `mb09-se61-index-orientation-resolution.md` resolves the literal
`4^k` count as the *oriented* `k`-mer alphabet, in tension with the paper's
molecular vocabulary. That is an **index-set** fact, not a candidate-universe
fact: whichever index convention is used, the candidates being scored are
circular sequences. [source fact + interpretation]

### 3.2 The fixed-`N` approximation changes the denominator, not the class

Source fact, MB09 §6.1:

> "Since in the binomial approximation the length of the genome `N(D)` is a
> constant that is independent of each `d_i`, we can replace it by `N`, which is
> the length of the actual genome from which the reads were sampled. … For our
> experiments, we assume that the genome size is known."

and §8.2:

> "Our algorithm relies on having an estimate on the length of the genome."

`N` is a **likelihood parameter** substituted into each marginal's denominator;
the paragraph says explicitly that it is independent of the `d_i`, i.e. the
coupling `Σ_i d_i = N(D)` has been dropped. No constraint `|D| = N` is added.
Hence readings (1) and (2) differ in the **objective**, not in the candidate
universe. This corrects the natural but invalid inference "known `N` ⇒ competitors
have length `N`"; the source-liveness note (§2) already refutes that inference,
and the primary text confirms it here. [source fact + source-supported inference]

### 3.3 §6.2 is a different universe, and not sequence-valued

Source facts, MB09 §6.2 and §7:

> "The first step is to build a bidirected overlap graph from the set of reads,
> which are DNA molecules. The vertices of this graph are the reads … Each vertex
> has a lower bound of `1` … By Observation 7, the `d_i`'s described above
> actually correspond to the value of the flow through vertex `i` … Since any
> flow can be decomposed into a collection of walks, our flow represents a
> **(non-contiguous) assembly** of the genome."

> "At this point, we have found a flow on the overlap graph … any flow can be
> decomposed into a collection of walks, which, in our case, correspond to the
> assembled contigs. Since there is an exponential number of decompositions
> possible, we use a heuristic …"

The §6.2 feasible set is flows, and its output is not necessarily a sequence.
It is a **different candidate universe**, not a restriction of the
circular-sequence one. [source fact]

### 3.4 Result

Under every reading in which the sentence has definite mathematical content
(readings 1–3), the candidate universe is exactly one of:

- free-length circular sequences (readings 1 and 2 — the sequence-level
  readings), or
- flows in a read-derived bidirected graph (reading 3, §6.2).

Reading (4) ("broad ML principle") fixes no objective and hence no candidate
universe; it is the residual source gap, and it is the reason this resolution is
stated as conditional. Among the definite readings, the sentence's own
sequence-level wording ("this sequence", "the maximum-likelihood sequence",
"the solution") and the "combinatorial optimization problem" phrasing both point
away from §6.2 (a convex min-cost flow returning a flow): see §5.3. [interpretation]

## 4. Four independent axes

The repository's four "readings" are not positions on one scale; they are a
product of independent axes. Separating them is what makes the candidate-universe
question answerable while the objective question stays open.

| Axis | Values | Status |
|---|---|---|
| **Candidate universe** (which objects are compared) | free-length circular sequences / §6.2 flows / unrestricted (reading 4) | **Resolved to free-length circular sequences** for the sequence-level referent; §6.2 is disfavored (§3.4) |
| **Objective** | exact multinomial `M28` / fixed-`N` binomial `M31` | Unresolved (both source-real; MB09's named ideal vs MB09's operative method) |
| **Read-type index** | oriented `4^k` types / `k`-molecule (`rc`) classes | Unresolved; coupled to genome equivalence (`equivalence-and-tie-wellposedness.md`) |
| **Algorithmic realization** | sequence-level optimization / §6.2 biflow + §7 heuristic | Not the referent; §6.2 is MB09's algorithm |

The published sentence's meaning depends on all four, but the *candidate
universe* is one axis and it is fixed (conditional on reading 4 being
non-definite). The model-match dispute between the exact multinomial and the
fixed-`N` binomial (see the unmerged
`shomorony-referent-model-match-decision.md`, which favors the exact `M28`, and
`mb-formulation-referent-reconciliation.md` §5, which favors the operative
binomial) is a dispute on the **objective** axis only: both sides agree the
candidates are circular sequences. [source analysis + interpretation]

## 5. `oriented + same-length + §6.2` is not source-live

This reconfirms and sharpens the branch determination of the source-liveness
note. The conjunction fails on three independent axes.

### 5.1 Length

`known N` is a likelihood parameter (§3.2), not a candidate constraint; the
exact objective has intrinsic `N(D)`; §6.2 states no total-flow or length
equation. `|D| = G` is imposed by no primary sentence. [source fact]

### 5.2 Strand

Shomorony's `I_s` is defined on an oriented circular sequence, and reverse
complements enter only as §4.1 preprocessing. MB09 §6.2's vertices "are the
reads, which are DNA molecules," one node per molecule (MB09 §1.1, §3.1, §4.1).
"Strict oriented + §6.2" therefore crosses the two papers' strand models.
[source fact]

### 5.3 Object type

The sentence asks about "the maximum-likelihood **sequence**" and "the
**solution** of a combinatorial optimization problem." §6.2 optimizes a flow and
is solved as a convex min-cost biflow. A min-cost flow is polynomial convex
optimization, not the discrete "combinatorial optimization" the sentence names;
its output is a "(non-contiguous) assembly," and the sequence is recovered by a
heuristic the source does not claim is likelihood-optimal. Reading §6.2
literally into the sentence is therefore a type mismatch independent of length
and strand. [source fact + interpretation]

A reader may *choose* the conjunction as a modeling control or boundary probe.
That is legitimate and the repository has done useful work with it. It is not a
source-live disambiguation of the published question, and a positive result on
it does not settle the published question. [interpretation]

## 6. New sharpening: same-length does not repair well-posedness

The strongest non-source defense of a same-length candidate class is
well-posedness: under free length the exact MB09 §6.1 likelihood is invariant
under tandem repetition `D ↦ D^k` (`N(D^k) = k N(D)` and `occ(D^k, w) = k·occ(D, w)`,
so every `occ/N(D)` is unchanged), so the truth is tied by the distinct, longer
`S²`; "the ML sequence" is then not unique, and one might infer that the authors
must have intended a bounded candidate length.

**This inference fails.** The §6.1 objective is a function of the `length-L`
spectrum `d(D)` alone; two candidates with the same spectrum receive the same
value for *every* observation. Same length does not prevent distinct spectra
from coinciding. Concretely, over DNA with `L = 2`,

```text
S1 = GAACA : circular 2-windows {GA, AA, AC, CA, AG}
S2 = GACAA : circular 2-windows {GA, AC, CA, AA, AG}
```

are distinct, have equal directed `2`-spectra, have the same length `5`, and are
not related by cyclic shift or reverse complement (both are canonically
`AACAG` vs `AAGAC` under the dihedral action). Hence even after fixing the
candidate length, the exact §6.1 objective admits same-length, non-equivalent
maximizers; "the maximum-likelihood sequence" is not a well-defined single
sequence under a same-length restriction either. [mathematical fact + verified
computation; `scripts/verify_candidate_universe_source_live.py`]

Two consequences:

1. The well-posedness argument cannot be used to infer a same-length candidate
   class, because same-length does not deliver well-posedness.
2. The published phrase is loose prose for "an ML sequence"; the honest
   formalization must carry both a candidate class and an equivalence (and, for
   §6.1, a spectrum-fiber selection convention). This is the "sequence identity
   gap" the candidate-semantics audit records, and it is orthogonal to the
   length and strand axes.

## 7. Consequence for settlement

For the source-live, sequence-level candidate universe (free-length circular
sequences):

- Under the **exact multinomial** (reading 1), the repository's kernel-checked
  same-length witnesses (`AAABB → AAAAB`; read-tiled) refute truth-is-a-maximizer
  by candidate-set inclusion, and free-length witnesses such as `ACGT → ACACGT`
  exhibit the length-dependence mechanism. [repository fact + mathematical fact]
- Under the **fixed-`N` binomial** (reading 2), `AAACC → AAAAC` refutes
  truth-is-a-maximizer likewise. [repository fact]
- For both, the free-length candidate universe contains the same-length one, so
  the same-length restriction is *not* what blocks the negative answer
  (`same-length-witnesses-candidate-set-inclusion.md`).

Therefore the published open question is settled negatively on the source-live
sequence-level candidate universe, conditional only on the referent being
sequence-level (readings 1 or 2) — which the sentence's own wording supports —
and not on resolving the exact-vs-binomial objective fork. The `oriented +
same-length + §6.2` conjunction is not needed, and positive/negative results on
it do not bear on the published statement. [source analysis + interpretation]

This does **not** claim that reading (4) is settled: if "the maximum-likelihood
formulation" is read as an objective family with no fixed formula, no finite
witness settles it, and the residual source gap is exactly which formula was
meant. It also does not settle the read-type/equivalence axis for `S`
(uniqueness), only the strict-competitor axis relevant to `W` (truth is a
maximizer). [source gap]

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| The accepted sentence is sequence-level, formulation-level, and points at no MB09 section | source fact | accepted PDF, p. i501 |
| The accepted main text contains no likelihood formula, `multinomial`/`binomial`, or length/tie discussion | source fact | accepted PDF full-text read |
| MB09 §6.1 exact objective has candidate-intrinsic `N(D)`, with no common competitor length | source fact | MB09 §6.1 |
| The fixed-`N` approximation substitutes a parameter `N`; it adds no `\|D\| = N` constraint | source fact | MB09 §6.1, §8.2 |
| §6.2 optimizes a flow and returns a "(non-contiguous) assembly" | source fact | MB09 §6.2, §7 |
| Read-type index (`4^k` vs molecule classes) is an index/equivalence axis, not a candidate-universe axis | interpretation | MB09 §6.1 vs §6.2; `equivalence-and-tie-wellposedness.md` |
| The candidate universe is free-length circular sequences for the sequence-level referent | source-supported inference | §3–§4 |
| `oriented + same-length + §6.2` is not selected by any primary text | interpretation | §5 |
| Same-length §6.1 objective admits non-equivalent maximizers (`GAACA`/`GACAA`) | mathematical fact, verified | §6, script |
| Free-length sequence-level readings are refuted by existing witnesses | repository fact + mathematical fact | `same-length-witnesses-candidate-set-inclusion.md` |
| Which objective (exact vs fixed-`N`) and which read-type/equivalence are meant; publisher supplement | source gap | §4, §7 |

## 9. Reproduce

```sh
python3 scripts/verify_candidate_universe_source_live.py
```

The script (self-contained, exact integer/`Counter` arithmetic, deterministic,
exits non-zero on a failed assertion) checks: the equal directed `2`-spectra of
`GAACA`/`GACAA`; same length; dihedral inequivalence; the tandem-scaling
invariance of the exact §6.1 `occ/N(D)` ratios; and that the fixed-`N` objective
does not reference candidate length. It shares no code with the repository's
other searches.

## 10. Cross-references

On `main`:
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
(provenance and ranking; §6.3 known-`N` vs candidate length),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
(four readings; sequence-vs-flow),
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
(exact vs approximation vs flow),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
(negative transfer),
[`equivalence-and-tie-wellposedness.md`](equivalence-and-tie-wellposedness.md)
(read-type/equivalence coupling),
[`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md)
(§6.1 index given §6.2),
[`../ml-formalization-contract.md`](../ml-formalization-contract.md)
(variants A/E/F).

On this branch:
[`oriented-same-length-se62-source-liveness.md`](oriented-same-length-se62-source-liveness.md)
(the §45 conjunction determination; this note sharpens it with the
candidate-universe separation and the well-posedness refutation).
Unmerged related packets: `docs/source-notes/shomorony-referent-model-match-decision.md`
(`agent/issue36-shomorony-referent-decision-0920`), which argues the exact
multinomial is the strongest sequence-level referent; and
`docs/source-notes/mb09-se61-se62-candidate-semantics-audit-2026-09-20.md`, which
records the sequence-vs-spectrum identity gap.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`,
§2 and §5; Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome Assembly*,
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`,
PMC3154397, §1.1, §3.1, §4.1, §6.1–§6.2, §7, §8.2.
