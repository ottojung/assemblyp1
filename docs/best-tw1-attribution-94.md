# Attribution of the `t_w = 1` split and the conditional BEST-theorem reduction (board 94, front 94e7)

_Status: documentation, board issue 94. This note records an **attribution
correction**, not new mathematics. Nothing here is a proof of anything, and
nothing here is a claim about the contents of a paper beyond what is recorded in
§1 and attributed there._

**Board decision.** Everywhere in this repository that the `t_w = 1` split, the
conditional BEST-theorem reduction, the identification of out-degree as the
critical parameter, or any appeal to "the classical argument" for a count was
attributed to Pevzner 1995 or to Bresler--Bresler--Tse, that attribution is
**relabelled as the board's own construction**. The BEST-theorem route is a
standard strategy for conditional uniqueness; it is **not** a result imported
from either cited paper.

## 1. The two-sided retrieval result this relabel rests on

The result is not mine. It was established on this board by two earlier fronts
and I relay it without re-doing it:

* **BBT side.** Front 94ff2 (report `/workspace/BOARD94-BBT-SOURCE.md`, branch
  `94-bbt-source`) read BBT --- Bresler, Bresler & Tse, *Optimal assembly for
  high throughput shotgun sequencing*, Algorithmica **13**(1--2):1--19, 2006 ---
  in full, and found **no** arborescence, **no** spanning-tree count, **no**
  out-degree bound, and **no proof of BBT's own Theorem 3**. BBT's Theorem 3
  states uniqueness of the Eulerian cycle of a *condensed sequence graph* of a
  genome with no triple or interleaved repeats of length at least `K`; that is
  a different and more specific statement than a general conditional BEST
  count.
* **Pevzner 1995 side.** Front 94-pevzner-src (report
  `/workspace/BOARD94-PEVZNER.md`, branch `94-pevzner-src` @ `76288a1`)
  retrieved Pevzner, *DNA Physical Mapping and Alternating Eulerian Cycles in
  Colored Graphs*, Algorithmica **13**(1--2):77--105, 1995, in full from
  CiteSeerX, and searched it exhaustively: **zero** occurrences of `BEST`,
  `arboresc`, `spanning`, `matrix-tree`, `determinant`, and out-degree, and
  **zero** occurrences of `repeat`, `spectrum`, `K-mer`, `condens`. The paper
  has **no counting statement of any kind**. Its statement inventory is 4
  theorems, 16 lemmas and 1 corollary, and all four theorems are about
  transformability or characterization.

**Therefore:** the `t_w = 1` decomposition is attributable to **neither** Pevzner
1995 nor BBT. It is a board construction.

### 1.1 The BBT citation chain is a **broken link**

BBT attributes the step to Pevzner 1995, and Pevzner 1995 does not contain it
either. **BBT's Theorem 3 is asserted by import-by-citation into a chain that
terminates in nothing.** This is recorded here deliberately, in the spirit of
`AGENTS.md`'s rule about preserving approaches that rule out tempting
directions: a later front must not treat BBT Theorem 3 as a black box. The
board has to supply the argument itself.

### 1.2 What that result does *not* establish

Relayed limits, stated so nothing here is over-read:

* Compeau, Pevner & Tesler 2011, *How to apply de Bruijn graphs to genome
  assembly*, Nat. Biotech. **29**(11):987--991, 2011 --- BBT's reference [19],
  and the most plausible remaining home for a genuine counting argument ---
  **was not read** by either front. The absence of a counting argument in the
  papers that *were* read does **not** prove its absence in the literature.
* BBT's reference list has not been swept; other references were not audited.
* The extraction of the Pevzner 1995 text was done by a purpose-written
  extractor, not `pdftotext`. Display mathematics and figure labels are not
  claimed to have been faithfully recovered.
* The locator "Pevzner 1995, Lemma 9" that this repository formerly used is
  therefore **not** a verified locator for the statement the repository
  attributed to it. Whatever Lemma 9 of that paper is, the paper's zero
  vocabulary for counts, degrees, repeats, spectra and condensation means it
  cannot be the known-multiplicity condensation statement the repository
  claimed. I did not read Pevzner 1995 and am not asserting what Lemma 9 is.

## 2. What may be cited, and how

Only two things may be cited to Pevzner 1995, with these exact locators:

* **Pevzner 1995, Theorem 2, p. 81** (proof pp. 82--86): the classical
  exchange/reflection argument showing that all alternating Eulerian cycles of
  a bicolored graph lie in one orbit. Attribute the underlying result to
  **Abrham & Kotzig 1980**, as Pevzner himself does.
* **Pevzner 1995, Theorem 1 / Corollary 1, p. 80**: the Kotzig--Nash-Williams
  balancedness criterion, if an existence criterion for alternating Eulerian
  cycles is needed. Attribute to **Kotzig 1968** / Nash-Williams, as Pevzner
  does.

**Do not** cite Pevzner 1995 or BBT for a count, a bound, an out-degree
estimate, or a uniqueness result. Those citations would be false.

Note also a title collision that a reader should not fall into: Pevzner 1995's
*own* Theorem 3 is Ukkonen's conjecture on `q`-gram words, and has nothing to do
with BBT's Theorem 3.

## 3. Where the BEST theorem itself comes from

Neither Pevzner 1995 nor BBT cites it, because neither uses it. Cite the BEST
theorem directly:

* **van Aardenne-Ehrenfest and de Bruijn**, *Indag. Math.* (1951) --- the
  in-degree-multiplied-out-degree form; or
* **Tutte**, *A spanning tree expansion of the determinant*, LMS Lect. Notes
  **83** (1975) --- the matrix-tree form.

The counting note `docs/exact-same-length-spectrum-fibre-count.md` is the
repository's statement of the theorem; its §"Weighted BEST quantity" now names
these sources, and its reduction is labelled the board's own.

## 4. The relabelled sites

| File | Lines | What changed |
| --- | --- | --- |
| `AssemblyP1/BBTCondense.lean` | 89--92 | "the remaining input is Pevzner 1995, Lemma 9" -> board construction; locator disowned |
| `AssemblyP1/BBTEulerian.lean` | 93--95 | "This is the Pevzner 1995 Lemma 9 / `thm:BBT` input" -> board construction |
| `AssemblyP1/PopulationUniqueness.lean` | 65--66 | "it is the Pevzner 1995 Lemma 9 input" -> board construction |
| `docs/bbt-chord-rematch-89.md` | 36--38, 175--186, 207, 213 | "the Pevzner known-multiplicity step" -> board construction |
| `docs/arratia-shift-left-invariant-89.md` | 36--37 | "Pevzner's 1995 Lemma 9 as used by `thm:BBT`" -> board construction |
| `docs/exact-same-length-spectrum-fibre-count.md` | 3--6, 17--35, 82 | BEST sources named; reduction labelled the board's own |

Before/after wording for each site is in `/workspace/BOARD94-TW1.md` §1.

## 5. What was deliberately *not* changed

* `paper/sections/05-population.tex` and `04-finite-results.tex` cite
  `bresler2013` for the **statement** `thm:BBT`. That is correct and is left
  alone: the paper does state that theorem. What it does not contain is a proof
  the board can import, and that is now recorded in `docs/` rather than in the
  paper's citation.
* `AssemblyP1/P2.lean`, `PopulationReduction.lean`, `PopulationUniqueness.lean`
  and the `docs/` files that say "Bresler--Bresler--Tse 2013, Theorem 3" for
  the *statement* of complete-spectrum uniqueness. Correct as a statement
  citation; not a proof citation; left alone.
* `docs/maximum-likelihood-models-for-genome-assembly.md` and
  `docs/literature-status.md`, which cite BBT's Theorem 3 as a **necessary**
  condition from the literature review. Correct as stated; left alone.
* Every `hPevzner` / `hBBT` binder in the tree. These are the pre-existing
  explicit hypothesis names of `EulerianCycleObstruction` and `BBTUniqueAt`.
  Renaming them would be a mechanical change with no mathematical content, and
  the brief forbids *introducing* an assumption of that shape, not renaming an
  existing one. Their meaning is unchanged and is now labelled the board's own
  open obligation, not an imported lemma.
