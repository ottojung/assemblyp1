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
  high throughput shotgun sequencing*, BMC Bioinformatics **14**(Suppl
  5):S18, 2013, doi 10.1186/1471-2105-14-S5-S18; preprint **arXiv:1301.0068**
  --- in full, and found **no** arborescence, **no** spanning-tree count and
  **no** out-degree bound.  It also reported **no proof of BBT's own Theorem
  3**; *that part is now known to be false, see §1.1.* BBT's Theorem 3
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

### 1.1 The BBT citation chain is a **stated-but-unproved import**, not a broken chain

> **CORRECTED by board 94 doc front 94d1.** This subsection previously read
> "### 1.1 The BBT citation chain is a **broken link**" and asserted that "BBT's
> Theorem 3 is asserted by import-by-citation into a chain that terminates in
> nothing." **That was false, and it is struck.** The bibliographic record was
> also wrong here: it gave BBT as *Algorithmica* 13(1--2):1--19, 2006. There is
> no such version. See `/workspace/BOARD94-PROVENANCE.md` and
> `/workspace/BOARD94-DOCFIX.md`.

**The bibliographic record, established from primary sources.** BBT is Guy
Bresler, Ma'ayan Bresler and **David Tse**, *Optimal assembly for high
throughput shotgun sequencing*, **BMC Bioinformatics 14(Suppl 5):S18, 2013**,
doi 10.1186/1471-2105-14-S5-S18. This matches the repository's own
`paper/references.bib` entry `bresler2013`. The preprint is **arXiv:1301.0068**
(v3, 2013-01-01), and it is the preprint that carries the appendix.

**The chain is not broken.** Front 94ff2 read the published 13-page BMC
rendering, which genuinely has no appendix and (in the extracted text) no
"Proof" section. But that rendering is not the whole paper: its own closing
paragraph states "All proofs can be found in the appendix." The authors' own
LaTeX source for **arXiv:1301.0068v3** (26 pages) does contain
`appendix_short.tex`, and `appendix_short.tex:157-169` carries a **complete
proof of Theorem 3** (`t:SBH_no_multiplicities`). So the earlier front read a
genuinely appendix-less rendering of a paper whose appendix exists.

**That proof contains no counting argument, no determinant and no spanning
tree.** The proof is short: it argues that a node traversed three times in the
`K`-mer graph would force a triple repeat of length `K`; hence at a
twice-traversed edge the tail has out-degree `1` and the head in-degree `1`;
hence that edge is contracted by Defn. `d:condensed`; hence the truth's cycle
traverses each condensed edge at most once as well as at least once, i.e. it is
Eulerian. Occurrence counts in `appendix_short.tex`: `arboresc` 0, `spanning` 0,
`matrix-tree` 0, `determinant` 0, `Cayley` 0. The only case-insensitive `best`
matches are the English word "best" in unrelated prose. (The prior claim that
BBT had no out-degree vocabulary is also wrong: `d⁺`/`d⁻` degrees are exactly
what its proof uses.)

**What the real defect is.** BBT's proof imports exactly one step,
`Lemma [Pevzner \cite{Pev95}] l:Pev95` (`appendix_short.tex:111-113`), used
only in the "only-if" direction: *if there are multiple Eulerian cycles then
Ukkonen's condition is violated*. BBT cites Pevzner 1995 **correctly** --- the
right paper, in the right neighbourhood (Eulerian cycles, `q`-grams, word
reconstruction from `q`-gram composition). But `l:Pev95` is a **statement that
is stated but proved nowhere in the chain**. That is a real, narrower, and
still-load-bearing defect; it is *not* a broken chain terminating in nothing.

**What this section does *not* establish.** Whether `l:Pev95` is mathematically
**true** is **NOT ESTABLISHED**. It is established only that BBT *asserts* it
and that one extraction of Pevzner 1995 does not *state* it. It has not been
shown false and it has not been shown true. The endpoint `hPevzner` is
therefore still formally out of reach, and this correction does not make it
reachable.

The prior spirit of this subsection is retained: a later front must not treat
BBT Theorem 3 as a black box, and the board still has to supply its own
argument. That is now for a different and better-documented reason.

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
  *Update (front 94d1):* front 94c8 subsequently read Pevzner 1995 and reports
  Lemma 9 to be about order exchange/reflection on the **double-digest fork
  graph**, i.e. a cassette-transformation statement with nothing to do with
  `hPevzner`. I did not independently re-read Pevzner 1995 on this front and
  mark that as **reported, not independently verified here**. It is consistent
  with, and reinforces, the withdrawal of the Lemma 9 attribution; the
  withdrawal stands either way.

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

*Update (front 94d1):* the "count / bound" half of that prohibition is
reinforced --- BBT's proof of Theorem 3 contains no count, no determinant and
no spanning tree (§1.1). The "uniqueness result" half needs one clarification:
BBT's arXiv appendix *does* prove a uniqueness result (Theorem 3 itself, by an
out-degree-and-contraction argument). That is a statement in the arXiv
preprint's appendix, not a result the published BMC article states with a
proof, and the repository still does not import it --- `EulerianCycleObstruction`
remains an explicit, unproved hypothesis. So the operative rule is unchanged:
the board must still supply its own argument, and no front may close
`hPevzner` by citation.

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

## 6. 2026-10-06 correction: Section 5 of Pevzner 1995 was missed

The provenance conclusions above must be narrowed again.

A direct retrieval of Pevzner 1995 Section 5 ("Ukkonen's Conjecture") found
the paper's own **Theorem 3**:

> Every two words with the same q-gram composition can be transformed into
> each other by transpositions and rotations.

Its proof explicitly identifies fixed q-gram composition with Eulerian paths in
the directed de Bruijn graph and identifies Ukkonen transpositions with order
exchanges in the associated bicolored graph. A later Pevzner textbook states
the graph version directly: every two Eulerian cycles in a directed graph can
be transformed into each other by a sequence of Euler switches.

Therefore the earlier claims in this note that Pevzner 1995 has "zero
occurrences of repeat/spectrum", that its Theorem 3 "has nothing to do with
BBT's Theorem 3", and that only Theorems 1/2 may be cited are **withdrawn**.
They arose from an incomplete/failed text extraction. The statement inventory
itself was not the problem; the interpretation/search of the extracted text
was.

What remains correct:

- Pevzner 1995 does not use the BEST theorem, arborescence counting, or the
  board's t_w=1 counting reduction.
- "Pevzner 1995, Lemma 9" is still the wrong locator for the desired result.
- BBT's short appendix proof still imports a Pevzner/Ukkonen uniqueness step
  rather than formalizing it.
- The Lean repository still needs a proof, not a citation.

What changes:

- Pevzner 1995 supplies a highly relevant **global connectivity theorem**:
  equal q-gram words / Euler tours are connected by transpositions and
  rotations.
- This can replace the board's attempted global ladder traversal induction.
  The remaining project-specific work can be localized to proving that, under
  P2/Ukkonen, each Euler switch in such a sequence is vertex-cycle-invisible
  (crossing raw branch pairs either give a forbidden long interleaving or,
  by the already-proved coalescence theorem, lie in one benign maximal-repeat
  ladder).

See docs/pevzner-transposition-route-94.md for the resulting proof plan.
