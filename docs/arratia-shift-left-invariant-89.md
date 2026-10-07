# The shift-left invariant of the Arratia/Bresler transposition argument (#89)

_Status: source-fidelity note, 2026-09-27.  Nothing here is formalized.  It
records what the `#89` route would need for the **interleaved** disjunct of
the dichotomy, and why the fibre/period lemma just proved
(`AssemblyP1/BBTFibrePeriod.lean`) does **not** need it._

## 0. Verdict on the current route

The packet just delivered (`AssemblyP1/BBTFibrePeriod.lean`) proves the
**fibre/period** bound:

* `three_occurrences_collapse_or_tripleRepeat` --- three distinct starts
  carrying one `(L-1)`-mer either collapse modulo `leastPeriod`, or (after
  the backward extension) they carry a maximal triple repeat of length
  `≥ L - 1`;
* `three_occurrences_collapse_of_Ukkonen` --- so under `Ukkonen` the first
  alternative always holds;
* `fibre_subset_two_classes`, `fibre_card_le_two_of_primitive` --- the
  starts realising one vertex lie in at most two period classes, and in the
  primitive stratum a fibre has at most two starts.

That route is **purely word-level**: it only ever compares the three
occurrences of one label and their maximal (forward and backward) agreement
extensions.  It never mentions a transposition, a breakpoint multiset, or an
"effect".  So the shift-left invariant below is *not* an input to it, and
adding effect/nontriviality to the formal state would be unused
infrastructure.

It is, however, exactly the input for the part that is still open.  See §3.

## 1. The invariant, as the source states it

Source: the transposition-based uniqueness argument for repeated
`t`-tuples (Arratia, Bartholdi, Brbélia, Martin, Penny 1996, *Approximation
of the longest common subsequence*; Bresler–Bresler–Tse 2013 §3, and
the board's own **known-multiplicity reduction** of `thm:BBT`).
**ATTRIBUTION (board 94, front 94e7; see `docs/best-tw1-attribution-94.md`):**
this line formerly ended "and Pevzner's 1995 Lemma 9 as used by `thm:BBT`".
That attribution is **withdrawn**.  Pevzner 1995 (Algorithmica 13:77--105) was
retrieved in full on this board and contains no counting statement of any kind
and none of the `BEST` / `arboresc` / `spanning` / `matrix-tree` /
`determinant` / out-degree / `repeat` / `spectrum` / `K-mer` / `condens`
vocabulary, so it cannot supply a transposition argument of this shape; and BBT
(BMC Bioinformatics 14(Suppl 5):S18, 2013) has no arborescence.

**CORRECTION (board 94, doc front 94d1).**  The same text formerly cited BBT as
"Algorithmica 13:1--19, 2006", said it "contains no proof of its own Theorem 3,
its Theorem 3 importing the step from Pevzner 1995, so the citation chain is
**broken**".  All of that is struck: BBT is Bresler, Bresler & Tse, *Optimal
assembly for high throughput shotgun sequencing*, BMC Bioinformatics
**14**(Suppl 5):S18, 2013, and the arXiv:1301.0068 v3 source does carry a
**complete proof of Theorem 3** (`appendix_short.tex:157-169`), an
out-degree-and-contraction argument with no count, no determinant and no
spanning tree.  BBT cites Pevzner 1995 correctly; the narrower and real defect
is that its one imported step, `Lemma [Pevzner \cite{Pev95}] l:Pev95`, is
**stated but proved nowhere in the chain**.  **Whether `l:Pev95` is true is NOT
ESTABLISHED.**  The Lemma 9 withdrawal above stands.

The reduction named here is the board's own.  What may still be
cited to Pevzner 1995 is Theorem 2, p. 81 (exchange/reflection orbit
connectivity on bicolored graphs, from Abrham & Kotzig 1980) and Theorem 1 /
Corollary 1, p. 80 (Kotzig–Nash-Williams balancedness) --- neither for a count,
a bound, an out-degree estimate, or a uniqueness result.
  State: let the circular
genome carry **two pairs** of identical `t`-tuples, the pairs interlaced,
`i < i' < j < j'`, and suppose the transposition `τ` of the two copies is
**nontrivial** (it changes the spectrum).  Then

> **Shift-left lemma.**  If both pairs can be shifted left by one position
> (the two left extensions of the `t`-tuples are equal), then the
> transposition of the shifted pairs is *again* nontrivial, and the shift
> preserves the effect of the transposition.  Iterating, one of the
> following happens:
>
> 1. **both-leftmost.**  Both pairs reach the leftmost configuration
>    simultaneously; or
> 2. **collision.**  Some endpoint collides --- `j = i'`, or `i' = i`, or
>    `j' = j`.  Then the configuration carries a **three-way repeated
>    `t`-tuple** at the collision point, and the transposition realised at
>    the collision has *the same effect* as the original interlaced
>    transposition, hence is still nontrivial.

The load-bearing content is the phrase "the same effect": a shift of the
whole configuration is a rotation of the circle, so the effect of the
transposition on the multiset of breakpoints is unchanged, and the collision
does not accidentally produce a *trivial* transposition (one that maps the
spectrum to itself).  Without that clause the iteration could degenerate and
the argument would lose nontriviality, which is exactly the quantity the
uniqueness theorem is about.

## 2. Why the formal state would have to carry effect and nontriviality

A `Prop` saying "the chords cross" is not enough, and the repository already
records two independent instances of that (`docs/bbt-chord-rematch-89.md` §5,
`AssemblyP1/BBTChords.lean`): the naive "a non-rotational alternative
transversal is obstructed" statement is *false*, and
`BBTMaximalExtension.not_maximalRepeat_branchPair_0111` is a kernel-checked
counterexample to reading a raw chord as a maximal repeat.  The reason is
structural: both statements are about the *presentation* of a permutation
where the theorem is about its *effect* on the spectrum.

To state the shift-left lemma one therefore needs, at minimum:

| object | meaning | status in this repository |
| --- | --- | --- |
| breakpoint multiset of a traversal | what a transposition acts on | **absent** |
| `Effect τ` | the multiset change induced by a transposition | **absent** |
| `Nontrivial τ` | `Effect τ ≠ 0`, i.e. the spectrum really changes | **absent** |
| `ShiftLeftEffect` | shifting the whole configuration preserves `Effect` | **absent** |
| `Collision → triple repeat` | the `j = i'` case of a collision | `BBTCondense`/`BBTChords` have the *chord* picture only |
| `both-leftmost → innermost chord` | case 1 | **proved**: `BBTUniqueEulerian.not_visitsAll_of_innermost_chord` and `EulerianCycle_no_innermost_chord` |

So case 1 of the shift-left lemma is *already* discharged, in the form the
repository needs: a both-leftmost configuration is exactly the innermost
chord, and an alternative Eulerian cycle cannot have one
(`BBTUniqueEulerian.EulerianCycle_no_innermost_chord`).  Case 2, the
collision, is the part that is missing, and it is missing precisely because
the effect/nontriviality formal state does not exist.

## 3. What it would buy, and why it matters for `EulerianCycleGap`

`AssemblyP1.BBTEulerian.EulerianCycleGap` needs the *interleaved* disjunct
of `LongObstruction` to be reachable: currently only the *triple-repeat*
disjunct is (`BBTMaximalExtension.triple_disjunct`, fed by the new
`three_occurrences_collapse_or_tripleRepeat`).

If the shift-left lemma is available in the form of §1, then case 2 turns an
**interleaved** obstruction into a **three-way repeated `t`-tuple** with a
nontrivial transposition, and case 1 is already impossible.  The dichotomy
would then collapse to a single clause:

```text
an alternative Eulerian cycle of the condensed (L-1)-mer graph
  ⟹ either it is the truth's own cycle up to rotation,
  or the truth carries a maximal TRIPLE repeat of length ≥ L-1
```

which is `Ukkonen`'s first clause alone --- the interleaved clause of
`Ukkonen` would not be needed at this step.  Combined with the fibre/period
lemma this is a strictly shorter route to `EulerianCycleGap` than the one
currently sketched in `docs/bbt-eulerian-cycle-89.md` §6, and it is the
reason the invariant is worth modelling even though the current packet does
not consume it.

## 4. Non-goals and honest status

* **Not formalized.**  None of §1 or §2 is in Lean.  No transposition, effect
  or nontriviality object exists in this repository, and per `AGENTS.md` such
  infrastructure must not be built speculatively: it should be built when, and
  only when, a mature argument needs it.  This note is the durable form of
  that decision.
* **Not verified here.**  The effect-invariance clause of the shift-left
  lemma ("the collision transposition has the same effect, hence is still
  nontrivial") is recorded as the *source's* statement.  It has not been
  checked in this repository's model, and this repository does not currently
  have a model in which it could be checked.  Anyone picking this up should
  treat it as the first thing to verify, and should re-derive the reduction
  of §3 rather than take it from this note.
* **Scope.**  The fibre/period packet (`AssemblyP1/BBTFibrePeriod.lean`) is
  unaffected by this note: its statements are about occurrences, not about
  transpositions, and its proof never assumes anything about effects.
