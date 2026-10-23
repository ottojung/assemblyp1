# Issue #272: Not-So-Greedy necessity remains algorithm-specific and open

Status: source/model audit, 2026-10-23. This note records why the existing
read-only-certainty counterexample does not establish success of the literal
2016 Not-So-Greedy procedure.

## Question and source boundary

The precise question is whether the 2016 Not-So-Greedy output is the true
rotation class for some positive-probability input in its stated oriented,
same-length model when the truth fails `I_s`. The primary source is Shomorony,
Kim, Courtade, and Tse, “Information-optimal genome assembly via sparse
read-overlap graphs,” *Bioinformatics* 32(17) (2016), i494–i502,
DOI [10.1093/bioinformatics/btw450](https://doi.org/10.1093/bioinformatics/btw450).
The repository's manuscript records its result as a reconstruction guarantee:
under the full hypotheses, the Not-So-Greedy overlap-graph construction has a
unique Eulerian spelling equal to the truth up to rotation
(`paper/sections/03-open-question.tex`, Theorem `notso-greedy`). The result is
explicitly attributed as published/external, not presented as a Lean theorem.

The source/model transcription needed for `I_s` is available in
`docs/bridging-source-semantics.md` and `AssemblyP1/HistoricalCovers.lean`.
The mathematical model already distinguishes oriented read strings, fixed read
length, circular rotation, and source-defined feasibility. However, the
repository contains no executable/formal implementation of the 2016
Not-So-Greedy graph builder and output procedure. In particular, the formal
surface in `AssemblyP1/ConditionalIdentifiability.lean` has a `decode` field
and assumes `decode_correct` on feasible inputs; it does not define how the
published algorithm constructs its graph, resolves graph multiplicities, or
selects/spells an Eulerian traversal outside the theorem's hypotheses.

The publisher-hosted article endpoint
`https://academic.oup.com/bioinformatics/article/32/17/i494/2450754` returned
HTTP 403 in this run. The DOI resolver confirmed the bibliographic identity,
but supplied no procedure text. The exact supplement has not been recovered in
this run. Existing source notes report the same archival limitation. Thus this
run does not claim an independent reconstruction of algorithm details from a
primary full-text copy.

## Why the existing witness does not transfer

`docs/source-notes/issue272-is-necessity.md` and
`AssemblyP1/FiniteIsNotNecessaryCertainty.lean` settle a different, precise
claim: a read-only decoder *can* be certain on an `I_s`-failing observation
(`AAAB`, `L = 3`, starts `{0,2}`, distinct strings `{AAA, ABA}`). This only
shows that the observed read support has one rotation class. It does not show
that the historical Not-So-Greedy construction returns that class. In
particular, the noted overlap graph for that witness is disconnected, so one
cannot infer its Eulerian spelling behavior from the uniqueness-of-support
argument. This run did not recompute or reuse that example as a new algorithmic
counterexample.

Nor does the published theorem settle the converse asked here: its implication
from `I_s` to correct unique spelling imposes no conclusion on inputs outside
`I_s`. The information-theoretic obstruction statements and abstract
read-only-decoder characterization likewise do not fix the output of this
particular algorithm on such inputs.

## Result and next decisive step

**Finding: the literal algorithm-specific claim remains open in the present
formal/source record.** No source-faithful bounded success witness was
established in this run, and no theorem that it cannot exist was established.
The decisive next step is to recover the primary/supplement procedure text and
translate its exact read-overlap graph, multiplicity rules, and deterministic
Eulerian-spelling/output semantics into a small evaluator under the same
orientation, read-length, genome-length, and candidate conventions. Then
search for a truth with `I_s` false whose actual algorithm output is in its
rotation class; exhaustively validate any finite witness independently. A
generic decoder chosen to return the unique supported orbit would not satisfy
that burden.

No Lean formalization was attempted because the source-faithful procedure
definition is still missing. No result here upgrades the external published
reconstruction theorem or the existing generic decoder lemma into a verified
historical algorithm claim.
