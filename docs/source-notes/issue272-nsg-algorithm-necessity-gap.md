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
HTTP 403 in this run. The DOI resolver confirmed the bibliographic identity;
the Crossref abstract confirms only the headline guarantee (information
feasibility implies reduction to an Eulerian path problem), not a full
tie-breaking specification. A contemporaneous author-associated implementation
is publicly available at
[`samhykim/nsg`](https://github.com/samhykim/nsg), pinned for this audit at
commit `32038da6b207e87b4572fbb6b91186f71814fe3a`. Its README describes the
greedy/next-largest non-aligning overlap selection and X/Z cleanup. The source
`nsg.cpp`, `find_xz.h`, and `nsg_util.h` provide implementation detail, but do
not define an output genome: this code builds/cleans an overlap graph and does
not spell an Eulerian traversal. It therefore cannot by itself settle a claim
about the paper's reconstructed sequence or its tie semantics. In particular,
the repository source's `MIN_L = 10` and use of hash-backed, parallel matching
make it unsafe to silently identify this implementation with a minimal finite
mathematical evaluator. The paper/supplement's exact output and tie rules remain
unrecovered.

## Why the existing witness does not transfer

### Connected distinct-read overlap check

The requested follow-up census was not run in this invocation. The prior
`AAAB` witness remains the only concrete example recorded here; its overlap
disconnection makes it unsuitable as evidence about an Eulerian spelling
procedure. In particular, the present source audit does not establish that
there are no connected `I_s`-failure singleton-fibre examples: such a negative
claim requires a precisely bounded enumeration and a completeness record. This
is an unresolved computational task, not a consequence of the algorithm-source
gap below.

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
The primary-source lookup was expanded: the article endpoint gave 403;
Crossref yielded only the abstract; the linked author implementation was
located and pinned, and its README and graph-builder/cleanup source were
inspected. That inspection narrows the blocker: a candidate could be tested
against the author's graph builder only after specifying a consistent
small-instance execution model, but correctness of that graph output still
does not equal correctness of a spelled genome because the checked-in
implementation does not include an Eulerian spelling/output procedure. A
generic decoder chosen to return the unique supported orbit would not satisfy
that burden.

No candidate search or Lean formalization was attempted: the primary paper's
exact tie/output semantics could not be recovered, and the located code stops at
graph construction rather than genome spelling. No result here upgrades the
external published reconstruction theorem or the existing generic decoder lemma
into a verified historical algorithm claim. The next decisive question is to
obtain the paper/supplement passage defining the output Eulerian path (including
ties), or an author-endorsed implementation of that output stage; only then can
the smallest connected-overlap, `I_s`-failing cases be enumerated faithfully.
