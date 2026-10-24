# Issue #272: boundary of the remaining Not-So-Greedy question

_Status: 2026-10-24. Research diagnostic; no claim about the 2016 algorithm is
proved here._

## Smallest next slice

The finite Bayesian theorem and the source-obstruction counterexamples settle
read-only certainty, but not whether the **specific** 2016 Not-So-Greedy
decoder is correct outside `I_s`. The next checkable subproblem is therefore
not to infer algorithm correctness from posterior certainty: first define its
input graph and output on one finite instance, including its behavior when the
graph is disconnected. The existing kernel-checked `AAAB`, `L = 3`,
`Y = {AAA, ABA}` witness is a useful boundary diagnostic, but does not answer
that subproblem.

## Exact finite diagnostic

Under the usual oriented de Bruijn overlap construction for length-`3` reads,
vertices are the observed length-`2` prefixes/suffixes, and each read is a
directed edge from its prefix to its suffix:

| read | directed edge |
|---|---|
| `AAA` | `AA → AA` |
| `ABA` | `AB → BA` |

The graph has two disconnected components. In particular, this observation
does not supply a single connected Eulerian circuit over both read edges. The
previous `I_s`-nonnecessity note correctly records this limitation; the
diagnostic here makes the actual graph explicit so a successor cannot mistake
the example's read-only certainty for a tested Not-So-Greedy output.

The read-only fact remains separate and is kernel checked by
`FiniteIsNotNecessaryCertainty.unambiguous_yaaab` and
`someReadOnlyDecoderCertain`. Those establish existence of a decoder from
unambiguous support, not the behavior of the historical Not-So-Greedy
algorithm. No algorithm output is inferred from the graph above.

## Remaining precise obligation

To proceed, formalize the source algorithm's preprocessing, graph convention,
connectivity/degree hypotheses, tie handling, and Eulerian-spelling output on
the same read-string observation. Then prove or refute correctness for this
instance. Only after that bounded case is source-faithful should it be used as
a step toward the general question: whether Not-So-Greedy can be certain on
some `I_s`-false inputs, or whether it requires `I_s` for its own correctness.

This diagnostic deliberately leaves that algorithm-specific question **open**.
It does not weaken the published sufficiency theorem, reinterpret `I_s`, or
claim that a disconnected graph is a counterexample to the algorithm; the
historical algorithm's defined behavior on such input must first be sourced.
