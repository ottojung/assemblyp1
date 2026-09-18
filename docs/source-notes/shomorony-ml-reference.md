# Shomorony et al. maximum-likelihood reference

_Status: source note for issue #7; parent issue #1._

Primary accepted source:

- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse,
  “Information-optimal genome assembly via sparse read-overlap graphs,”
  *Bioinformatics* 32(17), 2016, i494–i502, DOI
  <https://doi.org/10.1093/bioinformatics/btw450>.

Dependency:

- issue #5 / PR #6 separates the exact global likelihood, the later
  separable/binomial approximation, and the Section 6.2 flow feasible set in
  Medvedev–Brudno (2009). This note does not assume PR #6 is on `main`.

## Question

When Shomorony et al. ask whether bridging conditions guarantee that “the
maximum-likelihood sequence is the true sequence,” do they identify which of
the distinct Medvedev–Brudno likelihood/optimization objects they mean?

## Accepted-paper evidence

The relevant passage is in Section 5, Discussion, immediately after the authors
propose asking whether information-feasible instances coincide with solutions
of a combinatorial optimization problem.

The paper first says that Theorem 1 reconstructs the true sequence but does not
guarantee that this sequence solves an optimization-based assembly formulation,
and cites Nagarajan–Pop (2009) and Medvedev–Brudno (2009) as examples. It then
contrasts parsimony-based formulations, which can over-collapse repeats, with
“the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009),”
which it describes as robust to those issues and a candidate for the correct
formulation. The next sentence states the open question about bridging
conditions and the maximum-likelihood sequence.

Recoverable location: Shomorony et al. (2016), Section 5 (Discussion), final
paragraph, especially the sentences corresponding to the accepted online text
immediately before the footnotes.

The Introduction supplies useful context but no further disambiguation. It says
that parsimony-based formulations can fail to recover the truth and describes
the paper as following the line of Medvedev–Brudno and other basic assembly
formulations while changing the starting point to information feasibility and
efficient recovery. It does not write a likelihood formula or define a
candidate class.

## Source-supported conclusion

The accepted 2016 paper identifies the intended family only by the bibliographic
reference and the phrase “maximum-likelihood formulation.” In the open-question
passage it does **not**:

- reproduce the Medvedev–Brudno multinomial likelihood;
- mention the binomial/separable approximation;
- mention the Section 6.2 overlap-graph flow feasible set;
- say that candidate genome length is fixed to the true length;
- state a candidate-genome universe for the maximum-likelihood comparison; or
- provide a theorem/equation/section pointer inside Medvedev–Brudno that selects
  one of those objects.

Therefore the accepted 2016 main text does not justify choosing the exact
multinomial objective, the approximation, or the flow optimization as *the*
unique intended formal target merely from the wording of the open-question
sentence.

This is a **source ambiguity**, not evidence that the alternatives are
mathematically equivalent.

## Important distinction: what *is* fixed in the 2016 sequencing model

Earlier in the paper, Section 2 fixes the true circular genome `s` to length
`G` and samples `N` error-free length-`L` reads independently and uniformly
from its `G` circular start positions. This fixes the data-generating model used
for the bridging theorem. It does not by itself state that a competing genome
inside the separately cited Medvedev–Brudno maximum-likelihood optimization
must also have length `G`.

Consequently, transferring `|D| = G` to every ML competitor would be an
additional modeling decision unless another source passage establishes it.

## Formalization consequence

Until stronger primary-source evidence resolves the reference, AssemblyP1
should preserve parallel, explicitly named variants rather than silently select
one:

1. exact global read-count likelihood with candidate-dependent length;
2. a fixed-length/external-length variant corresponding to the approximation's
   length convention; and
3. the graph/flow optimization as a distinct algorithmic feasible set, not an
   interchangeable synonym for either likelihood definition.

The published conjecture should not be marked as fully source-locked merely by
proving one variant. Any eventual settlement must state which variant it proves
and separately justify why that variant corresponds to the 2016 question.

## What remains to check

This note establishes what the accepted **main text** does and does not say.
Issue #7 requested inspection of supplementary/version material as well. Such
material can strengthen or resolve the ambiguity if it explicitly defines the
cited maximum-likelihood target, but absence of such a definition cannot be
proved from the main text alone. Until that inspection is complete, the
strongest justified status is: **main-text ambiguity demonstrated; broader
source reconciliation still open**.
