# Longer shared overlaps alone do not preserve spelling

**Status:** Lean-kernel-checked finite counterexample to the repository's longer-overlap-only predicate, **not** a claim that Myers's published algorithm removes this edge.

Medvedev–Brudno (2009) §6.2 uses the phrase "two shorter overlaps". Myers (2005) measures edges by newly appended extension length and requires a transitive detour to spell the same word. At fixed read length L, the extension is L minus nucleotide overlap, so smaller extensions mean larger nucleotide overlaps; **equal spelling is an additional constraint**.

The repository has three predicates worth distinguishing:

1. **Literal shorter shared overlaps:** Section62Flow.isReducibleB, earlier kernel-checked vacuous for proper equal-length overlaps.
2. **Longer shared overlaps alone:** Section62Flow.isReducibleLongerB, comparing two maximal detour overlaps to a direct overlap but not checking their composed spelling.
3. **Spelling-preserving candidate:** Section62SpellingReductionCandidate.isReducibleSpellingB, demanding genuine proper overlaps of lengths l1,l2 and the composition equation **l1+l2 = L+ell**, justified by the existing kernel theorem spellPath_eq_spellDirect.

## Finite witness (L=4, minimum overlap 1)

Observed oriented reads are u=AAAT, v=TAAA, and m=ATTA.

The direct edge u→v has nucleotide overlap ell=1 and spells **AAATAAA** (length 7). The longer-only criterion finds two detour overlaps u→m and m→v, both of shared nucleotide length 2, and deletes the direct edge. But the detour spells **AAATTAAA** (length 8), not the same word: 2+2=4 while the required composition sum is L+ell=5.

The two length-4 words internally skipped by the direct overlap are AATA and ATAA, neither observed. The spelling-preserving reduction consequently **retains** the direct edge.

## Kernel certificate

AssemblyP1/Section62ReductionMismatch.lean imports the project's actual predicates and uses finite decidability to prove:

- the direct edge belongs to the genuine overlap graph;
- it is removed under the broad longer-overlap-only predicate;
- it survives the spelling-preserving predicate;
- the two actual spelled words are unequal;
- neither skipped length-4 word is in the observed read set.

The combined Lean theorem is longer_is_not_spelling_preserving. It is imported by AssemblyP1.lean so the full library CI and axiom audit cover it. The finite example is oriented (identity reverse-complement operation), isolating the overlap-length error without claiming complete bidirected source fidelity.

**Scientific consequence:** do not label the broader longer-overlap-only filter as the exact Myers string-graph reduction in manuscripts or code comments. This finite witness does not invalidate pre-existing scoped Lean theorems or establish algorithmic equivalence between the spelling-preserving candidate and every detail of Myers's 2005 implementation.

Primary sources: Medvedev–Brudno, Maximum Likelihood Genome Assembly (2009), https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/ ; Myers, The fragment assembly string graph (2005), https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf .
