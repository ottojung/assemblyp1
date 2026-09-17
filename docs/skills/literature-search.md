# Literature search

Use this skill to determine what the accepted literature actually states, how later work cites it, and which definitions must be preserved in the formal model.

## Objective

Produce recoverable source evidence, not a topical summary. The output should let another researcher reconstruct the exact statement without trusting the searching agent.

## Source order

Prefer:

1. the original accepted paper defining the model or theorem;
2. the authors' supplementary material or formal errata;
3. later peer-reviewed papers that explicitly restate, refine, solve, or cite the question;
4. dissertations or authoritative surveys for navigation and historical context;
5. informal sources only for finding primary literature, never as the final authority for a mathematical definition when a primary source exists.

Track versions. If arXiv and journal versions differ, identify which statement belongs to which version.

## Search procedure

### Recover the exact claim

Search by exact quoted sentence, distinctive terminology, authors, theorem names, and citation chains. For an open problem, search both forward citations and nearby terminology that later authors may have renamed.

### Read context, not snippets

For every consequential statement, inspect the surrounding definitions and assumptions. Record section/page/theorem/equation when available. A sentence such as "the ML sequence" is insufficient unless the candidate class, likelihood model, and equivalence convention are known.

### Build a convention matrix

For papers being reconciled, record at least:

| Dimension | Source A | Source B | Consequence |
| --- | --- | --- | --- |
| genome topology | | | |
| genome length known/fixed | | | |
| strand/orientation | | | |
| read length | | | |
| read errors | | | |
| sampling distribution | | | |
| multiplicity retained | | | |
| candidate genome class | | | |
| genome equivalence | | | |
| repeat definition | | | |
| bridging definition | | | |
| ML objective | | | |
| tie semantics | | | |

Add rows when the sources reveal other relevant differences.

### Separate quotation, paraphrase, and inference

A source note must make clear which parts are directly stated and which are the researcher's interpretation. Never cite a paper for an implication it does not itself assert without marking the implication as analysis.

### Search for settlement

When testing whether an open problem remains open:

- inspect papers that cite the original;
- search the exact problem phrase and mathematical synonyms;
- search the authors' later work;
- search for claimed counterexamples and impossibility results;
- search adjacent fields when terminology may have shifted;
- note the search date and databases/indexes used.

Failure to find a solution is evidence of non-discovery, not proof that the problem remains open.

## Deliverable

A useful handoff contains:

```text
Question investigated:
Primary sources:
Exact definitions/results recovered:
Locations in source:
Convention mismatches:
Later relevant citations:
What is directly sourced:
What remains inference/ambiguous:
Effect on the Lean model or theorem statement:
```

If the task resolves a modeling ambiguity, update the relevant project documentation and cite the primary source there. If it reveals an unresolved fork, preserve the fork rather than choosing the easier formalization.
