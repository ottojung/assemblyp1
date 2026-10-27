# Issue #272: bounded search status for a shared literal `I_s` fibre

_Status: 2026-10-27. This note records a bounded negative result, not a theorem
about the historical Not-So-Greedy decoder._

## Exact target

The repository's read-string adapter is
`FiniteSideInformationReadStringAdapter.isPromiseReadString`: a spelling/genome
promises a finite set `Y` of distinct read strings when there exists a start set
`R` whose induced string set is `Y` and for which
`HistoricalInformationFeasibleLiteral S L R` holds. Thus an ambiguity witness
must supply two nonrotation circular genomes, the same orientation and read
length, a common `Y`, and a literal feasible placement set for each. For a
Bayesian posterior witness, both genomes also need positive prior and positive
likelihood for the same observation. An ordered read tuple or a multiset with
counts is a distinct observation model and cannot be silently substituted for
this deduplicated `Finset` adapter.

## Result of this bounded attempt

No exact pair or general obstruction was established. I inspected the concrete
adapter and source predicate, and rebuilt the adapter module; the repository
already contains concrete repeat-bridging examples (`ABXABYABZ` and
`ABXABZABY`) where literal `I_s` fails, but those are not witnesses for this
question. In particular, a failure-of-`I_s` example cannot be used to claim two
members of the same `I_s` fibre.

The prior source-defined search verifier
`scripts/verify_272_source_defined.py` is not applicable here: it models
arbitrary truth-only/read-only promise tables over two abstract candidates and
does not enumerate circular spellings or evaluate literal `I_s`.

The earlier `ABAB`/`AABB` support example also does not meet this target: the
competing `AABB` candidate fails the supplied `I_s` promise in that fibre. The
`AAAB` example establishes existence of a certain read-only decoder when `I_s`
fails, not ambiguity or uniqueness after `I_s` conditioning.

## Reproducible verification

From the repository root, run:

```sh
lake build AssemblyP1.FiniteSideInformationReadStringAdapter
```

Observed result on branch `research/272-is-compare-VJ0Ttaxksx27FdwuEGIrya-inter`
at `7f3cecafabd572fc3ed3f1cb21427eef47ba6095`:
`Build completed successfully (8930 jobs)`. This checks the definitions and
existing finite examples, but is not an exhaustive search over genomes and does
not establish that no shared-fibre pair exists.

## Remaining lemma

For fixed genome length `G`, read length `L`, alphabet size `q`, and a specified
observation/candidate model, decide whether there exist nonrotation spellings
`u,v : Fin G → α` and a read-string set `Y` such that both adapter promises
`isPromiseReadStringSpelling G L ... u Y` and
`isPromiseReadStringSpelling G L ... v Y` hold. Any computational census must
enumerate the existential start sets and evaluate the literal predicate (all
coverage, triple-bridging, and interleaved-bridging clauses), then separately
check the chosen likelihood and prior supports. A complete finite census would
settle only its explicitly bounded `(G,L,q)` family; a general answer or
historical random-read multiplicity transfer remains open.
