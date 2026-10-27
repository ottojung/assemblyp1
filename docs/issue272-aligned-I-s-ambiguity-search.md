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

## Exact finite census

The executable verifier [`scripts/verify_272_aligned_is.py`](../scripts/verify_272_aligned_is.py)
by default enumerates **all** ternary circular spellings for `3 ≤ G ≤ 5`, every
`2 ≤ L < G`, and every placement subset `R ⊆ Z/GZ`. For each placement it
computes the distinct read-string set `Y`, its saturated matching-start set,
historical `L−1` coverage, the literal all-three-occurrence bridge clause, and
the interleaved-maximal-repeat clause. It groups accepted `(genome,Y)` pairs by
the rotation-canonical spelling. The census finds **zero** `Y` with two
different rotation classes in these bounded parameters.

| `G` | `L` | ternary spellings | feasible `(g,Y)` | shared nonrotation fibres |
|---:|---:|---:|---:|---:|
| 3 | 2 | 27 | 8 | 0 |
| 4 | 2 | 81 | 15 | 0 |
| 4 | 3 | 81 | 105 | 0 |
| 5 | 2 | 243 | 18 | 0 |
| 5 | 3 | 243 | 282 | 0 |
| 5 | 4 | 243 | 756 | 0 |

Run the ternary census with `python3 scripts/verify_272_aligned_is.py`; use
`--binary` to reproduce the earlier binary census. This is an exhaustive
combinatorial check in the stated finite family, not a Lean theorem and not a
general obstruction. Its result is consistent with the externally attributed
Not-So-Greedy feasible-fibre uniqueness, but it does not prove or independently
formalize that theorem. It uses the repository adapter's **distinct read-string
set**; source random sampling multiplicities/ordered tuples still require the
placement-weighted likelihood treatment from #266.

The prior source-defined search verifier
`scripts/verify_272_source_defined.py` is not applicable here: it models
arbitrary truth-only/read-only promise tables over two abstract candidates and
does not enumerate circular spellings or evaluate literal `I_s`.

The earlier `ABAB`/`AABB` support example also does not meet this target: the
competing `AABB` candidate fails the supplied `I_s` promise in that fibre. The
`AAAB` example establishes existence of a certain read-only decoder when `I_s`
fails, not ambiguity or uniqueness after `I_s` conditioning.

## Reproducible verification

The imported literal predicate/adapter definitions also build with:

```sh
lake build AssemblyP1.FiniteSideInformationReadStringAdapter
```

`lake build AssemblyP1.FiniteSideInformationReadStringAdapter` passed on this
branch. The Python census is complete for the explicit domain above; the Lean
build checks the source definitions and existing formal examples, not the Python
loop itself.

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

In particular, no exact `I_s`-conditioned two-orbit witness was found in the
exhaustive ternary domain `3 ≤ G ≤ 5` or earlier binary domain `3 ≤ G ≤ 6`;
larger genomes, alphabets, variable-length
competitors, read multiplicity observations, and the historical algorithm's
precise candidate universe remain open.
