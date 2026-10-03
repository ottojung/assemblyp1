# §8 of `BBTReplacementInvariant.lean`: a genome of minimal period `G/2` has no bad `θ`

Front `94a04` (§5 of `/workspace/BOARD94-BADNESS-0153.md`) left three cases of
the surviving crux configuration; this note records the discharge of **case 3**,
the fully-periodic one, and the census that was run *before* the proof.

## The claim, in the repository's language

Case 3, verbatim from §5 of `BOARD94-BADNESS-0153.md`: a genome whose minimal
period is `G/2` — so every `(L-1)`-mer occurs exactly twice and every
occurrence pair is preceding-blocked — admits no bijective, fibre-preserving,
one-cycle `θ` with `¬ OrbitVertexEq θ`.

Proved, at `AssemblyP1/BBTReplacementInvariant.lean:1359` and `:1398`:

* `half_no_bad_theta` — for **any** `n < G` that is a period of the word and
  at which every `(L-1)`-mer occurs exactly twice, **every** fibre-preserving
  `θ` satisfies `OrbitVertexEq θ`.  No bijectivity, no one-cycle hypothesis.
* `half_no_bad_theta_twoPeriod` — case 3 exactly, with `G = 2 * n`; the
  conclusion is stated as the negation of the existential of a bijective,
  fibre-preserving, one-cycle `θ` with `¬ OrbitVertexEq θ`.

The preceding-blocked clause of case 3 is carried as `_hprec` and is **not
used**: in this regime it is automatic, since `Preceding` inherits the period
`n`, and the conclusion does not need it.

## Why the crossing analysis of §7 was unnecessary

§7 of the report describes case 3 as "`ρ` permutes two 2-element shift
classes, and `θ` one-cycles only if the two transpositions form a crossing AND
something more". That is correct but strictly more than needed. `ρ = nextPos⁻¹ ∘ θ`
is indeed forced to act on the pairs `{x, x + n}` — that is
`half_theta_land`, `AssemblyP1/BBTReplacementInvariant.lean:1323` — but once
that is known, `θ` advances exactly one step around the circle modulo `n`, so
its orbit reads off the truth's vertex cycle with shift `k = 0`. There is no
bad `θ` to exclude, so `crossing_criterion_5` and the `K = 4`/`, 6` case
analysis never come into play.

Formally: `vtx` has period `n` (`half_vtx_period`, `:1309`, from `IsPeriod`-level
`hper`), so `vtx (θ^[j] x) = vtx (rotAdd j x)` follows by induction on `j` from
`half_theta_land`, and `OrbitVertexEq` is that statement at `x = origin` with
`k = 0`.

## Bounded census — labelled evidence, not proof

`scratch/halfperiod_census.py`. Range actually covered:

* `1 ≤ n ≤ 4` (`G = 2n ≤ 8`): **all** `G!` permutations of `Fin G` for every
  binary word of period `n` and every `2 ≤ L ≤ G + 1` with every `(L-1)`-mer
  occurring exactly twice;
* `n = 5, 6` (`G = 10, 12`): every member of the candidate set
  `{θ x ∈ {x + 1, x + 1 + n}}`, which §8 shows is *exactly* the fibre-preserving
  `θ`'s (verified independently by exhaustive check at `n ≤ 4`: 1496
  fibre-preserving `θ`, 0 outside the candidate form).

830 instances, 20 012 bijective fibre-preserving one-cycle `θ`, **0** with
`¬ OrbitVertexEq`, every instance with all occurrence pairs preceding-blocked.

This is a Python enumeration whose correspondence to the Lean definitions is
not machine-checked. It is evidence, and it is what the pass falsification-first
rule asked for; the proof in §8 is independent of it and holds at general `G`.

## Status

`InterleavingObstructionNeeded` (§5.4) is **still open**. What is gone is
case 3 of §5. The two remaining cases are case 1 (exactly one constituent
blocked, the other unblocked) and case 2 (both blocked, unequal finite
backward steps).
