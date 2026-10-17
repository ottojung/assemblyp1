# Finiteness of the primitive-P2 admissible class, and the unconditional
# finite-read ML recovery theorem (issue #281)

**Research status:** Lean theorem implementations with kernel axiom audits and
a non-vacuity witness. The conjectured length bound `G ≤ 2·q^(L−1)` for
primitive words with no maximal triple repeat of length `≥ L − 1` was tested
exhaustively first (binary exhaustive to `G = 16`, ternary to `G = 11`),
refuted nowhere, and is now proved in Lean. The finite-read maximum-likelihood
theorem of #270 no longer needs a caller-supplied finite candidate family:
the family is *constructed* from the length bound.

## The problem this closes

`AssemblyP1.FiniteReadRecoveryP2Complete.finite_primitiveP2_ML_confidence`
(PR #207) proved exact iid ML error decay against a competitor family `C`
handed over by the caller, with `hAdm : ∀ D ∈ C, AdmClass …` and
`hNotRot : ∀ D ∈ C, ¬ RotEquiv …` as hypotheses. So the theorem never said
that such a family exists: the admissible class ranges over **all positive
genome lengths**, and nothing bounded the lengths.

## The theorem

**Lean:** `AssemblyP1/PrimitiveP2FiniteClass.lean`.

1. `primitive_P2_len_le` — for a finite alphabet `α` of cardinal `q`, read
   length `L ≥ 2`, `K = L − 1`, every primitive circular word with no
   maximal triple repeat of length `≥ K` has
   `G ≤ 2 * q ^ K`.
2. `primitiveP2Class_finite` — the set
   `{D : Genome α | AdmClass L D.len_pos D.sym}` is finite, for every `L`.
3. `mem_primitiveP2Candidates` / `mem_primitiveP2Candidates_iff` — the finite
   set `primitiveP2Candidates L` contains exactly the admissible genomes of
   length `≤ maxLen L`, and it contains every admissible genome.
4. `all_primitiveP2_ML_confidence` — the #270 endpoint with the finite-family
   premise removed: hypotheses are only `L ≥ 2`, the truth `S` primitive and
   P2 (the actual `def:P1P2`), and `δ > 0`; the conclusion is the exact
   exponential decay against **every** primitive-P2 admissible
   non-rotational candidate of every positive length.

Axiom audit (`AssemblyP1/PrimitiveP2FiniteClassAudit.lean`): every endpoint
depends on `[propext, Classical.choice, Quot.sound]` only. No `sorry`,
`admit`, or project-specific axiom.

## The bound is tight

`AssemblyP1/PrimitiveP2FiniteClassAudit.lean` exhibits the binary circular
word `1100`, length `4 = 2·2¹`, primitive and P2 at `L = 2`
(`candidateClass_nonempty_binary_L2`, `lenBound_tight_binary_L2`,
`witness_in_candidates`). The class is therefore nonempty, and `2·q^(L−1)` is
not merely an upper estimate. Independent exhaustive censuses found the
maximum admissible length to be exactly `2·q^K` in every case enumerated
(binary `K = 1,2,3`, ternary `K = 1`).

### Tightness for every alphabet size at `K = 1`

The single `1100` witness is generalized to a whole family in
`AssemblyP1/PrimitiveP2FiniteClassTight.lean`. For every finite alphabet `α`
with `q = |α| ≥ 2`, the **doubled alphabet** circular word

    0 0 1 1 2 2 ... (q-1) (q-1)

of length `2 * q` is primitive and P2-admissible at `L = 2`; the word is
built from an arbitrary enumeration `α ≃ Fin q` (`Fintype.equivFin`), so no
ordering or computability of `α` is assumed. Hence

    `exists_primitive_P2_at_bound_K1` :
      ∀ α, 2 ≤ |α| → ∃ S : Fin (2|α|) → α, IsPrimitive S ∧ P2 S at L = 2,

with `maxLen_two : maxLen 2 = 2 * |α|`, so the bound `G ≤ 2·q^K` is attained
at `K = 1` for every `q ≥ 2`, not just at `q = 2`.

The two P2 clauses are checked on the source-faithful definitions:

* the triple-repeat clause forbids maximal triple repeats of length `≥ 1`.
  Each symbol occurs exactly twice, so no three starts share even a length-one
  window, hence there is no triple repeat of any length (`no_triple`).
* the interleaved-pair clause forbids interleaved maximal repeat pairs. Every
  maximal repeat of the doubled word is an adjacent equal pair `(2k, 2k+1)`
  (`repeat_consec`): the length-two window map is injective
  (`window_two_injective`), so no repeat has length `≥ 2`, and the only
  length-one repeats are the adjacent pairs. Consecutive starts span either the
  empty open arc or the whole circle, so `InOpenArc` agrees on all other starts
  and the alternation condition of `Interleaved` fails (`not_interleaved`).

This is exactly the maximality point raised for this issue: P2 constrains
*maximal* repeats, and the proof derives the multiplicity cap from the real
two-sided maximality, not from the mere absence of equal windows. The `K = 1`
bound is therefore exactly tight, and the exhaustive census is corroborated by
a theorem for every `q ≥ 2`.

## Why the trap in the issue statement matters

P2 forbids **maximal** triple repeats (preceding bases not all equal *and*
following bases not all equal). It does not directly bound the multiplicity
of a `K`-window: three occurrences of the same `K`-window are only a
contradiction *after* they are extended to a maximal common window, on both
sides. The Lean proof therefore does not assert "each `K`-window occurs at
most twice"; it proves it, in the form

`P2RepeatResidual.P2.imp_nodeCount_le_two` (ordinary regime `L ≤ G`): three
starts sharing a `K`-window are extended maximally backwards (a bounded
maximum over `Icc 0 G`) and forwards, which is the primitive branch of
`RepeatAdapter.primitive_nodeCount_le_two`; either an extension phase reaches
total length `≥ G` — contradicting primitivity — or both flanks differ and
the extended triple is a long `IsMaximalTriple`, which P2 rules out. That
engine and its translation are imported, not re-proved.

`nodeWindow_injective_of_short` (wrap-around regime `G < L`): a `K`-window
with `K ≥ G` sees the whole circle, so two occurrences at distinct starts
make the word shift-invariant, hence non-primitive. Multiplicity is then `1`,
not `2`, and `G ≤ q^K`.

The translation between the two models lives in `P2RepeatResidual`:
`isTripleRepeat_of_maximalTriple` converts the repeat-theory
`IsMaximalTriple` (over `ℕ` starts, through `OrientedRigidity.cyc`) into
the source-faithful `Genome.IsTripleRepeat` (over `Fin G` starts), because
`Genome.Preceding` is literally `cyc (start + G − 1)`, `Genome.Following` is
literally `cyc (start + e)`, and `cyc` cannot see the difference between a
start and its residue. `P2.imp_noLongTripleRepeat` packages it as
`P2 hG L S → ¬ RepeatAdapter.HasLongTripleRepeat hG S L`, and
`P2.imp_nodeCount_le_two` adds primitivity. An earlier revision of this work
re-proved both; independent review found the duplication and it was removed.

Both regimes are stated, and the second is a genuine result rather than a
patch: it yields the strictly stronger `G ≤ q^K` in that regime. A framing
correction, recorded for honesty: `primitive_nodeCount_le_two` never uses its
own `L ≤ G` argument, so the wrap-around regime is not forced by the imported
signatures — it is forced by what the count itself must say when a window
wraps.

## Edge cases handled

* **Cyclic wrap (`G < L`).** `nodeWindow_injective_of_short`; primitivity
  alone forces multiplicity `1`.
* **Primitive periodicity.** `not_primitive_of_ge_G_agree` plus the
  `P2RepeatResidual.IsPrimitive.shiftPrimitive` bridge between
  `PopulationReduction.IsPrimitive` ("not an exact nontrivial power") and
  `RepeatAdapter.IsPrimitive` ("minimal period `G`").
* **`q = 0`.** No genome of positive length exists over an empty alphabet, so
  the bound gives `G ≤ 0` and the class is empty; nothing is vacuous because
  the theorem's hypotheses are on an actual `S`.
* **`q = 1`.** Only the length-1 word is primitive, and `2·1^K = 2 ≥ 1`.
* **`L = 2` (`K = 1`).** The tight regime, witnessed by `1100`.
* **`L < 2`.** Genuinely outside the theorem, and *not* because the class is
  empty. At `L = 1` the P2 triple clause is satisfied by a word whose symbols
  are pairwise distinct — no window repeats, so no triple repeat exists at
  all — and such a word has length `q > 2 = 2 · q^0`. So `2 ≤ L` is a
  necessary hypothesis. `primitive_P2_len_le` takes it explicitly, and every
  membership lemma about the finite family carries it.

## Computational evidence gathered before (and independently of) the proof

All scripts are self-contained and small; none is required for the theorem.

* `scripts/verify_281_window_cap.py` (this directory's sibling scratch) —
  exhaustive check of the crux: in every primitive binary word of length
  `≤ 16` with `K = 1..4`, and every primitive ternary word of length `≤ 11`,
  three distinct starts sharing a `K`-window do force a maximal triple
  repeat of length `≥ K`.
* Direct search beyond the bound: for `q = 2, K = 1` all primitive words of
  length `5, 6, 7` have a maximal triple repeat of length `≥ 1`; for
  `q = 2, K = 2` all of length `9, 10`; for `q = 3, K = 1` all of `7, 8`;
  for `q = 2, K = 3` all `131070` primitive words of length `17`. No
  candidate family beyond `2·q^K` exists in the enumerated range.

These searches are evidence, not proof. The proof is `primitive_P2_len_le`.

## What is imported rather than re-proved

`P2RepeatResidual.isTripleRepeat_of_maximalTriple`,
`P2RepeatResidual.P2.imp_noLongTripleRepeat`,
`P2RepeatResidual.P2.imp_nodeCount_le_two`,
`RepeatAdapter.primitive_nodeCount_le_two`,
`RepeatAdapter.not_primitive_of_ge_G_agree`,
`P2RepeatResidual.IsPrimitive.shiftPrimitive`, and
`FiniteReadRecoveryGenome.circular_exists_n_for_confidence` are all imported
unchanged. New here: `nodeWindow_injective_of_short`, the fiber count and
`primitive_P2_len_le`, the finite family `primitiveP2Candidates` with its
membership characterization, the rotation filter `nonRotationalCandidates`,
and the endpoint `all_primitiveP2_ML_confidence`.

## What is classical

The two finite sets are built with explicit classical decidability
(`Classical.dec` for `DecidableEq (Genome α)` and for the two membership
predicates), so they are not executable programs. Every membership and
non-membership statement about them is stated as a theorem
(`mem_shortGenomes`, `mem_primitiveP2Candidates_iff`,
`mem_nonRotationalCandidates_iff`) and proved. The `Classical.choice` axiom
in the audit comes from exactly this and from Mathlib; it comes from nowhere
else, and no generic likelihood proof is duplicated — the union bound and
affinity engine is `FiniteReadRecoveryGenome.circular_exists_n_for_confidence`,
and the only new content is the finite family that makes it applicable.

## Reproducing the checks

```
lake env lean -DautoImplicit=false AssemblyP1/PrimitiveP2FiniteClass.lean
lake env lean -DautoImplicit=false AssemblyP1/PrimitiveP2FiniteClassAudit.lean
lake env lean -DautoImplicit=false AssemblyP1/PrimitiveP2FiniteClassTight.lean
lake env lean -DautoImplicit=false AssemblyP1/PrimitiveP2FiniteClassTightAudit.lean
lake build --wfail
lake env leanchecker AssemblyP1.PrimitiveP2FiniteClass
lake env leanchecker AssemblyP1.PrimitiveP2FiniteClassAudit
lake env leanchecker AssemblyP1.PrimitiveP2FiniteClassTight
lake env leanchecker AssemblyP1.PrimitiveP2FiniteClassTightAudit
```

## Independent verification of the finiteness obligation

The finiteness obligation for this issue is discharged by the merged
`AssemblyP1.PrimitiveP2FiniteClass` (`primitive_P2_len_le`,
`primitiveP2Class_finite`, `all_primitiveP2_ML_confidence`). A fresh clone of
`main` was built and kernel-replayed independently:

* `lake build --wfail` succeeds for the whole library;
* `lake env leanchecker AssemblyP1.PrimitiveP2FiniteClass` exits `0`;
* `#print axioms` for `primitive_P2_len_le`, `primitiveP2Class_finite`,
  `mem_primitiveP2Candidates`, and `all_primitiveP2_ML_confidence` reports only
  `[propext, Classical.choice, Quot.sound]` — no `sorry`, `admit`, or
  project-specific axiom;
* `scripts/verify_281_window_cap.py 3 11 4` reports zero cap failures and zero
  bound failures, with `120` attainments at `G = 2·q^K`;
* the new `PrimitiveP2FiniteClassTight` endpoints likewise use only the
  standard three axioms.

## Provenance

The affinity/union-bound engine, the population uniqueness theorem
`Issue94Complete.population_unique_ML`, the maximal-extension engine
`RepeatAdapter.extend_triple` (private, consumed through
`RepeatAdapter.primitive_nodeCount_le_two`), the `P2`-to-repeat-theory
translation `P2RepeatResidual.P2.imp_noLongTripleRepeat`, and the primitivity
bridge `P2RepeatResidual.IsPrimitive.shiftPrimitive` all predate this work and
are unchanged. New here: the wrap-around injectivity regime, the fiber count
giving the length bound, and the finite candidate family.
