# Rotation invariance of the source information-feasibility predicate `I_s`, and orbit descent of `E` (#271)

_Status: research comparison note. All Lean statements referenced below are
kernel-checked in `AssemblyP1/InformationFeasibleRotation271.lean` and audited in
`AxiomAudit271.lean` (only `propext`, `Classical.choice`, `Quot.sound`). This
revision closes item 1 of §6 of
[`conditional-vs-ml-genome-adapter-271.md`](conditional-vs-ml-genome-adapter-271.md):
the candidate-specific latent-start feasibility predicate `E` of the merged
genome-level adapter is shown to descend to rotation-orbit classes, because the
exact source predicate `SourceFaithfulIs.InformationFeasible` (the `I_s` of
Shomorony et al. (2016), Eq. (1)) is invariant under circular rotation once the
latent placement set rotates with it._

## 1. The question

`AssemblyP1/ConditionalVsMLGenomeAdapter271.lean` defines

```
E i r := ∃ T : Finset (Fin 4),
            (∃ s ∈ T, (genOf i).window 2 s = r) ∧ InformationFeasible (genOf i) 2 T
```

through the chosen representatives `genOf i = toGenome (rep i)`. The likelihood
side of the adapter is known to descend to orbits
(`GenomeOrbitAdapter.readPmf_rotWord`, #269); the side-predicate side was left
open. The question is whether `InformationFeasible` is equivariant under
rotation — rotating the genome by `k` and the placement set by `-k` (equivalently,
the cross-side form below) — so that `E` only depends on the rotation class of
the candidate.

## 2. The rotation action, and the exact statement

`rotGenome S k` (for `k : Fin S.len`) rotates the circle by `k`: the symbol at
position `i` of `rotGenome S k` is the symbol at position `i + k` of `S`. On
placements, `rotStartEmb S k` is the embedding `r ↦ r + k` of `Fin S.len`.

The main theorem is

```
informationFeasible_rotGenome :
  InformationFeasible (rotGenome S k) L R ↔
    InformationFeasible S L (R.map (rotStartEmb S k)).
```

It is proved at the generic `Genome α` level, not only for the length-`4`
adapter genomes. It is the cross-side equivariance: a placement set `R` is
feasible for the genome rotated by `k` iff the placement set rotated by `k` is
feasible for the original. Equivalently, rotating the genome by `k` and the
placement set by `-k` leaves `InformationFeasible` unchanged. The same-direction
diagonal form (`g ↦ rotGenome S k` with `T ↦ R.map (rotStartEmb S k)` in one
step) is **not** claimed and is false in general.

The development is structured so that the only non-symbol-free ingredients are
the repeat clauses:

* `rotGenome_window`: `(rotGenome S k).window e r = S.window e (r + k)`. Through
  it, `Agree`, `IsRepeat` and `IsTripleRepeat` are equivariant under the
  *simultaneous* rotation of the genome and all selected starts
  (`rotGenome_agree`, `rotGenome_isRepeat`, `rotGenome_isTripleRepeat`).
* `ReadCovers`, `Covers`, `BridgesCopy`, `BridgesRepeat`,
  `IsTripleRepeatAllBridged`, `InOpenArc`, `Interleaved` and
  `IsInterleavedPairBridged` mention the genome only through `len`, which
  `rotGenome` preserves definitionally, so they are invariant with no change to
  the placement set (`rotGenome_covers`, `rotGenome_bridgesCopy`, …).
* The one interaction with the placement set: `bridgesCopy_map_rotStartEmb`
  relates bridging by shifted reads to bridging of the shifted copy, and
  `covers_map_rotStartEmb` relates coverage of the shifted placement set to
  coverage of the original (a read shift is a bijection of positions). The
  modular arithmetic is isolated in `mod_cancel_add`, `mod_intro_add`,
  `bridges_mod_cancel`, `bridges_mod_intro`.
* The interleaved clause needs `InOpenArc` / `Interleaved` to be invariant under
  translating all selected starts (`inOpenArc_sub_add`, `interleaved_sub_add`,
  `interleaved_add`), which is the observation that `InOpenArc S a b p` is the
  comparison of the clockwise arc distances `(p - a).val` and `(b - a).val`
  (`inOpenArc_iff_sub`).

## 3. Orbit descent of `E`

At the source-faithful `Genome Sym` level the predicate is

```
EGenome g r := ∃ T : Finset (Fin g.len),
                 (∃ s ∈ T, g.window 2 s = r) ∧ InformationFeasible g 2 T,
```

so `E i r ↔ EGenome (genOf i) r` (`E_eq_EGenome`). From
`informationFeasible_rotGenome` and `rotGenome_window`,

```
EGenome_rotGenome : EGenome (rotGenome g k) r ↔ EGenome g r.
```

The `ZMod 4`-word rotation of #269 is the `rotGenome` rotation on the
source-faithful genome (`toGenome_rotWord`), hence

```
E_rotWord : rep j = rotWord (rep i) k → (E i r ↔ E j r),
```

and `E` descends to a well-defined predicate on the genuine rotation-orbit
quotient

```
Eorb : Quotient (rotSetoid Sym 4) → Read → Prop,
Eorb_orbit : Eorb (orbit i) r ↔ E i r.
```

`Eorb` is defined on the *whole* quotient `Quotient (rotSetoid Sym 4)`, not only
on the three classes of the adapter; `Eorb_orbit` identifies its value on the
adapter's classes with `E`.

## 4. Orbit-level (A ∧ ¬B) separation

Because `Eorb (orbit ·)` is propositionally equal to `E` (`Eorb_pred_eq_E`), the
merged `separation_genome` holds with the orbit-level predicate:

```
separation_orbit :
  (∀ i, 0 ≤ prior i) ∧ (∑ i, prior i = 1) ∧ (∀ i, ∑ w, p i w = 1) ∧
  posteriorMass prior p EorbPred orbit (r2 0 0) (orbit 1) = 1 ∧
  p 1 (r2 0 0) < p 0 (r2 0 0) ∧ ¬ MLMax 1 (r2 0 0) ∧
  posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1.
```

So the conditional certainty (A) is now a statement about rotation-orbit classes
rather than about the chosen representatives, on exactly the shared generative
model of the merged adapter.

## 5. Honest boundaries (labelled, not claimed)

* This closes the **representative-dependence** gap of `E`. It does not prove the
  general `E → B` implication; on this model `sep_truth_not_ml` refutes it (see
  item 3 of §6 of the adapter note). The refinement under which `E → B` does
  hold is the ML-soundness condition of
  `AssemblyP1/ConditionalBayesEImpliesB271` (#271), unchanged here.
* The adapter still observes a **single** read string and existentially
  quantifies the latent placement; the gap to the source's full sampled read-set
  and weighted-placement event mass
  (`AssemblyP1.ConditionalIdentifiability.PlacementModel`) remains **open**
  (item 2 of §6 of the adapter note).
* The ordinary-ML classification (#255/#258/#259/#261) is untouched, and #269's
  I_s-vs-Unambiguous comparison and the #269 Bayes/MAP theorem are reused by name
  rather than restated.

## 6. Manuscript-safe wording (for #265/#268, non-competing)

> The source information-feasibility predicate `I_s` is equivariant under
> circular rotation: rotating the genome by `k` and the latent placement set by
> `-k` preserves `InformationFeasible` (equivalently, a placement set is feasible
> for the rotated genome iff the placement set rotated by `k` is feasible for the
> original). Consequently the candidate-specific latent-start
> feasibility event `E` of the genome-level adapter — `∃` placement `T` that is
> `I_s`-feasible and realizes the observed read — depends only on the rotation
> orbit of the candidate, not on the chosen representative, and the
> conditional-certainty-versus-ordinary-ML separation holds at the orbit level.
> The likelihood side already descended to orbits (`readPmf_rotWord`); this is
> the matching descent of the side predicate.
