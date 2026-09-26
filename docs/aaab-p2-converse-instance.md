tion.RotEquiv hG` | #70, consumed by the population theorem #73 |
| forward multiplicity cap | `∀ k ∈ genomeNodes, nodeCount k ≤ 2` | #69 `rigidity_same_spectrum` |

No second notion of P2, of maximal repeat, or of interleaving is introduced
or assumed. Per the converse note, the failure already occurs at the
triple-repeat clause at `K = L - 1 = 1` (the symbols at starts `0, 1, 2` are
a maximal length-one triple repeat), so the interleaved-pair clause of
Ukkonen's condition is neither needed nor modelled. The multiplicity cap of
#69 also fails here (the symbol `A` occurs at `3` of the `4` starts), so the
instance lies genuinely outside the forward hypothesis region, not merely
outside its repeat-syntax half.

## Kernel-checked surface (`AssemblyP1/AAABConverse.lean`)

| theorem | content |
|---|---|
| `aaab_has_long_triple_repeat` | `HasLongTripleRepeat hG4 truth 2`: the P2 clause fails at starts `0,1,2`, `ℓ = 1` |
| `fibre_singleton_truth` | every same-length candidate with the truth's complete `2`-spectrum is a rotation of the truth (`RotEquiv4`, exhaustive `decide` over all `2^4 = 16` candidates) |
| `rotEquiv4_iff` | the `Fin`-indexed rotation form is equivalent to the repository's `RotEquiv` |
| `fibre_singleton_truth_rot` | the same statement at the actual predicates `specCount` and `RotEquiv` |
| `fibre_card_truth` | the fibre has exactly `4` elements, i.e. exactly the `4` rotations of the primitive truth |
| `fibre_contains_rotations`, `spec2_rot` | all rotations lie in the fibre (rotation invariance of the spectrum) |
| `truth_primitive` | `RepeatAdapter.IsPrimitive hG4 truth`: no nonzero shift below `G` preserves `AAAB` |
| `node_count_A`, `truth_outside_forward_hypothesis_region` | the #69 multiplicity cap fails at the node `A` (`3 > 2`) |
| `aaab_p2_fails_fibre_singleton` | the packaged final statement |
| `complete_spectrum_identifiability_does_not_imply_P2` | the converse, isolated as an existential statement |

`#print axioms` on the packaged theorems reports only `propext`,
`Classical.choice`, `Quot.sound`: no `sorry`, no `admit`, no added axiom.
The package is exhaustive, not a sample: the fibre claim is a `decide` over
the entire finite candidate universe, and the spectrum/primality data are
decided over the whole `Fin 4` index range.

The exact spectrum is also recorded concretely:
`specCount truth (AA) = 2`, `(AB) = 1`, `(BA) = 1`, total mass `4 = G`.

## Boundary of the result

* **Model.** Oriented, complete-spectrum, same-length model only. Nothing
  here concerns finite sampled-read likelihood, uniform recovery, ML
  optimality, or reverse-complement-collapsed molecule classes.
* **Alphabet.** The Lean statement ranges over the repository's two-letter
  alphabet. The converse note's uniqueness *proof* (the order-1 de Bruijn
  argument: the only Eulerian traversal of `AA{loop,loop} + AB + BA` is
  `AA, AB, BA, AA`) is alphabet-independent; the Lean instance reproduces
  that claim exhaustively for the binary universe only. Extending the
  kernel-check to arbitrary finite alphabets is not attempted here and is
  **not** claimed.
* **Direction.** This refutes the *necessity* of P2 for complete-spectrum
  identifiability. It does not refute, weaken, or require any change to the
  forward theorems of #70 (division–Eulerian gcd-one), #73 (population
  uniqueness for primitive P2 genomes), #69/#74 (same-length spectrum
  rigidity under `¬ HasLongTripleRepeat`).
* **Not the open problem.** Nothing here bears on whether a bridging
  condition guarantees that the maximum-likelihood sequence is the true
  sequence in the published model; that question is untouched, and the
  candidate-intrinsic `AdmP2` predicate of #70/#73 remains an opaque
  external parameter there.
* **Discovery evidence.** The converse note's bounded binary search
  remains computational evidence; the instance above is now kernel-checked,
  but the note's *exhaustiveness claim for the search scope* is not
  reproduced by this file.
