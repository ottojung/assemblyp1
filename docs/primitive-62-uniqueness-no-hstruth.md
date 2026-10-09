# #246: primitive §6.2 candidate uniqueness without the truth certificate is false

_Status: kernel-checked refutation. `AssemblyP1/Primitive62Uniqueness.lean`;
`lake build`-equivalent check with warnings-as-errors; every exported theorem's
`#print axioms` is `[propext, Classical.choice, Quot.sound]`._

## 1. The claim considered

The #211 / PR #124 theorem
`AssemblyP1.SameLength62Uniqueness.unique_62_maximizer_up_to_rotation` proves
that every genuine same-length Medvedev–Brudno §6.2 candidate `D` is a cyclic
shift of the truth `S`, from full source-faithful `I_s` at the realized start set
— **provided** a genuine §6.2 certificate for the truth itself (`hStruth`) is
supplied. The #211 source is explicit that `hStruth` is a nontrivial extra
hypothesis: it says the truth has complete observed support.

Board #246 asks whether `hStruth` can be dropped when `S` is **primitive**. The
formal claim (`AssemblyP1.Primitive62Uniqueness.NoHStruthPrimitive62Uniqueness`)
is:

> for every length-`4` truth `S`, realization `ρ`, and §6.2 vertex list `verts`
> equal to the actually observed oriented read-type set, if
> `S` is primitive, `I_s` holds at exactly `realizedStarts ρ`, and `D` is a
> same-length genuine §6.2 candidate (`Is62Candidate62`), then `D` is a cyclic
> shift of `S`.

This is the uniqueness reading only. The maximum-likelihood objective is kept
separate from §6.2 admissibility, per
`docs/source-notes/medvedev-brudno-candidate-class.md` and
`docs/ml-formalization-contract.md`; the refutation below uses no likelihood
value.

## 2. Result: the claim is false

`noHStruthPrimitive62Uniqueness_refuted` proves
`¬ NoHStruthPrimitive62Uniqueness`. The witness is the minimal binary instance
already used by #88 as a *negative* maximizer result:

| object | value |
| --- | --- |
| alphabet | `{A, B}` |
| truth `S` | `AABB` (`0011`), `G = 4` |
| read length | `L = 2` |
| realization `ρ` | `![1, 3]` — reads at starts `1` and `3` |
| realized starts | `realizedStarts ρ = {1, 3}` |
| observed reads | `AB` (`01`) at start `1`, `BA` (`10`) at start `3` |
| `verts` | `[AB, BA]` = exactly the observed read types |
| competitor `D` | `ABAB` (`0101`), same length `4` |

Kernel-checked facts (`AssemblyP1.Primitive62Uniqueness`):

* `S_primitive` — `AABB` is primitive: no nonzero shift below `4` fixes it.
* `infoFeasible_realizedStarts` — `InformationFeasible ⟨4, hG, S⟩ 2
  (realizedStarts ρ)` holds at full strength (all three `I_s` clauses, decided by
  computation). The realization's starts `{1, 3}` cover all four positions; there
  is no triple repeat; the only repeat pair does not interleave.
* `verts_correspondence` — the §6.2 vertex list is exactly the observed support
  `{w | 0 < observedOf hG S ρ w}`. `hwx` records the one-sided form.
* `D_is_genuine` — `ABAB` satisfies `Is62Candidate62` at `verts = [AB, BA]`:
  `Represents62` holds, the walk flow is the spelling's own flow
  (`walkFlow_eq_flow`), and the literal `SpelledFeasible62` certificate is the
  one already kernel-checked as
  `SameLengthExactMLCounterexample.competitor_spelledFeasible62`.
* `D_not_rotation` — `ABAB` is not a cyclic shift of `AABB`.
* `genuine_candidate_exists_not_rotation` — the genuine candidate class is
  non-empty and already contains a non-rotation member.

## 3. Why primitivity does not help

`SameLength62Maximizer.genuine62_support_eq` (proved) says a genuine §6.2
candidate's window support equals the **observed** read-type set, not the truth's
window support. Here:

* the truth's window support is `{AA, AB, BB, BA}`;
* the observed support is `{AB, BA}` (the `AABB` windows `AA`, `BB` were never
  observed).

A length-`4` word whose windows are exactly `{AB, BA}` need not be a rotation of
`AABB`; `ABAB` is one. It is a closed walk in the observed read-overlap graph,
because that graph has no vertex for the unobserved `AA` or `BB` (its vertices
are the observed reads `AB` and `BA`, joined by the two overlaps `AB → BA` and
`BA → AB`). Primitivity constrains the truth's period structure and is
irrelevant to this obstruction. Nor does the #243 support-rotation lemma apply:
`AABB` is not a simple cycle at `L = 2` (the node `A` has two outgoing read
types, `AA` and `AB`), so `RepeatAdapter.IsSimpleCycle` fails and
`CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_support_subset` cannot be
used.

The exact hypothesis that fails is `hStruth`: `S_not_genuine` proves the truth is
**not** a genuine §6.2 candidate here. The #88 module already recorded the
underlying asymmetry (`truth_not_spelled_on_observed`): clause 1 of `I_s` is
*position* coverage, which does not force every length-`L` window of the truth to
have been observed.

## 4. The high-leverage positive route is refuted here too

A natural plan to remove `hStruth` is to prove, from `I_s` + read provenance + the
existence of one genuine same-length candidate, that the observed `L`-mer support
equals the truth's full support, or at least that `specCount(D) = specCount(S)`
(after which the #211/#94 rigidity route yields rotation with no truth
certificate). Both intermediate claims are false at this instance and are
refuted explicitly:

* `observed_support_ne_truth_support` — `{AB, BA} ≠ {AA, AB, BB, BA}`
  (`AA` is a truth window that is not an observed read);
* `specCount_D_ne_S` — `d_D(AA) = 0 ≠ 1 = d_S(AA)`.

So no support- or spectrum-forcing lemma exists under these hypotheses, and the
shortcut to the #211 uniqueness conclusion via the primitive rigidity route is
not available.

## 5. Existence versus non-uniqueness (the two failure modes are distinct)

This repository now records both possible ways the no-`hStruth` statement can
fail, and they are different:

* **Non-unique actual candidates (this note).** `AABB`/`ABAB`: the genuine §6.2
  candidate class is non-empty (`ABAB` is in it) and contains a member that is
  not a rotation of the truth. The uniqueness conclusion fails on a real
  candidate.
* **No candidate exists (vacuous).** `AssemblyP1.AcgtWitness211`: truth `ACGT`,
  `L = 3`, starts `{0, 2}`. `I_s` holds and `hStruth` fails (the `3`-mers `CGT`
  and `TAC` are unobserved), but the overlap graph has no edges, so there is **no**
  closed §6.2 candidate at all. There the uniqueness claim is vacuous rather than
  false.

The #246 refutation is of the first kind: it is not an existence failure and is
not vacuous.

## 6. Source fidelity and remaining obstacles

* The §6.2 object is the literal bidirected-flow feasible set of Medvedev–Brudno,
  *Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116,
  §6.2, as encoded in `AssemblyP1.Section62Flow` (vertices = observed reads,
  vertex lower bound `1`, closed circuit). See
  `docs/section62-mb09-bidirected-graph-audit.md` §1 and
  `docs/source-notes/medvedev-brudno-candidate-class.md` §3.
* The published open question of Shomorony et al. (2016) concerns the
  maximum-likelihood sequence. This note settles only the §6.2 *uniqueness*
  reading without `hStruth`, and keeps the ML objective separate: no likelihood
  comparison is used. (The same instance also beats the truth in the exact
  objective, recorded in `AssemblyP1.SameLengthExactMLCounterexample`, but that
  is not part of this refutation.)
* Obstacles, recorded accurately: `hStruth` is not derivable from `I_s` at the
  realized starts; the #243 rotation lemma needs `IsSimpleCycle S`, which
  primitivity does not supply; and the Bresler–Bresler–Tse complete-spectrum
  input remains an explicit external premise in the `of_bbt` surface.
* No new `axiom`, `sorry`, or `admit`; no definition was changed to make a
  theorem provable.
