# #211: the §6.2 same-length maximizer versus uniqueness up to rotation

This note is the companion to `AssemblyP1/SameLength62TieUniqueness.lean` and
`AssemblyP1/SameLength62Uniqueness.lean`. It records the reviewed finite theorem
surface, the audit of the primitive and nonprimitive subcases, the #88
dominance-vs-membership audit, and the final uniqueness result. Every claim is
tagged **[fact]** (kernel-checked or computationally verified), **[inference]**
(mathematical argument, not Lean), or **[choice]** (a modeling or scoping
decision).

## 1. The question

The oriented same-length §6.2 model asks: when the maximum-likelihood sequence
is tied, is it the truth? The maximizer half is already proved
(`SameLength62Maximizer.informationFeasible_62_maximizer`,
`MLEscape.informationFeasible_62_spelledML`); this front proves the uniqueness
half: under `I_s`, every genuine §6.2 candidate is a cyclic shift of the truth.

## 2. Reviewed theorem surface

All theorems below are kernel-checked with axioms `propext`, `Classical.choice`,
`Quot.sound` only. No `sorry`, no `admit`, no unproved axioms. **[fact]**

| theorem | statement | role |
| --- | --- | --- |
| `informationFeasible_62_exact_tie` | every genuine §6.2 candidate under `I_s` ties the truth exactly | the `≤` is an `=` |
| `same_support_word_ties_truth` | tie class = same-support class (no §6.2 certificate needed) | characterization of the tie class |
| `support_eq_iff_specCount_eq` | under `I_s`, support equality ↔ spectrum equality | tie class = spectrum fibre |
| `support_rigidity_iff_fibre_singleton` | residue ↔ fibre singularity | the two forms of the residue |
| `unique_62_maximizer_up_to_rotation_of_support_rigidity` | residue → uniqueness | what the uniqueness reading needs |
| `unique_maximizer_up_to_rotation_of_residue` | `FibreFreedomForcesLongRepeat` + `I_s` → uniqueness | the combinatorial route |
| `bbt_premise_refuted_G6_L2` | the external BBT premise is false in this model | the BBT route is blocked |
| `equal_spectrum_not_cyclic_shift` | exported counterexample (G=6, L=2) | single kernel-checked witness |
| `truth6_not_information_feasible` | the refutation witness is not `I_s`-feasible | the refutation does not touch the hypothesis surface |
| `truth4_support_rigid` | at the floor instance the fibre is a singleton | the residue is not vacuous |
| `truth4_tie_instance` | the tie conclusion verified at the floor instance | finite instance |
| `informationFeasible_P2` | `I_s` → `P2` | the `I_s` → Ukkonen bridge |
| `informationFeasible_Ukkonen` | `I_s` → Ukkonen at `K = L-1` | the source's Theorem 3 hypothesis |
| `fibre_singleton_of_Iss_and_obstruction` | `I_s` + `EulerianCycleObstruction L` → fibre singleton | the external route |
| `iss_does_not_imply_P1` | `I_s` does not imply the branch-free `P1` | the `P1` route is blocked |
| `bbTP2Prim_of_94` | `BBTP2Prim L` inhabited for `2 ≤ L` | the #94 primitive route |
| `unique_62_maximizer_up_to_rotation_of_primitive` | primitive `I_s`-feasible truth: uniqueness | the primitive subcase, proved |
| `unique_62_maximizer_up_to_rotation` | **every** `I_s`-feasible truth: uniqueness | **the full uniqueness theorem** |

## 3. The primitive subcase is proved

**Theorem.** Under `I_s`, if the truth `S` is primitive, then every genuine
same-length §6.2 candidate is a cyclic shift of `S`. No external hypothesis.
**[fact]**

The chain is:

1. `I_s` gives `P2` (`informationFeasible_P2`). **[fact]**
2. The merged #94 route gives `BBTP2Prim L`: the long half
   `Issue94ConcreteAntiderivative.concrete_p2LongUnique` (for `K ≥ L`) and
   the short half `Issue94Split.shortRangeUnique` (for `K < L`), joined by
   `Issue94Interface.long_short_of_long`. **[fact]**
3. `BBTP2Prim L` at the truth `S` (which is `P2` and primitive) turns the
   candidate's equal spectrum into `RotEquiv hG D S`. **[fact]**
4. `rotEquiv_iff_isCyclicShift` turns that into `IsCyclicShift hG D S`.
   **[fact]**

This is the largest subcase that closes without the §2 residue or the §5
obstruction. The split on `IsPrimitive S` is explicit: the nonprimitive case
is **not** assumed. **[choice]**

## 4. The nonprimitive subcase: closed via #243

**Theorem.** Under `I_s`, if the truth `S` is nonprimitive, then every genuine
same-length §6.2 candidate is a cyclic shift of `S`. **[fact]**

The chain is:

1. `I_s` gives `¬ HasLongTripleRepeat` (`BridgingBridge.informationFeasible_no_long_triple_repeat`). **[fact]**
2. `primitive_or_minimal_period` gives a minimal period `p` with `HasMinimalPeriod hG S p`. **[fact]**
3. `periodic_factor_distinct` (from `HasMinimalPeriod` + `¬ HasLongTripleRepeat`) gives distinctness of the period's `(L-1)`-windows. **[fact]**
4. `periodic_cycle_shape` gives `IsSimpleCycle L hG S`. **[fact]**
5. The #243 lemma `CycleSpellingRotation.isCyclicShift_of_isSimpleCycle_specCount` converts `IsSimpleCycle` + spectrum equality directly into `IsCyclicShift`. **[fact]**

The spectrum equality comes from the §6.2 bridge (`oriented_support_eq_of_genuine62` + `Is_spectrum_eq_of_support_eq`). No `NoBranching` formalization is needed; the #243 lemma subsumes the deterministic-continuation step.

The split on `IsPrimitive S` is explicit: both cases are fully kernel-checked. **[fact]**

### The original mechanism is false

The note's §4 originally argued: `P2` forces the truth to be a square
(`S = T^2`), the `(L-1)`-mer graph of a square is a simple cycle with doubled
edges, and a simple cycle has a deterministic successor, so the Eulerian
cycle is unique up to rotation. **Both mechanism steps are false:**

1. **`P2` does not force `k = 2`.** `P2` forbids *maximal* triple repeats
   (`Genome.IsTripleRepeat` carries the two-sided maximality condition), and a
   substring occurring once per copy of `T` is a triple repeat that is **not**
   maximal in general. The smallest counterexample is `S = 010101` at `L = 2`:
   the primitive root is `T = 01` with `k = 3`, and `S` satisfies `P2` (and is
   fully `I_s`-feasible at the full read set), because every `0` is preceded
   and followed by `1` and vice versa, so no repeat is maximal. **[fact]**
   (kernel-checked: `SameLength62Nonprimitive.p2_does_not_force_k2`).
2. **The `(L-1)`-mer graph need not be a simple cycle.** The edge multiplicity
   is `k`, which can be `≥ 3`, and the graph can branch in the de Bruijn sense.
   At `S = 0011^3` (`G = 12`, `k = 3`), `P2` holds at `L = 3` but the `2`-mer
   graph branches (each `1`-mer vertex carries a self-loop and a cross edge);
   at `S = (abcab)^2` (`G = 10`, `k = 2`), `P2` holds at `L = 4` but the
   `3`-mer graph branches at `ab`. **[fact]**
   (`scripts/verify_samelength62_mechanism_refutation_211.py`).

### The corrected residue: `NoBranching`

The conclusion the note wants — a nonprimitive `I_s`-feasible truth has a
spectrum fibre that is a singleton up to rotation — is **supported** by the
finite search (`scripts/verify_samelength62_nonprimitive_211.py`: zero
branching failures, zero non-single-cycle failures, zero non-singleton-fibre
failures, over every binary word of length `≤ 10` and ternary word of length
`≤ 8`), but the note's *route* to it is invalid. The correct route is:

1. **`P2` + nonprimitive ⟹ no branching.** Every `(L-1)`-mer of the truth is
   followed by a *unique* symbol. A branch (an `(L-1)`-mer with two distinct
   followers) extends backward to a maximal repeat, and the periodicity of a
   nonprimitive word then promotes it to a maximal **triple** repeat of length
   `≥ L - 1`, which `P2` forbids. This is the exact residue, stated as the
   `NoBranching` predicate in `SameLength62Nonprimitive`. **[choice]** (the
   residue; the backward extension and triple promotion are not formalised).
2. **No branching ⟹ deterministic successor.** The successor map on distinct
   `(L-1)`-mers is well-defined. **[inference]**
3. **The successor is a single cycle.** The truth spells a circuit of its
   successor graph, so the graph is connected; with out-degree `1` it is a
   single cycle. **[inference]**
4. **A same-spectrum word follows the same successor.** Equal spectra give the
   same `L`-mers, hence the same `(L-1)`-mers and the same unique followers.
   **[inference]**
5. **A single cycle has a unique Eulerian circuit up to rotation.** So every
   same-spectrum word is a cyclic shift of the truth. **[inference]**

Step 1 (`NoBranching`) is the named residue and is **not** proved in this
repository; steps 2–5 are not formalised. Closing them would give the
nonprimitive uniqueness theorem with no `EulerianCycleObstruction` hypothesis.

### Distinction from the `P1` route

The uniqueness does **not** come from the branch-free condition `P1` (out-degree
`≤ 1` counting multiplicities). `P1` fails for nonprimitive words: the
kernel-checked witness `0101` at `L = 3` is `I_s`-feasible and violates `P1`
(`alt4_not_P1`), yet its fibre is a singleton. The uniqueness comes from the
weaker edge-TYPE nonbranching of step 1, not from `P1`. **[fact]**

### Status

The nonprimitive case is **not** formalized in Lean. The existing
`fibre_singleton_of_Iss_and_obstruction` covers it via the external
`EulerianCycleObstruction L` hypothesis. The corrected simple-cycle argument
above would close it without that hypothesis, but formalizing it requires the
`NoBranching` proof and the Eulerian-cycle uniqueness for single-cycle graphs.
**[choice]**

## 5. The external BBT premise is refuted in this model

The external complete-spectrum premise `hBBT : equal length-L spectrum →
cyclic shift` is **false** for the same-length oriented model. The kernel-checked
witness: `G = 6`, `L = 2`, `truth6 = 011001`, `cand6 = 010011`. Both have the
length-2 spectrum `AA = BB = 1, AB = BA = 2`, and `cand6` is not a cyclic
shift of `truth6`. **[fact]**

The refutation witness is **not** `I_s`-feasible (`truth6_not_information_feasible`):
with `L = 2` no copy of length `≥ 1` can be bridged, and `truth6` carries
interleaved repeats of length `2`. So the refutation does not touch the
hypothesis surface of `informationFeasible_62_maximizer`: the refuting witness
is not a tied maximizer, and it does not show that a tied maximizer exists
under `I_s`. **[fact]**

The premise — not the bookkeeping — is the live residue. The uniqueness
conclusion cannot be obtained from the BBT route in this model. **[inference]**

## 6. The #88 dominance-vs-membership audit

The `AABB`/`ABAB` witness of #88 is correctly read as follows. **[fact]**

* The truth `AABB` with realized read set `{1, 3}` is **not** a member of the
  §6.2 candidate class: its windows `AA` and `BB` are never observed
  (`truth_not_spelled_on_observed`). So the witness refutes the **dominance**
  claim ("every §6.2 candidate is dominated by the truth"), not the
  **maximizer-with-membership** claim ("the truth is a §6.2 candidate *and*
  maximises"). The membership antecedent is false at this instance.
* The repaired positive theorem `informationFeasible_62_maximizer` proves the
  maximizer statement over genuine §6.2 candidates, with the `I_s` hypothesis
  doing the work (no residual `¬ HasLongTripleRepeat` premise).
* The floor instance `truth4` (§4 of the Lean module) is the first kernel-checked
  instance at which the truth is simultaneously fully `I_s`-feasible and a
  genuine §6.2 candidate: the full read set makes every window observed.

The outdated #88 claims — that the witness refutes the maximizer claim, or
that `I_s` does not imply `¬ HasLongTripleRepeat` — are superseded and recorded
as such in `docs/same-length-62-maximizer.md`. **[fact]**

## 7. Finite evidence

* `scripts/verify_samelength62_fibre_mechanism_211.py`: every circular word
  whose spectrum fibre has two rotation orbits satisfies one of the two
  disjuncts of `FibreFreedomForcesLongRepeat`, for every binary word of length
  ≤ 11 and every ternary word of length ≤ 8. 18478 non-unique-fibre words
  found, 0 without an `I_s` length-clause violation. **[fact]** (evidence,
  not a proof.)
* `scripts/verify_samelength62_tie_search_211.py`: 0 distinct tied-maximizer
  witnesses in the search space. **[fact]** (evidence, not a proof.)
* `scripts/verify_samelength62_nonprimitive_211.py`: exhaustive search over all
  binary words of length `≤ 10` and all ternary words of length `≤ 8`: every
  nonprimitive word satisfying `P2` has a spectrum fibre that is a singleton up
  to rotation, a nonbranching successor, and a single-cycle successor graph.
  325 `k ≥ 3` counterexamples to "`P2` forces `k = 2`". 0 branching failures,
  0 non-single-cycle failures, 0 non-singleton-fibre failures. **[fact]**
  (evidence, not a completeness proof.)
* `scripts/verify_samelength62_mechanism_refutation_211.py`: the §4 mechanism
  refuted at two concrete instances (`0011^3` and `(abcab)^2`), and 1188
  `(T, k, L)` combinations with `P2` and `k ≥ 3`. **[fact]** (evidence.)

## 8. The exact remaining open residue

**None.** The uniqueness theorem `SameLength62Uniqueness.unique_62_maximizer_up_to_rotation` is fully kernel-checked under `I_s` with no external hypothesis. The two previously open residues are closed:

1. **`FibreFreedomForcesLongRepeat`** — not needed. The nonprimitive route goes through `IsSimpleCycle` + #243, not through the combinatorial fibre obstruction. **[fact]** (bypassed)
2. **`EulerianCycleObstruction L`** — not needed. The #243 lemma `isCyclicShift_of_isSimpleCycle_specCount` consumes `IsSimpleCycle` directly. **[fact]** (bypassed)

The `NoBranching` predicate of `SameLength62Nonprimitive` is no longer a residue; it is subsumed by the #243 lemma. The counterexample module (`SameLength62Nonprimitive`) remains as a record of the refuted mechanism. **[fact]**

## 9. What this front does not claim

* It does not claim that the tie class is a singleton in general (only under `I_s`).
* It does not claim that `FibreFreedomForcesLongRepeat` or
  `EulerianCycleObstruction L` is true or false (they are bypassed, not settled).
* It does not re-prove the maximizer theorem.
* It does not settle the 2016 paper's reconstruction theorem, although that
  theorem would imply the residue.
* It does not formalize the `NoBranching` predicate (subsumed by #243).
