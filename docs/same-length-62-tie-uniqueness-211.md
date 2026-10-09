# #211: the §6.2 same-length maximizer versus uniqueness up to rotation

This note is the companion to `AssemblyP1/SameLength62TieUniqueness.lean`. It
records the reviewed finite theorem surface, the audit of the primitive and
nonprimitive subcases, the #88 dominance-vs-membership audit, and the exact
remaining open residue. Every claim is tagged **[fact]** (kernel-checked or
computationally verified), **[inference]** (mathematical argument, not Lean),
or **[choice]** (a modeling or scoping decision).


## Current status (9 October 2026): historical audit, not an open theorem list

The statements called *open* in §§4 and 8 below preserve the historical
exploration. The later Lean theorem
\`SameLength62Uniqueness.unique_62_maximizer_up_to_rotation\` proves rotation
uniqueness when \`I_s\` holds **and the true genome and the competitor are both
genuine, same-length §6.2 candidates for the same observed vertex list**.
Its primitive branch uses #94; the nonprimitive branch uses periodic
factor distinctness, simple-cycle support, and the merged #243 rotation lemma.
No external BBT obstruction axiom is used.

Importantly, \`hStruth\` (the true genome's §6.2 certificate) is a genuine
additional assumption, *not* a consequence of \`I_s\`: the Lean-checked
\`AcgtWitness211.acgt4_not_candidate\` exhibits sparse observations on the
circular word \`ACGT\` where \`I_s\` holds but truth candidacy fails.
Do not infer unrestricted maximum-likelihood uniqueness from the conditional
candidate-rotation theorem.

A stronger nonprimitive result without \`hStruth\` is developed in
\`SameLength62NonprimitiveRotation\` (board #245, PR #126 as of this audit).
The corresponding primitive case is board #246. Whether candidates exist and
whether the §6.2 approximate objective represents exact multinomial ML are
distinct model questions.


## 1. The question

The oriented same-length §6.2 model asks: when the maximum-likelihood sequence
is tied, is it the truth? The maximizer half is already proved
(`SameLength62Maximizer.informationFeasible_62_maximizer`,
`MLEscape.informationFeasible_62_spelledML`); this front audits the uniqueness
half.

## 2. Reviewed theorem surface

All theorems below are in `AssemblyP1.SameLength62TieUniqueness` and
kernel-checked with axioms `propext`, `Classical.choice`, `Quot.sound` only.
No `sorry`, no `admit`, no unproved axioms. **[fact]**

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

## 4. The nonprimitive subcase: assessment

**Question.** For a nonprimitive `I_s`-feasible truth, does periodicity plus
`P2` force a nonbranching de Bruijn edge-TYPE support, giving uniqueness via a
deterministic successor?

**Assessment: the conclusion is supported by computation, but the note's
original mechanism is false.** The corrected residue is the `NoBranching`
predicate of `AssemblyP1.SameLength62Nonprimitive`. **[fact]**
(counterexample kernel-checked), **[inference]** (the corrected route),
**[choice]** (the residue).

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

## 8. Historical open residue (superseded for conditional uniqueness)

At the time of the initial audit, the following were two proposed, unproved
routes to the general spectrum-fibre theorem. They remain independently
interesting, but the later *conditional candidate-rotation theorem* no
longer requires either one:

1. **`FibreFreedomForcesLongRepeat`** (combinatorial, source-independent): if
   the fibre of a circular word's complete length-`L` spectrum contains a word
   that is not a cyclic shift of it, then the word carries a triple repeat of
   length `≥ L-1`, or two maximal repeats of length `≥ L-1` whose selected
   starts interleave. Both disjuncts are forbidden by `I_s`. Not proved. **[fact]**
   (status), **[inference]** (that it would close the residue).

2. **`EulerianCycleObstruction L`** (BBT 2013 Theorem 3): for any
   Ukkonen-satisfying circular word, every Eulerian cycle of its condensed
   `(L-1)`-mer graph is a rotation of the identity, or there is a long
   obstruction. Not proved in this repository; consumed as the explicit
   hypothesis it is in `fibre_singleton_of_Iss_and_obstruction`. **[fact]**
   (status).

**Subsequent proof.** The conditional nonprimitive result is now proved
in \`SameLength62Uniqueness\` by the minimal-period
\`IsSimpleCycle\` route, without a separate \`NoBranching\` conjecture.
This does not establish the unrestricted ML implication or the global
\`FibreFreedomForcesLongRepeat\` statement.

## 9. What this front does not claim

* It does not claim that the tie class is a singleton in general.
* It does not claim that `FibreFreedomForcesLongRepeat` or
  `EulerianCycleObstruction L` is true or false.
* It does not re-prove the maximizer theorem.
* It does not settle the 2016 paper's reconstruction theorem, although that
  theorem would imply the residue.
* The historical audit did not formalize the nonprimitive simple-cycle
  argument; \`SameLength62Uniqueness\` now does so for the conditional model.
* It does not remove the extra \`hStruth\` premise or equate candidate
  rotation with every maximizer of an unrestricted likelihood model.
