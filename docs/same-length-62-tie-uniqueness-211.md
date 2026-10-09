# #211: the §6.2 same-length maximizer versus uniqueness up to rotation

This note is the companion to `AssemblyP1/SameLength62TieUniqueness.lean`. It
records the reviewed finite theorem surface, the audit of the primitive and
nonprimitive subcases, the #88 dominance-vs-membership audit, and the exact
remaining open residue. Every claim is tagged **[fact]** (kernel-checked or
computationally verified), **[inference]** (mathematical argument, not Lean),
or **[choice]** (a modeling or scoping decision).

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
Ukkonen force a nonbranching de Bruijn edge-TYPE support, giving uniqueness
via a deterministic successor?

**Assessment: YES.** The argument is **[inference]** (not yet Lean), with
computational support **[fact]**.

### The argument

Let `S` be nonprimitive with least period `p`, so `S = T^k` for a primitive
word `T` of length `p` and `k ≥ 2`.

1. **`P2` forces `k = 2`.** If `k ≥ 3`, any substring of `T` (of any length)
   occurs at `k ≥ 3` distinct positions in `S` (one per copy), so it is a
   triple repeat. `P2` forbids triple repeats of length `≥ L-1`; since
   substrings of length `L-1` exist in `S` (as `L ≤ G = kp`), this is a
   contradiction. Hence `k = 2` and `G = 2p`. **[inference]**

2. **`P2` forces `T` to have no repeat of length `≥ L-1`.** A repeat in `T`
   of length `e` occurs at two positions in `T`, giving four occurrences in
   `S` (two per copy), hence a triple repeat. So `T` has no repeat of length
   `≥ L-1`, i.e., all `(L-1)`-mers of `T` are distinct. **[inference]**

3. **The de Bruijn graph of `S` is a simple cycle with edge multiplicities 2.**
   The `(L-1)`-mers of `S` are the `(L-1)`-mers of `T`, each occurring twice.
   Since they are all distinct and `T` is primitive, they form a simple cycle
   `v_0 → v_1 → … → v_{p-1} → v_0`. Each edge has multiplicity 2 (one from
   each copy of `T`). **[inference]**

4. **Each `(L-1)`-mer has exactly one distinct successor.** In a simple cycle,
   each vertex has exactly one outgoing edge type (to the next vertex), even
   though there are two parallel edges. So the successor is deterministic.
   **[inference]**

5. **The Eulerian cycle is unique (up to rotation).** A simple cycle with
   parallel edges has a unique Eulerian cycle: traverse the cycle twice. Any
   circular word with the same spectrum is an Eulerian cycle of the same graph,
   hence a cyclic shift of `S`. **[inference]**

### Computational support

Exhaustive search over all binary words of length `4 ≤ G ≤ 12` and all
`2 ≤ L ≤ G`: every nonprimitive word satisfying `P2` has a spectrum fibre that
is a singleton up to rotation. Zero counterexamples. Additionally, for every
such word: `G = 2p` holds, the primitive root `T` has no repeat of length
`≥ L-1`, and the de Bruijn graph has no branching (each `(L-1)`-mer has
exactly one distinct successor). **[fact]** (search script:
`scripts/verify_samelength62_fibre_mechanism_211.py` and the analysis above;
the search is evidence, not a completeness proof.)

### Distinction from the `P1` route

The uniqueness does **not** come from the branch-free condition `P1` (out-degree
`≤ 1` counting multiplicities). `P1` fails for nonprimitive words: the
kernel-checked witness `0101` at `L = 3` is `I_s`-feasible and violates `P1`
(`alt4_not_P1`), yet its fibre is a singleton. The uniqueness comes from the
weaker edge-TYPE nonbranching: each vertex has exactly one distinct successor,
which is sufficient for Eulerian-cycle uniqueness on a simple cycle. **[fact]**

### Status

The nonprimitive case is **not** formalized in Lean. The existing
`fibre_singleton_of_Iss_and_obstruction` covers it via the external
`EulerianCycleObstruction L` hypothesis. The simple-cycle argument above
would close it without that hypothesis, but formalizing it requires new
machinery (de Bruijn graph structure for periodic words, Eulerian-cycle
uniqueness for simple cycles). **[choice]**

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

## 8. The exact remaining open residue

The uniqueness reading of the §6.2 maximizer statement needs one proposition
that this repository does not have. Two forms, both open:

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

The nonprimitive simple-cycle argument of §4 would close the nonprimitive
subcase without either hypothesis, but it is not formalized. **[choice]**

## 9. What this front does not claim

* It does not claim that the tie class is a singleton in general.
* It does not claim that `FibreFreedomForcesLongRepeat` or
  `EulerianCycleObstruction L` is true or false.
* It does not re-prove the maximizer theorem.
* It does not settle the 2016 paper's reconstruction theorem, although that
  theorem would imply the residue.
* It does not formalize the nonprimitive simple-cycle argument.
