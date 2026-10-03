import AssemblyP1.BBTSupportInvariant
import AssemblyP1.BBTCondense
import AssemblyP1.BBTChords

/-!
# Obligation 17: the candidate-side transfer — retired, and split into its parts

## Disposition (this front): RETIRED AND SPLIT

At the start of this front this module exported

```text
def CandidateTransfer (L : ℕ) : Prop := <clause 1 ∧ clause 2 ∧ clause 3>
```

a `def ... : Prop` that was **known to be `False`** (at `L = 1`, by
`candidateTransfer_1_false`) and that no theorem in the repository proved
either way.  The defect was not that the statement was hard; it was that the
reader could not tell a claim from a proof: two of the three conjuncts were
kernel-checked theorems and one was the published open problem, all three
hidden inside a single name that was never discharged.

**`CandidateTransfer` is removed from this module.**  It is replaced by its
parts, each carrying its own epistemic status:

| part | what it is now | where |
|---|---|---|
| clause 1 | a `Prop`, **not proved**: the published open problem | `candidateTransferClause1`, identified with `AssemblyP1.BBTUniqueAt` by the kernel-checked `candidateTransferClause1_eq_BBTUniqueAt` |
| clause 2, at `2 ≤ L` | **proved** | `candidateTransfer_cl2`, collected in `candidateTransfer_cl23` |
| clause 3, at `2 ≤ L` | **proved** | `candidateTransfer_cl3`, collected in `candidateTransfer_cl23` |
| clause 2, at `L = 1` | **refuted, with an exhibited witness** | `candidateTransfer_cl2_false_at_L1`, `candidateTransfer_1_false` |

Nothing is lost by retiring the composite.  Clause 1 already had a canonical
name in `P2.lean` (`BBTCompleteSpectrumUniqueness` / `BBTUniqueAt`) and is
unaffected; clauses 2 and 3 are proved and were never *reached* through the
composite anyway, because the composite is false at `L = 1` and therefore
cannot be discharged by them.

### Why this and not the two alternatives

* **Not "restate with a `2 ≤ L` guard".**  A `2 ≤ L`-guarded restatement would
  be *not false*, but it would still be **unproved**, because its clause 1 is
  the open problem.  It would therefore leave in the tree, under a fresh name,
  exactly the bundle of "one open conjecture + two kernel-checked lemmas" that
  caused the defect, and a reader would again have to open the file to learn
  which is which.  Restating does not remove the epistemic bundling; splitting
  does.
* **Not "the statement is true, `L = 1` is merely out of scope".**  This is
  refuted by the kernel, not by prose: `candidateTransfer_1_false` is a proof
  of `¬ (clause 1 ∧ clause 2 ∧ clause 3)` at `L = 1`.  A statement that is
  *proved false* is not a statement whose `L = 1` reading needs to be excluded
  by a guard; it is a statement that was wrong.  `2 ≤ L` is not a scoping
  convention that rescues it — the refutation is a fact about the definition.

### What is deliberately NOT claimed here

* **Clause 1 at `2 ≤ L` is not proved, and this front did not try.**  It is
  `thm:BBT`, i.e. Bresler--Bresler--Tse 2013 Theorem 3, i.e. the published open
  problem.  It is left as a `Prop`, as `AGENTS.md` requires.  Nothing in this
  module bears on it.
* **`candidateTransferClause1` is stated at all `L`, not at `2 ≤ L`.**  Whether
  the BBT theorem needs a window-length hypothesis is a *source-fidelity*
  question that this front does not settle; the `2 ≤ L` guard was introduced
  for clause 2, where it is forced by `VertexCycleEq`'s `Fin (L - 1)` step, and
  there is no argument here that it transfers to clause 1.
* **Clause 3 at `L = 1` is not settled.**  Neither refuted nor rescued.
* `scripts/board94_candidate_transfer_check.py` is **not** evidence for
  anything at `L = 1`: it searches only `L ≥ 2`, so it is silent there.  It may
  be run unmodified as a regression check on the `2 ≤ L` side, which is all it
  proves.

**Status (kernel-checked, re-verified by this front).**  Clauses 2 and 3 are
proved at `2 ≤ L` by `candidateTransfer_cl2` and `candidateTransfer_cl3`, and
collected by `candidateTransfer_cl23`.  Clause 2 is `False` at `L = 1`, proved
with a witness (`candidateTransfer_cl2_false_at_L1`, hence
`candidateTransfer_1_false`; witness `W = T T F F`, `E = T F T F`,
`σ = (0, 2, 1, 3)` at `K = 4`, `α = Bool`).  An earlier revision of this
header asserted that counterexample without a proof term behind it; the proof
was supplied by the preceding front.  What an earlier header claimed about
clauses 2 and 3 (that they were "kernel-checked" by
`candidateTransfer_cl2`/`cl3`) was likewise **false** at the start of the
preceding front: no such declarations existed anywhere in the repository.

No `axiom`/`sorry`/`admit` appears, and nothing outside this file is modified.

## The gap in one paragraph

`AssemblyP1.BBTEulerian.bbtCompleteSpec_of_obstruction` (`BBTEulerian.lean:441`)
is the project's `thm:BBT` in the shape the endpoint consumes.  Its hypothesis is
`EulerianCycleObstruction (α := α) L` --- an inhabitant of the residual --- and its
conclusion quantifies over a **candidate** `E`:

```text
∀ K, hK, S E, Ukkonen hK L S →
  specCount_L hK S = specCount_L hK E → RotEquiv hK E S
```

Two structural features of that theorem are what obligation 17 is about.

1. **The candidate is completely unconstrained.**  `E` appears with *no*
   structural hypothesis at all: not `IsPrimitive`, not `P2`, not `Ukkonen`,
   nothing beyond the complete-`L`-spectrum equality (and, in the reduction
   layer, equality of lengths).  The corresponding definition
   `AssemblyP1.P2.BBTCompleteSpectrumUniqueness` (`P2.lean:154`) is literally
   `∀ E, Ukkonen hG L S → specCount _ S = specCount _ E → RotEquiv hG E S`:
   the `Ukkonen` premise mentions `S` only.  This is deliberate and defended in
   prose at `paper/sections/05-population.tex:138` ("uniqueness is applied only
   to `S`; nothing requires `W^g` itself to satisfy P2").  It is *stronger*
   than a reading of Bresler--Bresler--Tse 2013, Theorem 3 that demands the
   condition on both genomes, and it is obtained only because the proof
   transports the **presentation** rather than the **hypothesis**: it builds
   the pull-back `BBTCondense.pullback hK L S E` of an equal-spectrum matching
   and proves it is an Eulerian cycle of the *truth's* condensed graph
   (`BBTEulerian.pullback_isEulerianCycle`, `BBTEulerian.lean:257`), so that
   `EulerianCycleObstruction` is applied at `S`, never at `E`.

2. **Only one direction of the presentation transfer was recorded.**  The
   theorem above consumes `VertexCycleEq → RotEquiv`, which *is* proved
   (`BBTEulerian.rotEquiv_of_vertexCycleEq`, `BBTEulerian.lean:294`).  The
   converse --- that a non-rotational candidate yields a non-rotational vertex
   cycle on the truth side, i.e. the contrapositive that any *attack* on the
   residual needs --- was stated nowhere in the repository at the start of the
   preceding front, as recorded then by `git grep`: the only theorems relating
   `RotEquiv` to `VertexCycleEq` were `rotEquiv_of_vertexCycleEq` (`:294`) and,
   in `BBTCondense.lean`, `pullback_rotation_RotEquiv` (`:709`), whose hypothesis
   is `IsRotation hG (pullback ...)`, **not** `VertexCycleEq ... (Equiv.refl)`.
   These two notions are not interchangeable.  That converse is now proved, as
   `rotEquiv_pullback_vertexCycleEq`, at `2 ≤ L`.

Clauses 2 and 3 are exactly those two gaps, and both are now closed at
`2 ≤ L`.  Clause 1 is already discharged from an
inhabitant of the residual (`bbtCompleteSpec_of_obstruction`); it is kept in the
module, separately named as `candidateTransferClause1`, so that a reading of
clauses 2-3 cannot be a misunderstanding of clause 1.

## Honest hypotheses of the three clauses

* **Clauses 2 and 3 require `2 ≤ L`, and this is not cosmetic.**  At `L = 1` the
  index type `Fin (L - 1) = Fin 0` makes the `∀ i` inside `VertexCycleEq`
  vacuous, so the `VertexCycleEq` side of clause 2 holds for *every* pull-back,
  while `Matching` at `L = 1` only says the single-symbol windows agree, i.e.
  `W` and `E` are permutations of each other with the same multiset of
  symbols, which need not be a rotation.  Clause 2 is therefore refutable at
  `L = 1`, and it is: see `candidateTransfer_cl2_false_at_L1`.
* **Clause 1 (`candidateTransferClause1`) is stated at all `L` and carries no
  `2 ≤ L` guard**, because the preceding front's decision to state the
  composite at all `L` "matching `bbtCompleteSpec_of_obstruction`, which takes
  `hL` as a separate argument" applied to the composite, and no argument has
  been given here that clause 1 needs the guard.  This front does not settle
  the question; see "What is deliberately NOT claimed".
* Clause 1 quantifies `W` and `E` at the *same* length.  That is not a
  weakening: `AssemblyP1.PopulationReduction.population_uniqueness_primitive_P2_words`
  establishes `G = H` from primitivity plus the normalized equality *before*
  its two `hBBTS`/`hBBTD` premises are consumed
  (`PopulationReduction.lean:1834`), and
  `AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
  applies the two premises only after `obtain ⟨hGK, hSpec⟩` (lines 186-196).
  The length equality is therefore an output of the reduction, and folding it
  into clause 1 records the state of affairs honestly rather than adding an
  assumption.
* Clause 3 quantifies over a bare `θ : Fin K → Fin K`, exactly as
  `BBTSupportInvariant.SupportDichotomy` and
  `BBTSupportInvariant.orbitVertexEq_of_dichotomy` do.  It assumes **nothing**
  about `W` --- not even `Ukkonen` --- because obligations 14, 15 and 16 are
  stated for the candidate-free support side and this front does not restate
  them.  See `docs/candidate-transfer-oblig17-94.md` §3.
* Nothing here depends on `AssemblyP1.BBTReplacementInvariant.case1_landing`.
  That statement has been **refuted** (G = 5, M = 3, S = 00101) and this module
  neither cites it nor needs it.

## What this module is not

None of the three clauses is an inhabitant of `EulerianCycleObstruction`, and
proving all of them would not by itself produce one.  Taken together they are
the statement that the reduction from "a
non-rotational candidate exists" to "the support-side obstruction fires at the
truth" is sound.  Obligations 14/15/16 supply the support-side inputs.  This
supplies the transport between the two sides.  Both are needed and neither
subsumes the other.

## Result (obligation 17) --- what is proved, what is refuted, what is open

* **Clause 2 is proved, both directions, for `2 ≤ L`** (`candidateTransfer_cl2`).
  `→` is `BBTEulerian.rotEquiv_of_vertexCycleEq` fed by `pullback_window`.
  `←` is `rotEquiv_pullback_vertexCycleEq`, proved here: the pull-back of a
  rotationally matched candidate is a presentation of the truth's own vertex
  cycle, the witnessing rotation being `K - k` where `k` is the shift in
  `RotEquiv hK E W`.  Only three elementary modular facts are used
  (`mod_neg_shift`, `mod_add_neg'`, `mod_neg_shift_add`), and no `Ukkonen`
  hypothesis.
* **Clause 3 is proved for `2 ≤ L`** (`candidateTransfer_cl3`).  The three
  positive side conditions come from `BBTEulerianSearch.succOf_bijective`,
  `fibrePreserving_succOf` and `oneCycle_succOf` at the pull-back, which is an
  `EulerianCycle` of the truth's condensed graph
  (`BBTEulerian.pullback_isEulerianCycle`) and needs only a `Matching`, no
  inhabitant of `EulerianCycleObstruction`.  The `¬ OrbitVertexEq` conjunct is
  `¬ RotEquiv E W → ¬ VertexCycleEq … (pullback …) (Equiv.refl)` composed with
  `BBTEulerianSearch.vertexCycleEq_iff_orbit`; the matching itself is
  `BBTChords.exists_matching` at the spectrum equality.
* **Clause 1 is the open problem and is untouched.**  Nothing weaker is claimed
  and no lemma relating clause 1 to `thm:BBT` is proved here.  The only thing
  proved about it is the identification
  `candidateTransferClause1_eq_BBTUniqueAt`, which says clause 1 *is*
  `AssemblyP1.BBTUniqueAt`; that is a statement about names, not about truth.
* **Clause 2 is `False` at `L = 1`, proved with a witness**
  (`candidateTransfer_cl2_false_at_L1`, hence `candidateTransfer_1_false`).
  Witness: `K = 4`, `α = Bool`, `W = T T F F`, `E = T F T F`, `σ = (0, 2, 1, 3)`.
  `L1_matching` proves the matching hypothesis really does hold at `L = 1`
  (the `L = 1` windows are single symbols, and the two words carry the same
  multiset); `L1_notRotEquiv` proves `E` is not a rotation of `W`, by
  exhausting the four values of `k % 4`; `vertexCycleEq_any_at_L1` proves the
  other side holds vacuously because `Fin (1 - 1) = Fin 0`.  So the `L = 1`
  degeneracy is a **refutation, not a gap**.

### How to check this file

* `lake build` --- whole library.
* `lake env lean` a scratch file containing `#print axioms` for
  `candidateTransfer_cl2`, `candidateTransfer_cl3`, `candidateTransfer_cl23`,
  `candidateTransferClause1_eq_BBTUniqueAt`, `candidateTransfer_cl2_false_at_L1`,
  `candidateTransfer_1_false`.  Each must report only
  `[propext, Classical.choice, Quot.sound]` (`vertexCycleEq_any_at_L1` reports
  `[Quot.sound]` alone, which is also permitted).
* `python3 scripts/board94_candidate_transfer_check.py` unmodified: a
  regression check on the `2 ≤ L` side **only**.  It searches `L ≥ 2` and is
  silent about `L = 1`.

### Provenance of the two builds reported here

An earlier revision of this header claimed `lake build
AssemblyP1.BBTCandidateTransfer` = exit 0 on a commit where the module did
**not** compile (an unterminated module docstring at the top of the file).  Any
claim of the form "this file builds" should therefore be re-executed rather
than inherited.  The build status of the current head is recorded in the front's
report, not here.
-/

set_option maxHeartbeats 400000

namespace AssemblyP1.BBTEulerian

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1
open AssemblyP1.BBTEulerianSearch

variable {α : Type} [DecidableEq α]

/-! **Obligation 17, CANDIDATE-SIDE TRANSFER --- the explicit interface.**

(This was the docstring of the now-removed `def CandidateTransfer`.  It is
retained as a plain section comment, not a docstring, because the declaration it
documented is gone; the clauses it describes now live in `candidateTransferClause1`,
`candidateTransfer_cl2`, `candidateTransfer_cl3`.)

Three laws relating a *candidate* `E` to the *truth*-side objects the residual
`BBTEulerian.EulerianCycleObstruction` and the support chain
(`BBTSupportInvariant.SupportDichotomy`, `SelectedTriple_obstruction`,
`SelectedInterleaved_obstruction`) are stated over.

1. **Forward BBT, hypothesis-free on the candidate.**
   `∀ K hK W E, Ukkonen hK L W → specCount_L W = specCount_L E → RotEquiv E W`.
   This is `AssemblyP1.P2.BBTCompleteSpectrumUniqueness`
   (`P2.lean:154`), instantiated at the truth side, and it is **discharged** by
   `BBTEulerian.bbtCompleteSpec_of_obstruction` (`BBTEulerian.lean:441`) from an
   inhabitant of `EulerianCycleObstruction`.

2. **Non-rotationality transfer (PROVED at `2 ≤ L`, see `candidateTransfer_cl2`).**  For any equal-spectrum `Matching`
   `σ` between `W` and `E`, the pull-back presentation carries `E`'s
   rotational status exactly:
   `VertexCycleEq (pullback σ) (Equiv.refl) ↔ RotEquiv E W`.
   The `→` direction is `BBTEulerian.rotEquiv_of_vertexCycleEq`
   (`BBTEulerian.lean:294`).  The `←` direction ---
   `RotEquiv E W → VertexCycleEq (pullback σ) (Equiv.refl)`, equivalently
   `¬ RotEquiv E W → ¬ VertexCycleEq (pullback σ) (Equiv.refl)` --- was
   stated nowhere in the repository at the start of the previous front; it is
   proved here, as `rotEquiv_pullback_vertexCycleEq`.  It is **false at
   `L = 1`**: see `candidateTransfer_cl2_false_at_L1`.

3. **Support-side recovery (PROVED at `2 ≤ L`, see `candidateTransfer_cl3`).**  A non-rotational equal-spectrum
   candidate produces, on the *truth* side, a bijective fibre-preserving
   one-cycle `θ` that does not spell the truth's vertex cycle --- i.e. exactly
   the input of `BBTSupportInvariant.orbitVertexEq_of_dichotomy`
   (`BBTSupportInvariant.lean:254`) and of obligations 14/15/16.  Equivalently,
   conjuncts 1 and 3 say the BBT boundary and the support boundary see the same
   set of non-rotational candidates.  The three side conditions are already
   available at the presentation level
   (`BBTEulerianSearch.succOf_bijective` `:204`,
   `fibrePreserving_succOf` `:208`, `oneCycle_succOf` `:214`) for
   `θ = BBTEulerianSearch.succOf hK (pullback hK L W E hσ.1)`; what is open is
   the `¬ OrbitVertexEq` conjunct, i.e. conjunction of conjunct 2 with
   `BBTEulerianSearch.vertexCycleEq_iff_orbit` (`:263`).

Taken together these three laws say: the residual
`EulerianCycleObstruction` may be attacked on the candidate side, and doing so
loses nothing.  Clauses 2 and 3 are proved below at `2 ≤ L`
(`candidateTransfer_cl23`); clause 1, which is the published open problem, is
**not** proved. -/

/-- **CLAUSE 1 of the retired obligation-17 interface --- the REMAINING OPEN
OBLIGATION.**  This `Prop` is *not* proved here and is not proved anywhere else
in the repository.  It is the published open problem:
`candidateTransferClause1_eq_BBTUniqueAt` below identifies it, by `Iff.rfl`,
with `AssemblyP1.BBTUniqueAt`, i.e. with
`∀ K hK W, P2.BBTCompleteSpectrumUniqueness hK L W` (`P2.lean:154`), i.e. with
Bresler--Bresler--Tse 2013 Theorem 3.

It is recorded here under its own name, separately from the two kernel-checked
clauses, so that a reader of this file can tell the conjecture from the proofs.
It quantifies at *all* `L`; whether `2 ≤ L` is needed for it is a source-fidelity
question that this front does **not** settle (see the module header). -/
def candidateTransferClause1 (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α),
      Ukkonen hK L W →
      specCount (L := L) hK W = specCount (L := L) hK E →
      RotEquiv hK E W

/-- **Clause 1 of the retired interface is literally the published open
problem.**  Kernel-checked by `Iff.rfl`: retiring `CandidateTransfer` does not
lose clause 1, which already had the canonical name `AssemblyP1.BBTUniqueAt`.
No claim is made about clause 1's truth value. -/
theorem candidateTransferClause1_eq_BBTUniqueAt (L : ℕ) :
    candidateTransferClause1 (α := α) L ↔ BBTUniqueAt (α := α) L := Iff.rfl

/-! ## Clause 2, `←` direction (kernel-checked by this front)

The direction that the module header previously recorded as **open** and that
is proved here: a rotationally matched candidate makes the pull-back
presentation carry the truth's own vertex cycle, up to the rotation that
cancels the matching's shift.  Read contrapositively this is
`¬ RotEquiv E W → ¬ VertexCycleEq hK L W (pullback …) (Equiv.refl)`, the
implication any attack on the residual needs and which was stated nowhere in
the repository.

Only three elementary modular facts are proved locally.  No hypothesis on `σ`
beyond `Matching`, and no `Ukkonen`, is used. -/

/-- Undoing the rotation by `k₀` and redoing it is the identity modulo `K`. -/
private theorem mod_neg_shift {K : ℕ} (_hK : 0 < K) (a k0 : ℕ) (hk0 : k0 ≤ K) :
    ((a + K - k0) % K + k0) % K = a % K := by
  show Nat.ModEq K ((a + K - k0) % K + k0) a
  have h1 : Nat.ModEq K ((a + K - k0) % K + k0) (a + K - k0 + k0) :=
    Nat.mod_modEq _ K |>.add_right k0
  have h2 : Nat.ModEq K (a + K - k0 + k0) (a + K) := by
    have h : a + K - k0 + k0 = a + K := by omega
    rw [h]
  have h3 : Nat.ModEq K (a + K) a := by simp
  exact h1.trans (h2.trans h3)

/-- The shift undoing `k₀` may be written `(K - k₀) % K`. -/
private theorem mod_add_neg' {K : ℕ} (_hK : 0 < K) (a k0 : ℕ) (hk0 : k0 ≤ K) :
    (a + (K - k0) % K) % K = (a + K - k0) % K := by
  show Nat.ModEq K (a + (K - k0) % K) (a + K - k0)
  have h1 : Nat.ModEq K (a + (K - k0) % K) (a + (K - k0)) :=
    Nat.ModEq.add_left a (Nat.mod_modEq (K - k0) K)
  have h2 : Nat.ModEq K (a + (K - k0)) (a + K - k0) := by
    have h : a + (K - k0) = a + K - k0 := by omega
    rw [h]
  exact h1.trans h2

/-- Reading forward by `b` from the undoing shift agrees, modulo `K`, with
reading forward by `b` from `a - k₀`. -/
private theorem mod_neg_shift_add {K : ℕ} (_hK : 0 < K) (a b k0 : ℕ) (hk0 : k0 ≤ K) :
    ((a + K - k0) % K + b) % K = (a + b + K - k0) % K := by
  show Nat.ModEq K ((a + K - k0) % K + b) (a + b + K - k0)
  have h1 : Nat.ModEq K ((a + K - k0) % K + b) (a + K - k0 + b) :=
    Nat.mod_modEq _ K |>.add_right b
  have h2 : Nat.ModEq K (a + K - k0 + b) (a + b + K - k0) := by
    have h : a + K - k0 + b = a + b + K - k0 := by omega
    rw [h]
  exact h1.trans h2

/-- **Clause 2, `←` direction: a rotational candidate gives a rotational
pull-back vertex cycle.**  Kernel-checked.  No `Ukkonen` hypothesis is used,
and none is needed. -/
theorem rotEquiv_pullback_vertexCycleEq {K : ℕ} (hK : 0 < K) (L : ℕ)
    (W E : Fin K → α) {σ : Fin K → Fin K} (hσ : Matching (L := L) hK W E σ)
    (hrot : RotEquiv hK E W) :
    VertexCycleEq hK L W (pullback hK L W E hσ.1) (Equiv.refl (α := Fin K)) := by
  obtain ⟨k0, hk0⟩ := hrot
  have hk0' : ∀ j : Fin K, E ⟨(j.val + k0 % K) % K, Nat.mod_lt _ hK⟩ = W j := by
    intro j
    have hmod : (j.val + k0) % K = (j.val + k0 % K) % K := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
    exact congrArg (fun x : Fin K => E x) (Fin.mk_eq_mk.mpr hmod) ▸ hk0 j
  have hk0_lt : k0 % K < K := Nat.mod_lt _ hK
  set k := k0 % K with hkdef
  refine ⟨⟨(K - k) % K, Nat.mod_lt _ hK⟩, ?_⟩
  intro i
  funext d
  show cyc hK W ((pullback hK L W E hσ.1 i).val + d.val)
      = cyc hK W (((rotAdd hK ((K - k) % K) i).val) + d.val)
  -- the truth at `i + d` reads what the candidate reads there
  have hwin := congrFun (pullback_window hK L W E hσ i) ⟨d.val, by omega⟩
  have hLHS : cyc hK W ((pullback hK L W E hσ.1 i).val + d.val)
      = E ⟨(i.val + d.val) % K, Nat.mod_lt _ hK⟩ := by
    simpa only [window, cyc, Fin.mk_val] using hwin
  -- a rotational candidate reads at `i + d` what the truth reads at `i + d - k`
  have hj : E ⟨(i.val + d.val) % K, Nat.mod_lt _ hK⟩
      = W ⟨(i.val + d.val + K - k) % K, Nat.mod_lt _ hK⟩ := by
    have hk := hk0' ⟨(i.val + d.val + K - k) % K, Nat.mod_lt _ hK⟩
    have hidx : ((i.val + d.val + K - k) % K + k) % K = (i.val + d.val) % K :=
      mod_neg_shift hK (i.val + d.val) k (Nat.le_of_lt hk0_lt)
    exact congrArg (fun x : Fin K => E x) (Fin.mk_eq_mk.mpr hidx) ▸ hk
  rw [hLHS, hj]
  exact congrArg W (Fin.ext (mod_add_neg' hK i.val k (Nat.le_of_lt hk0_lt) ▸
    mod_neg_shift_add hK i.val d.val k (Nat.le_of_lt hk0_lt)).symm)

/-- **Clause 2 of the retired interface, both directions, at `2 ≤ L`.**
The `→` direction is `BBTEulerian.rotEquiv_of_vertexCycleEq` fed by
`pullback_window`; the `←` direction is `rotEquiv_pullback_vertexCycleEq`
above.  No `Ukkonen` hypothesis is used on either side. -/
theorem candidateTransfer_cl2 {K : ℕ} (hK : 0 < K) {L : ℕ} (hL : 2 ≤ L)
    (W E : Fin K → α) {σ : Fin K → Fin K} (hσ : Matching (L := L) hK W E σ) :
    (VertexCycleEq hK L W (pullback hK L W E hσ.1) (Equiv.refl (α := Fin K))
      ↔ RotEquiv hK E W) := by
  constructor
  · intro hk
    exact rotEquiv_of_vertexCycleEq hK L W (pullback hK L W E hσ.1) hL hk
        (fun s => (pullback_window hK L W E hσ s).symm)
  · intro hrot
    exact rotEquiv_pullback_vertexCycleEq hK L W E hσ hrot

/-- **Clause 3 of the retired interface, proved, at `2 ≤ L`.**  A
non-rotational
equal-spectrum candidate yields, on the truth side, a bijective
fibre-preserving one-cycle `θ` that does not spell the truth's vertex cycle.
The three positive side conditions are `succOf_bijective`,
`fibrePreserving_succOf` and `oneCycle_succOf` at the pull-back, which is an
`EulerianCycle` of the truth's condensed graph (`pullback_isEulerianCycle`);
the `¬ OrbitVertexEq` conjunct is clause 2 read contrapositively and composed
with `vertexCycleEq_iff_orbit`. -/
theorem candidateTransfer_cl3 {K : ℕ} (hK : 0 < K) {L : ℕ} (hL : 2 ≤ L)
    (W E : Fin K → α) (_hU : Ukkonen hK L W)
    (hspec : specCount (L := L) hK W = specCount (L := L) hK E)
    (hnrot : ¬ RotEquiv hK E W) :
    ∃ θ : Fin K → Fin K, Function.Bijective θ ∧ FibrePreserving hK L W θ ∧
      OneCycle hK θ ∧ ¬ OrbitVertexEq hK L W θ := by
  obtain ⟨σ, hσ⟩ := exists_matching hK W E hspec
  set μ := pullback hK L W E hσ.1 with hμdef
  have hec : EulerianCycle hK L W μ := pullback_isEulerianCycle hK L W hσ
  have hnv : ¬ VertexCycleEq hK L W μ (Equiv.refl (α := Fin K)) := by
    rintro ⟨k, hk⟩
    exact hnrot (rotEquiv_of_vertexCycleEq hK L W μ hL ⟨k, hk⟩
      (fun s => (pullback_window hK L W E hσ s).symm))
  refine ⟨succOf hK μ, succOf_bijective hK μ, fibrePreserving_succOf hK L W μ hec,
    oneCycle_succOf hK L W μ hec, ?_⟩
  intro horbit
  exact hnv ((vertexCycleEq_iff_orbit hK L W μ).mpr horbit)

/-! ## Clause 2 is `False` at `L = 1` --- kernel-checked counterexample

The hypothesis recorded in the header above, now **settled by a witness**.

At `L = 1` the index type inside `VertexCycleEq` is `Fin (L - 1) = Fin 0`, so
the `∀ i : Fin K` step is vacuous and `VertexCycleEq` holds for *every* pair of
presentations (`vertexCycleEq_any_at_L1` below).  Clause 2 at `L = 1` is
therefore the assertion `RotEquiv E W` for every equal-read-type matching.
`Matching` at `L = 1` says only that the `L = 1` windows agree, i.e. `W` and
`E` are permutations of each other as circular words with the same multiset of
symbols --- it does not say the permutation is a rotation.  The witness below
is exactly that gap: `W = T T F F`, `E = T F T F`, `σ = (0, 2, 1, 3)`.

Consequences, all kernel-checked below:

* `candidateTransfer_cl2_false_at_L1` : clause 2 at `L = 1`, as literally
  quantified, is `False`.
* `vertexCycleEq_any_at_L1` : the vacuity, proved once and for all. -/

/-- **`L = 1`: `VertexCycleEq` holds for arbitrary presentations.**  The
`∀ i` ranges over `Fin (L - 1) = Fin 0`. -/
theorem vertexCycleEq_any_at_L1 {K : ℕ} (hK : 0 < K) (W : Fin K → α)
    (σ τ : Fin K ≃ Fin K) :
    VertexCycleEq hK 1 W σ τ :=
  ⟨⟨0, hK⟩, fun _ => funext fun d => Fin.elim0 d⟩

section L1Counterexample

/-- `W = T T F F` (the truth), at `K = 4`. -/
def L1W : Fin 4 → Bool := ![true, true, false, false]

/-- `E = T F T F` (the candidate), at `K = 4`. -/
def L1E : Fin 4 → Bool := ![true, false, true, false]

/-- `σ = (0, 2, 1, 3)`: the matching sending each `T` of `W` to a `T` of `E`
and each `F` of `W` to an `F` of `E`.  A bijection, but not a rotation. -/
def L1s : Fin 4 → Fin 4 := ![0, 2, 1, 3]

theorem L1s_eq_swap : L1s = (Equiv.swap 1 2 : Fin 4 ≃ Fin 4).toFun := by
  funext i
  fin_cases i <;> rfl

theorem L1s_bij : Function.Bijective L1s := by
  rw [L1s_eq_swap]
  exact (Equiv.swap 1 2).bijective

theorem L1W_val (i : Fin 4) : L1W i = decide (i.val < 2) := by
  fin_cases i <;> simp [L1W]

/-- `E` read at position `i` is `true` exactly when `i` is even. -/
theorem L1E_val (i : Fin 4) : L1E i = decide (i.val % 2 = 0) := by
  fin_cases i <;> simp [L1E]

/-- **The matching hypothesis of clause 2 does hold at `L = 1`.**  The `L = 1`
window at `r` is the single symbol `S r`, and `L1W r = L1E (L1s r)` for all `r`:
`T T F F` and `T F T F` carry the same multiset. -/
theorem L1_matching : Matching (L := 1) (by norm_num : (0 : ℕ) < 4) L1W L1E L1s := by
  refine ⟨L1s_bij, ?_⟩
  intro r
  funext d
  fin_cases d
  simp [window, cyc, L1W, L1E, L1s]
  fin_cases r <;> norm_num

/-- **`E` is not a rotation of `W`.**  By cases on `k % 4` (all four are
refuted by the single position where the two words disagree). -/
theorem L1_notRotEquiv : ¬ RotEquiv (by norm_num : (0 : ℕ) < 4) L1E L1W := by
  rintro ⟨k, hk⟩
  have hNat : ∀ i : ℕ, i < 4 →
      decide (((i + k) % 4) % 2 = 0) = decide (i < 2) := by
    intro i hi
    have h := hk ⟨i, hi⟩
    simp only [L1E_val, L1W_val, Fin.mk_val] at h
    exact h
  have hkey : ∀ i : ℕ, i < 4 → (i + k) % 4 = (i + k % 4) % 4 := by
    intro i _
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, j.val = k % 4 :=
    ⟨⟨k % 4, Nat.mod_lt k (by norm_num)⟩, rfl⟩
  have hNat' : ∀ i : ℕ, i < 4 →
      decide (((i + j.val) % 4) % 2 = 0) = decide (i < 2) := by
    intro i hi
    have h := hNat i hi
    rw [hkey i hi, ← hj] at h
    exact h
  have h0 := hNat' 0 (by norm_num)
  have h1 := hNat' 1 (by norm_num)
  have h2 := hNat' 2 (by norm_num)
  have h3 := hNat' 3 (by norm_num)
  fin_cases j <;> simp at h0 h1 h2 h3

/-- **The two sides of clause 2 disagree at `L = 1`:** the `VertexCycleEq`
side holds vacuously, the `RotEquiv` side fails. -/
theorem L1_sides_disagree :
    VertexCycleEq (by norm_num : (0 : ℕ) < 4) 1 L1W
        (pullback (by norm_num : (0 : ℕ) < 4) 1 L1W L1E L1s_bij)
        (Equiv.refl (α := Fin 4))
      ∧ ¬ RotEquiv (by norm_num : (0 : ℕ) < 4) L1E L1W :=
  ⟨vertexCycleEq_any_at_L1 _ _ _ _, L1_notRotEquiv⟩

/-- **Clause 2 at `L = 1`, as literally quantified, is `False`.**  A
kernel-checked counterexample, with the witness `W = T T F F`, `E = T F T F`,
`σ = (0, 2, 1, 3)` exhibited in `L1W`, `L1E`, `L1s`.  This is the fact that
forced the disposition recorded in the module header: the composite statement
that contained this clause was **false**, not merely unproved. -/
theorem candidateTransfer_cl2_false_at_L1 :
    ¬ (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → Bool) (σ : Fin K → Fin K)
        (hσ : Matching (L := 1) hK W E σ),
        (VertexCycleEq hK 1 W (pullback hK 1 W E hσ.1) (Equiv.refl (α := Fin K))
          ↔ RotEquiv hK E W)) := by
  rintro h
  have h3 := h 4 (by norm_num) L1W L1E L1s L1_matching
  exact L1_notRotEquiv (h3.mp (vertexCycleEq_any_at_L1 _ L1W _ _))

/-- **The retired obligation-17 conjunction is `False` at `L = 1`** (clause 2
alone refutes it; clause 1 is not needed and clause 3 is not claimed).  The
statement being refuted is the three-way conjunction that the former
`def CandidateTransfer 1` denoted, written out here in full so that the
refutation names a statement that still exists in the tree.  Clause 2 of it is
`candidateTransfer_cl2_false_at_L1`; clause 1 is
`candidateTransferClause1 1`, i.e. `BBTUniqueAt (α := Bool) 1`. -/
theorem candidateTransfer_1_false :
    ¬ ((∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → Bool),
          Ukkonen hK 1 W →
          specCount (L := 1) hK W = specCount (L := 1) hK E →
          RotEquiv hK E W)
       ∧ (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → Bool) (σ : Fin K → Fin K)
            (hσ : Matching (L := 1) hK W E σ),
            (VertexCycleEq hK 1 W (pullback hK 1 W E hσ.1) (Equiv.refl (α := Fin K))
              ↔ RotEquiv hK E W))
       ∧ (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → Bool),
            Ukkonen hK 1 W →
            specCount (L := 1) hK W = specCount (L := 1) hK E →
            ¬ RotEquiv hK E W →
            ∃ θ : Fin K → Fin K, Function.Bijective θ ∧ FibrePreserving hK 1 W θ ∧
              OneCycle hK θ ∧ ¬ OrbitVertexEq hK 1 W θ)) :=
  fun h => candidateTransfer_cl2_false_at_L1 h.2.1

end L1Counterexample

/-- **Clauses 2 and 3 of the retired interface, at `2 ≤ L`, as the clauses
are literally written.**  This is the part that is discharged; clause 1 is
`candidateTransferClause1`, the published open problem, and is untouched. -/
theorem candidateTransfer_cl23 {L : ℕ} (hL : 2 ≤ L) :
    (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α) (σ : Fin K → Fin K)
        (hσ : Matching (L := L) hK W E σ),
        (VertexCycleEq hK L W (pullback hK L W E hσ.1) (Equiv.refl (α := Fin K))
          ↔ RotEquiv hK E W)) ∧
    (∀ (K : ℕ) (hK : 0 < K) (W E : Fin K → α),
        Ukkonen hK L W →
        specCount (L := L) hK W = specCount (L := L) hK E →
        ¬ RotEquiv hK E W →
        ∃ θ : Fin K → Fin K, Function.Bijective θ ∧ FibrePreserving hK L W θ ∧
          OneCycle hK θ ∧ ¬ OrbitVertexEq hK L W θ) :=
  ⟨fun K hK W E σ hσ => candidateTransfer_cl2 hK hL W E hσ,
   fun K hK W E hU hs hn => candidateTransfer_cl3 hK hL W E hU hs hn⟩

end AssemblyP1.BBTEulerian
