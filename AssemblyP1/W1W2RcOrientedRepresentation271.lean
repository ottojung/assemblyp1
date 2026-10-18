import AssemblyP1.SameLengthSection62Counterexample
import AssemblyP1.SourceFaithfulIs
import AssemblyP1.W1W2SeparationCompatibility
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# W1/W2 reverse-complement molecules versus oriented read strings (#271, goal 3)

**Status: kernel-checked representation result. It determines a *negative* answer
to goal 3's shared-model question for the historical W1/W2 reverse-complement
(molecule) witnesses; it manufactures no contradiction.**

Issue #271 goal 3 asks whether the existing historical W1/W2
**reverse-complement-collapsed** cases instantiate the conditional-Bayes `E`
guarantee (A) versus ordinary R-only maximum-likelihood recovery (B) under ONE
*exactly shared observable data model*: same candidate universe, same prior,
same read representation, same likelihood objective.

## Determination

They do **not**, for two independent reasons, only the first of which is
kernel-checked here.

1. **Representation mismatch (this module).** The W1/W2 observable is the
   reverse-complement **molecule-class count vector** `obs : Fin 8 → Nat`
   (`SameLengthSection62Counterexample.obs`, built by collapsing oriented
   length-`3` windows through the molecule class `cls`). The collapse `cls` is
   **not injective** (`cls_not_injective`): a read and its reverse complement
   share a class (`cls_rc`), and distinct oriented reads do too
   (`ATA`/`TAT`). Hence the molecule-class count is a *strict quotient* of the
   oriented read-string observable that the Not-So-Greedy / Shomorony read model
   is built on (`SourceFaithfulIs.Genome.window`). Any likelihood that is a
   function of the molecule-class count — the W1/W2 `lik` and `exactLik` — is
   therefore reverse-complement **invariant** (`molCount_map_rc`, `lik_rc_blind`),
   while the oriented observable is not (`window2_ne_window3`). The two are
   different observable representations; one cannot be substituted for the other
   in a single shared observable data model without either discarding the
   oriented distinctions NSG uses or changing the W1/W2 likelihood to a different
   one.

2. **Missing conditional layer (reused, not re-proved).** The W1/W2 model
   carries no candidate prior and no candidate-specific side event `E`, so the
   conditional posterior `P(g | obs, E) ∝ π g · P(obs | g) · 1_{E(g,obs)}` of (A)
   is not defined there. The merged `AssemblyP1.W1W2SeparationCompatibility`
   kernel-checks only the (B)-side failure under the shared fixed count-vector
   objectives. This module reuses that verdict and does not fork it.

## What is and is not claimed

* No contradiction is manufactured between the Not-So-Greedy oriented guarantee
  and the W1/W2 molecule likelihood failure: they are **different observables**
  (oriented strings versus reverse-complement molecule classes), exactly as the
  paper's Remark `rem:historical-distinctions`(b) and Proposition
  `prop:historical-source` require. The W1/W2 (B)-side failure is a statement
  about the molecule observable only.
* The feasibility-predicate axis also differs: W1/W2 use the historical
  matched-string `I_s^match` (`HistoricalInformationFeasible`), whereas the
  merged #271 genome adapter uses the placement-based latent-start
  `InformationFeasible`. The two are incomparable (paper Proposition
  `prop:historical-source`; kernel-checked instances in
  `AssemblyP1/AcgtWitness211.lean` and `AssemblyP1/HistoricalCovers.lean`), so
  even the `E`-side objects are not shared.
* The genome-level adapter for the oriented model remains the bounded finite
  witness of `AssemblyP1/ConditionalVsMLGenomeAdapter271`; it is a *separate*
  adapter on the oriented observable, not a reconciliation with the molecule
  W1/W2 model. Keeping that adapter open is allowed by the issue.

No `sorry`/`admit`/`axiom`/`native_decide`; the axiom audit is extended in
`AxiomAudit271.lean`.
-/

set_option autoImplicit false

namespace AssemblyP1.W1W2RcOrientedRepresentation271

open AssemblyP1.SameLengthSection62Counterexample

/-! ## 1. The reverse-complement collapse is non-injective and RC-invariant -/

/-- The implemented strand reverse complement `rc` is an involution on
length-`3` oriented words: `rc (rc w) = w`. -/
theorem rc_involutive : Function.Involutive rc := by
  intro w
  funext i
  fin_cases i <;> simp [rc, comp] <;> cases w 0 <;> cases w 1 <;> cases w 2 <;> rfl

/-- **The molecule class is reverse-complement invariant.** `cls (rc w) = cls w`:
a read and its reverse complement are the *same* molecule class, which is the
defining feature of the MB09 molecule representation. -/
theorem cls_rc (w : W3) : cls (rc w) = cls w := by
  apply Fin.ext
  simp only [cls, Fin.val_mk]
  rw [rc_involutive w]
  exact Nat.min_comm _ _

/-- **The molecule-class collapse is not injective.** There are distinct oriented
length-`3` reads with the same molecule class; concretely the read `ATA` and its
reverse complement `TAT`. Hence the molecule-class observable strictly coarsens
the oriented read-string observable. -/
theorem cls_not_injective : ¬ Function.Injective cls := by
  intro hinj
  let u : W3 := ![Base.A, Base.T, Base.A]
  have huv : u ≠ rc u := by decide
  exact huv (hinj (cls_rc u)).symm

/-- The packaged non-injectivity witness: distinct oriented reads `ATA`, `TAT`
collapse to one molecule class. -/
theorem exists_rc_pair_same_class :
    ∃ u v : W3, u ≠ v ∧ cls u = cls v := by
  refine ⟨![Base.A, Base.T, Base.A], rc ![Base.A, Base.T, Base.A],
    (by decide), ?_⟩
  exact (cls_rc ![Base.A, Base.T, Base.A]).symm

/-! ## 2. The concrete W1 instance: oriented windows `ATA`/`TAT` collapse -/

/-- On the W1 truth `AAATAT`, the oriented windows at starts `2` and `3` are
distinct (`ATA` versus `TAT`). -/
theorem window2_ne_window3 : window6 truth 2 ≠ window6 truth 3 := by decide

/-- The window at start `3` is the reverse complement of the window at start
`2` (`TAT = rc ATA`). -/
theorem window3_eq_rc_window2 : window6 truth 3 = rc (window6 truth 2) := by
  decide

/-- The two distinct oriented windows at starts `2` and `3` land in the *same*
molecule class: the W1 observable cannot tell them apart. -/
theorem window_cls_eq : cls (window6 truth 2) = cls (window6 truth 3) := by
  rw [window3_eq_rc_window2, cls_rc]

/-! ## 3. The molecule-class count observable is RC-invariant -/

/-- Count of a list of oriented reads that fall in molecule class `c`. This is
the molecule-class observable the W1/W2 spectra and likelihood are functions
of. -/
def molCount (reads : List W3) (c : Fin 8) : Nat :=
  (reads.filter (fun w => cls w = c)).length

/-- **The molecule-class count is reverse-complement invariant.** Replacing every
oriented read by its reverse complement leaves the molecule-class counts
unchanged, because `cls ∘ rc = cls`. -/
theorem molCount_map_rc (reads : List W3) (c : Fin 8) :
    molCount (reads.map rc) c = molCount reads c := by
  unfold molCount
  induction reads with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [cls_rc w]
    by_cases h : cls w = c
    · simp [h, ih]
    · simp [h, ih]

/-- The W1 observed read-molecule count vector is exactly the molecule-class
count of the oriented windows of the truth at the realized starts. -/
theorem obs_eq_molCount (c : Fin 8) :
    obs c = molCount (readStarts.map (window6 truth)) c := by
  unfold obs molCount
  rw [List.filter_map]
  simp only [List.length_map]
  rfl

/-! ## 4. The oriented read list and its reverse-complement image -/

/-- The oriented read list of the W1 realization: the truth's windows at the
realized starts. -/
def orientedReads : List W3 := readStarts.map (window6 truth)

/-- Its reverse-complement image, the same molecule content with every oriented
read replaced by its reverse complement. -/
def orientedReadsRc : List W3 := orientedReads.map rc

/-- The two oriented read lists are genuinely different oriented observations. -/
theorem orientedReads_ne_rc : orientedReads ≠ orientedReadsRc := by decide

/-- They have identical molecule-class count vectors. -/
theorem molCount_orientedReadsRc_eq :
    molCount orientedReadsRc = molCount orientedReads := by
  funext c
  exact molCount_map_rc orientedReads c

/-- The W1 observed molecule count is the molecule count of the oriented read
list. -/
theorem obs_eq_molCount_orientedReads : obs = molCount orientedReads := by
  funext c
  exact obs_eq_molCount c

/-- **The molecule likelihood is blind to the oriented/RC distinction.** The W1
molecule likelihood at the RC image of the oriented read list equals the
likelihood at the original: the objective is a function of the RC-invariant
molecule counts, not of the oriented reads. -/
theorem lik_rc_blind : lik (molCount orientedReadsRc) dS = lik obs dS := by
  rw [obs_eq_molCount_orientedReads, molCount_orientedReadsRc_eq]

/-! ## 5. The representation verdict, packaged -/

/-- **Representation verdict (kernel-checked core).** All at once:

* the reverse-complement collapse `cls` is non-injective (`ATA`/`TAT` share a
  class);
* on the W1 truth the distinct oriented windows at starts `2` and `3` collapse
  to one molecule class;
* the W1 observable `obs` is the molecule-class count of the oriented read list;
* replacing every oriented read by its reverse complement leaves the molecule
  counts — and hence the W1 likelihood — unchanged;
* yet the two oriented read lists are different oriented observations.

So the W1/W2 reverse-complement-collapsed likelihood is a function of a *strict
quotient* of the oriented read-string observable: it cannot be the oriented
Not-So-Greedy read-string likelihood, and no single shared observable data model
can carry both without discarding oriented distinctions (or changing the
likelihood). -/
theorem rc_vs_oriented_verdict :
    (∃ u v : W3, u ≠ v ∧ cls u = cls v) ∧
      (window6 truth 2 ≠ window6 truth 3 ∧
        cls (window6 truth 2) = cls (window6 truth 3)) ∧
      obs = molCount orientedReads ∧
      molCount orientedReadsRc = molCount orientedReads ∧
      orientedReads ≠ orientedReadsRc ∧
      lik (molCount orientedReadsRc) dS = lik obs dS :=
  ⟨exists_rc_pair_same_class,
    ⟨window2_ne_window3, window_cls_eq⟩,
    obs_eq_molCount_orientedReads,
    molCount_orientedReadsRc_eq,
    orientedReads_ne_rc,
    lik_rc_blind⟩

end AssemblyP1.W1W2RcOrientedRepresentation271
