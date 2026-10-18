import Mathlib
import AssemblyP1.FiniteBayesianSideInformation
import AssemblyP1.FiniteSideInformationOrder
import AssemblyP1.FiniteSideInformationSourcePromise
import AssemblyP1.FiniteSideInformationReadStringAdapter

/-!
# The concrete decoder-level conditional-certainty endpoint for the `I_s` adapter (#272)

The merged `#272` modules reduce the "does a weakest sufficient source-defined
promise exist?" question to a sufficiency obligation and instantiate it on the
literal read-string adapter `AssemblyP1.FiniteSideInformationReadStringAdapter`:

* `AssemblyP1.FiniteBayesianSideInformation` (PR #195) fixes the exact posterior
  semantics `π g · p_g(r) · 1_E(g,r)`, the structural predicate `Sufficient`, and
  the abstract bridge `fibreUnique_of_decoder` / `conditional_certain_of_fibreUnique`.
* `AssemblyP1.FiniteSideInformationReadStringAdapter` (PR #297) builds the literal
  adapter promise `isPromiseReadStringSpelling`, proves it is read-dependent, and
  reduces weakest-promise existence to sufficiency of the adapter.

What remained OPEN (case (b) of the `#272` open list, and §5.3 of the adapter
note) was the **concrete decoder-level certainty endpoint**: the abstract bridge
was proved, but nothing yet took an actual read-only decoder on the read-string
observation type, attributed the published Not-So-Greedy correctness guarantee to
it as an explicit hypothesis, and concluded that the conditional posterior on the
true orbit class equals one.  The adapter docstring *described* the chain but the
module only carried the fibre-uniqueness form.

This module supplies that endpoint, reusing (not reproving) the merged objects:

* `IsCorrectReadStringDecoder` — the read-only decoder `A : Finset (Fin L → α) →
  (Fin n → α)` is correct on the adapter support: every candidate promising `Y`
  lies in the orbit of `A Y`.  This is exactly the published
  Shomorony--Kim--Courtade--Tse (2016) Not-So-Greedy guarantee, stated as an
  explicit attributed hypothesis and **not** proved here.
* `fibreUnique_readStringIS_of_decoder` — that guarantee gives feasible-fibre
  uniqueness of the adapter promise (`fibreUnique_of_decoder`).
* `sufficient_readStringIS_of_decoder` / `weakest_readStringIS_of_decoder` — it
  makes the adapter promise sufficient and hence gives a weakest admissible
  sufficient promise in the read-dependent `I_s` family.
* `conditional_certain_readStringIS_of_decoder` — it forces the conditional
  posterior on the true orbit class to equal one at every positive-probability
  observation of a positive-probability truth
  (`conditional_certain_of_fibreUnique`).  This is the decoder-level certainty
  endpoint.
* `weakest_and_certain_readStringIS_of_decoder` — the bundled statement.

The external guarantee enters only as the hypothesis `hA`; no `axiom`, `sorry`,
or `admit` is introduced.  The axiom audit is
`AssemblyP1/FiniteSideInformationDecoderEndpointAudit.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace AssemblyP1.FiniteSideInformationDecoderEndpoint

open AssemblyP1.FiniteBayesianSideInformation
open AssemblyP1.FiniteSideInformationOrder
open AssemblyP1.FiniteSideInformationSourcePromise
open AssemblyP1.FiniteSideInformationReadStringAdapter

section Endpoint

variable {α : Type*} [DecidableEq α] [Fintype α]
variable {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
variable {n L : ℕ} {hn : 0 < n}

/-- **The attributed external guarantee.**  A read-only decoder `A` on the
read-string observation type is correct on the adapter support when every
candidate spelling `w` that promises the observation `Y` lies in the orbit of
`A Y`.  This is the published Not-So-Greedy correctness guarantee (Shomorony,
Kim, Courtade, Tse 2016), stated as an explicit hypothesis and not proved here. -/
def IsCorrectReadStringDecoder (hn : 0 < n) (orbit : (Fin n → α) → Θ)
    (A : Finset (Fin L → α) → (Fin n → α)) : Prop :=
  ∀ w Y, isPromiseReadStringSpelling n L hn w Y → orbit (A Y) = orbit w

/-- **Decoder correctness gives fibre uniqueness.**  The attributed guarantee
`hA` puts any two candidates promising the same observation in one orbit — the
exact form required by `Sufficient` and by the merged `fibreUnique_of_decoder`. -/
theorem fibreUnique_readStringIS_of_decoder (orbit : (Fin n → α) → Θ)
    (A : Finset (Fin L → α) → (Fin n → α))
    (hA : IsCorrectReadStringDecoder hn orbit A) :
    ∀ w v Y, isPromiseReadStringSpelling n L hn w Y →
      isPromiseReadStringSpelling n L hn v Y → orbit w = orbit v :=
  fibreUnique_of_decoder (isPromiseReadStringSpelling n L hn) A orbit hA

/-- **Decoder correctness makes the adapter promise sufficient.** -/
theorem sufficient_readStringIS_of_decoder
    (π : (Fin n → α) → ℝ) (p : (Fin n → α) → Finset (Fin L → α) → ℝ)
    (orbit : (Fin n → α) → Θ) (A : Finset (Fin L → α) → (Fin n → α))
    (hA : IsCorrectReadStringDecoder hn orbit A) :
    Sufficient π p orbit (isPromiseReadStringSpelling n L hn) :=
  sufficient_readStringIS_of_fibreUnique π p orbit
    (fibreUnique_readStringIS_of_decoder orbit A hA)

/-- **Decoder correctness yields a weakest admissible sufficient promise.** -/
theorem weakest_readStringIS_of_decoder
    (π : (Fin n → α) → ℝ) (p : (Fin n → α) → Finset (Fin L → α) → ℝ)
    (orbit : (Fin n → α) → Θ) (A : Finset (Fin L → α) → (Fin n → α))
    (hA : IsCorrectReadStringDecoder hn orbit A) :
    ∃ W, IsWeakestAdmissible (AdmReadStringIS n L hn) π p orbit W :=
  weakest_readStringIS_of_fibreUnique π p orbit
    (fibreUnique_readStringIS_of_decoder orbit A hA)

/-- **The concrete decoder-level conditional-certainty endpoint.**  Under the
attributed Not-So-Greedy guarantee `hA`, for any positive-probability truth `w`
and any observation `Y` it promises, the conditional posterior on the true orbit
class `orbit w` equals one.  This is `conditional_certain_of_fibreUnique`
instantiated on the literal read-string adapter. -/
theorem conditional_certain_readStringIS_of_decoder
    [DecidableRel (isPromiseReadStringSpelling (α := α) n L hn)]
    (π : (Fin n → α) → ℝ) (p : (Fin n → α) → Finset (Fin L → α) → ℝ)
    (orbit : (Fin n → α) → Θ) (A : Finset (Fin L → α) → (Fin n → α))
    (hA : IsCorrectReadStringDecoder hn orbit A)
    (hπ : ∀ w, 0 ≤ π w) (hp : ∀ w Y, 0 ≤ p w Y)
    (w : Fin n → α) (Y : Finset (Fin L → α))
    (hπw : 0 < π w) (hpw : 0 < p w Y)
    (hFY : isPromiseReadStringSpelling n L hn w Y) :
    posteriorMass π p (isPromiseReadStringSpelling n L hn) orbit Y (orbit w) = 1 :=
  conditional_certain_of_fibreUnique (isPromiseReadStringSpelling n L hn)
    π p orbit hπ hp (fibreUnique_readStringIS_of_decoder orbit A hA) w Y hπw hpw hFY

/-- **Bundled endpoint.**  The attributed Not-So-Greedy guarantee simultaneously
gives a weakest admissible sufficient promise in the read-dependent `I_s` family
and pointwise conditional certainty of the true orbit class. -/
theorem weakest_and_certain_readStringIS_of_decoder
    [DecidableRel (isPromiseReadStringSpelling (α := α) n L hn)]
    (π : (Fin n → α) → ℝ) (p : (Fin n → α) → Finset (Fin L → α) → ℝ)
    (orbit : (Fin n → α) → Θ) (A : Finset (Fin L → α) → (Fin n → α))
    (hA : IsCorrectReadStringDecoder hn orbit A)
    (hπ : ∀ w, 0 ≤ π w) (hp : ∀ w Y, 0 ≤ p w Y) :
    (∃ W, IsWeakestAdmissible (AdmReadStringIS n L hn) π p orbit W) ∧
      (∀ w Y, 0 < π w → 0 < p w Y → isPromiseReadStringSpelling n L hn w Y →
        posteriorMass π p (isPromiseReadStringSpelling n L hn) orbit Y (orbit w) = 1) :=
  ⟨weakest_readStringIS_of_decoder π p orbit A hA,
    fun w Y hπw hpw hFY =>
      conditional_certain_readStringIS_of_decoder π p orbit A hA hπ hp w Y hπw hpw hFY⟩

end Endpoint

end AssemblyP1.FiniteSideInformationDecoderEndpoint
