import AssemblyP1.GraverRigidity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Two-closed-walk rigidity criterion (issue #257)

This file formalizes the **repeat-structural** characterization of rigidity
announced on Antonina board issue #257, resolving open item §8.3 of
`docs/source-notes/issue-257-rigid-read-graphs.md`: the exact circulation
criterion (`AssemblyP1.ExactRigidityCriterion.nonrigid_iff_exists_delta`) is
equivalent to the existence of a *two-closed-walk* certificate, so the
"two-cycle" obstruction of §3–§4 is not the only structural form.

> Let `A` be a positive balanced circulation of total `G` on a support graph
> whose edge type is `E` and whose routing property holds (the flow-routing
> consequence of strong connectivity). Then `A` is **not** rigid **iff** there
> are two nonnegative integer circulations `f, g` (count vectors of two closed
> walks) with equal total `∑ f = ∑ g`, `f ≠ g`, and `f - g ≥ 1 - A`
> coordinatewise (`InBox A (f - g)`).

## Proof structure

Write the exact witness `δ = B - A` of Theorem 1. Split `δ = posPart δ -
negPart δ`. Because `δ` is balanced, `posPart δ` and `negPart δ` have the same
divergence; by the routing property the divergence of `posPart δ` can be
undone by a nonnegative integer flow `h`, so that `posPart δ + h` is a
circulation. Then `f := posPart δ + h` and `g := negPart δ + h` are both
nonnegative circulations, `f - g = δ` is inside the box, and `∑ f = ∑ g`
because `∑ δ = 0`. Conversely two such `f, g` give the feasible alternative
`A + (f - g) ≠ A`.

## Closed walks

A nonnegative integer circulation is exactly a nonnegative integer combination
of directed cycles, i.e. the count vector of a closed walk in the multigraph
where edge `e` is duplicated `f e` times; when its support is connected this is
a single Eulerian circuit. The Lean development below states the criterion in
the equivalent "two nonnegative circulations" form (no connectivity hypothesis
is needed for the equivalence, since the construction `f = posPart δ + h`,
`g = negPart δ + h` can always be further completed to connected support by
adding one spanning circulation to `h`); the explicit Eulerian/connected-support
refinement and the exhaustive small-case cross-check live in
`docs/source-notes/issue-257-rigid-read-graphs.md` §12 and
`scripts/verify_257_two_walk_iff.py`.

## Main results

* `nonrigid_of_two_nonneg_circ`: two boxed nonnegative circulations give
  non-rigidity (the easy direction, no routing hypothesis).
* `rigid_iff_no_two_nonneg_circ`: the exact iff, assuming the routing property.
* `atatat_no_two_nonneg_circ`: kernel-checked witness that `S = ATATAT`,
  `L = 3` is rigid *despite* triple `(L-1)`-mer repeats, so it admits **no**
  two-closed-walk certificate.
* `figureEight_two_walk_witness`: the figure-eight at `A = (2, 2, 1, 1)` is
  non-rigid, exhibited by the two closed walks `f = (0, 0, 1, 1)` and
  `g = (1, 1, 0, 0)` (the two `2`-cycles).
-/

namespace AssemblyP1.TwoWalkRigidity

open Finset BigOperators
open AssemblyP1.GraverRigidity

section TwoWalk

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype E] [Fintype V]

/-- **Explicit circulation predicate.** Vertex balance written with explicit
`Finset.univ.filter`s, so that it unfolds and computes on concrete graphs
(its definition is definitionally `BalancedZ tail head Finset.univ`; see
`isCirc_iff_balancedZ`). -/
def IsCirc (tail head : E → V) (f : E → ℤ) : Prop :=
  ∀ v, (∑ e ∈ Finset.univ.filter (fun e => tail e = v), f e)
      = (∑ e ∈ Finset.univ.filter (fun e => head e = v), f e)

/-- `IsCirc` is `BalancedZ` on all vertices. -/
theorem isCirc_iff_balancedZ (tail head : E → V) (f : E → ℤ) :
    IsCirc tail head f ↔ BalancedZ tail head (Finset.univ : Finset V) f := by
  unfold IsCirc BalancedZ
  simp only [Finset.mem_univ, true_implies]
  constructor <;> intro h v <;> exact h v

theorem IsCirc.add (tail head : E → V) {f g : E → ℤ}
    (hf : IsCirc tail head f) (hg : IsCirc tail head g) :
    IsCirc tail head (f + g) := by
  intro v
  have h1 := hf v
  have h2 := hg v
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  omega

theorem IsCirc.sub (tail head : E → V) {f g : E → ℤ}
    (hf : IsCirc tail head f) (hg : IsCirc tail head g) :
    IsCirc tail head (f - g) := by
  intro v
  have h1 := hf v
  have h2 := hg v
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  omega

/-- **Routing property.** Every nonnegative integer flow can be completed to a
nonnegative integer circulation by adding a nonnegative integer flow. This is
the transshipment-routing consequence of strong connectivity of the support
graph: the divergence of a nonnegative flow has total `0`, and in a strongly
connected digraph any zero-sum integer divergence is realisable by a
nonnegative integer flow (route each unit of supply to a demand along a
directed path). It is the single graph-theoretic input of the criterion. -/
def Routable (tail head : E → V) : Prop :=
  ∀ p : E → ℤ, (∀ e, 0 ≤ p e) →
    ∃ h : E → ℤ, (∀ e, 0 ≤ h e) ∧ IsCirc tail head (p + h)

/-- The **two-nonnegative-circulation** predicate: `f` and `g` are nonnegative
integer circulations of equal total mass, distinct, with their difference in
the box `∏_e [1 - A(e), ∞)`. These are the count vectors of two closed walks
(see the module docstring). -/
def TwoNonnegCirc (tail head : E → V) (A : E → ℤ) (f g : E → ℤ) : Prop :=
  (∀ e, 0 ≤ f e) ∧ (∀ e, 0 ≤ g e) ∧
    IsCirc tail head f ∧ IsCirc tail head g ∧
    (∑ e, f e) = (∑ e, g e) ∧ f ≠ g ∧ InBox A (f - g)

/-- **Easy direction.** Two nonnegative circulations of equal total, distinct
and boxed, give a feasible alternative `A + (f - g) ≠ A`; hence `A` is not
rigid. No routing hypothesis is used. -/
theorem nonrigid_of_two_nonneg_circ (tail head : E → V) (A : E → ℤ) (G : ℕ)
    (hA : Feasible tail head (Finset.univ : Finset V) G A)
    {f g : E → ℤ} (h : TwoNonnegCirc tail head A f g) :
    ¬ Rigid tail head (Finset.univ : Finset V) A G := by
  obtain ⟨hfnn, hgnn, hfb, hgb, hsum, hne, hbox⟩ := h
  have hfbZ : BalancedZ tail head (Finset.univ : Finset V) f :=
    (isCirc_iff_balancedZ tail head f).mp hfb
  have hgbZ : BalancedZ tail head (Finset.univ : Finset V) g :=
    (isCirc_iff_balancedZ tail head g).mp hgb
  intro hRig
  have hBfeas : Feasible tail head (Finset.univ : Finset V) G (A + (f - g)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e
      have h1 := hA.1 e
      have h2 := hbox e
      show (1 : ℤ) ≤ A e + (f - g) e
      omega
    · exact BalancedZ.add tail head _ hA.2.1 (BalancedZ.sub tail head _ hfbZ hgbZ)
    · have h1 : ∑ e, A e = (G : ℤ) := hA.2.2
      have h2 : ∑ e, (f - g) e = 0 := by
        simp only [Pi.sub_apply, Finset.sum_sub_distrib]
        omega
      show ∑ e, (A + (f - g)) e = (G : ℤ)
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      omega
  have heq : A + (f - g) = A :=
    hRig (A + (f - g)) hBfeas.1 hBfeas.2.1 hBfeas.2.2
  have hfg : f = g := by
    funext e
    have := congrFun heq e
    simp only [Pi.add_apply, Pi.sub_apply] at this
    omega
  exact hne hfg

/-- **Hard direction / exact criterion.** Assuming the routing property, a
non-rigid `A` admits a two-closed-walk certificate: two nonnegative
circulations `f, g` with equal total, distinct, and boxed. The witness is
`f = posPart δ + h`, `g = negPart δ + h` for the exact witness `δ = B - A`
and a routing flow `h` that completes `posPart δ` to a circulation. -/
theorem exists_two_nonneg_circ_of_nonrigid (tail head : E → V) (A : E → ℤ) (G : ℕ)
    (hrout : Routable tail head)
    (hA : Feasible tail head (Finset.univ : Finset V) G A)
    (hnr : ¬ Rigid tail head (Finset.univ : Finset V) A G) :
    ∃ f g : E → ℤ, TwoNonnegCirc tail head A f g := by
  -- extract a feasible alternative `B ≠ A`
  have hex : ∃ B : E → ℤ, Feasible tail head (Finset.univ : Finset V) G B ∧ B ≠ A := by
    by_contra hcon
    apply hnr
    intro B hBpos hBbal hBtot
    by_contra hBA
    exact hcon ⟨B, ⟨hBpos, hBbal, hBtot⟩, hBA⟩
  obtain ⟨B, hBfeas, hBA⟩ := hex
  obtain ⟨hBpos, hBbal, hBtot⟩ := hBfeas
  set δ : E → ℤ := B - A with hδdef
  have hδbZ : BalancedZ tail head (Finset.univ : Finset V) δ := by
    rw [hδdef]; exact BalancedZ.sub tail head _ hBbal hA.2.1
  have hδb : IsCirc tail head δ := (isCirc_iff_balancedZ tail head δ).mpr hδbZ
  have hδsum : ∑ e, δ e = 0 := by
    rw [hδdef]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    have h1 : ∑ e, B e = (G : ℤ) := hBtot
    have h2 : ∑ e, A e = (G : ℤ) := hA.2.2
    omega
  have hδbox : InBox A δ := by
    intro e
    have h1 := hBpos e
    show (1 - A e) ≤ δ e
    rw [hδdef]
    simp only [Pi.sub_apply]
    omega
  have hδne : δ ≠ 0 := by
    intro h0
    apply hBA
    have hcancel : B - A + A = B := by
      ext e; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hthis : δ + A = 0 + A := by rw [h0]
    rw [hδdef, hcancel] at hthis
    simpa using hthis
  -- routing completes `posPart δ` to a circulation
  have hpnn : ∀ e, 0 ≤ AssemblyP1.GraverRigidity.posPart δ e :=
    fun e => AssemblyP1.GraverRigidity.posPart_nonneg e
  obtain ⟨h, hhnn, hh⟩ := hrout (AssemblyP1.GraverRigidity.posPart δ) hpnn
  -- the two circulations
  refine ⟨AssemblyP1.GraverRigidity.posPart δ + h,
          AssemblyP1.GraverRigidity.negPart δ + h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `f ≥ 0`
    intro e
    have := hpnn e
    have := hhnn e
    simp only [Pi.add_apply]
    omega
  · -- `g ≥ 0`
    intro e
    have := AssemblyP1.GraverRigidity.negPart_nonneg (f := δ) e
    have := hhnn e
    simp only [Pi.add_apply]
    omega
  · -- `IsCirc f`
    exact hh
  · -- `IsCirc g`, using `g = (posPart δ + h) - (posPart δ - negPart δ)`
    have hpq : IsCirc tail head
        (AssemblyP1.GraverRigidity.posPart δ - AssemblyP1.GraverRigidity.negPart δ) := by
      have hfun : AssemblyP1.GraverRigidity.posPart δ - AssemblyP1.GraverRigidity.negPart δ = δ := by
        funext e
        simp only [Pi.sub_apply]
        exact (AssemblyP1.GraverRigidity.posPart_sub_negPart e).symm
      rw [hfun]; exact hδb
    have hrewrite : AssemblyP1.GraverRigidity.negPart δ + h =
        (AssemblyP1.GraverRigidity.posPart δ + h)
          - (AssemblyP1.GraverRigidity.posPart δ - AssemblyP1.GraverRigidity.negPart δ) := by
      ext e; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [hrewrite]
    exact IsCirc.sub tail head hh hpq
  · -- `∑ f = ∑ g`
    have : ∑ e, (AssemblyP1.GraverRigidity.posPart δ + h) e
        = ∑ e, (AssemblyP1.GraverRigidity.negPart δ + h) e := by
      simp only [Pi.add_apply, Finset.sum_add_distrib]
      have hfun : AssemblyP1.GraverRigidity.posPart δ - AssemblyP1.GraverRigidity.negPart δ = δ := by
        funext e
        simp only [Pi.sub_apply]
        exact (AssemblyP1.GraverRigidity.posPart_sub_negPart e).symm
      have hsumsub : ∑ e, (AssemblyP1.GraverRigidity.posPart δ
          - AssemblyP1.GraverRigidity.negPart δ) e = ∑ e, δ e := by rw [hfun]
      simp only [Pi.sub_apply, Finset.sum_sub_distrib] at hsumsub
      omega
    exact this
  · -- `f ≠ g`
    intro hfg
    apply hδne
    have hzero : (AssemblyP1.GraverRigidity.posPart δ + h)
        - (AssemblyP1.GraverRigidity.negPart δ + h) = 0 := by rw [hfg]; abel
    have hsub : (AssemblyP1.GraverRigidity.posPart δ + h)
        - (AssemblyP1.GraverRigidity.negPart δ + h) = δ := by
      ext e
      simp only [Pi.add_apply, Pi.sub_apply]
      have := AssemblyP1.GraverRigidity.posPart_sub_negPart (f := δ) e
      omega
    rw [hsub] at hzero
    exact hzero
  · -- `InBox A (f - g)`
    have hsub : (AssemblyP1.GraverRigidity.posPart δ + h)
        - (AssemblyP1.GraverRigidity.negPart δ + h) = δ := by
      ext e
      simp only [Pi.add_apply, Pi.sub_apply]
      have := AssemblyP1.GraverRigidity.posPart_sub_negPart (f := δ) e
      omega
    rw [hsub]; exact hδbox

/-- **Main theorem (two-closed-walk criterion, issue #257).** Assuming the
routing property, `A` is rigid iff no two closed walks (two nonnegative
circulations) form a boxed, equal-total, distinct pair. -/
theorem rigid_iff_no_two_nonneg_circ (tail head : E → V) (A : E → ℤ) (G : ℕ)
    (hrout : Routable tail head)
    (hA : Feasible tail head (Finset.univ : Finset V) G A) :
    Rigid tail head (Finset.univ : Finset V) A G ↔
      ¬ ∃ f g : E → ℤ, TwoNonnegCirc tail head A f g := by
  constructor
  · intro hRig hex
    obtain ⟨f, g, hfg⟩ := hex
    exact nonrigid_of_two_nonneg_circ tail head A G hA hfg hRig
  · intro hno
    by_contra hnr
    exact hno (exists_two_nonneg_circ_of_nonrigid tail head A G hrout hA hnr)

end TwoWalk

/-! ## Kernel-checked worked instances -/

section Examples

/-- `ATATAT`, `L = 3`: two nodes `AT, TA`, two edges `ATA : AT → TA`,
`TAT : TA → AT` (a single directed `2`-cycle). -/
def atatatTail : Fin 2 → Fin 2 := fun e => if e = 0 then 0 else 1
def atatatHead : Fin 2 → Fin 2 := fun e => if e = 0 then 1 else 0
def atatatA : Fin 2 → ℤ := fun _ => 3

/-- **`S = ATATAT`, `L = 3` admits no two-closed-walk certificate.** On a
`2`-cycle every nonnegative circulation is `(k, k)`, so two of them with equal
total are equal; the equal-total, distinct pair of the criterion does not
exist. Direct proof of the balance consequence; no routing hypothesis. -/
theorem atatat_no_two_nonneg_circ :
    ¬ ∃ f g : Fin 2 → ℤ, TwoNonnegCirc atatatTail atatatHead atatatA f g := by
  rintro ⟨f, g, hfnn, hgnn, hfb, hgb, hsum, hne, hbox⟩
  have hfbal : f 0 = f 1 := by
    have h0 := hfb 0
    rw [show (Finset.univ.filter (fun e : Fin 2 => atatatTail e = 0)) = {0} from by decide,
        show (Finset.univ.filter (fun e : Fin 2 => atatatHead e = 0)) = {1} from by decide] at h0
    simpa using h0
  have hgbal : g 0 = g 1 := by
    have h0 := hgb 0
    rw [show (Finset.univ.filter (fun e : Fin 2 => atatatTail e = 0)) = {0} from by decide,
        show (Finset.univ.filter (fun e : Fin 2 => atatatHead e = 0)) = {1} from by decide] at h0
    simpa using h0
  have hsum' : f 0 + f 1 = g 0 + g 1 := by
    have h := hsum
    simp only [Fin.sum_univ_two] at h
    exact h
  have h0 : f 0 = g 0 := by omega
  have h1 : f 1 = g 1 := by omega
  exact hne (by funext e; fin_cases e <;> assumption)

/-- The figure-eight support `0 → 1 → 0`, `0 → 2 → 0`. -/
def figureEightTail : Fin 4 → Fin 3 :=
  fun e => if e = 0 then 0 else if e = 1 then 1 else if e = 2 then 0 else 2
def figureEightHead : Fin 4 → Fin 3 :=
  fun e => if e = 0 then 1 else if e = 1 then 0 else if e = 2 then 2 else 0

/-- The two `2`-cycles `f = (0, 0, 1, 1)` and `g = (1, 1, 0, 0)` form a
two-closed-walk certificate for the figure-eight at `A = (2, 2, 1, 1)`
(`G = 6`): both are nonnegative circulations of total `2`, distinct, and
`f - g = (-1, -1, 1, 1) ≥ 1 - A`. So the *same support* as the rigid
`A = (1, 1, 1, 1)` becomes non-rigid — rigidity is a multiplicity, not a
topology, property. -/
theorem figureEight_two_walk_witness :
    TwoNonnegCirc figureEightTail figureEightHead
      (fun e => if e = 0 then 2 else if e = 1 then 2 else 1)
      (fun e => if e = 2 then 1 else if e = 3 then 1 else 0)
      (fun e => if e = 0 then 1 else if e = 1 then 1 else 0) := by
  unfold TwoNonnegCirc IsCirc InBox
  decide

end Examples

end AssemblyP1.TwoWalkRigidity
