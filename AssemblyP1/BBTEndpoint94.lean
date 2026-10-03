import AssemblyP1.PopulationUniqueness
import AssemblyP1.BBTAdmissibleObstruction
import AssemblyP1.BBTInterleavedAdmissible
import AssemblyP1.BBTSupportInvariant
import AssemblyP1.BBTEulerianSearch

/-!
# Board 94, front `94b15` (ENDPOINT): the SINGLE final theorem for #89

This module writes down, once, in the project's own terms, the theorem that
closes board issue #94 / issue #89, states it **without weakening it**, and
isolates the exact residual obligations as `Prop`s so that a later pass does not
have to re-derive them from board comments.

Read `docs/population-uniqueness-end-to-end-89.md` (the #89 endpoint note) and
`docs/board94-endgame-statement-94.md` (this branch's statement front) first.

## 1. The endpoint is ONE exported theorem

`thm:population` of Bresler–Bresler–Tse 2013, in the published model, is

```
Endpoint L  :=  ∀ {G} (hG : 0 < G) (hL : 1 < L) (S : Fin G → α),
    IsPrimitive S → P2 hG L S →
      (a) ∀ K hK W, AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S)
    ∧ (b) ∀ K hK W, AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
            ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S
```

clause (a) being "the truth is a population maximizer" and clause (b) being
"every population tie is a cyclic shift of the truth", i.e. uniqueness up to
cyclic rotation of the genome — the strict reading of "the maximum-likelihood
sequence is the true sequence" recorded in `docs/ml-formalization-contract.md`
and the tie-semantics section of `docs/population-uniqueness-end-to-end-89.md`.
It is
**not** weakened here: no `PopTie`, no `PopMaximizer`, no caller-supplied bridge
parameter survives, and the candidate class is the actual `P2` of `def:P1P2`
together with actual primitivity.

`Endpoint L` is **already a theorem of this repository**,
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`, on the
single non-kernel hypothesis `BBTEulerian.EulerianCycleObstruction L`.
`endpoint_of_obstruction` below is that fact, re-derived in one line so the
gap is visible in one place.

## 2. The SINGLE remaining obligation

`BBTEulerian.EulerianCycleObstruction (α := α) L` (Pevzner 1995 Lemma 9 /
`thm:BBT`, read in the Eulerian-cycle form of Bresler–Bresler–Tse 2013,
Theorem 3): the condensed `(L-1)`-mer graph of a Ukkonen-satisfying genome has
a unique Eulerian cycle up to choice of starting point.  Its exact text is
`BBTEulerian.lean:400`:

```
∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), Ukkonen hK L S →
  ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
    VertexCycleEq hK L S σ (Equiv.refl _) ∨ LongObstruction hK L S
```

Everything else in the chain — the Gibbs/KL layer, `P2.imp_Ukkonen`, the
gcd-one reduction, the proportional-cancellation lemma, `BBTUniqueAt` and its
derivation from the obstruction — is kernel-checked in this repository.

`Residual L` below is that obligation as a `Prop`.  It is stated, not proved.

## 3. STANDING RULE: `AdmissibleObstruction` is a CONCLUSION

`BBTAdmissible.AdmissibleObstruction` is the endgame's replacement for the
refuted `LongObstruction`: two interleaved right-maximal repeats of length
`≥ L - 1`, at least one preceding-blocked.  Because
`BBTAdmissible.P2_and_admissible_00101` is kernel-checked — `P2` and
`AdmissibleObstruction` hold **together** at `S = 00101`, `L = 3` — the
statement `P2 ∧ AdmissibleObstruction → False` is **false by construction**.

**No statement of that shape occurs anywhere in this file, and no future front
may write one.**  `AdmissibleObstruction` may only ever appear as a *conclusion*
(of the descent step) or as a *target to be refuted from another side*; the
discharger must produce `False` from `P2` plus `Bad`-ness alone.

`DescentObligation` / `DischargerObligation` below are stated in the only
admissible shapes: the descent obligation *concludes* `AdmissibleObstruction`
from descent hypotheses; the discharger obligation concludes `False` from `P2`
and badness and **never mentions** `AdmissibleObstruction`.

## 4. Non-axioms

No `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, or linter suppression
occurs in this file.  Everything is kernel-checked by `lake env lean`.
-/

namespace AssemblyP1.BBTEndpoint94

open AssemblyP1
open AssemblyP1.P2
open AssemblyP1.BBTEulerian
open AssemblyP1.PopulationUniqueness
open AssemblyP1.PopulationGibbs
open AssemblyP1.PopulationReduction
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords
open AssemblyP1.BBTAdmissible
open AssemblyP1.BBTReplacement
open AssemblyP1.BBTSupport
open AssemblyP1.BBTEulerianSearch
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.OrientedRigidity
open AssemblyP1.BBTChords

variable {α : Type} [DecidableEq α] [Fintype α] {G : ℕ}

/-! ## 1. The single final theorem for #89 -/

/-- **THE SINGLE FINAL THEOREM FOR #89 (`thm:population`).**  Among primitive
`P2`-admissible oriented circular candidates, the truth maximizes the published
population log-likelihood, and every population tie is a cyclic shift of the
truth.  Quantified here as a `Prop` so that the single hypothesis it needs is
visible; `endpoint_of_obstruction` shows it is already a theorem of the library
under `Residual`. -/
def Endpoint (L : ℕ) : Prop :=
  ∀ (hG : 0 < G) (_hL : 1 < L) (S : Fin G → α),
    PopulationReduction.IsPrimitive S → P2 hG L S →
      ( (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              ≤ PopLogLik (popSpectrum L hG S) (popSpectrum L hG S))
        ∧
        (∀ (K : ℕ) (hK : 0 < K) (W : Fin K → α), AdmClass L hK W →
            PopLogLik (popSpectrum L hG S) (popSpectrum L hK W)
              = PopLogLik (popSpectrum L hG S) (popSpectrum L hG S) →
            ∃ hGK : G = K, RotEquiv hG (hGK ▸ W) S) )

/-! ## 2. The single remaining obligation: `thm:BBT` in Eulerian-cycle form -/

/-- **THE SINGLE REMAINING MATHEMATICAL OBLIGATION.**  Uniqueness of the
Eulerian cycle of the condensed `(L-1)`-mer graph, in the obstruction form of
`BBTEulerian.EulerianCycleObstruction` (`BBTEulerian.lean:400`).  This is a
`def`, not an `axiom`; it is the only hypothesis of `Endpoint` that is not
kernel-checked in this repository. -/
def Residual (L : ℕ) : Prop := BBTEulerian.EulerianCycleObstruction (α := α) L

/-- **The endpoint follows from the single residual obligation.**  Kernel-checked;
this is the whole of the gap. -/
theorem endpoint_of_obstruction (L : ℕ) (h : Residual (α := α) L) :
    Endpoint (α := α) (G := G) L := by
  intro hG _hL S hPrimS hP2S
  exact population_unique_ML_up_to_rotation L hG _hL S hPrimS hP2S h

/-! ## 3. The descent obligations, in the only admissible shapes

`BBTAdmissible.AdmissibleObstruction` is a CONCLUSION.  The two obligations
below are what board 94 has left to prove inside the descent; both are stated
as `Prop`s with no proof, and both are discharged *upward* into `Endpoint` only
if `Residual` is proved.  Note they are obligations about the *descent*, not the
whole of `Residual`; the gap between them and `Residual` is documented in
`docs/population-uniqueness-end-to-end-89.md` ("the one residual formalization
boundary") and quantified in `docs/admissible-obstruction-94.md` §5. -/

/-- **Descent obligation (step 4 of `docs/admissible-obstruction-94.md` §5).**
A selected interleaving of a *primitive* genome yields the admissible
obstruction.  `AdmissibleObstruction` occurs here as a **conclusion**, never as a
hypothesis.

Kernel-checked on this branch at general `G`, general `L`, under primitivity:
`BBTInterleaved.selectedInterleaved_admissible_of_P2` (commit `078d2b7`).  This
`Prop` is the *full* form demanded by `docs/admissible-obstruction-94.md` §5,
i.e. without the `P2` hypothesis the front could not state. -/
def DescentObligation : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (θ : Fin K → Fin K), 2 ≤ M →
    PopulationReduction.IsPrimitive S → P2 hK M S →
      Function.Bijective θ → FibrePreserving (hG := hK) (L := M) S θ →
        OneCycle hK θ → ¬ OrbitVertexEq (hG := hK) (L := M) S θ →
          ¬ SelectedTriple (hG := hK) (L := M) S θ →
            SelectedInterleaved (hG := hK) (L := M) S θ →
              BBTAdmissible.AdmissibleObstruction hK M S

/-- The `SelectedInterleaved ⟹ AdmissibleObstruction` step, extracted from the
obligation above in the shape the descent actually uses. -/
theorem selectedInterleaved_concludes_admissible
    (hD : DescentObligation) (K M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K)
    (θ : Fin K → Fin K) (hM : 2 ≤ M)
    (hPrim : PopulationReduction.IsPrimitive S) (hP2 : P2 hK M S)
    (hbi : Function.Bijective θ) (hfp : FibrePreserving (hG := hK) (L := M) S θ)
    (hoc : OneCycle hK θ) (hgood : ¬ OrbitVertexEq (hG := hK) (L := M) S θ)
    (hnT : ¬ SelectedTriple (hG := hK) (L := M) S θ)
    (hSel : SelectedInterleaved (hG := hK) (L := M) S θ) :
    BBTAdmissible.AdmissibleObstruction hK M S :=
  hD K M S hK θ hM hPrim hP2 hbi hfp hoc hgood hnT hSel

/-- **Discharger obligation.**  From `P2` alone (plus the descent facts), derive
`False`.

This is stated so that it **cannot** be read as `P2 ∧ AdmissibleObstruction →
False`: `AdmissibleObstruction` does not occur in it, and must not.  The
instance `P2_and_admissible_00101` (kernel-checked, commit `b0de723`) shows any
statement that puts the two together as hypotheses and concludes `False` is
false at `S = 00101`, `L = 3`. -/
def DischargerObligation : Prop :=
  ∀ (K : ℕ) (M : ℕ) (S : Fin K → Fin 2) (hK : 0 < K) (θ : Fin K → Fin K), 2 ≤ M →
    PopulationReduction.IsPrimitive S → P2 hK M S →
      Function.Bijective θ → FibrePreserving (hG := hK) (L := M) S θ →
        OneCycle hK θ → ¬ OrbitVertexEq (hG := hK) (L := M) S θ →
          ¬ SelectedTriple (hG := hK) (L := M) S θ →
            SelectedInterleaved (hG := hK) (L := M) S θ → False

/-! ## 4. The refuted shapes, recorded so no future front re-proposes them -/

/-- **`P2 → LongObstruction` is refuted by construction** (`BBTAdmissible`,
commit `b0de723`): under `2 ≤ L`, `P2` is the conjunction of the negations of
exactly the two clauses of `LongObstruction`.  No discharger obligation may have
`LongObstruction` as its conclusion. -/
theorem P2_refutes_LongObstruction (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (hL : 2 ≤ L) (hP2 : P2 hG L S) : ¬ LongObstruction hG L S :=
  BBTAdmissible.P2_not_LongObstruction hG L S hL hP2

/-- **`P2` and the admissible obstruction are jointly inhabited** (`00101`,
`L = 3`), so the admissible obstruction is a real conclusion and not a
refutation of `P2`. -/
theorem admissible_not_refuted_by_P2 :
    P2 BBTChords.hG5 3 BBTReplacement.S5b ∧
      BBTAdmissible.AdmissibleObstruction (hG := BBTChords.hG5) (L := 3)
        BBTReplacement.S5b :=
  BBTAdmissible.P2_and_admissible_00101

/-! ## 5. A proved case of `Residual`: injective genomes -/

/-- **Rotation commutes with rotation.**  Missing from `BBTChords` (which has
`rotAdd_iterate` and `rotAdd_succ_add` but no commutativity lemma); proved here
because §5 needs it. -/
theorem rotAdd_comm (hG : 0 < G) (a b : ℕ) (x : Fin G) :
    rotAdd hG a (rotAdd hG b x) = rotAdd hG b (rotAdd hG a x) := by
  apply Fin.ext
  show ((x.val + b) % G + a) % G = ((x.val + a) % G + b) % G
  have h1 : Nat.ModEq G (((x.val + b) % G) + a) (x.val + b + a) :=
    (Nat.mod_modEq (x.val + b) G).symm.add_right a |>.symm
  have h2 : Nat.ModEq G (((x.val + a) % G) + b) (x.val + a + b) :=
    (Nat.mod_modEq (x.val + a) G).symm.add_right b |>.symm
  calc
    ((x.val + b) % G + a) % G = (x.val + b + a) % G := h1
    _ = (x.val + a + b) % G := by rw [show x.val + b + a = x.val + a + b by omega]
    _ = ((x.val + a) % G + b) % G := h2.symm

/-- On an injective genome, `cyc` distinguishes positions below `G`. -/
theorem cyc_inj_lt {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hS : Function.Injective S) {i j : ℕ} (hi : i < G) (hj : j < G)
    (h : cyc hG S i = cyc hG S j) : i = j := by
  unfold cyc at h
  have e1 : (⟨i % G, Nat.mod_lt _ hG⟩ : Fin G) = ⟨j % G, Nat.mod_lt _ hG⟩ := hS h
  have e2 := congrArg Fin.val e1
  simp only at e2
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at e2
  exact e2

/-- **The vertex map of an injective genome is injective** (`L ≥ 2`, so the
`(L-1)`-mer is nonempty and its first symbol pins the start). -/
theorem vtx_inj_of_inj {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (hS : Function.Injective S) (hL : 2 ≤ L) {r t : Fin G}
    (h : vtx hG L S r = vtx hG L S t) : r = t := by
  have hz : (0 : ℕ) < L - 1 := Nat.sub_pos_of_lt (by omega)
  have h0 := congrFun h (⟨0, hz⟩ : Fin (L - 1))
  unfold vtx nodeWindow at h0
  have h1 : cyc hG S r.val = cyc hG S t.val := h0
  refine Fin.ext (cyc_inj_lt hG S hS r.isLt t.isLt h1)

/-- **A `σ` commuting with the one-step rotation is a rotation.**  The centre of
the cyclic group generated by `nextPos` is generated by it. -/
theorem sigma_rot_of_comm {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G)
    (h : ∀ i : Fin G, σ (nextPos hG i) = nextPos hG (σ i))
    (i : Fin G) : σ i = rotAdd hG (σ (origin hG)).val i := by
  have key : ∀ (j : Fin G) (n : ℕ), σ (rotAdd hG n j) = rotAdd hG n (σ j) := by
    intro j n
    induction n with
    | zero =>
      calc σ (rotAdd hG 0 j) = σ j := congrArg σ (BBTChords.rotAdd_zero hG j)
        _ = rotAdd hG 0 (σ j) := (BBTChords.rotAdd_zero hG (σ j)).symm
    | succ n ih =>
      calc σ (rotAdd hG (n + 1) j) = σ (rotAdd hG 1 (rotAdd hG n j)) :=
          (rotAdd_succ_add hG n j).symm ▸ rfl
        _ = σ (nextPos hG (rotAdd hG n j)) := rfl
        _ = nextPos hG (σ (rotAdd hG n j)) := h _
        _ = nextPos hG (rotAdd hG n (σ j)) := congrArg _ ih
        _ = rotAdd hG (n + 1) (σ j) := (rotAdd_succ_add hG n (σ j))
  have hi : rotAdd hG i.val (origin hG) = i := by
    apply Fin.ext; simp only [rotAdd, origin_val, Nat.zero_add, Nat.mod_eq_of_lt i.isLt]
  have he : σ (origin hG) = rotAdd hG (σ (origin hG)).val (origin hG) := by
    refine Fin.ext ?_
    simp only [rotAdd]
    rw [origin_val, Nat.zero_add, Nat.mod_eq_of_lt (σ (origin hG)).isLt]
  have hk := key (origin hG) i.val
  rw [hi] at hk
  calc σ i = rotAdd hG i.val (σ (origin hG)) := hk
    _ = rotAdd hG i.val (rotAdd hG (σ (origin hG)).val (origin hG)) := by rw [← he]
    _ = rotAdd hG (σ (origin hG)).val (rotAdd hG i.val (origin hG)) :=
        (rotAdd_comm hG (σ (origin hG)).val i.val (origin hG)).symm
    _ = rotAdd hG (σ (origin hG)).val i := by rw [hi]

/-- Every Eulerian cycle of an injective genome's multigraph has the truth's
own vertex cycle, so the left disjunct of `EulerianCycleObstruction` always
holds there. -/
theorem vertexCycleEq_of_inj {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (_hS : Function.Injective S) (_hL : 2 ≤ L) (σ : Fin G ≃ Fin G)
    (h : ∀ i : Fin G, σ (nextPos hG i) = nextPos hG (σ i)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  refine ⟨(σ (origin hG)), ?_⟩
  intro i
  have hi := sigma_rot_of_comm hG σ h i
  rw [hi, Equiv.refl_apply]

theorem obstruction_left_of_inj {α : Type} [DecidableEq α] {K L : ℕ} (hK : 0 < K)
    (hL : 2 ≤ L) (T : Fin K → α) (hT : Function.Injective T) (σ : Fin K ≃ Fin K)
    (hEul : EulerianCycle hK L T σ) :
    VertexCycleEq hK L T σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L T :=
  Or.inl (vertexCycleEq_of_inj hK T hT hL σ
    (fun i => vtx_inj_of_inj hK T hT hL (hEul.1 i)))

omit [Fintype α] in
/-- **The residual obligation restricted to injective genomes is PROVED.**

This is `Residual L` with the candidate-genome quantifier narrowed to injective
genomes.  It is a genuine theorem of this module, with no additional hypothesis
on the truth: for every `K`, every injective `T`, every `Ukkonen` truth
condition and every Eulerian cycle `σ` of `T`'s `(L-1)`-mer multigraph, `σ`
presents the truth's own vertex cycle.

It is **strictly weaker than `Residual L`**, which quantifies over *all* genomes
`T` — in particular over the non-injective ones.  This is the precise boundary
of what front `94c02` established: the step "the vertex map is injective"
(`vtx_inj_of_inj`) is what forces `σ` to be a rotation (`sigma_rot_of_comm`), and
that step has no analogue when `T` repeats a symbol. -/
def ResidualInjective (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (T : Fin K → α), Function.Injective T →
    Ukkonen hK L T → ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L T σ →
      VertexCycleEq hK L T σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L T

omit [Fintype α] in
/-- **The injective-genome slice of `Residual`, proved.** -/
theorem residualInjective (L : ℕ) (hL : 2 ≤ L) : ResidualInjective (α := α) L := by
  intro K hK T hT hUkk σ hEul
  exact Or.inl (vertexCycleEq_of_inj hK T hT hL σ
    (fun i => vtx_inj_of_inj hK T hT hL (hEul.1 i)))

omit [Fintype α] in
/-- **The obstruction itself, on injective genomes** (`thm:BBT` restricted to
injective genomes), by `Residual`'s equivalence with `UniqueEulerianCycle`
(`BBTEulerian.uniqueEulerianCycle_of_obstruction`). -/
theorem uniqueEulerianCycle_injective (L : ℕ) (hL : 2 ≤ L) :
    ∀ (K : ℕ) (hK : 0 < K) (T : Fin K → α), Function.Injective T →
      Ukkonen hK L T → ∀ σ : Fin K ≃ Fin K, EulerianCycle hK L T σ →
        VertexCycleEq hK L T σ (Equiv.refl (α := Fin K)) := by
  intro K hK T hT hUkk σ hEul
  exact vertexCycleEq_of_inj hK T hT hL σ
    (fun i => vtx_inj_of_inj hK T hT hL (hEul.1 i))

/-! ## 6. Carrying the slice: the hypothesis that is actually used, and `L = 2` -/

/-- **The exact sufficient hypothesis for the left disjunct: the vertex map is
injective.**  This is the *only* place §5 used `Function.Injective T`, and it is
strictly weaker in two directions:

* it makes no reference to the truth `T` at all, only to its `(L-1)`-mer
  multigraph, and
* it does not require injectivity of the genome — injectivity of `T` is just one
  sufficient way of separating vertices, since the first symbol of the
  `(L-1)`-mer at `r` is `cyc hG T r`. -/
def VtxSeparating (hG : 0 < G) (L : ℕ) (T : Fin G → α) : Prop :=
  Function.Injective (vtx hG L T)

/-- **The left disjunct, from the `traverses` clause alone.**  Any `σ` commuting
with `nextPos` is a rotation (`sigma_rot_of_comm`), and rotations carry the vertex
word to itself, so `VtxSeparating` is *not* needed here and the binder is `_hV`:
separating vertices is used exactly once in §5, to turn `traverses`' equality of
*identified* vertices into an equality of points.  Isolating that step is the
point of this lemma. -/
theorem vertexCycleEq_of_vtx_inj {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S : Fin G → α) (_hL : 2 ≤ L) (σ : Fin G ≃ Fin G) (_hV : VtxSeparating hG L S)
    (h : ∀ i : Fin G, σ (nextPos hG i) = nextPos hG (σ i)) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  refine ⟨σ (origin hG), fun i => ?_⟩
  have hi : σ i = rotAdd hG (σ (origin hG)).val i := sigma_rot_of_comm hG σ h i
  funext d
  rw [hi, Equiv.refl_apply]

omit [Fintype α] in
/-- **`Residual L` restricted to genomes whose `(L-1)`-mers separate positions.**
This is §5's `ResidualInjective` with the genome-level hypothesis replaced by the
vertex-level one it actually used, so it also covers non-injective genomes whose
repeats are shorter than the read length. -/
def ResidualVtxSep (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (T : Fin K → α), VtxSeparating hK L T →
    Ukkonen hK L T → ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L T σ →
      VertexCycleEq hK L T σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L T

omit [Fintype α] in
/-- **Vertex-separating genomes satisfy the residual obligation**, proved.  This
subsumes `residualInjective`, which is re-derived below from it. -/
theorem residualVtxSep (L : ℕ) (hL : 2 ≤ L) : ResidualVtxSep (α := α) L := by
  intro K hK T hV hUkk σ hEul
  exact Or.inl (vertexCycleEq_of_vtx_inj hK T hL σ hV (fun i => hV (hEul.1 i)))

omit [Fintype α] in
/-- **§5's theorem, re-derived: injectivity of the genome separates vertices.** -/
theorem residualInjective' (L : ℕ) (hL : 2 ≤ L) : ResidualInjective (α := α) L := by
  intro K hK T hT hUkk σ hEul
  exact Or.inl (vertexCycleEq_of_vtx_inj hK T hL σ
    (fun r t h => vtx_inj_of_inj hK T hT hL h)
    (fun i => vtx_inj_of_inj hK T hT hL (hEul.1 i)))

/-- **A constant vertex map already presents the truth's own vertex cycle.**
This is the degenerate case of the same conclusion, needing no injectivity at
all: if every `(L-1)`-mer of `T` is the same window, then `VertexCycleEq σ (refl)`
holds for *every* `σ`, for the trivial reason. -/
theorem vertexCycleEq_of_vtx_const {α : Type} {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hK : 0 < G) (σ : Fin G ≃ Fin G)
    (hc : ∀ (r t : Fin G) (d : Fin (L - 1)), vtx hG L S r d = vtx hG L S t d) :
    VertexCycleEq hG L S σ (Equiv.refl (α := Fin G)) := by
  refine ⟨origin hK, fun i => ?_⟩
  have hi : rotAdd hG (origin hK).val ((Equiv.refl (α := Fin G)) i) = i := by
    apply Fin.ext
    simp only [rotAdd, origin_val, Equiv.refl_apply]
    exact Nat.mod_eq_of_lt i.isLt
  rw [hi]
  funext _
  exact hc (σ i) ((Equiv.refl (α := Fin G)) i) _

omit [Fintype α] in
/-- **A second proved slice of `Residual`, with no injectivity hypothesis: a
constant genome.**  For `T` constant the `(L-1)`-mers coincide, so the truth's
own vertex cycle is the only one and the left disjunct holds for every `σ`,
independent of the `traverses` clause.  This case is genuine (non-vacuous) but
it does not extend §5's slice: it is a different, much smaller class of genomes,
and it does not survive adding one symbol. -/
theorem residual_constant (L : ℕ) :
    ∀ (K : ℕ) (hK : 0 < K) (c : α) (T : Fin K → α), (∀ i, T i = c) →
      Ukkonen hK L T → ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L T σ →
        VertexCycleEq hK L T σ (Equiv.refl (α := Fin K)) ∨ LongObstruction hK L T := by
  intro K hK c T hT hUkk σ hEul
  refine Or.inl (vertexCycleEq_of_vtx_const hK T hK σ ?_)
  intro r t d
  have e1 : cyc hK T r.val = c := hT ⟨r.val % K, Nat.mod_lt _ hK⟩
  have e2 : cyc hK T t.val = c := hT ⟨t.val % K, Nat.mod_lt _ hK⟩
  unfold vtx nodeWindow
  have e1' : cyc hK T (r.val + d.val) = c := by
    unfold cyc
    exact hT _
  have e2' : cyc hK T (t.val + d.val) = c := by
    unfold cyc
    exact hT _
  rw [e1', e2']

/-! ### What still blocks `Residual L` at general `α`

§5 used the genome hypothesis `Function.Injective T` in exactly one place: to
turn the `traverses` clause of `EulerianCycle`, an equality of `(L-1)`-mers
`vtx (σ (nextPos i)) = vtx (nextPos (σ i))`, into an equality of *points*
`σ (nextPos i) = nextPos (σ i)` (`vtx_inj_of_inj`).  Everything after that point
is unconditional: `vertexCycleEq_of_vtx_inj` needs only the commutation, and the
commutation pins `σ` to be a rotation.

So the exact remaining step for general `α` is the single statement

> `VtxSeparating hK L T` — or, more precisely, the weaker "the `(L-1)`-mers that
> `T` identifies are the ones the truth's own cycle identifies" — for every
> `Ukkonen`-satisfying `T`.

It is **not** available and I am not claiming it.  It is false as stated for
`VtxSeparating`: a genome with a repeated symbol at distance `< L` is not
`Ukkonen`-refuted, and then `vtx` identifies two distinct starts, so `traverses`
yields `σ (nextPos i) = nextPos (σ i)` only up to the identification induced by
`vtx`.  Recovering a shift of the vertex word from that quotient is exactly
Pevzner 1995 Lemma 9 / `thm:BBT`, i.e. the content of `Residual L` itself; the
combinatorics of that quotient is not in `BBTEulerian`, and no amount of
Eulerian-cycle bookkeeping substitutes for it.  Two further honest negatives:

* `ResidualInjective'` is not a new theorem — `residualVtxSep` subsumes it, and
  it is kept only to show §5's result re-derives from the weaker hypothesis.
* **`Residual 2` is *not* a trivial case.**  At `L = 2` the window index ranges
  over `Fin 1`, so `vtx r` is constant in the window index but still separates
  `r` from `t` whenever `S r ≠ S t`; the left disjunct is then the genuine
  statement `S (σ i) = S (rotAdd k i)` for all `i`.  I drafted a proof of
  `Residual 2` on the mistaken reading that the vertex map is constant there,
  found it reduces to `S r = S t` for arbitrary `r, t`, and discarded it.  A
  front that "proves" `Residual 2` by that route is wrong.

The only genuinely new proved content of this pass is therefore: `VtxSeparating`
is the hypothesis actually used, `ResidualVtxSep` is `Residual` proved under it
(it also covers non-injective genomes whose repeats are shorter than `L`), and
`residual_constant` proves the left disjunct for constant genomes with no
hypothesis at all.  Neither reaches general `α`. -/

end AssemblyP1.BBTEndpoint94
