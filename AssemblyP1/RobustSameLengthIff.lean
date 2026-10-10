import AssemblyP1.OrientedFinalRigidity

/-!
# The exact robust same-length ML iff (board issue #256, child of #255)

This module formalizes, kernel-checks and explains the **exact** multinomial
robustness statement for the strict oriented same-length model:

> Fix a circular oriented truth `S` of length `G` and a read length `L` with
> `G ≥ L ≥ 2`. Let `A` be the length-`L` spectrum of `S` (`A w = spec_L(S)(w)`),
> let `E = supp(A)` be the edge set of the de Bruijn support graph `X_S`, and let
> `F` be the set of **all** positive integer balanced circulations `B` on `E` of
> total `G`. Admissible samples are the arbitrary finite positive count vectors
> `x` on every edge of `E`. Then
>
> `(∀ x, ∀ B ∈ F, Lik(B;x) ≤ Lik(A;x))  ↔  F = {A}`.

The two directions are:

* **`⇐` (uniqueness ⇒ robustness).** If `F = {A}` then every `B ∈ F` is `A`, so
  every ratio is `1`; this is the paper's "converse by equality of spectra".
* **`⇒` (robustness ⇒ uniqueness), the beatability direction.** If `F ≠ {A}`
  then some `B ∈ F` differs from `A`; since both are positive with equal total,
  some edge `w` has `A w < B w`. Amplifying the sample at `w` makes the exact
  likelihood ratio `(B w / A w)^M · C` exceed `1` for large `M`, so `B` strictly
  beats `A` and robustness fails. This is the paper §4 beatability argument.

The key structural point, made explicit by the formalization, is that **this iff
does not use balance, strong connectivity, the triple-repeat clause of `I_s`, or
any repeat hypothesis at all.** Balance only enters through the *definition* of
`F`: it is what makes `A ∈ F` and hence what makes the "if" direction available.
The rigidity theorem `OrientedFinal.oriented_same_length_spectrum_rigidity` is
what turns `I_s` (or merely "no long Bresler triple repeat") into `F = {A}`; the
iff itself is the general arithmetic fact `robust_iff_unique` below.

## What is proved here

* `lik`, `lik_pos`, `lik_mul_ratio`: the exact multinomial factor, its
  positivity, and the ratio identity `Lik(B;x) = Lik(A;x) · ∏_e (B e / A e)^{x e}`.
* `exists_beating_sample`: the **constructive witness**. Given positive `A ≠ B`
  with equal total `G`, it returns a concrete sample `x`, positive on every edge,
  with `Lik(A;x) < Lik(B;x)`.
* `robust_iff_unique`: the abstract iff over an arbitrary finite edge type.
* `IsPositiveCirculation`, `specVec`, `robust_iff_unique_spectrum`: the model
  instantiation `E = supp(A)`, `F` = positive balanced circulations of total `G`.
* `F_eq_singleton_of_rigidity`, `robust_of_rigidity`: the connection to the
  rigidity chain, recovering the paper's `I_s ⇒ F = {A}` consequence.

## Quantifier / modeling notes (issue #256 deliverable 4)

* **Observation realizability.** The admissible sample `x` is *any* function
  `E → ℕ` that is positive on every edge. Every such `x` is realizable: each
  `w ∈ E` is a window of `S` (`mem_support_iff_window`), so drawing `x w` reads at
  a start spelling `w` produces exactly the multiplicity vector `x`. No
  consistency between edges is imposed by the model, because reads are drawn
  independently and repeats are counted repeatedly
  (`OrientedSameLengthML.objective_depends_only_on_observation`).
* **Zero-count factors.** Restricting to samples positive on *every* edge is
  exactly what removes zero-count factors: for `B ∈ F` and `x > 0` on `E`, every
  factor `(B e / G)^{x e}` has a positive base. The beating witness constructed
  below is also positive on every edge (it equals `1` off the amplified edge), so
  it is admissible for the stated `∀ x`.
* **Fixed `G`.** The total `G` is fixed once, before `F` is formed, and appears
  both in the truth total `∑ A = G` and in every `∑ B = G`; the length factors
  `(·/G)^{x e}` therefore cancel in every ratio, which is why the comparison is
  independent of `G`. (The paper's `n > G` phenomenon is about *different*
  candidate lengths and does not occur on this same-length slice.)
* **Quantifier scope.** `∀ x` ranges over `E → ℕ` positive on every edge;
  `∀ B ∈ F` ranges over the positive balanced circulations of total `G` on `E`.
  `F = {A}` is set equality of the circulation set with the singleton spectrum.
* **Candidate extraction.** `F` is taken to be the circulation set directly, as
  the issue permits. The reduction "spelled same-length candidates ↔ positive
  circulations of total `G`" is the source note's Reduction R; the formal theorem
  here is stated over the circulation set and therefore does not depend on the
  graph-theoretic circuit-to-candidate direction, which is not formalized.

## Trust surface

No `sorry`, `admit`, or new `axiom`. The only noncomputable ingredient is the
real-number likelihood; `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace AssemblyP1.RobustSameLengthIff

open Finset BigOperators

set_option linter.unusedSectionVars false

noncomputable section

set_option maxHeartbeats 800000

/-! ## The exact multinomial factor on an abstract edge set -/

/-- **Exact multinomial factor over an edge set `E`.** For a spectrum-like
weight vector `B : E → ℕ` and an observed read-type multiplicity `x : E → ℕ`,
`lik G B x = ∏_{e} (B e / G)^{x e}`. This is the oriented same-length exact
Medvedev–Brudno objective with the observation-only scale factor
`n! / ∏_e x e!` divided out; that factor is candidate-independent and so cannot
move a comparison. -/
def lik {E : Type} [Fintype E] (G : ℕ) (B x : E → ℕ) : ℝ :=
  ∏ e, ((B e : ℝ) / (G : ℝ)) ^ (x e)

/-- The likelihood factor is positive whenever the weight vector is positive on
every edge and `G > 0`. -/
theorem lik_pos {E : Type} [Fintype E] {G : ℕ} (hG : 0 < G)
    {B x : E → ℕ} (hB : ∀ e, 0 < B e) : 0 < lik G B x := by
  unfold lik
  exact Finset.prod_pos fun e _ =>
    pow_pos (div_pos (by exact_mod_cast hB e) (by exact_mod_cast hG)) _

/-- Splitting the `G` denominator off a single factor: the candidate-dependent
part of `(b/G)^n` factors through the ratio `b/a`. -/
lemma div_pow_factor {G : ℕ} (hG : 0 < G) {a b : ℕ} (ha : 0 < a) (n : ℕ) :
    ((b : ℝ) / (G : ℝ)) ^ n = ((a : ℝ) / (G : ℝ)) ^ n * ((b : ℝ) / (a : ℝ)) ^ n := by
  rw [← mul_pow]
  congr 1
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  field_simp

/-- **Likelihood-ratio identity.** For positive `A`, the exact likelihood of `B`
is the exact likelihood of `A` times the edgewise ratio product
`∏_e (B e / A e)^{x e}`. The fixed `G` cancels. -/
theorem lik_mul_ratio {E : Type} [Fintype E] {G : ℕ} (hG : 0 < G)
    (A B x : E → ℕ) (hA : ∀ e, 0 < A e) :
    lik G B x = lik G A x * ∏ e, ((B e : ℝ) / (A e : ℝ)) ^ (x e) := by
  unfold lik
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => div_pow_factor hG (hA e) (x e)

/-! ## The constructive witness (beatability) -/

/-- **The constructive beating sample.** Let `A` and `B` be positive integer
weight vectors with the same total `G`, and suppose `B ≠ A`. Then there is a
concrete admissible sample `x` — positive on **every** edge — that strictly
defeats `A` with `B`:

`Lik(A;x) < Lik(B;x)`.

*Proof.* Since `B ≠ A` and `∑ B = ∑ A`, some edge `w₀` has `A w₀ < B w₀`. Let
`r = B w₀ / A w₀ > 1` and `C = ∏_{e ≠ w₀} (B e / A e) > 0`. Choose `M` with
`1/C < r^M` and set `x w₀ = M + 1`, `x e = 1` for `e ≠ w₀`. Then
`Lik(B;x) / Lik(A;x) = r^{M+1} · C > (1/C) · r · C = r > 1`, so `Lik(A;x) <
Lik(B;x)`. This is the paper §4 amplification, made fully constructive. -/
theorem exists_beating_sample {E : Type} [Fintype E] [DecidableEq E]
    {G : ℕ} (hG : 0 < G) (A B : E → ℕ)
    (hApos : ∀ e, 0 < A e) (hBpos : ∀ e, 0 < B e)
    (hAtot : ∑ e, A e = G) (hBtot : ∑ e, B e = G) (hne : B ≠ A) :
    ∃ x : E → ℕ, (∀ e, 0 < x e) ∧ lik G A x < lik G B x := by
  have hw : ∃ w, A w < B w := by
    by_contra h
    rw [not_exists] at h
    simp only [not_lt] at h
    apply hne
    funext e
    have hsum : ∑ e, B e = ∑ e, A e := by rw [hBtot, hAtot]
    exact (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := B) (g := A) (fun e _ => h e)).mp hsum e (Finset.mem_univ e)
  obtain ⟨w0, hw0⟩ := hw
  set r : ℝ := (B w0 : ℝ) / (A w0 : ℝ) with hrdef
  have hr1 : 1 < r := by
    rw [hrdef, one_lt_div (by exact_mod_cast hApos w0)]
    exact_mod_cast hw0
  set C : ℝ := ∏ e ∈ Finset.univ.erase w0, ((B e : ℝ) / (A e : ℝ)) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact Finset.prod_pos fun e _ =>
      div_pos (by exact_mod_cast hBpos e) (by exact_mod_cast hApos e)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / C) hr1
  refine ⟨Function.update (fun _ => 1) w0 (n + 1), ?_, ?_⟩
  · intro e
    by_cases he : e = w0
    · subst he; rw [Function.update_self]; omega
    · rw [Function.update_of_ne he]; omega
  · set x : E → ℕ := Function.update (fun _ => 1) w0 (n + 1) with hxdef
    have hx0 : x w0 = n + 1 := by rw [hxdef, Function.update_self]
    have hxne : ∀ e, e ≠ w0 → x e = 1 := by
      intro e he; rw [hxdef, Function.update_of_ne he]
    have hprod_eq : (∏ e, ((B e : ℝ) / (A e : ℝ)) ^ (x e)) = r ^ (n + 1) * C := by
      rw [show (∏ e : E, ((B e : ℝ) / (A e : ℝ)) ^ (x e))
            = ((B w0 : ℝ) / (A w0 : ℝ)) ^ (x w0)
              * ∏ e ∈ Finset.univ.erase w0, ((B e : ℝ) / (A e : ℝ)) ^ (x e)
            from (Finset.mul_prod_erase Finset.univ
              (fun e => ((B e : ℝ) / (A e : ℝ)) ^ (x e))
              (Finset.mem_univ w0)).symm]
      rw [hx0, ← hrdef]
      have herase : (∏ e ∈ Finset.univ.erase w0, ((B e : ℝ) / (A e : ℝ)) ^ (x e))
          = ∏ e ∈ Finset.univ.erase w0, ((B e : ℝ) / (A e : ℝ)) := by
        refine Finset.prod_congr rfl fun e he => ?_
        rw [hxne e (Finset.mem_erase.mp he).1, pow_one]
      rw [herase, ← hCdef]
    have hprod_gt : 1 < ∏ e, ((B e : ℝ) / (A e : ℝ)) ^ (x e) := by
      rw [hprod_eq]
      have hrpos : 0 < r := by linarith
      have hstep : (1 / C) * (r * C) < r ^ n * (r * C) :=
        mul_lt_mul_of_pos_right hn (mul_pos hrpos hCpos)
      have h1 : (1 / C) * (r * C) = r := by field_simp
      have h2 : r ^ n * (r * C) = r ^ (n + 1) * C := by rw [pow_succ]; ring
      rw [h1, h2] at hstep
      linarith
    have hratio := lik_mul_ratio hG A B x hApos
    rw [hratio]
    exact lt_mul_of_one_lt_right (lik_pos hG hApos) hprod_gt

/-! ## The abstract iff -/

/-- **The exact robust iff, abstract form.** Let `A` be a positive integer weight
vector of total `G` and let `F` be *any* set of positive integer weight vectors
of total `G` with `A ∈ F`. Then

`(∀ x positive on every edge, ∀ B ∈ F, Lik(B;x) ≤ Lik(A;x)) ↔ F = {A}`.

The `⇐` direction is immediate (if `F = {A}` every candidate is `A`). The `⇒`
direction is the contrapositive of `exists_beating_sample`: a competitor
`B ∈ F \ {A}` can be amplified to strictly beat `A`, so robustness fails.

Note that no balance, connectivity or repeat hypothesis appears: `F` is treated
opaquely. Balance enters only through the model instantiation
`robust_iff_unique_spectrum` below, which supplies `A ∈ F` for the circulation
set. -/
theorem robust_iff_unique {E : Type} [Fintype E] [DecidableEq E]
    {G : ℕ} (hG : 0 < G) (A : E → ℕ) (hApos : ∀ e, 0 < A e)
    (hAtot : ∑ e, A e = G)
    (F : Set (E → ℕ))
    (hFpos : ∀ B ∈ F, ∀ e, 0 < B e)
    (hFtot : ∀ B ∈ F, ∑ e, B e = G)
    (hAF : A ∈ F) :
    (∀ x : E → ℕ, (∀ e, 0 < x e) → ∀ B ∈ F, lik G B x ≤ lik G A x) ↔ F = {A} := by
  constructor
  · intro H
    ext B
    constructor
    · intro hB
      rw [Set.mem_singleton_iff]
      by_contra hne
      obtain ⟨x, hxpos, hxlt⟩ :=
        exists_beating_sample hG A B hApos (hFpos B hB) hAtot (hFtot B hB) hne
      exact absurd (H x hxpos B hB) (not_le.mpr hxlt)
    · intro hB
      rw [Set.mem_singleton_iff] at hB
      rw [hB]
      exact hAF
  · intro hF x _ B hB
    rw [hF] at hB
    rw [Set.mem_singleton_iff] at hB
    rw [hB]

/-! ## The model layer: `E = supp(A)` and `F` = positive balanced circulations

The abstract iff is instantiated at the actual edge set `E = supp(A)` and the
actual circulation set `F`. The only model-specific obligation is `A ∈ F`:
`specVec` (the truth spectrum restricted to `E`) is positive, balanced and of
total `G`. -/

section Model

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The edge set `E = supp(A)` of the de Bruijn support graph `X_S`: the
length-`L` windows that occur in the truth `S`. This is a subtype of
`Fin L → α`, so it carries the finite decidable instances inherited from `α`. -/
abbrev Edge {G : ℕ} (L : ℕ) (hG : 0 < G) (S : Fin G → α) : Type :=
  {w : Fin L → α // w ∈ OrientedRigidity.support (L := L) hG S}

/-- The truth spectrum `A`, read on the edge set `E = supp(A)`. -/
def specVec {G L : ℕ} (hG : 0 < G) (S : Fin G → α) : Edge L hG S → ℕ :=
  fun e => OrientedRigidity.specCount (L := L) hG S e.1

/-- **Positive balanced circulation of total `G` on `E`.** A weight vector on the
edge set that is positive on every edge, balanced at every de Bruijn node (the
out-sum equals the in-sum, written with the window prefix/suffix maps), and has
total mass `G`. This is exactly the circulation class whose uniqueness the
rigidity chain proves. -/
def IsPositiveCirculation {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ) : Prop :=
  (∀ e, 0 < B e) ∧
  (∀ k : Fin (L - 1) → α,
    (∑ e : Edge L hG S,
        (if OrientedRigidity.winPrefix e.1 = k then B e else 0)) =
    (∑ e : Edge L hG S,
        (if OrientedRigidity.winSuffix e.1 = k then B e else 0))) ∧
  (∑ e : Edge L hG S, B e = G)

/-- The circulation set `F` as a set of weight vectors on `E`. -/
def circulations {G L : ℕ} (hG : 0 < G) (S : Fin G → α) : Set (Edge L hG S → ℕ) :=
  {B | IsPositiveCirculation hG S B}

/-- Subtype sums over `E = supp(A)` are ordinary sums over the support finset. -/
theorem edge_sum_subtype {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (f : (Fin L → α) → ℕ) :
    (∑ e : Edge L hG S, f e.1) = ∑ w ∈ OrientedRigidity.support (L := L) hG S, f w :=
  (Finset.sum_subtype (OrientedRigidity.support (L := L) hG S)
    (fun _ => Iff.rfl) f).symm

/-- **The truth spectrum is positive on every edge.** -/
theorem specVec_pos {G L : ℕ} (hG : 0 < G) (S : Fin G → α) :
    ∀ e, 0 < specVec (L := L) hG S e := by
  intro e
  have h := OrientedRigidity.truth_pos_on_support (L := L) hG S e.1 e.2
  simp only [specVec]
  omega

/-- **The truth spectrum has total mass `G`.** -/
theorem specVec_total {G L : ℕ} (hG : 0 < G) (S : Fin G → α) :
    ∑ e : Edge L hG S, specVec (L := L) hG S e = G := by
  simp only [specVec]
  rw [edge_sum_subtype hG S (fun w => OrientedRigidity.specCount (L := L) hG S w)]
  exact OrientedRigidity.truth_total (L := L) hG S

/-- **The truth spectrum is balanced at every de Bruijn node.** -/
theorem specVec_balanced {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (k : Fin (L - 1) → α) :
    (∑ e : Edge L hG S,
        (if OrientedRigidity.winPrefix e.1 = k then specVec (L := L) hG S e else 0)) =
    (∑ e : Edge L hG S,
        (if OrientedRigidity.winSuffix e.1 = k then specVec (L := L) hG S e else 0)) := by
  simp only [specVec]
  rw [edge_sum_subtype hG S (fun w =>
        if OrientedRigidity.winPrefix w = k
          then OrientedRigidity.specCount (L := L) hG S w else 0),
      edge_sum_subtype hG S (fun w =>
        if OrientedRigidity.winSuffix w = k
          then OrientedRigidity.specCount (L := L) hG S w else 0)]
  by_cases hk : k ∈ OrientedRigidity.genomeNodes (L := L) hG S
  · have hb := OrientedRigidity.truth_balanced (L := L) hG S k hk
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    exact hb
  · have hpre : ∀ w ∈ OrientedRigidity.support (L := L) hG S,
        OrientedRigidity.winPrefix w ≠ k := by
      intro w hw hwk
      exact hk (hwk ▸ (OrientedRigidity.mem_nodes_of_mem_support (L := L) hG S w hw).1)
    have hsuf : ∀ w ∈ OrientedRigidity.support (L := L) hG S,
        OrientedRigidity.winSuffix w ≠ k := by
      intro w hw hwk
      exact hk (hwk ▸ (OrientedRigidity.mem_nodes_of_mem_support (L := L) hG S w hw).2)
    rw [Finset.sum_eq_zero (fun w hw => by rw [ite_eq_right (hpre w hw)]),
        Finset.sum_eq_zero (fun w hw => by rw [ite_eq_right (hsuf w hw)])]

/-- **The truth spectrum is a positive balanced circulation of total `G`**, i.e.
`A ∈ F`. -/
theorem specVec_mem_circulations {G L : ℕ} (hG : 0 < G) (S : Fin G → α) :
    specVec (L := L) hG S ∈ circulations hG S :=
  ⟨specVec_pos hG S, specVec_balanced hG S, specVec_total hG S⟩

/-- **The exact robust iff for the strict oriented same-length model.** For the
edge set `E = supp(A)` and the circulation set `F`, robustness of the truth
spectrum over all admissible samples is equivalent to `F = {A}`. -/
theorem robust_iff_unique_spectrum {G L : ℕ} (hG : 0 < G) (S : Fin G → α) :
    (∀ x : Edge L hG S → ℕ, (∀ e, 0 < x e) →
        ∀ B ∈ circulations hG S, lik G B x ≤ lik G (specVec (L := L) hG S) x) ↔
      circulations hG S = {specVec (L := L) hG S} :=
  robust_iff_unique hG (specVec (L := L) hG S) (specVec_pos hG S) (specVec_total hG S)
    (circulations hG S)
    (fun _ hB => hB.1) (fun _ hB => hB.2.2) (specVec_mem_circulations hG S)

end Model

/-! ## Connection to the rigidity chain: `I_s`-type hypotheses give `F = {A}`

The rigidity theorem `OrientedFinal.oriented_same_length_spectrum_rigidity`
turns the no-long-triple-repeat premise (discharged from the source-faithful
`I_s` by `BridgingBridge.informationFeasible_no_long_triple_repeat`) into
uniqueness of the positive balanced circulation of total `G`. Composing it with
the iff above recovers the paper's consequence: under `I_s`, the truth spectrum
is robustly optimal. -/

section Rigidity

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The extension of a weight vector on `E` to all length-`L` windows, zero off
the support. This is the bridge that lets the circulation set on the subtype
speak to `oriented_same_length_spectrum_rigidity`. -/
def extend {G L : ℕ} (hG : 0 < G) (S : Fin G → α) (B : Edge L hG S → ℕ) :
    (Fin L → α) → ℕ :=
  fun w => if hw : w ∈ OrientedRigidity.support (L := L) hG S then B ⟨w, hw⟩ else 0

theorem extend_of_mem {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ) {w : Fin L → α}
    (hw : w ∈ OrientedRigidity.support (L := L) hG S) :
    extend hG S B w = B ⟨w, hw⟩ := dite_eq_left hw

theorem extend_of_not_mem {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ) {w : Fin L → α}
    (hw : w ∉ OrientedRigidity.support (L := L) hG S) :
    extend hG S B w = 0 := dite_eq_right hw

/-- The extended vector is supported exactly on `E`. -/
theorem extend_support {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ) (hB : ∀ e, 0 < B e) :
    ∀ w, w ∈ OrientedRigidity.support (L := L) hG S ↔ 0 < extend hG S B w := by
  intro w
  constructor
  · intro hw; rw [extend_of_mem hG S B hw]; exact hB _
  · intro hw
    by_contra hnot
    rw [extend_of_not_mem hG S B hnot] at hw
    exact lt_irrefl 0 hw

/-- The extended vector has the same total `G`. -/
theorem extend_total {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ)
    (hBtot : ∑ e : Edge L hG S, B e = G) :
    ∑ w ∈ OrientedRigidity.support (L := L) hG S, extend hG S B w = G := by
  rw [← edge_sum_subtype hG S (fun w => extend hG S B w)]
  rw [show (∑ e : Edge L hG S, extend hG S B e.1) = ∑ e : Edge L hG S, B e from
    Finset.sum_congr rfl (fun e _ => extend_of_mem hG S B e.2)]
  exact hBtot

/-- The extended vector is balanced. -/
theorem extend_balanced {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (B : Edge L hG S → ℕ)
    (hBbal : ∀ k : Fin (L - 1) → α,
      (∑ e : Edge L hG S,
          (if OrientedRigidity.winPrefix e.1 = k then B e else 0)) =
      (∑ e : Edge L hG S,
          (if OrientedRigidity.winSuffix e.1 = k then B e else 0))) :
    OrientedRigidity.Balanced OrientedRigidity.winPrefix OrientedRigidity.winSuffix
      (OrientedRigidity.genomeNodes (L := L) hG S)
      (OrientedRigidity.support (L := L) hG S) (extend hG S B) := by
  intro v _
  have hL : (∑ w ∈ (OrientedRigidity.support (L := L) hG S).filter
        (fun w => OrientedRigidity.winPrefix w = v), extend hG S B w)
      = ∑ e : Edge L hG S,
          (if OrientedRigidity.winPrefix e.1 = v then B e else 0) := by
    rw [Finset.sum_filter,
      ← edge_sum_subtype hG S (fun w =>
        if OrientedRigidity.winPrefix w = v then extend hG S B w else 0)]
    exact Finset.sum_congr rfl (fun e _ => by rw [extend_of_mem hG S B e.2])
  have hR : (∑ w ∈ (OrientedRigidity.support (L := L) hG S).filter
        (fun w => OrientedRigidity.winSuffix w = v), extend hG S B w)
      = ∑ e : Edge L hG S,
          (if OrientedRigidity.winSuffix e.1 = v then B e else 0) := by
    rw [Finset.sum_filter,
      ← edge_sum_subtype hG S (fun w =>
        if OrientedRigidity.winSuffix w = v then extend hG S B w else 0)]
    exact Finset.sum_congr rfl (fun e _ => by rw [extend_of_mem hG S B e.2])
  change (∑ w ∈ (OrientedRigidity.support (L := L) hG S).filter
        (fun w => OrientedRigidity.winPrefix w = v), extend hG S B w)
      = ∑ w ∈ (OrientedRigidity.support (L := L) hG S).filter
        (fun w => OrientedRigidity.winSuffix w = v), extend hG S B w
  rw [hL, hR]
  exact hBbal v

/-- **Under the no-long-triple-repeat premise, the circulation set is the
singleton `{A}`.** Every positive balanced circulation of total `G` on `E` is
the truth spectrum, by `oriented_same_length_spectrum_rigidity`. -/
theorem F_eq_singleton_of_rigidity {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L) :
    circulations hG S = {specVec (L := L) hG S} := by
  ext B
  constructor
  · intro hB
    rw [Set.mem_singleton_iff]
    have hspec := OrientedFinal.oriented_same_length_spectrum_rigidity hG S hL hLG hno
      (extend hG S B) (extend_support hG S B hB.1) (extend_balanced hG S B hB.2.1)
      (extend_total hG S B hB.2.2)
    funext e
    have h1 : extend hG S B e.1 = OrientedRigidity.specCount (L := L) hG S e.1 := hspec e.1
    rw [extend_of_mem hG S B e.2] at h1
    simpa only [specVec] using h1
  · intro hB
    rw [Set.mem_singleton_iff] at hB
    rw [hB]
    exact specVec_mem_circulations hG S

/-- **The paper's consequence, end to end.** Under the no-long-triple-repeat
premise (hence under the source-faithful `I_s`), the truth spectrum is robustly
optimal over the whole circulation set: every positive balanced circulation `B`
of total `G` has exact likelihood at most the truth's, for every admissible
sample. -/
theorem robust_of_rigidity {G L : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hL : 2 ≤ L) (hLG : L ≤ G)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L) :
    ∀ x : Edge L hG S → ℕ, (∀ e, 0 < x e) →
      ∀ B ∈ circulations hG S, lik G B x ≤ lik G (specVec (L := L) hG S) x :=
  (robust_iff_unique_spectrum hG S).mpr (F_eq_singleton_of_rigidity hG S hL hLG hno)

end Rigidity

end

end AssemblyP1.RobustSameLengthIff
