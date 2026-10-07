import AssemblyP1.Issue94SameAltF
import AssemblyP1.Issue94TW5Single
import AssemblyP1.BBTLadder

namespace AssemblyP1.Issue94SupportDescent

open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94SameAltF

variable {α : Type} [DecidableEq α] {G : ℕ}

def PointwiseVtxEq (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ τ : Fin G ≃ Fin G) : Prop :=
  ∀ i : Fin G, vtx hG L S (σ i) = vtx hG L S (τ i)

theorem PointwiseVtxEq.refl (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (σ : Fin G ≃ Fin G) :
    PointwiseVtxEq hG L S σ σ := by
  intro i
  rfl

theorem PointwiseVtxEq.trans (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {σ τ υ : Fin G ≃ Fin G}
    (hστ : PointwiseVtxEq hG L S σ τ)
    (hτυ : PointwiseVtxEq hG L S τ υ) :
    PointwiseVtxEq hG L S σ υ := by
  intro i
  exact (hστ i).trans (hτυ i)

def supportMeasure (hG : 0 < G) (σ : Fin G ≃ Fin G) : ℕ :=
  (Support (AltF hG σ)).card

theorem supportMeasure_zero_iff (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    supportMeasure hG σ = 0 ↔ ∀ q : Fin G, AltF hG σ q = q := by
  constructor
  · intro hzero q
    have hempty : Support (AltF hG σ) = ∅ := Finset.card_eq_zero.mp hzero
    by_contra hne
    have hmem : q ∈ Support (AltF hG σ) := (mem_Support).2 hne
    rw [hempty] at hmem
    simp at hmem
  · intro hfix
    apply Finset.card_eq_zero.mpr
    ext q
    simp [Support, hfix q]

theorem altF_refl (hG : 0 < G) (q : Fin G) :
    AltF hG (Equiv.refl (Fin G)) q = q := by
  unfold AltF Succ
  simp only [Equiv.refl_symm, Equiv.refl_apply]
  exact nextPrev hG q

theorem exists_terminal_of_support_descent
    (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (hstep :
      ∀ σ : Fin G ≃ Fin G,
        EulerianCycle hG L S σ →
        0 < supportMeasure hG σ →
        ∃ τ : Fin G ≃ Fin G,
          EulerianCycle hG L S τ ∧
          supportMeasure hG τ < supportMeasure hG σ ∧
          PointwiseVtxEq hG L S σ τ) :
    ∀ σ : Fin G ≃ Fin G, EulerianCycle hG L S σ →
      ∃ τ : Fin G ≃ Fin G,
        EulerianCycle hG L S τ ∧
        supportMeasure hG τ = 0 ∧
        PointwiseVtxEq hG L S σ τ := by
  have go :
      ∀ n : ℕ, ∀ σ : Fin G ≃ Fin G,
        supportMeasure hG σ ≤ n →
        EulerianCycle hG L S σ →
        ∃ τ : Fin G ≃ Fin G,
          EulerianCycle hG L S τ ∧
          supportMeasure hG τ = 0 ∧
          PointwiseVtxEq hG L S σ τ := by
    intro n
    induction n with
    | zero =>
        intro σ hle hEul
        have hz : supportMeasure hG σ = 0 := by omega
        exact ⟨σ, hEul, hz, PointwiseVtxEq.refl hG L S σ⟩
    | succ n ih =>
        intro σ hle hEul
        by_cases hz : supportMeasure hG σ = 0
        · exact ⟨σ, hEul, hz, PointwiseVtxEq.refl hG L S σ⟩
        · have hpos : 0 < supportMeasure hG σ := Nat.pos_of_ne_zero hz
          obtain ⟨τ, hEτ, hlt, hpw⟩ := hstep σ hEul hpos
          have hleτ : supportMeasure hG τ ≤ n := by omega
          obtain ⟨υ, hEυ, hzero, hpwτυ⟩ := ih τ hleτ hEτ
          exact ⟨υ, hEυ, hzero,
            PointwiseVtxEq.trans hG L S hpw hpwτυ⟩
  intro σ hEul
  exact go (supportMeasure hG σ) σ (Nat.le_refl _) hEul

theorem long_eulerian_unique_of_support_descent
    (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    (hstep :
      ∀ σ : Fin G ≃ Fin G,
        EulerianCycle hG L S σ →
        0 < supportMeasure hG σ →
        ∃ τ : Fin G ≃ Fin G,
          EulerianCycle hG L S τ ∧
          supportMeasure hG τ < supportMeasure hG σ ∧
          PointwiseVtxEq hG L S σ τ) :
    ∀ σ : Fin G ≃ Fin G,
      EulerianCycle hG L S σ →
      VertexCycleEq hG L S σ (Equiv.refl (Fin G)) := by
  intro σ hEul
  obtain ⟨τ, _hEτ, hzero, hpw⟩ :=
    exists_terminal_of_support_descent hG L S hstep σ hEul
  have hfix : ∀ q : Fin G, AltF hG τ q = q :=
    (supportMeasure_zero_iff hG τ).mp hzero
  have hsame :
      ∀ q : Fin G,
        AltF hG (Equiv.refl (Fin G)) q = AltF hG τ q := by
    intro q
    rw [altF_refl hG q, hfix q]
  have hterminal :
      VertexCycleEq hG L S τ (Equiv.refl (Fin G)) :=
    same_altF_vertexCycleEq hG L S
      (Equiv.refl (Fin G)) τ
      (fun _ => rfl) hsame
  rcases hterminal with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro i
  exact (hpw i).trans (hk i)

#print axioms AssemblyP1.Issue94SupportDescent.exists_terminal_of_support_descent
#print axioms AssemblyP1.Issue94SupportDescent.long_eulerian_unique_of_support_descent

end AssemblyP1.Issue94SupportDescent
