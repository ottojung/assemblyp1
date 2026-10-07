import AssemblyP1.Issue94SupportDescent

namespace AssemblyP1.Issue94InvolutionSplit

open AssemblyP1
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94SupportDescent

variable {G : ℕ}

def onSet (f : Fin G → Fin G) (D : Finset (Fin G)) (x : Fin G) : Fin G :=
  if x ∈ D then f x else x

def offSet (f : Fin G → Fin G) (D : Finset (Fin G)) (x : Fin G) : Fin G :=
  if x ∈ D then x else f x

theorem onSet_involutive
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) :
    Function.Involutive (onSet f D) := by
  intro x
  by_cases hx : x ∈ D
  · have hfx : f x ∈ D := (hclosed x).mp hx
    simp [onSet, hx, hfx, hinv x]
  · simp [onSet, hx]

theorem offSet_involutive
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) :
    Function.Involutive (offSet f D) := by
  intro x
  by_cases hx : x ∈ D
  · simp [offSet, hx]
  · have hfx : f x ∉ D := by
      intro h
      exact hx ((hclosed x).mpr h)
    simp [offSet, hx, hfx, hinv x]

theorem bijective_of_involutive {g : Fin G → Fin G}
    (hinv : Function.Involutive g) : Function.Bijective g := by
  constructor
  · intro a b hab
    calc
      a = g (g a) := (hinv a).symm
      _ = g (g b) := congrArg g hab
      _ = b := hinv b
  · intro y
    exact ⟨g y, hinv y⟩

noncomputable def onSetEquiv
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) : Fin G ≃ Fin G :=
  Equiv.ofBijective (onSet f D)
    (bijective_of_involutive (onSet_involutive f D hinv hclosed))

noncomputable def offSetEquiv
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) : Fin G ≃ Fin G :=
  Equiv.ofBijective (offSet f D)
    (bijective_of_involutive (offSet_involutive f D hinv hclosed))

@[simp] theorem onSetEquiv_apply
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) (x : Fin G) :
    onSetEquiv f D hinv hclosed x = onSet f D x := rfl

@[simp] theorem offSetEquiv_apply
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) (x : Fin G) :
    offSetEquiv f D hinv hclosed x = offSet f D x := rfl

theorem split_apply
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) (x : Fin G) :
    f x =
      onSetEquiv f D hinv hclosed
        (offSetEquiv f D hinv hclosed x) := by
  by_cases hx : x ∈ D
  · simp [onSet, offSet, hx]
  · have hfx : f x ∉ D := by
      intro h
      exact hx ((hclosed x).mpr h)
    simp [onSet, offSet, hx, hfx]

theorem commute_apply
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D) (x : Fin G) :
    onSetEquiv f D hinv hclosed (offSetEquiv f D hinv hclosed x) =
      offSetEquiv f D hinv hclosed (onSetEquiv f D hinv hclosed x) := by
  by_cases hx : x ∈ D
  · have hfx : f x ∈ D := (hclosed x).mp hx
    simp [onSet, offSet, hx, hfx]
  · have hfx : f x ∉ D := by
      intro h
      exact hx ((hclosed x).mpr h)
    simp [onSet, offSet, hx, hfx]

theorem offSet_fixes
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D)
    {x : Fin G} (hx : x ∈ D) :
    offSetEquiv f D hinv hclosed x = x := by
  simp [offSet, hx]

theorem offSet_agrees
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D)
    {x : Fin G} (hx : x ∉ D) :
    offSetEquiv f D hinv hclosed x = f x := by
  simp [offSet, hx]

theorem onSet_preserves
    {β : Type} (lab : Fin G → β)
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D)
    (hf : ∀ x, lab (f x) = lab x) :
    ∀ x, lab (onSetEquiv f D hinv hclosed x) = lab x := by
  intro x
  by_cases hx : x ∈ D
  · simpa [onSet, hx] using hf x
  · simp [onSet, hx]

theorem offSet_preserves
    {β : Type} (lab : Fin G → β)
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D)
    (hf : ∀ x, lab (f x) = lab x) :
    ∀ x, lab (offSetEquiv f D hinv hclosed x) = lab x := by
  intro x
  by_cases hx : x ∈ D
  · simp [offSet, hx]
  · simpa [offSet, hx] using hf x

theorem offSet_support
    (f : Fin G → Fin G) (D : Finset (Fin G))
    (hinv : ∀ x, f (f x) = x)
    (hclosed : ∀ x, x ∈ D ↔ f x ∈ D)
    (hmoved : ∀ x, x ∈ D → f x ≠ x) :
    Support (offSetEquiv f D hinv hclosed) = Support f \ D := by
  apply support_eq_sdiff_of_delete
  · intro x hx
    exact offSet_fixes f D hinv hclosed hx
  · intro x hx
    exact offSet_agrees f D hinv hclosed hx
  · exact hmoved

end AssemblyP1.Issue94InvolutionSplit
