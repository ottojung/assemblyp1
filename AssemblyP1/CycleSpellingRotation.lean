import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.RepeatAdapter

/-!
# Board #243: deterministic de Bruijn support forces a cyclic rotation

Independent subgoal of #211. For two circular words `S D : Fin G → α` of the
same positive length `G`, if

* their complete oriented length-`L` spectra agree
  (`specCount hG D w = specCount hG S w` for every `w`), and
* the positive `L`-mer support of `S` has a **unique outgoing edge type** for
  every `(L-1)`-mer node (`RepeatAdapter.IsSimpleCycle L hG S`),

then `D` is a cyclic rotation of `S` (`OrientedFinal.IsCyclicShift hG D S`).

The argument is a deterministic-continuation induction:

1. equal spectra make the two window supports coincide
   (`support hG S = support hG D`), via `w ∈ support ↔ 0 < specCount w`;
2. pick a start `j` of `S` spelling `D`'s initial `L`-mer (it occurs because
   the spectra agree);
3. `hstep`: if the `L`-window of `D` at `a` equals the `L`-window of `S` at
   `b`, then their `(L-1)`-suffixes agree, so the unique outgoing edge from
   that node in `S`'s support forces the two *next* `L`-windows to agree;
4. induction on `t` gives `window hG D (t) = window hG S (j + t)`, and reading
   the first symbol gives `cyc hG D t = cyc hG S (j + t)`, i.e.
   `IsCyclicShift hG D S` with shift `j`.

This is independent of `IsPrimitive` and does **not** reprove
`periodic_factor_distinct` / `periodic_cycle_shape`; it only consumes the
`IsSimpleCycle` interface they produce. No `sorry`, no new `axiom`.
-/

namespace AssemblyP1.CycleSpellingRotation

open Finset

/-- Membership in the window support is equivalent to positive spectrum
multiplicity (no `Fintype α` needed). -/
private theorem support_iff_specCount_pos {α : Type} [DecidableEq α] {G L : ℕ}
    (hG : 0 < G) (X : Fin G → α) (w : Fin L → α) :
    w ∈ OrientedRigidity.support hG X ↔ 0 < OrientedRigidity.specCount hG X w := by
  constructor
  · intro hw
    simp only [OrientedRigidity.support, Finset.mem_image] at hw
    obtain ⟨r, _, rfl⟩ := hw
    have hmem : r ∈ Finset.univ.filter
        (fun r' : Fin G => OrientedRigidity.window (L := L) hG X r'
          = OrientedRigidity.window (L := L) hG X r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    exact Finset.card_pos.mpr ⟨r, hmem⟩
  · intro hpos
    simp only [OrientedRigidity.specCount] at hpos
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
    have hwr : OrientedRigidity.window hG X r = w := (Finset.mem_filter.mp hr).2
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hwr⟩

/-- `cyc` only depends on the residue mod `G`. -/
private theorem cyc_mod {α : Type} {G : ℕ} (hG : 0 < G) (X : Fin G → α) (x : ℕ) :
    OrientedRigidity.cyc hG X (x % G) = OrientedRigidity.cyc hG X x := by
  unfold OrientedRigidity.cyc
  apply congrArg X
  apply Fin.ext
  show x % G % G = x % G
  rw [Nat.mod_mod]

/-- Prefix of the successor window equals the suffix of the current window:
`winPrefix (window X (a+1)) = winSuffix (window X a)`, all mod `G`. -/
private theorem winPrefix_next_eq_winSuffix {α : Type} {G L : ℕ} (hG : 0 < G)
    (X : Fin G → α) (a : Fin G) :
    OrientedRigidity.winPrefix
        (OrientedRigidity.window (L := L) hG X ⟨(a.val + 1) % G, Nat.mod_lt _ hG⟩)
      = OrientedRigidity.winSuffix
        (OrientedRigidity.window (L := L) hG X a) := by
  funext d
  show OrientedRigidity.cyc hG X ((a.val + 1) % G + d.val)
    = OrientedRigidity.cyc hG X (a.val + (d.val + 1))
  unfold OrientedRigidity.cyc
  apply congrArg X
  apply Fin.ext
  show ((a.val + 1) % G + d.val) % G = (a.val + (d.val + 1)) % G
  rw [Nat.mod_add_mod (a.val + 1) G d.val]
  congr 1
  omega

/-- **Deterministic successor.** Equal `L`-windows in `D` and `S` (whose support
carries the unique-outgoing-edge property) have equal successors. -/
private theorem step_eq {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S D : Fin G → α)
    (hsup : ∀ w : Fin L → α,
      w ∈ OrientedRigidity.support hG S ↔ w ∈ OrientedRigidity.support hG D)
    (hcyc : RepeatAdapter.IsSimpleCycle L hG S) :
    ∀ a b : Fin G,
      OrientedRigidity.window (L := L) hG D a
        = OrientedRigidity.window (L := L) hG S b →
      OrientedRigidity.window (L := L) hG D ⟨(a.val + 1) % G, Nat.mod_lt _ hG⟩
        = OrientedRigidity.window (L := L) hG S ⟨(b.val + 1) % G, Nat.mod_lt _ hG⟩ := by
  intro a b hwin
  have hwS : OrientedRigidity.window (L := L) hG S b
      ∈ OrientedRigidity.support (L := L) hG S :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hnode : OrientedRigidity.winSuffix (OrientedRigidity.window (L := L) hG S b)
      ∈ OrientedRigidity.genomeNodes (L := L) hG S :=
    (OrientedRigidity.mem_nodes_of_mem_support hG S _ hwS).2
  obtain ⟨w, _, huniq⟩ := hcyc.1 _ hnode
  have hpreD : OrientedRigidity.winPrefix
      (OrientedRigidity.window (L := L) hG D ⟨(a.val + 1) % G, Nat.mod_lt _ hG⟩)
      = OrientedRigidity.winSuffix (OrientedRigidity.window (L := L) hG S b) := by
    rw [winPrefix_next_eq_winSuffix hG D a, hwin]
  have hpreS : OrientedRigidity.winPrefix
      (OrientedRigidity.window (L := L) hG S ⟨(b.val + 1) % G, Nat.mod_lt _ hG⟩)
      = OrientedRigidity.winSuffix (OrientedRigidity.window (L := L) hG S b) :=
    winPrefix_next_eq_winSuffix hG S b
  have hmemD : OrientedRigidity.window (L := L) hG D ⟨(a.val + 1) % G, Nat.mod_lt _ hG⟩
      ∈ OrientedRigidity.support (L := L) hG S :=
    (hsup _).mpr (Finset.mem_image.mpr
      ⟨⟨(a.val + 1) % G, Nat.mod_lt _ hG⟩, Finset.mem_univ _, rfl⟩)
  have hmemS : OrientedRigidity.window (L := L) hG S ⟨(b.val + 1) % G, Nat.mod_lt _ hG⟩
      ∈ OrientedRigidity.support (L := L) hG S :=
    Finset.mem_image.mpr
      ⟨⟨(b.val + 1) % G, Nat.mod_lt _ hG⟩, Finset.mem_univ _, rfl⟩
  rw [huniq _ ⟨hmemD, hpreD⟩, huniq _ ⟨hmemS, hpreS⟩]

/-- **Board #243.** Equal complete oriented `L`-spectrum plus a simple-cycle
support on `S` forces `D` to be a cyclic rotation of `S`. -/
theorem isCyclicShift_of_isSimpleCycle_specCount {α : Type} [DecidableEq α]
    {G L : ℕ} (hG : 0 < G) (hL : 2 ≤ L) (S D : Fin G → α)
    (hspec : ∀ w : Fin L → α,
      OrientedRigidity.specCount hG D w = OrientedRigidity.specCount hG S w)
    (hcyc : RepeatAdapter.IsSimpleCycle L hG S) :
    OrientedFinal.IsCyclicShift hG D S := by
  -- 1. Equal spectra ⟹ equal window supports.
  have hsup : ∀ w : Fin L → α,
      w ∈ OrientedRigidity.support hG S ↔ w ∈ OrientedRigidity.support hG D := by
    intro w
    rw [support_iff_specCount_pos hG S w, support_iff_specCount_pos hG D w,
      hspec w]
  -- 2. Pick a start `j` of `S` spelling `D`'s initial `L`-mer.
  have hD0 : OrientedRigidity.window (L := L) hG D ⟨0, hG⟩
      ∈ OrientedRigidity.support (L := L) hG D :=
    Finset.mem_image.mpr ⟨⟨0, hG⟩, Finset.mem_univ _, rfl⟩
  have hS0 : OrientedRigidity.window (L := L) hG D ⟨0, hG⟩
      ∈ OrientedRigidity.support (L := L) hG S :=
    (hsup _).mpr hD0
  simp only [OrientedRigidity.support, Finset.mem_image] at hS0
  obtain ⟨j, _, hjwindow⟩ := hS0
  -- 3. Deterministic-continuation induction.
  have hwalk : ∀ t : ℕ,
      OrientedRigidity.window (L := L) hG D ⟨t % G, Nat.mod_lt _ hG⟩
        = OrientedRigidity.window (L := L) hG S ⟨(j.val + t) % G, Nat.mod_lt _ hG⟩ := by
    intro t
    induction t with
    | zero =>
        have e1 : (⟨0 % G, Nat.mod_lt _ hG⟩ : Fin G) = ⟨0, hG⟩ := by
          ext; simp
        have e2 : (⟨(j.val + 0) % G, Nat.mod_lt _ hG⟩ : Fin G) = j := by
          apply Fin.ext
          show (j.val + 0) % G = j.val
          rw [Nat.add_zero, Nat.mod_eq_of_lt j.isLt]
        rw [e1, e2]
        exact hjwindow.symm
    | succ t ih =>
        have eD : (⟨(t + 1) % G, Nat.mod_lt _ hG⟩ : Fin G)
            = ⟨(t % G + 1) % G, Nat.mod_lt _ hG⟩ := by
          apply Fin.ext
          exact (Nat.mod_add_mod t G 1).symm
        have eS : (⟨(j.val + (t + 1)) % G, Nat.mod_lt _ hG⟩ : Fin G)
            = ⟨((j.val + t) % G + 1) % G, Nat.mod_lt _ hG⟩ := by
          apply Fin.ext
          rw [show j.val + (t + 1) = j.val + t + 1 from by omega]
          exact (Nat.mod_add_mod (j.val + t) G 1).symm
        rw [eD, eS]
        exact step_eq hG S D hsup hcyc _ _ ih
  -- 4. Read the first symbol of each window.
  refine ⟨j.val, fun i => ?_⟩
  have key : OrientedRigidity.cyc hG D i
      = OrientedRigidity.cyc hG S (j.val + i) := by
    have h := congrFun (hwalk i) (⟨0, by omega⟩ : Fin L)
    have e1 : OrientedRigidity.cyc hG D (i % G + 0) = OrientedRigidity.cyc hG D i := by
      rw [Nat.add_zero]
      exact cyc_mod hG D i
    have e2 : OrientedRigidity.cyc hG S ((j.val + i) % G + 0)
        = OrientedRigidity.cyc hG S (j.val + i) := by
      rw [Nat.add_zero]
      exact cyc_mod hG S (j.val + i)
    exact e1.symm.trans (h.trans e2)
  rw [key, Nat.add_comm]

#print axioms isCyclicShift_of_isSimpleCycle_specCount

end AssemblyP1.CycleSpellingRotation
