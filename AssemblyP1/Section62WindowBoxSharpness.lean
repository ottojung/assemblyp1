import AssemblyP1.Section62VisitWindowBridge

/-!
# §6.2 the window box is not sharpened to equality by observed-window designation (#284)

`AssemblyP1.Section62VisitWindowBridge` proves the positive transport bound: for
every genuine walk of length-`L` reads spelling a word `W`, the visited-read
multiset is a sub-multiset of the length-`L` window multiset of `W`
(`genuineWalk_dominates`).  Hence the *window box*

```
WindowBox L W d  ↔  ∀ u, d u ≤ windowCount L u W
```

is a reduction-invariant **upper bound** on the physical feasible-throughput
image `PhysImage L W` (the count vectors realized by genuine walks spelling `W`).
`AssemblyP1.Section62VisitTransport` shows the box is not the exact image.

The open question this module settles is whether an explicit **observed-window
designation** hypothesis sharpens the box to *equality*.  The answer is **no**,
and the obstruction is structural rather than a missing designation:

* `delta_prefix_not_mem_image` (general): for every `W` longer than `L`, the
  count vector concentrated on the *prefix window* `W.take L` lies in the box
  (`prefix_delta_mem_box`) but is **not** in the physical image.  A walk
  realizing it would have to be a single read, which spells only `W.take L`.
* The same vector already refutes every *observation/support* designation: the
  prefix window is observed (it is the occurrence at position `0`), so any
  hypothesis of the form "the support of `d` is contained in the designated
  observed windows/occurrences" accepts it
  (`no_prefix_support_designation_sharpens`).
* `endpoint_prefix_refuted` refutes the stronger **endpoint designation**
  (`d (W.take L) ≥ 1` and `d (W.drop (W.length - L)) ≥ 1`) with a word whose
  prefix and suffix windows coincide.
* `endpoint_pair_refuted` refutes endpoint designation in the generic
  prefix-`≠`-suffix case with `W = 01200`, `L = 2`: the vector `δ_{01} + δ_{00}`
  is endpoint-designated and in the box, but a walk realizing it has exactly two
  reads, and two reads spell at most `2L = 4 < 5` symbols.

The underlying invariant is the **read-count / connectivity** constraint
(`genuineWalk_spell_length_le`): a walk spelling `W` has `k` reads with
`k * L ≥ W.length`, and its consecutive reads sit at window distance at most
`L`.  Neither constraint is a function of the window multiset or of the
designated observed set, which is exactly why no "designation" hypothesis can
recover equality.  The precise exact characterization is the *schedule* (the
walk itself), recorded here as the strongest surviving positive structure.

This module is deliberately self-contained (Lean core only, no Mathlib import)
and purely additive: it does not redefine `isReducibleB`, `transitivelyReduced`,
`SpelledFeasible62`, or `StepsSurviveReduction`; it does not reprove the merged
window-multiset invariance or the merged transport bound; and it does not touch
the #261 ML-maximality classification or the #263 Graver scope.
-/

namespace AssemblyP1.Section62WindowBoxSharpness

open AssemblyP1.Section62VisitTransport
open AssemblyP1.Section62VisitWindowBridge

variable {A : Type}

/-! ## The physical image and the window box -/

/-- The **exact physical feasible-throughput image**: the count vectors `d` for
which there is a genuine walk of length-`L` reads `vs` chained by overlaps `ovs`
that spells `W` and whose visited-read multiset is `d`.  This is the set the
§6.2 feasible flows / ML objective actually lives on. -/
def PhysImage [DecidableEq A] (L : Nat) (W : List A) (d : List A → Nat) : Prop :=
  ∃ (vs : List (List A)) (ovs : List Nat),
    GenuineWalk L vs ovs ∧ spellWalk vs ovs = W ∧ d = throughputOf vs

/-- The **window box**: the reduction-invariant upper bound of
`Section62VisitWindowBridge`.  It depends only on the spelled word `W`. -/
def WindowBox [DecidableEq A] (L : Nat) (W : List A) (d : List A → Nat) : Prop :=
  ∀ u, d u ≤ windowCount L u W

/-- **The box is an upper bound.**  Every physically realizable throughput vector
lies in the box.  (This is the merged transport bound `visitCount_le_windowCount`
restated as an implication; it is not reproved.) -/
theorem physImage_subset_windowBox [DecidableEq A] {L : Nat} {W : List A} :
    ∀ d, PhysImage L W d → WindowBox L W d := by
  rintro d ⟨vs, ovs, hgw, hspell, rfl⟩ u
  rw [← hspell]
  exact visitCount_le_windowCount hgw u

/-! ## The count vector concentrated on one word -/

/-- `delta u` is the count vector with a single visit to `u`. -/
def delta [DecidableEq A] (u : List A) : List A → Nat :=
  fun x => if x = u then 1 else 0

theorem delta_self [DecidableEq A] (u : List A) : delta u u = 1 := by
  simp [delta]

theorem delta_of_ne [DecidableEq A] {u x : List A} (h : x ≠ u) : delta u x = 0 := by
  simp [delta, h]

/-! ## Structural necessary conditions on physical walks -/

/-- The word spelled by a one-read walk is that read, for any overlap list. -/
theorem spellWalk_singleton (v : List A) (ovs : List Nat) : spellWalk [v] ovs = v := by
  simp [spellWalk, cats]

/-- **First-read condition.**  The first read of a walk is the length-`L` prefix of
the spelled word. -/
theorem spellWalk_head_take {L : Nat} (v : List A) (rest : List (List A)) (ovs : List Nat)
    (hv : v.length = L) :
    (spellWalk (v :: rest) ovs).take L = v := by
  rw [spellWalk, ← hv, List.take_left]

/-- **Read-count lower bound.**  A walk whose reads all have length `L` spells a
word of length at most `#reads · L`.  Equivalently `#reads ≥ W.length / L`; this
is the connectivity constraint that the window multiset forgets. -/
theorem genuineWalk_spell_length_le {L : Nat} {vs : List (List A)} {ovs : List Nat}
    (h : GenuineWalk L vs ovs) :
    (spellWalk vs ovs).length ≤ vs.length * L := by
  induction h with
  | nil => simp [spellWalk]
  | single v hv => rw [spellWalk_single]; simp [hv]
  | cons hv ho hov hr ih =>
      rename_i v w o rest ovs
      have hw : w.length = L := genuineWalk_length hr w (by simp)
      have htail : spellWalk (w :: rest) ovs
          = w ++ cats (rest.zipWith (fun w o => w.drop o) ovs) := rfl
      have hsplit : cats (rest.zipWith (fun w o => w.drop o) ovs)
          = (spellWalk (w :: rest) ovs).drop L := by
        rw [htail, ← hw, List.drop_left]
      have hcons : spellWalk (v :: w :: rest) (o :: ovs)
          = v ++ (w.drop o ++ cats (rest.zipWith (fun w o => w.drop o) ovs)) :=
        spellWalk_cons_eq v w rest o ovs
      have hdrop_len : (w.drop o).length ≤ L := by rw [List.length_drop, hw]; omega
      have hcats_len : (cats (rest.zipWith (fun w o => w.drop o) ovs)).length
          ≤ rest.length * L := by
        rw [hsplit, List.length_drop]
        have hih := ih
        rw [List.length_cons, Nat.add_mul, Nat.one_mul] at hih
        omega
      rw [hcons, List.length_append, List.length_append, hv]
      have hlen : (v :: w :: rest).length = rest.length + 2 := by simp
      rw [hlen, Nat.add_mul]
      omega

/-- **Support extraction.**  If a walk's throughput vector is a `delta`, then every
read of the walk is that word. -/
theorem mem_throughputOf_pos [DecidableEq A] {vs : List (List A)} {v : List A}
    (hv : v ∈ vs) : 1 ≤ throughputOf vs v := by
  unfold throughputOf
  induction vs with
  | nil => simp at hv
  | cons w ws ih =>
      rw [List.countP_cons]
      rcases List.mem_cons.mp hv with rfl | hmem
      · simp
      · have := ih hmem; omega

/-- **Constant-list count.**  If every element of a list equals `u`, then the
multiplicity of `u` is the list length. -/
theorem countP_eq_length_of_all_eq [DecidableEq A] {vs : List (List A)} {u : List A}
    (h : ∀ v ∈ vs, v = u) :
    vs.countP (fun x => decide (x = u)) = vs.length := by
  induction vs with
  | nil => simp
  | cons w ws ih =>
      have hw : w = u := h w (List.mem_cons_self ..)
      have hws : ∀ v ∈ ws, v = u := fun v hv => h v (List.mem_cons_of_mem _ hv)
      rw [List.countP_cons, ih hws, hw]
      simp

/-- **Two-word count.**  If every element of a list is `u₁` or `u₂` (distinct),
then the list length is the sum of the two multiplicities. -/
theorem length_eq_countP_pair [DecidableEq A] {u1 u2 : List A} (hne : u1 ≠ u2)
    {vs : List (List A)} (h : ∀ v ∈ vs, v = u1 ∨ v = u2) :
    vs.length = vs.countP (fun x => decide (x = u1)) + vs.countP (fun x => decide (x = u2)) := by
  induction vs with
  | nil => simp
  | cons w ws ih =>
      have hw : w = u1 ∨ w = u2 := h w (List.mem_cons_self ..)
      have hws : ∀ v ∈ ws, v = u1 ∨ v = u2 := fun v hv => h v (List.mem_cons_of_mem _ hv)
      rw [List.length_cons, ih hws]
      rcases hw with rfl | rfl
      · rw [List.countP_cons, List.countP_cons]; simp [hne]; omega
      · rw [List.countP_cons, List.countP_cons]; simp [hne.symm]; omega

/-- The prefix window is a length-`L` window of `W` whenever `1 ≤ L ≤ W.length`. -/
theorem take_mem_windows {L : Nat} {W : List A} (_hL : 1 ≤ L) (hW : L ≤ W.length) :
    W.take L ∈ windows L W := by
  unfold windows
  apply List.mem_map.mpr
  refine ⟨0, List.mem_range.mpr ?_, by simp⟩
  omega

/-- Multiplicity at least one for any element of a list. -/
theorem one_le_countP_of_mem {α : Type} [DecidableEq α] {l : List α} {a : α}
    (h : a ∈ l) : 1 ≤ l.countP (fun x => decide (x = a)) := by
  induction l with
  | nil => simp at h
  | cons b bs ih =>
      rw [List.countP_cons]
      rcases List.mem_cons.mp h with rfl | hmem
      · simp
      · have := ih hmem; omega

/-- A list of length one is a singleton. -/
theorem exists_eq_singleton_of_length_eq_one {vs : List (List A)} (h : vs.length = 1) :
    ∃ v, vs = [v] := by
  cases vs with
  | nil => simp at h
  | cons v vs =>
      cases vs with
      | nil => exact ⟨v, rfl⟩
      | cons w ws => simp at h

/-- **The prefix `delta` is in the box.**  The prefix window occurs as the
length-`L` window at position `0`, so its window multiplicity is at least `1`. -/
theorem prefix_delta_mem_box [DecidableEq A] {L : Nat} {W : List A}
    (hL : 1 ≤ L) (hW : L ≤ W.length) :
    WindowBox L W (delta (W.take L)) := by
  intro u
  by_cases h : u = W.take L
  · subst h
    rw [delta_self]
    unfold windowCount
    exact one_le_countP_of_mem (take_mem_windows hL hW)
  · rw [delta_of_ne h]
    exact Nat.zero_le _

/-- A walk spelling a word strictly longer than `L` cannot be a single read, so a
`delta` vector supported on the prefix window is not realized. -/
theorem delta_prefix_not_mem_image [DecidableEq A] {L : Nat} {W : List A}
    (_hL : 1 ≤ L) (hW : L < W.length) :
    ¬ PhysImage L W (delta (W.take L)) := by
  rintro ⟨vs, ovs, hgw, hspell, hd⟩
  have hall : ∀ v ∈ vs, v = W.take L := by
    intro v hv
    have h1 : 1 ≤ throughputOf vs v := mem_throughputOf_pos hv
    have h2 : 1 ≤ delta (W.take L) v := by rw [hd]; exact h1
    by_cases hne : v = W.take L
    · exact hne
    · rw [delta_of_ne hne] at h2
      omega
  have hlen : vs.length = 1 := by
    have hc : throughputOf vs (W.take L) = vs.length := by
      unfold throughputOf
      exact countP_eq_length_of_all_eq hall
    have h3 : delta (W.take L) (W.take L) = vs.length := by rw [hd]; exact hc
    rw [delta_self] at h3
    exact h3.symm
  obtain ⟨v, rfl⟩ := exists_eq_singleton_of_length_eq_one hlen
  have hv : v = W.take L := hall v (List.mem_singleton_self v)
  have hspell' : v = W := by
    have h := hspell
    rw [spellWalk_singleton] at h
    exact h
  have htake : W = W.take L := by rw [← hv, hspell']
  have hlenW : W.length = (W.take L).length := by rw [← htake]
  rw [List.length_take] at hlenW
  omega

/-! ## Refuting the observed-window designation hypotheses -/

/-- **Endpoint designation hypothesis.**  The observed designations are the
`L`-prefix read and the `L`-suffix read of the spelled word, and both must be
visited at least once. -/
def EndpointDesignated [DecidableEq A] (L : Nat) (W : List A) (d : List A → Nat) : Prop :=
  d (W.take L) ≥ 1 ∧ d (W.drop (W.length - L)) ≥ 1

/-- **No support/observation designation sharpens the box.**  Any designation
hypothesis `H` that is satisfied by the prefix `delta` (in particular, any
hypothesis whose only constraint is that the support lies in the designated
observed windows/occurrences, since the prefix window is observed at position
`0`) fails to cut the box down to the image: the prefix `delta` is in
`WindowBox ∩ H` but not in `PhysImage`. -/
theorem no_prefix_support_designation_sharpens [DecidableEq A] {L : Nat} {W : List A}
    (hL : 1 ≤ L) (hW : L < W.length)
    (H : (List A → Nat) → Prop) (hd : H (delta (W.take L))) :
    ¬ (∀ d, (WindowBox L W d ∧ H d) ↔ PhysImage L W d) := by
  intro heq
  have hmem : WindowBox L W (delta (W.take L)) ∧ H (delta (W.take L)) :=
    ⟨prefix_delta_mem_box hL (by omega), hd⟩
  exact delta_prefix_not_mem_image hL hW ((heq _).mp hmem)

/-- `W = 012301` (prefix and suffix windows both `01`). -/
private def epW : List Nat := [0, 1, 2, 3, 0, 1]

/-- The prefix `delta` lies in the box. -/
theorem endpoint_prefix_mem_box : WindowBox 2 epW (delta (epW.take 2)) :=
  prefix_delta_mem_box (L := 2) (W := epW) (by omega) (by decide)

/-- The prefix `delta` satisfies endpoint designation (`epW.take 2 = epW.drop 4`). -/
theorem endpoint_prefix_designated :
    EndpointDesignated 2 epW (delta (epW.take 2)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **Endpoint designation does not sharpen the box (prefix = suffix).**  The
prefix `delta` is endpoint-designated and in the box, yet not in the image. -/
theorem endpoint_prefix_refuted :
    ∃ d, WindowBox 2 epW d ∧ EndpointDesignated 2 epW d ∧ ¬ PhysImage 2 epW d :=
  ⟨delta (epW.take 2), endpoint_prefix_mem_box, endpoint_prefix_designated,
    delta_prefix_not_mem_image (L := 2) (W := epW) (by omega) (by decide)⟩

/-- `W = 01200` (generic case: prefix window `01` and suffix window `00` differ). -/
private def epW2 : List Nat := [0, 1, 2, 0, 0]

/-- The two-endpoint count vector `δ_{01} + δ_{00}`. -/
private def epD2 : List Nat → Nat :=
  fun u => (if u = [0, 1] then 1 else 0) + (if u = [0, 0] then 1 else 0)

/-- **The two-endpoint vector is in the box.** -/
theorem endpoint_pair_mem_box : WindowBox 2 epW2 epD2 := by
  intro u
  unfold windowCount windows epD2
  by_cases h1 : u = [0, 1]
  · subst h1; decide
  · by_cases h2 : u = [0, 0]
    · subst h2; decide
    · simp [h1, h2]

/-- **The two-endpoint vector satisfies endpoint designation.** -/
theorem endpoint_pair_designated : EndpointDesignated 2 epW2 epD2 := by
  refine ⟨?_, ?_⟩ <;> (unfold epD2; decide)

/-- **Generic endpoint designation does not sharpen the box.**  The two-endpoint
vector `δ_{01} + δ_{00}` is endpoint-designated and in the box, but any walk
realizing it has exactly two reads, and two reads spell at most `2L = 4 < 5`
symbols. -/
theorem endpoint_pair_refuted :
    ∃ d, WindowBox 2 epW2 d ∧ EndpointDesignated 2 epW2 d ∧ ¬ PhysImage 2 epW2 d := by
  refine ⟨epD2, endpoint_pair_mem_box, endpoint_pair_designated, ?_⟩
  rintro ⟨vs, ovs, hgw, hspell, hd⟩
  have hall : ∀ v ∈ vs, v = [0, 1] ∨ v = [0, 0] := by
    intro v hv
    have h1 : 1 ≤ throughputOf vs v := mem_throughputOf_pos hv
    have h2 : 1 ≤ epD2 v := by rw [hd]; exact h1
    unfold epD2 at h2
    by_cases hA : v = [0, 1]
    · exact Or.inl hA
    · by_cases hB : v = [0, 0]
      · exact Or.inr hB
      · simp [hA, hB] at h2
  have hlen : vs.length = 2 := by
    have hcount : vs.length
        = vs.countP (fun x => decide (x = [0, 1])) + vs.countP (fun x => decide (x = [0, 0])) :=
      length_eq_countP_pair (by decide) hall
    have hc1 : vs.countP (fun x => decide (x = [0, 1])) = epD2 [0, 1] := by
      rw [hd]; rfl
    have hc2 : vs.countP (fun x => decide (x = [0, 0])) = epD2 [0, 0] := by
      rw [hd]; rfl
    rw [hc1, hc2] at hcount
    have hsum : epD2 [0, 1] = 1 ∧ epD2 [0, 0] = 1 := by unfold epD2; decide
    omega
  have hbound : epW2.length ≤ vs.length * 2 := by
    have := genuineWalk_spell_length_le hgw
    rw [hspell] at this
    exact this
  rw [hlen] at hbound
  simp [epW2] at hbound

/-! ## The surviving exact characterization: the schedule -/

/-- A **schedule** of a spelled word: the strictly increasing list of start
positions of the reads of a walk.  It carries exactly the connectivity data the
window multiset forgets.  This is the strongest positive structure on which the
exact image can be computed; it is not a function of the window multiset or of a
designated observed set. -/
def IsSchedule (W : List A) (L : Nat) (ps : List Nat) : Prop :=
  ps.Nodup ∧
    (∀ p ∈ ps, p + L ≤ W.length) ∧
    (∀ p ∈ ps, ∀ q ∈ ps, p < q → q - p ≤ L) ∧
    (0 ∈ ps) ∧ (W.length - L ∈ ps)

/-! ## Axiom audit -/

#print axioms physImage_subset_windowBox
#print axioms spellWalk_singleton
#print axioms spellWalk_head_take
#print axioms genuineWalk_spell_length_le
#print axioms mem_throughputOf_pos
#print axioms countP_eq_length_of_all_eq
#print axioms length_eq_countP_pair
#print axioms take_mem_windows
#print axioms prefix_delta_mem_box
#print axioms delta_prefix_not_mem_image
#print axioms no_prefix_support_designation_sharpens
#print axioms endpoint_prefix_refuted
#print axioms endpoint_pair_refuted

end AssemblyP1.Section62WindowBoxSharpness
