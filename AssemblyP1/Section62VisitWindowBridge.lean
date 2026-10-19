import AssemblyP1.Section62VisitTransport

/-!
# §6.2 read-window multiset bounds physical visits (#284)

`AssemblyP1.Section62VisitTransport` records the exact obstruction on the
physical visit-count transport for the corrected spelling-preserving §6.2
transitive reduction: the *full* length-`L` window multiset of a spelled word is
invariant under the reduction, but it does **not** determine the multiset of
vertices (observed read molecules) visited by a walk, because the spelled word
has *unobserved seam windows*.

This module supplies the complementary **positive** half of that transport, which
is the useful one for the §6.2 feasible-flow / ML objective: the invariant window
multiset *dominates* the physical visit counts.

* `GenuineWalk` is the explicit walk hypothesis: consecutive length-`L` reads
  chained by genuine proper suffix/prefix overlaps.
* `genuineWalk_dominates` (the main theorem): for every such walk, the multiset of
  visited read words is a sub-multiset of the length-`L` window multiset of the
  spelled word.  Equivalently, for every read `u`,
  `throughputOf vs u ≤ windowCount L u (spellWalk vs ovs)`.
* `visitCount_le_windowCount` states this per read, in the vocabulary of the §6.2
  vertex throughput (`Section62Flow.throughput` / `Spelling.visits`, identified
  with the submolecule count by MB09 Observation 7).
* `windowCount_congr` / `windowCount_detour_eq` transfer the bound along the
  spelling-preserving reduction: since the reduction preserves the spelled word,
  it preserves the window multiset, hence the *upper bound* on the throughput is
  invariant even though the throughput itself is not.
* The `L = 5` witness `witness_bound_strict` shows the bound is not tight: the
  seam window `34120` has window multiplicity `1` but visit count `0`.  So the
  window multiset is a genuine, computable, reduction-invariant **upper bound** on
  the §6.2 throughput, and the residual gap is exactly the unobserved seam
  windows — the additional structure a faithful *equality* transport would need.

This module is deliberately self-contained (Lean core only, no Mathlib import) so
that the transport bound stands independently of the heavy §6.2 chain.  It adds
new definitions and theorems only; it does not redefine `isReducibleB`,
`transitivelyReduced`, `SpelledFeasible62`, or `StepsSurviveReduction`, it does
not reprove any merged §6.2 theorem, and it does not touch the #261 ML-maximality
classification or the #263 Graver scope.
-/

namespace AssemblyP1.Section62VisitWindowBridge

open AssemblyP1.Section62VisitTransport

variable {A : Type}

/-! ## The genuine-overlap walk hypothesis -/

/-- A walk of observed reads `vs` chained by genuine proper overlaps `ovs`.

`vs = [v₀, v₁, …, vₙ₋₁]` and `ovs = [o₀, …, oₙ₋₂]`, where `oᵢ < L` is the
overlap length from `vᵢ` to `vᵢ₊₁`: the `oᵢ`-length suffix of `vᵢ` is the
`oᵢ`-length prefix of `vᵢ₊₁`, i.e. `vᵢ.drop (L − oᵢ) = vᵢ₊₁.take oᵢ`.  Every read
has length `L` (derived in `genuineWalk_length`).  This is the walk object of
`Section62VisitTransport.spellWalk`, with the overlap compatibility made
explicit. -/
inductive GenuineWalk (L : Nat) : List (List A) → List Nat → Prop where
  | nil : GenuineWalk L [] []
  | single (v : List A) : v.length = L → GenuineWalk L [v] []
  | cons {v w : List A} {o : Nat} {rest : List (List A)} {ovs : List Nat}
      (hv : v.length = L) (ho : o < L) (hov : v.drop (L - o) = w.take o)
      (hr : GenuineWalk L (w :: rest) ovs) :
      GenuineWalk L (v :: w :: rest) (o :: ovs)

/-- Every read of a genuine walk has the common read length `L`. -/
theorem genuineWalk_length {L : Nat} {vs : List (List A)} {ovs : List Nat}
    (h : GenuineWalk L vs ovs) : ∀ v ∈ vs, v.length = L := by
  induction h with
  | nil => intro v hv; simp at hv
  | single v hv => intro u hu; simp at hu; subst hu; exact hv
  | cons hv ho hov hr ih =>
      rename_i v w o rest ovs
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hv
      · exact ih u hu

/-! ## Spelling and window algebra -/

/-- The spelled word of a two-or-more read walk, as the first read followed by
the extensions of the rest. -/
theorem spellWalk_cons_eq (v w : List A) (rest : List (List A)) (o : Nat)
    (ovs : List Nat) :
    spellWalk (v :: w :: rest) (o :: ovs)
      = v ++ (w.drop o ++ cats (rest.zipWith (fun w o => w.drop o) ovs)) := by
  simp [spellWalk, List.zipWith_cons_cons, cats]

/-- The one-read walk spells that read. -/
theorem spellWalk_single (v : List A) : spellWalk [v] [] = v := by
  simp [spellWalk, cats]

/-- **The reduction step at the word level.**  A genuine overlap of length `o`
between two length-`L` reads makes the tail spelling a suffix of the full
spelling: dropping the first read's `L − o` remaining positions leaves exactly
the tail spelling.  This is the invariant the window bound is built on. -/
theorem spellWalk_cons_drop {L o : Nat} {v w : List A} {rest : List (List A)}
    {ovs : List Nat}
    (hv : v.length = L) (hw : w.length = L) (ho : o ≤ L)
    (hov : v.drop (L - o) = w.take o) :
    (spellWalk (v :: w :: rest) (o :: ovs)).drop (L - o) = spellWalk (w :: rest) ovs := by
  have hw' : (w.drop o).length = L - o := by rw [List.length_drop, hw]
  rw [spellWalk_cons_eq]
  rw [← List.append_assoc]
  have hle : L - o ≤ (v ++ w.drop o).length := by
    rw [List.length_append, hv, hw']; omega
  rw [List.drop_append_of_le_length hle]
  have hstep : (v ++ w.drop o).drop (L - o) = w := by
    rw [List.drop_append_of_le_length (by rw [hv]; omega)]
    rw [hov, List.take_append_drop]
  rw [hstep]
  rw [spellWalk]

/-- Splitting the length-`L` windows of a word at an offset `c`: the windows whose
start is below `c`, followed by the windows of the `c`-suffix. -/
theorem windows_eq_append_windows_drop {L : Nat} (W : List A) (c : Nat)
    (hL : 1 ≤ L) (hc : c ≤ W.length + 1 - L) :
    windows L W =
      (List.range c).map (fun i => (W.drop i).take L) ++ windows L (W.drop c) := by
  unfold windows
  have hcn : c ≤ W.length + 1 - L := hc
  have hcW : c ≤ W.length := by omega
  have hsplit : List.range (W.length + 1 - L) =
      List.range c ++ List.map (fun x => c + x) (List.range (W.length + 1 - L - c)) := by
    have h := List.range_add (n := c) (m := W.length + 1 - L - c)
    rw [Nat.add_sub_of_le hcn] at h
    exact h
  rw [hsplit, List.map_append]
  congr 1
  rw [List.map_map]
  have hlen : W.length + 1 - L - c = (W.drop c).length + 1 - L := by
    rw [List.length_drop]; omega
  rw [hlen]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply]
  have : W.drop (c + i) = (W.drop c).drop i := by
    rw [List.drop_drop]
  rw [this]

/-- **The window decomposition at a genuine walk step.**  The length-`L` windows
of the spelled word split into the `L − o` windows that start inside the first
read's remaining positions (the first of which is the first read itself), followed
by the windows of the tail spelling. -/
theorem windows_spellWalk_cons {L o : Nat} {v w : List A} {rest : List (List A)}
    {ovs : List Nat}
    (hv : v.length = L) (hw : w.length = L) (ho : o < L)
    (hov : v.drop (L - o) = w.take o) :
    windows L (spellWalk (v :: w :: rest) (o :: ovs)) =
      (List.range (L - o)).map
          (fun i => ((spellWalk (v :: w :: rest) (o :: ovs)).drop i).take L)
        ++ windows L (spellWalk (w :: rest) ovs) := by
  have hL : 1 ≤ L := by omega
  have hWlen : (spellWalk (v :: w :: rest) (o :: ovs)).length
      = L + (L - o) + (cats (rest.zipWith (fun w o => w.drop o) ovs)).length := by
    rw [spellWalk_cons_eq]
    simp only [List.length_append, List.length_drop, hv, hw]
    omega
  have hc : L - o ≤ (spellWalk (v :: w :: rest) (o :: ovs)).length + 1 - L := by
    rw [hWlen]; omega
  rw [windows_eq_append_windows_drop _ (L - o) hL hc]
  rw [spellWalk_cons_drop hv hw (by omega) hov]

/-- A length-`L` read is the unique length-`L` window of itself. -/
theorem windows_self {L : Nat} (v : List A) (hv : v.length = L) :
    windows L v = [v] := by
  unfold windows
  rw [hv, show L + 1 - L = 1 from by omega, List.range_one]
  simp only [List.map_cons, List.map_nil, List.drop_zero]
  rw [← hv, List.take_length]

/-! ## Multiset domination -/

/-- `Dominates l₁ l₂` means every word occurs in `l₁` no more often than in `l₂`
(with multiplicity).  This is the sub-multiset order on lists, phrased with
`List.countP` to avoid the `BEq`/`DecidableEq` diamond. -/
def Dominates [DecidableEq A] (l₁ l₂ : List (List A)) : Prop :=
  ∀ u, l₁.countP (fun x => decide (x = u)) ≤ l₂.countP (fun x => decide (x = u))

theorem dominates_refl [DecidableEq A] (l : List (List A)) : Dominates l l :=
  fun _ => Nat.le_refl _

theorem dominates_append_right [DecidableEq A] {l₁ l₂ l₃ : List (List A)}
    (h : Dominates l₁ l₂) : Dominates l₁ (l₂ ++ l₃) := by
  intro u
  rw [List.countP_append]
  exact Nat.le_trans (h u) (Nat.le_add_right _ _)

theorem dominates_cons [DecidableEq A] {l₁ l₂ : List (List A)} (a : List A)
    (h : Dominates l₁ l₂) : Dominates (a :: l₁) (a :: l₂) := by
  intro u
  rw [List.countP_cons, List.countP_cons]
  exact Nat.add_le_add_right (h u) _

/-- Splitting a range map at its head, used to expose the first read as the
offset-zero window. -/
theorem map_range_head {n : Nat} (hn : 1 ≤ n) (f : Nat → List A) (v : List A)
    (h0 : f 0 = v) :
    (List.range n).map f = v :: (List.range (n - 1)).map (fun i => f (i + 1)) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  subst hm
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, h0]
  congr 1

/-! ## The main theorem: the window multiset dominates the visited reads -/

/-- **Window multiset dominates physical visits.**  For any walk of length-`L`
reads chained by genuine proper overlaps, the multiset of visited read words is a
sub-multiset of the length-`L` window multiset of the spelled word.

The proof is the induction that follows the reduction: at each step the tail
walk's spelling is a suffix of the full spelling (`spellWalk_cons_drop`), so the
tail's windows are windows of the full spelling (`windows_spellWalk_cons`), while
the offset-zero window is the head read.  Only the head read is *added*, never
removed, so no visited read is lost. -/
theorem genuineWalk_dominates [DecidableEq A] {L : Nat} {vs : List (List A)}
    {ovs : List Nat} (h : GenuineWalk L vs ovs) :
    Dominates vs (windows L (spellWalk vs ovs)) := by
  induction h with
  | nil => intro u; simp [windows]
  | single v hv =>
      intro u
      rw [spellWalk_single, windows_self v hv]
      exact dominates_refl [v] u
  | cons hv ho hov hr ih =>
      rename_i v w o rest ovs
      have hw : w.length = L := genuineWalk_length hr w (by simp)
      have h0 : (fun i => ((spellWalk (v :: w :: rest) (o :: ovs)).drop i).take L) 0 = v := by
        simp only [List.drop_zero]
        rw [spellWalk_cons_eq, ← hv, List.take_left]
      have hpre : (List.range (L - o)).map
            (fun i => ((spellWalk (v :: w :: rest) (o :: ovs)).drop i).take L)
          = v :: (List.range (L - o - 1)).map
              (fun i => ((spellWalk (v :: w :: rest) (o :: ovs)).drop (i + 1)).take L) :=
        map_range_head (by omega) _ v h0
      intro u
      have hdec : (v :: w :: rest).countP (fun x => decide (x = u))
          = (w :: rest).countP (fun x => decide (x = u))
            + (if decide (v = u) = true then 1 else 0) := List.countP_cons
      have hwin : (windows L (spellWalk (v :: w :: rest) (o :: ovs))).countP
              (fun x => decide (x = u))
          = ((List.range (L - o - 1)).map
                (fun i => ((spellWalk (v :: w :: rest) (o :: ovs)).drop (i + 1)).take L)).countP
                (fun x => decide (x = u))
            + (if decide (v = u) = true then 1 else 0)
            + (windows L (spellWalk (w :: rest) ovs)).countP (fun x => decide (x = u)) := by
        rw [windows_spellWalk_cons hv hw ho hov, hpre, List.countP_append, List.countP_cons]
      rw [hdec, hwin]
      have := ih u
      omega

/-! ## The §6.2 vertex-throughput corollary -/

/-- The §6.2 vertex throughput of a candidate whose cyclic walk visits the read
words `vs`: the number of walk positions whose read word is `u`.  This is exactly
`Section62Flow.Spelling.visits` (Observation 7 identifies it with the submolecule
count), stated here on the bare list of visited reads. -/
def throughputOf [DecidableEq A] (vs : List (List A)) (u : List A) : Nat :=
  vs.countP (fun x => decide (x = u))

/-- The length-`L` window multiplicity of the read word `u` in the spelled word
`w`.  This is a function of `w` alone, hence invariant under any reduction that
preserves the spelled word. -/
def windowCount [DecidableEq A] (L : Nat) (u w : List A) : Nat :=
  (windows L w).countP (fun x => decide (x = u))

/-- **The transport bound.**  The physical visit count of any read is at most its
length-`L` window multiplicity in the spelled word.  Since `windowCount` is a
function of the spelled word, the right-hand side is invariant under the
spelling-preserving §6.2 reduction, while the left-hand side (the §6.2 vertex
throughput) is not. -/
theorem visitCount_le_windowCount [DecidableEq A] {L : Nat} {vs : List (List A)}
    {ovs : List Nat} (h : GenuineWalk L vs ovs) (u : List A) :
    throughputOf vs u ≤ windowCount L u (spellWalk vs ovs) :=
  genuineWalk_dominates h u

/-- The window-count bound is a function of the spelled word: equal words give
equal bounds. -/
theorem windowCount_congr [DecidableEq A] {L : Nat} {w v : List A} (h : w = v)
    (u : List A) : windowCount L u w = windowCount L u v := by
  rw [h]

/-- **The bound is invariant under the reduction.**  If a detour `sx → m → sy`
spells the same word as the direct edge `sx → sy` (the content of the merged
`Section62SpellingReductionCandidate.spellPath_eq_spellDirect`), then the
window-count upper bound on the throughput is unchanged. -/
theorem windowCount_detour_eq [DecidableEq A] {L : Nat} {sx m sy : List A}
    {l1 l2 l : Nat}
    (hspell : spellWalk [sx, m, sy] [l1, l2] = spellWalk [sx, sy] [l])
    (u : List A) :
    windowCount L u (spellWalk [sx, m, sy] [l1, l2]) =
      windowCount L u (spellWalk [sx, sy] [l]) :=
  windowCount_congr hspell u

/-! ## The bound is not tight: the `L = 5` seam-window witness -/

/-- `sx = 01234`. -/
private def wxSx : List Nat := [0, 1, 2, 3, 4]
/-- `sy = 41200`. -/
private def wxSy : List Nat := [4, 1, 2, 0, 0]
/-- The unobserved seam window `34120`. -/
private def wxSeam : List Nat := [3, 4, 1, 2, 0]

/-- The direct `1`-overlap walk `sx → sy` is a genuine walk. -/
theorem witness_genuine : GenuineWalk 5 [wxSx, wxSy] [1] := by
  refine GenuineWalk.cons (by decide) (by decide) (by decide) ?_
  exact GenuineWalk.single _ (by decide)

/-- The seam window `34120` is a length-`5` window of the spelled word. -/
theorem witness_seam_windowCount : windowCount 5 wxSeam (spellWalk [wxSx, wxSy] [1]) = 1 := by
  decide

/-- The seam window `34120` is visited by no read of the direct walk. -/
theorem witness_seam_visitCount : throughputOf [wxSx, wxSy] wxSeam = 0 := by
  decide

/-- **The bound is strict at `L = 5`.**  The invariant window multiset has a
window with multiplicity `1` that is visited by no read, so the transport bound
`throughputOf ≤ windowCount` is not an equality, and the exact throughput is not
recoverable from the window multiset alone.  The residual gap is precisely the
unobserved seam windows. -/
theorem witness_bound_strict :
    throughputOf [wxSx, wxSy] wxSeam
      < windowCount 5 wxSeam (spellWalk [wxSx, wxSy] [1]) := by
  rw [witness_seam_visitCount, witness_seam_windowCount]
  decide

/-- The transport bound holds for the witness (via the main theorem). -/
theorem witness_bound_holds :
    throughputOf [wxSx, wxSy] wxSeam
      ≤ windowCount 5 wxSeam (spellWalk [wxSx, wxSy] [1]) :=
  visitCount_le_windowCount witness_genuine wxSeam

/-! ## Axiom audit -/

#print axioms genuineWalk_length
#print axioms spellWalk_cons_drop
#print axioms windows_eq_append_windows_drop
#print axioms windows_spellWalk_cons
#print axioms genuineWalk_dominates
#print axioms visitCount_le_windowCount
#print axioms windowCount_detour_eq
#print axioms witness_bound_strict
#print axioms witness_bound_holds

end AssemblyP1.Section62VisitWindowBridge
