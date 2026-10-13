import AssemblyP1.Section62SpellingReductionCandidate

/-!
A local algebraic step toward #284: an internal length-L window of a direct
equal-read-length overlap decomposes into a suffix of the first read plus a
prefix of the extension of the second read.
-/

namespace AssemblyP1.Section62SkippedWindowFactor

open Section62Flow Section62SpellingReductionCandidate

variable {A : Type}

theorem internal_window_decomposition (u v : List A) (L ell t : Nat)
    (hu : u.length = L) (hv : v.length = L)
    (hell : ell < L) (ht : t < L - ell) :
    ((spellDirect u v ell).drop t).take L =
      u.drop t ++ (v.drop ell).take t := by
  have htle : t ≤ u.length := by omega
  have hlen : (u.drop t).length = L - t := by
    rw [List.length_drop, hu]
  unfold spellDirect
  rw [List.drop_append_of_le_length (h := htle)]
  rw [List.take_append]
  rw [hlen]
  have heq : L - (L - t) = t := by omega
  rw [heq]
  have hle : (u.drop t).length ≤ L := by omega
  rw [List.take_of_length_le hle]

theorem internal_window_length (u v : List A) (L ell t : Nat)
    (hu : u.length = L) (hv : v.length = L)
    (hell : ell < L) (ht : t < L - ell) :
    (((spellDirect u v ell).drop t).take L).length = L := by
  rw [List.length_take, List.length_drop]
  have hd := spellDirect_length hu hv (Nat.le_of_lt hell)
  rw [hd]
  omega

theorem internal_window_first_overlap (u v : List A) (L ell t : Nat)
    (hu : u.length = L) (hv : v.length = L)
    (hell : ell < L) (ht : t < L - ell) :
    sufOf u (L - t) =
      preOf (((spellDirect u v ell).drop t).take L) (L - t) := by
  rw [internal_window_decomposition u v L ell t hu hv hell ht]
  unfold sufOf preOf
  rw [hu]
  have hsuf : L - (L - t) = t := by omega
  rw [hsuf]
  rw [List.take_append]
  rw [List.length_drop, hu]
  have hzero : (L - t) - (L - t) = 0 := by omega
  rw [hzero]
  simp [List.length_drop, hu]

#print axioms internal_window_first_overlap



theorem internal_window_second_overlap (u v : List A) (L ell t : Nat)
    (hu : u.length = L) (hv : v.length = L)
    (hell : ell < L) (ht : t < L - ell)
    (hoverlap : sufOf u ell = preOf v ell) :
    sufOf (((spellDirect u v ell).drop t).take L) (ell + t) =
      preOf v (ell + t) := by
  let m := ((spellDirect u v ell).drop t).take L
  have hm : m.length = L := internal_window_length u v L ell t hu hv hell ht
  have hdec : m = u.drop t ++ (v.drop ell).take t :=
    internal_window_decomposition u v L ell t hu hv hell ht
  have hlen : (u.drop t).length = L - t := by
    rw [List.length_drop, hu]
  have hbound : L - (ell + t) ≤ (u.drop t).length := by omega
  have hov : u.drop (L - ell) = v.take ell := by
    simpa [sufOf, preOf, hu] using hoverlap
  have htakes : v.take ell ++ (v.drop ell).take t = v.take (ell + t) := by
    have hlenv : (v.take ell).length = ell := by
      rw [List.length_take, hv]
      omega
    have hle : (v.take ell).length ≤ ell + t := by omega
    have htmp : (v.take ell ++ v.drop ell).take (ell + t) =
        v.take ell ++ (v.drop ell).take t := by
      rw [List.take_append]
      rw [List.take_of_length_le hle, hlenv]
      simp only [Nat.add_sub_cancel_left]
    rw [List.take_append_drop] at htmp
    exact htmp.symm
  change m.drop (m.length - (ell + t)) = v.take (ell + t)
  rw [hm, hdec]
  rw [List.drop_append_of_le_length (h := hbound)]
  rw [List.drop_drop]
  have hcut : t + (L - (ell + t)) = L - ell := by omega
  rw [hcut, hov]
  exact htakes

#print axioms internal_window_second_overlap



/-- The local combinatorial heart of Observation 7 for the *implemented*
spelling-preserving reduction: if an observed strand occurs in an internal
window of a genuine direct overlap, it yields a genuine equal-spelling
two-edge replacement. No circular or probability assumptions are needed. -/
theorem observed_internal_window_reducible
    {W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W)
    (L oMin : Nat) (verts : List W) (e : BdEdge A W)
    (hsx : (toList e.sx).length = L)
    (hsy : (toList e.sy).length = L)
    (hell : e.len < L)
    (hmin : oMin ≤ e.len)
    (_hoverlap : sufOf (toList e.sx) e.len = preOf (toList e.sy) e.len)
    (t : Nat) (ht0 : 0 < t) (ht : t < L - e.len)
    (m : W) (hobs : m ∈ strandsOf rc verts)
    (hword : toList m =
       ((spellDirect (toList e.sx) (toList e.sy) e.len).drop t).take L) :
    isReducibleSpellingB W toList rc L oMin verts e = true := by
  have h1 : sufOf (toList e.sx) (L - t) =
      preOf (toList m) (L - t) := by
    rw [hword]
    exact internal_window_first_overlap _ _ _ _ _ hsx hsy hell ht
  have h2 : sufOf (toList m) (e.len + t) =
      preOf (toList e.sy) (e.len + t) := by
    rw [hword]
    exact internal_window_second_overlap _ _ _ _ _ hsx hsy hell ht _hoverlap
  unfold isReducibleSpellingB
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨m, hobs, L - t, List.mem_range.mpr (by omega),
    e.len + t, List.mem_range.mpr (by omega), ?_⟩
  exact ⟨⟨⟨⟨by omega, by omega⟩, h1⟩, h2⟩, by omega⟩

/-- No surviving edge can skip an internal occurrence of an observed read
strand. This is a *local, oriented* theorem, not yet the global/circular
occurrence-count identity, RC molecule-class lift, or Myers source fidelity. -/
theorem surviving_edge_skips_no_observed_strand
    {W : Type} [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W)
    (L oMin : Nat) (verts : List W) (edges : List (BdEdge A W))
    (e : BdEdge A W)
    (hsx : (toList e.sx).length = L)
    (hsy : (toList e.sy).length = L)
    (hell : e.len < L)
    (hmin : oMin ≤ e.len)
    (hoverlap : sufOf (toList e.sx) e.len = preOf (toList e.sy) e.len)
    (hem : e ∈ transitivelyReducedSpelling W toList rc L oMin verts edges)
    (t : Nat) (ht0 : 0 < t) (ht : t < L - e.len) :
    ¬ ∃ m ∈ strandsOf rc verts,
      toList m =
        ((spellDirect (toList e.sx) (toList e.sy) e.len).drop t).take L := by
  rintro ⟨m, hobs, hword⟩
  have hb := observed_internal_window_reducible toList rc L oMin verts e
    hsx hsy hell hmin hoverlap t ht0 ht m hobs hword
  have hnot : e ∉ transitivelyReducedSpelling W toList rc L oMin verts edges := by
    simp [transitivelyReducedSpelling, hb]
  exact hnot hem

#print axioms observed_internal_window_reducible
#print axioms surviving_edge_skips_no_observed_strand

end AssemblyP1.Section62SkippedWindowFactor
