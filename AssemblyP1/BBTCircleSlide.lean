import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.BBTChords

/-!
# Sliding one end of a chord pair back (pure finite circle, #89)

Pure finite-circle lemma: on the circle of `G` positions, if the two chords
`{a, b}` and `{c, d}` interleave, and neither `prev a` nor `prev b` coincides
with `c` or `d` (where `prev x := rotAdd hG (G-1) x`), then the chords
`{prev a, prev b}` and `{c, d}` still interleave.

The hypotheses `prev a ≠ c, d` and `prev b ≠ c, d` are exactly what is needed:
`prev b = c` means the slid end lands *on* one of the other endpoints, which is
the only configuration in which the alternation can flip.

This module is self-contained: it uses only `rotAdd`/`sh`/`InArc` from
`BBTChords` and `BBTUniqueEulerian`, no words, spectra or graphs.
No `sorry`, no `admit`, no new axiom.
-/

namespace AssemblyP1.BBTCircleSlide

open AssemblyP1.BBTChords
open AssemblyP1.BBTUniqueEulerian

variable {G : ℕ} (hG : 0 < G)

/-- One step backwards around the circle. -/
def prev (x : Fin G) : Fin G := rotAdd hG (G - 1) x

/-- The shift coordinate is invariant under a common rotation of the two
starts. -/
theorem sh_rotAdd (t : ℕ) (a b : Fin G) :
    sh hG (rotAdd hG t a) (rotAdd hG t b) = sh hG a b := by
  have key : rotAdd hG (sh hG a b) (rotAdd hG t a) = rotAdd hG t b := by
    calc rotAdd hG (sh hG a b) (rotAdd hG t a)
        = rotAdd hG (t + sh hG a b) a := by
          rw [rotAdd_add hG (sh hG a b) t a]
          congr 1
          omega
      _ = rotAdd hG t (rotAdd hG (sh hG a b) a) :=
          (rotAdd_add hG t (sh hG a b) a).symm
      _ = rotAdd hG t b := by rw [rotAdd_sh hG a b]
  rw [← key, sh_rotAdd_left, Nat.mod_eq_of_lt (sh_lt hG a b)]

theorem prev_ne_self (x : Fin G) : prev hG x ≠ x := by
  intro e
  have h := congrArg Fin.val e
  simp [prev, rotAdd] at h
  obtain ⟨k, hk, he⟩ := Nat.exists_eq_add_of_le (Nat.le_pred_of_lt x.isLt)
  simp [hk, Nat.mod_eq_of_lt he] at h

/-- The shift coordinate of the same point, from a point one step back, is one
more than from the point itself. -/
theorem sh_prev (a c : Fin G) : sh hG (prev hG a) c = (sh hG a c + 1) % G := by
  have h1 := sh_rotAdd hG 1 (prev hG a) c
  have h2 := sh_rotAdd_left (hG := G) hG a (sh hG a c + 1)
  have e1 : rotAdd hG 1 (prev hG a) = a := by
    have := rotAdd_add hG 1 (G - 1) a
    rwa [prev, rotAdd_full] at this
  have e2 : rotAdd hG 1 c = rotAdd hG (sh hG a c + 1) a := by
    have := rotAdd_add hG 1 (sh hG a c) a
    rwa [add_comm] at this
  rw [e1, e2] at h1
  rwa [h2, Nat.mod_eq_of_lt (Nat.mod_lt _ hG)]

/-- `prev` of both ends of a chord keeps the chord's own shift. -/
theorem sh_prev_prev (a b : Fin G) : sh hG (prev hG a) (prev hG b) = sh hG a b :=
  sh_rotAdd hG (G - 1) a b

theorem sh_eq_zero {a b : Fin G} (h : sh hG a b = 0) : a = b := by
  rw [h, rotAdd_zero] at rotAdd_sh hG a b

theorem sh_inj_right {a b c : Fin G} (h : sh hG a b = sh hG a c) : b = c := by
  rw [← rotAdd_sh hG a b, ← rotAdd_sh hG a c, h]

theorem sh_ne_pred {a b : Fin G} (h : sh hG a b = G - 1) :
    rotAdd hG (G - 1) a = b := by
  rw [h] at rotAdd_sh hG a b
  exact rotAdd_sh hG a b

/-- `prev b` is the point `sh a b` steps forward from `prev a`. -/
theorem prev_eq (a b : Fin G) : rotAdd hG (sh hG a b) (prev hG a) = prev hG b := by
  have h1 := rotAdd_sh_comm hG a (prev hG a) b
  have e1 : sh hG a (prev hG a) = G - 1 := by
    rw [prev]
    exact sh_rotAdd_left hG a (G - 1)
  have e2 : (G - 1) % G = G - 1 := by
    exact Nat.mod_eq_of_lt (by omega)
  have e3 : rotAdd hG (sh hG a (prev hG a)) b = rotAdd hG (G - 1) b := by
    rw [e1, e2]
  rw [e1, e3] at h1
  exact h1

/-- **Sliding a chord pair back one step preserves interleaving.** -/
theorem interleavedStarts_prev (a b c d : Fin G)
    (h : InterleavedStarts hG a b c d) (hpc : prev hG a ≠ c) (hpd : prev hG a ≠ d)
    (hqc : prev hG b ≠ c) (hqd : prev hG b ≠ d) :
    InterleavedStarts hG (prev hG a) (prev hG b) c d := by
  obtain ⟨hdistinct, hinter⟩ := h
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hdistinct
  have hIc : InArc hG a b c := (hinter).1
  have hId : ¬ InArc hG a b d := (hinter).2
  -- the shift coordinates, all in [0, G)
  have hsa : sh hG a b < G := sh_lt hG a b
  have hua : sh hG a c < G := sh_lt hG a c
  have hva : sh hG a d < G := sh_lt hG a d
  have hs0 : 0 < sh hG a b := by
    by_contra hcon
    exact hab (sh_eq_zero hG (Nat.le_zero.mp (Nat.not_lt.mp hcon)))
  have hu0 : 0 < sh hG a c := by
    by_contra hcon
    exact hac (sh_eq_zero hG (Nat.le_zero.mp (Nat.not_lt.mp hcon)))
  have hv0 : 0 < sh hG a d := by
    by_contra hcon
    exact had (sh_eq_zero hG (Nat.le_zero.mp (Nat.not_lt.mp hcon)))
  have hune : sh hG a c ≠ sh hG a d := fun e => hcd (sh_inj_right hG e)
  have hus : sh hG a c ≠ sh hG a b := fun e => hbc (sh_inj_right hG e)
  have hvs : sh hG a d ≠ sh hG a b := fun e => hbd (sh_inj_right hG e)
  -- the slid ends do not land on `G - 1`'s partner, i.e. the `+1` does not wrap
  have hunpred : sh hG a c ≠ G - 1 := by
    intro e
    exact hpc (by rw [e]; exact sh_ne_pred hG e)
  have hvnpred : sh hG a d ≠ G - 1 := by
    intro e
    exact hpd (by rw [e]; exact sh_ne_pred hG e)
  have hucmod : (sh hG a c + 1) % G = sh hG a c + 1 :=
    Nat.mod_eq_of_lt (by omega)
  have hvdmod : (sh hG a d + 1) % G = sh hG a d + 1 :=
    Nat.mod_eq_of_lt (by omega)
  -- the slid chord's own end does not land on `c` or `d`
  have hucne : (sh hG a c + 1) % G ≠ sh hG a b := by
    intro e
    have : sh hG (prev hG a) c = sh hG (prev hG a) (prev hG b) := by
      rw [sh_prev, sh_prev, sh_prev_prev]
    have := sh_inj_right hG (this.trans e)
    rw [prev_eq] at this
    exact hqc this
  have hvdne : (sh hG a d + 1) % G ≠ sh hG a b := by
    intro e
    have : sh hG (prev hG a) d = sh hG (prev hG a) (prev hG b) := by
      rw [sh_prev, sh_prev, sh_prev_prev]
    have := sh_inj_right hG (this.trans e)
    rw [prev_eq] at this
    exact hqd this
  refine ⟨⟨?_, hpc, hpd, hqc, hqd⟩, ?_⟩
  · intro e
    exact hab (sh_inj_right hG e)
  rw [inArc_iff, inArc_iff, sh_prev, sh_prev, sh_prev_prev]
  constructor
  · intro hc
    refine ⟨by omega, ?_⟩
    rcases hc with ⟨hc1, hc2⟩
    rw [inArc_iff, sh_rotAdd_left] at hIc
    rw [inArc_iff, sh_rotAdd_left] at hId
    rw [hucmod, hvdmod] at hc2
    have hvlt : ¬ (0 < sh hG a d ∧ sh hG a d < sh hG a b) :=
      fun hh => hId ⟨by simpa using hh.1, by simpa using hh.2⟩
    rcases lt_or_ge (sh hG a d) (sh hG a b) with hcase | hcase
    · exact False.elim (hvlt ⟨by omega, by omega⟩)
    · have : sh hG a d < sh hG a b → False := fun hh => hvlt ⟨by omega, hh⟩
      omega
  · intro hd
    rcases hd with ⟨hd1, hd2⟩
    rw [inArc_iff, sh_rotAdd_left] at hIc
    rw [inArc_iff, sh_rotAdd_left] at hId
    rw [hvdmod] at hd2
    have hucne' : ¬ (0 < sh hG a c ∧ sh hG a c < sh hG a b) :=
      fun hh => hId ⟨by simpa using hh.1, by simpa using hh.2⟩
    have hge : sh hG a b ≤ sh hG a c := by
      rcases lt_or_ge (sh hG a c) (sh hG a b) with hcase | hcase
      · exact False.elim (hucne' ⟨by omega, by omega⟩)
      · omega
    have : sh hG a c < sh hG a b → False := fun hh => hucne' ⟨by omega, hh⟩
    omega

end AssemblyP1.BBTCircleSlide
