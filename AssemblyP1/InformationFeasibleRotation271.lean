import AssemblyP1.ConditionalVsMLGenomeAdapter271
import AssemblyP1.GenomeOrbitAdapter
import AssemblyP1.SourceFaithfulIs

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-!
# Rotation invariance of `SourceFaithfulIs.InformationFeasible`, and orbit descent of `E` (#271)
-/

namespace AssemblyP1.SourceFaithfulIs

universe u
variable {α : Type u} [DecidableEq α]

/-- Rotate the circular genome `S` by `k` positions. -/
@[reducible] def rotGenome (S : Genome α) (k : Fin S.len) : Genome α :=
  ⟨S.len, S.len_pos, fun i => S.sym (i + k)⟩

@[simp] theorem rotGenome_len (S : Genome α) (k : Fin S.len) :
    (rotGenome S k).len = S.len := rfl

/-- `cycl` only depends on the argument modulo `S.len`. -/
theorem cycl_congr {S : Genome α} {a b : ℕ} (h : a % S.len = b % S.len) :
    S.cycl a = S.cycl b := by
  simp only [Genome.cycl]
  congr 1
  exact Fin.ext h

/-- The `i`-th cyclic symbol of the rotated genome is the `(i+k)`-th of `S`. -/
theorem rotGenome_cycl (S : Genome α) (k : Fin S.len) (i : ℕ) :
    (rotGenome S k).cycl i = S.cycl (i + k.val) := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  simp only [Genome.cycl, rotGenome]
  congr 1
  apply Fin.ext
  rw [Fin.val_add]
  exact Nat.mod_add_mod i S.len k.val

/-- A window of the rotated genome is a window of the original at the shifted start. -/
theorem rotGenome_window {S : Genome α} {e : ℕ} {r : Fin S.len} {k : Fin S.len} :
    (rotGenome S k).window e r = S.window e (r + k) := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  funext d
  simp only [Genome.window, rotGenome_cycl]
  apply cycl_congr
  rw [Fin.val_add]
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- The symbol preceding the copy at `t` rotates with `t`. -/
theorem rotGenome_preceding {S : Genome α} {t : Fin S.len} {k : Fin S.len} :
    (rotGenome S k).Preceding t = S.Preceding (t + k) := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  have hlen : 0 < S.len := S.len_pos
  simp only [Genome.Preceding, rotGenome_cycl, rotGenome_len]
  apply cycl_congr
  rw [Fin.val_add]
  have h1 : t.val + S.len - 1 + k.val = (t.val + k.val) + (S.len - 1) := by omega
  rw [h1, ← Nat.mod_add_mod]
  congr 1
  omega

/-- The symbol following the length-`e` copy at `t` rotates with `t`. -/
theorem rotGenome_following {S : Genome α} {e : ℕ} {t : Fin S.len} {k : Fin S.len} :
    (rotGenome S k).Following e t = S.Following e (t + k) := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  simp only [Genome.Following, rotGenome_cycl, rotGenome_len]
  apply cycl_congr
  rw [Fin.val_add]
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- Agreement of two selected starts is invariant under simultaneous rotation. -/
theorem rotGenome_agree {S : Genome α} {e a b : Fin S.len} {k : Fin S.len} :
    (rotGenome S k).Agree e a b ↔ S.Agree e (a + k) (b + k) := by
  simp only [Genome.Agree, rotGenome_window]

/-- A maximal repeat is invariant under simultaneous rotation of the genome and
its two selected starts. -/
theorem rotGenome_isRepeat {S : Genome α} {e a b : Fin S.len} {k : Fin S.len} :
    (rotGenome S k).IsRepeat e a b ↔ S.IsRepeat e (a + k) (b + k) := by
  haveI : NeZero (rotGenome S k).len := ⟨(rotGenome S k).len_pos.ne'⟩
  simp only [Genome.IsRepeat, rotGenome_agree, rotGenome_preceding, rotGenome_following]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, fun h => h3 (add_right_cancel h), h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, fun h => h3 (by rw [h]), h4, h5, h6⟩

/-- A maximal triple repeat is invariant under simultaneous rotation of the
genome and its three selected starts. -/
theorem rotGenome_isTripleRepeat {S : Genome α} {e a b c : Fin S.len}
    {k : Fin S.len} :
    (rotGenome S k).IsTripleRepeat e a b c ↔
      S.IsTripleRepeat e (a + k) (b + k) (c + k) := by
  haveI : NeZero (rotGenome S k).len := ⟨(rotGenome S k).len_pos.ne'⟩
  simp only [Genome.IsTripleRepeat, rotGenome_agree, rotGenome_preceding, rotGenome_following]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, (fun h => h3 (add_right_cancel h)),
      (fun h => h4 (add_right_cancel h)), (fun h => h5 (add_right_cancel h)),
      h6, h7, h8, h9, h10⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, (fun h => h3 (by rw [h])),
      (fun h => h4 (by rw [h])), (fun h => h5 (by rw [h])),
      h6, h7, h8, h9, h10⟩


/-! ## Symbol-free ingredients of `I_s`

`ReadCovers`, `Covers`, `BridgesCopy`, `BridgesRepeat`, `IsTripleRepeatAllBridged`,
`InOpenArc`, `Interleaved` and `IsInterleavedPairBridged` mention the genome only
through `len`, which `rotGenome` preserves definitionally, so they are invariant
under rotation with no change to the placement set. -/

theorem rotGenome_readCovers {S : Genome α} {L : ℕ} {r : Fin S.len} {p : ℕ}
    {k : Fin S.len} : ReadCovers (rotGenome S k) L r p ↔ ReadCovers S L r p :=
  Iff.rfl

theorem rotGenome_covers {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {k : Fin S.len} : Covers (rotGenome S k) L R ↔ Covers S L R :=
  Iff.rfl

theorem rotGenome_bridgesCopy {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {e : ℕ} {t : Fin S.len} {k : Fin S.len} :
    BridgesCopy (rotGenome S k) L R e t ↔ BridgesCopy S L R e t :=
  Iff.rfl

theorem rotGenome_bridgesRepeat {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {e : ℕ} {a b : Fin S.len} {k : Fin S.len} :
    BridgesRepeat (rotGenome S k) L R e a b ↔ BridgesRepeat S L R e a b :=
  Iff.rfl

theorem rotGenome_isTripleRepeatAllBridged {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e : ℕ} {a b c : Fin S.len} {k : Fin S.len} :
    IsTripleRepeatAllBridged (rotGenome S k) L R e a b c ↔
      IsTripleRepeatAllBridged S L R e a b c :=
  Iff.rfl

theorem rotGenome_inOpenArc {S : Genome α} {a b p : Fin S.len} {k : Fin S.len} :
    InOpenArc (rotGenome S k) a b p ↔ InOpenArc S a b p :=
  Iff.rfl

theorem rotGenome_interleaved {S : Genome α} {a b c d : Fin S.len}
    {k : Fin S.len} : Interleaved (rotGenome S k) a b c d ↔ Interleaved S a b c d :=
  Iff.rfl

theorem rotGenome_isInterleavedPairBridged {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {e₁ e₂ : ℕ} {a b c d : Fin S.len} {k : Fin S.len} :
    IsInterleavedPairBridged (rotGenome S k) L R e₁ e₂ a b c d ↔
      IsInterleavedPairBridged S L R e₁ e₂ a b c d :=
  Iff.rfl

/-! ## Shifting the placement set -/

/-- The placement rotation `r ↦ r + k`, as an embedding of `Fin S.len`. -/
def rotStartEmb (S : Genome α) (k : Fin S.len) : Fin S.len ↪ Fin S.len :=
  ⟨fun r => r + k, by
    haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
    exact add_left_injective k⟩

@[simp] theorem rotStartEmb_apply (S : Genome α) (k r : Fin S.len) :
    rotStartEmb S k r = r + k := rfl

/-- Modular cancellation: `(a + k) % n = ((b + k) % n + d) % n` cancels the
common shift `k`. -/
theorem mod_cancel_add {n a b k d : ℕ}
    (h : (a + k) % n = ((b + k) % n + d) % n) : a % n = (b + d) % n := by
  have h' : (a + k) % n = (b + k + d) % n := by
    rw [h, Nat.mod_add_mod]
  have hm : Nat.ModEq n (a + k) (b + d + k) := by
    rw [Nat.ModEq]; rw [h']; congr 1; omega
  have hm2 := Nat.ModEq.add_right_cancel' k hm
  rwa [Nat.ModEq] at hm2

/-- Modular introduction: from `a % n = (b + d) % n` add the common shift `k`. -/
theorem mod_intro_add {n a b k d : ℕ}
    (h : a % n = (b + d) % n) : (a + k) % n = ((b + k) % n + d) % n := by
  have hm : Nat.ModEq n a (b + d) := h
  have hm2 := hm.add_right k
  rw [Nat.ModEq] at hm2
  rw [hm2, Nat.mod_add_mod]
  congr 1
  omega

/-- Coverage is invariant under shifting the placement set: a read at `r + k`
covers exactly the shift by `k` of what a read at `r` covers, and shifting is a
bijection of positions, so covering everything is preserved. -/
theorem readCovers_add (S : Genome α) (L : ℕ) (r p : Fin S.len) (k : Fin S.len) :
    ReadCovers S L (r + k) (p + k).val ↔ ReadCovers S L r p.val := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  unfold ReadCovers
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Fin.val_add, Fin.val_add] at hd
    have h := mod_cancel_add (n := S.len) (a := p.val) (b := r.val)
      (k := k.val) (d := d.val) hd
    rwa [Nat.mod_eq_of_lt p.isLt] at h
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    rw [Fin.val_add, Fin.val_add]
    exact mod_intro_add (n := S.len) (a := p.val) (b := r.val)
      (k := k.val) (d := d.val) (by rwa [Nat.mod_eq_of_lt p.isLt])

/-- Coverage of the shifted placement set is coverage of the original. -/
theorem covers_map_rotStartEmb {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {k : Fin S.len} :
    Covers S L (R.map (rotStartEmb S k)) ↔ Covers S L R := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  constructor
  · intro h q
    obtain ⟨r, hr, hcov⟩ := h (q + k)
    obtain ⟨r', hr', rfl⟩ := Finset.mem_map.mp hr
    exact ⟨r', hr', (readCovers_add S L r' q k).mp hcov⟩
  · intro h p
    obtain ⟨r, hr, hcov⟩ := h (p - k)
    refine ⟨r + k, Finset.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
    have hh := (readCovers_add S L r (p - k) k).mpr hcov
    rwa [sub_add_cancel] at hh

/-- Modular cancellation for the bridging offset: the common shift `k` on the
read start and the target copy cancels. -/
theorem bridges_mod_cancel {n r t k d : ℕ}
    (h : ((r + k) % n + d + 1) % n = (t + k) % n) : (r + d + 1) % n = t % n := by
  have h1 : ((r + k) % n + (d + 1)) % n = (t + k) % n := by
    simpa only [Nat.add_assoc] using h
  rw [Nat.mod_add_mod] at h1
  have hm : Nat.ModEq n (r + (d + 1) + k) (t + k) := by
    rw [Nat.ModEq]
    have he : r + (d + 1) + k = r + k + (d + 1) := by omega
    rw [he, h1]
  have hm2 := Nat.ModEq.add_right_cancel' k hm
  rw [Nat.ModEq] at hm2
  have he : r + (d + 1) = r + d + 1 := by omega
  rwa [he] at hm2

/-- Modular introduction for the bridging offset. -/
theorem bridges_mod_intro {n r t k d : ℕ}
    (h : (r + d + 1) % n = t % n) : ((r + k) % n + d + 1) % n = (t + k) % n := by
  have h1 : (r + (d + 1)) % n = t % n := by
    simpa only [Nat.add_assoc] using h
  have hm : Nat.ModEq n (r + (d + 1)) t := h1
  have hm2 := hm.add_right k
  rw [Nat.ModEq] at hm2
  have hm3 : ((r + k) % n + (d + 1)) % n = (t + k) % n := by
    rw [Nat.mod_add_mod]
    have he : r + k + (d + 1) = r + (d + 1) + k := by omega
    rw [he, hm2]
  rw [Nat.add_assoc]
  exact hm3

/-- Bridging commutes with shifting the placement set: the copy at `t + k` is
bridged by the shifted reads exactly when the copy at `t` is bridged by the
original reads. -/
theorem bridgesCopy_map_rotStartEmb {S : Genome α} {L : ℕ} {R : Finset (Fin S.len)}
    {e : ℕ} {t : Fin S.len} {k : Fin S.len} :
    BridgesCopy S L (R.map (rotStartEmb S k)) e (t + k) ↔ BridgesCopy S L R e t := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  unfold BridgesCopy
  constructor
  · rintro ⟨r, hr, d, hd, ht⟩
    obtain ⟨r', hr', rfl⟩ := Finset.mem_map.mp hr
    refine ⟨r', hr', d, hd, ?_⟩
    simp only [rotStartEmb_apply] at ht
    rw [Fin.val_add, Fin.val_add] at ht
    have h := bridges_mod_cancel (n := S.len) (r := r'.val) (t := t.val)
      (k := k.val) (d := d.val) ht
    rwa [Nat.mod_eq_of_lt t.isLt] at h
  · rintro ⟨r, hr, d, hd, ht⟩
    refine ⟨r + k, Finset.mem_map.mpr ⟨r, hr, rfl⟩, d, hd, ?_⟩
    rw [Fin.val_add, Fin.val_add]
    exact bridges_mod_intro (n := S.len) (r := r.val) (t := t.val)
      (k := k.val) (d := d.val) (by rwa [Nat.mod_eq_of_lt t.isLt])


/-! ## Shifting all selected starts of `InOpenArc` / `Interleaved`

`InOpenArc S a b p` is the clockwise arc distance from `a` to `p` compared with
`a` to `b`; translating all three starts by `-k` leaves the distances unchanged.
Hence `Interleaved` (cyclic alternation) is invariant under translating all four
selected starts, which is what lets the interleaved clause of `InformationFeasible`
transfer under rotation. -/

/-- `InOpenArc` is the comparison of the clockwise arc distances, i.e. of
`(p - a).val` and `(b - a).val`. -/
theorem inOpenArc_iff_sub (S : Genome α) (a b p : Fin S.len) :
    InOpenArc S a b p ↔ 0 < (p - a).val ∧ (p - a).val < (b - a).val := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  unfold InOpenArc
  rw [Fin.val_sub, Fin.val_sub]
  have hp : p.val + S.len - a.val = S.len - a.val + p.val := by omega
  have hb : b.val + S.len - a.val = S.len - a.val + b.val := by omega
  rw [hp, hb]

theorem inOpenArc_sub_add (S : Genome α) (a b p k : Fin S.len) :
    InOpenArc S (a - k) (b - k) (p - k) ↔ InOpenArc S a b p := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  rw [inOpenArc_iff_sub, inOpenArc_iff_sub]
  have h1 : p - k - (a - k) = p - a := by abel
  have h2 : b - k - (a - k) = b - a := by abel
  rw [h1, h2]

theorem sub_right_eq_cancel {n : ℕ} [NeZero n] {a b k : Fin n}
    (h : a - k = b - k) : a = b := by
  have := congrArg (fun x => x + k) h
  rwa [sub_add_cancel, sub_add_cancel] at this

theorem fourDistinct_sub_add (S : Genome α) (a b c d k : Fin S.len) :
    FourDistinct (S := S) (a - k) (b - k) (c - k) (d - k) ↔
      FourDistinct (S := S) a b c d := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  unfold FourDistinct
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h]), fun h => h3 (by rw [h]),
      fun h => h4 (by rw [h]), fun h => h5 (by rw [h]), fun h => h6 (by rw [h])⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨fun h => h1 (sub_right_eq_cancel h), fun h => h2 (sub_right_eq_cancel h),
      fun h => h3 (sub_right_eq_cancel h), fun h => h4 (sub_right_eq_cancel h),
      fun h => h5 (sub_right_eq_cancel h), fun h => h6 (sub_right_eq_cancel h)⟩

theorem interleaved_sub_add (S : Genome α) (a b c d k : Fin S.len) :
    Interleaved S (a - k) (b - k) (c - k) (d - k) ↔ Interleaved S a b c d := by
  unfold Interleaved
  rw [fourDistinct_sub_add, inOpenArc_sub_add, inOpenArc_sub_add]

theorem interleaved_add (S : Genome α) (a b c d k : Fin S.len) :
    Interleaved S (a + k) (b + k) (c + k) (d + k) ↔ Interleaved S a b c d := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  have h := interleaved_sub_add S (a + k) (b + k) (c + k) (d + k) k
  rw [add_sub_cancel_right, add_sub_cancel_right, add_sub_cancel_right,
    add_sub_cancel_right] at h
  exact h.symm

/-! ## Rotation invariance of `InformationFeasible` -/

/-- **Rotation invariance of the source information-feasibility predicate
`I_s`.** Rotating the circular genome by `k` preserves `InformationFeasible`
exactly when the latent read-start set rotates with it.  This is the
`InformationFeasible g T ↔ InformationFeasible (rot g) (rot T)` statement, with
`rotGenome` the genome rotation and `R.map (rotStartEmb S k)` the placement
rotation. -/
theorem informationFeasible_rotGenome {S : Genome α} {L : ℕ}
    {R : Finset (Fin S.len)} {k : Fin S.len} :
    InformationFeasible (rotGenome S k) L R ↔
      InformationFeasible S L (R.map (rotStartEmb S k)) := by
  haveI : NeZero S.len := ⟨S.len_pos.ne'⟩
  constructor
  · rintro ⟨hc, htri, hint⟩
    refine ⟨covers_map_rotStartEmb.mpr (rotGenome_covers.mp hc), ?_, ?_⟩
    · intro e a b c ht
      have ht' : (rotGenome S k).IsTripleRepeat e (a - k) (b - k) (c - k) :=
        (rotGenome_isTripleRepeat (S := S) (e := e) (a := a - k) (b := b - k)
          (c := c - k) (k := k)).mpr (by
            rw [sub_add_cancel, sub_add_cancel, sub_add_cancel]; exact ht)
      have hb := htri e (a - k) (b - k) (c - k) ht'
      refine ⟨?_, ?_, ?_⟩
      · have h1 : BridgesCopy S L R e (a - k) := rotGenome_bridgesCopy.mp hb.1
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
          (t := a - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
      · have h1 : BridgesCopy S L R e (b - k) := rotGenome_bridgesCopy.mp hb.2.1
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
          (t := b - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
      · have h1 : BridgesCopy S L R e (c - k) := rotGenome_bridgesCopy.mp hb.2.2
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
          (t := c - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
    · intro e₁ e₂ a b c d h₁ h₂ hi
      have h₁' : (rotGenome S k).IsRepeat e₁ (a - k) (b - k) :=
        (rotGenome_isRepeat (S := S) (e := e₁) (a := a - k) (b := b - k) (k := k)).mpr (by
          rw [sub_add_cancel, sub_add_cancel]; exact h₁)
      have h₂' : (rotGenome S k).IsRepeat e₂ (c - k) (d - k) :=
        (rotGenome_isRepeat (S := S) (e := e₂) (a := c - k) (b := d - k) (k := k)).mpr (by
          rw [sub_add_cancel, sub_add_cancel]; exact h₂)
      have hi' : Interleaved (rotGenome S k) (a - k) (b - k) (c - k) (d - k) :=
        rotGenome_interleaved.mpr ((interleaved_sub_add S a b c d k).mpr hi)
      have hb := hint e₁ e₂ (a - k) (b - k) (c - k) (d - k) h₁' h₂' hi'
      rcases hb with hb | hb | hb | hb
      · left
        have h1 : BridgesCopy S L R e₁ (a - k) := rotGenome_bridgesCopy.mp hb
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₁)
          (t := a - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
      · right; left
        have h1 : BridgesCopy S L R e₁ (b - k) := rotGenome_bridgesCopy.mp hb
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₁)
          (t := b - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
      · right; right; left
        have h1 : BridgesCopy S L R e₂ (c - k) := rotGenome_bridgesCopy.mp hb
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₂)
          (t := c - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
      · right; right; right
        have h1 : BridgesCopy S L R e₂ (d - k) := rotGenome_bridgesCopy.mp hb
        have h2 := (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₂)
          (t := d - k) (k := k)).mpr h1
        rwa [sub_add_cancel] at h2
  · rintro ⟨hc, htri, hint⟩
    refine ⟨rotGenome_covers.mpr (covers_map_rotStartEmb.mp hc), ?_, ?_⟩
    · intro e a b c ht
      have htS : S.IsTripleRepeat e (a + k) (b + k) (c + k) :=
        (rotGenome_isTripleRepeat (S := S) (e := e) (a := a) (b := b) (c := c)
          (k := k)).mp ht
      have hb := htri e (a + k) (b + k) (c + k) htS
      refine ⟨?_, ?_, ?_⟩
      · have h1 : BridgesCopy S L R e a :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
            (t := a) (k := k)).mp hb.1
        exact rotGenome_bridgesCopy.mpr h1
      · have h1 : BridgesCopy S L R e b :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
            (t := b) (k := k)).mp hb.2.1
        exact rotGenome_bridgesCopy.mpr h1
      · have h1 : BridgesCopy S L R e c :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e)
            (t := c) (k := k)).mp hb.2.2
        exact rotGenome_bridgesCopy.mpr h1
    · intro e₁ e₂ a b c d h₁ h₂ hi
      have h₁S : S.IsRepeat e₁ (a + k) (b + k) :=
        (rotGenome_isRepeat (S := S) (e := e₁) (a := a) (b := b) (k := k)).mp h₁
      have h₂S : S.IsRepeat e₂ (c + k) (d + k) :=
        (rotGenome_isRepeat (S := S) (e := e₂) (a := c) (b := d) (k := k)).mp h₂
      have hiS : Interleaved S (a + k) (b + k) (c + k) (d + k) :=
        (interleaved_add S a b c d k).mpr (rotGenome_interleaved.mp hi)
      have hb := hint e₁ e₂ (a + k) (b + k) (c + k) (d + k) h₁S h₂S hiS
      rcases hb with hb | hb | hb | hb
      · left
        have h1 : BridgesCopy S L R e₁ a :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₁)
            (t := a) (k := k)).mp hb
        exact rotGenome_bridgesCopy.mpr h1
      · right; left
        have h1 : BridgesCopy S L R e₁ b :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₁)
            (t := b) (k := k)).mp hb
        exact rotGenome_bridgesCopy.mpr h1
      · right; right; left
        have h1 : BridgesCopy S L R e₂ c :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₂)
            (t := c) (k := k)).mp hb
        exact rotGenome_bridgesCopy.mpr h1
      · right; right; right
        have h1 : BridgesCopy S L R e₂ d :=
          (bridgesCopy_map_rotStartEmb (S := S) (L := L) (R := R) (e := e₂)
            (t := d) (k := k)).mp hb
        exact rotGenome_bridgesCopy.mpr h1

end AssemblyP1.SourceFaithfulIs



namespace AssemblyP1.ConditionalVsMLGenomeAdapter271

open AssemblyP1.SourceFaithfulIs
open AssemblyP1.GenomeOrbitAdapter
open AssemblyP1.FiniteBayesianSideInformation

/-! ## Descent of the conditional predicate `E` to rotation orbits -/

/-- The candidate-specific latent-start information-feasibility predicate of
#271, stated at the source-faithful `Genome Sym` level (so that it is meaningful
for an arbitrary representative, not only the three chosen ones). -/
def EGenome (g : Genome Sym) (r : Read) : Prop :=
  ∃ T : Finset (Fin g.len),
    (∃ s ∈ T, g.window 2 s = r) ∧ InformationFeasible g 2 T

/-- `E` is exactly `EGenome` at the chosen representatives. -/
theorem E_eq_EGenome (i : Fin 3) (r : Read) : E i r ↔ EGenome (genOf i) r :=
  Iff.rfl

/-- Rotating a placement set back and forth is the identity. -/
theorem map_eq_self {n : ℕ} (T : Finset (Fin n)) (e : Fin n ↪ Fin n)
    (h : ∀ x, e x = x) : T.map e = T := by
  ext x
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    rw [h a] at hax
    exact hax ▸ ha
  · intro hx
    exact ⟨x, hx, h x⟩

theorem map_rotStartEmb_neg_add (g : Genome Sym) (T : Finset (Fin g.len))
    (k : Fin g.len) :
    (T.map (rotStartEmb g (-k))).map (rotStartEmb g k) = T := by
  haveI : NeZero g.len := ⟨g.len_pos.ne'⟩
  rw [Finset.map_map]
  apply map_eq_self
  intro x
  show (rotStartEmb g k) (rotStartEmb g (-k) x) = x
  rw [rotStartEmb_apply, rotStartEmb_apply]
  simp

/-- `EGenome` is invariant under rotating the candidate genome: the placement
that realizes the observed read for the rotated genome is the same placement
rotated back, and the feasibility predicate commutes with the joint rotation
(`informationFeasible_rotGenome`). -/
theorem EGenome_rotGenome {g : Genome Sym} {k : Fin g.len} {r : Read} :
    EGenome (rotGenome g k) r ↔ EGenome g r := by
  haveI : NeZero g.len := ⟨g.len_pos.ne'⟩
  constructor
  · rintro ⟨T, ⟨s, hs, hsr⟩, hIF⟩
    refine ⟨T.map (rotStartEmb g k),
      ⟨s + k, Finset.mem_map.mpr ⟨s, hs, by simp [rotStartEmb_apply]⟩, ?_⟩,
      informationFeasible_rotGenome.mp hIF⟩
    rw [rotGenome_window] at hsr
    exact hsr
  · rintro ⟨T, ⟨s, hs, hsr⟩, hIF⟩
    refine ⟨T.map (rotStartEmb g (-k)),
      ⟨s - k, Finset.mem_map.mpr ⟨s, hs, by simp [rotStartEmb_apply, sub_eq_add_neg]⟩, ?_⟩, ?_⟩
    · rw [rotGenome_window, sub_add_cancel]
      exact hsr
    · have hTT : (T.map (rotStartEmb g (-k))).map (rotStartEmb g k) = T :=
        map_rotStartEmb_neg_add g T k
      exact (informationFeasible_rotGenome (S := g) (L := 2)
        (R := T.map (rotStartEmb g (-k))) (k := k)).mpr (by rwa [hTT])

/-- The `ZMod 4`-word rotation of #269 (`GenomeOrbitAdapter.rotWord`) is the
`rotGenome` rotation on the source-faithful genome. -/
theorem toGenome_rotWord (w : Word) (j : ZMod 4) :
    toGenome (rotWord w j) = rotGenome (toGenome w) ⟨j.val, j.val_lt⟩ := by
  apply congrArg (fun s => (⟨4, by norm_num, s⟩ : Genome Sym))
  funext i
  simp only [toGenome, rotGenome, rotWord]
  congr 1
  apply Fin.ext
  simp [Fin.val_add]

/-- **Descent to rotation-orbit classes.** If one representative is a rotation
of another, the feasibility event `E` holds of one exactly when it holds of the
other, at every observed read.  The proof routes through `toGenome_rotWord` and
the rotation invariance `EGenome_rotGenome`. -/
theorem E_rotWord {i j : Fin 3} {k : ZMod 4} (hrep : rep j = rotWord (rep i) k)
    {r : Read} : E i r ↔ E j r := by
  have hgen : genOf j = rotGenome (genOf i) ⟨k.val, k.val_lt⟩ := by
    unfold genOf
    rw [hrep]
    exact toGenome_rotWord (rep i) k
  show EGenome (genOf i) r ↔ EGenome (genOf j) r
  rw [hgen]
  exact (EGenome_rotGenome (g := genOf i) (k := ⟨k.val, k.val_lt⟩) (r := r)).symm

/-- The feasibility event `E`, descended to the genuine rotation-orbit quotient
`Quotient (rotSetoid Sym 4)`; `Eorb (orbit i)` is `E i`. -/
noncomputable def Eorb : Quotient (rotSetoid Sym 4) → Read → Prop :=
  Quotient.lift (fun w r => EGenome (toGenome w) r) (by
    intro w w' h
    obtain ⟨j, rfl⟩ := h
    funext r
    apply propext
    rw [toGenome_rotWord]
    exact (EGenome_rotGenome (g := toGenome w) (k := ⟨j.val, j.val_lt⟩) (r := r)).symm)

/-- On the orbit class of a candidate, `Eorb` agrees with `E`. -/
theorem Eorb_orbit (i : Fin 3) (r : Read) : Eorb (orbit i) r ↔ E i r := by
  unfold Eorb orbit
  rw [Quotient.lift_mk]
  exact Iff.rfl

/-! ## Orbit-level separation (A ∧ ¬B)

The merged `separation_genome` conditions on the representative-level predicate
`E : Fin 3 → Read → Prop`.  Since `Eorb (orbit ·)` is propositionally equal to
`E`, the same separation holds with the orbit-level predicate, so the certainty
is a statement about rotation-orbit classes rather than about the chosen
representatives. -/

/-- The orbit-level predicate `Eorb (orbit ·)` packaged as a function. -/
noncomputable def EorbPred : Fin 3 → Read → Prop := fun i r => Eorb (orbit i) r

noncomputable instance instDecidableRelEorbPred : DecidableRel EorbPred :=
  fun _ _ => Classical.propDecidable _

theorem Eorb_pred_eq_E : EorbPred = E := by
  funext i r
  exact propext (Eorb_orbit i r)

/-- **Orbit-level separation (A ∧ ¬B).** With the conditional predicate
`Eorb (orbit ·)` on the rotation-orbit classes, the conditional posterior on the
true orbit `1` is `1`, while ordinary R-only ML strictly prefers the wrong orbit
`0`, and the ordinary posterior on the truth is not certain. -/
theorem separation_orbit :
    (∀ i : Fin 3, 0 ≤ prior i) ∧ (∑ i : Fin 3, prior i = 1) ∧
      (∀ i : Fin 3, ∑ w : Read, p i w = 1) ∧
      posteriorMass prior p EorbPred orbit (r2 0 0) (orbit 1) = 1 ∧
      p 1 (r2 0 0) < p 0 (r2 0 0) ∧ ¬ MLMax 1 (r2 0 0) ∧
      posteriorMass prior p (fun _ _ => True) orbit (r2 0 0) (orbit 1) ≠ 1 := by
  simpa only [Eorb_pred_eq_E] using separation_genome

end AssemblyP1.ConditionalVsMLGenomeAdapter271
