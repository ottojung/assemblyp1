import AssemblyP1.P2
import AssemblyP1.RepeatAdapter

/-!
# Why the *interleaved* clause of P2 cannot be replaced by same-length
# spectrum rigidity (issue #89, second attempt at closing `BBTUniqueAt`)

Goal of the parent attempt: remove the `BBTUniqueAt` /
`BBTCompleteSpectrumUniqueness` premise from
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
by deriving the needed complete-spectrum *rotation* uniqueness from the
kernel-checked same-length rigidity
(`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`,
issue #74) plus the actual P2 of `def:P1P2`.

This file is the evidence that the derivation is impossible in that form,
and it localises precisely which clause of P2 carries the missing
mathematics.

## Provenance

The mathematical content and the witness were produced by a parallel #89
worker, whose worktree was stopped for the five-agent cap and left this
file untracked and **not compiling** (it was missing the
`AssemblyP1.RepeatAdapter` import; its `noLongTriple_of_letterCap` proof
and both `IsPrimitive` goals were unfinished; its `IsRepeat`/`Interleaved`
witnesses were mis-elaborated). It has been repaired here — the lemma
`noLongTriple_of_letterCap` is re-proved from `TripleAgree` at offset `0`,
primitivity is re-proved through the general lemma `prim_of_not_periodic`
(a nontrivial power witness makes the word `H`-periodic), the
`Fin`-valued position witnesses are made explicit, and the `IsRepeat` and
`Interleaved` witnesses are built componentwise and kernel-checked. No
mathematical claim was added beyond the worker's; nothing was weakened to
make it go through.

## What the existing rigidity does and does not conclude

`OrientedFinal.oriented_same_length_spectrum_rigidity` concludes

  `∀ w, B w = specCount hG S w`,

i.e. it pins the *edge multiplicities* of the length-`L` de Bruijn
multigraph. Both BBT consumers in
`AssemblyP1.PopulationReduction.gcd_one_of_primitive_P2_words` and
`population_uniqueness_primitive_P2_words` instead demand

  `RotEquiv hG D S`,

a statement about *words*. Equality of spectra is strictly weaker, and the
gap is not closed by primitivity nor by the triple-repeat clause of P2 —
which is exactly what this file checks.

## The witness

At read length `L = 2` (so `K = L - 1 = 1`) over a three-letter alphabet,
with `G = 6`:

* `sW = A B A C B C`,
* `eW = A B C A C B`.

Facts, all kernel-checked here:

1. the complete `2`-spectra are **equal** (`sSpec_eq`);
2. `eW` is **not** a rotation of `sW` (`eW_not_rot`);
3. neither word has a maximal triple repeat of length `≥ 1`
   (`sW_noLongTriple`, `eW_noLongTriple`): every letter occurs exactly
   twice, so the triple-repeat clause of P2 is satisfied for both;
4. both words are **primitive** (`sW_primitive`, `eW_primitive`);
5. nevertheless P2 **fails** on both, and it fails *only* on the
   interleaved clause: `sW` has the maximal repeats
   `A` at starts `0, 2` and `B` at starts `1, 4`, which interleave
   (`sW_interleaved_pair`), each of length `1 ≥ L - 1`
   (`sW_notP2`, `eW_notP2`).

So the interleaved clause is exactly the hypothesis that rules out
alternative Eulerian circuits of the spectrum graph, i.e. exactly the
content of `thm:BBT`. It cannot be dropped in favour of same-length
spectrum rigidity, and it is not a hypothesis the existing circulation
rigidity can consume: `AssemblyP1.OrientedRigidity` and
`AssemblyP1.RepeatAdapter` contain no statement about the *order* in which
the window edges are traversed, which is what a rotation claim needs.
-/

namespace AssemblyP1.InterleavingNeeded

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open P2
open RepeatAdapter

/-- Three-letter alphabet: two letters give no interleaved maximal repeats
without forcing a period, so three are the smallest useful size here. -/
inductive Tern where
  | A | B | C
  deriving DecidableEq, Repr, Inhabited, BEq

instance : Fintype Tern :=
  ⟨{.A, .B, .C}, by intro x; cases x <;> simp⟩

/-- The truth-side word `S = A B A C B C`. -/
def sW : Fin 6 → Tern := ![Tern.A, Tern.B, Tern.A, Tern.C, Tern.B, Tern.C]

/-- The competitor `E = A B C A C B`: the same `2`-spectrum, a different
cyclic order of the letters. -/
def eW : Fin 6 → Tern := ![Tern.A, Tern.B, Tern.C, Tern.A, Tern.C, Tern.B]

theorem h6 : (0 : ℕ) < 6 := by norm_num

/-- `S` as a source-faithful circular genome. -/
def sGen : Genome Tern := mkGenome h6 sW

/-- `E` as a source-faithful circular genome. -/
def eGen : Genome Tern := mkGenome h6 eW

/-! ## A letter cap rules out long Bresler triple repeats -/

/-- **No three distinct positions carry the same symbol** is enough to
exclude every maximal triple repeat of length `≥ L - 1`: three distinct
residues agreeing on a window of positive length agree on their first
symbol, hence on `S` itself, contradicting the cap. This is the easy
direction of Lemma B of the rigidity note, and it is what the two words
above satisfy (each of their three letters occurs exactly twice). -/
theorem noLongTriple_of_letterCap {α : Type} [DecidableEq α] {G : ℕ}
    (hG : 0 < G) (S : Fin G → α) {L : ℕ} (hL : 2 ≤ L)
    (h : ∀ x y z : Fin G, x ≠ y → x ≠ z → y ≠ z → S x ≠ S y ∨ S y ≠ S z) :
    ¬ RepeatAdapter.HasLongTripleRepeat hG S L := by
  rintro ⟨a, b, c, ℓ, hℓ1, hℓ2, hab, hbc, hac, hmax⟩
  have hL1 : 0 < L - 1 := Nat.sub_pos_iff_lt.mpr (lt_of_lt_of_le (by omega) hL)
  have hpos : 0 < ℓ := lt_of_lt_of_le hL1 hℓ1
  let A : Fin G := ⟨a % G, Nat.mod_lt _ hG⟩
  let B : Fin G := ⟨b % G, Nat.mod_lt _ hG⟩
  let C : Fin G := ⟨c % G, Nat.mod_lt _ hG⟩
  have hAB : A ≠ B := fun hE => hab (congrArg Fin.val hE)
  have hAC : A ≠ C := fun hE => hac (congrArg Fin.val hE)
  have hBC : B ≠ C := fun hE => hbc (congrArg Fin.val hE)
  -- agreement at offset `0`: the three first symbols coincide
  have hag := hmax.1 0 hpos
  have h₁ : OrientedRigidity.cyc hG S a = OrientedRigidity.cyc hG S b := hag.1
  have h₂ : OrientedRigidity.cyc hG S b = OrientedRigidity.cyc hG S c := hag.2
  -- `cyc` reads the residue, so this is a statement about three positions
  simp only [OrientedRigidity.cyc] at h₁ h₂
  have hcases := h A B C hAB hAC hBC
  rcases hcases with hxy | hyz
  · exact hxy h₁
  · exact hyz h₂

/-! ## The two words -/

/-- `¬ HasLongTripleRepeat h6 sW 2`: each letter of `S` occurs exactly
twice. -/
theorem sW_noLongTriple : ¬ RepeatAdapter.HasLongTripleRepeat h6 sW 2 := by
  refine noLongTriple_of_letterCap h6 sW (by norm_num) ?_
  intro x y z hxy hxz hyz
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [sW] <;> decide

/-- `¬ HasLongTripleRepeat h6 eW 2`: likewise for `E`. -/
theorem eW_noLongTriple : ¬ RepeatAdapter.HasLongTripleRepeat h6 eW 2 := by
  refine noLongTriple_of_letterCap h6 eW (by norm_num) ?_
  intro x y z hxy hxz hyz
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [eW] <;> decide

/-- Modulo bookkeeping: if `H` divides `G` then advancing by `H` and
reducing mod `G` does not change the residue mod `H`. -/
theorem mod_mod_add {G H : ℕ} (hHG : H ∣ G) (i : ℕ) :
    ((i + H) % G) % H = i % H := by
  rw [Nat.mod_mod_of_dvd _ hHG, Nat.add_mod]
  simp

/-- A circular word that is not periodic with any shift `p` satisfying
`0 < p < |S|` is primitive: a nontrivial power witness `H * q = |S|`,
`1 < q`, would make it `H`-periodic. -/
theorem prim_of_not_periodic {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G)
    (S : Fin G → α)
    (hnp : ∀ p : ℕ, 0 < p → p < G →
      ∃ i : Fin G, S i ≠ S ⟨(i.val + p) % G, Nat.mod_lt _ hG⟩) :
    PopulationReduction.IsPrimitive S := by
  rintro ⟨H, hH, U, q, hq, hlen, hrep⟩
  have hHlt : H < G := by
    have h1 : H * 1 < H * q := Nat.mul_lt_mul_of_pos_left hq hH
    have h2 : H * 1 = H := by simp
    omega
  obtain ⟨i, hi⟩ := hnp H hH hHlt
  have hHG : H ∣ G := ⟨q, hlen.symm⟩
  have h1 : S i = U ⟨i.val % H, Nat.mod_lt _ hH⟩ := hrep i
  have h2 : S ⟨(i.val + H) % G, Nat.mod_lt _ hG⟩
      = U ⟨((i.val + H) % G) % H, Nat.mod_lt _ hH⟩ := hrep _
  have hval : ((i.val + H) % G) % H = i.val % H := mod_mod_add hHG i.val
  have hkey : (⟨((i.val + H) % G) % H, Nat.mod_lt _ hH⟩ : Fin H)
      = ⟨i.val % H, Nat.mod_lt _ hH⟩ := by
    apply Fin.ext
    exact hval
  rw [hkey] at h2
  refine hi ?_
  exact h1.trans h2.symm

/-- `S = A B A C B C` is not periodic with shift `1`, `2` or `3` (the
only shifts a nontrivial power of a length-`6` word could have). -/
theorem sW_not_periodic : ∀ p : ℕ, 0 < p → p < 6 →
    ∃ i : Fin 6, sW i ≠ sW ⟨(i.val + p) % 6, Nat.mod_lt _ h6⟩ := by
  intro p hp1 hp6
  have hcases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
  have hne : ¬ (∀ i : Fin 6, sW i = sW ⟨(i.val + p) % 6, Nat.mod_lt _ h6⟩) := by
    rcases hcases with hp | hp | hp | hp | hp <;> subst hp <;> decide
  exact (not_forall).mp hne

/-- Hence `S` is primitive. -/
theorem sW_primitive : IsPrimitive sW :=
  prim_of_not_periodic h6 sW sW_not_periodic

/-- `E = A B C A C B` is likewise not periodic with shift `1`, `2` or `3`. -/
theorem eW_not_periodic : ∀ p : ℕ, 0 < p → p < 6 →
    ∃ i : Fin 6, eW i ≠ eW ⟨(i.val + p) % 6, Nat.mod_lt _ h6⟩ := by
  intro p hp1 hp6
  have hcases : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 := by omega
  have hne : ¬ (∀ i : Fin 6, eW i = eW ⟨(i.val + p) % 6, Nat.mod_lt _ h6⟩) := by
    rcases hcases with hp | hp | hp | hp | hp <;> subst hp <;> decide
  exact (not_forall).mp hne

/-- Hence `E` is primitive as well. -/
theorem eW_primitive : IsPrimitive eW :=
  prim_of_not_periodic h6 eW eW_not_periodic

/-! ## Equal spectra, different rotations -/

/-- **The two complete `2`-spectra agree.** Each of the six ordered pairs
`AB, BA, AC, CB, BC, CA` occurs once in each word. -/
theorem sSpec_eq :
    specCount (L := 2) h6 sW = specCount (L := 2) h6 eW := by
  funext w
  fin_cases w <;> decide

/-- The shift of `RotEquiv` only matters modulo `6`. -/
theorem rot_shift_mod {α : Type} {G : ℕ} (hG : 0 < G) {D S : Fin G → α} (k : ℕ)
    (h : ∀ i : Fin G, D ⟨(i.val + k) % G, Nat.mod_lt _ hG⟩ = S i) :
    ∀ i : Fin G, D ⟨(i.val + k % G) % G, Nat.mod_lt _ hG⟩ = S i := by
  intro i
  have e1 : (i.val + k) % G = (i.val + k % G) % G := by
    calc (i.val + k) % G = (i.val % G + k % G) % G := Nat.add_mod _ _ _
      _ = (i.val + k % G) % G := by rw [Nat.mod_eq_of_lt i.isLt]
  have e2 : (⟨(i.val + k) % G, Nat.mod_lt _ hG⟩ : Fin G)
      = ⟨(i.val + k % G) % G, Nat.mod_lt _ hG⟩ := Fin.ext e1
  show D ⟨(i.val + k % G) % G, Nat.mod_lt _ hG⟩ = S i
  rw [← e2]
  exact h i

/-- `E` is not a cyclic shift of `S`: `E` also has length `6`, so it
suffices to check the six shifts mod `6`, and each is refuted by a finite
check. -/
theorem eW_not_rot : ¬ RotEquiv h6 eW sW := by
  rintro ⟨k, hk⟩
  have hk' := rot_shift_mod h6 k hk
  have hlt : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hcases : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by
    omega
  rcases hcases with hc | hc | hc | hc | hc | hc <;>
    rw [hc] at hk' <;>
    exact absurd hk' (by decide)

/-! ## P2 fails on both words, and only through interleaving -/

/-- The genome length, in numerals: both `sGen` and `eGen` are built by
`mkGenome` from a length-`6` word, so `.len` reduces but is not syntactically
`6` until the projection is exposed. -/
theorem sGen_len : sGen.len = 6 := rfl

theorem eGen_len : eGen.len = 6 := rfl

/-- A position of `S`, as a `Fin sGen.len`. -/
def f0 : Fin sGen.len := ⟨0, by rw [sGen_len]; norm_num⟩
/-- A position of `S`. -/
def f1 : Fin sGen.len := ⟨1, by rw [sGen_len]; norm_num⟩
/-- A position of `S`. -/
def f2 : Fin sGen.len := ⟨2, by rw [sGen_len]; norm_num⟩
/-- A position of `S`. -/
def f3 : Fin sGen.len := ⟨3, by rw [sGen_len]; norm_num⟩
/-- A position of `S`. -/
def f4 : Fin sGen.len := ⟨4, by rw [sGen_len]; norm_num⟩
/-- A position of `S`. -/
def f5 : Fin sGen.len := ⟨5, by rw [sGen_len]; norm_num⟩

/-- The same numerals, as positions of `E`. -/
def g0 : Fin eGen.len := ⟨0, by rw [eGen_len]; norm_num⟩
def g1 : Fin eGen.len := ⟨1, by rw [eGen_len]; norm_num⟩
def g3 : Fin eGen.len := ⟨3, by rw [eGen_len]; norm_num⟩
def g5 : Fin eGen.len := ⟨5, by rw [eGen_len]; norm_num⟩
/-- The repeat length `L - 1 = 1` used throughout. -/
def e1 : Fin sGen.len := ⟨1, by rw [sGen_len]; norm_num⟩

/-- `f0 ≠ f2` and friends, by reducing to the underlying numerals. -/
private theorem fin_ne (a b : Fin 6) (h : a.val = b.val) (hab : a.val ≠ b.val) : False :=
  absurd h hab

/-- The two copies of `A` at starts `0` and `2` of `S = A B A C B C` form a
maximal repeat of length `1`: the windows agree, and the preceding symbols
(`C` against `B`) and following symbols (`B` against `C`) differ. -/
theorem sIsRepeat_A : sGen.IsRepeat 1 f0 f2 := by
  have e1 : sGen.Preceding f0 = Tern.C := by rfl
  have e2 : sGen.Preceding f2 = Tern.B := by rfl
  have e3 : sGen.Following 1 f0 = Tern.B := by rfl
  have e4 : sGen.Following 1 f2 = Tern.C := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [sGen, mkGenome]
  · norm_num [sGen, mkGenome]
  · intro h
    have hv := congrArg Fin.val h
    simp [f0, f2] at hv
  · intro d
    fin_cases d
    rfl
  · rw [e1, e2]
    decide
  · rw [e3, e4]
    decide

/-- The two copies of `B` at starts `1` and `4` of `S` form a maximal
repeat of length `1`. -/
theorem sIsRepeat_B : sGen.IsRepeat 1 f1 f4 := by
  have e1 : sGen.Preceding f1 = Tern.A := by rfl
  have e2 : sGen.Preceding f4 = Tern.C := by rfl
  have e3 : sGen.Following 1 f1 = Tern.A := by rfl
  have e4 : sGen.Following 1 f4 = Tern.C := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [sGen, mkGenome]
  · norm_num [sGen, mkGenome]
  · intro h
    have hv := congrArg Fin.val h
    simp [f1, f4] at hv
  · intro d
    fin_cases d
    rfl
  · rw [e1, e2]
    decide
  · rw [e3, e4]
    decide

/-- The four starts `0, 2, 1, 4` alternate around the circle: `1` lies on
the open clockwise arc from `0` to `2`, and `4` does not. -/
theorem sInterleaved : Interleaved sGen f0 f2 f1 f4 := by
  have h1 : InOpenArc sGen f0 f2 f1 := by
    refine ⟨?_, ?_⟩
    · norm_num [InOpenArc, sGen, mkGenome, f0, f1, f2, f3, f4, f5]
    · norm_num [InOpenArc, sGen, mkGenome, f0, f1, f2, f3, f4, f5]
  have h4 : ¬ InOpenArc sGen f0 f2 f4 := by
    intro h
    obtain ⟨hlo, hhi⟩ := h
    norm_num [InOpenArc, sGen, mkGenome, f0, f1, f2, f3, f4, f5] at hlo hhi
  have h4d : FourDistinct f0 f2 f1 f4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro h <;> have hv := congrArg Fin.val h <;>
        simp [f0, f1, f2, f4] at hv
  exact ⟨h4d, Iff.intro (fun _ => h4) (fun _ => h1)⟩

/-- The two copies of `A` at starts `0` and `3` of `E = A B C A C B` form a
maximal repeat of length `1`. -/
theorem eIsRepeat_A : eGen.IsRepeat 1 g0 g3 := by
  have e1 : eGen.Preceding g0 = Tern.B := by rfl
  have e2 : eGen.Preceding g3 = Tern.C := by rfl
  have e3 : eGen.Following 1 g0 = Tern.B := by rfl
  have e4 : eGen.Following 1 g3 = Tern.C := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [eGen, mkGenome]
  · norm_num [eGen, mkGenome]
  · intro h
    have hv := congrArg Fin.val h
    simp [g0, g3] at hv
  · intro d
    fin_cases d
    rfl
  · rw [e1, e2]
    decide
  · rw [e3, e4]
    decide

/-- The two copies of `B` at starts `1` and `5` of `E` form a maximal
repeat of length `1`. -/
theorem eIsRepeat_B : eGen.IsRepeat 1 g1 g5 := by
  have e1 : eGen.Preceding g1 = Tern.A := by rfl
  have e2 : eGen.Preceding g5 = Tern.C := by rfl
  have e3 : eGen.Following 1 g1 = Tern.C := by rfl
  have e4 : eGen.Following 1 g5 = Tern.A := by rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [eGen, mkGenome]
  · norm_num [eGen, mkGenome]
  · intro h
    have hv := congrArg Fin.val h
    simp [g1, g5] at hv
  · intro d
    fin_cases d
    rfl
  · rw [e1, e2]
    decide
  · rw [e3, e4]
    decide

/-- The four starts `0, 3, 1, 5` alternate around the circle. -/
theorem eInterleaved : Interleaved eGen g0 g3 g1 g5 := by
  have h1 : InOpenArc eGen g0 g3 g1 := by
    refine ⟨?_, ?_⟩
    · norm_num [InOpenArc, eGen, mkGenome, g0, g1, g3, g5]
    · norm_num [InOpenArc, eGen, mkGenome, g0, g1, g3, g5]
  have h4 : ¬ InOpenArc eGen g0 g3 g5 := by
    intro h
    obtain ⟨hlo, hhi⟩ := h
    norm_num [InOpenArc, eGen, mkGenome, g0, g1, g3, g5] at hlo hhi
  have h4d : FourDistinct g0 g3 g1 g5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intro h <;> have hv := congrArg Fin.val h <;>
        simp [g0, g1, g3, g5] at hv
  exact ⟨h4d, Iff.intro (fun _ => h4) (fun _ => h1)⟩

/-- The witness that the *interleaved* clause is the load-bearing one: in
`S` the maximal repeats `A` at starts `0, 2` and `B` at starts `1, 4`
interleave, and both have length `1 = L - 1`. -/
theorem sW_interleaved_pair :
    ∃ (e₁ e₂ a b c d : Fin 6), sGen.IsRepeat e₁ a b ∧ sGen.IsRepeat e₂ c d ∧
      Interleaved sGen a b c d ∧ 1 ≤ e₁.val ∧ 1 ≤ e₂.val := by
  -- the two copies of `A` at starts 0 and 2 and of `B` at starts 1 and 4,
  -- each a maximal repeat of length 1, with the four starts alternating
  exact ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩, f0, f2, f1, f4, sIsRepeat_A,
    sIsRepeat_B, sInterleaved, by decide, by decide⟩

/-- Hence `S` does **not** satisfy P2 at `L = 2`. -/
theorem sW_notP2 : ¬ P2 h6 2 sW := by
  intro hP2
  obtain ⟨e₁, e₂, a, b, c, d, hR₁, hR₂, hI, h1, h2⟩ := sW_interleaved_pair
  rcases hP2.2 e₁ e₂ a b c d hR₁ hR₂ hI with hc1 | hc2 <;> omega

/-- Likewise `E` does not satisfy P2 at `L = 2`: the maximal repeats `A` at
starts `0, 3` and `B` at starts `1, 5` interleave. -/
theorem eW_notP2 : ¬ P2 h6 2 eW := by
  intro hP2
  have hpair : ∃ (e₁ e₂ a b c d : Fin 6), eGen.IsRepeat e₁ a b ∧
      eGen.IsRepeat e₂ c d ∧ Interleaved eGen a b c d := by
    exact ⟨⟨1, by norm_num⟩, ⟨1, by norm_num⟩, g0, g3, g1, g5, eIsRepeat_A,
      eIsRepeat_B, eInterleaved⟩
  obtain ⟨e₁, e₂, a, b, c, d, hR₁, hR₂, hI⟩ := hpair
  rcases hP2.2 e₁ e₂ a b c d hR₁ hR₂ hI with hc1 | hc2
  · have hle := hR₁.1
    simp at hle hc1
    omega
  · have hle := hR₂.1
    simp at hle hc2
    omega

/-- **Summary.** Same length, same complete `2`-spectrum, both primitive,
both free of long Bresler triple repeats — and still not rotations. The
single hypothesis that separates this pair, and the only thing
`thm:BBT` needs on top of same-length spectrum rigidity, is the
interleaved-repeat clause of P2. Any kernel proof of complete-spectrum
rotation uniqueness must therefore be a *word-level* argument about the
traversal order of the window edges, not an argument in
`AssemblyP1.OrientedRigidity`. -/
theorem rotation_uniqueness_needs_interleaving :
    specCount (L := 2) h6 sW = specCount (L := 2) h6 eW ∧
      ¬ RotEquiv h6 eW sW ∧
      ¬ RepeatAdapter.HasLongTripleRepeat h6 sW 2 ∧
      ¬ RepeatAdapter.HasLongTripleRepeat h6 eW 2 ∧
      ¬ P2 h6 2 sW ∧ ¬ P2 h6 2 eW :=
  ⟨sSpec_eq, eW_not_rot, sW_noLongTriple, eW_noLongTriple, sW_notP2, eW_notP2⟩

end AssemblyP1.InterleavingNeeded
