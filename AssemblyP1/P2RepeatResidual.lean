import Mathlib
import AssemblyP1.RepeatAdapter
import AssemblyP1.P2

/-!
# The R1 / R2 side of the #89 P2 spectrum-uniqueness residual

`AssemblyP1.P2SpectrumUniqueness` reduces `thm:BBT` at `K = L - 1` to
`UniqueEulerCircuit` for the `(L-1)`-de Bruijn multigraph, and documents the two
missing repeat-theoretic ingredients on the *genome* side:

* **(R1)** simultaneous maximal extension of agreeing starts to a maximal
  repeat / maximal triple repeat;
* **(R2)** the consequences of actual `P2` for the multigraph: node
  multiplicity `≤ 2` and the non-interleaving property.

This module proves the genome-side parts of (R1) and (R2), reusing
`SourceFaithfulIs` maximal-repeat definitions and the `RepeatAdapter`
extension engine. It deliberately does **not** touch the multigraph/chord
combinatorics ((R3), handled elsewhere).

## Two corrections to the residual, forced by counterexamples

The residual as written in `docs/issue89-spectrum-uniqueness.md` §3 states

* (R1) "there are `E` and **the same starts** `r₁, …, rₙ` …";
* (R2) "`P2` (clause 2) + (R1) with `n = 2` gives `NodeCrossing`", i.e. that
  the `NodeCrossing` of `P2SpectrumUniqueness` is a consequence of `P2`.

**Both are false**, and the false step in both is the same one: a maximal
extension does not stay at the selected starts.  The kernel-checked
counterexample for both is the **primitive** circular word `S = AABAB`
(`G = 5`) at read length `L = 3` — it satisfies the repository's actual `P2`
(`cex_is_p2`), its two repeated `2`-mers are `01` (starts `1, 3`) and `10`
(starts `2, 4`), and `Interleaved 1 3 2 4` holds:

* (R1) the starts `2, 4` carry the common `2`-mer `10`
  (`cex_pair_agrees`), but there is **no** `e` with `2 ≤ e < 5` for which
  `IsRepeat e 2 4` holds: the two copies are preceded by the same symbol
  (`S 1 = S 3 = A`), so no extension *at these starts* is left-maximal
  (`cex_not_maximalRepeat_at_same_starts`).
* (R2) `NodeCrossing hG 3 S` fails on that word (`cex_not_NodeCrossing`).

Nothing in the library was weakened.  The corrected (R1) keeps
`Genome.IsRepeat` / `Genome.IsTripleRepeat` exactly as they are, but the
maximal extension is taken at the **shifted** starts
(`maxPairStart`, `maxPairLen`); the corrected (R2) non-crossing statement
(`ExtCrossing`, `P2.imp_ExtCrossing`) is about those **extended** pairs, which
is exactly what clause 2 of `P2` forbids: each extension is a maximal repeat of
length `≥ L - 1 > L - 2`.  Exhaustive search over primitive binary words of
length `≤ 10` (all `2 ≤ L ≤ G`) finds 4838 interleaving double-node
configurations, 2534 of them on words satisfying actual `P2`; of the 1320
configurations **whose maximal extensions interleave**, *none* lies on a `P2`
word.  The smallest `P2` word carrying an interleaving double-node
configuration is `AABAB` at `L = 3`, exactly the counterexample above.

## What is proved here

* `IsPrimitive.shiftPrimitive`: the primitivity hypothesis actually carried by
  `p2_spectrum_unique_up_to_rotation` (`PopulationReduction.IsPrimitive`, "not
  a nontrivial power") implies the shift-invariance primitivity
  (`RepeatAdapter.IsPrimitive`, "minimal period `G`") that the repeat theory
  needs.  So the two notions *do* coincide in the direction used here; the
  Euclidean reduction `s ↦ G mod s` is proved rather than assumed.
* **(R1, `n = 3`)** `isTripleRepeat_of_maximalTriple` and
  `P2.imp_noLongTripleRepeat`: `RepeatAdapter.IsMaximalTriple` at natural
  starts *is* a source-faithful maximal triple repeat at the residues, so
  actual `P2` forbids `HasLongTripleRepeat` at `L`.
* **(R1, `n = 2`)** `pairBack` / `pairFwd` / `maxPair_isRepeat`: two distinct
  agreeing starts on a primitive circle extend (maximally backwards, then
  maximally forwards) to a **maximal repeat** of length `e` with
  `ℓ ≤ e < G`, at the shifted starts.  This is the full pair side of the
  simultaneous-maximal-extension lemma.
* **(R2a)** `P2.imp_nodeCount_le_two`: under actual `P2` and primitivity,
  **every** `(L-1)`-mer of `S` is spelled at most twice, i.e. every node of
  the `(L-1)`-de Bruijn multigraph of `S` has multiplicity `≤ 2`.
* **(R2b)** `P2.imp_ExtCrossing`: if two pairs of distinct starts each carry a
  common `(L-1)`-mer and the four starts interleave, then the two maximal
  extensions of those pairs do not interleave (in either ordering of the first
  pair).  This is the corrected non-interleaving property the chord worker
  consumes.

No `axiom`, `sorry` or `admit` occurs in this file, and no definition in the
library was changed to make a theorem provable.
-/
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AssemblyP1.P2RepeatResidual

open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-! ## 0. `NodeCrossing`, the (R2b) statement that `P2` does *not* imply

`NodeCrossing` is `AssemblyP1.P2SpectrumUniqueness.NodeCrossing` of the
spectrum-uniqueness lineage; this file (ported into the `BBTEulerian` tree)
quotes it verbatim so that the refutation `cex_not_NodeCrossing` below can be
stated.  Nothing else from that lineage is used. -/

/-- **Node crossing** (`P2SpectrumUniqueness.NodeCrossing`, quoted): two
vertices `u, v` of the `(L-1)`-de Bruijn multigraph of `S`, each of
multiplicity exactly `2` and realised at exactly the starts `a, b` resp.
`c, d`, never have interleaving occurrence pairs. -/
def NodeCrossing (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ (u v : Fin (L - 1) → α) (a b c d : Fin G),
    nodeCount (L := L) hG S u = 2 → nodeCount (L := L) hG S v = 2 →
    (∀ x : Fin G, nodeWindow (L := L) hG S x = u → x = a ∨ x = b) →
    (∀ x : Fin G, nodeWindow (L := L) hG S x = v → x = c ∨ x = d) →
    ¬ Interleaved (mkGenome hG S) a b c d

/-! ## 1. Primitivity: the two notions do coincide, in the direction we need

`p2_spectrum_unique_up_to_rotation` carries `PopulationReduction.IsPrimitive`
("`S` is not an *exact* `q`-fold power"), while the repeat theory of
`RepeatAdapter` uses `RepeatAdapter.IsPrimitive` ("no shift by `0 < s < G`
preserves the word"), which is the hypothesis of Bresler's Lemma B (minimal
period `G`) consumed by `RepeatAdapter.primitive_nodeCount_le_two`.

The two are not definitionally the same, so the implication is proved:
invariance under a shift `s` makes `S` constant on the cosets of
`gcd s G` inside `ℤ / Gℤ`, hence a `G / gcd s G`-fold repetition of its first
`gcd s G` symbols — an exact power.  The reduction is the Euclidean one
(`s ↦ G mod s`), which *is* valid here because invariance by `s` iterates. -/

/-- `cyc` is `G`-periodic. -/
private theorem cyc_add_G (hG : 0 < G) (S : Fin G → α) (x : ℕ) :
    cyc hG S (x + G) = cyc hG S x := by
  unfold cyc
  apply congrArg S
  apply Fin.ext
  show (x + G) % G = x % G
  calc (x + G) % G = (x % G + G) % G := (Nat.mod_add_mod x G G).symm
    _ = x % G := by
      rw [Nat.add_mod, Nat.mod_self, Nat.mod_mod, Nat.add_zero, Nat.mod_mod]

/-- Shift-invariance by `s` iterates. -/
private theorem shiftIter (hG : 0 < G) (S : Fin G → α) {s : ℕ}
    (hper : RepeatAdapter.ShiftInvariant hG S s) (x m : ℕ) :
    cyc hG S x = cyc hG S (x + s * m) := by
  induction m with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
      rw [Nat.mul_succ, show x + (s * n + s) = (x + s * n) + s by omega]
      exact ih.trans (hper (x + s * n))

/-- **Invariance under a shift is an exact power decomposition.**  Strong
induction on the shift `s`, with the Euclidean reduction `s ↦ G mod s` (which is
available because invariance by `s` iterates, and `cyc` is `G`-periodic).  This
is the minimal-counterexample engine behind `IsPrimitive.shiftPrimitive`. -/
private theorem invShift_isPower (hG : 0 < G) (S : Fin G → α) :
    ∀ (s : ℕ), 0 < s → s < G → RepeatAdapter.ShiftInvariant hG S s →
      ∃ (H q : ℕ), 0 < H ∧ H ≤ G ∧ 1 < q ∧ H * q = G ∧
        ∀ (i : Fin G) (hi : 0 < H) (hiG : H ≤ G),
          S i = S ⟨i.val % H, Nat.lt_of_lt_of_le (Nat.mod_lt _ hi) hiG⟩ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs0 hsG hper
    by_cases hm : G % s = 0
    · -- `s ∣ G`: the word is `G / s` copies of its first `s` symbols.
      have hdiv : s ∣ G := Nat.dvd_of_mod_eq_zero hm
      have hsG' : s ≤ G := Nat.le_of_dvd hG hdiv
      refine ⟨s, G / s, hs0, hsG', ?_, ?_, ?_⟩
      · by_contra hc
        have hq1 : G / s ≤ 1 := by omega
        have hmul : s * (G / s) = G := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_cancel hdiv
        have hle := Nat.mul_le_mul_left s hq1
        omega
      · rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
      · intro i hi hiG
        have hkey := shiftIter hG S hper (i.val % s) (i.val / s)
        have hdecomp : i.val % s + s * (i.val / s) = i.val := Nat.mod_add_div i.val s
        have hmodlt : i.val % s < G := by
          have hlt := Nat.lt_of_lt_of_le (Nat.mod_lt i.val hi) hiG
          omega
        have h1 : cyc hG S i.val = S ⟨i.val, i.isLt⟩ := by
          unfold cyc
          exact congrArg S (Fin.ext (Nat.mod_eq_of_lt i.isLt))
        calc S i = S ⟨i.val, i.isLt⟩ := (congrArg S (Fin.eta i i.isLt)).symm
          _ = cyc hG S i.val := h1.symm
          _ = cyc hG S (i.val % s) := by rw [hkey, hdecomp]
          _ = S ⟨i.val % s, hmodlt⟩ := by
            unfold cyc
            exact congrArg S (Fin.ext (Nat.mod_eq_of_lt hmodlt))
    · -- Euclidean step: `G mod s` is a smaller positive shift invariance.
      have hm0 : 0 < G % s := by omega
      have hmG : G % s < G := by
        have hltmod := Nat.mod_lt G hs0
        omega
      have hmul : s * (G / s) + G % s = G := by
        rw [Nat.add_comm]
        exact Nat.mod_add_div G s
      have hper' : RepeatAdapter.ShiftInvariant hG S (G % s) := by
        intro i
        have hstep : cyc hG S (i + G % s)
            = cyc hG S ((i + G % s) + s * (G / s)) :=
          shiftIter hG S hper (i + G % s) (G / s)
        have hid : (i + G % s) + s * (G / s) = i + G := by omega
        rw [hid] at hstep
        exact (hstep.trans (cyc_add_G hG S i)).symm
      obtain ⟨H, q, hH, hHG, hq1, hlen, hfac⟩ :=
        ih (G % s) (Nat.mod_lt G hs0) hm0 hmG hper'
      exact ⟨H, q, hH, hHG, hq1, hlen, fun i hi hiG => hfac i hi hiG⟩

/-- **The primitivity hypothesis of `thm:BBT` is enough for the repeat
theory.**  `PopulationReduction.IsPrimitive` ("not an exact nontrivial power")
implies `RepeatAdapter.IsPrimitive` ("minimal period `G`"), which is what every
maximal-extension argument below consumes.  This is the bridge that makes the
`_hPrimS` of `p2_spectrum_unique_up_to_rotation` usable here. -/
theorem IsPrimitive.shiftPrimitive (hG : 0 < G) {S : Fin G → α}
    (h : PopulationReduction.IsPrimitive S) : RepeatAdapter.IsPrimitive hG S := by
  intro s hs0 hsG hsInv
  obtain ⟨H, q, hH, hHG, hq1, hlen, hfac⟩ :=
    invShift_isPower hG S s hs0 hsG hsInv
  refine h ⟨H, hH, fun j => S ⟨j.val, by omega⟩, q, hq1, hlen, fun i => ?_⟩
  exact hfac i hH hHG

/-! ## 2. `cyc` bookkeeping -/

/-- `cyc` depends only on the residue mod `G`. -/
private theorem cyc_congr (hG : 0 < G) (S : Fin G → α) {x y : ℕ}
    (h : x % G = y % G) : cyc hG S x = cyc hG S y := by
  unfold cyc
  exact congrArg S (Fin.ext h)

private theorem cyc_plus_G (hG : 0 < G) (S : Fin G → α) (x d : ℕ) :
    cyc hG S (x + G + d) = cyc hG S (x + d) := by
  have h := cyc_add_G hG S (x + d)
  rwa [show x + G + d = (x + d) + G from by omega]

/-- `(x % G + y) % G = (x + y) % G`. -/
private theorem mod_add_mod (hG : 0 < G) (x y : ℕ) :
    (x % G + y) % G = (x + y) % G := by
  calc (x % G + y) % G = (x % G + (y % G + G * (y / G))) % G := by
        rw [Nat.mod_add_div y G]
    _ = ((x % G + y % G) + G * (y / G)) % G := by rw [Nat.add_assoc]
    _ = (x % G + y % G) % G := Nat.add_mul_mod_self_left _ _ _
    _ = (x + y) % G := (Nat.add_mod x y G).symm

/-- Shifting both starts back by `β` preserves the distinctness of their
residues: the shift is the *same* amount at both starts. -/
private theorem sub_ne_mod (hG : 0 < G) (x y β : ℕ) (hβ : β ≤ G)
    (hne : x % G ≠ y % G) : (x + G - β) % G ≠ (y + G - β) % G := by
  intro hcon
  have h1 := congrArg (fun z : ℕ => (z + β) % G) hcon
  rw [mod_add_mod hG, mod_add_mod hG] at h1
  have h2 : x % G = y % G := by
    rwa [show x + G - β + β = x + G from by omega,
      show y + G - β + β = y + G from by omega,
      Nat.add_mod_right, Nat.add_mod_right] at h1
  exact hne h2

/-- Re-indexing a start by its residue does not change the symbols it reads. -/
private theorem cyc_of_start (hG : 0 < G) (S : Fin G → α) (a d : ℕ) :
    cyc hG S (a % G + d) = cyc hG S (a + d) :=
  cyc_congr hG S (Nat.mod_add_mod a G d)

/-- Same, for the preceding offset. -/
private theorem cyc_of_start_pred (hG : 0 < G) (S : Fin G → α) (a : ℕ) :
    cyc hG S (a % G + G - 1) = cyc hG S (a + G - 1) := by
  calc cyc hG S (a % G + G - 1) = cyc hG S (a % G + (G - 1)) := by
        congr 3 <;> omega
    _ = cyc hG S (a + (G - 1)) := cyc_of_start hG S a (G - 1)
    _ = cyc hG S (a + G - 1) := by congr 3 <;> omega

/-- `Preceding` at the explicit start `⟨a, ha⟩`. -/
private theorem gen_preceding_of (hG : 0 < G) (S : Fin G → α) (a : ℕ) (ha : a < G) :
    (mkGenome hG S).Preceding ⟨a, ha⟩ = cyc hG S (a + G - 1) := rfl

/-- `Following` at the explicit start `⟨a, ha⟩`. -/
private theorem gen_following_of (hG : 0 < G) (S : Fin G → α) (a ℓ : ℕ) (ha : a < G) :
    (mkGenome hG S).Following ℓ ⟨a, ha⟩ = cyc hG S (a + ℓ) := rfl

/-! ## 3. (R1, `n = 3`): actual `P2` forbids long maximal triple repeats

`RepeatAdapter.extend_triple` already produces, from three distinct starts
carrying a common `(L-1)`-window and a primitive `S`, a maximal triple repeat of
length `≥ L - 1` — at *shifted* starts.  The only missing step was the
translation of `RepeatAdapter.IsMaximalTriple` (natural starts) into the
source-faithful `Genome.IsTripleRepeat` of `SourceFaithfulIs` (which is what
`P2` quantifies over).  That translation is proved here. -/

/-- **The `RepeatAdapter` maximal-triple condition is a source-faithful
maximal triple repeat at the residues.**  `Preceding`/`Following`/`window` of
`mkGenome hG S` are exactly `cyc` at `start + G - 1`, `start + e` and
`start + d`, so the natural-start formulation and the `Fin G`-start
formulation coincide. -/
theorem isTripleRepeat_of_maximalTriple (hG : 0 < G) (S : Fin G → α)
    (a b c ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ < G)
    (hd : a % G ≠ b % G ∧ b % G ≠ c % G ∧ a % G ≠ c % G)
    (h : RepeatAdapter.IsMaximalTriple hG S a b c ℓ) :
    (mkGenome hG S).IsTripleRepeat ℓ ⟨a % G, Nat.mod_lt _ hG⟩ ⟨b % G, Nat.mod_lt _ hG⟩
      ⟨c % G, Nat.mod_lt _ hG⟩ := by
  obtain ⟨hag, hpre, hfol⟩ := h
  have h12 : (⟨a % G, Nat.mod_lt _ hG⟩ : Fin G) ≠ ⟨b % G, Nat.mod_lt _ hG⟩ :=
    fun e => hd.1 (congrArg Fin.val e)
  have h13 : (⟨a % G, Nat.mod_lt _ hG⟩ : Fin G) ≠ ⟨c % G, Nat.mod_lt _ hG⟩ :=
    fun e => hd.2.2 (congrArg Fin.val e)
  have h23 : (⟨b % G, Nat.mod_lt _ hG⟩ : Fin G) ≠ ⟨c % G, Nat.mod_lt _ hG⟩ :=
    fun e => hd.2.1 (congrArg Fin.val e)
  refine ⟨h1, hℓ, h12, h13, h23, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    calc cyc hG S (a % G + d.val) = cyc hG S (a + d.val) := cyc_of_start hG S a d.val
      _ = cyc hG S (b + d.val) := (hag d.val d.isLt).1
      _ = cyc hG S (b % G + d.val) := (cyc_of_start hG S b d.val).symm
  · intro d
    calc cyc hG S (a % G + d.val) = cyc hG S (a + d.val) := cyc_of_start hG S a d.val
      _ = cyc hG S (b + d.val) := (hag d.val d.isLt).1
      _ = cyc hG S (c + d.val) := (hag d.val d.isLt).2
      _ = cyc hG S (c % G + d.val) := (cyc_of_start hG S c d.val).symm
  · intro d
    calc cyc hG S (b % G + d.val) = cyc hG S (b + d.val) := cyc_of_start hG S b d.val
      _ = cyc hG S (c + d.val) := (hag d.val d.isLt).2
      _ = cyc hG S (c % G + d.val) := (cyc_of_start hG S c d.val).symm
  · intro hcon
    obtain ⟨h1', h2'⟩ := hcon
    have e1 : (mkGenome hG S).Preceding ⟨a % G, Nat.mod_lt _ hG⟩
        = cyc hG S (a + G - 1) :=
      (gen_preceding_of hG S (a % G) (Nat.mod_lt _ hG)).trans
        (cyc_of_start_pred hG S a)
    have e2 : (mkGenome hG S).Preceding ⟨b % G, Nat.mod_lt _ hG⟩
        = cyc hG S (b + G - 1) :=
      (gen_preceding_of hG S (b % G) (Nat.mod_lt _ hG)).trans
        (cyc_of_start_pred hG S b)
    have e3 : (mkGenome hG S).Preceding ⟨c % G, Nat.mod_lt _ hG⟩
        = cyc hG S (c + G - 1) :=
      (gen_preceding_of hG S (c % G) (Nat.mod_lt _ hG)).trans
        (cyc_of_start_pred hG S c)
    exact hpre ⟨e1.symm.trans (h1'.trans e2), e2.symm.trans (h2'.trans e3)⟩
  · intro hcon
    obtain ⟨h1', h2'⟩ := hcon
    have e1 : (mkGenome hG S).Following ℓ ⟨a % G, Nat.mod_lt _ hG⟩
        = cyc hG S (a + ℓ) :=
      (gen_following_of hG S (a % G) ℓ (Nat.mod_lt _ hG)).trans
        (cyc_of_start hG S a ℓ)
    have e2 : (mkGenome hG S).Following ℓ ⟨b % G, Nat.mod_lt _ hG⟩
        = cyc hG S (b + ℓ) :=
      (gen_following_of hG S (b % G) ℓ (Nat.mod_lt _ hG)).trans
        (cyc_of_start hG S b ℓ)
    have e3 : (mkGenome hG S).Following ℓ ⟨c % G, Nat.mod_lt _ hG⟩
        = cyc hG S (c + ℓ) :=
      (gen_following_of hG S (c % G) ℓ (Nat.mod_lt _ hG)).trans
        (cyc_of_start hG S c ℓ)
    exact hfol ⟨e1.symm.trans (h1'.trans e2), e2.symm.trans (h2'.trans e3)⟩

/-- **Actual `P2` implies `¬ HasLongTripleRepeat` at `L`.**  This is clause 1 of
`def:P1P2` ("no maximal triple repeat of length `≥ L - 1`") transferred to the
`RepeatAdapter` interface, with no primitivity needed: the maximal triple
repeat produced by `extend_triple` is a source-faithful one, so `P2` forbids
it directly. -/
theorem P2.imp_noLongTripleRepeat (hG : 0 < G) (hL : 2 ≤ L) (S : Fin G → α)
    (hP2 : P2 hG L S) : ¬ RepeatAdapter.HasLongTripleRepeat hG S L := by
  rintro ⟨a, b, c, ℓ, hℓ1, hℓ2, hda, hdb, hac, h⟩
  have h1 : 1 ≤ ℓ := by omega
  have ht := isTripleRepeat_of_maximalTriple hG S a b c ℓ h1 hℓ2 ⟨hda, hdb, hac⟩ h
  have hlt := hP2.1 ⟨ℓ, hℓ2⟩ ⟨a % G, Nat.mod_lt _ hG⟩ ⟨b % G, Nat.mod_lt _ hG⟩
    ⟨c % G, Nat.mod_lt _ hG⟩ ht
  have hgl : (⟨ℓ, hℓ2⟩ : Fin G).val = ℓ := rfl
  omega

/-! ## 4. (R2a): every `(L-1)`-mer of a `P2` truth occurs at most twice

This is the "node multiplicity `≤ 2`" hypothesis of the multigraph side, and it
is exactly what `docs/issue89-spectrum-uniqueness.md` §3(R2) asks for from
clause 1 of `P2`.  It is *not* a restatement of `P1`: double nodes are allowed,
only triples are forbidden. -/

/-- **Node multiplicity `≤ 2` from actual `P2` + primitivity.**  Every
`(L-1)`-mer of a primitive `P2` truth is spelled at most twice, i.e. every node
of the `(L-1)`-de Bruijn multigraph of `S` has throughput at most two. -/
theorem P2.imp_nodeCount_le_two (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S) :
    ∀ k : Fin (L - 1) → α, nodeCount (L := L) hG S k ≤ 2 := by
  have hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L :=
    P2.imp_noLongTripleRepeat hG hL S hP2
  intro k
  by_contra hgt
  have h3 : 2 < nodeCount (L := L) hG S k := lt_of_not_ge hgt
  have h3' : 0 < nodeCount (L := L) hG S k := by omega
  unfold nodeCount at h3 h3' hgt
  obtain ⟨r, hr⟩ := Finset.card_pos.mp h3'
  have hk : nodeWindow (L := L) hG S r = k := (Finset.mem_filter.mp hr).2
  have hmem : k ∈ genomeNodes (L := L) hG S :=
    Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hk⟩
  have h2 := RepeatAdapter.primitive_nodeCount_le_two hG S hL hLG hprim hno k hmem
  unfold nodeCount at h2
  omega

/-! ## 5. (R1, `n = 2`): the maximal extension of two agreeing starts

This is the corrected form of (R1) for `n = 2`.  The maximal extension of a pair
of agreeing starts is taken at the **shifted** starts
`a + G - β, b + G - β` (`β` = maximal backward extension), and the length is
`β + γ` (`γ` = maximal forward extension from there).  `docs/issue89-spectrum-uniqueness.md`
§3 states (R1) "at the same starts"; that is false, see
`counterexample_R1_same_starts` in §7. -/

/-- The two starts `a, b` agree on the `t` positions `[a + G - t, a + G)`. -/
private def backAgree (hG : 0 < G) (S : Fin G → α) (a b t : ℕ) : Prop :=
  ∀ u : ℕ, u < t → cyc hG S (a + G - t + u) = cyc hG S (b + G - t + u)

private noncomputable def backSet (hG : 0 < G) (S : Fin G → α) (a b : ℕ) : Finset ℕ := by
  classical
  exact Finset.Icc 0 G |>.filter (backAgree hG S a b)

/-- The maximal backward extension of the pair of starts `a, b`: the largest
`t ≤ G` for which the two starts agree on the `t` positions immediately before
`a`.  The set is never empty (`t = 0` is vacuous). -/
noncomputable def pairBack (hG : 0 < G) (S : Fin G → α) (a b : ℕ) : ℕ := by
  classical
  exact (backSet hG S a b).max'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩,
      fun _ hu => absurd hu (by omega)⟩⟩

/-- The maximal backward extension agrees, and is at most `G`. -/
theorem pairBack_spec (hG : 0 < G) (S : Fin G → α) (a b : ℕ) :
    backAgree hG S a b (pairBack hG S a b) ∧ pairBack hG S a b ≤ G := by
  classical
  have hmem : pairBack hG S a b ∈ backSet hG S a b := by
    unfold pairBack
    exact Finset.max'_mem _ _
  have h := Finset.mem_filter.mp hmem
  exact ⟨h.2, (Finset.mem_Icc.mp h.1).2⟩

/-- Maximality of `pairBack`. -/
theorem pairBack_ge (hG : 0 < G) (S : Fin G → α) (a b t : ℕ) (ht : t ≤ G)
    (h : backAgree hG S a b t) : t ≤ pairBack hG S a b := by
  classical
  have hmem : t ∈ backSet hG S a b := by
    unfold backSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ht⟩, h⟩
  exact Finset.le_max' _ _ hmem

/-- **The backward extension is maximal: one more position breaks the
agreement.**  The blocks `[a + G - t, a + G)` are nested in `t`, so the only
position the `β`-block does not cover is `a + G - β - 1`. -/
theorem pairBack_succ (hG : 0 < G) (S : Fin G → α) (a b : ℕ)
    (hβ : pairBack hG S a b < G) :
    cyc hG S (a + G - pairBack hG S a b - 1)
      ≠ cyc hG S (b + G - pairBack hG S a b - 1) := by
  classical
  intro hcon
  have hβ1 : pairBack hG S a b + 1 ≤ G := by omega
  have hnew : backAgree hG S a b (pairBack hG S a b + 1) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      have harg : a + G - (pairBack hG S a b + 1) + 0
          = a + G - pairBack hG S a b - 1 := by omega
      rw [harg]
      exact hcon
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu0
      have hv : v < pairBack hG S a b := by omega
      have hag := (pairBack_spec hG S a b).1 v hv
      have harg : a + G - (pairBack hG S a b + 1) + (v + 1)
          = a + G - pairBack hG S a b + v := by omega
      have harg2 : b + G - (pairBack hG S a b + 1) + (v + 1)
          = b + G - pairBack hG S a b + v := by omega
      rw [harg, harg2]
      exact hag
  exact absurd (pairBack_ge hG S a b _ hβ1 hnew) (by omega)

/-! ### 5a. The backward chain of a chord: persistence *conditioned by
`pairBack`*, maximality, and the head of the chain

These three lemmas live here, and not in `AssemblyP1.BBTCrossingCoalesce`,
because they are statements about `backAgree` / `pairBack`, and `backAgree` is
`private` to this file: from outside it, `pairBack` can be applied but its
defining condition cannot be named, so `pairBack_spec` is not usable there.

**The shift must be bounded by `pairBack`.**  The predicate "the pair `a, b`,
shifted back by `t`, still spells a common `ℓ`-mer" is *not* monotone in `t`:
`S = 001`, `L = 2`, `a = 0`, `b = 1` carry the common `1`-mer `0`, but at
`t = 1` they read `vtx 2 = 1` and `vtx 0 = 0`.  So an unconditional
"shift-left persistence" statement is **false**, and the correct hypothesis is
`t ≤ pairBack a b`.  See `docs/crossing-coalesce-89.md` §2.1. -/

/-- **Backward chord persistence, conditioned by `pairBack`:** if the starts
`a, b` agree on the `ℓ` positions from their starts and `t ≤ pairBack a b`,
then the starts `a - t`, `b - t` (read as residues) agree on the `ℓ` positions
from their starts.

The proof is the union of two agreements: the backward agreement of length
`pairBack a b ≥ t` covers the positions `[a - t, a)`, and the original `ℓ`-mer
covers `[a, a + ℓ)`, which together cover the whole window `[a - t, a - t + ℓ)`
because `ℓ ≥ 1` at the position actually used. -/
theorem chord_shift_left (hG : 0 < G) (S : Fin G → α) (a b : Fin G) (ℓ t : ℕ)
    (hag : ∀ d : Fin ℓ, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val))
    (ht : t ≤ pairBack hG S a.val b.val) :
    ∀ d : Fin ℓ, cyc hG S ((a.val + G - t) % G + d.val)
        = cyc hG S ((b.val + G - t) % G + d.val) := by
  intro d
  rw [cyc_of_start hG S (a.val + G - t) d.val, cyc_of_start hG S (b.val + G - t) d.val]
  have hβG : pairBack hG S a.val b.val ≤ G := (pairBack_spec hG S a.val b.val).2
  by_cases hdt : d.val < t
  · -- the position lies in the backward agreement
    have hu : d.val + (pairBack hG S a.val b.val - t) < pairBack hG S a.val b.val := by omega
    have h := (pairBack_spec hG S a.val b.val).1 (d.val + (pairBack hG S a.val b.val - t)) hu
    have hidxA : a.val + G - pairBack hG S a.val b.val
          + (d.val + (pairBack hG S a.val b.val - t)) = a.val + G - t + d.val := by omega
    have hidxB : b.val + G - pairBack hG S a.val b.val
          + (d.val + (pairBack hG S a.val b.val - t)) = b.val + G - t + d.val := by omega
    rw [← hidxA, ← hidxB]; exact h
  · -- the position lies in the original `ℓ`-mer
    have hule : t ≤ d.val := Nat.le_of_not_gt hdt
    have hed : d.val - t < ℓ := by
      have := d.isLt
      omega
    have h := hag ⟨d.val - t, hed⟩
    have hidxA : a.val + G - t + d.val = a.val + (d.val - t) + G := by omega
    have hidxB : b.val + G - t + d.val = b.val + (d.val - t) + G := by omega
    have h1 : cyc hG S (a.val + G - t + d.val) = cyc hG S (a.val + (d.val - t)) := by
      rw [hidxA]
      simpa using (cyc_plus_G hG S (a.val + (d.val - t)) 0)
    have h2 : cyc hG S (b.val + G - t + d.val) = cyc hG S (b.val + (d.val - t)) := by
      rw [hidxB]
      simpa using (cyc_plus_G hG S (b.val + (d.val - t)) 0)
    rw [h1, h2]
    exact h

/-- **The head of a backward chain is reached at the shift predicted by
`pairBack`.**  If `t ≤ pairBack a b` then the maximal backward agreement of the
*shifted* pair `(a - t, b - t)` is exactly `pairBack a b - t`.

This is what makes a collision of two backward chains conclusive: the head of a
chain is the head of the *orbit*, not of the entry point, so two chords that
occur at two places of the same chain have the same head.  The upper bound is
`pairBack_ge` at `β + 1`; the lower bound is the backward agreement at `β`
restricted to the first `β - t` positions. -/
theorem pairBack_shift (hG : 0 < G) (S : Fin G → α) {a b : Fin G} (t : ℕ)
    (ht : t ≤ pairBack hG S a.val b.val)
    (hβlt : pairBack hG S a.val b.val < G) :
    pairBack hG S (a.val + G - t) (b.val + G - t) = pairBack hG S a.val b.val - t := by
  have hβG : pairBack hG S a.val b.val ≤ G := (pairBack_spec hG S a.val b.val).2
  have _ := hG
  -- lower bound
  have hlow : backAgree hG S (a.val + G - t) (b.val + G - t) (pairBack hG S a.val b.val - t) := by
    intro u hu
    have hu' : u < pairBack hG S a.val b.val := by omega
    have h := (pairBack_spec hG S a.val b.val).1 u hu'
    have hidxA : a.val + G - t + G - (pairBack hG S a.val b.val - t) + u
        = (a.val + G - pairBack hG S a.val b.val + u) + G := by omega
    have hidxB : b.val + G - t + G - (pairBack hG S a.val b.val - t) + u
        = (b.val + G - pairBack hG S a.val b.val + u) + G := by omega
    have h1 : cyc hG S (a.val + G - t + G - (pairBack hG S a.val b.val - t) + u)
        = cyc hG S (a.val + G - pairBack hG S a.val b.val + u) := by
      rw [hidxA]
      simpa using (cyc_plus_G hG S (a.val + G - pairBack hG S a.val b.val + u) 0)
    have h2 : cyc hG S (b.val + G - t + G - (pairBack hG S a.val b.val - t) + u)
        = cyc hG S (b.val + G - pairBack hG S a.val b.val + u) := by
      rw [hidxB]
      simpa using (cyc_plus_G hG S (b.val + G - pairBack hG S a.val b.val + u) 0)
    rw [h1, h2]
    exact h
  have hge1 : pairBack hG S a.val b.val - t ≤ pairBack hG S (a.val + G - t) (b.val + G - t) :=
    pairBack_ge hG S (a.val + G - t) (b.val + G - t) _ (by omega) hlow
  -- upper bound
  have hupp : ∀ s : ℕ, s ≤ G →
      backAgree hG S (a.val + G - t) (b.val + G - t) s → s ≤ pairBack hG S a.val b.val - t := by
    intro s hs hag
    have ht' : t ≤ pairBack hG S a.val b.val := ht
    by_contra hcon
    have hst : pairBack hG S a.val b.val - t < s := Nat.lt_of_not_ge hcon
    have hβ1 : pairBack hG S a.val b.val + 1 ≤ G := by omega
    have hne : cyc hG S (a.val + G - pairBack hG S a.val b.val - 1)
        ≠ cyc hG S (b.val + G - pairBack hG S a.val b.val - 1) :=
      pairBack_succ hG S a.val b.val hβlt
    have hhu : s + t - (pairBack hG S a.val b.val + 1) < s := by omega
    have h := hag (s + t - (pairBack hG S a.val b.val + 1)) hhu
    have hidxA : (a.val + G - t) + G - s + (s + t - (pairBack hG S a.val b.val + 1))
        = (a.val + G - pairBack hG S a.val b.val - 1) + G := by omega
    have hidxB : (b.val + G - t) + G - s + (s + t - (pairBack hG S a.val b.val + 1))
        = (b.val + G - pairBack hG S a.val b.val - 1) + G := by omega
    have h1 : cyc hG S ((a.val + G - t) + G - s + (s + t - (pairBack hG S a.val b.val + 1)))
        = cyc hG S (a.val + G - pairBack hG S a.val b.val - 1) := by
      rw [hidxA]
      exact (cyc_plus_G hG S _ 0)
    have h2 : cyc hG S ((b.val + G - t) + G - s + (s + t - (pairBack hG S a.val b.val + 1)))
        = cyc hG S (b.val + G - pairBack hG S a.val b.val - 1) := by
      rw [hidxB]
      exact (cyc_plus_G hG S _ 0)
    exact hne (h1.symm.trans (h.trans h2))
  have hge2 : pairBack hG S (a.val + G - t) (b.val + G - t) ≤ pairBack hG S a.val b.val - t := by
    exact hupp (pairBack hG S (a.val + G - t) (b.val + G - t))
      (pairBack_spec hG S (a.val + G - t) (b.val + G - t)).2
      (pairBack_spec hG S (a.val + G - t) (b.val + G - t)).1
  exact le_antisymm hge2 hge1

/-- The two starts `a, b` agree on the `t` positions `[a, a + t)`. -/
private def fwdAgree (hG : 0 < G) (S : Fin G → α) (a b t : ℕ) : Prop :=
  ∀ u : ℕ, u < t → cyc hG S (a + u) = cyc hG S (b + u)

private noncomputable def fwdSet (hG : 0 < G) (S : Fin G → α) (a b : ℕ) : Finset ℕ := by
  classical
  exact Finset.Icc 0 G |>.filter (fwdAgree hG S a b)

/-- The maximal forward extension of the pair of starts `a, b`. -/
noncomputable def pairFwd (hG : 0 < G) (S : Fin G → α) (a b : ℕ) : ℕ := by
  classical
  exact (fwdSet hG S a b).max'
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩,
      fun _ hu => absurd hu (by omega)⟩⟩

theorem pairFwd_spec (hG : 0 < G) (S : Fin G → α) (a b : ℕ) :
    fwdAgree hG S a b (pairFwd hG S a b) ∧ pairFwd hG S a b ≤ G := by
  classical
  have hmem : pairFwd hG S a b ∈ fwdSet hG S a b := by
    unfold pairFwd
    exact Finset.max'_mem _ _
  have h := Finset.mem_filter.mp hmem
  exact ⟨h.2, (Finset.mem_Icc.mp h.1).2⟩

theorem pairFwd_ge (hG : 0 < G) (S : Fin G → α) (a b t : ℕ) (ht : t ≤ G)
    (h : fwdAgree hG S a b t) : t ≤ pairFwd hG S a b := by
  classical
  have hmem : t ∈ fwdSet hG S a b := by
    unfold fwdSet
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ht⟩, h⟩
  exact Finset.le_max' _ _ hmem

theorem pairFwd_succ (hG : 0 < G) (S : Fin G → α) (a b : ℕ)
    (hγ : pairFwd hG S a b < G) :
    cyc hG S (a + pairFwd hG S a b) ≠ cyc hG S (b + pairFwd hG S a b) := by
  classical
  intro hcon
  have hγ1 : pairFwd hG S a b + 1 ≤ G := by omega
  have hnew : fwdAgree hG S a b (pairFwd hG S a b + 1) := by
    intro u hu
    by_cases hu0 : u = pairFwd hG S a b
    · subst hu0
      exact hcon
    · have hu' : u < pairFwd hG S a b := by omega
      exact (pairFwd_spec hG S a b).1 u hu'
  exact absurd (pairFwd_ge hG S a b _ hγ1 hnew) (by omega)

/-- Two distinct residues cannot agree on `G` consecutive positions on a
primitive circle. -/
private theorem not_agree_G (hG : 0 < G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) {x y : ℕ} (hne : x % G ≠ y % G)
    (hag : ∀ d : ℕ, d < G → cyc hG S (x + d) = cyc hG S (y + d)) : False :=
  (RepeatAdapter.not_primitive_of_ge_G_agree hG S x y G hne (le_refl _) hag) hprim

/-- **On a primitive circle the backward extension stays below `G`.** -/
theorem pairBack_lt_G (hG : 0 < G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b) :
    pairBack hG S a.val b.val < G := by
  have hne : a.val % G ≠ b.val % G := by
    intro hcon
    exact hab (Fin.ext (by
      rw [Nat.mod_eq_of_lt a.isLt] at hcon
      rw [Nat.mod_eq_of_lt b.isLt] at hcon
      exact hcon))
  by_contra hnot
  have hβle := (pairBack_spec hG S a.val b.val).2
  have hβeq : pairBack hG S a.val b.val = G := by omega
  have hag : ∀ d : ℕ, d < G → cyc hG S (a.val + d) = cyc hG S (b.val + d) := by
    intro d hd
    have hd' : d < pairBack hG S a.val b.val := by omega
    have h := (pairBack_spec hG S a.val b.val).1 d hd'
    rw [hβeq] at h
    rwa [show a.val + G - G + d = a.val + d from by omega,
      show b.val + G - G + d = b.val + d from by omega] at h
  exact not_agree_G hG S hprim hne hag

/-- **On a primitive circle the forward extension stays below `G`.** -/
theorem pairFwd_of_pairBack_lt_G (hG : 0 < G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b) :
    pairFwd hG S (a.val + G - pairBack hG S a.val b.val)
        (b.val + G - pairBack hG S a.val b.val) < G := by
  have hβle := (pairBack_spec hG S a.val b.val).2
  have hab' : a.val % G ≠ b.val % G := by
    intro hcon
    have h1 : a.val = b.val := by
      rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hcon
      exact hcon
    exact hab (Fin.ext h1)
  have hne : (a.val + G - pairBack hG S a.val b.val) % G
      ≠ (b.val + G - pairBack hG S a.val b.val) % G :=
    sub_ne_mod hG a.val b.val (pairBack hG S a.val b.val) hβle hab'
  by_contra hnot
  have hγle := (pairFwd_spec hG S (a.val + G - pairBack hG S a.val b.val)
      (b.val + G - pairBack hG S a.val b.val)).2
  have hag : ∀ d : ℕ, d < G →
      cyc hG S (a.val + G - pairBack hG S a.val b.val + d)
        = cyc hG S (b.val + G - pairBack hG S a.val b.val + d) := by
    intro d hd
    have hd' : d < pairFwd hG S (a.val + G - pairBack hG S a.val b.val)
        (b.val + G - pairBack hG S a.val b.val) := by omega
    exact (pairFwd_spec hG S (a.val + G - pairBack hG S a.val b.val)
      (b.val + G - pairBack hG S a.val b.val)).1 d hd'
  exact not_agree_G hG S hprim hne hag

/-- `IsRepeat` along a pair of equalities of starts. -/
private theorem isRepeat_congr (hG : 0 < G) (S : Fin G → α) (e : ℕ) {a a' b b' : Fin G}
    (ha : a = a') (hb : b = b') (h : (mkGenome hG S).IsRepeat e a' b') :
    (mkGenome hG S).IsRepeat e a b := by
  subst ha
  subst hb
  exact h

/-- The backward extension does not depend on the order of the two starts. -/
theorem pairBack_comm (hG : 0 < G) (S : Fin G → α) (a b : ℕ) :
    pairBack hG S b a = pairBack hG S a b := by
  classical
  refine le_antisymm
    (pairBack_ge hG S a b (pairBack hG S b a) (pairBack_spec hG S b a).2 ?_)
    (pairBack_ge hG S b a (pairBack hG S a b) (pairBack_spec hG S a b).2 ?_)
  · intro u hu
    exact ((pairBack_spec hG S b a).1 u hu).symm
  · intro u hu
    exact ((pairBack_spec hG S a b).1 u hu).symm

/-- **The starts of the maximal extension**: both agreeing starts shifted back
by the maximal backward extension. -/
noncomputable def maxPairStart (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Fin G :=
  ⟨(a.val + G - pairBack hG S a.val b.val) % G, Nat.mod_lt _ hG⟩

/-- **The length of the maximal extension**: the maximal forward extension of
the shifted pair.  It is `≥` the length of the initial agreement, because the
shifted pair already agrees on the `pairBack` positions covered by the backward
extension. -/
noncomputable def maxPairLen (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : ℕ :=
  pairFwd hG S (a.val + G - pairBack hG S a.val b.val)
    (b.val + G - pairBack hG S a.val b.val)

/-- **(R1, `n = 2`), the corrected form.**  Two distinct starts of a *primitive*
circular word that carry a common `ℓ`-window extend to a **maximal repeat** —
`SourceFaithfulIs.Genome.IsRepeat` — of some length `e` with `ℓ ≤ e < G`.  The
maximal repeat sits at the *shifted* starts `maxPairStart hG S a b`,
`maxPairStart hG S b a`; it is not in general at `a, b` themselves, and
`counterexample_R1_same_stats` (§7) exhibits the smallest failure of the
"same starts" version. -/
theorem maxPair_isRepeat (hG : 0 < G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hℓG : ℓ ≤ G)
    (hag : ∀ d : Fin ℓ, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    (mkGenome hG S).IsRepeat (maxPairLen hG S a b) (maxPairStart hG S a b)
        (maxPairStart hG S b a) ∧ ℓ ≤ maxPairLen hG S a b := by
  classical
  set β := pairBack hG S a.val b.val
  set ap := a.val + G - β
  set bp := b.val + G - β
  set γ := pairFwd hG S ap bp
  have hβle : β ≤ G := (pairBack_spec hG S a.val b.val).2
  have hβlt : β < G := pairBack_lt_G hG S hprim hab
  have hγlt : γ < G := pairFwd_of_pairBack_lt_G hG S hprim hab
  have hspec := pairFwd_spec hG S ap bp
  have hγag : ∀ u : ℕ, u < γ → cyc hG S (ap + u) = cyc hG S (bp + u) := hspec.1
  have hA : maxPairStart hG S a b = ⟨ap % G, Nat.mod_lt _ hG⟩ := by
    apply Fin.ext
    show (a.val + G - pairBack hG S a.val b.val) % G = (a.val + G - β) % G
    rfl
  have hB : maxPairStart hG S b a = ⟨bp % G, Nat.mod_lt _ hG⟩ := by
    apply Fin.ext
    show (b.val + G - pairBack hG S b.val a.val) % G = (b.val + G - β) % G
    rw [pairBack_comm]
  have hne : ap % G ≠ bp % G := by
    have hab' : a.val % G ≠ b.val % G := by
      intro hcon
      have h1' : a.val = b.val := by
        rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hcon
        exact hcon
      exact hab (Fin.ext h1')
    exact sub_ne_mod hG a.val b.val β hβle hab'
  -- the shifted pair agrees on the initial `ℓ` positions
  have hagfwd : fwdAgree hG S ap bp ℓ := by
    intro u hu
    by_cases huβ : u < β
    · have h := (pairBack_spec hG S a.val b.val).1 u huβ
      rwa [show a.val + G - β + u = ap + u from by omega,
        show b.val + G - β + u = bp + u from by omega] at h
    · have hule : β ≤ u := Nat.le_of_not_gt huβ
      have huv : u - β < ℓ := by omega
      obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hule
      have hvg : v < ℓ := by omega
      have hagv := hag ⟨v, hvg⟩
      have hAp : ap + u = a + G + v := by omega
      have hBp : bp + u = b + G + v := by omega
      calc cyc hG S (ap + u) = cyc hG S (a + G + v) := by rw [hAp]
        _ = cyc hG S (a + v) := cyc_plus_G hG S a v
        _ = cyc hG S (b + v) := hagv
        _ = cyc hG S (b + G + v) := (cyc_plus_G hG S b v).symm
        _ = cyc hG S (bp + u) := by rw [hBp]
  have hγge : ℓ ≤ γ := pairFwd_ge hG S ap bp ℓ hℓG hagfwd
  have hpre : (mkGenome hG S).Preceding ⟨ap % G, Nat.mod_lt _ hG⟩
      ≠ (mkGenome hG S).Preceding ⟨bp % G, Nat.mod_lt _ hG⟩ := by
    calc (mkGenome hG S).Preceding ⟨ap % G, Nat.mod_lt _ hG⟩
        = cyc hG S (ap + G - 1) :=
          (gen_preceding_of hG S (ap % G) (Nat.mod_lt _ hG)).trans
            (cyc_of_start_pred hG S ap)
      _ = cyc hG S (ap - 1) := by
          rw [show ap + G - 1 = (ap - 1) + G from by omega]
          exact cyc_add_G hG S (ap - 1)
      _ ≠ cyc hG S (bp - 1) := by
          intro hcon
          exact pairBack_succ hG S a.val b.val hβlt hcon
      _ = cyc hG S (bp + G - 1) := by
          rw [show bp + G - 1 = (bp - 1) + G from by omega]
          exact (cyc_add_G hG S (bp - 1)).symm
      _ = (mkGenome hG S).Preceding ⟨bp % G, Nat.mod_lt _ hG⟩ :=
          by rw [← cyc_of_start_pred hG S bp]
             exact (gen_preceding_of hG S (bp % G) (Nat.mod_lt _ hG)).symm
  have hfol : (mkGenome hG S).Following γ ⟨ap % G, Nat.mod_lt _ hG⟩
      ≠ (mkGenome hG S).Following γ ⟨bp % G, Nat.mod_lt _ hG⟩ := by
    calc (mkGenome hG S).Following γ ⟨ap % G, Nat.mod_lt _ hG⟩
        = cyc hG S (ap + γ) :=
          (gen_following_of hG S (ap % G) γ (Nat.mod_lt _ hG)).trans
            (cyc_of_start hG S ap γ)
      _ ≠ cyc hG S (bp + γ) := pairFwd_succ hG S ap bp hγlt
      _ = (mkGenome hG S).Following γ ⟨bp % G, Nat.mod_lt _ hG⟩ :=
          by rw [← cyc_of_start hG S bp γ]
             exact (gen_following_of hG S (bp % G) γ (Nat.mod_lt _ hG)).symm
  refine ⟨?_, ?_⟩
  · have hR : (mkGenome hG S).IsRepeat γ ⟨ap % G, Nat.mod_lt _ hG⟩
        ⟨bp % G, Nat.mod_lt _ hG⟩ := by
      refine ⟨by omega, ?_, ?_, ?_, hpre, hfol⟩
      · simpa only [mkGenome, SourceFaithfulIs.Genome.len] using hγlt
      · intro e
        exact hne (congrArg Fin.val e)
      · intro d
        exact (cyc_of_start hG S ap d.val).trans
          ((hγag d.val d.isLt).trans (cyc_of_start hG S bp d.val).symm)
    exact isRepeat_congr (hG := hG) (S := S) (e := γ)
      (a := maxPairStart hG S a b) (a' := ⟨ap % G, Nat.mod_lt _ hG⟩)
      (b := maxPairStart hG S b a) (b' := ⟨bp % G, Nat.mod_lt _ hG⟩)
      hA hB hR
  · show ℓ ≤ γ
    exact hγge

/-! ## 6. (R2b): the corrected non-crossing consequence of `P2`

`NodeCrossing` of `P2SpectrumUniqueness` (the occurrence pairs of double
`(L-1)`-mers do not interleave) is **false** for `P2` truths; §7 exhibits the
smallest counterexample.  The true consequence of clause 2 of `P2` is about the
*maximal extensions* of those pairs: each pair extends to a maximal repeat of
length `≥ L - 1 > L - 2` (§5), and two interleaved maximal repeats are
forbidden by clause 2. -/

/-- Two starts carrying the same `(L-1)`-mer agree on it. -/
theorem agree_of_nodeWindow_eq (hG : 0 < G) (S : Fin G → α) {a b : Fin G}
    (h : nodeWindow (L := L) hG S a = nodeWindow (L := L) hG S b) :
    ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) :=
  fun d => congrFun h d

/-- **The corrected second residual (R2b).**  Two pairs of distinct starts, each
pair carrying a common `(L-1)`-mer, that interleave, have *non-interleaving*
maximal extensions.  This replaces `NodeCrossing`, which is not a consequence
of `P2`; see `cex_not_NodeCrossing` in §7.

**What this says, exactly.**  For any two pairs of starts `(a, b)` and
`(c, d)`, with `a ≠ b`, `c ≠ d`, with `a, b` carrying the same `(L-1)`-mer and
`c, d` carrying the same `(L-1)`-mer: if the four starts interleave, then the
four *extended* starts
`maxPairStart hG S a b`, `maxPairStart hG S b a`,
`maxPairStart hG S c d`, `maxPairStart hG S d c` do not interleave, in either
ordering of the first pair.  It is a statement purely about `S`; it mentions no
spectrum, no graph and no trail.

**What this does NOT give.**

* It does **not** give `NodeCrossing` (the un-extended pairs); that statement is
  false, see `cex_not_NodeCrossing`.
* It does **not** give `UniqueEulerCircuit` for the `(L-1)`-de Bruijn
  multigraph, and it is not a lemma about Eulerian circuits at all: no
  `EulerCircuit`, `TrailEquiv`, `specCount` or `RotEquiv` occurs in it.  The
  missing step is still the multigraph/chord combinatorics (R3): that node
  multiplicity `≤ 2` (from `P2.imp_nodeCount_le_two`) together with the
  non-interleaving of the double nodes' *extended* pairs (this definition) forces
  a single Eulerian circuit of `specCount` up to cyclic shift.  The laminar-chord
  / flip-set argument that would do it is not in this file and is not attempted
  here.
* It does **not** settle `p2_spectrum_unique_up_to_rotation`, which still takes
  `hUnique : UniqueEulerCircuit …`; combining (R2a) and (R2b) with that lemma is
  the block-factorization worker's layer, and it must be redone against
  `ExtCrossing` rather than against `NodeCrossing`. -/
def ExtCrossing (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  ∀ (a b c d : Fin G), a ≠ b → c ≠ d →
    nodeWindow (L := L) hG S a = nodeWindow (L := L) hG S b →
    nodeWindow (L := L) hG S c = nodeWindow (L := L) hG S d →
    Interleaved (mkGenome hG S) a b c d →
    (¬ Interleaved (mkGenome hG S) (maxPairStart hG S a b) (maxPairStart hG S b a)
        (maxPairStart hG S c d) (maxPairStart hG S d c)) ∧
      (¬ Interleaved (mkGenome hG S) (maxPairStart hG S b a) (maxPairStart hG S a b)
        (maxPairStart hG S c d) (maxPairStart hG S d c))

/-- **Clause 2 of `P2` forbids interleaving maximal extensions.**  On a
primitive `P2` truth, if two pairs of distinct starts each carry a common
`(L-1)`-mer and the four starts interleave, then the two maximal extensions
(`maxPair_isRepeat`, each a maximal repeat of length `≥ L - 1 > L - 2`) do
*not* interleave, in either ordering of the first pair.  This is the
non-interleaving property the chord worker consumes, and it is exactly what
`ExtCrossing` states. -/
theorem P2.imp_ExtCrossing (hG : 0 < G) (hL : 2 ≤ L) (_hLG : L ≤ G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S) :
    ExtCrossing hG L S := by
  have hℓ1 : 1 ≤ L - 1 := by omega
  have hℓG : L - 1 ≤ G := by omega
  intro a b c d hab hcd hab' hcd' hI
  obtain ⟨hR₁, hℓ1'⟩ :=
    maxPair_isRepeat hG S hprim hab hℓ1 hℓG (agree_of_nodeWindow_eq hG S hab')
  obtain ⟨hR₂, hℓ2'⟩ :=
    maxPair_isRepeat hG S hprim hcd hℓ1 hℓG (agree_of_nodeWindow_eq hG S hcd')
  have hsw : (mkGenome hG S).IsRepeat (maxPairLen hG S a b)
      (maxPairStart hG S b a) (maxPairStart hG S a b) :=
    (Genome.IsRepeat_comm (mkGenome hG S) (maxPairLen hG S a b)
      (maxPairStart hG S a b) (maxPairStart hG S b a)).mp hR₁
  refine ⟨?_, ?_⟩
  · intro hI'
    have hP := hP2.2 ⟨maxPairLen hG S a b, hR₁.2.1⟩
      ⟨maxPairLen hG S c d, hR₂.2.1⟩
      (maxPairStart hG S a b) (maxPairStart hG S b a)
      (maxPairStart hG S c d) (maxPairStart hG S d c) hR₁ hR₂ hI'
    simp only [Fin.val_mk] at hP
    rcases hP with hP | hP <;> omega
  · intro hI'
    have hP := hP2.2 ⟨maxPairLen hG S a b, hR₁.2.1⟩
      ⟨maxPairLen hG S c d, hR₂.2.1⟩
      (maxPairStart hG S b a) (maxPairStart hG S a b)
      (maxPairStart hG S c d) (maxPairStart hG S d c) hsw hR₂ hI'
    simp only [Fin.val_mk] at hP
    rcases hP with hP | hP <;> omega

/-! ## 6b. The two (R2) consequences for the primitivity of `thm:BBT`

`p2_spectrum_unique_up_to_rotation` carries `PopulationReduction.IsPrimitive`
as `_hPrimS`.  With `IsPrimitive.shiftPrimitive` the two (R2) consequences are
therefore available under exactly the hypothesis the paper states. -/

/-- **(R2a) for the primitivity of `thm:BBT`**: every `(L-1)`-mer of a
non-power `P2` truth is spelled at most twice. -/
theorem P2.imp_nodeCount_le_two_of_powerPrimitive (hG : 0 < G) (hL : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hprim : PopulationReduction.IsPrimitive S)
    (hP2 : P2 hG L S) :
    ∀ k : Fin (L - 1) → α, nodeCount (L := L) hG S k ≤ 2 :=
  P2.imp_nodeCount_le_two hG hL hLG S (IsPrimitive.shiftPrimitive hG hprim) hP2

/-- **(R2b) for the primitivity of `thm:BBT`**: the maximal extensions of two
interleaving double-node pairs do not interleave. -/
theorem P2.imp_ExtCrossing_of_powerPrimitive (hG : 0 < G) (hL : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hprim : PopulationReduction.IsPrimitive S)
    (hP2 : P2 hG L S) : ExtCrossing hG L S :=
  P2.imp_ExtCrossing hG hL hLG S (IsPrimitive.shiftPrimitive hG hprim) hP2

/-! ## 7. Kernel-checked counterexamples: the "same starts" (R1) and
`NodeCrossing` (R2b) versions are false

The word is `S = A A B A B` (`G = 5`), read at `L = 3`, so the de Bruijn nodes are
the `2`-mers.  It is **primitive** (`G = 5` is prime and the word is not
constant), and it satisfies **actual `P2`** at `L = 3`
(`cex_is_p2`): the only repeated `2`-mers are `01` (at starts `1, 3`) and `10`
(at starts `2, 4`), each occurring exactly twice, so there is no maximal triple
repeat of length `≥ 2` at all; and the two occurrence pairs *do* interleave,
while neither pair is a maximal repeat (the two copies of `10` are preceded by
the same symbol), so clause 2 is vacuous.

The three facts below are what force the corrections of §5 and §6. -/

/-- `S = AABAB` on five positions. -/
def cexWord : Fin 5 → PopulationReduction.Bin :=
  ![Bin.A, Bin.A, Bin.B, Bin.A, Bin.B]

/-- `AABAB` is primitive: no shift by `0 < s < 5` preserves it.  (Checked
against the shift-invariance definition, `RepeatAdapter.IsPrimitive`.) -/
theorem cex_is_shiftPrimitive :
    RepeatAdapter.IsPrimitive (hG := by norm_num) cexWord := by
  intro s hs0 hsG
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · intro hcon
    exact absurd (hcon 1) (by decide)
  · intro hcon
    exact absurd (hcon 0) (by decide)
  · intro hcon
    exact absurd (hcon 1) (by decide)
  · intro hcon
    exact absurd (hcon 0) (by decide)

/-- Clause 1 of `P2` for `cexWord` at `L = 3`, over the admissible repeat
lengths `e < 5` (which is all `IsTripleRepeat` allows). -/
theorem cex_clause1 : ∀ (e : Fin 5) (a b c : Fin 5),
    (mkGenome (hG := by norm_num) (S := cexWord)).IsTripleRepeat e a b c →
      e.val < 2 := by
  unfold mkGenome
  decide

/-- Clause 2 of `P2` for `cexWord` at `L = 3`, over the admissible repeat
lengths `e < 5`. -/
theorem cex_clause2 : ∀ (e₁ e₂ : Fin 5) (a b c d : Fin 5),
    (mkGenome (hG := by norm_num) (S := cexWord)).IsRepeat e₁ a b →
    (mkGenome (hG := by norm_num) (S := cexWord)).IsRepeat e₂ c d →
    Interleaved (mkGenome (hG := by norm_num) (S := cexWord)) a b c d →
      e₁.val ≤ 1 ∨ e₂.val ≤ 1 := by
  unfold mkGenome
  decide

/-- **`cexWord` satisfies the repository's actual `P2` at `L = 3`.** -/
theorem cex_is_p2 : P2 (hG := by norm_num) (L := 3) (S := cexWord) := by
  refine ⟨?_, ?_⟩
  · intro e a b c h
    exact cex_clause1 e a b c h
  · intro e₁ e₂ a b c d h₁ h₂ hI
    have h₁5 : e₁ < (mkGenome (hG := by norm_num) (S := cexWord)).len := h₁.2.1
    have h₂5 : e₂ < (mkGenome (hG := by norm_num) (S := cexWord)).len := h₂.2.1
    exact cex_clause2 ⟨e₁, h₁5⟩ ⟨e₂, h₂5⟩ a b c d h₁ h₂ hI

/-- **`P2` does *not* imply `NodeCrossing`.**  On `S = AABAB` at `L = 3` the
`2`-mer `01` occurs exactly at starts `1, 3` and `10` exactly at starts `2, 4`,
and those four starts interleave.  So the residual of
`docs/issue89-spectrum-uniqueness.md` §3(R2) — "`P2` gives `NodeCrossing`" — is
false, and the corrected statement is `ExtCrossing` (§6). -/
theorem cex_not_NodeCrossing :
    ¬ NodeCrossing (hG := by norm_num) (L := 3) (S := cexWord) := by
  unfold NodeCrossing mkGenome
  decide

/-- **(R1) at the *same* starts is false.**  On `S = AABAB` at `L = 3` the
starts `2, 4` carry the common `2`-mer `10` (see `cex_pair_agrees`), but there
is **no** `e` with `2 ≤ e < 5` for which the two copies are a maximal repeat:
they are preceded by the same symbol, so the repeat is never left-maximal at
these starts.  The maximal extension exists only at the shifted starts, which is
what `maxPair_isRepeat` proves. -/
theorem cex_pair_agrees : ∀ d : Fin 2,
    (mkGenome (hG := by norm_num) (S := cexWord)).window 2 (2 : Fin 5) d
      = (mkGenome (hG := by norm_num) (S := cexWord)).window 2 (4 : Fin 5) d := by
  unfold mkGenome
  decide

theorem cex_not_maximalRepeat_at_same_starts :
    ∀ e : Fin 4, ¬ (mkGenome (hG := by norm_num) (S := cexWord)).IsRepeat
      ((e : ℕ) + 2) (2 : Fin 5) (4 : Fin 5) := by
  have h4 : ∀ k : Fin 4, ¬ (Genome.mk 5 (by norm_num) cexWord).IsRepeat
      ((k : ℕ) + 2) (2 : Fin 5) (4 : Fin 5) := by
    intro k
    fin_cases k <;> decide
  unfold mkGenome
  exact h4

/-- **The backward chain of a chord stops one step past `pairBack`.**  If
`a ≠ b` and `S` is primitive, the pair `a, b` shifted back by
`pairBack a b + 1` does *not* carry a common `ℓ`-mer with `ℓ ≥ 1`: the two
copies are preceded by different symbols (`pairBack_succ`), and the preceding
symbol is read at the first position of the window.

Together with `chord_shift_left` this says the backward chain of the chord
`{a, b}` is *exactly* `{{a - j, b - j} : 0 ≤ j ≤ pairBack a b}`, and its head
is the deterministic maximal extension `{maxPairStart a b, maxPairStart b a}`. -/
theorem not_chord_beyond_pairBack (hG : 0 < G) (S : Fin G → α)
    (hprim : RepeatAdapter.IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b) {L : ℕ}
    (hL : 2 ≤ L) :
    nodeWindow (L := L) hG S
        ⟨(a.val + G - pairBack hG S a.val b.val - 1) % G, Nat.mod_lt _ hG⟩ ≠
      nodeWindow (L := L) hG S
        ⟨(b.val + G - pairBack hG S a.val b.val - 1) % G, Nat.mod_lt _ hG⟩ := by
  intro hcon
  have hβlt : pairBack hG S a.val b.val < G := pairBack_lt_G hG S hprim hab
  have hne := pairBack_succ hG S a.val b.val hβlt
  have h1 : cyc hG S ((a.val + G - pairBack hG S a.val b.val - 1) % G + 0)
      = cyc hG S (a.val + G - pairBack hG S a.val b.val - 1) :=
    cyc_of_start hG S _ _
  have h2 : cyc hG S ((b.val + G - pairBack hG S a.val b.val - 1) % G + 0)
      = cyc hG S (b.val + G - pairBack hG S a.val b.val - 1) :=
    cyc_of_start hG S _ _
  have hthis : cyc hG S ((a.val + G - pairBack hG S a.val b.val - 1) % G + 0)
      = cyc hG S ((b.val + G - pairBack hG S a.val b.val - 1) % G + 0) := by
    have := congrFun hcon ⟨0, by omega⟩
    show cyc hG S (((a.val + G - pairBack hG S a.val b.val - 1) % G) + (0 : ℕ))
        = cyc hG S (((b.val + G - pairBack hG S a.val b.val - 1) % G) + (0 : ℕ))
    exact this
  exact hne (h1.symm.trans (hthis.trans h2))

end AssemblyP1.P2RepeatResidual
