import AssemblyP1.P2
import AssemblyP1.P2RepeatAdapter
import AssemblyP1.RepeatAdapter
import AssemblyP1.PopulationReduction

/-!
# `thm:BBT`: the `(L-1)`-mer multiplicity cap for a `P2` truth (issue #89)

`docs/bbt-unique-eulerian-89.md` §4, **Lemma 1**, *primitive branch*: for a
`P2` truth that is **not a nontrivial power**, every `(L-1)`-mer is spelled by
at most two starts --- the multiplicity clause of `thm:BBT`, and the bound
that makes the label-preserving permutation of an alternative Eulerian
traversal a product of disjoint transpositions.

## What this module is

Two statements, and nothing else:

* **`IsPrimitive.shiftPrimitive`** --- the primitivity bridge, *ported
  identically* from `AssemblyP1/P2RepeatResidual.lean` at commit `1c67a14`
  (kernel-proved there; that genome-side content is sound and is not
  re-derived, only re-expressed in current names).
  `PopulationReduction.IsPrimitive` --- "`S` is not an exact nontrivial power",
  the primitivity hypothesis the paper states and the one carried by
  `p2_spectrum_unique_up_to_rotation` --- implies
  `RepeatAdapter.IsPrimitive` --- "no shift by `0 < s < G` preserves the word",
  which is the hypothesis of Bresler's Lemma B as consumed by
  `RepeatAdapter.primitive_nodeCount_le_two`.  The engine: invariance by `s`
  makes `S` constant on the cosets of `gcd s G`, hence a `G / gcd s G`-fold
  repetition of its first symbols, i.e. an exact power; the reduction is the
  Euclidean `s ↦ G mod s`, valid because invariance by `s` iterates and `cyc`
  is `G`-periodic.  Without this bridge the multiplicity theorem does not
  apply to the primitivity hypothesis of the paper.
* **`P2.imp_nodeCount_le_two_of_powerPrimitive`** --- the exact theorem:

  ```text
  PopulationReduction.IsPrimitive S   (the truth is not a nontrivial power)
  P2 hG L S                           (no maximal triple repeat of length ≥ L-1)
  2 ≤ L ≤ G
  ⟹  ∀ k : Fin (L-1) → α, nodeCount (L := L) hG S k ≤ 2
  ```

  i.e. every node of the `(L-1)`-de Bruijn multigraph of the truth has
  throughput at most two.  It is the composition of three kernel-checked
  components, and this module states nothing new:

  * `AssemblyP1.P2.noLongTripleRepeat` (commit `7794603`): actual `P2` forbids
    a `RepeatAdapter.HasLongTripleRepeat`, i.e. the hypothesis of
    `extend_triple`;
  * `RepeatAdapter.primitive_nodeCount_le_two`: primitivity + that hypothesis
    give the per-node cap;
  * the ported `shiftPrimitive`, to read primitivity in the paper's terms.

## Scope, and what is deliberately absent

* **No periodic / nonprimitive branch.**  It is outside the population target
  (`docs/population-uniqueness-end-to-end-89.md` needs only the primitive
  multiplicity cap), so `three_congruent_of_minimal_period` and the periodic
  alternative of Lemma 1 are *not* here.
* **No `Ukkonen` variants**; `P2` is the source-faithful hypothesis and
  `P2.imp_Ukkonen` transfers it.
* **No chord, crossing or interleaving claim.**  `ExtCrossing` /
  `NodeCrossing` from the same old file are refuted
  (`BBTChords.raw_node_crossing_not_maximal`, `S = 00101`) and are not
  ported.
* **No re-proof of the two-sided extension.**  It is
  `RepeatAdapter.extend_triple`, reached only through
  `¬ RepeatAdapter.HasLongTripleRepeat`; the known-false *one-sided*
  maximality claim of `docs/bbt-unique-eulerian-89.md` §4 is used nowhere.

No `sorry`, no `admit`, no new axiom, no changed definition; `#print axioms`
for both theorems reports only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace AssemblyP1.P2Multiplicity

open SourceFaithfulIs
open OrientedRigidity
open AssemblyP1
open AssemblyP1.PopulationReduction
open AssemblyP1.RepeatAdapter

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-! ## 1. The primitivity bridge (`thm:BBT`'s primitivity hypothesis) -/


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


/-! ## 2. The multiplicity theorem -/

/-- **Lemma 1, primitive branch: every `(L-1)`-mer of a primitive `P2` truth
occurs at most twice.**  This is the `RepeatAdapter` Lemma-B statement with
the multiplicity hypothesis discharged by the source-faithful `P2` clause
(through `AssemblyP1.P2.noLongTripleRepeat`): every node of the `(L-1)`
de Bruijn multigraph of `S` has throughput at most two. -/
theorem P2.imp_nodeCount_le_two (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G)
    (S : Fin G → α) (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S) :
    ∀ k : Fin (L - 1) → α, nodeCount (L := L) hG S k ≤ 2 := by
  have hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L :=
    P2.noLongTripleRepeat hG hL S hP2
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

/-- **The exact theorem of this module: the `(L-1)`-mer multiplicity cap at
the paper's primitivity hypothesis.**  If the truth `S` is not an exact
nontrivial power (`PopulationReduction.IsPrimitive`), satisfies `P2` at read
length `L` with `2 ≤ L ≤ G`, then every `(L-1)`-mer of `S` is spelled by at
most two starts.

This is the multiplicity clause of `thm:BBT` (`docs/bbt-unique-eulerian-89.md`
§4, Lemma 1, primitive branch) in the terms of the population target: the
`(L-1)`-mer multigraph of the truth has every node of throughput `≤ 2`, so a
label-preserving permutation of the starts is a product of disjoint
transpositions.  The `Ukkonen` route transfers it verbatim, since
`P2.imp_Ukkonen` turns `P2` into `Ukkonen`. -/
theorem P2.imp_nodeCount_le_two_of_powerPrimitive (hG : 0 < G) (hL : 2 ≤ L)
    (hLG : L ≤ G) (S : Fin G → α) (hprim : PopulationReduction.IsPrimitive S)
    (hP2 : P2 hG L S) :
    ∀ k : Fin (L - 1) → α, nodeCount (L := L) hG S k ≤ 2 :=
  P2.imp_nodeCount_le_two hG hL hLG S (IsPrimitive.shiftPrimitive hG hprim) hP2

end AssemblyP1.P2Multiplicity
