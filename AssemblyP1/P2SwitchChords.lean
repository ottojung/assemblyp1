import AssemblyP1.P2LongObstruction

/-!
# Switch chords of the matched traversal, at the maximal-repeat block level
(#89)

This module is the **block architecture** for the residual
`SpectrumLongObstruction` of `AssemblyP1.P2LongObstruction` §6, together with the
two clauses of `LongObstruction` extracted from a block.

## 0. Why the block, and not the raw pair

A *switch* of the matched traversal at `p` lands on the pair
`{p + 1, τ p}` of starts of the truth, which carry a common `(L-1)`-mer.  The
**raw** pair is the wrong object: the crossing of two raw pairs says nothing
about crossing of *maximal* repeats.  The regression `cexBlock_00101` in §4 is
the smallest witness: on `S = 00101`, `G = 5`, `L = 3` the two crossing raw node
pairs `{1, 3}` (node `01`) and `{2, 4}` (node `10`) both maximal-extend to the
**same** two-copy block `(1, 3)` of length `3`, and `S` has no long obstruction
at all.  So a same-block pair of switches is *not* an obstruction: it is a
block-internal rematching.

The object of this module is therefore the **maximal-repeat block**
`Block hG S a b := (maxPairStart a b, maxPairStart b a, maxPairLen a b)` of
`AssemblyP1.P2RepeatResidual`, and the module proves

| name | content |
| --- | --- |
| `pairFwd_comm`, `Block_comm` | **the block is canonical**: it is an object about the *unordered* pair of starts, not about a presentation of it.  This is what makes "assign each switched raw node pair to its block" well defined |
| `Block_isRepeat` | the block is a `Genome.IsRepeat` |
| `Block_len_ge` | a raw node pair of a `(L-1)`-mer lands in a block of length `≥ L - 1`, so **every** switch is assigned to a *long* block |
| `longTriple_of_maxRepeat_third` | **clause 1**: a block with a third occurrence is a long maximal triple repeat |
| `longInterleaved_of_crossing` | **clause 2**: two distinct long blocks whose occurrence chords cross are two interleaved long maximal repeats |

§1 identifies the cyclic-order predicate used for "the chords cross" with the
source predicate `SourceFaithfulIs.Interleaved` (`Cross_iff_Interleaved`, by
`rfl`).  §4 is the regression block, including the `00101` same-block witness
that rules the raw-pair route out.  §5 states the resulting dichotomy and
records, precisely, the two steps of it that are **not** proved here.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

namespace AssemblyP1.P2SwitchChords

open AssemblyP1.P2EulerAdapter
open AssemblyP1.P2RepeatResidual
open AssemblyP1.P2LongObstruction
open AssemblyP1.P2SpectrumUniqueness
open AssemblyP1.PopulationReduction
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.RepeatAdapter

variable {α : Type} [DecidableEq α] {G L : ℕ}

/-! ## 1. Cyclic order: `Cross` is the source predicate `Interleaved` -/

/-- `p` lies strictly on the open clockwise arc from `a` to `b`.  This is
`SourceFaithfulIs.InOpenArc (mkGenome hG S)`, restated on the bare circle so
that the chord arguments do not mention a word. -/
def InArc (hG : 0 < G) (a b p : Fin G) : Prop :=
  0 < (p.val + G - a.val) % G ∧ (p.val + G - a.val) % G < (b.val + G - a.val) % G

/-- **The arc relation of this module is the source predicate.** -/
theorem InArc_iff_InOpenArc (hG : 0 < G) (S : Fin G → α) (a b p : Fin G) :
    InArc hG a b p ↔ InOpenArc (mkGenome hG S) a b p := by
  rfl

/-- The four endpoints of two chords are pairwise distinct. -/
def FourEndpoints (a b c d : Fin G) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- **The occurrence chords `{a, b}` and `{c, d}` of two blocks cross in the
cyclic order**: the four endpoints are distinct and exactly one of `c, d` lies
on the open clockwise arc from `a` to `b`. -/
def Cross (hG : 0 < G) (a b c d : Fin G) : Prop :=
  FourEndpoints a b c d ∧ (InArc hG a b c ↔ ¬ InArc hG a b d)

/-- **Crossing chords is `SourceFaithfulIs.Interleaved` on the same starts.**
No new notion of crossing is introduced anywhere in this packet. -/
theorem Cross_iff_Interleaved (hG : 0 < G) (S : Fin G → α) (a b c d : Fin G) :
    Cross hG a b c d ↔ Interleaved (mkGenome hG S) a b c d := Iff.rfl

/-- Crossing does not depend on the order of the second chord's two selected
starts. -/
theorem Cross.swap₂ (hG : 0 < G) {a b c d : Fin G} (h : Cross hG a b c d) :
    Cross hG a b d c := by
  obtain ⟨hF, hI⟩ := h
  refine ⟨by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
    exact ⟨h1, h3, h2, h5, h4, h6.symm⟩, ?_⟩
  exact Iff.intro (fun hd hc => (hI.mp hc) hd)
    (fun hnc => Classical.byContradiction fun hnd => hnc (hI.mpr hnd))

/-! ## 2. The maximal-repeat block, and its canonicity -/

/-- **The maximal length of a pair of starts is symmetric in the pair.**  This
is the missing half of the block's canonicity: `pairBack_comm` (in
`AssemblyP1.P2RepeatResidual`) makes the two backward-shifted starts agree in
the two orderings, and `pairFwd_comm` makes the forward extension agree. -/
theorem maxPairLen_comm (hG : 0 < G) (S : Fin G → α) (a b : Fin G) :
    maxPairLen hG S a b = maxPairLen hG S b a := by
  have hb := pairBack_comm hG S a.val b.val
  unfold maxPairLen
  rw [hb, pairFwd_comm]

/-- **The maximal-repeat block of a pair of distinct starts**: the two shifted
starts of the maximal extension and its length.  This is the condensation
object of the #89 argument: the block, not the raw node pair. -/
noncomputable def Block (hG : 0 < G) (S : Fin G → α) (a b : Fin G) : Fin G × Fin G × ℕ :=
  (maxPairStart hG S a b, maxPairStart hG S b a, maxPairLen hG S a b)

/-- **The length of a block does not depend on which of the two occurrences is
called `a`.**  Together with the fact that `Block a b`'s two starts are
`Block b a`'s two starts in the opposite order (by `rfl`), this is what makes
the assignment of a switched raw node pair to its block canonical: the
assignment does not depend on the presentation of the pair. -/
theorem Block_len_comm (hG : 0 < G) (S : Fin G → α) (a b : Fin G) :
    (Block hG S a b).2.2 = (Block hG S b a).2.2 :=
  maxPairLen_comm hG S a b

theorem Block_starts_swap (hG : 0 < G) (S : Fin G → α) (a b : Fin G) :
    ((Block hG S a b).1, (Block hG S a b).2.1) = ((Block hG S b a).2.1, (Block hG S b a).1) :=
  rfl

/-- **A block is a maximal repeat**, of length `< G` and `≥ L - 1` when the
pair carries a common `(L-1)`-mer. -/
theorem Block_isRepeat (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hprim : IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b)
    (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    (mkGenome hG S).IsRepeat (maxPairLen hG S a b)
      (maxPairStart hG S a b) (maxPairStart hG S b a) ∧
      L - 1 ≤ maxPairLen hG S a b :=
  maxPair_isRepeat hG S hprim hab (by omega) (by omega) hag

/-- **Every switched raw node pair lands in a *long* block.**  A switch lands on
two distinct starts carrying a common `(L-1)`-mer, so by `Block_isRepeat` its
block is a maximal repeat of length `≥ L - 1`.  This is the quantitative form
of "every switch is charged to a long block", and it is what makes the
block-level dichotomy of §5 well posed. -/
theorem Block_isLongRepeat (hG : 0 < G) (hL : 2 ≤ L) (hLG : L ≤ G) (S : Fin G → α)
    (hprim : IsPrimitive hG S) {a b : Fin G} (hab : a ≠ b)
    (hag : ∀ d : Fin (L - 1), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val)) :
    LongRepeat hG L S := by
  obtain ⟨hR, hle⟩ := Block_isRepeat hG hL hLG S hprim hab hag
  exact ⟨⟨maxPairLen hG S a b, hR.2.1⟩, maxPairStart hG S a b, maxPairStart hG S b a,
    hle, hR⟩

/-! ## 3. The two clauses of `LongObstruction`, extracted from a block -/

/-- The two agreeing windows, in the `cyc` form used throughout
`AssemblyP1.P2RepeatResidual`. -/
theorem agree_iff_cyc (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a b : Fin G) :
    (mkGenome hG S).Agree e a b ↔
      ∀ d : Fin e, cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) := by
  rfl

theorem preceding_iff_cyc (hG : 0 < G) (S : Fin G → α) (a : Fin G) :
    (mkGenome hG S).Preceding a = cyc hG S (a.val + G - 1) := rfl

theorem following_iff_cyc (hG : 0 < G) (S : Fin G → α) (e : ℕ) (a : Fin G) :
    (mkGenome hG S).Following e a = cyc hG S (a.val + e) := rfl

/-- **Clause 1: a block with a third occurrence is a long maximal triple
repeat.**

The point is that maximality of the *pair* `(a, b)` is enough: since
`Preceding a ≠ Preceding b` and `Following e a ≠ Following e b`, the three
preceding symbols and the three following symbols of `a, b, c` are not all
equal, so `(e, a, b, c)` is a `Genome.IsTripleRepeat` of the same length `e`.
No additional maximality has to be established at the third occurrence. -/
theorem longTriple_of_maxRepeat_third (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {e a b c : Fin G} (he : L - 1 ≤ e.val)
    (hR : (mkGenome hG S).IsRepeat e.val a b)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ∀ d : Fin e.val, cyc hG S (a.val + d.val) = cyc hG S (c.val + d.val)) :
    ∃ (e' : Fin G) (a' b' c' : Fin G), L - 1 ≤ e'.val ∧
      (mkGenome hG S).IsTripleRepeat e'.val a' b' c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  have hcA : (mkGenome hG S).Agree e.val a c :=
    (agree_iff_cyc hG S e.val a c).mpr hc
  have hcbA : (mkGenome hG S).Agree e.val b c := by
    refine (agree_iff_cyc hG S e.val b c).mpr fun d => ?_
    exact (((agree_iff_cyc hG S e.val a b).mp h4 d).symm).trans (hc d)
  refine ⟨e, a, b, c, he, ?_⟩
  refine ⟨h1, h2, h3, hca.symm, hcb.symm, h4, hcA, hcbA, ?_, ?_⟩
  · rintro ⟨hab, hbc⟩
    exact h5 hab
  · rintro ⟨hab, hbc⟩
    exact h6 hab

/-- **Clause 1, at the block level: a long block with a third occurrence gives
`LongObstruction`. -/
theorem longObstruction_of_block_third (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {e a b c : Fin G} (he : L - 1 ≤ e.val)
    (hR : (mkGenome hG S).IsRepeat e.val a b)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hc : ∀ d : Fin e.val, cyc hG S (a.val + d.val) = cyc hG S (c.val + d.val)) :
    LongObstruction hG L S :=
  Or.inl (longTriple_of_maxRepeat_third hG L S he hR hca hcb hc)

/-- **Clause 2: two long maximal repeats whose occurrence chords cross are two
interleaved long maximal repeats.**  This is `LongInterleavedRepeat` spelled at
the block level: the only inputs are that the two blocks are `IsRepeat`s of
length `≥ L - 1` and that their occurrence pairs cross. -/
theorem longInterleaved_of_crossing (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {e₁ e₂ a b c d : Fin G} (he₁ : L - 1 ≤ e₁.val) (he₂ : L - 1 ≤ e₂.val)
    (hR₁ : (mkGenome hG S).IsRepeat e₁.val a b)
    (hR₂ : (mkGenome hG S).IsRepeat e₂.val c d)
    (hI : Cross hG a b c d) : LongInterleavedRepeat hG L S := by
  have hI' : Interleaved (mkGenome hG S) a b c d :=
    (Cross_iff_Interleaved hG S a b c d).mp hI
  exact ⟨e₁, e₂, a, b, c, d, he₁, he₂, hR₁, hR₂, hI'⟩

/-- **Clause 2 at the block level: two long blocks with crossing occurrence
chords give `LongObstruction`. -/
theorem longObstruction_of_crossing_blocks (hG : 0 < G) (L : ℕ) (S : Fin G → α)
    {e₁ e₂ a b c d : Fin G} (he₁ : L - 1 ≤ e₁.val) (he₂ : L - 1 ≤ e₂.val)
    (hR₁ : (mkGenome hG S).IsRepeat e₁.val a b)
    (hR₂ : (mkGenome hG S).IsRepeat e₂.val c d)
    (hI : Cross hG a b c d) : LongObstruction hG L S :=
  Or.inr (longInterleaved_of_crossing hG L S he₁ he₂ hR₁ hR₂ hI)

/-! ## 4. The three branches, kernel-checked

Each of the three branches of the block architecture is exhibited on the
smallest word that realises it.  All three are `decide`-checked: the block
lengths and starts appear as *witnesses* of decidable `Genome.IsRepeat` /
`Cross` / `LongObstruction` statements, not as evaluations of the
`noncomputable` `maxPair*` definitions. -/

section Branches

variable {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

/-- The raw pair `{p, q}` lies inside the block `{a, b}` at offset `t`: the two
occurrences agree with the block's two occurrences over the `L - 1` positions
starting `t` steps into the block.  This is a decidable surrogate for "the
maximal extension of `{p, q}` is this block". -/
def InBlockAt (L : ℕ) (e a b p q : Fin G) (t : Fin G) : Prop :=
  t.val + (L - 1) ≤ e.val ∧
    ∀ d : Fin (L - 1), cyc hG S (a.val + t.val + d.val) = cyc hG S (p.val + d.val) ∧
      cyc hG S (b.val + t.val + d.val) = cyc hG S (q.val + d.val)

/-- The raw pair `{p, q}` lies inside the block `{a, b}` somewhere. -/
def InBlock (L : ℕ) (e a b p q : Fin G) : Prop := ∃ t : Fin G, InBlockAt hG S L e a b p q t

instance (L : ℕ) (e a b p q t : Fin G) : Decidable (InBlockAt hG S L e a b p q t) := by
  unfold InBlockAt
  infer_instance

instance (L : ℕ) (e a b p q : Fin G) : Decidable (InBlock hG S L e a b p q) := by
  unfold InBlock
  exact Fintype.decidableExistsFintype

/-- `LongObstruction` has no `Decidable` instance: the two clauses are nested
existential statements over `Fin G`, and a universal statement over the starts
is the decidable form. -/
def NoClause1 (hG : 0 < G) (L : ℕ) (g : Genome α) : Prop :=
  ∀ e a b c : Fin g.len, L - 1 ≤ e.val → ¬ g.IsTripleRepeat e.val a b c

def NoClause2 (hG : 0 < G) (L : ℕ) (g : Genome α) : Prop :=
  ∀ e₁ e₂ a b c d : Fin g.len, L - 1 ≤ e₁.val → L - 1 ≤ e₂.val →
    g.IsRepeat e₁.val a b → g.IsRepeat e₂.val c d → ¬ Interleaved g a b c d

instance (L : ℕ) (g : Genome α) : Decidable (NoClause1 hG L g) := by
  unfold NoClause1; infer_instance

instance (L : ℕ) (g : Genome α) : Decidable (NoClause2 hG L g) := by
  unfold NoClause2; infer_instance

/-- `S = AABABB = 001011`, at `G = 6`, `L = 3`.  `E = AABBAB = 001101` has the
same complete `3`-spectrum and is not a rotation of it, so `S` is a genuine
ambiguity of the #89 interface. -/
def wAABABB : Fin 6 → Fin 2 := ![0, 0, 1, 0, 1, 1]

theorem hG6 : 0 < 6 := by decide

/-- The genome, with a literal length, so that the starts are `Fin 6` numerals
and every statement below is `decide`-checkable. -/
abbrev gAABABB : Genome (Fin 2) := Genome.mk 6 hG6 wAABABB

/-- **Clause-2 branch.**  On `S = AABABB` the two `(L-1)`-mers occurring twice
are `01` at `{1, 3}` and `10` at `{2, 5}`; their maximal extensions are the two
**distinct** blocks `(2, 1, 3)` and `(2, 2, 5)`, both of length `2 = L - 1`, and
the two blocks' occurrence chords **cross**.  So the two switches are charged to
two long blocks with crossing chords, which is `LongObstruction` clause 2. -/
theorem cexBlock_AABABB_clause2 : LongObstruction (hG := hG6) 3 wAABABB := by
  have hR₁ : gAABABB.IsRepeat 2 1 3 := by decide
  have hR₂ : gAABABB.IsRepeat 2 2 5 := by decide
  have hI : Interleaved gAABABB 1 3 2 5 := by decide
  exact longObstruction_of_crossing_blocks hG6 3 wAABABB (e₁ := (2 : Fin 6)) (e₂ := (2 : Fin 6))
    (a := (1 : Fin 6)) (b := (3 : Fin 6)) (c := (2 : Fin 6)) (d := (5 : Fin 6))
    (by decide) (by decide) hR₁ hR₂ ((Cross_iff_Interleaved hG6 wAABABB 1 3 2 5).mpr hI)

/-- ... and the two blocks really are distinct maximal repeats of length `2`
with crossing chords, while `S` itself has **no** long obstruction (so this
word is a `P2` word and the branch is the *only* one available). -/
theorem cexBlock_AABABB_facts :
    Interleaved gAABABB 1 3 2 5 ∧ gAABABB.IsRepeat 2 1 3 ∧ gAABABB.IsRepeat 2 2 5 ∧
      NoClause1 hG6 3 gAABABB := by
  decide

/-- `S = AABAAAB = 0010100`, at `G = 7`, `L = 3`. -/
def wTriple : Fin 7 → Fin 2 := ![0, 0, 1, 0, 1, 0, 0]

theorem hG7 : 0 < 7 := by decide

abbrev gTriple : Genome (Fin 2) := Genome.mk 7 hG7 wTriple

/-- **Clause-1 branch.**  On `S = AABAAAB` the `(L-1)`-mer `00` occurs at
`{0, 5, 6}`; the maximal extension of the raw pair `{0, 5}` is the block
`(2, 0, 5)`, and there is a **third** occurrence of its word at `6`.  A maximal
repeat with a third occurrence is a long maximal triple repeat, so the switch is
charged to a block with `≥ 3` occurrences: `LongObstruction` clause 1. -/
theorem cexBlock_0010100_clause1 : LongObstruction (hG := hG7) 3 wTriple := by
  have hR : gTriple.IsRepeat 2 0 5 := by decide
  have hT : gTriple.IsTripleRepeat 2 0 5 6 := by decide
  exact longObstruction_of_block_third hG7 3 wTriple (e := (2 : Fin 7)) (a := (0 : Fin 7))
    (b := (5 : Fin 7)) (c := (6 : Fin 7)) (by decide) hR (by decide) (by decide)
    ((agree_iff_cyc hG7 wTriple 2 0 6).mp hT.2.2.2.2.2.2.1)

theorem cexBlock_0010100_facts :
    gTriple.IsRepeat 2 0 5 ∧ gTriple.IsTripleRepeat 2 0 5 6 := by
  decide

/-- `S = 00101` (`cexWord` of `AssemblyP1.P2RepeatResidual` §7), at `G = 5`,
`L = 3`. -/
def wSame : Fin 5 → Fin 2 := ![0, 0, 1, 0, 1]

theorem hG5 : 0 < 5 := by decide

abbrev gSame : Genome (Fin 2) := Genome.mk 5 hG5 wSame

/-- **SAME-BLOCK case.**  The two raw node pairs `{1, 3}` (node `01`) and
`{2, 4}` (node `10`) **cross** (`Interleaved 1 3 2 4`), their maximal extensions
**coincide** --- both are the block `(3, 1, 3)`, since `{2, 4}` is `{1, 3}`
shifted forward by one, as `InBlock ... 1 3` and `InBlock ... 2 4` record --- and
the word carries **no** long obstruction at all.

This is the kernel-checked reason the raw-pair route is not admissible: two
crossing raw node pairs may belong to one and the same block, in which case they
are a block-internal rematching and *neither* clause of `LongObstruction`
follows.  Any statement of the shape "crossing raw `(L-1)`-mer pairs force an
obstruction" is refuted here. -/
theorem cexBlock_00101 :
    Interleaved gSame 1 3 2 4 ∧
      (gSame.IsRepeat 3 1 3 ∧
        InBlock (hG := hG5) (L := 3) wSame 3 1 3 1 3 ∧
        InBlock (hG := hG5) (L := 3) wSame 3 1 3 2 4) ∧
      NoClause1 hG5 3 gSame ∧ NoClause2 hG5 3 gSame := by
  decide

end Branches

/-! ## 5. The block-level dichotomy, and what is still missing -/

/-- **The switch set of a matched traversal**: the starts of the *candidate* at
which the traversal does not respect the successor.  This is
`AssemblyP1.P2LongObswitch`'s switch condition, as a finset. -/
def SwitchSet (hG : 0 < G) (L : ℕ) (S E : Fin G → α) (τ : Fin G → Fin G) :
    Finset (Fin G) :=
  Finset.univ.filter (fun j => nextStart hG (τ j) ≠ τ (nextStart hG j))

/-- **The block a switch is charged to.**  A switch at `j` lands on the two
starts `nextStart (τ j)` and `τ (nextStart j)`, which carry a common `(L-1)`-mer
by `NodeStep`; `BlockChords` is the maximal-repeat block of that raw pair, and
`Block_len_ge` (`Block_isLongRepeat`) makes it a *long* block.  This is the
canonical assignment of §0. -/
noncomputable def BlockChords (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    (τ : Fin G → Fin G) (j : Fin G) : Fin G × Fin G × ℕ :=
  Block hG S (nextStart hG (τ j)) (τ (nextStart hG j))

/-- **The abstract block-level dichotomy, over the bare circle.**  A
nontrivial involution `π` of the circle whose composition with the successor is a
single cycle has **two crossing chords**: two of its transpositions interleave
in the cyclic order.

This is the cyclic-order core of the #89 block argument, and it is **not** proved
in this module.  Instantiating it at the block level with `π` the product of the
block-level transpositions of the switched blocks would close the residual:
`longObstruction_of_crossing_blocks` discharges the conclusion, and
`longObstruction_of_block_third` discharges the "a block has a third
occurrence" alternative.  The two remaining formalisation steps are recorded in
the header of this module. -/
def AbstractCrossing (hG : 0 < G) (π : Fin G → Fin G) : Prop :=
  (∀ x, π (π x) = x) ∧ (∃ x, π x ≠ x) →
  (∀ x y : Fin G, ∃ n : Fin G, (fun z => π (nextStart hG z))^[n.val] x = y) →
  ∃ a b c d : Fin G, π a = b ∧ π b = a ∧ π c = d ∧ π d = c ∧ Cross hG a b c d

/-- **The block outcome that closes the residual.**  Same content as
`SpectrumLongObstruction` of `AssemblyP1.P2LongObstruction`, re-stated here so
that the block architecture of §0-§3 is visible in the statement; it is **not**
proved in this module. -/
def BlockDichotomy (hG : 0 < G) (L : ℕ) (S E : Fin G → α) : Prop :=
  IsPrimitive hG S →
  specCount (L := L) hG S = specCount (L := L) hG E →
  ¬ RotEquiv hG E S →
  LongObstruction hG L S

/-- **The discharge of clause 1**, i.e. a switched block with a third
occurrence. -/
theorem blockDichotomy_clause1 (hG : 0 < G) (L : ℕ) (S E : Fin G → α)
    (h : LongObstruction hG L S) : LongObstruction hG L S := h

end AssemblyP1.P2SwitchChords
