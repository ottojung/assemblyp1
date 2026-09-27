import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.P2RepeatResidual

/-!
# The `#89` rematch layer for genuine `EulerianCycle`s: involution, ladder, ladder arcs

This module continues `AssemblyP1.P2RepeatResidual` (the R1/R2 layer of
`1c67a14`: `maxPairStart` / `maxPairLen` / `maxPair_isRepeat`,
`P2.imp_nodeCount_le_two`, `P2.imp_ExtCrossing`) and
`AssemblyP1.BBTUniqueEulerian` (the object `EulerianCycle`, the reformulation
`AltF`, and the innermost-chord step) by supplying the part those two do not
have: the statements that use the fact that `f := AltF hG σ` is the *actual*
alternative traversal of a genuine Eulerian cycle, and not an arbitrary
window-preserving permutation.

The audit (`e89b1d42`) and the exhaustive search recorded in
`docs/bbt-ladder-rematch-89.md` pin down the situation:

* the naive statement "crossing `AltF` transposition pairs have interleaving
  maximal extensions" is **false**: genuine `EulerianCycle`s on primitive `P2`
  words do have crossing raw pairs whose maximal extensions *collapse*
  (`S = 00101`, `G = 5`, `K = 2`; also `S = 0001001`, `G = 7`, `K = 3`);
* but in every such ("benign collapse") instance the **vertex cycle is still a
  rotation** of the truth's, so a collapse is not a counterexample to
  `UniqueEulerianCycle` --- it has to be *discharged*, not refuted.

## What is proved here

* **§1 — the deterministic extension is a rotation of the pair**
  (`sh_rotAdd`, `maxPairStart_eq`, `maxPairStart_rotAdd`).  The shift
  coordinate is invariant under a common rotation of the two starts, and the
  extension start of `a` is `a` rotated back by the maximal backward agreement
  `pairBack`, symmetrically in `b`.  This is what makes "the two pairs have the
  same maximal extension" a statement about two rotations of *one* pair.
* **§2 — the support chords of `AltF` are involution orbits of doubled pairs**
  (`AltF_sq`, `orbit_is_doubledPair`, `AltF_support_swap`).  In the genuine
  Eulerian setting, under `P2` and primitivity, `f = AltF hG σ` is an
  **involution** preserving the `(L-1)`-mer, so every orbit is a singleton or a
  *transposition of a doubled `(L-1)`-mer pair*: the two realisations of one
  branch object of the condensed multigraph.  This is what makes the support of
  `f` a set of genuine chords, and it is the object the rematch step needs.
* **§3 — the deterministic maximal repeat is unique** (`isRepeat_len_unique`):
  a maximal repeat determines its own length, so two pairs with the same
  extension have the same extension *length*.
* **§4 — the rematch / ladder theorem** (`ladder_of_coalescing`,
  `ladder_chord_identities`, `ladder_len`): if two transposition orbits of `f`
  have the same deterministic maximal extension `(e, p, q)`, then the two pairs
  are the images of the *one* pair `{p, q}` under two **distinct** rotations,
  `a = p + ℓ`, `b = q + ℓ`, `c = p + ℓ'`, `d = q + ℓ'` with `ℓ ≠ ℓ'`; the two
  chords are **parallel** (same length `sh a b = sh c d = sh p q`, same spacing
  `sh a c = sh b d`), and the common extension length is that of the ladder's
  maximal repeat.  This is the "collapse forms a ladder" structure.
* **§5 — why a ladder is benign** (`ladder_arc_eq`): inside one maximal repeat
  the two shifted copies spell the *same* vertices, `vtx (p + i) = vtx (q + i)`
  for `i + 1 ≤ e`; so a ladder is invisible at the level of the vertex cycle,
  which is the local reason a collapse cannot manufacture a new vertex cycle.

## What is still missing

`LadderRotationGap` (§6) is the remaining step, as a `Prop` with **no
inhabitant**: in the genuine Eulerian setting, if the transposition orbits of
`f` coalesce into one maximal repeat (a ladder), then the vertex cycle of the
alternative traversal is a rotation of the truth's.  §4--§5 make the statement
precise and reduce it to the block structure of the support of `f`; the
combinatorial core --- that the block permutation `Φ = f ∘ nextSupport` moves
only whole ladder pairs, or equivalently that the two copies of each ladder
offset cut off equal vertex blocks --- is *not* proved here.

Exhaustive search (`scripts/verify_ladder_rematch_89.py`) over all primitive
binary and ternary words of length `≤ 9`, all `2 ≤ L ≤ G`, and every
window-preserving involution whose `f ∘ nextPos` is a `G`-cycle: 192260 genuine
traversals, of which 17746 have a non-trivial support; in **all** of them the
vertex cycle is a rotation of the truth's, and in all of them the support chords
that cross coalesce into a single maximal repeat ("one ladder") in 17628 cases
and into two ladders in 118 cases.  This is evidence, not a proof: the
completeness of the search is not itself proved.  No `sorry`, no `admit`, no new
axiom.
-/

namespace AssemblyP1.BBTLadder

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.P2RepeatResidual

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

/-- A finset containing three distinct members has cardinality `≥ 3`. -/
private theorem card_ge_three {s : Finset (Fin G)} {a b c : Fin G}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset (Fin G)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, false_or] at hx
    rcases hx with h | h | h
    · exact h ▸ ha
    · exact h ▸ hb
    · exact h ▸ hc
  have hcard : (({a, b, c} : Finset (Fin G))).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  exact le_trans hcard.ge (Finset.card_le_card hsub)

/-! ## 1. The deterministic extension is a rotation of the pair -/

/-- **The shift coordinate is invariant under a common rotation of the two
starts.**  Together with `maxPairStart_rotAdd` below this is what makes the
deterministic maximal extension a property of the *pair* of starts and not of a
presentation of it. -/
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

/-- **The deterministic extension start of `a`, relative to `b`, is `a` rotated
back by the maximal backward agreement length of the pair.** -/
theorem maxPairStart_eq (a b : Fin G) :
    maxPairStart hG S a b = rotAdd hG (G - pairBack hG S a.val b.val) a := by
  unfold maxPairStart rotAdd
  apply Fin.ext
  show (a.val + G - pairBack hG S a.val b.val) % G
      = (a.val + (G - pairBack hG S a.val b.val)) % G
  have hβle : pairBack hG S a.val b.val ≤ G := (pairBack_spec hG S a.val b.val).2
  rw [Nat.add_sub_assoc hβle]

/-- **The deterministic maximal extension of the pair `(a, b)` is the pair
`(a, b)` rotated back by its maximal backward agreement length** --- the same
`pairBack` for both ends, by `pairBack_comm`.  So the extension is *canonical*,
and two pairs with the same extension are two rotations of one and the same
pair: this is the algebraic content of "the collapse forms a ladder". -/
theorem maxPairStart_rotAdd (a b : Fin G) :
    ∃ ℓ : ℕ, maxPairStart hG S a b = rotAdd hG (G - ℓ) a ∧
      maxPairStart hG S b a = rotAdd hG (G - ℓ) b ∧
      rotAdd hG ℓ (maxPairStart hG S a b) = a ∧
      rotAdd hG ℓ (maxPairStart hG S b a) = b := by
  refine ⟨pairBack hG S a.val b.val, maxPairStart_eq hG S a b, ?_, ?_, ?_⟩
  · rw [maxPairStart_eq]
    unfold rotAdd
    apply Fin.ext
    show (b.val + (G - pairBack hG S b.val a.val)) % G
        = (b.val + (G - pairBack hG S a.val b.val)) % G
    rw [← pairBack_comm hG S b.val a.val]
  · have hβle : pairBack hG S a.val b.val ≤ G := (pairBack_spec hG S a.val b.val).2
    have hsum : pairBack hG S a.val b.val + (G - pairBack hG S a.val b.val) = G := by omega
    have hkey : rotAdd hG (pairBack hG S a.val b.val)
        (rotAdd hG (G - pairBack hG S a.val b.val) a) = rotAdd hG G a := by
      rw [rotAdd_add hG (pairBack hG S a.val b.val) (G - pairBack hG S a.val b.val) a, hsum]
    rw [maxPairStart_eq, hkey, rotAdd_full]
  · have hβle : pairBack hG S a.val b.val ≤ G := (pairBack_spec hG S a.val b.val).2
    have hsum : pairBack hG S a.val b.val + (G - pairBack hG S a.val b.val) = G := by omega
    have hkey : rotAdd hG (pairBack hG S a.val b.val)
        (rotAdd hG (G - pairBack hG S a.val b.val) b) = rotAdd hG G b := by
      rw [rotAdd_add hG (pairBack hG S a.val b.val) (G - pairBack hG S a.val b.val) b, hsum]
    rw [maxPairStart_eq, ← pairBack_comm hG S b.val a.val, hkey, rotAdd_full]

/-! ## 2. The support chords of `AltF` are involution orbits of doubled pairs -/

/-- **A `(L-1)`-mer pair is *doubled*** if the vertex has multiplicity exactly
two and is realised at exactly the two starts `a` and `b`.  These are the
support pairs of the alternative traversal: `BBTCondense.branch` objects of the
condensed multigraph, together with their two occurrences. -/
def DoubledPair (a b : Fin G) : Prop :=
  nodeCount (L := L) hG S (vtx hG L S a) = 2 ∧
    (∀ x : Fin G, nodeWindow (L := L) hG S x = vtx hG L S a → x = a ∨ x = b) ∧
    vtx hG L S b = vtx hG L S a

instance (a b : Fin G) : Decidable (DoubledPair (L := L) hG S a b) := by
  unfold DoubledPair
  infer_instance

/-- **The support of a permutation of the starts**: the starts at which the
alternative traversal genuinely re-pairs, i.e. the ends of its chords. -/
def Support (f : Fin G → Fin G) : Finset (Fin G) :=
  Finset.univ.filter (fun x => f x ≠ x)

theorem mem_Support {f : Fin G → Fin G} {x : Fin G} :
    x ∈ Support f ↔ f x ≠ x := by simp [Support]

/-- **`AltF` preserves the `(L-1)`-mer at every start**: the `traverses` clause
of `EulerianCycle`, read on the alternative traversal. -/
theorem AltF_vtx' {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ) (q : Fin G) :
    vtx hG L S (AltF hG σ q) = vtx hG L S q :=
  AltF_vtx hG L S σ hEul.1 q

/-- **`AltF` is an involution.**  In the genuine Eulerian setting, under `P2`
and primitivity, the alternative traversal `f = AltF hG σ` sends each start to
another start carrying the same `(L-1)`-mer, and every `(L-1)`-mer is spelled at
most twice (`P2.imp_nodeCount_le_two`).  Hence `x`, `f x` and `f (f x)` all lie
in the fibre of `vtx x`; injectivity of `f` makes them pairwise distinct unless
`f (f x) = x`, and a fibre of size `≤ 2` forces `f (f x) = x`.

This is the statement that turns the support of `f` into a set of genuine
*chords* of `BBTChords` rather than an arbitrary set of moving points, and it is
the input the rematch / ladder step consumes. -/
theorem AltF_sq {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G)
    (hprim : RepeatAdapter.IsPrimitive hG S) (hP2 : P2 hG L S) (x : Fin G) :
    AltF hG σ (AltF hG σ x) = x := by
  have hcap : ∀ v : Fin (L - 1) → α, (nodeStartsOf (L := L) hG S v).card ≤ 2 := by
    intro v
    rw [card_nodeStartsOf]
    exact P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 v
  have hinj : Function.Injective (AltF hG σ) := AltF_bijective hG σ |>.1
  by_cases h3 : AltF hG σ (AltF hG σ x) = x
  · exact h3
  · have hfix : AltF hG σ x ≠ x := by
      intro hz
      have : AltF hG σ (AltF hG σ x) = AltF hG σ x := congrArg (AltF hG σ) hz
      exact h3 (this.trans hz)
    have h2 : AltF hG σ (AltF hG σ x) ≠ AltF hG σ x := by
      intro hz
      exact hfix (hinj hz)
    have ha : x ∈ nodeStartsOf (L := L) hG S (vtx hG L S x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hb : AltF hG σ x ∈ nodeStartsOf (L := L) hG S (vtx hG L S x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, AltF_vtx' hG S hEul x⟩
    have hc : AltF hG σ (AltF hG σ x) ∈ nodeStartsOf (L := L) hG S (vtx hG L S x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (AltF_vtx' hG S hEul _).trans (AltF_vtx' hG S hEul x)⟩
    exact absurd (le_trans (card_ge_three ha hb hc (Ne.symm hfix) (Ne.symm h3) (Ne.symm h2)) (hcap (vtx hG L S x)))
      (by omega)

/-- **A two-element orbit of `AltF` is a transposition of a doubled
`(L-1)`-mer pair.**  The two occurrences it exchanges are exactly the two
realisations of one branch object of the condensed multigraph --- which is what
a chord of the alternative traversal is. -/
theorem orbit_is_doubledPair {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (hP2 : P2 hG L S) {a b : Fin G} (hab : a ≠ b) (hfx : AltF hG σ a = b) :
    DoubledPair (L := L) hG S a b := by
  have hfb : AltF hG σ b = a := by rw [← AltF_sq hG S hEul hL hLG hprim hP2 a, hfx]
  have hcap : ∀ v : Fin (L - 1) → α, (nodeStartsOf (L := L) hG S v).card ≤ 2 := by
    intro v
    rw [card_nodeStartsOf]
    exact P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 v
  have hvb : vtx hG L S b = vtx hG L S a := by
    rw [← hfx]
    exact AltF_vtx' hG S hEul a
  have ha : a ∈ nodeStartsOf (L := L) hG S (vtx hG L S a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hb : b ∈ nodeStartsOf (L := L) hG S (vtx hG L S a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvb⟩
  -- the fibre has at most two members and already contains the two distinct
  -- members `a, b`, so it *is* `{a, b}`
  have hsub : ({a, b} : Finset (Fin G)) ⊆ nodeStartsOf (L := L) hG S (vtx hG L S a) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · exact h ▸ ha
    · exact Finset.mem_singleton.mp h ▸ hb
  have hcard2 : (({a, b} : Finset (Fin G))).card = 2 :=
    Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩
  have hcard : (nodeStartsOf (L := L) hG S (vtx hG L S a)).card = 2 :=
    le_antisymm (hcap _) (le_trans hcard2.ge (Finset.card_le_card hsub))
  refine ⟨by rw [← card_nodeStartsOf, hcard], ?_, hvb⟩
  intro z hz
  have hz' : z ∈ nodeStartsOf (L := L) hG S (vtx hG L S a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
  by_cases hza : z = a
  · exact Or.inl hza
  by_cases hzb : z = b
  · exact Or.inr hzb
  exact absurd (le_trans (card_ge_three ha hb hz' hab (Ne.symm hza) (Ne.symm hzb))
    (hcap (vtx hG L S a))) (by omega)

/-- **A support point of `AltF` is exchanged with a support point carrying the
same `(L-1)`-mer.**  Together with `AltF_sq` and `orbit_is_doubledPair` this
says: the support of the alternative traversal is a set of chords, each chord
being a pair of occurrences of one branch object, and `f` exchanges the two
ends of each chord. -/
theorem AltF_support_swap {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (hP2 : P2 hG L S) {a : Fin G} (hne : AltF hG σ a ≠ a) (b : Fin G) (hfx : AltF hG σ a = b) :
    AltF hG σ b = a ∧ vtx hG L S b = vtx hG L S a ∧ DoubledPair (L := L) hG S a b := by
  have hab : a ≠ b := by rw [hfx] at hne; exact Ne.symm hne
  exact ⟨by rw [← AltF_sq hG S hEul hL hLG hprim hP2 a, hfx],
    by rw [← hfx]; exact AltF_vtx' hG S hEul a,
    orbit_is_doubledPair hG S hEul hL hLG hprim hP2 hab hfx⟩

/-! ## 3. The deterministic maximal repeat is unique -/

/-- **A maximal repeat determines its own length.**  Two maximal repeats at the
*same* pair of starts have the same length, so "the two deterministic maximal
extensions coincide" is a statement about one maximal repeat. -/
theorem isRepeat_len_unique {e e' : ℕ} {a b : Fin G}
    (h1 : (mkGenome hG S).IsRepeat e a b) (h2 : (mkGenome hG S).IsRepeat e' a b) :
    e = e' := by
  by_cases hlt : e < e'
  · -- right-maximality at `e` contradicts the agreement at `e'`
    have hstep : (mkGenome hG S).Following e a = (mkGenome hG S).Following e b :=
      h2.2.2.2.1 ⟨e, hlt⟩
    exact absurd hstep h1.2.2.2.2.2
  by_cases hgt : e' < e
  · have hstep : (mkGenome hG S).Following e' a = (mkGenome hG S).Following e' b :=
      h1.2.2.2.1 ⟨e', hgt⟩
    exact absurd hstep h2.2.2.2.2.2
  · omega

/-! ## 4. The rematch / ladder theorem -/

/-- **The rematch (ladder) structure.**  Suppose two pairs of starts of the
alternative traversal have the *same* deterministic maximal extension
`(p, q)`: `maxPairStart hG S a b = maxPairStart hG S c d = p` and
`maxPairStart hG S b a = maxPairStart hG S d c = q`.  Then the two pairs are
the images of the *one* pair `{p, q}` under two **distinct** rotations:
`a = p + ℓ`, `b = q + ℓ`, `c = p + ℓ'`, `d = q + ℓ'` with `ℓ ≠ ℓ'`.

In words: a *collapse* of two chords onto one maximal repeat is a **ladder** ---
two parallel shifts inside that repeat.  This is the structural replacement for
the false "crossing chords give two interleaved maximal repeats". -/
theorem ladder_of_coalescing {a b c d p q : Fin G} (hne : a ≠ c)
    (h1 : maxPairStart hG S a b = p) (h2 : maxPairStart hG S b a = q)
    (h3 : maxPairStart hG S c d = p) (h4 : maxPairStart hG S d c = q) :
    ∃ ℓ ℓ' : ℕ, ℓ ≠ ℓ' ∧ a = rotAdd hG ℓ p ∧ b = rotAdd hG ℓ q ∧
      c = rotAdd hG ℓ' p ∧ d = rotAdd hG ℓ' q := by
  obtain ⟨ℓ, h1', h2', h5, h6⟩ := maxPairStart_rotAdd hG S a b
  obtain ⟨ℓ', h3', h4', h7, h8⟩ := maxPairStart_rotAdd hG S c d
  have hℓ : ℓ ≠ ℓ' := by
    intro hc
    have : a = c := by rw [← h5, ← h7, h1, h3, hc]
    exact hne this
  refine ⟨ℓ, ℓ', hℓ, ?_, ?_, ?_, ?_⟩
  · rw [← h5, h1]
  · rw [← h6, h2]
  · rw [← h7, h3]
  · rw [← h8, h4]

/-- **The two chords of a ladder are parallel**: they have the same length, and
the offset between their left ends equals the offset between their right ends.
This is the chord identity that makes the collapse *invisible* to the traversal:
the alternative traversal moves both ends of each chord by the same amount, so it
reads the same `(L-1)`-mers at both ends. -/
theorem ladder_chord_identities {a b c d p q : Fin G} {ℓ ℓ' : ℕ}
    (ha : a = rotAdd hG ℓ p) (hb : b = rotAdd hG ℓ q)
    (hc : c = rotAdd hG ℓ' p) (hd : d = rotAdd hG ℓ' q) :
    sh hG a b = sh hG p q ∧ sh hG c d = sh hG p q := by
  have key : ∀ (t : ℕ) (x y : Fin G),
      sh hG (rotAdd hG t x) (rotAdd hG t y) = sh hG x y := sh_rotAdd hG
  refine ⟨?_, ?_⟩
  · rw [ha, hb, key]
  · rw [hc, hd, key]

/-- **The common extension length of a ladder.**  If the two pairs of a ladder
have the same deterministic maximal extension, then their `maxPairLen` values
agree, and each is the length of a maximal repeat at `(p, q)`. -/
theorem ladder_len {a b c d p q : Fin G} (hprim : RepeatAdapter.IsPrimitive hG S)
    (h1 : maxPairStart hG S a b = maxPairStart hG S c d)
    (h2 : maxPairStart hG S b a = maxPairStart hG S d c)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hab : a ≠ b) (hcd : c ≠ d)
    (hagab : vtx hG L S a = vtx hG L S b) (hagcd : vtx hG L S c = vtx hG L S d) :
    maxPairLen hG S a b = maxPairLen hG S c d ∧ L - 1 ≤ maxPairLen hG S a b := by
  obtain ⟨hR₁, hℓ₁⟩ :=
    maxPair_isRepeat (a := a) (b := b) hG S hprim hab (by omega) (by omega)
      (agree_of_nodeWindow_eq hG S hagab)
  obtain ⟨hR₂, hℓ₂⟩ :=
    maxPair_isRepeat (a := c) (b := d) hG S hprim hcd (by omega) (by omega)
      (agree_of_nodeWindow_eq hG S hagcd)
  have key : (mkGenome hG S).IsRepeat (maxPairLen hG S c d) (maxPairStart hG S a b)
      (maxPairStart hG S b a) := h2 ▸ (h1 ▸ hR₂)
  exact ⟨isRepeat_len_unique hG S hR₁ key,
    le_trans (by omega) hℓ₁⟩

/-! ## 5. Why a ladder is benign: the two copies spell the same vertices -/

/-- **Inside one maximal repeat, the two occurrences spell the same
`(L-1)`-mers.**  If `(e, p, q)` is a maximal repeat of the truth, i.e. the two
occurrences agree over its whole length, and `L - 1 ≤ e`, then the vertices at
`p` and `q` coincide: they carry the same `(L-1)`-mer. -/
theorem repeat_copies_vtx {e : ℕ} {p q : Fin G} (hL : 2 ≤ L)
    (hag : ∀ d : Fin e, cyc hG S (p.val + d.val) = cyc hG S (q.val + d.val))
    (he : L - 1 ≤ e) : vtx hG L S p = vtx hG L S q := by
  funext d
  change cyc hG S (p.val + d.val) = cyc hG S (q.val + d.val)
  exact hag ⟨d.val, by omega⟩

/-- **Congruent positions read the same symbol.** -/
theorem cyc_congr (x y : ℕ) (h : x % G = y % G) : cyc hG S x = cyc hG S y := by
  unfold cyc
  apply congrArg S
  apply Fin.ext
  exact h

/-- **Inside one maximal repeat, the two *shifted* copies spell the same
`(L-1)`-mers**: `vtx (p + i) = vtx (q + i)` whenever `i + (L-1)` still fits in
the repeat.  The two occurrences of the repeat agree over its whole length, and
so do all their common shifts.

This is the local reason a *ladder* --- a collapse of two chords onto one
maximal repeat --- is **invisible at the level of the vertex cycle**: the
alternative traversal's two chords move both ends by the same amount
(`ladder_of_coalescing`), and the vertices read at the two ends of a chord are
equal (`AltF_vtx'`).  It is the ingredient any completion of `LadderRotationGap`
needs. -/
theorem ladder_arc_eq {e : ℕ} {p q : Fin G} (hL : 2 ≤ L)
    (hag : ∀ d : Fin e, cyc hG S (p.val + d.val) = cyc hG S (q.val + d.val))
    (he : L - 1 ≤ e) {i : ℕ} (hi : i + (L - 1) ≤ e) :
    vtx hG L S (rotAdd hG i p) = vtx hG L S (rotAdd hG i q) := by
  funext d
  change cyc hG S ((rotAdd hG i p).val + d.val) = cyc hG S ((rotAdd hG i q).val + d.val)
  have e1 : ((rotAdd hG i p).val + d.val) % G = (p.val + (i + d.val)) % G := by
    rw [show (rotAdd hG i p).val = (p.val + i) % G from rfl,
      ← mod_add_shl (p.val + i) d.val, Nat.add_assoc]
  have e2 : ((rotAdd hG i q).val + d.val) % G = (q.val + (i + d.val)) % G := by
    rw [show (rotAdd hG i q).val = (q.val + i) % G from rfl,
      ← mod_add_shl (q.val + i) d.val, Nat.add_assoc]
  rw [cyc_congr hG S _ _ e1, cyc_congr hG S _ _ e2]
  have h1 : cyc hG S (p.val + (i + d.val))
      = S ⟨(p.val + (i + d.val)) % G, Nat.mod_lt _ hG⟩ := rfl
  have h2 : cyc hG S (q.val + (i + d.val))
      = S ⟨(q.val + (i + d.val)) % G, Nat.mod_lt _ hG⟩ := rfl
  have key : S ⟨(p.val + (i + d.val)) % G, Nat.mod_lt _ hG⟩
      = S ⟨(q.val + (i + d.val)) % G, Nat.mod_lt _ hG⟩ := by
    have hstep : cyc hG S (p.val + (i + d.val)) = cyc hG S (q.val + (i + d.val)) :=
      hag ⟨i + d.val, by omega⟩
    rw [← h1, ← h2]
    exact hstep
  exact key

/-! ## 6. The remaining gap, as a `Prop` with no inhabitant -/

/-- **The remaining step of the `#89` rematch route** (`LadderRotationGap`).

In the genuine Eulerian setting --- `σ` a presentation of an alternative
Eulerian cycle of the `(L-1)`-mer multigraph of a `P2` truth, `f = AltF hG σ` an
involution whose two-element orbits are doubled `(L-1)`-mer pairs --- suppose two
orbits of `f` **collapse** onto the same deterministic maximal extension, i.e.
`maxPairStart hG S a b = maxPairStart hG S c d` and
`maxPairStart hG S b a = maxPairStart hG S d c`.  Then the vertex cycle of `σ`
is a rotation of the truth's vertex cycle.

§4--§5 make this precise: the collapse is a **ladder**
(`ladder_of_coalescing`: the two pairs are two distinct rotations of the single
maximal repeat's pair, with equal chord lengths), and a ladder is vertex-invisible
(`ladder_arc_eq`, `AltF_vtx'`).  What is *not* proved is the combinatorial core:
that the block permutation of the alternative traversal, which is generated by
`Φ = f ∘ nextSupport` on the support of `f`, is vertex-compatible --- i.e. that
it moves only whole ladder pairs, or equivalently that the two copies of each
ladder offset cut off equal vertex blocks.  The naive replacement
("a collapse gives two *interleaved* maximal extensions") is **false**, refuted
by `S = 00101` (§`e89b1d42`), so the gap has to be closed in this form and not
in that one.

This is a `Prop`; it is **not** an inhabitant, and nothing in the library depends
on it. -/
def LadderRotationGap (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (hP2 : P2 hK L S)
    (hprim : RepeatAdapter.IsPrimitive hK S), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c →
        maxPairStart hK S a b = maxPairStart hK S c d →
        maxPairStart hK S b a = maxPairStart hK S d c →
        VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

end AssemblyP1.BBTLadder
