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

/-- **The starts at which the `(L-1)`-mer `v` of the truth is spelled.** -/
def Fiber (v : Fin (L - 1) → α) : Finset (Fin G) := nodeStartsOf hG S v

theorem card_Fiber (v : Fin (L - 1) → α) : (Fiber hG L S v).card = nodeCount (L := L) hG S v :=
  card_nodeStartsOf hG S v

theorem mem_Fiber {v : Fin (L - 1) → α} {r : Fin G} :
    r ∈ Fiber hG L S v ↔ nodeWindow (L := L) hG S r = v := Iff.rfl

/-- A finset containing three distinct members has cardinality `≥ 3`. -/
private theorem card_ge_three {s : Finset (Fin G)} {a b c : Fin G}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset (Fin G)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | h | h
    · exact ha h
    · exact hb h
    · exact hc h
  have hcard : ({a, b, c} : Finset (Fin G)).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  exact le_trans hcard (Finset.card_le_card hsub)

/-! ## 1. The deterministic extension is a rotation of the pair -/

/-- **The shift coordinate is invariant under a common rotation of the two
starts.**  Together with `maxPairStart_rotAdd` below this is what makes the
deterministic maximal extension a property of the *pair* of starts and not of a
presentation of it. -/
theorem sh_rotAdd (t : ℕ) (a b : Fin G) :
    sh hG (rotAdd hG t a) (rotAdd hG t b) = sh hG a b := by
  have key : rotAdd hG (sh hG a b) (rotAdd hG t a) = rotAdd hG t b := by
    calc rotAdd hG (sh hG a b) (rotAdd hG t a)
        = rotAdd hG (t + sh hG a b) a := rotAdd_add hG (sh hG a b) t a
      _ = rotAdd hG t (rotAdd hG (sh hG a b) a) := by rw [rotAdd_add]
      _ = rotAdd hG t b := rotAdd_sh hG a b
  rw [← key, sh_rotAdd_left, Nat.mod_eq_of_lt (sh_lt hG a b)]

/-- **The deterministic extension start of `a`, relative to `b`, is `a` rotated
back by the maximal backward agreement length of the pair.** -/
theorem maxPairStart_eq (a b : Fin G) :
    maxPairStart hG S a b = rotAdd hG (G - pairBack hG S a.val b.val) a := by
  unfold maxPairStart rotAdd
  rfl

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
    congr 1
    exact pairBack_comm hG S a.val b.val
  · have hkey : rotAdd hG (pairBack hG S a.val b.val)
        (rotAdd hG (G - pairBack hG S a.val b.val) a) = rotAdd hG G a := by
      rw [rotAdd_add]
      congr 1
      omega
    rwa [rotAdd_full] at hkey
  · have hkey : rotAdd hG (pairBack hG S a.val b.val)
        (rotAdd hG (G - pairBack hG S a.val b.val) b) = rotAdd hG G b := by
      rw [rotAdd_add]
      congr 1
      omega
    rwa [rotAdd_full] at hkey

/-! ## 2. The support chords of `AltF` are involution orbits of doubled pairs -/

/-- **A `(L-1)`-mer pair is *doubled*** if the vertex has multiplicity exactly
two and is realised at exactly the two starts `a` and `b`.  These are the
support pairs of the alternative traversal: `BBTCondense.branch` objects of the
condensed multigraph, together with their two occurrences. -/
def DoubledPair (a b : Fin G) : Prop :=
  nodeCount (L := L) hG S (vtx hG L S a) = 2 ∧
    (∀ x : Fin G, nodeWindow (L := L) hG S x = vtx hG L S a → x = a ∨ x = b) ∧
    vtx hG L S b = vtx hG L S a

instance (a b : Fin G) : Decidable (DoubledPair hG L S a b) := by
  unfold DoubledPair
  infer_instance

/-- **The support of a permutation of the starts**: the starts at which the
alternative traversal genuinely re-pairs, i.e. the ends of its chords. -/
def Support (f : Fin G → Fin G) : Finset (Fin G) :=
  Finset.univ.filter (fun x => f x ≠ x)

theorem mem_Support {f : Fin G → Fin G} {x : Fin G} :
    x ∈ Support f ↔ f x ≠ x := Iff.rfl

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
  have hcap : ∀ v : Fin (L - 1) → α, (Fiber hG L S v).card ≤ 2 := by
    intro v
    rw [card_Fiber]
    exact P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 v
  have hinj : Function.Injective (AltF hG σ) := AltF_bijective hG σ |>.1
  by_cases hfix : AltF hG σ x = x
  · rw [hfix]
    exact hfix
  · have h2 : AltF hG σ (AltF hG σ x) ≠ AltF hG σ x := by
      intro h
      exact hfix (hinj h)
    have h3 : AltF hG σ (AltF hG σ x) ≠ x := by
      intro h
      exact h2 (h ▸ rfl)
    have ha : x ∈ Fiber hG L S (vtx hG L S x) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hb : AltF hG σ x ∈ Fiber hG L S (vtx hG L S x) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (AltF_vtx' hG L S σ hEul x).symm⟩
    have hc : AltF hG σ (AltF hG σ x) ∈ Fiber hG L S (vtx hG L S x) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := AltF_vtx' hG L S σ hEul (AltF hG σ x)
      rwa [this]
    exact absurd (hcap (vtx hG L S x) (card_ge_three ha hb hc (Ne.symm hfix) h3 h2)) (by omega)

/-- **A two-element orbit of `AltF` is a transposition of a doubled
`(L-1)`-mer pair.**  The two occurrences it exchanges are exactly the two
realisations of one branch object of the condensed multigraph --- which is what
a chord of the alternative traversal is. -/
theorem orbit_is_doubledPair {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (hP2 : P2 hG L S) {a b : Fin G} (hab : a ≠ b) (hfx : AltF hG σ a = b) :
    DoubledPair hG L S a b := by
  have hfb : AltF hG σ b = a := by rw [← AltF_sq hEul hL hLG hprim hP2 a, hfx]
  have hcap : ∀ v : Fin (L - 1) → α, (Fiber hG L S v).card ≤ 2 := by
    intro v
    rw [card_Fiber]
    exact P2.imp_nodeCount_le_two hG hL hLG S hprim hP2 v
  have hvb : vtx hG L S b = vtx hG L S a := (AltF_vtx' hG L S σ hEul a).symm
  have ha : a ∈ Fiber hG L S (vtx hG L S a) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hb : b ∈ Fiber hG L S (vtx hG L S a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvb⟩
  -- the fibre has at most two members and already contains the two distinct
  -- members `a, b`, so it *is* `{a, b}`
  have hsub : ({a, b} : Finset (Fin G)) ⊆ Fiber hG L S (vtx hG L S a) := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | h
    · exact ha h
    · exact hb h
  have hcard2 : (({a, b} : Finset (Fin G))).card = 2 :=
    Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩
  have hcard : (Fiber hG L S (vtx hG L S a)).card = 2 :=
    le_antisymm (hcap _) (le_trans hcard2 (Finset.card_le_card hsub))
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard
  have hsubxy : ({a, b} : Finset (Fin G)) ⊆ ({x, y} : Finset (Fin G)) := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with h | h
    · rw [hset] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton, or_false] at ha
      exact ha
    · rw [hset] at hb
      simp only [Finset.mem_insert, Finset.mem_singleton, false_or] at hb
      exact hb
  refine ⟨by rw [card_Fiber, hcard], ?_, hvb⟩
  intro x hx
  rw [← Finset.Subset.antisymm hsubxy (Finset.Subset.rfl : ({x, y} : Finset (Fin G))
    ⊆ ({x, y} : Finset (Fin G))), hset] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton, or_false] at hx
  exact hx

/-- **A support point of `AltF` is exchanged with a support point carrying the
same `(L-1)`-mer.**  Together with `AltF_sq` and `orbit_is_doubledPair` this
says: the support of the alternative traversal is a set of chords, each chord
being a pair of occurrences of one branch object, and `f` exchanges the two
ends of each chord. -/
theorem AltF_support_swap {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (hP2 : P2 hG L S) {a : Fin G} (hne : AltF hG σ a ≠ a) (b : Fin G) (hfx : AltF hG σ a = b) :
    AltF hG σ b = a ∧ vtx hG L S b = vtx hG L S a ∧ DoubledPair hG L S a b := by
  exact ⟨by rw [← AltF_sq hEul hL hLG hprim hP2 a, hfx],
    (AltF_vtx' hG L S σ hEul a).symm,
    orbit_is_doubledPair hEul hL hLG hprim hP2 hne hfx⟩

/-! ## 3. The deterministic maximal repeat is unique -/

/-- **A maximal repeat determines its own length.**  Two maximal repeats at the
*same* pair of starts have the same length, so "the two deterministic maximal
extensions coincide" is a statement about one maximal repeat. -/
theorem isRepeat_len_unique {e e' : ℕ} {a b : Fin G}
    (h1 : (mkGenome hG S).IsRepeat e a b) (h2 : (mkGenome hG S).IsRepeat e' a b) :
    e = e' := by
  rcases lt_or_gt_of_ne (fun h => h rfl) with hlt | hlt
  · -- `e < e'`: the agreement at `e'` contradicts right-maximality at `e`
    have hag : ∀ d : Fin (e' - e), cyc hG S (a.val + d.val) = cyc hG S (b.val + d.val) := by
      intro d
      have h2d := h2.2.2.2 d
      have h1d := h1.2.2.2 ⟨d.val + e, by omega⟩
      simpa only [SourceFaithfulIs.Genome.Agree, SourceFaithfulIs.Genome.window,
        SourceFaithfulIs.Genome.cycl, cycl_mkGenome] using h2d.symm.trans h1d
    have hltG : e < G := h1.2.1
    have hfol : (mkGenome hG S).Following e a = (mkGenome hG S).Following e b := by
      have h := hag ⟨e' - e - 1, by omega⟩
      have h1' : (mkGenome hG S).Following e a = cyc hG S (a.val + e) := by
        simp only [SourceFaithfulIs.Genome.Following, len_mkGenome, cycl_mkGenome]
      have h2' : (mkGenome hG S).Following e b = cyc hG S (b.val + e) := by
        simp only [SourceFaithfulIs.Genome.Following, len_mkGenome, cycl_mkGenome]
      rw [h1', h2']
      have hkey : a.val + e + (e' - e - 1) = a.val + e' - 1 := by omega
      rw [← hkey] at h
      exact h
    exact absurd hfol h1.2.2.2.2
  · by_contra hcon
    exact absurd (h2 ▸ isRepeat_len_unique hG S h2 h1) (by omega)

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
    rw [← h5, ← h7, hc] at hne
    exact hne rfl
  refine ⟨ℓ, ℓ', hℓ, ?_, ?_, ?_, ?_⟩
  · rw [← h1', h1]
  · rw [← h2', h2]
  · rw [← h3', h3]
  · rw [← h4', h4]

/-- **The two chords of a ladder are parallel**: they have the same length, and
the offset between their left ends equals the offset between their right ends.
This is the chord identity that makes the collapse *invisible* to the traversal:
the alternative traversal moves both ends of each chord by the same amount, so it
reads the same `(L-1)`-mers at both ends. -/
theorem ladder_chord_identities {p q : Fin G} {ℓ ℓ' : ℕ}
    (ha : a = rotAdd hG ℓ p) (hb : b = rotAdd hG ℓ q)
    (hc : c = rotAdd hG ℓ' p) (hd : d = rotAdd hG ℓ' q) :
    sh hG a b = sh hG p q ∧ sh hG c d = sh hG p q ∧ sh hG a c = sh hG b d := by
  have key : ∀ (t : ℕ) (x y : Fin G),
      sh hG (rotAdd hG t x) (rotAdd hG t y) = sh hG x y := sh_rotAdd hG
  refine ⟨?_, ?_, ?_⟩
  · rw [ha, hb, key]
  · rw [hc, hd, key]
  · rw [ha, hc, key, hb, hd, key]

/-- **The common extension length of a ladder.**  If the two pairs of a ladder
have the same deterministic maximal extension, then their `maxPairLen` values
agree, and each is the length of a maximal repeat at `(p, q)`. -/
theorem ladder_len {a b c d p q : Fin G} (hprim : RepeatAdapter.IsPrimitive hG S)
    (h1 : maxPairStart hG S a b = p) (h2 : maxPairStart hG S b a = q)
    (h3 : maxPairStart hG S c d = p) (h4 : maxPairStart hG S d c = q)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hab : a ≠ b) (hcd : c ≠ d)
    (hagab : vtx hG L S a = vtx hG L S b) (hagcd : vtx hG L S c = vtx hG L S d) :
    maxPairLen hG S a b = maxPairLen hG S c d ∧ L - 1 ≤ maxPairLen hG S a b := by
  obtain ⟨hR₁, hℓ₁⟩ :=
    maxPair_isRepeat hG S hprim hab (by omega) (by omega) (agree_of_nodeWindow_eq hG S hagab)
  obtain ⟨hR₂, hℓ₂⟩ :=
    maxPair_isRepeat hG S hprim hcd (by omega) (by omega) (agree_of_nodeWindow_eq hG S hagcd)
  have h1' : maxPairStart hG S a b = p := h1
  have h2' : maxPairStart hG S b a = q := h2
  have h3' : maxPairStart hG S c d = p := h3
  have h4' : maxPairStart hG S d c = q := h4
  rw [h1', h2'] at hR₁
  rw [h3', h4'] at hR₂
  refine ⟨isRepeat_len_unique hG S hR₁ hR₂, le_trans (by omega) hℓ₁⟩

/-! ## 5. Why a ladder is benign: the two copies spell the same vertices -/

/-- **Inside one maximal repeat, the two shifted copies spell the same
`(L-1)`-mers.**  If `(e, p, q)` is a maximal repeat of the truth then
`vtx (p + i) = vtx (q + i)` for every `i + 1 ≤ e`: the two occurrences of the
repeat agree over its whole length, and so do all their common shifts.

This is the local reason a *ladder* --- a collapse of two chords onto one
maximal repeat --- is **invisible at the level of the vertex cycle**: the
alternative traversal's two chords move both ends by the same amount, and the
vertices read at the two ends of a chord are equal.  It is the ingredient any
completion of `LadderRotationGap` (§6) needs. -/
theorem ladder_arc_eq {e : ℕ} {p q : Fin G} (hL : 2 ≤ L)
    (hag : ∀ d : Fin e, cyc hG S (p.val + d.val) = cyc hG S (q.val + d.val))
    (he : L - 1 ≤ e) {i : ℕ} (hi : i + (L - 1) ≤ e) :
    vtx hG L S (rotAdd hG i p) = vtx hG L S (rotAdd hG i q) := by
  funext d
  change cyc hG S ((rotAdd hG i p).val + d.val) = cyc hG S ((rotAdd hG i q).val + d.val)
  unfold cyc
  congr 1
  apply Fin.ext
  have h1 : (rotAdd hG i p).val = (p.val + i) % G := rfl
  have h2 : (rotAdd hG i q).val = (q.val + i) % G := rfl
  rw [h1, h2, ← mod_add_shl (p.val + i) d.val, ← mod_add_shl (q.val + i) d.val]
  have hstep : i + d.val < e := by omega
  have hag' := hag ⟨i + d.val, hstep⟩
  unfold cyc at hag'
  have h1' : cyc hG S (p.val + (i + d.val)) = S (rotAdd hG (i + d.val) p) := by
    unfold cyc rotAdd
    rfl
  have h2' : cyc hG S (q.val + (i + d.val)) = S (rotAdd hG (i + d.val) q) := by
    unfold cyc rotAdd
    rfl
  rw [h1', h2'] at hag'
  exact congrArg S hag'

end AssemblyP1.BBTLadder
