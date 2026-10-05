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
* **§6 — the support is a laminar family of ladder blocks**
  (`orbit_maxPair_isRepeat`, `support_blocks_nonCrossing`): every support chord
  extends to a maximal repeat of length `≥ L - 1`, and two *crossing* support
  chords do not have *crossing* maximal extensions.  Both are `P2` alone.

## What is still missing

`#89` reduces to two `Prop`s with **no inhabitant**, §7:

* `CrossingChordsCoalesce` --- the repeat-theoretic core: two crossing support
  chords must carry the **same** deterministic maximal extension.  This is the
  direction that was missing.  The earlier formulation made coalescence an
  *assumption*; it has to be *derived*, because the support need not be a single
  ladder: over binary `G ≤ 10` there are genuine traversals whose support spans
  **two** maximal repeats.
* `LadderVertexCycle` --- the global block lemma: a laminar family of ladder
  blocks, each vertex-invisible, forces the vertex listing to be a rotation.
  This replaces the previous `LadderRotationGap`, which was stated with a
  *local* antecedent (one pair of coalescing orbits) and a *global* conclusion,
  and so could not be applied to a support that does not coalesce.

§4--§6 make both precise; the combinatorial core that is *not* proved is that
the traversal walks the laminar blocks in the geometric order.  Note the target
is `VertexCycleEq`, never start-level equality and never `AltF = id`: `S = 00101`
has `f = (1 3)(2 4) ≠ id` and a correct `VertexCycleEq`.

Exhaustive search (`scripts/verify_ladder_blocks_89.py`) over all primitive
binary words of length `≤ 10` and ternary words of length `≤ 7`, all
`2 ≤ L ≤ G`, and every `(L-1)`-mer-preserving involution `f` whose
`f ∘ nextPos` is a `G`-cycle: 3770 genuine traversals with nontrivial support,
**zero** failures of `VertexCycleEq` and **zero** of `CrossingChordsCoalesce`.
The same search **refutes** the intermediate invariant
`nextSupport (f x) = f (nextSupport x)` (`nextSupport x` = next support point
clockwise): verified for `G ≤ 9` (1110 cases), refuted at `G = 10` by
`S = 0010010101`, `L = 5`, `f = (0 3)(1 8)(4 6)(5 7)`.  It also refutes
"the support is the disjoint union of the full ladders of all maximal repeats of
length `≥ L - 1`" (`S = 000101`, `L = 3`) and "the geometric gap lengths of a
ladder are equal" (`S = 00101`, `L = 3`: gaps of length 1 and 2).  This is
evidence, not a proof: the completeness of the search is not itself proved.
No `sorry`, no `admit`, no new `axiom`.
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
-- Repository convention (cf. `BBTFibrePeriod`, `P2RepeatResidual`): the
-- auto-included `[DecidableEq α]` section variable is not needed by every
-- lemma here.  This is a diagnostic about an unused *name*, not about a proof
-- obligation, and no theorem statement is weakened to obtain it.
-- Binder-level unused hypotheses are handled individually, by prefixing the
-- unused binder with `_` (which keeps it in the statement) rather than by
-- suppressing the `unusedVariables` linter module-wide.
set_option linter.unusedSectionVars false

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G) (S : Fin G → α)

/-- A finset containing three distinct members has cardinality `≥ 3`. -/
private theorem card_ge_three {s : Finset (Fin G)} {a b c : Fin G}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset (Fin G)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
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
agree, and each is at least `L - 1`.  (The `p, q` binders of an earlier
draft were vestigial and never appeared in the statement, so they are gone.) -/
theorem ladder_len {a b c d : Fin G} (hprim : RepeatAdapter.IsPrimitive hG S)
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
theorem repeat_copies_vtx {e : ℕ} {p q : Fin G} (_hL : 2 ≤ L)
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
theorem ladder_arc_eq {e : ℕ} {p q : Fin G} (_hL : 2 ≤ L)
    (hag : ∀ d : Fin e, cyc hG S (p.val + d.val) = cyc hG S (q.val + d.val))
    (_he : L - 1 ≤ e) {i : ℕ} (hi : i + (L - 1) ≤ e) :
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

/-! ## 6. The support is a laminar family of ladder blocks

The support of `f = AltF hG σ` splits into **blocks**: two support points are in
the same block when their transposition orbits carry the *same* deterministic
maximal extension.  Two facts about that decomposition are proved here.

* **§6.1** (`orbit_maxPair_isRepeat`) every transposition orbit of `f` sits in a
  maximal repeat of length `≥ L - 1`.  This is what makes the support chords
  *extensible* objects rather than raw `(L-1)`-mer pairs, and it is the input
  `P2.imp_ExtCrossing` needs.
* **§6.2** (`support_blocks_nonCrossing`) two **crossing** support chords do not
  have crossing maximal extensions --- the blocks are *laminar*.  This is
  `P2.imp_ExtCrossing` read at the support of `f`, i.e. exactly the "crossing
  deterministic maximal extensions contradict `P2`" ingredient the rematch route
  is organised around.

Both are consequences of `P2` alone; neither mentions the traversal beyond the
`vtx`-preservation `AltF_vtx'`. -/

/-- **A transposition orbit of `AltF` lies in a maximal repeat of length
`≥ L - 1`.**  The two ends of the chord carry the same `(L-1)`-mer
(`AltF_vtx'`), so their deterministic maximal extension (`maxPair_isRepeat`,
`R1` at `n = 2`) is a genuine `IsRepeat` of length at least `L - 1`, sitting at
the *shifted* starts `maxPairStart hG S a b` and `maxPairStart hG S b a`. -/
theorem orbit_maxPair_isRepeat {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (_hP2 : P2 hG L S) {a b : Fin G} (hab : a ≠ b) (hfx : AltF hG σ a = b) :
    (mkGenome hG S).IsRepeat (maxPairLen hG S a b)
        (maxPairStart hG S a b) (maxPairStart hG S b a) ∧
      L - 1 ≤ maxPairLen hG S a b :=
  maxPair_isRepeat hG S hprim hab (by omega) (by omega)
    (agree_of_nodeWindow_eq hG S (hfx ▸ AltF_vtx' hG S hEul a).symm)

/-- **Two crossing support chords do not have crossing maximal extensions.**
The blocks of the support are therefore *laminar*: crossing chords are
necessarily in the same block, and chords in different blocks never cross.

This is `P2.imp_ExtCrossing` instantiated at the support of the alternative
traversal: the two hypotheses `ExtCrossing` asks for are exactly
`vtx a = vtx b` and `vtx c = vtx d`, read off `AltF_vtx'`. -/
theorem support_blocks_nonCrossing {σ : Fin G ≃ Fin G} (hEul : EulerianCycle hG L S σ)
    (hL : 2 ≤ L) (hLG : L ≤ G) (hprim : RepeatAdapter.IsPrimitive hG S)
    (hP2 : P2 hG L S) {a b c d : Fin G}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hfx : AltF hG σ a = b) (hfd : AltF hG σ c = d)
    (hI : Interleaved (mkGenome hG S) a b c d) :
    ¬ Interleaved (mkGenome hG S) (maxPairStart hG S a b) (maxPairStart hG S b a)
        (maxPairStart hG S c d) (maxPairStart hG S d c) ∧
      ¬ Interleaved (mkGenome hG S) (maxPairStart hG S b a) (maxPairStart hG S a b)
        (maxPairStart hG S c d) (maxPairStart hG S d c) :=
  (P2.imp_ExtCrossing hG hL hLG S hprim hP2) a b c d hab hcd
    (hfx ▸ AltF_vtx' hG S hEul a).symm (hfd ▸ AltF_vtx' hG S hEul c).symm hI

/-! ## 7. The remaining step, as `Prop`s with no inhabitant

**The two statements are about *unordered* extension pairs, and this is
load-bearing.**  `Interleaved (mkGenome hK S) a b c d` is symmetric in `c` and
`d` (`SourceFaithfulIs.Interleaved` is `FourDistinct a b c d ∧ (InOpenArc a b c ↔
¬ InOpenArc a b d)`), so a hypothesis about `(a, b, c, d)` is a hypothesis about
`(a, b, d, c)` as well.  An *ordered* conclusion
`maxPairStart a b = maxPairStart c d ∧ maxPairStart b a = maxPairStart d c`
therefore cannot be right in general: it is refuted by `S = 00101`, `G = 5`,
`L = 3`, the genuine traversal `f = (1 3)(2 4)` (so `VertexCycleEq` holds and
`f ≠ id`), with `a = 1`, `b = 3`, `c = 4`, `d = 2`.  There `Interleaved 1 3 4 2`
holds, and the ordered conclusion reads `1 = 3 ∧ 3 = 1`, which is false; the
*unordered* conclusion holds, because `maxPairStart 1 3 = 1`,
`maxPairStart 3 1 = 3`, `maxPairStart 4 2 = 3`, `maxPairStart 2 4 = 1`, so the
two unordered extension pairs are both `{1, 3}`.

`SameExtension` below is that unordered statement, written as the disjunction of
the two orientations; it is the only form used from here on.  It is a *shared
abbreviation*, not a third gap: it is what both remaining `Prop`s take as a
hypothesis, and the word-level statement that proves it for the support, **at
`2 ≤ L`**, is `BBTCrossingCoalesce.CrossingPairsCoalesce` (see §7 below for why
the bound cannot be dropped).

§6 reduces `#89` to **two** statements, and it is worth being precise about
which is which, because the earlier formulation (`LadderRotationGap`, and the
first draft of `LadderVertexCycle` in this packet) had them the wrong way round
and was stated in a form that could not be applied.

The first, `CrossingChordsCoalesce`, is the *repeat-theoretic* core: in the
genuine Eulerian setting, two **crossing** support chords must carry the **same**
determinimal maximal extension.  Note the direction: the old statement assumed
coalescing and concluded a rotation, i.e. it made the block structure an
*assumption*.  The block structure is not an assumption --- §6.1 and §6.2 make
every support chord extensible and make the blocks laminar, and what is missing
is that *crossing forces coalescence*.  This is the corrected form of the
correction recorded at `e89b1d42`: it is **false** that crossing raw chords have
*interleaved* maximal extensions (`S = 00101`, `G = 5`, `L = 2` at the `(L-1)`-mers,
kernel-checked as `BBTChords.raw_node_crossing_not_maximal`), and the true
statement is the opposite one --- their maximal extensions *coalesce*.

The second, `LadderVertexCycle`, is the *global* block lemma: a support that is a
laminar family of ladder blocks, together with the two facts that a block is two
rotations of one pair (`ladder_of_coalescing`) and that such a block is
vertex-invisible (`ladder_arc_eq`, `AltF_vtx'`), forces the vertex listing to be
a rotation of the truth's.  It is a statement about the *whole* support, not
about one pair of chords, which is what is needed: the target is
`VertexCycleEq`, never start-level equality, and never `AltF = id` --- `S = 00101`
has a nonidentity `AltF` (`f = (1 3)(2 4)`) and a correct `VertexCycleEq`.

Both are `Prop`s; **neither is an inhabitant**, and nothing in the library
depends on them.

### Evidence, and its limits

`scripts/verify_ladder_blocks_89.py` enumerates, over all primitive `P2` words,
every `vtx`-preserving involution `f` with `J = f ∘ nextPos` a `G`-cycle (the
`J = f ∘ ρ` representation, which is the only safe one: `σ` is an arbitrary
presentation and `prevPos` is geometric, so `AltF (σ i) ≠ σ (i + 1)` in general).
For binary `G ≤ 10` and ternary `G ≤ 7` (3770 traversals with nontrivial
support) it finds

* **zero** failures of `VertexCycleEq` --- so `thm:BBT` at `K = L - 1` survives
  the enlargement to `G = 10`;
* **zero** failures of `CrossingChordsCoalesce`;
* **zero** failures of `LadderVertexCycle` read off the listing;
* and, importantly, **70 refutations of a tempting intermediate lemma**: the
  claim `nextSupport (f x) = f (nextSupport x)` for `x ∈ Support f`, where
  `nextSupport x` is the next support point clockwise after `x`.  It is
  verified for `G ≤ 9` (1110 cases) and fails at `G = 10`, e.g.
  `S = 0010010101`, `L = 5`, `f = (0 3)(1 8)(4 6)(5 7)`, whose four chords carry
  only **two** maximal extensions, one at the start pair `{1, 8}` of length 6 and
  one at `{4, 6}` of length 5.  So neither the
  support-commutation invariant nor the single-ladder invariant is available
  here, and the block argument has to be genuinely global.  Equally, the support
  need **not** be the disjoint union of the full ladders of all maximal repeats
  of length `≥ L - 1`, because a traversal need not swap at every branch vertex
  (`S = 000101`, `L = 3`, support `{2,3,4,5}` while the full ladder union is
  all of `Fin 6`).  Equal geometric gap lengths are likewise false
  (`S = 00101`, `L = 3`: the gaps `2 → 3` and `4 → 1` have lengths 1 and 2).

This is evidence, not a proof: the completeness of the search is not itself
proved.  No `sorry`, no `admit`, no new axiom. -/

/-- **Two pairs of starts carry the same deterministic maximal extension**, as
an **unordered** pair of extension starts.

This is the disjunction of the two orientations, and it must be: `Interleaved`
is symmetric in its last two arguments, so `(a, b, c, d)` and `(a, b, d, c)` are
interchangeable in any hypothesis built on it, while `maxPairStart a b` and
`maxPairStart b a` are the two *swapped* starts of one repeat.  See the head of
§7 for the `S = 00101` refutation of the ordered form. -/
def SameExtension (K : ℕ) (hK : 0 < K) (S : Fin K → α) (a b c d : Fin K) : Prop :=
  (maxPairStart hK S a b = maxPairStart hK S c d ∧
      maxPairStart hK S b a = maxPairStart hK S d c) ∨
    (maxPairStart hK S a b = maxPairStart hK S d c ∧
      maxPairStart hK S b a = maxPairStart hK S c d)

/-- **The repeat-theoretic core of `#89` (`CrossingChordsCoalesce`):** in the
genuine Eulerian setting, two **crossing** chords of the support of
`f = AltF hK σ` carry the **same** deterministic maximal extension, as unordered
pairs (`SameExtension`).

`§6.1` makes every support chord extensible to a maximal repeat of length
`≥ L - 1`, and `§6.2` (`support_blocks_nonCrossing`) makes the blocks laminar.
What §6 does **not** do is the remaining direction: that *crossing forces
coalescence*, so that the support is a single laminar family of ladder blocks
rather than several.

**The direction is at the vertex level, and the word-level theorem does
*not* settle it.**  An earlier version of this comment claimed that the
word-level statement `BBTCrossingCoalesce.CrossingPairsCoalesce` --- which
mentions no `EulerianCycle` and no `AltF` at all --- "implies this one
outright".  **That claim was false and is withdrawn.**  The two statements are
not interderivable as spelled:

* `CrossingPairsCoalesce` carries the hypothesis **`2 ≤ L`** (and `L ≤ K`),
  because it is stated for two pairs of starts that merely carry a common
  `(L-1)`-mer.  This `def` carries **no bound on `L`**.
* At `L = 1` the word-level statement is **true and vacuous** --- its `2 ≤ L`
  hypothesis is unsatisfiable, so it is a `Prop` with no content --- while this
  `def` at `L = 1` is **refuted**: `Issue94CrossingChords.
  crossingChordsCoalesce_refuted` exhibits `K = 4`, `S = 0011`, `σ = (1 3)` over
  the two-letter alphabet `α := Fin 2`, at which the two crossing chords
  `0 2` and `1 3` of `AltF` carry different maximal extensions.  The
  regression is `Issue94CrossingChords.wordLevel_vacuous_at_one_ladder_refuted`
  below; it is a kernel-checked refutation of this implication, and it is
  deliberately kept in the build.

So the missing ingredient is not a word-level implication but the
**imposition direction at the vertex level**: from `AltF hK σ a = b` and
`AltF hK σ b = a` on *both* chords, `AltF_vtx'` yields `vtx a = vtx b` and
`vtx c = vtx d`, and those are exactly the word-level hypotheses.  Two things
are needed for that hand-off and neither is available from the word level
alone: an **`EulerianCycle`** hypothesis, which is what `AltF_vtx'` consumes and
what `CrossingPairsCoalesce` never mentions, and a **non-degenerate window**,
`2 ≤ L`, which is what makes `vtx` (the `(L-1)`-mer labelling) injective enough
for a chord to be a genuine repeated window rather than an arbitrary pair of
starts.  At `L = 1` the labelling is the constant `Fin 0 → α` and the four
`AltF_vtx'` equalities say nothing about the word.

**The surviving sharp statement** is therefore not this unbounded `def` but
its bounded form: `Issue94CrossingChords.CrossingChordsCoalesce_ge2`
(`2 ≤ L`, at arbitrary `[DecidableEq α]`, an inhabitant) and
`Issue94CrossingChords.crossingChordsCoalesce_sharp_bin`, which over `α := Fin 2`
characterises this `def` exactly --- true for every `L ≥ 2`, false at `L = 1`.
This `def` is left exactly as written; the bound is not retrofitted into it. -/
def CrossingChordsCoalesce (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α) (_hP2 : P2 hK L S)
    (_hprim : RepeatAdapter.IsPrimitive hK S), Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K) (_hEul : EulerianCycle hK L S σ),
      ∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d

/-- **The global block lemma of `#89` (`LadderVertexCycle`):** if the support of
the alternative traversal is a laminar family of blocks --- that is, if
**every** pair of crossing support chords carries the same deterministic
maximal extension --- then the vertex listing of the traversal is a rotation of
the truth's vertex listing.

The hypothesis quantifies over **all** crossing quadruples of support points, not
over one chosen pair.  An earlier draft of this packet had it the other way
round, with a single crossing pair as the antecedent, and that is the same
defect as the original `LadderRotationGap`: it makes the block structure an
assumption in a form that cannot be applied to a support which does not
coalesce, and it reads as a local hypothesis with a global conclusion.

Each block is vertex-invisible --- `ladder_of_coalescing` puts its two orbits at
`rotAdd ℓ p`, `rotAdd ℓ q`, and `ladder_arc_eq` gives
`vtx (rotAdd i p) = vtx (rotAdd i q)` for every shift that still fits in the
block's maximal repeat --- and `AltF_vtx'` says the two ends of each chord read
the same vertex.  What is missing is that these local facts assemble into a
statement about the *whole* listing: the blocks are only known to be laminar, and
one has to show that the traversal walks them in the geometric order.

The conclusion is the full `VertexCycleEq` and is not weakened.  This is a
`Prop`; it is **not** an inhabitant. -/
def LadderVertexCycle (L : ℕ) : Prop :=
  ∀ (K : ℕ) (hK : 0 < K) (S : Fin K → α), P2 hK L S →
    RepeatAdapter.IsPrimitive hK S → 2 ≤ L → L ≤ K → Ukkonen hK L S →
    ∀ (σ : Fin K ≃ Fin K), EulerianCycle hK L S σ →
      (∀ (a b c d : Fin K),
        AltF hK σ a = b → AltF hK σ b = a → AltF hK σ c = d → AltF hK σ d = c →
        a ≠ c → b ≠ c → a ≠ d → b ≠ d →
        Interleaved (mkGenome hK S) a b c d →
        SameExtension K hK S a b c d) →
      VertexCycleEq hK L S σ (Equiv.refl (α := Fin K))

end AssemblyP1.BBTLadder
