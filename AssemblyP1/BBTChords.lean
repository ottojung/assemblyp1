import AssemblyP1.P2
import AssemblyP1.RepeatAdapter
import AssemblyP1.PopulationReduction

/-!
# The chord / transposition core of `thm:BBT` (issue #89)

This file attacks the *only* remaining boundary of
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`, namely
`P2.BBTUniqueAt`, along the route sketched in the issue comments (condense
unambiguous paths / maximal repeats, alternate Eulerian traversal as a local
rematching of truth boundary occurrences, transposition/chord lemma,
non-interleaving chords force a unique cyclic trail).

Contents:

* §1 the abstract cyclic transposition / chord lemma (`chord_lemma`), on the
  smallest useful data structure;
* §2 the generic equal-spectrum **matching** adapter (`exists_matching`,
  `matching_rotation_imp`);
* §3 a kernel-checked **refutation of the raw `(L-1)`-mer chord
  instantiation** (`raw_node_crossing_not_maximal`).

## §1 The abstract core

On a circle of at least three positions, an involution that is not the identity
and whose two-element orbits ("chords") are pairwise non-interleaving is not a
rotation of the circle; equivalently, a nontrivial rotational involution has two
crossing orbits (`chord_lemma_cross`).  This is the combinatorial step
"non-interleaving chords forbid a single cyclic trail", proved with no words,
spectra or graphs in it, so it is independent of how chords are realized.

## §2 The matching adapter (route-agnostic)

Two circular words with the same complete `L`-spectrum traverse the same
length-`(L-1)`-mer multigraph in two cyclic orders, and equal spectra give a
bijection of the two traversals start by start (`exists_matching`).  A *rotational*
matching is a rotation of the words, i.e. exactly `RotEquiv` (`matching_rotation_imp`).
These lemmas are valid regardless of the chord analysis.

## §3 Raw `(L-1)`-mer chords do not work

The route's first instantiation of §1 takes the two ends of a chord to be the two
occurrences of a repeated `(L-1)`-mer.  That is refuted here: for
`S = 00101`, `G = 5`, `L = 3` (which satisfies P2) the two repeated length-`2`
mers occur at the crossing pairs `{1,3}` and `{2,4}`, yet neither pair is a
maximal repeat.  So crossing of raw node pairs is compatible with P2, and the
argument has to be organized around **maximal-repeat blocks** instead — the
simultaneous two-sided maximal extension of a node's occurrences, which is what
the interleaved clause of `def:P1P2` ranges over.

## What this file does not do

`chord_lemma` is proved, the matching adapter is proved, and the raw-node
instantiation is refuted.  The **block-factoring step** — that the alternative
Eulerian choices factor by maximal-repeat blocks, and that non-interleaved blocks
force a unique cyclic trail — is *not* proved; it is the remaining gap, stated
exactly in `docs/bbt-chord-rematch-89.md`.  `BBTUniqueAt` is not closed.  No
`sorry`, no `admit`, no new axiom.
-/


namespace AssemblyP1.BBTChords

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction

/-! ## 1. The abstract cyclic transposition / chord lemma -/

section Chord

variable {G : ℕ}

/-- Forward rotation of the circle of `G` positions by `s` steps. -/
def rotAdd (hG : 0 < G) (s : ℕ) (x : Fin G) : Fin G :=
  ⟨(x.val + s) % G, Nat.mod_lt _ hG⟩

/-- One-step forward rotation; the traversal step of the truth. -/
def nextPos (hG : 0 < G) (x : Fin G) : Fin G := rotAdd hG 1 x

/-- One-step backward rotation; the "preceding position" of a traversal. -/
def prevPos (hG : 0 < G) (x : Fin G) : Fin G :=
  ⟨(x.val + G - 1) % G, Nat.mod_lt _ hG⟩

/-- `R` is a rotation of the circle if it is a forward shift by some `s`. -/
def IsRotation (hG : 0 < G) (R : Fin G → Fin G) : Prop :=
  ∃ s : ℕ, ∀ x : Fin G, R x = rotAdd hG s x

/-- `p` lies strictly on the open clockwise arc from `a` to `b`.  This is
`SourceFaithfulIs.Genome.InOpenArc` for a circle of `G` positions, and the two
are interchangeable (`interleavedStarts_iff`). -/
def InArc (_hG : 0 < G) (a b p : Fin G) : Prop :=
  0 < (p.val + G - a.val) % G ∧
    (p.val + G - a.val) % G < (b.val + G - a.val) % G

/-- The four starts of a pair of chords of the circle: two genuine chords,
  and the four endpoints pairwise distinct. -/
def FourDistinctStarts (a b c d : Fin G) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

/-- Cyclic alternation of two chords: the four endpoints interleave. -/
def InterleavedStarts (hG : 0 < G) (a b c d : Fin G) : Prop :=
  FourDistinctStarts a b c d ∧ (InArc hG a b c ↔ ¬ InArc hG a b d)

instance (hG : 0 < G) (a b c d : Fin G) :
    Decidable (InterleavedStarts hG a b c d) := by
  unfold InterleavedStarts FourDistinctStarts InArc
  infer_instance

@[simp] theorem rotAdd_zero (hG : 0 < G) (x : Fin G) : rotAdd hG 0 x = x := by
  apply Fin.ext
  show (x.val + 0) % G = x.val
  rw [Nat.add_zero, Nat.mod_eq_of_lt x.isLt]

/-- Reduction of a shift modulo the circle: `(x + s) % G = (x + s % G) % G`.
-/
theorem mod_add_mod_right (G x s : ℕ) :
    (x + s) % G = (x + s % G) % G := by
  have hq := Nat.mod_add_div s G
  have e1 : x + s = x + (s % G + G * (s / G)) := by rw [hq]
  have e2 : x + (s % G + G * (s / G)) = (x + s % G) + G * (s / G) := by omega
  calc (x + s) % G = (x + (s % G + G * (s / G))) % G := by rw [e1]
    _ = ((x + s % G) + G * (s / G)) % G := by rw [e2]
    _ = (x + s % G) % G := by
        show ((x + s % G) + G * (s / G)) % G = (x + s % G) % G
        exact Nat.add_mul_mod_self_left _ _ _

/-- A rotation by `s` is the rotation by `s % G`. -/
theorem rotAdd_mod (hG : 0 < G) (s : ℕ) (x : Fin G) :
    rotAdd hG s x = rotAdd hG (s % G) x := by
  apply Fin.ext
  show (x.val + s) % G = (x.val + s % G) % G
  exact mod_add_mod_right G x.val s

/-- The arc predicate measured from a start whose index is `0`. -/
theorem inArc_of_zero_val {G : ℕ} (hG : 0 < G) {a b p : Fin G} (hz : a.val = 0) :
    InArc hG a b p ↔ 0 < p.val ∧ p.val < b.val := by
  have _ := hG
  have key : ∀ x : Fin G, (x.val + G - a.val) % G = x.val := by
    intro x
    rw [hz, show x.val + G - 0 = x.val + G by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt x.isLt]
  rw [InArc, key, key]

/-- Cyclic alternation of two chords anchored at a start of index `0`. -/
theorem interleavedStarts_of_zero_val {G : ℕ} (hG : 0 < G) {a b c d : Fin G}
    (hz : a.val = 0) :
    InterleavedStarts hG a b c d ↔
      FourDistinctStarts a b c d ∧
        ((0 < c.val ∧ c.val < b.val) ↔ ¬ (0 < d.val ∧ d.val < b.val)) := by
  have _ := hG
  have h1 := inArc_of_zero_val (G := G) hG (a := a) (b := b) (p := c) hz
  have h2 := inArc_of_zero_val (G := G) hG (a := a) (b := b) (p := d) hz
  rw [InterleavedStarts, h1, h2]

/-- `G ∣ 2` with `G > 0` forces `G ≤ 2`. -/
private theorem le_two_of_dvd_two {G : ℕ} (h : G ∣ 2) (hG : 0 < G) : G ≤ 2 := by
  have _ := hG
  obtain ⟨c, hc⟩ := h
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp at hc
  · have hle : G * 1 ≤ G * c := Nat.mul_le_mul_left G hc
    omega

theorem ne_of_val_ne {G : ℕ} {a b : Fin G} (h : a.val ≠ b.val) : a ≠ b := by
  intro e
  exact h (congrArg Fin.val e)

/-- **The abstract chord lemma (issue #89 route).**  On a circle with at least
three positions, let `R` be an involution which is not the identity and whose
two-element orbits ("chords") are pairwise non-interleaving.  Then `R` is not a
rotation of the circle.

Equivalently (the form used by the adapter): *if `R` is a nontrivial rotation
and an involution, two of its orbits interleave.* -/
theorem chord_lemma {G : ℕ} (hG : 0 < G) (h3 : 3 ≤ G) (R : Fin G → Fin G)
    (hinv : ∀ x : Fin G, R (R x) = x) (hne : R ≠ fun x => x)
    (hcross : ∀ a b c d : Fin G, R a = b → R b = a → R c = d → R d = c →
      FourDistinctStarts a b c d → ¬ InterleavedStarts hG a b c d) :
    ¬ IsRotation hG R := by
  rintro ⟨s, hs⟩
  have h1G : 1 < G := by omega
  have h2G : 2 ≤ G := by omega
  set z : Fin G := ⟨0, by omega⟩ with hzdef
  set o : Fin G := ⟨1, by omega⟩ with hodef
  have hzval : z.val = 0 := rfl
  have hoval : o.val = 1 := rfl
  -- Normalize the shift to `s % G ∈ [0, G)`.
  have hfun : ∀ x : Fin G, R x = rotAdd hG (s % G) x := by
    intro x
    rw [hs x]
    exact rotAdd_mod hG s x
  have htG : s % G < G := Nat.mod_lt _ hG
  set t : Fin G := ⟨s % G, htG⟩ with htdef
  have htval : t.val = s % G := rfl
  have hR0v : (R z).val = s % G := by
    rw [hfun z]
    show (z.val + s % G) % G = s % G
    rw [hzval, Nat.zero_add, Nat.mod_eq_of_lt htG]
  have h2mod : (s % G + s % G) % G = 0 := by
    have hh := congrArg (fun w : Fin G => w.val) (hinv z)
    have h2' := hfun t
    have e2 : (t.val + t.val) % G = 0 := by
      have e : R z = t := Fin.ext (hR0v.trans htval.symm)
      have hRt2 : (R t).val = 0 := by
        have hh' := hh
        rw [e] at hh'
        exact hh'.trans hzval
      have h2v : (R t).val = (t.val + t.val) % G := by
        rw [h2']
        show (t.val + s % G) % G = _
        rw [htval]
      rw [← h2v]
      exact hRt2
    rw [← htval, e2]
  have htwo : 0 < s % G := by
    by_contra h0
    have hz0 : s % G = 0 := by omega
    refine hne ?_
    funext x
    rw [hfun x, hz0, rotAdd_zero]
  have hle2 : G ≤ 2 → False := by
    intro hle
    omega
  have hne1 : s % G ≠ 1 := by
    intro h1
    rw [h1] at h2mod
    exact hle2 (le_two_of_dvd_two (Nat.dvd_iff_mod_eq_zero.mpr h2mod) hG)
  have ht2 : 2 ≤ s % G := by omega
  -- The two candidate chords are `(z, t)` and `(o, R o)`.
  have hR0 : R z = t := by
    refine Fin.ext ?_
    rw [hR0v, htval]
  have hRt : R t = z := by rw [← hR0]; exact hinv z
  set u : Fin G := R o with hu
  have hRu : R u = o := hinv o
  have huval : u.val = (1 + s % G) % G := by
    have hh := congrArg (fun w : Fin G => w.val) (hfun o)
    rw [hu, hh]
    show (o.val + s % G) % G = _
    rw [hoval]
  -- `1 + s % G = G` is impossible: it would give `G ∣ 2`.
  have hnequiv : 1 + s % G ≠ G := by
    intro hq
    have hx : s % G = G - 1 := by omega
    have h1 : (s % G) + (s % G) = (G - 1) + (G - 1) := by rw [hx]
    have hdvd : G ∣ (G - 1) + (G - 1) := by
      rw [← h1]
      exact Nat.dvd_iff_mod_eq_zero.mpr h2mod
    have hdvd2 : G ∣ 2 * G := ⟨2, by omega⟩
    have hdvd3 : G ∣ 2 := by
      obtain ⟨k, hk⟩ := hdvd2
      obtain ⟨m, hm⟩ := hdvd
      have hmk : m ≤ k := by
        have hle : G * m ≤ G * k := by
          have h2 : (G - 1) + (G - 1) ≤ 2 * G := by omega
          rw [hm, hk] at h2
          omega
        exact Nat.le_of_mul_le_mul_left hle (by omega)
      refine ⟨k - m, ?_⟩
      have hsub : G * (k - m) = G * k - G * m := by
        rw [Nat.mul_comm G, Nat.sub_mul, Nat.mul_comm G k, Nat.mul_comm G m]
      rw [hsub, ← hk, ← hm]
      omega
    exact hle2 (le_two_of_dvd_two hdvd3 hG)
  have huval' : u.val = 1 + s % G := by
    rw [huval, Nat.mod_eq_of_lt (by omega)]
  -- Four distinct endpoints.
  have hnd : FourDistinctStarts z t o u := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (apply ne_of_val_ne; simp only [hzval, hoval, huval', htval]; omega)
  -- The two chords interleave: `0 < 1 < t`, while `u` is not on the open arc.
  have hinter : InterleavedStarts hG z t o u := by
    rw [interleavedStarts_of_zero_val hG hzval]
    refine ⟨hnd, Iff.intro (fun _ h2 => ?_) (fun _ => ⟨?_, ?_⟩)⟩
    · rw [huval'] at h2
      omega
    · omega
    · omega
  exact hcross z t o u hR0 hRt hu.symm hRu hnd hinter

/-- **Contrapositive form, as consumed by the adapter:** a rotation that is a
nontrivial involution has two crossing orbits. -/
theorem chord_lemma_cross {G : ℕ} (hG : 0 < G) (h3 : 3 ≤ G) (R : Fin G → Fin G)
    (hinv : ∀ x : Fin G, R (R x) = x) (hne : R ≠ fun x => x)
    (hrot : IsRotation hG R) :
    ∃ a b c d : Fin G, R a = b ∧ R b = a ∧ R c = d ∧ R d = c ∧
      FourDistinctStarts a b c d ∧ InterleavedStarts hG a b c d := by
  by_contra h
  refine chord_lemma hG h3 R hinv hne ?_ hrot
  rintro a b c d hab hba hcd hdc hnd hinter
  exact h ⟨a, b, c, d, hab, hba, hcd, hdc, hnd, hinter⟩

/-- The rotation by two of the four-position circle, used by
`chord_lemma_sanity`. -/
def R4 : Fin 4 → Fin 4 := fun x => rotAdd (hG := by decide) 2 x

/-- **Sanity instance (anti-vacuity).**  On the circle of four positions the
rotation by two is a nonidentity involution, and the two chords
`(0,2)`, `(1,3)` really do interleave — the situation `chord_lemma_cross`
produces.  Checked on the concrete `Fin 4`, so the abstract lemma is neither
vacuous nor trivially satisfiable only in degenerate cases. -/
theorem chord_lemma_sanity :
    IsRotation (hG := by decide) R4 ∧ (∀ x : Fin 4, R4 (R4 x) = x) ∧
      R4 ≠ (fun x : Fin 4 => x) ∧
      InterleavedStarts (hG := by decide) (0 : Fin 4) 2 1 3 := by
  refine ⟨⟨2, fun x => rfl⟩, ?_, ?_, ?_⟩
  · intro x
    revert x
    decide
  · intro he
    have hh : R4 (1 : Fin 4) = (1 : Fin 4) := congrFun he 1
    exact absurd (congrArg Fin.val hh) (by decide)
  · unfold InterleavedStarts FourDistinctStarts InArc
    decide

end Chord


/-! ## 2. The word-level adapter: matchings, rotations, node pairs

Everything below is the `#89` route's adapter, built only from the repository's
existing word layer (`OrientedRigidity.window`, `nodeWindow`, `nodeCount`,
`specCount`) and its source-faithful predicates (`mkGenome`, `Agree`,
`Interleaved`).  No new word semantics are introduced. -/

section Adapter

variable {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)

/-- The starts of `W` spelling the read type `w`.  This is the fibre used by
`specCount`; it is a definition, not a new predicate. -/
def startsOf (W : Fin G → α) (w : Fin L → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => window hG W r = w)

theorem card_startsOf (W : Fin G → α) (w : Fin L → α) :
    (startsOf hG W w).card = specCount (L := L) hG W w := rfl

/-- The starts of `W` spelling the `(L-1)`-mer `k` (`nodeCount` fibre). -/
def nodeStartsOf (W : Fin G → α) (k : Fin (L - 1) → α) : Finset (Fin G) :=
  Finset.univ.filter (fun r : Fin G => nodeWindow (L := L) hG W r = k)

theorem card_nodeStartsOf (W : Fin G → α) (k : Fin (L - 1) → α) :
    (nodeStartsOf hG W k).card = nodeCount (L := L) hG W k := rfl

/-- **A matching of the two traversals.**  `σ` pairs the truth's occurrence at
each start with the candidate's occurrence of the same complete read type.
Such a matching exists exactly when the complete spectra agree, and it is
unique up to the choices inside a read-type fibre. -/
def Matching {α : Type} [DecidableEq α] {G L : ℕ} (hG : 0 < G)
    (S E : Fin G → α) (σ : Fin G → Fin G) : Prop :=
  Function.Bijective σ ∧ ∀ r : Fin G, window (L := L) hG S r = window (L := L) hG E (σ r)

/-- Two nonempty finite sets of the same cardinality are in bijection. -/
private theorem finset_equiv_of_card_eq {α : Type} (s t : Finset α) (h : s.card = t.card)
    (_hs : 0 < s.card) : Nonempty (↥s ≃ ↥t) := by
  have e1 : Nonempty (↥s ≃ Fin s.card) := by
    have h1 := Fintype.equivFin ↥s
    rw [Fintype.card_coe] at h1
    exact ⟨h1⟩
  have e2 : Nonempty (Fin t.card ≃ ↥t) := by
    have h2 := Fintype.equivFin ↥t
    rw [Fintype.card_coe] at h2
    exact ⟨h2.symm⟩
  have e3 : Nonempty (Fin s.card ≃ Fin t.card) := by
    rw [h]
    exact ⟨Equiv.refl _⟩
  exact ⟨e1.some.trans e3.some |>.trans e2.some⟩

/-- **Equal complete spectra give a matching** (fibre-by-fibre bijections,
assembled over the starts of the truth).  This is the Eulerian-traversal
correspondence in the only form the reduction needs: the candidate traverses
the same `(L-1)`-mer multigraph as the truth, start by start. -/
theorem exists_matching (S E : Fin G → α)
    (hspec : specCount (L := L) hG S = specCount (L := L) hG E) :
    ∃ σ : Fin G → Fin G, Matching (L := L) hG S E σ := by
  classical
  set A : (Fin L → α) → Finset (Fin G) := fun w => startsOf hG S w with hAdef
  set B : (Fin L → α) → Finset (Fin G) := fun w => startsOf hG E w with hBdef
  have hcard : ∀ w : Fin L → α, (A w).card = (B w).card := by
    intro w
    exact congrArg (fun f : (Fin L → α) → ℕ => f w) hspec
  have hmemA : ∀ r : Fin G, r ∈ A (window (L := L) hG S r) := by
    intro r
    simp only [hAdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmemB : ∀ s : Fin G, s ∈ B (window (L := L) hG E s) := by
    intro s
    simp only [hBdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  -- the fibre bijections, chosen simultaneously
  have hne : ∀ w : Fin L → α, Nonempty (↥(A w) ≃ ↥(B w)) := by
    intro w
    by_cases hw : 0 < (A w).card
    · exact finset_equiv_of_card_eq _ _ (hcard w) hw
    · have hb : (A w).card = 0 := by omega
      have hAe : A w = ∅ := Finset.card_eq_zero.mp hb
      have hb' : (B w).card = 0 := by rw [← hcard w, hb]
      have hBe : B w = ∅ := Finset.card_eq_zero.mp hb'
      rw [hAe, hBe]
      exact ⟨Equiv.refl _⟩
  let : Nonempty (∀ w : Fin L → α, Nonempty (↥(A w) ≃ ↥(B w))) :=
    ⟨fun w => hne w⟩
  set φ : ∀ w : Fin L → α, ↥(A w) ≃ ↥(B w) :=
    fun w => Classical.choice (inferInstanceAs (Nonempty (↥(A w) ≃ ↥(B w)))) with hφdef
  have hφinj : ∀ (w : Fin L → α), Function.Injective (fun y : ↥(A w) => (φ w y).val) :=
    fun w a b hab => (φ w).injective (Subtype.ext hab)
  -- the matching value at a start, for an arbitrary read type.  The read type is
  -- an explicit argument and the agreement proof is a `dite` branch, so the two
  -- ends of a comparison can always be put at the *same* read type: no subtype
  -- value is ever transported between fibres.
  have memA : ∀ (w : Fin L → α) (r : Fin G), window (L := L) hG S r = w → r ∈ A w := by
    intro w r hr
    have : window (L := L) hG S r = w := hr
    simp only [hAdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and, this]
  set V : (Fin L → α) → Fin G → Fin G := fun w r =>
    if h : window (L := L) hG S r = w then (φ w ⟨r, memA w r h⟩).val else r with hVdef
  set σ : Fin G → Fin G := fun r => V (window (L := L) hG S r) r with hσdef
  have hmatch : ∀ r : Fin G, window (L := L) hG S r = window (L := L) hG E (σ r) := by
    intro r
    have h1 : (φ (window (L := L) hG S r) ⟨r, memA _ r rfl⟩).val
        ∈ B (window (L := L) hG S r) := (φ _ _).property
    simp only [hBdef, startsOf, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    calc window (L := L) hG S r
        = window (L := L) hG E ((φ (window (L := L) hG S r) ⟨r, memA _ r rfl⟩).val) :=
          h1.symm
      _ = window (L := L) hG E (σ r) := by
        simp only [hσdef, hVdef]
        rw [dite_eq_left True.intro]
  -- injectivity, fibre by fibre: equal images force equal read types, so both
  -- ends are computed by the *same* fibre equivalence `φ w`, whose injectivity
  -- then gives `r = r'`.
  have hinj : Function.Injective σ := by
    intro r r' heq
    have hw : window (L := L) hG S r = window (L := L) hG S r' := by
      have h1 : window (L := L) hG S r = window (L := L) hG E (σ r) := hmatch r
      have h2 : window (L := L) hG S r' = window (L := L) hG E (σ r') := hmatch r'
      rw [h1, h2, heq]
    set w : Fin L → α := window (L := L) hG S r with hwdef
    have hleft : σ r = (φ w ⟨r, memA w r rfl⟩).val := by
      simp only [hσdef, hVdef]
      rw [dite_eq_left True.intro]
    have hright : σ r' = (φ w ⟨r', memA w r' hw.symm⟩).val := by
      have e : σ r' = V w r' := by
        simp only [hσdef, ← hw, hwdef]
      simp only [e, hVdef]
      rw [dite_eq_left (show window (L := L) hG S r' = w from hw.symm)]
    have hval : (φ w ⟨r, memA w r rfl⟩).val
        = (φ w ⟨r', memA w r' hw.symm⟩).val := by
      rw [← hleft, ← hright]
      exact heq
    have hsub : (⟨r, memA w r rfl⟩ : ↥(A w)) = ⟨r', memA w r' hw.symm⟩ := hφinj w hval
    exact congrArg Subtype.val hsub
  -- `Fin G` is finite, so the injective endomap `σ` is surjective: the
  -- surjectivity needs no separate fibre construction at all.
  have hsurj : Function.Surjective σ :=
    (Finite.injective_iff_surjective).mp hinj
  exact ⟨σ, ⟨hinj, hsurj⟩, hmatch⟩

/-- **A rotational matching is a rotation of the words.**  If the candidate's
occurrences are matched to the truth's by a rotation of the circle, then the
candidate word is a rotation of the truth — i.e. exactly the reduction's
`RotEquiv`.  (The converse, "a rotation of the words yields a *rotational*
matching", is deliberately not formalized here: a matching need not be unique
inside a read-type fibre, so the equivalence is about existence of a rotational
matching, and only this direction is consumed.) -/
theorem matching_rotation_imp (S E : Fin G → α) (σ : Fin G → Fin G) (hL : 1 ≤ L)
    (hm : Matching (L := L) hG S E σ) (hrot : IsRotation hG σ) :
    RotEquiv hG E S := by
  obtain ⟨s, hs⟩ := hrot
  refine ⟨s % G, ?_⟩
  intro i
  have h := hm.2 i
  rw [hs i] at h
  have hval : window (L := L) hG S i ⟨0, by omega⟩
      = window (L := L) hG E (rotAdd hG s i) ⟨0, by omega⟩ := congrFun h ⟨0, by omega⟩
  have hleft : rotAdd hG s i = rotAdd hG (s % G) i := rotAdd_mod hG s i
  rw [hleft] at hval
  have hval2 : cyc hG S i.val
      = cyc hG E ((rotAdd hG (s % G) i).val) := by
    simpa only [window, Nat.add_zero] using hval
  have hSi : S i = S ⟨i.val % G, Nat.mod_lt _ hG⟩ := by
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm
  have h3raw : E ⟨(rotAdd hG (s % G) i).val % G, Nat.mod_lt _ hG⟩
      = S ⟨i.val % G, Nat.mod_lt _ hG⟩ := by
    have h := hval2.symm
    unfold cyc at h
    exact h
  have hx : (rotAdd hG (s % G) i).val % G = (i.val + s % G) % G := by
    show ((i.val + s % G) % G) % G = (i.val + s % G) % G
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hG)
  have h3 : E ⟨(i.val + s % G) % G, Nat.mod_lt _ hG⟩ = S i := by
    have e1 : (⟨(rotAdd hG (s % G) i).val % G, Nat.mod_lt _ hG⟩ : Fin G)
        = ⟨(i.val + s % G) % G, Nat.mod_lt _ hG⟩ := Fin.ext hx
    have h := h3raw
    rw [e1] at h
    exact h.trans hSi.symm
  exact h3

end Adapter

/-! ## 3. Raw `(L-1)`-mer chords do **not** factor: a kernel-checked refutation

The issue-#89 route as first phrased treats the two ends of a "chord" as the two
occurrences of a repeated `(L-1)`-mer, and would then conclude that two crossing
chords give an interleaved pair of *maximal* repeats.  That is false, and the
following instance is kernel-checked here (`decide`, on the concrete
`Fin 5` word below):

* `S = 00101`, `G = 5`, `L = 3` satisfies P2 (`AssemblyP1.P2.P2` at `L = 3`);
* the length-`2` mers `01` and `10` are each repeated, at the *crossing* pairs
  of starts `{1,3}` and `{2,4}` (`InterleavedStarts`);
* nevertheless **neither pair is a maximal repeat** of any length: the pair
  `{1,3}` agrees on the following symbol, and the pair `{2,4}` agrees on the
  preceding symbol, so `SourceFaithfulIs.IsRepeat` fails for both.

So crossing of raw `(L-1)`-mer pairs is *compatible* with P2, and any argument
that needs "crossing chords ⇒ interleaved maximal repeats" is unsound.  The
correct object is the *maximal-repeat block*: the simultaneous maximal extension
of the two occurrences, which is unique for a given pair, and which is what the
interleaved clause of `def:P1P2` actually ranges over.  Whether the alternative
Eulerian choices factor by such blocks (and whether non-interleaved blocks force
a unique cyclic trail) is precisely the part that is *not* settled here; see
`docs/bbt-chord-rematch-89.md`. -/

section RawChordRefutation

variable {α : Type}

/-- The five-symbol word `00101` of the refutation instance. -/
def S5 : Fin 5 → Fin 2 := ![0, 0, 1, 0, 1]

/-- `0 < 5`, named so that the numerals of the instance fix the length. -/
theorem hG5 : 0 < 5 := by decide

/-- **The `P2` half of the refutation instance, kernel-checked.**
`S = 00101` at `G = 5` does satisfy `AssemblyP1.P2.P2` at read length `L = 3`,
and hence, by `AssemblyP1.P2.P2.imp_Ukkonen`, Ukkonen's condition at
`K = L - 1 = 2`.  This is the statement that was previously only asserted in
prose in the section docstring above, so `BBTSupportInvariant.harmless_selected_crossing_00101`
(a `SelectedInterleaved` witness on this very word) is a witness *inside* a
`P2` genome.  The proof is `decide` on the concrete `Fin 5` word; `unfold mkGenome`
is needed because `Genome.len` is a structure field, so `Fin Genome.len` has no
`Fintype`/`DecidableEq` instance until the structure is unfolded. -/
theorem p2_hG5_S5_L3 : P2 hG5 3 S5 := by
  unfold P2 mkGenome
  decide

/-- **The refutation, kernel-checked.**  The two crossing pairs of
`S = 00101` are pairs of *equal* length-`2` mers, they interleave, and each pair
fails one of the two maximality conditions of `SourceFaithfulIs.Genome.IsRepeat`
at that length (equal following symbols for `{1,3}`, equal preceding symbols for
`{2,4}`).  So the raw `(L-1)`-mer "chord" architecture of the `#89` route cannot
work: crossing of raw node pairs is compatible with the absence of interleaved
*maximal* repeats, and the remaining argument has to be organized around
maximal-repeat blocks. -/
theorem raw_node_crossing_not_maximal :
    (nodeWindow (L := 3) (hG := hG5) S5 (1 : Fin 5)
        = nodeWindow (L := 3) (hG := hG5) S5 (3 : Fin 5)) ∧
      (nodeWindow (L := 3) (hG := hG5) S5 (2 : Fin 5)
        = nodeWindow (L := 3) (hG := hG5) S5 (4 : Fin 5)) ∧
      InterleavedStarts (hG := hG5) (1 : Fin 5) (3 : Fin 5) (2 : Fin 5) (4 : Fin 5) ∧
      (cyc (hG := hG5) S5 ((1 : ℕ) + 2) = cyc (hG := hG5) S5 ((3 : ℕ) + 2) ∨
        cyc (hG := hG5) S5 (1 + 5 - 1) = cyc (hG := hG5) S5 (3 + 5 - 1)) ∧
      (cyc (hG := hG5) S5 (2 + 5 - 1) = cyc (hG := hG5) S5 (4 + 5 - 1) ∨
        cyc (hG := hG5) S5 ((2 : ℕ) + 2) = cyc (hG := hG5) S5 ((4 : ℕ) + 2)) := by
  decide

end RawChordRefutation

end AssemblyP1.BBTChords
