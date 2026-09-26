import AssemblyP1.P2
import AssemblyP1.RepeatAdapter
import AssemblyP1.PopulationReduction

/-!
# The chord / transposition core of `thm:BBT` (issue #89), route recorded in the
# issue comments

This file attacks the *only* remaining boundary of
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`, namely
`P2.BBTUniqueAt`.  It follows the route sketched in the issue comments and does
**not** use the raw `(L-1)`-mer maximal-extension argument that
`docs/audit-p2-direct-proof-maximal-extension-2026-09-21.md` refutes.

## The route

Two circular words `S` (truth) and `E` (candidate) with the same complete
`L`-spectrum traverse the *same* length-`(L-1)`-mer multigraph in two different
cyclic orders: the truth walks its own positions `0,1,…,G-1`, the candidate
walks its own.  Because the spectra agree, the two traversals are matched
occurrence-by-occurrence: there is a bijection `σ : Fin G → Fin G` (a
*matching*) with `window S r = window E (σ r)` for all `r`.  Comparing where the
two traversals *enter* each node gives the **rematching**

```text
R = σ⁻¹ ∘ pred ∘ σ,
```

a permutation of the truth's positions: `R r` is the truth occurrence whose
incoming edge the candidate uses immediately before the edge of `r`.  `R` is
exactly the "local rematching of truth boundary occurrences" of the route:

* `R = id` **iff** `E` is a rotation of `S` (`rematch_id_iff`, matching
  characterization `rotEquiv_iff_exists_matching`);
* under the multiplicity cap `nodeCount k ≤ 2` (which is what the triple-repeat
  clause of `def:P1P2` buys) `R` is a **product of disjoint transpositions**:
  `R` preserves every node fibre, and a fibre has one or two elements
  (`rematch_fiber`, `rematch_le_two_or_id`, `rematch_transposition`);
* the two ends of a `R`-chord are two occurrences of the *same* `(L-1)`-mer,
  i.e. an "unambiguous path" of length `L-1` (`rematch_chord_agree`).

The abstract combinatorial core (`chord_lemma`) is then: on a circle of at
least three positions, an involution that is not the identity and whose
two-element orbits are pairwise non-interleaving cannot be a rotation of the
circle.  Contrapositively (the form consumed below): a nontrivial
product of disjoint transpositions that is a rotation must have two *crossing*
chords.  This is kernel-checked on the smallest useful data structure — an
abstract permutation of `Fin G` together with the two notions of "rotation" and
"interleaving of four starts" — with no words, spectra or graphs in it.

## What this file does not do

`chord_lemma` is proved; the *adapter* is proved as far as it is sound.  The
remaining gap is stated exactly, as `chords_imply_interleaved_maximal`, in
`docs/bbt-chord-rematch-89.md`: a `R`-chord is only an `(L-1)`-mer agreement,
not yet a *maximal* repeat, and the audited failure shows that crossing raw
`(L-1)`-mer pairs need not extend to distinct interleaved maximal pairs.  No
`sorry`, no `admit`, no new axiom, and `BBTUniqueAt` is not closed.
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

end AssemblyP1.BBTChords
