import AssemblyP1.BBTUniqueEulerian
import AssemblyP1.BBTMaximalExtension

/-!
# `#89`: the support-permutation / chord structure of an alternative Eulerian
# cycle --- an independent route, proved abstractly

**Status.**  §1–§3 are **proved, kernel-checked**, and they are the abstract
combinatorial half of `thm:BBT` in the shape
`AssemblyP1.BBTEulerian.EulerianCycleObstruction`.  They are an *alternative*
to the direct "glue" route: nothing here constructs a candidate genome, and
nothing here uses the pull-back matching adapter.  The only inputs reused are
the innermost-chord lemma `BBTUniqueEulerian.not_visitsAll_of_innermost_chord`
(§4 there) and the maximal-extension lemmas of
`AssemblyP1.BBTMaximalExtension`.

No `sorry`, no `admit`, no new axiom.  The remaining step is stated, and only
stated, in §5 and §6.

## The abstract statement

An alternative Eulerian cycle of the condensed `(L-1)`-mer multigraph is, by
`BBTUniqueEulerian.AltF_vtx`, a **label-preserving permutation** `f` of the
starts (`vtx (f q) = vtx q` for every `q`) whose successor `f ∘ ρ` is a
`G`-cycle (one circuit).  §1 proves the following purely finite combinatorial
statement, with no words, no spectra and no graphs, for an *arbitrary*
labelling `W : Fin G → λ` of the circle:

> **The support dichotomy.**  Let `f` be a bijection of the circle with
> `W (f x) = W x` for all `x`, such that `f ∘ ρ` is a `G`-cycle.  If
> `f ≠ id` then **either**
>
> * **(W)** some label occurs at three pairwise distinct positions, or
> * **(X)** there are two *doubled pairs* `{a, b}`, `{c, d}` --- distinct
>   positions carrying the same label --- whose four endpoints interleave
>   around the circle.
>
> Equivalently, the contrapositive (`eq_id_of_noTriple_noCross`): if no label
> occurs three times and no two doubled pairs interleave, then `f = id`.

The two disjuncts are exactly the two clauses of `def:P1P2`: (W) is the
triple-repeat clause, (X) is the interleaved-repeat clause.  So **the whole
combinatorial content of `thm:BBT` is the support dichotomy**, and the two
repeat-theoretic bridges of §5 are the only remaining content.

## Why the involution route is legitimate here

`BBTChords.chord_lemma` needs an *involution*, and the earlier packet
(`docs/bbt-chord-rematch-89.md` §5) could not supply one.  §1.1 supplies it as
a **consequence** of (W) failing, not as an extra hypothesis: under
`¬ TripleClass` the orbits of `f` have size at most two (`two_or_triple`,
`involution_of_noTriple`).  This is why the multiplicity clause is not merely
one of two symmetric cases --- it is what makes the chord picture legitimate
at all.  `BBTUniqueEulerian` §4 needs neither an involution nor global
non-crossing, only a single innermost chord, so `BBTChords.chord_lemma`
remains unused.
-/

namespace AssemblyP1.BBTSupportChords

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## 1. The abstract layer: labels on a circle

No words, no spectra, no `DecidableEq`: the label type `λ` is arbitrary and
`W` is an arbitrary map.  Everything below is finite combinatorics of a
circle. -/

/-- A **doubled pair**: two distinct positions carrying the same label.  This
is the shape a repeated `(L-1)`-mer has. -/
def DoubledPair {λ : Type} {G : ℕ} (W : Fin G → λ) (a b : Fin G) : Prop :=
  a ≠ b ∧ W a = W b

/-- A **wide label**: one label carried by three pairwise distinct positions.
This is the shape a repeated `(L-1)`-mer of multiplicity `≥ 3` has. -/
def TripleClass {λ : Type} {G : ℕ} (W : Fin G → λ) (a b c : Fin G) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ W a = W b ∧ W a = W c

/-- **Two interleaving doubled pairs.**  The four endpoints alternate around
the circle, so no single maximal repeat can cover both pairs: this is the
shape of an interleaved repeat pair. -/
def CrossedDoubledPairs {λ : Type} {G : ℕ} (hG : 0 < G) (W : Fin G → λ) : Prop :=
  ∃ a b c d : Fin G, DoubledPair W a b ∧ DoubledPair W c d ∧
    InterleavedStarts hG a b c d

/-- The **oriented chords** of `f`: the pairs `(a, b)` with `a ≠ b`,
`f a = b` and `f b = a`.  Both orientations of a two-element orbit are
present, which is what makes the minimal-arc argument of §1.4 go through. -/
def ChordSet {G : ℕ} (f : Fin G → Fin G) : Finset (Fin G × Fin G) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ f p.1 = p.2 ∧ f p.2 = p.1)

section Abstract

variable {λ : Type} {G : ℕ} (hG : 0 < G) (W : Fin G → λ) (f : Fin G → Fin G)

/-! ### 1.1 Orbits have size at most two, unless a label is wide -/

/-- **Two-or-three.**  If no label is carried by three distinct positions and
`f` moves `a` to a distinct `b`, then `f b = a`: the orbit of `a` is exactly
`{a, b}`, so `f` is a product of disjoint transpositions.

The reason is that `W (f b) = W b = W a` by label preservation, so the three
positions `a`, `b`, `f b` all carry the same label; unless `f b = a` that is a
wide label.  (`f b = b` is impossible by injectivity, since `f a = b`.) -/
theorem two_or_triple (hbij : Function.Bijective f) (hW : ∀ x, W (f x) = W x)
    (hnot : ¬ ∃ a b c, TripleClass W a b c) {a b : Fin G} (hab : a ≠ b)
    (hfa : f a = b) : f b = a ∨ ∃ c, TripleClass W a b c := by
  by_cases h : f b = a
  · exact Or.inl h
  · right
    refine ⟨f b, hab, ?_, ?_, hW a, (hW b).trans (hW a)⟩
    · intro e
      exact h e.symm
    · intro e
      apply hab
      exact hbij.injective (hfa.trans e.symm)

/-- **Under "no wide label" every orbit of `f` has size one or two**, i.e.
`f` is an involution.  This is the hypothesis `BBTChords.chord_lemma` needs;
it is *obtained* here, not assumed. -/
theorem involution_of_noTriple (hbij : Function.Bijective f) (hW : ∀ x, W (f x) = W x)
    (hnot : ¬ ∃ a b c, TripleClass W a b c) : ∀ x, f (f x) = x := by
  intro x
  by_cases h : f x = x
  · rw [h]
  · have hd := two_or_triple hG W f hbij hW hnot h h
    rcases hd with hd | ⟨c, hc⟩
    · exact hd
    · exact absurd hc hnot

theorem chord_mem_iff {p : Fin G × Fin G} :
    p ∈ ChordSet f ↔ (p.1 ≠ p.2 ∧ f p.1 = p.2 ∧ f p.2 = p.1) :=
  Finset.mem_filter

theorem mem_chordSet {a b : Fin G} (hab : a ≠ b) (hfa : f a = b) (hfb : f b = a) :
    (a, b) ∈ ChordSet f := by
  rw [chord_mem_iff]
  exact ⟨hab, hfa, hfb⟩

/-! ### 1.2 The chords of `f` are doubled pairs, so they do not interleave -/

theorem doubledPair_of_chord {a b : Fin G} (hW : ∀ x, W (f x) = W x)
    (h2 : (a, b) ∈ ChordSet f) : DoubledPair W a b := by
  rw [chord_mem_iff] at h2
  refine ⟨h2.1, ?_⟩
  have : W b = W a := hW a ▸ rfl
  -- `W (f a) = W a` and `f a = b`
  have h1 : W b = W a := by rw [h2.2.1]; exact (hW a).symm
  exact h1.symm

/-- **The chords of `f` never interleave.**  Each chord is a doubled pair by
label preservation, so "no interleaving doubled pairs" immediately gives the
non-crossing that the chord picture needs. -/
theorem chord_not_interleaving (hW : ∀ x, W (f x) = W x)
    (hnot : ¬ CrossedDoubledPairs hG W)
    {a b c d : Fin G} (h2a : (a, b) ∈ ChordSet f) (h2b : (b, a) ∈ ChordSet f)
    (h2c : (c, d) ∈ ChordSet f) (h2d : (d, c) ∈ ChordSet f)
    (h4 : FourDistinctStarts a b c d) : ¬ InterleavedStarts hG a b c d := by
  intro hi
  exact hnot ⟨a, b, c, d, doubledPair_of_chord hG W f hW h2a,
    doubledPair_of_chord hG W f hW h2c, hi⟩

/-! ### 1.3 Arcs in the shift coordinate

`InArc` (`BBTChords`) is stated with the coordinate `sh`, and
`BBTUniqueEulerian.inArc_iff` makes it an interval of that coordinate.  We
need the *converse* form: a point on the open arc from `a` to `b` is
`rotAdd t a` for some `t` strictly between `0` and `sh a b`. -/

/-- **Points of the open arc are shift-coordinates of `a`.** -/
theorem exists_rotAdd_of_inArc {a b x : Fin G} (hx : InArc hG a b x) :
    ∃ t : ℕ, x = rotAdd hG t a ∧ 0 < t ∧ t < sh hG a b := by
  exact ⟨sh hG a x, rotAdd_sh hG a x, hx.1, hx.2⟩

theorem inArc_ne_left {a b x : Fin G} (hx : InArc hG a b x) : a ≠ x := by
  intro e
  rw [e] at hx
  exact absurd hx.1 (by
    show ¬ (0 < (a.val + G - a.val) % G)
    rw [Nat.add_sub_cancel, Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]
    omega)

theorem inArc_ne_right {a b x : Fin G} (hx : InArc hG a b x) : b ≠ x := by
  intro e
  rw [e] at hx
  exact absurd hx.2 (by
    show ¬ ((b.val + G - a.val) % G < (b.val + G - a.val) % G)
    omega)

/-- **A sub-arc is shorter than the arc containing it.**  If `c` and `d` both
lie on the open arc from `a` to `b`, then one of the two orientations of the
pair `{c, d}` has `sh`-length strictly below `sh a b`.  This is the metric
input of the minimal-chord argument. -/
theorem sh_lt_of_both_inArc {a b c d : Fin G} (hc : InArc hG a b c)
    (hd : InArc hG a b d) (hne : c ≠ d) :
    sh hG c d < sh hG a b ∨ sh hG d c < sh hG a b := by
  obtain ⟨t, hc', ht1, ht2⟩ := exists_rotAdd_of_inArc hG hc
  obtain ⟨t', hd', ht1', ht2'⟩ := exists_rotAdd_of_inArc hG hd
  have hne' : t ≠ t' := by
    intro e
    apply hne
    rw [← hc', ← hd', e]
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · have hstep : rotAdd hG (t' - t) c = d := by
      rw [hc', hd', ← rotAdd_add]
      congr 1
      omega
    have hltG : t' - t < G := by omega
    left
    rw [(rotAdd_eq_iff hG (t' - t) c d hltG).mp hstep]
    omega
  · have hstep : rotAdd hG (t - t') d = c := by
      rw [hd', hc', ← rotAdd_add]
      congr 1
      omega
    have hltG : t - t' < G := by omega
    right
    rw [(rotAdd_eq_iff hG (t - t') d c hltG).mp hstep]
    omega

/-- **The backward remainder of an arc is shorter than the arc.**  If `x` lies
on the open arc from `a` to `b` then the arc from `x` to `b` is strictly
shorter than the arc from `a` to `b`. -/
theorem sh_xb_lt_of_inArc {a b x : Fin G} (hx : InArc hG a b x) :
    sh hG x b < sh hG a b := by
  obtain ⟨t, hx', ht1, ht2⟩ := exists_rotAdd_of_inArc hG hx
  have hstep : rotAdd hG (sh hG a b - t) x = b := by
    rw [hx', rotAdd_add, ← rotAdd_add]
    congr 1
    omega
  have hltG : sh hG a b - t < G := by omega
  rw [(rotAdd_eq_iff hG (sh hG a b - t) x b hltG).mp hstep]
  omega

/-! ### 1.4 There is an innermost chord

The combinatorial core.  A nonempty finite set of pairwise non-crossing
chords of a circle has a chord whose open arc contains **no** endpoint of any
chord; combined with `BBTUniqueEulerian.not_visitsAll_of_innermost_chord` that
breaks the circuit. -/

/-- **A nontrivial label-preserving permutation has a chord.** -/
theorem chordSet_nonempty (hbij : Function.Bijective f) (hW : ∀ x, W (f x) = W x)
    (hnot : ¬ ∃ a b c, TripleClass W a b c) (hf : f ≠ fun x => x) :
    (ChordSet f).Nonempty := by
  by_contra hne
  push_neg at hne
  have hfix : ∀ x, f x = x := by
    intro x
    by_cases h : f x = x
    · exact h
    · have h2b : f (f x) = x ∨ ∃ c, TripleClass W x (f x) c :=
        two_or_triple hG W f hbij hW hnot h h
      rcases h2b with h2b | ⟨c, hc⟩
      · exact absurd h2b hne
      · exact absurd hc hnot
  exact absurd hf hfix

/-- **The innermost-chord lemma (the new combinatorial content).**  Under "no
wide label" and "no two interleaving doubled pairs", a nontrivial `f` has a
chord `(a, b)` such that

* `1 ≤ sh a b < G` --- it is a genuine chord, not a full turn, and
* `f` is the identity on the **open arc from `a` to `b`**.

Neither an involution hypothesis nor global non-crossing is *assumed*: the
two-element-orbit structure is derived in §1.1 from the absence of a wide
label, and non-crossing is used only to rule out a *second* chord endpoint on
the chosen minimal arc. -/
theorem exists_innermost_chord (hbij : Function.Bijective f) (hW : ∀ x, W (f x) = W x)
    (hnot1 : ¬ ∃ a b c, TripleClass W a b c)
    (hnot2 : ¬ CrossedDoubledPairs hG W) (hf : f ≠ fun x => x) :
    ∃ a b : Fin G, 1 ≤ sh hG a b ∧ sh hG a b < G ∧ f b = a ∧ f a = b ∧
      ∀ x, InArc hG a b x → f x = x := by
  have hne : (ChordSet f).Nonempty := chordSet_nonempty hG W f hbij hW hnot1 hf
  have himg : ((ChordSet f).image (fun p => sh hG p.1 p.2)).Nonempty := hne.image _
  set m : ℕ := ((ChordSet f).image (fun p => sh hG p.1 p.2)).min' himg with hmdef
  -- the minimal `sh`-length is attained, and every chord is at least `m` long
  obtain ⟨a, b, hab, hminsh⟩ := by
    obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp (Finset.min'_mem _ himg)
    have hpa := (Finset.mem_filter.mp hp)
    exact ⟨p.1, p.2, hp, hpv⟩
  have hmin : m = sh hG a b := by rw [← hmdef]; exact hminsh
  have hmle : ∀ p ∈ ChordSet f, m ≤ sh hG p.1 p.2 := by
    intro p hp
    have hmem : sh hG p.1 p.2 ∈ (ChordSet f).image (fun p => sh hG p.1 p.2) :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [← hmdef]
    exact Finset.le_min' _ (Finset.min'_mem _ himg) hmem
  have hGm : G ≤ m := Nat.le_of_lt_succ (show m < G from by
    rw [hmin]; exact sh_lt hG a b)
  have hab1 : 1 ≤ sh hG a b := by rw [hmin] at hGm; omega
  -- no chord endpoint lies on the open arc from `a` to `b`
  have hfree : ∀ x, InArc hG a b x → f x = x := by
    intro x hx
    by_contra hn
    set y := f x with hydef
    have hxn : x ≠ y := hn
    have hxa : a ≠ x := inArc_ne_left hG hx
    have hxb : b ≠ x := inArc_ne_right hG hx
    -- either `{x, y}` is a chord, or a label is wide
    rcases two_or_triple hG W f hbij hW hnot1 hxn (by rw [hydef]) with h2 | ⟨c, hc⟩
    · -- the pair `{x, y}` is a chord
      have h2xy : (x, y) ∈ ChordSet f := mem_chordSet hG f hxn (by rw [hydef]) h2
      have h2yx : (y, x) ∈ ChordSet f := mem_chordSet hG f hxn h2 (by rw [hydef])
      by_cases hyx : InArc hG a b y
      · -- both on the arc: a strictly shorter chord
        have hlt := sh_lt_of_both_inArc hG hx hyx hxn
        rcases hlt with hlt | hlt
        · exact absurd hlt (hmle _ h2xy)
        · exact absurd hlt (hmle _ h2yx)
      · -- `x` on the arc and `y` off it: the two chords interleave, unless
        -- `y` is `a` or `b`, which would again give a shorter chord
        have hya : y ≠ a := by
          intro e
          -- `{a, x}` would be a chord strictly shorter than `m`
          rw [e] at h2xy
          refine absurd (hmle (a, x) ?_) ?_
          · exact mem_chordSet hG f hxa hxn h2
          · rw [hmin] at hxa
            have := hx.2
            omega
        have hyb : y ≠ b := by
          intro e
          rw [e] at h2xy
          refine absurd (hmle (x, b) ?_) ?_
          · exact mem_chordSet hG f hxn (by rw [hydef]) h2
          · rw [hmin]
            exact sh_xb_lt_of_inArc hG hx
        refine absurd hnot2 ⟨a, b, x, y, ?_, ?_, ?_⟩
        · exact ⟨hxa, by rw [hydef]; exact (hW x).symm⟩
        · exact ⟨hxn, by rw [hydef]; exact (hW x)⟩
        · refine ⟨hxa, hxb, hya, hyb, hxn, ?_, hx.1, ?_⟩
          · exact Ne.symm hxn
          · intro hcontra
            exact hyx hcontra
    · exact absurd hc hnot1
  exact ⟨a, b, hab1, sh_lt hG a b, hab.2.2, hab.2.1, hfree⟩

/-! ### 1.5 The support dichotomy -/

/-- **The support dichotomy.**  A label-preserving bijection of the circle
whose successor is a `G`-cycle, if nontrivial, exhibits either a label carried
by three distinct positions, or two interleaving doubled pairs. -/
theorem support_dichotomy (hbij : Function.Bijective f) (hW : ∀ x, W (f x) = W x)
    (hV : VisitsAll (fun x => f (nextPos hG x)) (origin hG)) (hf : f ≠ fun x => x) :
    (∃ a b c, TripleClass W a b c) ∨ CrossedDoubledPairs hG W := by
  by_cases hnot1 : ∃ a b c, TripleClass W a b c
  · exact Or.inl hnot1
  · by_cases hnot2 : CrossedDoubledPairs hG W
    · exact Or.inr hnot2
    · exfalso
      obtain ⟨a, b, hg, hgb, hfb, hfa, hfree⟩ :=
        exists_innermost_chord hG W f hbij hW hnot1 hnot2 hf
      exact not_visitsAll_of_innermost_chord hG hbij hg hgb hfree hfb hV

/-- **The contrapositive, which is the form the word layer consumes:** no
wide label and no interleaving doubled pairs force `f = id`. -/
theorem eq_id_of_noTriple_noCross (hbij : Function.Bijective f)
    (hW : ∀ x, W (f x) = W x)
    (hV : VisitsAll (fun x => f (nextPos hG x)) (origin hG))
    (hnot1 : ¬ ∃ a b c, TripleClass W a b c)
    (hnot2 : ¬ CrossedDoubledPairs hG W) : f = fun x => x := by
  by_contra hn
  exact support_dichotomy hG W f hbij hW hV hn hnot1 hnot2

end Abstract

end AssemblyP1.BBTSupportChords
