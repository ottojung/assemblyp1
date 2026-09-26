import AssemblyP1.SourceFaithfulIs
import AssemblyP1.RepeatAdapter

/-!
# The bridging-length bridge: what `I_s` really implies about long triple repeats

This module is the *new bridge* of issue #88. It replaces the previously
external "Fact D" recorded in `docs/oriented-same-length-ml-88.md` §3, which
asserted

> a length-`L` read bridges a repeat copy only if its length is `≤ L - 2`, so a
> read realization in `I_s` forbids Bresler triple repeats of length `≥ L - 1`

by a theorem that is (a) actually provable, (b) **sharp**, and (c) explains
why Fact D is **false**.

## The theorem (`bridgingLength`)

Let `S` be the circular genome of length `G := S.len`, let the read length
satisfy `L ≤ G`, and let the copy of length `e` (`1 ≤ e < G`) at start `t` be
**bridged** by the realized start set `R`. Then

```
e + 2 ≤ L   ∨   G - e ≤ L
```

The first disjunct is the intended one: the bridging read *straddles* the
copy, covering a base before position `t - 1` and a base after position
`t + e`, hence spanning at least `e + 2 ≤ L` bases.

The second disjunct is the **wraparound mode**: the read does not straddle the
copy at all. It covers position `t - 1` and position `t + e` by going the
other way around the circle, so it covers the entire *complement* arc
`[t + e, t - 1]`, of length `G - e`; a read of length `L` can do that exactly
when `G - e ≤ L`. Differences of two or more full turns are excluded by
`L ≤ G`, which is why that hypothesis appears.

Wraparound is not a formal artifact. In
`AssemblyP1.BridgingWraparoundCounterexample` there is a kernel-checked genome
and realized start set satisfying **full** source-faithful
`InformationFeasible` and nevertheless carrying a maximal triple repeat of
length `2 = L - 1`. So

```
InformationFeasible → ¬ HasLongTripleRepeat
```

is **false**, and the maximum-likelihood endpoint must be stated with the
wraparound regime visible rather than hidden.

## Consequence (`informationFeasible_tripleRepeat_ge_G_sub_L`)

Combining `bridgingLength` with clause 2 of `InformationFeasible` gives the
sharp statement about long triple repeats:

> If `R ∈ I_s`, `2 ≤ L ≤ G`, and the truth carries a triple repeat of length
> `e` with `L - 1 ≤ e`, then `G - L ≤ e`.

Equivalently: `I_s` forbids every triple repeat of length `e` with

```
L - 1 ≤ e   ∧   e < G - L,
```

that is, every long triple repeat whose complement arc is longer than a read.
`SharpNoLongTripleRepeat` is exactly that hypothesis, written on the genome;
`informationFeasible_sharp_no_long_triple_repeat` derives
`¬ HasLongTripleRepeat` from `InformationFeasible` plus it. This is the
replacement for the lost Fact D, and it is the exact premise consumed by
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`.
-/

namespace AssemblyP1.BridgingBridge

open SourceFaithfulIs

set_option maxHeartbeats 400000

noncomputable section

/-! ## Reconciling the two circular-word conventions

`Genome` reads position `i` as `S.sym ⟨i % S.len, _⟩`; `OrientedRigidity.cyc`
at length `G` reads it as `S.sym ⟨i % G, _⟩`. Instantiating `G := S.len` makes
the two the same term up to the `Fin` proof, which is irrelevant, so
`OrientedRigidity.cyc S.len_pos S.sym i` and `Genome.cycl S i` agree. The
lemmas below record that identification together with the three shape
transfers it enables (`cyc_eq_cycl`, `window_rep`, `cycl_to_preceding`,
`cycl_to_following`); they are used throughout rather than re-proved locally. -/

private theorem cyc_eq_cycl {α : Type} [DecidableEq α] {S : Genome α} (i : ℕ) :
    OrientedRigidity.cyc S.len_pos S.sym i = S.cycl i := rfl

/-- `Genome.cycl` depends only on the residue of its index. -/
private theorem cycl_sub {α : Type} [DecidableEq α] {S : Genome α} {i j : ℕ}
    (h : i % S.len = j % S.len) : S.cycl i = S.cycl j := by
  unfold Genome.cycl
  exact congrArg S.sym (Fin.ext h)

/-- The `Fin S.len` representative of a natural-number start. -/
private def rep {α : Type} (S : Genome α) (a : ℕ) : Fin S.len :=
  ⟨a % S.len, Nat.mod_lt _ S.len_pos⟩

private theorem rep_val {α : Type} {S : Genome α} (a : ℕ) :
    (rep S a).val = a % S.len := rfl

private theorem rep_ne {α : Type} {S : Genome α} {a b : ℕ}
    (h : a % S.len ≠ b % S.len) : rep S a ≠ rep S b := by
  intro he
  refine h (by rw [← rep_val, ← rep_val]; exact congrArg Fin.val he)

/-- Adding a summand inside a modulus only depends on its residue. -/
private theorem mod_add_mod (n x y : ℕ) : (x + y) % n = (x + y % n) % n := by
  obtain ⟨k, hk⟩ : ∃ k, y = y % n + n * k := ⟨y / n, (Nat.mod_add_div y n).symm⟩
  have hz : (n * k) % n = 0 := by
    have hdvd : n ∣ n * k := ⟨k, rfl⟩
    exact (Nat.modEq_zero_iff_dvd).mpr hdvd
  rw [hk]
  simp only [Nat.add_mod, hz, Nat.zero_add, Nat.add_zero, Nat.mod_mod]

/-- Agreement at natural-number starts transfers to the representative starts:
the length-`e` window at `rep a` is the `S.cycl` read at the raw index `a + d`. -/
private theorem window_of_cyc {α : Type} [DecidableEq α] {S : Genome α} {a b e : ℕ}
    (d : Fin e) (hag : S.cycl (a + d.val) = S.cycl (b + d.val)) :
    S.window e (rep S a) d = S.window e (rep S b) d := by
  have hA : S.window e (rep S a) d = S.cycl ((rep S a).val + d.val) := rfl
  have hB : S.window e (rep S b) d = S.cycl ((rep S b).val + d.val) := rfl
  have e1 : ((rep S a).val + d.val) % S.len = (a + d.val) % S.len := by
    rw [rep_val]
    exact Eq.trans (mod_add_mod S.len (a % S.len) d.val) (Nat.add_mod a d.val S.len).symm
  have e2 : ((rep S b).val + d.val) % S.len = (b + d.val) % S.len := by
    rw [rep_val]
    exact Eq.trans (mod_add_mod S.len (b % S.len) d.val) (Nat.add_mod b d.val S.len).symm
  rw [hA, hB]
  calc S.cycl ((rep S a).val + d.val) = S.cycl (a + d.val) := cycl_sub e1
    _ = S.cycl (b + d.val) := hag
    _ = S.cycl ((rep S b).val + d.val) := (cycl_sub e2).symm

/-- The `cyc` value one step before the raw index `a` is the preceding symbol
of the representative start `a`. -/
private theorem cycl_to_preceding {α : Type} [DecidableEq α] {S : Genome α} (a : ℕ) :
    OrientedRigidity.cyc S.len_pos S.sym (a + S.len - 1) = S.Preceding (rep S a) := by
  have hG : 0 < S.len := S.len_pos
  have hh : S.Preceding (rep S a) = S.cycl ((rep S a).val + S.len - 1) := rfl
  rw [cyc_eq_cycl, hh]
  refine cycl_sub ?_
  show (a + S.len - 1) % S.len = ((rep S a).val + S.len - 1) % S.len
  have h1 : a + S.len - 1 = a + (S.len - 1) := by omega
  have h2 : (rep S a).val + S.len - 1 = (rep S a).val + (S.len - 1) := by omega
  rw [h1, h2, rep_val]
  exact Eq.trans (Nat.add_mod a (S.len - 1) S.len)
    (mod_add_mod S.len (a % S.len) (S.len - 1)).symm

/-- The `cyc` value `e` steps after the raw index `a` is the following symbol
of the representative start `a`. -/
private theorem cycl_to_following {α : Type} [DecidableEq α] {S : Genome α} (a e : ℕ) :
    OrientedRigidity.cyc S.len_pos S.sym (a + e) = S.Following e (rep S a) := by
  have hh : S.Following e (rep S a) = S.cycl ((rep S a).val + e) := rfl
  rw [cyc_eq_cycl, hh]
  refine cycl_sub ?_
  show (a + e) % S.len = ((rep S a).val + e) % S.len
  rw [rep_val]
  exact Eq.trans (Nat.add_mod a e S.len) (mod_add_mod S.len (a % S.len) e).symm

/-! ## The sharp bridging-length restriction -/

/-- **Sharp bridging-length restriction.** If the copy of length `e` at start
`t` is bridged by the realized reads, whose length satisfies `L ≤ S.len`, then
either

* `e + 2 ≤ L`: the bridging read strictly straddles the copy, entering before
  `t - 1` and leaving after `t + e`; or
* `S.len - e ≤ L`: the bridging read goes around the other way and covers the
  whole complement arc `[t + e, t - 1]`, of length `S.len - e`.

These are the only two possibilities. -/
theorem bridgingLength {α : Type} [DecidableEq α] {L e : ℕ} {S : Genome α}
    {R : Finset (Fin S.len)} {t : Fin S.len} (hLG : L ≤ S.len)
    (he : 1 ≤ e) (heG : e < S.len) (hb : BridgesCopy S L R e t) :
    e + 2 ≤ L ∨ S.len - e ≤ L := by
  classical
  obtain ⟨r, hr, ⟨d₁, h₁⟩, ⟨d₂, h₂⟩⟩ := hb
  set a : ℕ := d₁.val with ha
  set b : ℕ := d₂.val with hb
  have haL : a < L := ha.symm ▸ d₁.isLt
  have hbL : b < L := hb.symm ▸ d₂.isLt
  -- The two coverage equations, as modular equalities.
  have hform₁ : t.val + S.len - 1 = t.val + (S.len - 1) := by omega
  have hm₁ : t.val + (S.len - 1) ≡ r.val + a [MOD S.len] := by
    rw [← hform₁]; exact h₁
  have hm₂ : t.val + e ≡ r.val + b [MOD S.len] := h₂
  -- Add the respective wrap-around offsets, so that the start `r` drops out.
  have hmk : (t.val + (S.len - 1)) + (S.len - a) ≡ (t.val + e) + (S.len - b)
      [MOD S.len] := by
    have hx : r.val + a + (S.len - a) = r.val + S.len := by omega
    have hy : r.val + b + (S.len - b) = r.val + S.len := by omega
    calc (t.val + (S.len - 1)) + (S.len - a) ≡ (r.val + a) + (S.len - a)
        [MOD S.len] := hm₁.add_right (S.len - a)
      _ = r.val + S.len := hx
      _ = (r.val + b) + (S.len - b) := hy.symm
      _ ≡ (t.val + e) + (S.len - b) [MOD S.len] :=
        (hm₂.add_right (S.len - b)).symm
  -- Cancel the shared `t.val`.
  have hmod : S.len - 1 + (S.len - a) ≡ e + (S.len - b) [MOD S.len] := by
    have hk : t.val + ((S.len - 1) + (S.len - a)) ≡ t.val + (e + (S.len - b))
        [MOD S.len] := by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hmk
    exact hk.add_left_cancel' t.val
  -- Both sides lie in `(0, 2 * S.len)`, so the congruence has exactly the
  -- three possibilities `P = Q`, `P = Q + S.len`, `Q = P + S.len`.
  have hP0 : 0 < S.len - 1 + (S.len - a) := by
    have : 0 < S.len - a := by omega
    omega
  have hQ0 : 0 < e + (S.len - b) := by
    have : 0 < S.len - b := by omega
    omega
  have hQlt : e + (S.len - b) < 2 * S.len := by omega
  rcases lt_trichotomy (S.len - 1 + (S.len - a)) (e + (S.len - b))
    with hPQ | hPeq | hQP
  · -- `P < Q`: then `Q = P + S.len * t` with `t ≥ 1`, and `t = 1` would give
    -- `e = 2 * S.len - 1 - b + a ≥ S.len`, contradicting `e < S.len`.
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add (Nat.le_of_lt hPQ)).mp hmod
    have htlt : S.len * t < 2 * S.len := by omega
    have ht0 : 1 ≤ t := by
      by_contra hc
      have hz : t = 0 := by omega
      rw [hz, Nat.mul_zero] at ht
      omega
    have ht1 : t = 1 := by
      by_contra hne
      have h2 : 2 ≤ t := by omega
      have hm := Nat.mul_le_mul_left S.len h2
      omega
    rw [ht1, Nat.mul_one] at ht
    omega
  · -- `P = Q`, i.e. `e = S.len - 1 + b - a`, so `S.len - e = a - b + 1 ≤ L`:
    -- the complement arc fits inside one read.
    right
    omega
  · -- `Q < P`: then `P = Q + S.len * t`; `t = 0` contradicts `Q < P`, so
    -- `t = 1`, i.e. `P = Q + S.len`, which is the straddling case.
    obtain ⟨t, ht⟩ :=
      (Nat.modEq_iff_exists_eq_add (Nat.le_of_lt hQP)).mp hmod.symm
    have htlt : S.len * t < 2 * S.len := by omega
    have ht0 : 1 ≤ t := by
      by_contra hc
      have hz : t = 0 := by omega
      rw [hz, Nat.mul_zero] at ht
      omega
    have ht1 : t = 1 := by
      by_contra hne
      have h2 : 2 ≤ t := by omega
      have hm := Nat.mul_le_mul_left S.len h2
      omega
    rw [ht1, Nat.mul_one] at ht
    left
    omega

/-! ## Clause 2 of `I_s` bounds the length of every triple repeat -/

/-- **Clause 2 of `I_s` bounds triple-repeat lengths.** If a length-`e` triple
repeat of `S` is all-bridged, then `e + 2 ≤ L ∨ S.len - e ≤ L`. -/
theorem tripleRepeat_bridged_length {α : Type} [DecidableEq α] {L : ℕ}
    {S : Genome α} {R : Finset (Fin S.len)} (hLG : L ≤ S.len)
    (h : InformationFeasible S L R) {e : ℕ} {a b c : Fin S.len}
    (ht : S.IsTripleRepeat e a b c) (heG : e < S.len) (he1 : 1 ≤ e) :
    e + 2 ≤ L ∨ S.len - e ≤ L := by
  obtain ⟨ha, -, -⟩ := h.triples ht heG
  exact bridgingLength hLG he1 heG ha

/-- **The sharp consequence for long triple repeats.** If `R ∈ I_s`, `2 ≤ L`,
`L ≤ S.len`, and the truth carries a triple repeat of length `e` with
`L - 1 ≤ e`, then `S.len - L ≤ e`. -/
theorem informationFeasible_tripleRepeat_ge_G_sub_L {α : Type} [DecidableEq α]
    {L : ℕ} {S : Genome α} {R : Finset (Fin S.len)} (hL2 : 2 ≤ L) (hLG : L ≤ S.len)
    (h : InformationFeasible S L R) {e : ℕ} {a b c : Fin S.len}
    (he1 : L - 1 ≤ e) (heG : e < S.len) (ht : S.IsTripleRepeat e a b c) :
    S.len - L ≤ e := by
  have he1' : 1 ≤ e := by omega
  rcases tripleRepeat_bridged_length hLG h ht heG he1' with h' | h'
  · omega
  · omega

/-! ## The sharp nondegeneracy hypothesis, and the replacement for Fact D -/

/-- **The sharp nondegeneracy hypothesis on the truth.** The truth carries no
triple repeat of length `e` in the bridging-permitted regime
`max (L - 1) (S.len - L) ≤ e`.

This is the weakest hypothesis under which the oriented same-length rigidity
chain can be run: everything strictly below `max (L - 1) (S.len - L)` is
already excluded by clause 2 of `I_s` alone
(`informationFeasible_tripleRepeat_ge_G_sub_L`), and the hypothesis excludes
precisely the wraparound regime that clause 2 cannot reach. -/
def SharpNoLongTripleRepeat {α : Type} [DecidableEq α] {L : ℕ} {S : Genome α} : Prop :=
  ∀ (e : Fin S.len) (a b c : Fin S.len),
    max (L - 1) (S.len - L) ≤ e.val → ¬ S.IsTripleRepeat e.val a b c

/-- A Bresler maximal triple repeat at natural-number starts `a, b, c` of length
`ℓ` is a `Genome.IsTripleRepeat` at the representative starts: distinct residues
give the three pairwise-distinct selected starts and the three agreement
clauses, and the symbol-level three-copy maximality transfers verbatim. -/
theorem isTripleRepeat_of_maximalTriple {α : Type} [DecidableEq α] {S : Genome α}
    {a b c ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓG : ℓ < S.len)
    (hab : a % S.len ≠ b % S.len) (hac : a % S.len ≠ c % S.len)
    (hbc : b % S.len ≠ c % S.len)
    (hag : RepeatAdapter.TripleAgree S.len_pos S.sym a b c ℓ)
    (hpre : ¬ (OrientedRigidity.cyc S.len_pos S.sym (a + S.len - 1) =
          OrientedRigidity.cyc S.len_pos S.sym (b + S.len - 1) ∧
        OrientedRigidity.cyc S.len_pos S.sym (b + S.len - 1) =
          OrientedRigidity.cyc S.len_pos S.sym (c + S.len - 1)))
    (hfol : ¬ (OrientedRigidity.cyc S.len_pos S.sym (a + ℓ) =
          OrientedRigidity.cyc S.len_pos S.sym (b + ℓ) ∧
        OrientedRigidity.cyc S.len_pos S.sym (b + ℓ) =
          OrientedRigidity.cyc S.len_pos S.sym (c + ℓ))) :
    S.IsTripleRepeat ℓ (rep S a) (rep S b) (rep S c) := by
  refine ⟨h1, hℓG, rep_ne hab, rep_ne hac, rep_ne hbc, ?_, ?_, ?_, ?_, ?_⟩
  · intro d
    exact window_of_cyc d (by rw [← cyc_eq_cycl, ← cyc_eq_cycl]; exact (hag d d.isLt).1)
  · intro d
    exact window_of_cyc d (by
      rw [← cyc_eq_cycl, ← cyc_eq_cycl]
      exact (hag d d.isLt).1.trans (hag d d.isLt).2)
  · intro d
    exact window_of_cyc d (by rw [← cyc_eq_cycl, ← cyc_eq_cycl]; exact (hag d d.isLt).2)
  · intro hc
    apply hpre
    refine ⟨?_, ?_⟩
    · calc OrientedRigidity.cyc S.len_pos S.sym (a + S.len - 1)
          = S.Preceding (rep S a) := cycl_to_preceding (S := S) a
        _ = S.Preceding (rep S b) := hc.1
        _ = OrientedRigidity.cyc S.len_pos S.sym (b + S.len - 1) :=
            (cycl_to_preceding (S := S) b).symm
    · calc OrientedRigidity.cyc S.len_pos S.sym (b + S.len - 1)
          = S.Preceding (rep S b) := cycl_to_preceding (S := S) b
        _ = S.Preceding (rep S c) := hc.2
        _ = OrientedRigidity.cyc S.len_pos S.sym (c + S.len - 1) :=
            (cycl_to_preceding (S := S) c).symm
  · intro hc
    apply hfol
    refine ⟨?_, ?_⟩
    · calc OrientedRigidity.cyc S.len_pos S.sym (a + ℓ)
          = S.Following ℓ (rep S a) := cycl_to_following (S := S) a ℓ
        _ = S.Following ℓ (rep S b) := hc.1
        _ = OrientedRigidity.cyc S.len_pos S.sym (b + ℓ) :=
            (cycl_to_following (S := S) b ℓ).symm
    · calc OrientedRigidity.cyc S.len_pos S.sym (b + ℓ)
          = S.Following ℓ (rep S b) := cycl_to_following (S := S) b ℓ
        _ = S.Following ℓ (rep S c) := hc.2
        _ = OrientedRigidity.cyc S.len_pos S.sym (c + ℓ) :=
            (cycl_to_following (S := S) c ℓ).symm

/-- **The replacement for Fact D.** If `R ∈ I_s`, `2 ≤ L ≤ S.len`, and the truth
satisfies the sharp nondegeneracy hypothesis, then the truth has no long
Bresler triple repeat — exactly the hypothesis consumed by
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`.

This is the strongest *true* statement of the `I_s → no long triple repeat`
shape. Without the nondegeneracy hypothesis it is false, as
`AssemblyP1.BridgingWraparoundCounterexample` kernel-checks. -/
theorem informationFeasible_sharp_no_long_triple_repeat {α : Type} [DecidableEq α]
    {L : ℕ} {S : Genome α} {R : Finset (Fin S.len)} (hL2 : 2 ≤ L) (hLG : L ≤ S.len)
    (h : InformationFeasible S L R) (hnr : SharpNoLongTripleRepeat (L := L) (S := S)) :
    ¬ RepeatAdapter.HasLongTripleRepeat S.len_pos S.sym L := by
  intro hlt
  obtain ⟨a, b, c, ℓ, hℓ1, hℓG, hab, hbc, hac, hmax⟩ := hlt
  have h1 : 1 ≤ ℓ := by omega
  obtain ⟨hag, hpre, hfol⟩ := hmax
  have hrep : S.IsTripleRepeat ℓ (rep S a) (rep S b) (rep S c) :=
    isTripleRepeat_of_maximalTriple h1 hℓG hab hac hbc hag hpre hfol
  have hge : S.len - L ≤ ℓ :=
    informationFeasible_tripleRepeat_ge_G_sub_L (L := L) hL2 hLG h hℓ1 hℓG hrep
  exact hnr ⟨ℓ, hℓG⟩ _ _ _ (max_le hℓ1 hge) hrep

end

end AssemblyP1.BridgingBridge
