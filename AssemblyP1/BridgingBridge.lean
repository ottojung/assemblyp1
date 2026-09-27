import AssemblyP1.SourceFaithfulIs
import AssemblyP1.RepeatAdapter

/-!
# What `I_s` really implies about long triple repeats

This module is the *bridge* of issue #88: it turns clause 2 of the
source-faithful `InformationFeasible` predicate into the nondegeneracy fact the
maximum-likelihood reduction needs.

## The result

`informationFeasible_no_long_triple_repeat`: if `2 ≤ L` and `R ∈ I_s`, then

```
¬ RepeatAdapter.HasLongTripleRepeat S.len_pos S.sym L
```

i.e. the truth carries **no** maximal triple repeat of length `e ≥ L - 1`,
whatever the start set is. No bound relating `L` to the genome length is needed.

The proof is short. A long maximal triple repeat is a `Genome.IsTripleRepeat`, so
clause 2 of `I_s` says all three of its copies are bridged; a bridged copy
satisfies `e + 2 ≤ L` (`SourceFaithfulIs.bridgesCopy_length`); and `e ≥ L - 1`
gives `e + 2 ≥ L + 1`.

## Why this used to be false, and what changed

This is the external "Fact D" recorded in `docs/oriented-same-length-ml-88.md` §3.
Until this commit the repository could not prove it, and instead carried

* `bridgingLength : e + 2 ≤ L ∨ G - e ≤ L`, whose second disjunct was the
  "wraparound mode", and
* `AssemblyP1.WraparoundTripleRepeat`, a kernel-checked instance (`AAAAB`,
  `G = 5`, `L = 3`, all five starts) of `R ∈ I_s` together with a long triple
  repeat, i.e. a kernel-checked *counterexample* to Fact D,

and a whole research programme (`AssemblyP1.MLEscape`,
`docs/issue88-wraparound-contrapositive.md`) built on the resulting
"wraparound regime".

Both rested on an endpoint-only reading of `SourceFaithfulIs.BridgesCopy`: that a
copy is bridged when a realized read covers `(t-1) % G` and covers `(t+e) % G`.
That is not the source's condition. Bresler et al. and Shomorony et al. require
one read to *strictly straddle* the occurrence, i.e. on a suitable lift
`r < t` and `t + e < r + L` (`docs/bridging-source-semantics.md`); the
endpoint-only reading lets a read reach a long copy's two endpoints by travelling
around the *complementary* circular arc without ever containing the copy. The
corrected `BridgesCopy` (a single read, a single offset `d`, the copy at offset
`d+1`, with `d + e + 1 < L`) rules that out, `bridgesCopy_length` follows, and
the wraparound regime is empty.

`bridgingLength` is kept with its old two-disjunct shape, and its second
disjunct is now unreachable, only so that downstream references do not break.

## Layout

* `bridgingLength` — the two-disjunct statement, now degenerate.
* `tripleRepeat_bridged_length`, `informationFeasible_tripleRepeat_ge_G_sub_L` —
  the clause-2 length bounds, kept because they remain true and are used by
  `AssemblyP1.MLEscape` to name the band clause 2 forbids.
* `isTripleRepeat_of_maximalTriple` — the `RepeatAdapter` ↔ `Genome` transfer.
* `informationFeasible_no_long_triple_repeat` — the result above.
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
  simp only [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

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

* `e + 2 ≤ L`: the bridging read strictly straddles the copy, entering before
  `t - 1` and leaving after `t + e`.

Up to this commit the statement had a second disjunct, `S.len - e ≤ L`,
corresponding to a "bridging" read that reaches the copy's two endpoints by
travelling around the *complementary* circular arc. That disjunct was an
artifact of an endpoint-only reading of `BridgesCopy` which is not the source's
condition (`docs/bridging-source-semantics.md`); with the corrected
`BridgesCopy` the first disjunct is forced, and
`AssemblyP1.SourceFaithfulIs.bridgesCopy_length` is the one-line reason. The
statement is kept with its old shape so that downstream references do not
break. -/
theorem bridgingLength {α : Type} [DecidableEq α] {L e : ℕ} {S : Genome α}
    {R : Finset (Fin S.len)} {t : Fin S.len} (_hLG : L ≤ S.len)
    (_he : 1 ≤ e) (_heG : e < S.len) (hb : BridgesCopy S L R e t) :
    e + 2 ≤ L ∨ S.len - e ≤ L :=
  Or.inl (bridgesCopy_length hb)

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

/-! ## Full `I_s` excludes long triple repeats outright -/

/-- **Full source-faithful `I_s` excludes every long Bresler triple repeat.**

If `2 ≤ L` and `R ∈ I_s`, then the truth carries no maximal triple repeat of
length `e ≥ L - 1`, whatever the start set is.

The argument is one line of arithmetic once `bridgesCopy_length` is available: a
long triple repeat is a triple repeat of clause 2, so `I_s` makes all three of
its copies bridged, and a bridged copy satisfies `e + 2 ≤ L`, whereas
`e ≥ L - 1` gives `e + 2 ≥ L + 1`.

This is the statement that `docs/oriented-same-length-ml-88.md` §3 recorded as
the external "Fact D". Up to this commit the repository could not prove it, and
`AssemblyP1.WraparoundTripleRepeat` kernel-checked its *negation* (`AAAAB` at
`G = 5`, `L = 3`, all five starts) on the strength of an endpoint-only reading
of `BridgesCopy` that let a read reach a copy's two endpoints around the
complementary circular arc. That reading is not the source's condition
(`docs/bridging-source-semantics.md`); under the corrected `BridgesCopy` the
instance is not `I_s`-feasible and the whole "wraparound" regime disappears.
`L ≤ S.len` is not needed: `bridgesCopy_length` is unconditional. -/
theorem informationFeasible_no_long_triple_repeat {α : Type} [DecidableEq α]
    {L : ℕ} {S : Genome α} {R : Finset (Fin S.len)} (_hL2 : 2 ≤ L)
    (h : InformationFeasible S L R) :
    ¬ RepeatAdapter.HasLongTripleRepeat S.len_pos S.sym L := by
  rintro ⟨a, b, c, ℓ, hLong, hEllG, hab, hbc, hac, hmax⟩
  have h1 : 1 ≤ ℓ := by omega
  obtain ⟨hag, hpre, hfol⟩ := hmax
  have hrep : S.IsTripleRepeat ℓ (rep S a) (rep S b) (rep S c) :=
    isTripleRepeat_of_maximalTriple h1 hEllG hab hac hbc hag hpre hfol
  have hall := h.triples hrep hEllG
  have hlen : ℓ + 2 ≤ L := bridgesCopy_length hall.1
  omega

end

end AssemblyP1.BridgingBridge
