import AssemblyP1.Issue94TW6Lemma1
import AssemblyP1.Issue94TW5Single

/-!
# Board 94, front tw7: the purely combinatorial step is **`FALSE` as the
# board stated it**, and the correct replacement is `VertexCycleEq`, not
# `AltF = id`

This module is the answer to tw6 §8 point 8(b) and to the briefing of this
front.  **The primary obligation as assigned — "`Ukkonen` plus label-preserving
implies `AltF = id`" — is not proved, because it is false.**  §3 below is a
kernel-checked counterexample, and §2 is the kernel-checked *characterisation*
of what "`AltF = id`" actually means, which is the reason the assigned
statement fails: `AltF = id` is equivalent to the pull-back `σ` being a
**rotation of the circle**, and that is far stronger than what `thm:BBT`
asserts and far stronger than `Ukkonen` implies.

`BBTLadder.lean:559-560` had already recorded the correct target in prose
("`VertexCycleEq`, never start-level equality and never `AltF = id`").  This
module turns that prose warning into a theorem.

`hPevzner` is **not** discharged; see §7.

## What "label-preserving" and "`AltF = id`" mean here, quoted not paraphrased

`AssemblyP1/Issue94TW5Single.lean:249-250` (`tw5`'s object, RELAYED as the
definition, quoted verbatim):

```lean
def LabelPreserving (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G) : Prop :=
  ∀ q : Fin G, vtx hG L S (AltF hG σ q) = vtx hG L S q
```

`AssemblyP1/BBTUniqueEulerian.lean:665-666`:

```lean
def AltF {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) (q : Fin G) : Fin G :=
  Succ hG σ (prevPos hG q)
```

So "`AltF = id`" is read as `∀ q : Fin G, AltF hG σ q = q`, pointwise on the
starts, i.e. **the alternative traversal's successor fixes every start**.

`AssemblyP1/BBTChords.lean:87-88`:

```lean
def IsRotation (hG : 0 < G) (R : Fin G → Fin G) : Prop :=
  ∃ s : ℕ, ∀ x : Fin G, R x = rotAdd hG s x
```

and `AssemblyP1/BBTEulerian.lean:181-182`:

```lean
def VertexCycleEq (σ τ : Fin G ≃ Fin G) : Prop :=
  ∃ k : Fin G, ∀ i : Fin G, vtx hG L S (σ i) = vtx hG L S (rotAdd hG k.val (τ i))
```

`AssemblyP1/P2.lean:91-96` (`Ukkonen`, quoted verbatim):

```lean
def Ukkonen (hG : 0 < G) (L : ℕ) (S : Fin G → α) : Prop :=
  (∀ e a b c : Fin G, (mkGenome hG S).IsTripleRepeat e a b c → e.val < L - 1) ∧
    (∀ (e₁ e₂ : Fin G) (a b c d : Fin G), (mkGenome hG S).IsRepeat e₁ a b →
      (mkGenome hG S).IsRepeat e₂ c d →
      Interleaved (mkGenome hG S) a b c d →
      e₁.val < L - 1 ∨ e₂.val < L - 1)
```

## The main theorem

`altF_eq_id_iff_rotation`, in
`AssemblyP1.Issue94TW7AltF.altF_eq_id_iff_rotation`:

```lean
theorem altF_eq_id_iff_rotation {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    (∀ q : Fin G, AltF hG σ q = q) ↔ IsRotation hG (σ : Fin G → Fin G)
```

*Proof sketch, in the repository's own vocabulary.*  `AltF hG σ (nextPos hG x) =
Succ hG σ x` (`AltF_succ`), so `AltF = id` is `Succ hG σ = nextPos hG`, i.e.
`σ ∘ ρ ∘ σ⁻¹ = ρ` for `ρ = nextPos hG`, i.e. `σ` **commutes with the one-step
rotation**.  A map commuting with `ρ` is a rotation of the circle
(`comm_nextPos_isRotation`): iterating the commutation gives
`σ (rotAdd hG n y) = rotAdd hG n (σ y)`, and evaluating at the origin, whose
orbit under `ρ` is all of `Fin G`, pins the shift to be `(σ 0).val`.  ∎

The direction "`IsRotation` ⟹ `AltF = id`" is the easy one: a rotation
commutes with `ρ`, so `Succ σ = σ ρ σ⁻¹ = ρ`.

**This characterisation is unconditional**: it mentions no word, no `L`, no
`vtx`, no `Ukkonen`, no `P2`, no primitivity.  It is a fact about
`BBTUniqueEulerian.AltF` and `BBTChords.IsRotation` alone, and it is
ESTABLISHED here, not RELAYED.

## The refutation of the assigned obligation

`AssemblyP1/BBTEulerian.lean:520-524` defines the anti-vacuity instance, which
this module reuses (RELAYED as the instance, ESTABLISHED as the two new facts
about it):

```lean
def S4 : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def tau4 : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
```

| theorem | statement | how |
| --- | --- | --- |
| `ukk_S4` | `Ukkonen hG4 3 S4` | `decide +kernel` |
| `labelPreserving_S4` | `LabelPreserving hG4 3 S4 tau4` | `decide +kernel` |
| `altF_S4_ne` | `AltF hG4 tau4 0 ≠ 0` | `decide +kernel` |
| `not_ukk_then_not_altF` | `Ukkonen hG4 3 S4 → LabelPreserving hG4 3 S4 tau4 → AltF hG4 tau4 0 ≠ 0` | from the three above |

So at `G = 4`, `L = 3` (so `K = L - 1 = 2`), the word `0101` **satisfies
`Ukkonen`**, `tau4` **is** label-preserving, and `AltF` **is not** the
identity.  `¬ IsRotation hG4 tau4` is already in the tree
(`BBTEulerian.not_rotation_S4`), which by `altF_eq_id_iff_rotation` is the
same fact read in the other vocabulary.

**Why this does not contradict `thm:BBT`.**  `tau4` is a *presentation* of the
truth's own Eulerian cycle read from a different start:
`BBTEulerian.trivial_vertexCycleEq_S4` already proves
`VertexCycleEq hG4 3 S4 tau4 (Equiv.refl _)`.  `VertexCycleEq` is the object
`EulerianCycleObstruction` (`BBTEulerian.lean:415-418`) actually quantifies
over.  `AltF = id` is a strictly stronger, *start-level* statement, and
`BBTEulerian`'s own §4.2 was written precisely to warn that it is the wrong
hypothesis.

## The correct purely combinatorial step, and the exact point where it stops

`vtx_nextPos_shift` and `node_prefix` (§4) are the unconditional combinatorial
content of the *correct* route.  `node_prefix` says: for every `n < G` and
every `d e : Fin (L - 1)` with `e.val = d.val + n` and `e.val < L - 1`,

```text
   vtx (σ n) d = vtx (σ 0) e
```

**No `Ukkonen`, no `P2`, no primitivity, no repeat theory, no `AltF`.**  The
node at listing position `n` is pinned to the truth's node at `σ 0` on
coordinates `0 … L-2-n`, and on no others.

**The full step `traverses ⟹ VertexCycleEq` is NOT proved, and I checked that
it does not compile rather than assuming it.**  A draft induction aiming at
the point-level chain

```text
   σ (rotAdd n y) = rotAdd n (σ (origin hG))
```

fails at exactly one step, with the residual goal

```text
   rotAdd hG 1 (σ ⟨n, hnG⟩) = rotAdd hG (n + 1) (σ (origin hG))
```

`rw [← hbase, rotAdd_add, Nat.add_comm]` reports *"Did not find an occurrence
of the pattern `vtx hG L S (rotAdd hG n (σ (origin hG)))`"*.  The reason is
precise and is **not** a syntactic accident: the induction hypothesis `hbase`
is an equality of **vertices**, `vtx (σ n) = vtx (rotAdd n (σ 0))`, while the
residual goal is an equality of **points of `Fin G`**,
`σ (n + 1) = rotAdd (n + 1) (σ 0)`.  Promoting the former to the latter
requires `vtx`-injectivity along the listing, which is exactly the
repeat-theoretic content `Ukkonen` is supposed to supply and which is **not**
in the tree.  **I am flagging this rather than reporting `hPevzner` as
discharged.**

A second, independent obstruction to the same step is that even the *vertex*
identity does not follow from `traverses` alone: `vtx_nextPos_shift` loses the
last coordinate of the node at every step (`d` is read from coordinate `d + 1`,
and there is no coordinate `L - 1` to read), so after `n` steps `n`
coordinates of the node remain unconstrained.  `node_prefix` is what survives
once both obstructions are respected.

## What is proved, and what is not

* **Proved (kernel-checked).**
  - `comm_nextPos_isRotation`, `altF_eq_id_iff_rotation` — the unconditional
    characterisation of "`AltF = id`" as "`σ` is a rotation of the circle".
    This is the main theorem of the front.
  - `vtx_nextPos_shift`, `node_prefix` — the unconditional de Bruijn-shift
    content of `traverses`, and its exact extent.
  - `ukk_S4`, `labelPreserving_S4`, `altF_S4_ne`, `not_ukk_then_not_altF`,
    `not_ukk_then_not_rotation`, `refutation_is_nonvacuous` — the refutation of
    the assigned obligation, and its non-vacuity.
  - The anti-vacuity facts `S4_length`, `S4_vtx_02`, `S4_vtx_13`, `S4_vtx_01`,
    `S4_consistent`, `not_labelPreserving_altF_id`, `traverses_is_restrictive`.
  - The hand-built `Decidable` instances `dTR` and `dIL` plus the three
    registered instances built from them.  The brief's prediction that
    `infer_instance` does not build `Decidable (∀ a b c : Fin G, …)` is
    **CONFIRMED** at `Fin 4`: `decide` and `infer_instance` both fail, and
    `Fintype.decidableForallFintype` must be applied layer by layer under
    `letI : DecidablePred`.
* **Refuted.**  The assigned obligation, at `S = 0101`, `G = 4`, `L = 3`.
* **Not proved.**  `BBTEulerian.EulerianCycleObstruction`, i.e. `hPevzner`
  (`AssemblyP1/PopulationUniqueness.lean` lines 164, 217, 247) — **unchanged
  and still a hypothesis.**  `BBTEulerian.UniqueEulerianCycle` — unchanged.
  `BBTLadder.LadderVertexCycle`, `BBTUniqueEulerian` Lemma 2,
  `AssemblyP1/BBTTripleBridge.lean` — untouched.  No `sorry`, no `admit`, no
  `native_decide`, no new axiom, no theorem statement weakened, no `def`
  changed.  The `Decidable` instances here are instances only.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace AssemblyP1.Issue94TW7AltF

open SourceFaithfulIs
open OrientedRigidity
open PopulationReduction
open AssemblyP1
open AssemblyP1.BBTChords
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.Issue94TW5Single

/-! ## 1. A map commuting with the one-step rotation is a rotation of the
circle -/

/-- **A map commuting with `nextPos` is a rotation.**  If `f ∘ ρ = ρ ∘ f` for
the one-step rotation `ρ` of a circle of `G` positions, then `f` is the
rotation by `(f 0).val`.

Purely combinatorial: no word, no window, no `vtx`, no `Ukkonen`.  The proof
iterates the commutation (`hit`) and then evaluates at the origin, whose orbit
under `ρ` is all of `Fin G` (`hcov`). -/
theorem comm_nextPos_isRotation {G : ℕ} (hG : 0 < G) (f : Fin G → Fin G)
    (hcomm : ∀ y : Fin G, f (nextPos hG y) = nextPos hG (f y)) :
    IsRotation hG f := by
  have hstep : ∀ (n : ℕ) (z : Fin G),
      rotAdd hG (n + 1) z = nextPos hG (rotAdd hG n z) := by
    intro n z
    rw [nextPos, rotAdd_add, Nat.add_comm]
  have hit : ∀ (n : ℕ) (y : Fin G), f (rotAdd hG n y) = rotAdd hG n (f y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
        intro y
        calc f (rotAdd hG (n + 1) y)
            = f (nextPos hG (rotAdd hG n y)) := by rw [hstep]
          _ = nextPos hG (f (rotAdd hG n y)) := hcomm _
          _ = nextPos hG (rotAdd hG n (f y)) := by rw [ih y]
          _ = rotAdd hG (n + 1) (f y) := (hstep n (f y)).symm
  refine ⟨(f (origin hG)).val, fun x => ?_⟩
  have hcov : rotAdd hG x.val (origin hG) = x := by
    apply Fin.ext
    simp only [rotAdd, origin, Fin.val_mk, Nat.zero_add]
    exact Nat.mod_eq_of_lt x.isLt
  have h1 := hit x.val (origin hG)
  have h2 : rotAdd hG x.val (f (origin hG)) = rotAdd hG (f (origin hG)).val x := by
    apply Fin.ext
    simp only [rotAdd, Fin.val_mk]
    exact congrArg (fun t => t % G) (Nat.add_comm _ _)
  calc f x = f (rotAdd hG x.val (origin hG)) := by rw [hcov]
    _ = rotAdd hG x.val (f (origin hG)) := h1
    _ = rotAdd hG (f (origin hG)).val x := h2

/-! ## 2. `AltF = id` is exactly "`σ` is a rotation of the circle"

This is the load-bearing result of the front, and it is what makes the
assigned obligation false: `AltF = id` is a **start-level** statement, strictly
stronger than the `VertexCycleEq` that `EulerianCycleObstruction` asks for. -/

/-- **`AltF hG σ` is the identity on the starts exactly when the pull-back `σ`
is a rotation of the circle.**

`AltF hG σ (nextPos hG x) = Succ hG σ x` (`BBTUniqueEulerian.AltF_succ`), so

```text
   AltF = id   ⟺   Succ hG σ = nextPos hG
                  ⟺   σ ∘ ρ ∘ σ⁻¹ = ρ          (ρ = nextPos hG)
                  ⟺   σ ∘ ρ = ρ ∘ σ
                  ⟺   IsRotation hG σ          (comm_nextPos_isRotation)
```

Unconditional: no `S`, no `L`, no `vtx`, no `Ukkonen`, no `P2`, no primitivity,
no repeat theory.  This is a theorem about `BBTUniqueEulerian.AltF` and
`BBTChords.IsRotation` alone. -/
theorem altF_eq_id_iff_rotation {G : ℕ} (hG : 0 < G) (σ : Fin G ≃ Fin G) :
    (∀ q : Fin G, AltF hG σ q = q) ↔ IsRotation hG (σ : Fin G → Fin G) := by
  constructor
  · intro h
    have hsucc : ∀ x : Fin G, Succ hG σ x = nextPos hG x := by
      intro x
      have hx := h (nextPos hG x)
      rwa [AltF_succ] at hx
    refine comm_nextPos_isRotation hG (σ : Fin G → Fin G) ?_
    intro y
    have h2 := hsucc (σ y)
    unfold Succ at h2
    simpa only [Equiv.symm_apply_apply] using h2
  · rintro ⟨s, hs⟩ q
    have hsucc : ∀ x : Fin G, Succ hG σ x = nextPos hG x := by
      intro x
      unfold Succ
      calc σ (nextPos hG (σ.symm x))
          = rotAdd hG s (nextPos hG (σ.symm x)) := hs _
        _ = rotAdd hG (s + 1) (σ.symm x) := rotAdd_add hG s 1 _
        _ = nextPos hG (rotAdd hG s (σ.symm x)) := by
            rw [Nat.add_comm, nextPos, rotAdd_add]
        _ = nextPos hG x := by
            have e := congrArg (nextPos hG) (hs (σ.symm x))
            have e2 : nextPos hG (rotAdd hG s (σ.symm x))
                = nextPos hG (σ (σ.symm x)) := e.symm
            rwa [Equiv.apply_symm_apply] at e2
    have hx : AltF hG σ q = nextPos hG (prevPos hG q) := by
      simp only [AltF]
      rw [hsucc]
    rw [hx, nextPrev]

/-! ## 3. The assigned obligation is FALSE: a kernel-checked counterexample

The instance is `BBTEulerian`'s own §4.2 anti-vacuity example
(`BBTEulerian.lean:520-524`), reused.  `S4 = 0101` on four positions, `L = 3`
so `K = L - 1 = 2`, and `tau4 = (0 1)(2 3)`. -/

instance decAgree4 (e : ℕ) (a b : Fin 4) :
    Decidable ((mkGenome hG4 S4).Agree e a b) := by
  unfold SourceFaithfulIs.Genome.Agree
  infer_instance

instance decIsTripleRepeat4 (e : ℕ) (a b c : Fin 4) :
    Decidable ((mkGenome hG4 S4).IsTripleRepeat e a b c) := by
  show Decidable (1 ≤ e ∧ e < 4 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (mkGenome hG4 S4).Agree e a b ∧ (mkGenome hG4 S4).Agree e a c ∧
      (mkGenome hG4 S4).Agree e b c ∧
      ¬((mkGenome hG4 S4).Preceding a = (mkGenome hG4 S4).Preceding b ∧
        (mkGenome hG4 S4).Preceding b = (mkGenome hG4 S4).Preceding c) ∧
      ¬((mkGenome hG4 S4).Following e a = (mkGenome hG4 S4).Following e b ∧
        (mkGenome hG4 S4).Following e b = (mkGenome hG4 S4).Following e c))
  infer_instance

instance decIsRepeat4 (e : ℕ) (a b : Fin 4) :
    Decidable ((mkGenome hG4 S4).IsRepeat e a b) := by
  show Decidable (1 ≤ e ∧ e < 4 ∧ a ≠ b ∧ (mkGenome hG4 S4).Agree e a b ∧
      (mkGenome hG4 S4).Preceding a ≠ (mkGenome hG4 S4).Preceding b ∧
      (mkGenome hG4 S4).Following e a ≠ (mkGenome hG4 S4).Following e b)
  infer_instance

instance decInterleaved4 (a b c d : Fin 4) :
    Decidable (Interleaved (mkGenome hG4 S4) a b c d) := by
  unfold SourceFaithfulIs.Interleaved SourceFaithfulIs.FourDistinct
  show Decidable ((a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ∧
      ((0 < (c.val + 4 - a.val) % 4 ∧ (c.val + 4 - a.val) % 4 < (b.val + 4 - a.val) % 4) ↔
        ¬(0 < (d.val + 4 - a.val) % 4 ∧ (d.val + 4 - a.val) % 4 < (b.val + 4 - a.val) % 4)))
  infer_instance

/-- **`Decidable` for the `∀`-over-`Fin 4` triple-repeat clause, built by
hand, layer by layer.**

The brief's warning is CONFIRMED in this pin: `decide` and `infer_instance`
both fail to synthesise `Decidable (∀ e a b c : Fin 4, …)`, because
`Fintype.decidableForallFintype` needs a `DecidablePred` for the *next*
binder and the recursion bottoms out in a failed leaf search.  Each layer is
therefore introduced with `letI : DecidablePred … := by intro …` and
`Fintype.decidableForallFintype` is applied explicitly.  This is an instance
for the counterexample word `S4` only; no definition is changed. -/
def dTR (L : ℕ) : Decidable (∀ e a b c : Fin 4,
    (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < L - 1) := by
  letI : DecidablePred (fun e : Fin 4 => ∀ a b c : Fin 4,
      (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < L - 1) := by
    intro e
    letI : DecidablePred (fun a : Fin 4 => ∀ b c : Fin 4,
        (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < L - 1) := by
      intro a
      letI : DecidablePred (fun b : Fin 4 => ∀ c : Fin 4,
          (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < L - 1) := by
        intro b
        letI : DecidablePred (fun c : Fin 4 =>
            (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < L - 1) := by
          intro c
          infer_instance
        exact Fintype.decidableForallFintype
      exact Fintype.decidableForallFintype
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- ... and the same, for the interleaved-repeat clause of `Ukkonen`. -/
def dIL (L : ℕ) : Decidable (∀ (e₁ e₂ : Fin 4) (a b c d : Fin 4),
    (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
    Interleaved (mkGenome hG4 S4) a b c d →
    e₁.val < L - 1 ∨ e₂.val < L - 1) := by
  letI : DecidablePred (fun e₁ : Fin 4 => ∀ (e₂ : Fin 4) (a b c d : Fin 4),
      (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
      Interleaved (mkGenome hG4 S4) a b c d →
      e₁.val < L - 1 ∨ e₂.val < L - 1) := by
    intro e₁
    letI : DecidablePred (fun e₂ : Fin 4 => ∀ (a b c d : Fin 4),
        (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
        Interleaved (mkGenome hG4 S4) a b c d →
        e₁.val < L - 1 ∨ e₂.val < L - 1) := by
      intro e₂
      letI : DecidablePred (fun a : Fin 4 => ∀ (b c d : Fin 4),
          (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
          Interleaved (mkGenome hG4 S4) a b c d →
          e₁.val < L - 1 ∨ e₂.val < L - 1) := by
        intro a
        letI : DecidablePred (fun b : Fin 4 => ∀ (c d : Fin 4),
            (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
            Interleaved (mkGenome hG4 S4) a b c d →
            e₁.val < L - 1 ∨ e₂.val < L - 1) := by
          intro b
          letI : DecidablePred (fun c : Fin 4 => ∀ (d : Fin 4),
              (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
              Interleaved (mkGenome hG4 S4) a b c d →
              e₁.val < L - 1 ∨ e₂.val < L - 1) := by
            intro c
            letI : DecidablePred (fun d : Fin 4 =>
                (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
                Interleaved (mkGenome hG4 S4) a b c d →
                e₁.val < L - 1 ∨ e₂.val < L - 1) := by
              intro d
              infer_instance
            exact Fintype.decidableForallFintype
          exact Fintype.decidableForallFintype
        exact Fintype.decidableForallFintype
      exact Fintype.decidableForallFintype
    exact Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

/-- The two `Decidable` instances for `Ukkonen hG4 3 S4`, registered at
namespace level so that `decide` can use them.  These are instances for the
counterexample word `S4` only; no definition is changed. -/
instance decUkk_triple_S4_L3 : Decidable (∀ e a b c : Fin 4,
    (mkGenome hG4 S4).IsTripleRepeat e a b c → e.val < 3 - 1) := dTR 3

instance decUkk_interleaved_S4_L3 : Decidable (∀ (e₁ e₂ : Fin 4) (a b c d : Fin 4),
    (mkGenome hG4 S4).IsRepeat e₁ a b → (mkGenome hG4 S4).IsRepeat e₂ c d →
    Interleaved (mkGenome hG4 S4) a b c d →
    e₁.val < 3 - 1 ∨ e₂.val < 3 - 1) := dIL 3

/-- The `Decidable` instance for `Ukkonen hG4 3 S4` itself, assembled from the
two hand-built clause instances.  Needed because instance search will not
unfold the `def Ukkonen` to find the conjunction. -/
instance decUkk_S4_L3 : Decidable (Ukkonen hG4 3 S4) := by
  unfold Ukkonen
  infer_instance

/-- **`S4 = 0101` at `L = 3` satisfies `Ukkonen`.**  Kernel-checked with
`decide +kernel`, i.e. by the kernel reduction checker and not by the
compiler.  Both clauses are decided at the hand-built instances `dTR 3` and
`dIL 3`. -/
theorem ukk_S4 : Ukkonen hG4 3 S4 := by decide +kernel

/-- ... and `tau4` is label-preserving at the same `(hG, L, S)`.  RELAYED from
`BBTEulerian.eulerianCycle_S4` together with tw5's
`labelPreserving_iff_traverses`, and independently re-checked here by
`decide +kernel`. -/
theorem labelPreserving_S4 : LabelPreserving hG4 3 S4 tau4 := by decide +kernel

/-- **... and `AltF` is not the identity on it.**  This is tw5's
`altF_S4_ne`, re-established here on the same instance. -/
theorem altF_S4_ne : AltF hG4 tau4 (0 : Fin 4) ≠ 0 := by decide +kernel

/-- **THE ASSIGNED OBLIGATION IS FALSE.**

`Ukkonen` and label-preservation, together, do **not** give `AltF = id`.  The
witness is `S = 0101`, `G = 4`, `L = 3` (so `K = L - 1 = 2`), `σ = tau4`.

Read through `altF_eq_id_iff_rotation` this is the same statement as
`¬ IsRotation hG4 tau4`, which is `BBTEulerian.not_rotation_S4`, already in
the tree at `e3fe5a5`; the three hypotheses above are the new content. -/
theorem not_ukk_then_not_altF :
    Ukkonen hG4 3 S4 → LabelPreserving hG4 3 S4 tau4 → AltF hG4 tau4 0 ≠ 0 :=
  fun _ _ => altF_S4_ne

/-- The same refutation in the `IsRotation` vocabulary of
`altF_eq_id_iff_rotation`, so that a reader who prefers that formulation does
not have to translate. -/
theorem not_ukk_then_not_rotation :
    Ukkonen hG4 3 S4 → LabelPreserving hG4 3 S4 tau4 → ¬ IsRotation hG4 tau4 := by
  intro hUkk hLP hRot
  exact altF_S4_ne ((altF_eq_id_iff_rotation hG4 tau4).mpr hRot (0 : Fin 4))

/-! ## 4. The correct purely combinatorial step, and the exact point where it
stops

This is the step the front was asked for, with `VertexCycleEq` — the object
`EulerianCycleObstruction` actually quantifies over — in place of the
(stronger, false) `AltF = id`.  Two unconditional results:

* `vtx_nextPos_shift`, the de Bruijn shift at the node level;
* `node_prefix`, the maximal extent of what `traverses` determines.

**And a negative result, which is the point of this section:** the
*full* step `traverses ⟹ VertexCycleEq` is **not** provable by the chain
induction, and I checked that it does not compile rather than assuming it. -/

/-- **The de Bruijn shift at the node level.**  The `d`-th symbol of the
`(L-1)`-mer at `r + 1` is the `(d+1)`-th symbol of the `(L-1)`-mer at `r`, for
every `d` with `d + 1 < L - 1`.

**This is where the open content lives, and the bound is the whole story.**
The shift loses the *last* coordinate of the node: it determines coordinate `d`
of the node at `r + 1` from coordinate `d + 1` of the node at `r`, and there is
no coordinate `L - 1` of the node at `r` to read.  So one traversal step
consumes one unit of the window budget, and after `n` steps only coordinates
`0, …, L - 2 - n` are pinned down. -/
theorem vtx_nextPos_shift {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ)
    (S : Fin G → α) (r : Fin G) (d : Fin (L - 1)) (hd : d.val + 1 < L - 1) :
    vtx hG L S (nextPos hG r) d = vtx hG L S r ⟨d.val + 1, hd⟩ := by
  have h1 := cyc_add (hG := hG) (S := S) (r.val + 1) d.val
  show cyc hG S ((r.val + 1) % G + d.val) = cyc hG S (r.val + (d.val + 1))
  rw [← h1]
  congr 1
  omega

/-- **What `traverses` determines: the first `L - 1 - n` coordinates of the
node at listing position `n`.**

For every `n < G` and every `d < e.val < L - 1` with `e.val = d.val + n`:

```text
   vtx (σ n) d = vtx (σ 0) e
```

Unconditional: no `Ukkonen`, no `P2`, no primitivity, no repeat theory, no
`AltF`.  Only the `traverses` clause `h` and the de Bruijn shift.

**Read the hypothesis as the finding:** the node at listing position `n` is
pinned to the truth's node at `σ 0` **only on coordinates `0 … L-2-n`**.  The
remaining `n` coordinates are exactly what `traverses` does not constrain, and
closing them is the open content of `thm:BBT` on this object. -/
theorem node_prefix {α : Type} [DecidableEq α] {G : ℕ} (hG : 0 < G) (L : ℕ)
    (S : Fin G → α) (σ : Fin G ≃ Fin G)
    (h : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) :
    ∀ (n : ℕ) (hn1 : n < G) (d e : Fin (L - 1)) (he : e.val < L - 1)
      (hde : e.val = d.val + n),
      vtx hG L S (σ ⟨n, hn1⟩) d = vtx hG L S (σ (origin hG)) e := by
  intro n
  induction n with
  | zero =>
      intro hn1 d e he hde
      have hed : e = d := Fin.ext hde
      rw [hed]
      have ho : ((⟨0, hn1⟩ : Fin G) : Fin G) = origin hG := by
        apply Fin.ext
        rfl
      rw [ho]
  | succ n ih =>
      intro hn1 d e he hde
      have hnG : n < G := Nat.lt_trans (Nat.lt_succ_self n) hn1
      have hd : d.val + 1 < L - 1 := by omega
      have hshift := vtx_nextPos_shift hG L S (σ ⟨n, hnG⟩) d hd
      have htrav := h ⟨n, hnG⟩
      have hpos : nextPos hG ⟨n, hnG⟩ = ⟨n + 1, hn1⟩ := by
        apply Fin.ext
        show (n + 1) % G = n + 1
        exact Nat.mod_eq_of_lt hn1
      have hnext : vtx hG L S (nextPos hG (σ ⟨n, hnG⟩)) d
          = vtx hG L S (σ ⟨n, hnG⟩) ⟨d.val + 1, hd⟩ := hshift
      have hde' : e.val = (d.val + 1) + n := by omega
      rw [← hpos, htrav, hnext, ih hnG ⟨d.val + 1, hd⟩ e he hde']

/-! **The point-level chain does not go through, and here is the exact
residual goal.**  A draft induction aiming at

```lean
theorem chain {G : ℕ} (hG : 0 < G) (L : ℕ) (S : Fin G → α) (σ : Fin G ≃ Fin G)
    (h : ∀ i : Fin G, vtx hG L S (σ (nextPos hG i)) = vtx hG L S (nextPos hG (σ i))) :
    ∀ n : ℕ, n ≤ G → ∀ i : Fin G, i.val = n →
      vtx hG L S (σ i) = vtx hG L S (rotAdd hG n (σ (origin hG)))
```

fails at exactly one step, with the residual goal

```text
   rotAdd hG 1 (σ ⟨n, hnG⟩) = rotAdd hG (n + 1) (σ (origin hG))
```

`rw [← hbase, rotAdd_add, Nat.add_comm]` reports *"Did not find an occurrence
of the pattern `vtx hG L S (rotAdd hG n (σ (origin hG)))`"*.  The reason is
precise and is **not** a syntactic accident: the induction hypothesis `hbase`
is an equality of **vertices**, `vtx (σ n) = vtx (rotAdd n (σ 0))`, while the
residual goal is an equality of **points of `Fin G`**,
`σ (n + 1) = rotAdd (n + 1) (σ 0)`.  Promoting
the former to the latter requires `vtx`-injectivity along the listing, which is
precisely the repeat-theoretic content that `Ukkonen` is supposed to supply
and which is **not** in the tree.  `node_prefix` is what survives of the chain
once the promotion is refused. -/

/-! ## 5. Anti-vacuity: the statements of §2-§4 are not trivially true -/

/-- **`S4` is a genuine `Ukkonen` instance, not a degenerate one.**  Anti-
vacuity for the refutation of §3: if `Ukkonen hG4 3 S4` were false the
refutation would be vacuous.  `S4` really does carry the `(L-1)`-mer
multigraph with two nodes and two edges each, and `Ukkonen` really does hold,
so the refutation is about a real word. -/
theorem S4_length : S4 0 = 0 ∧ S4 1 = 1 ∧ S4 2 = 0 ∧ S4 3 = 1 := by decide

/-- ... and the two `vtx` values really are *equal* at the two starts `tau4`
exchanges, so `tau4` is genuinely label-preserving rather than trivially so. -/
theorem S4_vtx_02 : vtx hG4 3 S4 (0 : Fin 4) = vtx hG4 3 S4 (2 : Fin 4) := by decide

theorem S4_vtx_13 : vtx hG4 3 S4 (1 : Fin 4) = vtx hG4 3 S4 (3 : Fin 4) := by decide

/-- ... and they are *not all* equal, so the labelling is not constant and
`labelPreserving_S4` is not the trivial `True`. -/
theorem S4_vtx_01 : vtx hG4 3 S4 (0 : Fin 4) ≠ vtx hG4 3 S4 (1 : Fin 4) := by decide

/-- **`AltF` genuinely moves a point on a `Ukkonen` word.**  This is the
non-vacuity witness for the whole front: it exhibits a `Ukkonen` word and a
label-preserving pull-back on which the assigned conclusion fails, so
`not_ukk_then_not_altF` is a real refutation and not an artefact of a
degenerate instance. -/
theorem refutation_is_nonvacuous :
    Ukkonen hG4 3 S4 ∧ LabelPreserving hG4 3 S4 tau4 ∧ AltF hG4 tau4 0 ≠ 0 :=
  ⟨ukk_S4, labelPreserving_S4, altF_S4_ne⟩

/-- **The three facts of §3 are jointly consistent**, so no one of them is
carrying a hidden contradiction: `S4` has length four, `tau4` is not a
rotation, and `AltF` moves a point. -/
theorem S4_consistent : S4 (0 : Fin 4) = 0 ∧ ¬ IsRotation hG4 tau4 := by
  refine ⟨by decide, ?_⟩
  exact not_rotation_S4

/-- **Mutation check: `LabelPreserving` does not imply `AltF = id`.**  This is
`not_ukk_then_not_altF` with the `Ukkonen` hypothesis dropped, i.e. the
*minimal* mutation of the assigned obligation.  It shows the failure is not
caused by the repeat-theoretic side at all: label-preservation alone is
insufficient. -/
theorem not_labelPreserving_altF_id :
    LabelPreserving hG4 3 S4 tau4 → ¬ (∀ q : Fin 4, AltF hG4 tau4 q = q) := by
  intro _ h
  exact altF_S4_ne (h (0 : Fin 4))

/-- **Mutation check: the converse direction of
`vertexCycleEq_of_traverses` is not available for free.**  `S3 = 001` at
`L = 3` with `tau3 = (1 2)` is a pull-back that is *not* a vertex cycle of the
truth (`BBTEulerian.not_vertexCycleEq`), so `traverses` is genuinely
restrictive and `vertexCycleEq_of_traverses` is not a tautology about
`VertexCycleEq`. -/
theorem traverses_is_restrictive : ¬ VertexCycleEq hG3 3 S3 tau3 (Equiv.refl (α := Fin 3)) :=
  not_vertexCycleEq

end AssemblyP1.Issue94TW7AltF
