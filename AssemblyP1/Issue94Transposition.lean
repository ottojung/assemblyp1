import AssemblyP1.BBTLadder
import AssemblyP1.Issue94TW5Single

/-!
# The Kotzig/Ukkonen/Pevzner transposition descent in this repository's
# language, and a kernel-checked obstruction to it (front 94tr)

This file re-expresses the classical directed-Euler transposition induction in
the finite cyclic listing/transition language of `AssemblyP1/BBTEulerian.lean`
and `AssemblyP1/BBTLadder.lean`, and then establishes that **the classical step,
in this language, cannot decrease `|W|` by `2` while remaining an Eulerian
listing.**

## §0. The classical argument, and where each piece lands here

Kotzig's transposition induction for directed Eulerian circuits: given two
circuits `θ₁ ≠ θ₂`, let `W` be the set of transitions on which they differ.  Pick
`w ∈ W` whose return arc is shortest; some `w' ∈ W` lies strictly inside that
arc; the two interlace; the transposition at `w` and `w'` gives a third circuit
differing from `θ₁` only on `W \ {w, w'}`, so `|W|` drops by `2`.  Induct.

Translated object by object:

| classical | this repository |
|---|---|
| Eulerian circuit of the directed `(L-1)`-mer multigraph | `Succ hG σ` for a listing `σ : Fin G ≃ Fin G` |
| the truth circuit | `nextPos hG` |
| difference set `W` of transitions | `Support (AltF hG σ) = {q : AltF hG σ q ≠ q}` (`BBTLadder.Support`) |
| `W` splits into pairs | `BBTLadder.AltF_sq` (an involution under `P2` + primitivity), so `|W| = 2t` |
| "2-in / 2-out at a doubled `(L-1)`-mer" | `BBTLadder.AltF_support_swap`, `BBTLadder.DoubledPair` |
| the transposition | deleting one transposition factor `(a b)` of `AltF` |
| the result is still a circuit | **false; `no_single_factor_step_*`** |

## §1. `Succ = AltF ∘ nextPos`, and what "one cycle" means here

`BBTUniqueEulerian.AltF_succ` gives pointwise

```
Succ hG σ = AltF hG σ ∘ nextPos hG                                (★)
```

`Succ hG σ q = σ (nextPos hG (σ.symm q))` is the conjugate `σ ∘ nextPos ∘ σ⁻¹`,
so it is a `G`-cycle for **every** listing: that is
`Issue94TW5Single.succ_visitsAll`, and it is why
`Issue94TW5Single.eulerianCycle_iff_traverses` reduces `EulerianCycle` to its
first conjunct `traverses`.  So in this repository "is it still one circuit" is
not a statement about `f` but about

```
    f ∘ nextPos                                                            (★★)
```

being a `G`-cycle, and (★) says (★★) is exactly `Succ hG σ` for some listing.

(★★) is a real constraint, not a restatement of `single`: `Succ` is a `G`-cycle
for every `σ`, but `f` ranges over more functions than the `AltF` of some
listing, and (★★) is what cuts it down.

## §2. The parity obstruction

`Succ = σ ∘ nextPos ∘ σ⁻¹` is a conjugate of `nextPos`, and the sign
homomorphism kills conjugates, so `sign Succ = sign nextPos`.  Together with (★):

```
    sign Succ = sign f * sign nextPos = sign nextPos   =>   sign f = +1
```

So every reachable `f = AltF hG σ` is an **even** permutation.  If `f` is an
involution with `t` transposition factors then `sign f = (-1)^t`, so `t` is even
and

```
    |W| = 2t ≡ 0   (mod 4)                                        (⋆)
```

The 2-in/2-out pairing is therefore not merely "even": `|W|` is a **multiple of
four**, and the classical base case `|W| = 2` cannot occur at all.

## §3. The obstruction: the classical step does not exist here

Deleting one transposition factor `(a b)` of an involution `f` gives
`f' = f ∘ swap a b` with `|supp f'| = |supp f| - 2`.  By (⋆) for `f` and `f'`,
`|supp f'| ≡ 2 (mod 4)`, so `f' ∘ nextPos` is **not** a `G`-cycle, and by (★) and
(★★) no listing has `AltF hG σ = f'`.

This is **not** a claim that the classical theorem is false, and not a tactic
failure.  It is a statement about the translation.  The classical `W` is a set of
**arcs of the multigraph** and *both* circuits are valid, so removing one arc
from the difference set leaves a valid circuit.  Here
`Support (AltF hG σ)` counts **positions**, and `t = |W| / 2` counts each
differing transition **twice** — once per endpoint of its transposition.  The
reaching map `σ ↦ AltF hG σ` lands in the even-sign half and so misses every
odd-support object, and every single-factor deletion lands there.

The descent step compatible with this language therefore deletes a **pair** of
factors (`|W|` by `4`, `t` by `2`), not one.  That statement is recorded as the
unproved `Prop` `PairDeletionDescent`.  Its `t = 2` base case is the
`TwoTranspositionsBlock` shape already refuted at `docs/board94-*` §7
(`not_TwoTranspositionsBlock`), and it is **not** re-attacked here.

## §4. The 2-in / 2-out pairing hypotheses: verified, with two additions

The front asked first whether primitive `P2` plus the existing `fibre ≤ 2` and
branch lemmas really give the 2-in/2-out pairing.  They do, upstream and
kernel-checked; this file records the dependency and adds what was missing:

* `BBTLadder.AltF_sq` (`BBTLadder.lean:237`): under `P2` + primitivity +
  `2 ≤ L ≤ G`, `AltF` is an involution.  This is "every differing transition comes
  in pairs".
* `BBTLadder.AltF_support_swap` (`BBTLadder.lean:312`): each support point pairs
  with a support point of the same `(L-1)`-mer, and the pair is a `DoubledPair`.
  This is "2-in / 2-out at a doubled `(L-1)`-mer".
* **new here:** `|W| ≡ 0 (mod 4)` (§2), i.e. the pairing is a *multiple of four*
  and the classical `|W| = 2` base case does not exist.

Neither §2 nor §3 mentions a word, a spectrum, `P2` or primitivity: they are
statements about `Fin G` and `nextPos`.  `P2` enters solely through `AltF_sq`,
which supplies the involution.

**A caveat found while auditing (important, and it corrected an earlier draft of
this file).**  `AltF_sq` needs `EulerianCycle` **and** `P2` **and** primitivity.
Over *all* listings `σ : Fin 5 ≃ Fin 5` the statement "`|Support (AltF hG5 σ)|` is
a multiple of 4" is **false**: the distribution over all 120 listings is
`{|W| = 0} : 5, {|W| = 3} : 50, {|W| = 4} : 25, {|W| = 5} : 40`, and `|W| = 3, 5`
occur precisely where `AltF` is *not* an involution.  So the hypotheses are
load-bearing and are stated explicitly in §5 rather than hidden.

## §5. Scope, evidence, dependencies

**Kernel-checked in this file** (no `sorry`, no `admit`, no `axiom`, no
`native_decide`; `decide` only on closed `Fin 5` / `Fin 6` statements over all
listings, so these are *complete* for those sizes):

| declaration | content |
|---|---|
| `succ_eq_altF_nextPos` | `Succ hG σ = AltF hG σ ∘ nextPos hG` (from `AltF_succ`) |
| `succ_eq_conj_nextPos` | `Succ hG σ = σ ∘ nextPos ∘ σ⁻¹`, the sign step of §2 |
| `involution_support_mod_four_5` | for `f = AltF hG5 σ` with `f² = id`: `\|Support f\| % 4 = 0` |
| `involution_support_mod_four_6` | the same at `G = 6` |
| `involution_support_two_impossible_5` | `f² = id` forces `\|Support f\| ≠ 2` |
| `no_single_factor_step_5` | **the obstruction**: no two listings at `G = 5` have `AltF`s of equal support size differing by one factor |
| `no_single_factor_step_6` | the same at `G = 6` |
| `altF_even_5` | `sign (AltF hG5 σ) = 1` for every listing: the sign form of §2 |
| `PairDeletionDescent` | the corrected descent measure: a `Prop`, **not proved** |

`G = 5` is not an arbitrary size: it is the size at which the refuted `00101`
crossing of `docs/board94-*` §3 lives.

**Bounded computational evidence** (`scratch94/kotzig_census.py`: exhaustive over
all binary words, `G ≤ 8`, `2 ≤ L ≤ 4`, all `G!` listings per truth — 364
primitive `P2` truths, 4264 admitted traversals):

* on the genuine slice (`EulerianCycle` + `P2` + primitive) `|W| ∈ {0, 4}`
  exactly; no `|W| = 2`; no odd `t = |W| / 2`; 0 exceptions to (⋆);
* all 1832 of the `|W| = 4` traversals are **good** (`VertexCycleEq`), i.e. the
  only nonzero difference sets in range are already the truth's own vertex
  cycle — consistent with `θ₅ = nextPos ∘ ρ₅` being good in `docs/board94-*` §3;
* 3664 single-factor deletion attempts, **0** leaving a `G`-cycle; and
* at `t = 2`, the two chords interleave in 4910 / 4910 cases.

This is finite evidence, not a proof.  §2 and §3 do not rest on it.

**Dependencies.** Imports: `AssemblyP1.BBTLadder`, `AssemblyP1.Issue94TW5Single`.
The upstream chain used:

* `BBTLadder.AltF`, `BBTLadder.Support`, `BBTLadder.mem_Support`,
  `BBTLadder.AltF_sq`, `BBTLadder.AltF_support_swap`, `BBTLadder.DoubledPair`
  (`AssemblyP1/BBTLadder.lean`);
* `BBTEulerian.EulerianCycle`, `BBTEulerian.VisitsAll`, `BBTEulerian.origin`,
  `BBTUniqueEulerian.Succ`, `BBTUniqueEulerian.AltF_succ`,
  `BBTUniqueEulerian.Succ_eq_altF`, `BBTUniqueEulerian.AltF_bijective`;
* `Issue94TW5Single.succ_visitsAll`,
  `Issue94TW5Single.eulerianCycle_iff_traverses`;
* `BBTChords.nextPos`, `BBTChords.rotAdd`, `BBTChords.hG5`;
* for `AltF_sq`: `P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive`,
  `P2Multiplicity.IsPrimitive.shiftPrimitive`,
  `RepeatAdapter.primitive_nodeCount_le_two`, `P2.noLongTripleRepeat`.

Nothing outside this file is modified.  `BBTEulerian.EulerianCycleObstruction`
(i.e. `thm:BBT`) has no inhabitant and this file neither supplies nor assumes
one.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AssemblyP1.Issue94Transposition

open Finset
open AssemblyP1.BBTLadder
open AssemblyP1.BBTUniqueEulerian
open AssemblyP1.BBTEulerian
open AssemblyP1.BBTChords

/-! ## §1. The translation identities -/

section Basic

variable {G : ℕ}

/-- **`Succ hG σ = AltF hG σ ∘ nextPos hG`**, pointwise: `AltF_succ` in the
direction the descent needs.  With `succ_eq_conj_nextPos` this identifies
"one `G`-cycle" for a candidate `f` with "`f ∘ nextPos` is a `G`-cycle". -/
theorem succ_eq_altF_nextPos {hG : 0 < G} (σ : Fin G ≃ Fin G) (q : Fin G) :
    Succ hG σ q = AltF hG σ (nextPos hG q) :=
  (AltF_succ hG σ q).symm

/-- **`Succ hG σ = σ ∘ nextPos ∘ σ⁻¹`.**  The definition of `Succ`
(`BBTUniqueEulerian.lean:656`); this is the step that makes §2's sign computation
go, since the successor is a conjugate of the one-step rotation and so carries
the same sign. -/
theorem succ_eq_conj_nextPos {hG : 0 < G} (σ : Fin G ≃ Fin G) (q : Fin G) :
    Succ hG σ q = σ (nextPos hG (σ.symm q)) := rfl

end Basic

/-! ## §2–§3. Kernel checks

All of these are `decide`d over **all** listings at the stated size, so they are
complete for that size, not samples.  The `hinv` hypothesis is the `AltF_sq`
content, i.e. the genuine slice; see the caveat in the module docstring, §4. -/

section Kernel

variable {G : ℕ}

/-- `AltF hG σ` as a permutation of the starts, from
`BBTUniqueEulerian.AltF_bijective`. -/
noncomputable def altF_perm {hG : 0 < G} (σ : Fin G ≃ Fin G) : Equiv.Perm (Fin G) :=
  Equiv.ofBijective (AltF hG σ) (AltF_bijective hG σ)

/-- **§2: an `AltF` that is an involution has support a multiple of four.**
`Support (AltF hG5 σ)` is the transition-difference set `W` of §0. -/
theorem involution_support_mod_four_5 :
    ∀ σ : Fin 5 ≃ Fin 5, (∀ x : Fin 5, AltF hG5 σ (AltF hG5 σ x) = x) →
      (Support (AltF hG5 σ)).card % 4 = 0 := by decide

/-- **§2 at `G = 6`.** -/
theorem involution_support_mod_four_6 :
    ∀ σ : Fin 6 ≃ Fin 6, (∀ x : Fin 6, AltF (hG := by decide) σ (AltF (hG := by decide) σ x) = x) →
      (Support (AltF (hG := by decide) σ)).card % 4 = 0 := by decide

/-- **§3, consequence: the classical base case `|W| = 2` does not exist.**  In
the classical argument the induction terminates at `|W| = 2`, where the single
transposition *is* the alternative circuit.  Here it cannot be reached. -/
theorem involution_support_two_impossible_5 :
    ∀ σ : Fin 5 ≃ Fin 5, (∀ x : Fin 5, AltF hG5 σ (AltF hG5 σ x) = x) →
      (Support (AltF hG5 σ)).card ≠ 2 := by decide

/-- **§2 in sign form:** every `AltF` of a listing is an *even* permutation.
This is the content §3 actually consumes: an involution with even sign has an
even number of transposition factors, so `|W| = 2t` with `t` even. -/
theorem altF_even_5 :
    ∀ σ : Fin 5 ≃ Fin 5, Equiv.Perm.sign (altF_perm (hG := hG5) σ) = 1 := by decide

/-- **The obstruction of §3, at `G = 5`.**  No two listings at `G = 5` have
`AltF`s whose support sizes differ by `2`: **the classical one-transposition step
is unavailable in this language.**

Over the 30 listings of `Fin 5` whose `AltF` is an involution the support sizes
are exactly `{|W| = 0} : 5` and `{|W| = 4} : 25`, so no two differ by `2`.  (Over
*all* 120 listings the sizes are `{|W| = 0} : 5, {|W| = 3} : 50, {|W| = 4} : 25,
{|W| = 5} : 40`, and `3` and `5` *do* differ by `2` — which is why the `hinv`
hypotheses are load-bearing and stated explicitly, and why the caveat in §4 of
the module docstring matters.)

The `≥ 2` guard on the second disjunct is not decoration: `ℕ` subtraction is
truncated, so without it `0 - 2 = 0` and the statement collapses to `σ' = σ`. -/
theorem no_single_factor_step_5 :
    ∀ σ σ' : Fin 5 ≃ Fin 5,
      (∀ x : Fin 5, AltF hG5 σ (AltF hG5 σ x) = x) →
      (∀ x : Fin 5, AltF hG5 σ' (AltF hG5 σ' x) = x) →
      ¬ ((Support (AltF hG5 σ')).card = (Support (AltF hG5 σ)).card + 2 ∨
         (Support (AltF hG5 σ)).card ≥ 2 ∧
           (Support (AltF hG5 σ)).card = (Support (AltF hG5 σ')).card + 2) := by
  decide

/-- **The obstruction of §3, at `G = 6`.** -/
theorem no_single_factor_step_6 :
    ∀ σ σ' : Fin 6 ≃ Fin 6,
      (∀ x : Fin 6, AltF (hG := by decide) σ (AltF (hG := by decide) σ x) = x) →
      (∀ x : Fin 6, AltF (hG := by decide) σ' (AltF (hG := by decide) σ' x) = x) →
      ¬ ((Support (AltF (hG := by decide) σ')).card =
            (Support (AltF (hG := by decide) σ)).card + 2 ∨
         (Support (AltF (hG := by decide) σ)).card ≥ 2 ∧
           (Support (AltF (hG := by decide) σ)).card =
             (Support (AltF (hG := by decide) σ')).card + 2) := by
  decide

end Kernel

/-! ## §4. The corrected descent measure, stated but NOT proved -/

/-- **The descent step compatible with this language.**  Deleting a *pair* of
transposition factors of `AltF` lowers `t = |W| / 2` by `2` and `|W|` by `4`,
preserving the `mod 4` divisibility of (⋆).

This is a `Prop`, deliberately **not proved**.  `AGENTS.md` requires a conjecture
to be a `Prop` until actually proved, and the bounded search in
`scratch94/kotzig_census.py` is evidence only.  The `t = 2` base case of the
resulting induction is the `TwoTranspositionsBlock` shape already refuted at
`docs/board94-*` §7, so proving this `Prop` would gain nothing over attacking
that shape directly; see `docs/transposition-descent-94.md`. -/
def PairDeletionDescent : Prop :=
  ∀ (σ σ' : Fin 5 ≃ Fin 5) (a b : Fin 5) (_hab : a ≠ b),
    (AltF hG5 σ a = b ∧ AltF hG5 σ b = a) →
    (Support (AltF hG5 σ')).card = (Support (AltF hG5 σ)).card - 4

end AssemblyP1.Issue94Transposition
