# The Kotzig/Ukkonen/Pevzner directed-Euler transposition descent, re-expressed in this repository's language — and why its central step does not exist here

Front 94tr. Branch `research/94-transposition-induction`. Module
`AssemblyP1/Issue94Transposition.lean`.

## 1. Verdict

**The classical "one transposition reducing `|W|` by 2" step is unavailable in
this repository's language, and the reason is a sign obstruction — not a tactic
failure and not a defect of the classical theorem.**

Two results, both kernel-checked:

1. **The 2-in/2-out pairing is real, and stronger than "even".**  On the genuine
   slice the transition-difference set `W` always has `|W| ≡ 0 (mod 4)`.
2. **The classical base case `|W| = 2` does not exist, and no two reachable
   `AltF`s differ by one transposition factor.**  So the descent cannot run.

The descent step that *is* compatible with this language deletes a **pair** of
factors (`|W|` by `4`).  That is recorded as an unproved `Prop`,
`Issue94Transposition.PairDeletionDescent`; its `t = 2` base case is the
`TwoTranspositionsBlock` shape already refuted at `docs/board94-*` §7
(`not_TwoTranspositionsBlock`), and **is not re-attacked here**, per this front's
scope.

## 2. The classical argument and the object-by-object translation

Kotzig's transposition induction for directed Eulerian circuits: for two circuits
`θ₁ ≠ θ₂` let `W` be the transitions on which they differ; pick `w ∈ W` with
shortest return arc; some `w' ∈ W` lies strictly inside that arc; they interlace;
the transposition at `w, w'` gives a third circuit differing from `θ₁` only on
`W \ {w, w'}`; induct on `|W|`.

| classical | this repository |
|---|---|
| Eulerian circuit of the directed `(L-1)`-mer multigraph | `Succ hG σ`, `σ : Fin G ≃ Fin G` |
| the truth circuit | `nextPos hG` |
| difference set `W` | `Support (AltF hG σ) = {q : AltF hG σ q ≠ q}` (`BBTLadder.Support`) |
| `W` splits into pairs | `BBTLadder.AltF_sq`, so `\|W\| = 2t` |
| 2-in/2-out at a doubled `(L-1)`-mer | `BBTLadder.AltF_support_swap`, `BBTLadder.DoubledPair` |
| shortest return arc | `BBTChords.InArc`, `InterleavedStarts` |
| the transposition | deleting one transposition factor `(a b)` of `AltF` |
| result still one circuit | **false** |

The two translation identities that do the work:

* `succ_eq_altF_nextPos` — `Succ hG σ = AltF hG σ ∘ nextPos hG`
  (this is `BBTUniqueEulerian.AltF_succ`, restated).
* `succ_eq_conj_nextPos` — `Succ hG σ = σ ∘ nextPos ∘ σ⁻¹`.

`Succ` is therefore a **conjugate** of `nextPos`, hence has the same sign.  And
since `Succ` is one cycle for *every* listing (`Issue94TW5Single.succ_visitsAll`;
this is why `EulerianCycle` reduces to `traverses`), "is `f` still one circuit"
in this language means precisely

> `f ∘ nextPos` is a `G`-cycle,

which by `succ_eq_altF_nextPos` says `f` is the `AltF` of some listing.  That is
the right notion of the classical "still a valid circuit" clause.

## 3. The obstruction (kernel-checked)

From `sign Succ = sign nextPos` and `Succ = f ∘ nextPos`:

```
    sign nextPos = sign f * sign nextPos    =>    sign f = +1
```

So every reachable `f = AltF hG σ` is an **even** permutation.  If `f` is an
involution with `t` transposition factors (the `AltF_sq` content) then
`sign f = (-1)^t`, so `t` is even and

```
    |W| = 2t ≡ 0  (mod 4).
```

Deleting one factor gives `|W'| = |W| - 2 ≡ 2 (mod 4)`, which by the same argument
cannot be the support of a reachable `AltF`.  Hence the classical step.

| declaration | size | content |
|---|---|---|
| `succ_eq_altF_nextPos` | general | `Succ = AltF ∘ nextPos` |
| `succ_eq_conj_nextPos` | general | `Succ = σ ∘ nextPos ∘ σ⁻¹` |
| `involution_support_mod_four_5` | `G = 5` | `AltF` involutive ⟹ `\|W\| % 4 = 0` |
| `involution_support_mod_four_6` | `G = 6` | same |
| `involution_support_two_impossible_5` | `G = 5` | `\|W\| ≠ 2` |
| `altF_even_5` | `G = 5` | `sign (AltF hG5 σ) = 1` for every listing |
| `no_single_factor_step_5` | `G = 5` | **no two reachable `AltF`s differ by one factor** |
| `no_single_factor_step_6` | `G = 6` | same |
| `PairDeletionDescent` | — | `Prop`, **not proved** |

All axiom sets are `[propext, Classical.choice, Quot.sound]` (two are weaker).
No `sorry`, no `admit`, no `axiom`, no `native_decide`; `decide` is used only on
closed `Fin 5` / `Fin 6` statements quantified over **all** listings, so those
checks are *complete* for those sizes rather than samples.

`G = 5` is not arbitrary: it is the size of the refuted `00101` crossing of
`docs/board94-*` §3.

## 4. Why this is a fact about the translation, not about the classical theorem

The classical `W` is a set of **arcs of the multigraph**, and both circuits are
valid, so deleting one arc from the difference set leaves a valid circuit.

Here `Support (AltF hG σ)` counts **positions**.  Each differing transition is
counted **twice** — once per endpoint of its transposition — so the repo's `|W|`
is twice the natural count, `|W| / 2` counts each differing transition once, and
the reaching map `σ ↦ AltF hG σ` lands entirely in the even-sign half.  The
classical induction measures the number of differing arcs; in this language the
corresponding measure has `4`-divisibility built in.  Any induction that tries to
step by `2` on `|W|` will fall through that floor.

## 5. A caveat that corrected this front mid-course

The first draft asserted `|W| % 4 = 0` over **all** listings.  `decide`
refuted it, correctly: over all 120 listings of `Fin 5` the support sizes are

```
    |W| = 0 :  5 listings
    |W| = 3 : 50 listings
    |W| = 4 : 25 listings
    |W| = 5 : 40 listings
```

and `3` and `5` differ by `2`.  The `3` and `5` cases are precisely those where
`AltF` is **not** an involution.  So `AltF_sq`'s hypotheses — `EulerianCycle`
**and** `P2` **and** primitivity — are load-bearing, and the statements here carry
them explicitly.  Recorded in the module docstring, §4, so the next front does not
re-derive it.

A second, smaller trap: the obstruction statement needs a `≥ 2` guard, because
`ℕ` subtraction is truncated and `0 - 2 = 0`, which collapses the claim to
`σ' = σ`.  Both are noted in the source.

## 6. Bounded computational evidence

`scratch94/kotzig_census.py`, exhaustive over all binary words, `G ≤ 8`,
`2 ≤ L ≤ 4`, all `G!` listings per truth: 364 primitive `P2` truths, 4264
admitted traversals.

* on the genuine slice (`EulerianCycle` + `P2` + primitive),
  `|W| ∈ {0, 4}` exactly; no `|W| = 2`; no odd `t = |W| / 2`; **0 exceptions**
  to `|W| ≡ 0 (mod 4)`;
* all 1832 of the `|W| = 4` traversals are **good** (`VertexCycleEq`) — i.e. in
  this range the only nonzero difference sets already spell the truth's own
  vertex cycle.  This is consistent with `θ₅ = nextPos ∘ ρ₅` being good at
  `docs/board94-*` §3, and it means the search found **no** counterexample to
  uniqueness in range;
* 3664 single-factor deletion attempts, **0** leaving a `G`-cycle — the
  obstruction, computed independently of the Lean check;
* at `t = 2`, the two chords interleave in 4910 / 4910 cases.

This is finite evidence.  §3 does not rest on it.

## 7. Dependency on the rest of the tree

Imports: `AssemblyP1.BBTLadder`, `AssemblyP1.Issue94TW5Single`.

Upstream declarations actually used:

* `BBTLadder.AltF`, `Support`, `mem_Support`, `AltF_sq`, `AltF_support_swap`,
  `DoubledPair` (`AssemblyP1/BBTLadder.lean`);
* `BBTEulerian.EulerianCycle`, `VisitsAll`, `origin`;
  `BBTUniqueEulerian.Succ`, `AltF_succ`, `Succ_eq_altF`, `AltF_bijective`;
* `Issue94TW5Single.succ_visitsAll`, `eulerianCycle_iff_traverses`;
* `BBTChords.nextPos`, `rotAdd`, `hG5`;
* for `AltF_sq`: `P2Multiplicity.P2.imp_nodeCount_le_two_of_powerPrimitive`,
  `P2Multiplicity.IsPrimitive.shiftPrimitive`,
  `RepeatAdapter.primitive_nodeCount_le_two`, `P2.noLongTripleRepeat`.

`BBTEulerian.EulerianCycleObstruction` (i.e. `thm:BBT`) still has no inhabitant;
this front neither supplies nor assumes one.  `lake build --wfail` is green
(exit 0, "Build completed successfully (8996 jobs)") and the aggregator's
distinct axiom sets are unchanged at `[propext]`, `[propext, Quot.sound]`,
`[Quot.sound]`, `[propext, Classical.choice, Quot.sound]`.

## 8. What the next front should do

1. **Do not step by `2` on `|W|`.**  It falls through the `mod 4` floor.  Use
   `t = |W| / 2` (the number of doubled `(L-1)`-mers, which
   `BBTLadder.AltF_support_swap` already identifies) and step by `2` there.
2. **The interesting content is `t = 2`, not `|W| = 2`.**  At `t = 2` the two
   chords interleave (kernel-checked and 4910/4910 in search), and that is the
   already-refuted `TwoTranspositionsBlock` configuration.  Attacking it again
   buys nothing; the gap remains badness.
3. **The genuinely open part is unchanged and is not this front's:** a *bad*
   traversal on a `P2` genome.  This front shows the classical descent cannot
   produce one, and the finite search found none either.
