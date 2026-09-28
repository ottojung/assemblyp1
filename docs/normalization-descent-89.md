# The normalization descent for `#89`: what is verified, and where the
# argument actually stops (#89)

_Status: 2026-09-28.  Source of the route: the root proof audit
(`/tmp/assemblyp1-normalization-proof.txt`), independently re-derived and
mechanically re-checked here.  Nothing in this note is formalized except the
three lemmas of `AssemblyP1/P2RepeatResidual.lean` §8 (`pairBack_add_lt_G`,
`pairBack_add_le_maxPairLen`, `maxPairLen_lt_G`,
`nodeWindow_eq_of_shift_within_pairBack`), which are the depth input the route
consumes.  The exhaustive check below is **evidence, not a proof**: its
completeness is not established.*

## 0. Verdict

The descent is sound and worth formalizing; the **endgame specified in the
route is not valid**, and the argument does not close.

| claim in the route | status |
| --- | --- |
| `AltF (h ∘ σ) = h ∘ AltF σ ∘ (ρ h ρ⁻¹)` | **correct**, and exact (see §1) |
| the move preserves the vertex listing and `EulerianCycle` | **correct** |
| the move toggles exactly `P` and `Q` | **correct** |
| `P`, `Q` disjoint; `β` decrements; `Φ` strictly decreases | **correct** |
| move is available when `β > 0` | **wrong**: the threshold is `β ≥ K = L - 1` (§2) |
| minimality forces `pairBack = 0` on all active chords | **wrong**: only `β < K` (§2) |
| "`P2` excludes crossings among the active chords" | **false** in general (§3) |
| innermost chord ⟹ `f = id` | follows from the previous two, both of which are wrong as stated |

So the residual step is *not* finished.  What the descent does achieve is a
clean normal form (§4) and a sharp statement of what is still missing (§5).

## 1. The conjugation move, with the exact formula

`Succ hG σ x = σ (nextPos hG (σ.symm x))`,
`AltF hG σ q = Succ hG σ (prevPos hG q)`, and `Succ hG σ y = f (nextPos hG y)`.
Hence, for `σ' := h ∘ σ` with `h` an involution,

```text
AltF hG σ' = h ∘ f ∘ nextPos ∘ h ∘ prevPos = h ∘ f ∘ (ρ h ρ⁻¹).        (★)
```

This is the formula in the route note, and it is right.  (Two plausible-looking
alternatives, `h f h⁻¹` and a formula with `ρ⁻¹` at the left, are wrong; the
place to be careful is that `ρ` and `h` do not commute, so `Succ σ' ` cannot be
read as `h (Succ σ) h⁻¹` followed by a rotation.)  Sanity check: `S = AABAB`,
`G = 5`, `L = 3`, `σ = (0 3 2 1 4)`, `f = (1 3)(2 4)`, `h = (1 3)`: (★) gives
`f' = (1 3)(2 4)(1 3)(2 4) = id`, and computing `AltF (h ∘ σ)` gives `id`.

**`h` preserves the labelling, hence preserves the listing and `EulerianCycle`.**
`h` is supported on one `K`-mer fibre `P`, so `vtx (h x) = vtx x` for *every*
`x` (this is the step that makes "the same exact vertex listing" survive the
move).  It also preserves the `L`-mer labels, because the `L`-mer at a start is
determined by the `K`-mer there and the `K`-mer at `ρ` of it, and both are
preserved.  `EulerianCycle` is then preserved clause by clause; the `single`
clause needs the general fact that "being a `G`-cycle" does not depend on the
base point of `VisitsAll` (because `h` need not fix `origin hG`), i.e. a
`visitsAll_iff` lemma, which does not exist in the repository yet.

**The toggle.**  With `P = {p, q}`, `Q = ρ P = {a, b}`, `h = swap p q`,
`r = swap a b`, `ρ h ρ⁻¹ = r`, and `f` commuting with both `h` and `r`
(because `f` preserves fibres of size `≤ 2`, so it permutes each of them and
`S₂` is abelian):

```text
f' = h f r = h (f r),    f r = f with the Q-toggle removed.
```

`f'` therefore toggles exactly `P` and `Q`: the active `Q` disappears and `P`
toggles on.  This is the whole content of "the switch moves one step left", and
it is *not* a conjugation: it is a composition.

**The measure.**  `Φ(σ) = Σ_{x : AltF σ x ≠ x} (pairBack S x (AltF σ x) + 1)`
counts both endpoints of every active chord, so with `β = pairBack a b` and
`β' = β - 1`:

* `P` inactive:  `ΔΦ = -2(β+1) + 2(β'+1) = -2`;
* `P` active:    `ΔΦ = -2(β+1) - 2(β'+1) = -(4β + 2)`.

Both are strictly negative, so minimality of `Φ` among the presentations with a
fixed vertex listing is contradicted whenever a move is available.

**Disjointness of `P` and `Q`.**  `P ∩ Q ≠ ∅` would make the two chords the
same unordered pair, and then `β = β' = β - 1`, impossible.  This is what rules
out the degenerate case, and it needs no primitivity.

## 2. The threshold is `β ≥ K`, not `β > 0`

The move needs `vtx p = vtx q` with `p = prev a`, `q = prev b`.  A `β`-block of
backward agreement at `(a, b)` gives equality of the *predecessor symbol*
(`β ≥ 1`), and equality of the whole `K`-mer at `p, q` only when
`β ≥ K = L - 1` (the block `[a - K, a)` is exactly the `K`-mer at `p`).

Mechanically confirmed: of the 32766 non-trivial presentations in the check
below, the number for which `pairBack > 0` but the predecessor pair is not a
fibre is large (13144 in the first run), and all of them disappear when the
threshold is `β ≥ K`.

So minimality gives `β < K` on every active chord, **not** `β = 0`.  Everything
the route says after "hence all active pairs have `pairBack = 0`" has to be
redone at `β < K`.

Consequence: an active chord with `β < K` is *not* a maximal repeat at its own
starts, so the `P2` interleaved clause does not apply to it, and the clause-2
exclusion of crossings is unavailable.

## 3. "`P2` excludes crossings directly" is false at `β < K`

Exhaustive check (see §6): there are 29666 configurations — on genuine
primitive `P2` words, `G ≤ 8`, read length `L` in range — in which the
descent is stuck (all active chords have `β < K`) and the active chords
**pairwise cross**.  Each of those has exactly two active chords, and they
interleave.  Their maximal extensions do *not* interleave (`ExtCrossing`),
which is consistent with `P2`, so there is no contradiction to extract.  In
other words the P2 clause-2 argument at the raw starts fails, and with it the
"innermost chord" endgame.

The saving observation: in every one of those 29666 stuck configurations the
vertex cycle is nevertheless a rotation of the truth's (0 exceptions), so the
*conclusion* is not in doubt; only the route to it is missing.

## 4. What the descent does give: a sharp normal form

> **Normal form (verified).**  Every Eulerian presentation of the `(L-1)`-mer
> multigraph of a primitive `P2` word can be transformed, by moves that
> preserve the vertex listing, into a presentation all of whose active chords
> satisfy `pairBack < L - 1`.  The transformation is finite, because `Φ`
> strictly decreases and `Φ` is bounded below.

The normal form is small: on the whole check, every stuck normal form has
**exactly two** active chords (29474 cases) or four (192 cases), and the two
chords **cross**.  So the residual content of `#89` is a statement about
*crossing active chords with `β, β' < K`* on a primitive `P2` word — and
nothing else.  That is a much smaller target than the global ladder, and it is
the one worth formalizing.

### The stuck normal forms, in detail

Collected over the same enumeration.  With `β_i` the backward extension of the
`i`-th active chord and `ext_i` its maximal extension
(`maxPairStart`, `maxPairStart`), a two-chord normal form has:

| `β`-pair | count | extensions coalesce | extensions interleave |
| --- | --- | --- | --- |
| `(0, 1)` | 25874 | 21342 of 29474 in total | 0 |
| `(0, 2)` | 1800 | | 0 |
| `(1, 2)` | 1800 | | 0 |
| `(0, 0)` | **0** | | |

The last row is the sharpest fact here: **a minimal configuration never has
`β = β' = 0`.**  In every two-chord normal form exactly one of the two chords
is left-maximal at its own starts (`β = 0`, hence a maximal repeat of length
`≥ K > L - 2` there), and the other has `β' ∈ {1, 2}`.  The extensions never
interleave (as clause 2 of `P2` forces) and sometimes but not always coalesce.

Consequences for the endgame:

* the "`P2` excludes crossings" argument needs **both** constituents to be
  maximal repeats at their own starts, which minimality never provides, so
  clause 2 cannot be applied to a crossing pair of a minimal configuration;
* but a minimal configuration always contains a chord which *is* a maximal
  repeat at its own starts.  A descent that could move such a chord (i.e. a
  move keyed on the `L`-mer agreement of the pair rather than on the `K`-mer
  agreement of its predecessor pair — §5.2) would do it.  The 192 four-chord
  normal forms, whose `β`-pattern is `(0, 0, 1, 1)`, show that two such
  `β = 0` chords can coexist; they are then genuinely maximal repeats, so
  clause 2 *is* available for any two of them that cross.
* the minimal example is the repository's own `S = AABAB`, `G = 5`, `L = 3`
  with chords `(1, 3)` (`β = 0`) and `(2, 4)` (`β = 1`) — the pair that
  `P2RepeatResidual.cex_not_NodeCrossing` already exhibits.  Its two maximal
  extensions coalesce (both are the pair `(1, 3)`), so this instance is
  *not* a counterexample to `P2`, and it is exactly the configuration the
  residual lemma has to say something about.

## 5. What is still missing (the one lemma)

For the argument to close, one of the following must be proved.

1. **Rematch (the residual lemma).**  Two crossing active chords `(a, b)`,
   `(c, d)` with `β_ab, β_cd < K` on a primitive `P2` word force the vertex
   cycle of the presentation to be a rotation of the truth's.  In the
   crossing-chords language this is the "interleaved" disjunct of the `#89`
   dichotomy, i.e. the item `docs/arratia-shift-left-invariant-89.md` §3 calls
   the shift-left lemma *without* the effect/nontriviality apparatus: the
   normalization measure above supplies a candidate substitute for
   "nontriviality", namely "the presentation is not the `Φ`-minimiser".
2. Or: a *stronger* descent, whose measure allows a move also for `β < K`
   (e.g. by using the `L`-mer agreement of the pair rather than the `K`-mer
   agreement of its predecessor), and which therefore forces `β = 0` after all.

Nothing in this note is a proof of either.

## 6. The check that produced §2–§4

Exhaustive, all circular words over alphabets of size `≤ 3` with `3 ≤ G ≤ 8`,
all `2 ≤ L ≤ G`, filtered to `S` **primitive and satisfying the repository's
actual `P2` (both clauses)**, and all `G!` presentations of `Fin G` as
candidate Eulerian presentations (the two clauses of `EulerianCycle` computed
from the definitions).  For each non-trivial presentation, the descent was
iterated and every intermediate invariant was *re-verified at every step*:

| check | violations |
| --- | --- |
| `P` and `Q` disjoint | 0 |
| `pairBack p q = pairBack a b - 1` | 0 |
| `h ∘ σ` still an Eulerian presentation | 0 |
| vertex listing of `h ∘ σ` = that of `σ` | 0 |
| `AltF (h ∘ σ) = f ∘ swap P ∘ swap Q` (the toggle) | 0 |
| `Φ` strictly decreases | 0 |
| descent ends with `f = id` | 3100 of 32766 |
| descent stuck, all active `β < L - 1` | 29666, **all with crossing chords** |
| descent stuck, chords non-crossing | 0 |
| stuck, but vertex cycle is not a rotation of the truth's | 0 |
| a second `E` with the same `L`-spectrum that is not a rotation of `S` | 0 |
| minimal configuration with `β = β' = 0` (two chords) | 0 |

The last row is the sanity check on the *target theorem itself* (it is the only
row that says the thing we actually want); it is satisfied on this range.  A
finite search is evidence: completeness is not proved, and the table is not a
proof of any of its rows.

One caution recorded for the record: the first two runs of this check used a
`P2` predicate that implemented only clause 1, and a `traverses` test that
compared `σ (ρ i)` with `σ (ρ (σ i))` instead of `ρ (σ i)`.  Both bugs
manufactured apparent counterexamples to the target theorem (`S = AABABB`,
`E = AABBAB` at `G = 6`, `L = 3`); `AABABB` in fact **fails** clause 2 of `P2`
(it has the interleaved maximal repeats `(1, 3)` and `(2, 5)` of length `2 >
L - 2`).  Any re-check of these numbers must reproduce the predicate from
`AssemblyP1.P2` rather than from a script.

## 7. The endpoint, if and when the residual lemma lands

`BBTEulerian.bbt_of_P2_obstruction` reduces the issue-`#89` target to a single
statement about Eulerian presentations:

```text
vertexCycleEq_of_primitive_P2 :
  hG, 2 ≤ L ≤ G, IsPrimitive S, P2 hG L S, EulerianCycle hG L S σ
  → VertexCycleEq hG L S σ (Equiv.refl)
```

after which `exists_matching`, `pullback_isEulerianCycle` and
`rotEquiv_of_vertexCycleEq` give `RotEquiv hG E S` from
`specCount hG S = specCount hG E`.  Note that **no hypothesis about `E` is
needed**: the whole argument is on the truth side, so the issue-`#89` target
only ever needs `S` primitive and `P2`, and the target statement can drop
`IsPrimitive E` and `P2 hG L E`.  The check of §6 gives no violation of
`VertexCycleEq` for Eulerian presentations, so this endpoint is not itself
refuted; but it is the endpoint that the residual lemma of §5 must feed.
