# Issue #94 — the backward-extension step, and the common-back-step obstruction

Branch `board/94-replacement`, front **B94-BADNESS**.  Companion to
`docs/rematching-invariant-94.md` (§5, the `ρ` language) and
`docs/two-transposition-criterion-94.md` (front `94a03`: the cycle criterion is
crossing, `TwoTranspositionsBlock` is false).

## What was missing

`AssemblyP1.BBTMaximalExtension` carries the backward-extension vocabulary
(`BackAgrees`, `backAgreeSet`, `max_back_agrees`, `preceding_ne_of_max_back`)
and names its own two gaps:

* §3a: *"The index arithmetic that combines a backward step of size `p` with a
  forward agreement of length `e₀` yields an agreement of length `e₀ + p` at the
  extended pair; this is what is needed to compose §3a with §2."*
* the fact that the alternation clause `Interleaved` survives a common rotation
  of the four starts, which every such composition needs and which nothing in
  the repository states.

Both are now in `AssemblyP1/BBTReplacementInvariant.lean` §7.

## The statements (all kernel-checked)

| name | content |
| --- | --- |
| `agrees_back` | `BackAgrees p a b → Agrees e₀ a b → Agrees (e₀ + p) (prevPos^[p] a) (prevPos^[p] b)` — **the missing index arithmetic** |
| `agrees_back_step` | the one-step form: `BackAgrees 1` + `Agrees e₀` → `Agrees (e₀+1)` one place back |
| `BackAgrees_shift` | `BackAgrees (p + q) a b → BackAgrees p (prevPos^[q] a) (prevPos^[q] b)` |
| `interleaved_iter` | `Interleaved S a b c d → Interleaved S (prevPos^[q] a) … (prevPos^[q] d)` — **rotation invariance of the alternation clause** |
| `distVal`, `distVal_step1`, `distVal_iter` | the clockwise distance between two starts, and its invariance under a backward step |
| `preceding_ne_of_maxBack` | `BackAgrees p a b ∧ ¬ BackAgrees (p+1) a b → Preceding (prevPos^[p] a) ≠ Preceding (prevPos^[p] b)` |
| **`commonBackStep_obstruction`** | **two interleaved pairs carrying the same `(L-1)`-mers, agreeing backwards for the same number of places and stopping there, are two interleaved maximal repeats of length `≥ L-1`: a `LongObstruction`** |
| `crux_no_commonBackStep`, `crux_commonBackStep_obstruction` | at the crux configuration of §5.3 the two constituents' maximal backward agreements stop at **different** places |

`agrees_back` is the sharp form: the agreement window that `BackAgrees p`
supplies starts at `prevPos^[p] a`, which is exactly what
`preceding_ne_of_maxBack` needs for maximality.  The weaker form
(`BackAgrees (q+1) → Agrees (e₀ + q)` at shift `q`) is off by one against
`preceding_ne_of_maxBack` and would *not* compose with it; `BBTMaximalExtension`
does not state either form.

## Why this is not a proof of the obligation

`InterleavingObstructionNeeded` (§5.4) is still open.  What is new is a
**necessary condition on its configuration**: if the two interleaved
constituents agree backwards for the same number of places and stop together,
there is already a `LongObstruction`, so the configuration can only survive
when the two backward steps differ, or when one of them runs the whole way
round the circle (`p = G`, the periodic case, in which the pair supports no
maximal repeat at all and the obstruction theorem does not apply).

Bounded census (`scratch/backstep_census.py`, all binary circular words,
`G ≤ 8`, `2 ≤ L ≤ G+1`): 816 crux geometries sit on `P2` genomes; **0** of them
have equal *finite* backward steps — consistent with the theorem, and a
counterexample to it if one ever appears — and 528 have `p = G` for both pairs
(e.g. `10001000` at `L = 7`), the periodic residue.  288 have unequal steps,
e.g. `(0, 1)` on `00101` at `L = 3`, `(0, 2)`, `(1, 2)`.

## What remains

The residue is mathematical, not a toolkit gap.  See
`/workspace/BOARD94-BADNESS-0153.md` §5 for the two remaining cases and the
cheapest next step.