# #94: the reduction of the candidate replacement invariant, proved in Lean

Date: 2026-10-03. Branch `board/94-replacement`, on top of `16347a7`.
Front: bounded front B94-INV-2600 (`/workspace/BOARD94-INVARIANT-2600.md`).

## 1. What is proved

`AssemblyP1/BBTReplacementInvariant.lean` gains a section `Reduction` with
five kernel-checked results (all depending only on `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`):

1. `interleaved_maximal_pair` — two interleaved doubled `(L-1)`-mers whose
   **preceding** symbols both differ extend to two interleaved maximal repeats
   of length `≥ L-1`, i.e. to the second disjunct of `LongObstruction`.  This is
   `BBTMaximalExtension.maximalRepeat_of_branch` applied twice; no `θ`, no
   selection, no `P2`.
2. `selectedInterleaved_crux` — hence a selected interleaving on a genome with
   `¬ LongObstruction` has a **preceding-blocked** constituent: one of the two
   pairs of selected starts carries the same preceding symbol, so the maximal
   extension is unavailable there.
3. `four_distinct_card` — a small finiteness helper (four distinct elements
   force `4 ≤ card`).
4. `selectedInterleaved_coincides_selectedTriple` — if the two constituents of
   a selected interleaving are the **same** condensed vertex, all four starts
   lie in one fibre of multiplicity `≥ 4 ≥ 3`, rematched, so `SelectedTriple`
   holds.
5. `selectedInterleaved_crux_or_triple` — the consolidated form: under
   `¬ LongObstruction`, a selected interleaving is either degenerate into
   `SelectedTriple`, or it has two **distinct** interleaved fibres with one
   constituent preceding-blocked.

## 2. Why the raw statement is false, and what the true statement is

The raw form `SelectedInterleaved θ ⟹ LongObstruction`
(`BBTSupport.SelectedInterleaved_obstruction`) is **refuted, kernel-checked**,
at `BBTSupport.selectedInterleaved_obstruction_false_00101`: `θ = nextPos` on
`S = 00101`, `L = 3`, where `SelectedInterleaved` holds and `LongObstruction`
fails (`00101` is `P2`, hence `Ukkonen`).  Front `BOARD94-BOUNDED-ELAB-2315`
additionally reports the raw version failing in 768 of 1024 generated
instances; that count is computational evidence, completeness not proved.

Results 1–5 show what the selection buys: the extension step is available
**unless** a constituent is blocked at the preceding symbol, and the blocking is
*located*.  So the `(I)` clause of `SupportDichotomy` is load-bearing in exactly
one configuration.

## 3. The remaining obligation

`AssemblyP1.BBTReplacement.BadSelectedInterleavingRemaining` (a `Prop`, not
proved): a `P2` genome with a bijective, fibre-preserving, one-cycle **bad**
`θ`, `¬ SelectedTriple θ`, `SelectedInterleaved θ`, `¬ LongObstruction`.  By
result 5 this is exactly the configuration of two **distinct** interleaved
selected fibres with one preceding-blocked.  Closing it — forcing a
`LongObstruction`, necessarily through the first disjunct (a maximal triple
repeat of length `≥ L-1`) — is the residual content of the `#89` endgame.  This
front did not prove it.

## 4. Files

* `AssemblyP1/BBTReplacementInvariant.lean` — section `Reduction`.
* `scratch/InvCrux.lean`, `scratch/InvAxioms.lean` — the working file and the
  `#print axioms` run (`lake env lean`, exit 0).