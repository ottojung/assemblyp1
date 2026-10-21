# §6.2 `spellChain` window multiset and physical visited reads (#284)

**Status:** Lean-kernel-checked module
`AssemblyP1/Section62SpellChainWindowTransport.lean`, added on top of the merged
`Section62SimultaneousReduction`, `Section62VisitTransport`,
`Section62VisitWindowBridge`, and `Section62WindowBoxSharpness`. It is purely
additive: it does not redefine `isReducibleB`, `transitivelyReduced`,
`isReducibleSpellingB`, `transitivelyReducedSpelling`, `SpelledFeasible62`, or
`StepsSurviveReduction`, and it reproves no merged §6.2 theorem.

## What was missing

The merged transport modules state the sliding length-`L` window multiset on the
repository's **toy** walk spelling `spellWalk` of `Section62VisitTransport`, not
on the **actual** §6.2 spelling function `spellChain` of
`Section62SimultaneousReduction`. The two had never been connected. This module
closes that fidelity gap.

## The bridge

For a chain `es` of overlap edges starting at `s`, define

* `chainStrands s es = s :: es.map (·.sy)` — the strands visited by the chain;
* `chainOvs es = es.map (·.len)` — the overlap lengths.

`spellChain_eq_spellWalk`: if every overlap of `es` is no longer than its
arrival read, then

```
spellChain toList s es
  = spellWalk (toList s :: es.map (fun e => toList e.sy)) (es.map (fun e => e.len)).
```

So the §6.2 reduction module's spelling function and the window-transport
module's walk spelling are the same object.

## Window-multiset invariance

`spellChain_windows_congr`: equal spelled words have equal window multisets.
`reduction_preserves_language_windows`: when the chain `es` from `e.sx` spells
exactly the word the direct edge `e` spells (the hypothesis of
`Section62SimultaneousReduction.reduction_preserves_language`), their length-`L`
window multisets agree. This is the detour-replacement invariance on the real
`spellChain`.

## Physical visited reads

`genuineChain_of_overlapEdges`: a chain of edges of the `overlapEdges` graph,
starting at an observed strand, is a `GenuineWalk` of proper overlaps.
`chain_visited_dominated` and `genuineChain_visited_dominated`: for such a chain,
the visited read-word multiset is a **sub-multiset** of the length-`L` window
multiset of `spellChain`:

```
Dominates ((chainStrands s es).map toList) (windows L (spellChain toList s es)).
```

Equivalently, for every read word `u`, the number of chain positions whose read
is `u` is at most the multiplicity of `u` among the length-`L` windows of the
spelled word. This is the explicit relation between the complete window multiset
and the physical class counts. The residual gap is exactly the unobserved seam
windows.

## What this licenses, and what it does not

**Licenses.** A reduction-invariant *upper bound* on the physical visit count of
each read word by its window multiplicity, valid for every genuine chain in the
§6.2 overlap graph. The window multiset is a function of the spelled word, so the
bound survives the spelling-preserving reduction while the visit count itself
does not.

**Does not license.** Exact physical class counts, exact §6.2 vertex throughput,
or an ML-flow/likelihood equivalence. The bound is strict (the unobserved seam
window of `Section62VisitWindowBridge.witness_bound_strict`), and the window box
is not sharpened to the exact physical image by any observed-window designation
(`Section62WindowBoxSharpness`). The molecule-class quotient (`rep`, reverse
complements) additionally needs the separate Observation 7 / RC arguments of
`Section62ObservedMoleculeCount` and `Section62GlobalSkippedBridge`. The exact
ML-likelihood transport to §6.2 feasible flows remains **OPEN**.

## Verification

* `lake build --wfail AssemblyP1.Section62SpellChainWindowTransport` — exit 0.
* `lake env leanchecker AssemblyP1` — whole-library kernel replay.
* Every endpoint prints only `propext`, `Classical.choice`, `Quot.sound`; no
  `sorryAx`.
* `python3 scripts/verify_284_spellchain_window_transport.py` — re-derives the
  bridge and the domination bound on the `L = 5` witness and on a finite sweep of
  short genuine chains, and checks module hygiene and documentation.
