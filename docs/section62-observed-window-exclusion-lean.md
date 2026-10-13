# An observed internal window forces a spelling-preserving detour

**Status:** Lean-kernel-checked local theorem, not yet the global/circular Observation 7 theorem.

The module `AssemblyP1.Section62SkippedWindowFactor` proves the following under equal read length `L`, a genuine proper suffix-prefix overlap `ell<L`, and a minimum overlap threshold `oMin<=ell`:

If an observed strand `m` occurs as a length-`L` window at offset `0<t<L-ell` strictly inside the word spelled by direct edge `e=(u,v,ell)`, then the two overlaps

```
l1 = L-t
l2 = ell+t
```

are genuine, proper, meet the threshold, and satisfy `l1+l2=L+ell`. Thus `isReducibleSpellingB` returns true for `e`. Consequently, if `e` belongs to `transitivelyReducedSpelling`, **no such observed internal strand can occur**.

Kernel endpoints:

- `internal_window_decomposition` and `internal_window_length`, for the interior window of `spellDirect`;
- `internal_window_first_overlap` and `internal_window_second_overlap`, with explicit suffix/prefix equality;
- `observed_internal_window_reducible`, turning the internal window into an explicit positive Boolean witness for `isReducibleSpellingB`;
- `surviving_edge_skips_no_observed_strand`, showing no internal observed strand can occur on a surviving edge.

All statements use the repository's actual definitions and ordinary list operations. No `sorry`, `admit`, or added axioms are used. The targeted build is required to pass with `--wfail`, with separate CI and source review before merge.

**Important scope:** This proves a local edge property for strands of the implemented *spelling-preserving candidate*. It does **not** establish the cyclic-start partition identity for an arbitrary bidirected SignedPath, a reverse-complement class occurrence-count theorem, or equivalence to the full Myers 2005 transitive reduction. The former two are the next proof goals of Antonina #284; source fidelity stays open under #284/#285. It also does not imply that the broader `transitivelyReducedLonger` predicate preserves the spelled language (counterexample PR #185).
