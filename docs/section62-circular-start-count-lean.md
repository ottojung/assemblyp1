# Circular-start interval and occurrence-count identities in Lean

**Status:** Scoped general combinatorial theorems kernel-checked by Lean. These are the start-position accounting half of AssemblyP1's Observation 7 proof, not yet the full signed circular-walk theorem. Tracked under Antonina #284.

For a finite list of positive extension lengths d_0,...,d_(m-1), define consecutive anchor positions by s_0=0 and s_(j+1)=s_j+d_j, with total spelled length G=sum_j d_j.

The module AssemblyP1/Section62CircularStarts.lean defines covered, anchors, and interiors from those lengths and proves:

- covered_eq_interval: consecutive blocks [s_j,s_j+d_j) concatenate to exactly [s_0,s_0+G).
- interval_head_and_internal: each positive block is its anchor plus internal offsets.
- covered_zero_eq_all_starts: with s_0=0, those blocks contain exactly genomic starts 0,...,G-1.
- covered_weight_sum: an arbitrary nonnegative-valued function of starts sums over all starts as anchor contribution plus internal contribution.
- covered_class_count: for any class-valued function f on genomic starts and class c, the number of occurrences of c over all starts equals the number on anchor starts plus the number on internal skipped starts.
- covered_count_eq_anchors_iff_no_internal: total occurrences of c equal anchor visits exactly when none of the skipped internal starts has class c.

These statements are mathematical, not biological: f can later be instantiated with the length-L circular genomic window (or its RC molecule class). The positivity of each extension d_j is essential: otherwise a zero-length traversal could contribute an anchor but no genomic start.

In PR #186, Section62SkippedWindowFactor proves that a surviving edge of the implemented spelling-preserving reduction cannot have an OBSERVED read strand at any skipped internal position. Combining those two modules requires a separate formal circular spelling adapter ensuring: the j-th anchor is the read visited by the j-th edge, each extension agrees with the spelled genome, the circular seam is valid, and RC-strand classes aggregate correctly. Equivalence to the full Myers or MB09 algorithm remains separately open.

Verification target: lake --quiet --wfail build AssemblyP1.Section62CircularStarts, followed by the exact-head project-wide CI and axiom audit. No sorry, admit, axioms or classical assumptions added by this module.
