# Fixed-`x` admissibility necessity for exact ML (#255 umbrella, axis A)

_Status: scoped Lean increment, 2026-10-23. Child of #255; does not duplicate
#256/#257/#259/#260/#261._

## Scoped claim

Under the oriented same-length exact multinomial objective
(`OrientedSameLengthML.exactLik`, product over all read types), truth-support
admissibility of the fixed sample `x` is **necessary** for truth maximality:

* **General lemma** (`FiniteMLAdmissibility255.exactLik_eq_zero_of_inadmissible`):
  if `x w > 0` for a read type `w` with `specCount S w = 0`, then
  `exactLik S x = 0`.
* **Witness theorem** (`truth_not_maximal_at_xStar`): for truth
  `S255L3 = AAABBB` at `L = 3`, the single-read sample on `wStar = 010`
  (absent from the truth's six windows `000,001,011,111,110,100`) gives the
  truth likelihood `0` while competitor `SComp = A C A A A A`-pattern
  `![0,1,0,0,0,0]` (spelling `010` once) attains `1/6 > 0`. Hence the truth
  is not an exact-ML maximizer at this fixed `x`.

## Frozen axes

Oriented molecule types; exact multinomial (not fixed-`N` binomial);
same length (`G = 6` both genomes); spelled genomes; truth candidacy kept
(both genomes length `6`); literal read-string types at `L = 3`.

## Relation to `FixedXExactML`

That module's classification iff is stated under the admissibility
hypothesis `hx : support x ⊆ support S`. This increment states the
complementary necessity: without `hx`, the truth is already knocked out
whenever any positively-weighted candidate exists. It proves no
sample-uniform (axis-B) claim; all broader conjectures stay OPEN.

## Evidence

* Kernel: `AssemblyP1/FiniteMLAdmissibility255.lean`
  (`exactLik_eq_zero_of_inadmissible`, `truth_not_maximal_at_xStar`;
  `#print axioms` recorded in-file).
* Computation cross-check: `python3 -c` enumeration of the length-3 circular
  windows of both genomes (truth `010`-count `0`, competitor count `1`).
