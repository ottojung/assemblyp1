# Ternary length-5 independent verification (#259)

Scope: MB09 §6.1 fixed-external-N product-binomial objective only, NOT the
exact multinomial of #256, NOT the §6.2 bidirected-flow objective of #260–#261.
Alphabet {0,1,2}; oriented 2-mer universe of size 9; circular candidate length
G=5; normalization N=G=5; sample size n=sum_w x(w).

## Census (exact integers, independently re-enumerated)

- Words: 3^5 = 243.
- Realizable spectra: 48.
- Candidates (total-5 vectors over 9 coordinates): C(5+9-1, 9-1) = 1287.
- Covered-sample maximality iff used (checked, not re-proved): truth A weakly
  maximizes against B on every covered complete-support x iff q_B vanishes
  somewhere on supp(A) or q_B(w) <= q_A(w) for all w in supp(A), where
  q_B(w) = B(w) * prod_{v != w} (N - B(v)).
- Violations: full-class 672, realizable-class 78.

## Smallest realizable witness

- A = (0,0,0,0,0,1,0,1,3), B = (0,0,0,0,0,2,0,2,1), both realizable,
  lexicographically smallest violating realizable pair (verified by scan).
- q_A = (0,0,0,0,0,125000,0,125000,750000).
- q_B = (0,0,0,0,0,375000,0,375000,140625).
- Iff fails via strict excess at coordinates 5 and 7.

## Explicit beating sample (exact integers)

- x = A + 3*e_5 = (0,0,0,0,0,4,0,1,3), n = 8, covered complete-support.
- F_A(x) = 12874603271484375000000000000000000000000000.
- F_B(x) = 20622625015676021575927734375000000000000000.
- F_B > F_A exactly; ratio identity
  F_B * prod(q_A^x) == F_A * prod(q_B^x) over supp {5,7,8} holds.
- Minimality along e_5: t = 0, 1, 2 do NOT beat; t = 3 is minimal.
- Mutation control: q with wrongly included self factor gives mutated
  full-class count 2154 != 672, so the control is non-vacuous.

## Relation to prior work

Independent of, and not duplicating, the ternary L=4 verifier (c8d2de2:
81 words, 24 spectra, 495 candidates, full=96/realizable=6). This cell extends
the census to ternary G=5. Quaternary L=2 (16 words, 10 spectra, 136
candidates) and L=3 (64 words, 24 spectra, 816 candidates) were scanned and
found violation-free (0/0); those negative cells are reported here, not as
separate artifacts. Universal rigidity classification, G>=6, alphabets >=4
with L>=4, arbitrary realizable truths, and CI wiring remain open.
#260/#261 flows untouched.

Run: `python3 scripts/verify_ternary_length5_witness_259.py` (exit 0 = ALL OK).
