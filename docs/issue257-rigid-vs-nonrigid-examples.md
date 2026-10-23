# Issue #257: rigid vs non-rigid worked examples and candidate certificate status

Owner: agent-uk64aP1scgBtUa15EYSXX5-hardly. Base: origin/main 234f348.
Branch: research/257-rigid-criterion-uk64aP1scgBtUa15EYSXX5.
Verifier: `scripts/verify_257_rigid_examples.py` (exit 0).

## 1. Kernel condition (Theorem 1 restatement)

For support edge-set E with vertex-incidence matrix M and multiplicity vector
A (A >= 1 on E, total G = sum A): A is NON-RIGID iff there exists a nonzero
integral delta with M*delta = 0, sum(delta) = 0, and A + delta >= 1 on E.
RIGID iff no such delta exists.

## 2. Non-rigid example: S = AATATT, L = 2

Circular 2-mer counts: A = {AA:1, AT:2, TA:2, TT:1}, G = 6.
Witness delta = (AA:+1, AT:-1, TA:-1, TT:+1): conservation holds at A
(delta_TA - delta_AT = 0) and at T by symmetry; sum = 0;
B = A + delta = (2,1,1,2) >= 1 with total 6. Hence NON-RIGID.
(The exhaustive search also finds delta = (0,-1,-1,2), B = (1,1,1,3).)

## 3. Rigid repetitive example: S = ATATAT, L = 3

Circular 3-mer counts: A = {ATA:3, TAT:3}, G = 6. Support is the directed
2-cycle AT -> TA -> AT. ker(M) = span((1,1)); sum(delta) = 2t = 0 forces t = 0.
Hence RIGID, although (L-1)-mers AT and TA each occur exactly 3 times.

## 4. Failed simpler hypothesis (explicit counterexample, as required)

H: "rigid IFF no length-(L-1) word occurs >= 3 times" is FALSE as an iff.
Section 3 is the counterexample: rigid with two distinct triples.
Sufficiency direction undisputed.

## 5. Candidate certificate: CONJECTURE (not proved)

(C1) Chord-parametrized box feasibility (exact restatement of Theorem 1, no
new graph structure proved): fix a spanning forest; parametrize delta by chord
values; decide rigidity by box-constrained integer feasibility. Whether a
polynomial min-cut/max-flow closed form exists for arbitrary explicit supports
is OPEN; the direct LP relaxation is already refuted (merged coin/LP no-go).

## 6. Lean lemma for later work (not formalized in this increment)

lemma rigid_iff_no_admissible_delta (M : Matrix V E Z) (A : E -> N)
  (hA : forall e in support, A e >= 1) :
  Rigid M A <-> ~(exists delta : E -> Z, (forall v, sum_e M v e * delta e = 0)
    /\ (sum_e delta e = 0) /\ delta != 0
    /\ (forall e in support, (A e : Z) + delta e >= 1)).

## 7. Validation

244 (S,L) cases over binary circular genomes length 2..6, L in {2,3}:
brute-force positive-circulation uniqueness vs kernel-witness search agree
everywhere (0 mismatches); 154 rigid, of which 62 carry an (L-1)-mer triple.

## 8. Next

Prove or refute (C1)-beyond-restatement structure for a concrete new family
(e.g. formalize the p,q long-bridge criterion), or state a precise no-go for a
bounded gadget class. Keep #257 OPEN; general-support closed form unresolved.
