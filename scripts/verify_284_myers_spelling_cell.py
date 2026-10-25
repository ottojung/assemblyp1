"""Spelling-cell advance for issue #284 (Myers scope matrix companion).

Checks one previously unasserted spelling-fidelity cell on the
Section62SpellingReductionCandidate regression instance (VERTS=[0,1,2],
READLEN=3, OMIN=1, STRAND table shared with
verify_284_reduction_survival_matrix.py):

  cell S-ORIENT: the corrected direct-edge detour witness uses an
  intermediate molecule whose strand is an *observed* strand (member of
  strandsOf, hence reverse-complement closed), with genuine suffix-prefix
  overlaps (oMin <= l1,l2 < L) and the same-spelled outer length law
  l1 + l2 = L + e.len, plus forced l1,l2 > e.len.

Exit 0 iff the witness (m=1 strand family, l1=l2=2, direct e.len=1)
satisfies every conjunct. Exits nonzero otherwise.
"""
import sys

STRAND = {
    0: [0, 1, 2],
    1: [1, 2, 3],
    2: [2, 3, 4],
    3: [5, 6, 7],
    4: [4, 5, 6],
    5: [3, 4, 5],
}
VERTS = [0, 1, 2]
READLEN = 3
OMIN = 1


def rc(w: int) -> int:
    return (w + 3) % 6


def strands_of(verts):
    return verts + [rc(v) for v in verts]


def pre(lst, k):
    return lst[:k]


def suf(lst, k):
    return lst[len(lst) - k:] if k <= len(lst) else lst


def main() -> int:
    strands = strands_of(VERTS)
    # Bidirected closure: every observed strand's rc partner is observed.
    for s in list(strands):
        if rc(s) not in strands:
            print(f"FAIL: strand {s} lacks rc partner in strandsOf")
            return 1
    # Direct edge (0 -> 2, overlap 1) detour witness from the survival matrix.
    m, l1, l2, elen = 1, 2, 2, 1
    checks = [
        (m in strands, "intermediate m is an observed strand"),
        (OMIN <= l1 < READLEN, "l1 proper overlap window"),
        (OMIN <= l2 < READLEN, "l2 proper overlap window"),
        (suf(STRAND[0], l1) == pre(STRAND[m], l1), "leg1 suffix-prefix overlap"),
        (suf(STRAND[m], l2) == pre(STRAND[2], l2), "leg2 suffix-prefix overlap"),
        (l1 + l2 == READLEN + elen, "same-spelled outer length law"),
        (elen < l1 and elen < l2, "forced longer detour overlaps"),
    ]
    failed = [label for ok, label in checks if not ok]
    if failed:
        print("FAIL:")
        for label in failed:
            print(f" - {label}")
        return 1
    print("spelling cell S-ORIENT verified: observed rc-closed m=1, "
          "l1=l2=2 proper overlaps, l1+l2=L+e.len, e.len<l1,l2")
    return 0


if __name__ == "__main__":
    sys.exit(main())
