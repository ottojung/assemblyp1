#!/usr/bin/env python3
"""Independent audit of the AAATT truth/read instances against the exact
Shomorony 2016 / Bresler 2013 information-feasible bridging condition I_s.

Written from the PRIMARY SOURCE text, not from any repository helper.  The
Bresler-Bresler-Tse 2013 prose (PMC3706340, retrieved 2026-09-20) is quoted in
the audit note docs/source-notes/aaatt-bridging-source-audit-2026-09-20.md.

Verifies, with plain characters and exact integer logic, that

  * the integrated Lean instance        truth = AAATT, L = 3, starts (0, 1, 4)
  * the non-spellable flow-search variant truth = AAATT, L = 3, starts (0, 0, 1, 4)

both satisfy I_s = coverage AND every maximal triple repeat all-bridged AND
every interleaved maximal-repeat pair bridged, under Bresler's maximality and
Figure-5 strict-bridging definitions on a circular genome.

Exits non-zero on any failed assertion.

Run: python3 scripts/audit_aaatt_bridging_source.py
"""

from itertools import combinations


def sym(s, i):
    return s[i % len(s)]


def win(s, t, ell):
    return "".join(sym(s, t + j) for j in range(ell))


# --------------------------------------------------------------------------
# Source repeat definitions (Bresler et al. 2013, verbatim in the note)
# --------------------------------------------------------------------------

def maximal_repeat_pairs(s):
    """All (ell, {t1,t2}) satisfying the source maximal repeat definition."""
    g = len(s)
    out = []
    for ell in range(1, g):
        byword = {}
        for t in range(g):
            byword.setdefault(win(s, t, ell), []).append(t)
        for w, ts in byword.items():
            for t1, t2 in combinations(sorted(ts), 2):
                if sym(s, t1 - 1) != sym(s, t2 - 1) and \
                   sym(s, t1 + ell) != sym(s, t2 + ell):
                    out.append((ell, frozenset((t1, t2)), w))
    return out


def maximal_triple_repeats(s):
    """All (ell, {t1,t2,t3}) satisfying the source maximal triple repeat def."""
    g = len(s)
    out = []
    for ell in range(1, g):
        byword = {}
        for t in range(g):
            byword.setdefault(win(s, t, ell), []).append(t)
        for w, ts in byword.items():
            for tri in combinations(sorted(ts), 3):
                pre = {sym(s, t - 1) for t in tri}
                post = {sym(s, t + ell) for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    out.append((ell, frozenset(tri), w))
    return out


# --------------------------------------------------------------------------
# Source bridging: read [r, r+L) strictly contains copy [t, t+ell) plus one
# base on each side.  On an integer lift this is  r < t and t+ell < r+L,
# i.e. Bresler's "the read arrives in the preceding length L-ell-1 interval".
# --------------------------------------------------------------------------

def copy_bridged(s, starts, L, t, ell):
    g = len(s)
    for r in starts:
        for m in range(-3, 4):
            T = t + m * g
            if r < T and T + ell < r + L:
                return True
    return False


# --------------------------------------------------------------------------
# Interleaving: origin-independent cyclic alternation, equivalent to
# Bresler's t1 < t2 < t3 < t4 or t2 < t1 < t4 < t3 for some cut.
# --------------------------------------------------------------------------

def interleaved(a, b, c, d):
    pts = [a, b, c, d]
    if len(set(pts)) < 4:
        return False
    for start in range(4):
        order = pts[start:] + pts[:start]
        labels = [0 if x in (a, b) else 1 for x in order]
        if labels[0] == labels[2] and labels[1] == labels[3] and \
           labels[0] != labels[1]:
            return True
    return False


def check_I_s(s, starts, L, verbose=True):
    g = len(s)
    covered = {(r + j) % g for r in starts for j in range(L)}
    coverage = covered == set(range(g))

    triples = maximal_triple_repeats(s)
    triple_fail = [(ell, t, w) for ell, ts, w in triples
                   for t in sorted(ts) if not copy_bridged(s, starts, L, t, ell)]

    pairs = maximal_repeat_pairs(s)
    inter_seen, inter_fail = [], []
    for i in range(len(pairs)):
        for j in range(i + 1, len(pairs)):
            e1, p1, _ = pairs[i]
            e2, p2, _ = pairs[j]
            p1s, p2s = sorted(p1), sorted(p2)
            if len(set(p1s + p2s)) < 4:
                continue
            a, b = p1s
            c, d = p2s
            if not interleaved(a, b, c, d):
                continue
            bridged = (any(copy_bridged(s, starts, L, t, e1) for t in (a, b))
                       or any(copy_bridged(s, starts, L, t, e2) for t in (c, d)))
            inter_seen.append((e1, p1s, e2, p2s, bridged))
            if not bridged:
                inter_fail.append((e1, p1s, e2, p2s))

    ok = coverage and not triple_fail and not inter_fail
    if verbose:
        print(f"  S={s} L={L} starts={starts}")
        print(f"    coverage               = {coverage}")
        print(f"    maximal repeat pairs   = {[(e, sorted(p), w) for e, p, w in pairs]}")
        print(f"    maximal triple repeats = {[(e, sorted(t), w) for e, t, w in triples]}")
        print(f"    triple-bridge failures = {triple_fail}")
        print(f"    interleaved pairs      = {inter_seen}")
        print(f"    interleave failures    = {inter_fail}")
        print(f"    I_s                    = {ok}")
    return ok


def main():
    print("Independent audit: exact Shomorony/Bresler I_s")
    print("=" * 52)

    instances = [
        ("integrated Lean instance            AAATT, starts (0,1,4)",
         "AAATT", [0, 1, 4], 3),
        ("non-spellable flow-search variant    AAATT, starts (0,0,1,4)",
         "AAATT", [0, 0, 1, 4], 3),
    ]
    for name, s, starts, L in instances:
        print(f"\n[{name}]")
        assert check_I_s(s, starts, L), name

    print("\nPer-copy bridging witnesses for the unique triple repeat A@{0,1,2}:")
    s = "AAATT"
    for t in (0, 1, 2):
        w = [r for r in (0, 1, 4) if copy_bridged(s, [r], 3, t, 1)]
        print(f"    copy t={t} bridged by read start(s) {w}")
        assert w, t

    print("\nCircularity: copy t=0 is bridged by the origin-crossing read start 4")
    print("  (lift: read [4,7) strictly contains copy [5,6)).")

    print("\nReverse complement (Shomorony theory is single-strand; revcomp is a")
    print("read-TYPE relabelling, not a change of genomic placement):")
    def rc(w):
        return "".join("T" if c == "A" else "A" for c in reversed(w))
    for r in (0, 1, 4):
        w = win(s, r, 3)
        print(f"    start {r}: window={w} rc={rc(w)} molecule-class={min(w, rc(w))}")
    assert check_I_s(s, [0, 1, 4], 3, verbose=False)
    print("    -> placement certificate unchanged by revcomp relabelling.")

    print("\nProse cross-check of the longest length-2 maximal repeat:")
    len2 = [(sorted(p), w) for e, p, w in maximal_repeat_pairs(s) if e == 2]
    print(f"    actual maximal length-2 repeat pairs = {len2}")
    assert len2 == [([0, 1], "AA")], len2
    assert not any(sorted([3, 4]) == p for p, w in len2)

    print("\nAll independent assertions passed.")


if __name__ == "__main__":
    main()
