#!/usr/bin/env python3
"""
Exact-rational analysis of the same-length run-shift family

    S = A^p C^q,   D = A^(p+1) C^(q-1)      (|S| = |D| = p+q)

under the fixed-length exact multinomial objective (Medvedev-Brudno 6.1,
"Variant E" with |D| = G), together with the source bridging hypothesis I_s
(coverage + all-bridged triple repeats + bridged interleaved pairs).

Independent exact-rational re-implementation of the repeat/bridging semantics
of docs/bridging-source-semantics.md.  Reports:

  (A) the slice q = 2, p = L (L = read length), for L = 3..12:
      a verified counterexample with ratio exactly 2^x;
  (B) a complete support search for p,q<=5, L<=5, p+q<=9 showing which
      (p,q,L) admit ANY sample satisfying I_s while using no type absent
      from D and admitting an amplifying observed type;
  (C) the q >= 3 obstruction: the middle copy of the maximal triple repeat
      C^(q-2) can only be bridged by a read containing all q C's, absent
      from D = A^(p+1) C^(q-1).

Usage: python3 verify_exact_run_family.py
"""

from fractions import Fraction
from itertools import combinations
from collections import defaultdict


# ---------------------------------------------------------------- core semantics
def win(seq, t, ell, G):
    return tuple(seq[(t + j) % G] for j in range(ell))


def spectrum(seq, L):
    G = len(seq)
    d = defaultdict(int)
    for i in range(G):
        d[win(seq, i, L, G)] += 1
    return dict(d)


def covered_set(seq, starts, L):
    G = len(seq)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return cov


def reads(seq, starts, L):
    G = len(seq)
    obs = defaultdict(int)
    for r in starts:
        obs[win(seq, r, L, G)] += 1
    return dict(obs)


def maximal_pairs(seq):
    G = len(seq)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[win(seq, i, ell, G)].append(i)
        for w, ts in groups.items():
            for a, b in combinations(ts, 2):
                if seq[(a - 1) % G] != seq[(b - 1) % G] and \
                   seq[(a + ell) % G] != seq[(b + ell) % G]:
                    out.append((ell, (a, b), w))
    return out


def triple_repeats(seq):
    G = len(seq)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[win(seq, i, ell, G)].append(i)
        for w, ts in groups.items():
            for tri in combinations(ts, 3):
                pres = [seq[(t - 1) % G] for t in tri]
                posts = [seq[(t + ell) % G] for t in tri]
                if len(set(pres)) > 1 and len(set(posts)) > 1:
                    out.append((ell, tuple(sorted(tri)), w))
    return out


def interleaved_pairs(seq):
    reps = maximal_pairs(seq)
    out = []
    for i in range(len(reps)):
        for j in range(i + 1, len(reps)):
            e1, p1, _ = reps[i]
            e2, p2, _ = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def read_windows(starts, L, G):
    return [frozenset((r + o) % G for o in range(L)) for r in starts]


def copy_bridged(windows, t, ell, G):
    """A single read must strictly contain the copy on both sides."""
    left, right = (t - 1) % G, (t + ell) % G
    return any(left in w and right in w for w in windows)


def check_I_s_precomputed(G, cov, triples, inter, windows):
    if len(cov) != G:
        return False
    for ell, tri, w in triples:
        for t in tri:
            if not copy_bridged(windows, t, ell, G):
                return False
    for (e1, p1, _), (e2, p2, _) in inter:
        if not (any(copy_bridged(windows, t, e1, G) for t in p1) or
                any(copy_bridged(windows, t, e2, G) for t in p2)):
            return False
    return True


def check_I_s(seq, starts, L):
    G = len(seq)
    cov = covered_set(seq, starts, L)
    return check_I_s_precomputed(G, cov, triple_repeats(seq),
                                 interleaved_pairs(seq), read_windows(starts, L, G))


def ratio(S, D, obs):
    L = len(next(iter(obs)))
    dS, dD = spectrum(S, L), spectrum(D, L)
    r = Fraction(1)
    for w, x in obs.items():
        if dS.get(w, 0) == 0 or dD.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(dD[w], dS[w]) ** x
    return r


# ---------------------------------------------------------------- (A) infinite slice
def slice_counterexamples(lo=3, hi=12, x=3):
    print("(A) exact run-shift slice  S=A^L C^2,  D=A^(L+1) C,  G=L+2")
    print(f"    starts = [0]*x + [1, G-1],  x = {x}")
    ok_all = True
    for L in range(lo, hi + 1):
        S, D = "A" * L + "C" * 2, "A" * (L + 1) + "C"
        G = L + 2
        starts = [0] * x + [1, G - 1]
        obs = reads(S, starts, L)
        good = check_I_s(S, starts, L)
        same = len(S) == len(D)
        r = ratio(S, D, obs)
        cheap = (r == Fraction(2) ** x)
        ok_all = ok_all and good and same and cheap and r > 1
        print(f"    L={L:2d} G={G:2d} |S|=|D|={same}  I_s={good}  "
              f"ratio={r}  ==2^x:{cheap}")
    print(f"    ALL OK: {ok_all}\n")
    return ok_all


# ---------------------------------------------------------------- (B) support search
def has_amplifier(S, D, L):
    dS, dD = spectrum(S, L), spectrum(D, L)
    return any(dS.get(w, 0) > 0 and dD.get(w, 0) > dS[w] for w in dS)


def support_search(P=5, Q=5, M=5, Gmax=9):
    print(f"(B) complete support search p,q<={P}, L<={M}, G<= {Gmax}")
    hits = []
    for p in range(1, P + 1):
        for q in range(1, Q + 1):
            G = p + q
            if G > Gmax:
                continue
            S = "A" * p + "C" * q
            D = "A" * (p + 1) + "C" * (q - 1)
            for L in range(1, M + 1):
                if L > G:
                    continue
                dS, dD = spectrum(S, L), spectrum(D, L)
                missing = {w for w in dS if dD.get(w, 0) == 0}
                amp = has_amplifier(S, D, L)
                triples, inter = triple_repeats(S), interleaved_pairs(S)
                found = None
                for mask in range(1, 1 << G):
                    starts = [i for i in range(G) if mask >> i & 1]
                    if set(reads(S, starts, L)) & missing:
                        continue
                    cov = covered_set(S, starts, L)
                    if len(cov) != G:
                        continue
                    if check_I_s_precomputed(G, cov, triples, inter,
                                             read_windows(starts, L, G)):
                        found = starts
                        break
                if found is not None and amp:
                    hits.append((p, q, L, found))
    for p, q, L, st in hits:
        print(f"    p={p} q={q} L={L}  G={p+q}  starts={st}  S={'A'*p+'C'*q}")
    print(f"    #counterexample-admitting triples: {len(hits)}\n")
    return hits


# ---------------------------------------------------------------- (C) q>=3 obstruction
def q_ge_3_obstruction():
    print("(C) q>=3 obstruction probe")
    print("    Maximal triple repeat C^(q-2) has middle copy at start p+1.")
    print("    Report all read types bridging it and whether D can realize one.")
    for (p, q) in [(2, 3), (3, 3), (3, 4), (4, 5), (5, 3), (3, 5)]:
        G = p + q
        S = "A" * p + "C" * q
        D = "A" * (p + 1) + "C" * (q - 1)
        ell = q - 2
        tri = (p, p + 1, p + 2)
        words = {tuple(S[(t + j) % G] for j in range(ell)) for t in tri}
        assert len(words) == 1, words
        mid = p + 1
        by_len = defaultdict(list)
        for L in range(1, G + 1):
            for s in range(G):
                w = tuple(S[(s + j) % G] for j in range(L))
                pos = {(s + o) % G for o in range(L)}
                if (mid - 1) % G in pos and (mid + ell) % G in pos:
                    by_len[L].append(w)
        realizable = []
        for L, ws in by_len.items():
            dD = spectrum(D, L)
            for w in ws:
                if dD.get(w, 0) > 0:
                    realizable.append((L, w, w.count("C")))
        print(f"    p={p} q={q}: lengths with a middle-copy bridge = "
              f"{sorted(by_len)}")
        if realizable:
            print(f"      D-realizable bridging types: "
                  f"{sorted(set((L, ''.join(w), c) for L, w, c in realizable))}")
        else:
            print(f"      NO bridging type is realizable in D")
    print()


def main():
    a = slice_counterexamples()
    hits = support_search()
    q_ge_3_obstruction()
    print("Summary")
    print("  (A) slice L>=3 verified:", a)
    triples = sorted({(p, q, L) for (p, q, L, _) in hits})
    print("  (B) (p,q,L) with a counterexample:", triples)
    print("      distinct (q,L):", sorted({(q, L) for (_, q, L, _) in hits}))


if __name__ == "__main__":
    main()
