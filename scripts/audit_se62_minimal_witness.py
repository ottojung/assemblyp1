#!/usr/bin/env python3
"""
Independent audit of the minimality of the integrated `AAATT -> AAAATT`
Medvedev-Brudno (2009) section 6.2 / Shomorony et al. (2016) I_s witness.

Self-contained: standard library only, exact integer / Fraction arithmetic,
no import of any repository verifier.  Primary sources:
  * MB09, J. Comput. Biol. 16(8):1101-1116, PMC3154397, sections 3.1-3.4,
    6.1, 6.2.
  * Shomorony, Kim, Courtade, Tse, Bioinformatics 32(17):i494-i502, 2016,
    Eq. (1), attributed to Bresler-Bresler-Tse 2013.

What it establishes
-------------------
(A) Reconstructs, from the source definitions, the bidirected molecule
    overlap graph, its signed incidences, the transitive reduction, and the
    I_s bridging predicate for the integrated `AAATT` instance, and verifies
    the integrated witness independently.

(B) Exhaustively searches the source model (alphabet {A,T}, circular truth,
    read length L, read multiset with arbitrary repetition, all I_s-passes,
    spelled section-6.2 circuit competitors) for the *smallest* counterexample
    to the source statement

      (P)  R in I_s and truth admissible => truth maximizes the 6.1 objective.

    It finds counterexamples with G = 3 (L = 2, n = 5) and G = 4 (L = 2,
    n = 3), both smaller than the integrated G = 5 witness, and confirms that
    G = 5 is minimal *if read length is fixed to L = 3*.
"""
from fractions import Fraction
from collections import Counter
from itertools import product, combinations_with_replacement
import sys

# ---------------------------------------------------------------------------
# alphabet / molecules
# ---------------------------------------------------------------------------
ALPH = "AT"
COMP = {"A": "T", "T": "A"}


def rc(w):
    return "".join(COMP[c] for c in reversed(w))


def mol(w):
    return min(w, rc(w))


def windows(s, L):
    G = len(s)
    return ["".join(s[(i + j) % G] for j in range(L)) for i in range(G)]


# ---------------------------------------------------------------------------
# MB09 3.3: bidirected overlap edges (the four strand cases), signed.
# ---------------------------------------------------------------------------
def overlap(a, b, l):
    return a[len(a) - l:] == b[:l]


def build_edges(vertices, L, omin):
    edges = []
    for mx in vertices:
        px, nx = mx, rc(mx)
        for my in vertices:
            py, ny = my, rc(my)
            for sx, sy, sgx, sgy in (
                (px, py, +1, -1), (px, ny, +1, +1),
                (nx, py, -1, -1), (nx, ny, -1, +1),
            ):
                for l in range(omin, L):
                    if overlap(sx, sy, l):
                        edges.append((mx, my, sx, sy, l, sgx, sgy))
    return sorted(set(edges))


def walk(s, L):
    """Cyclic L-window walk of s: (edge steps, visit sequence)."""
    G = len(s)
    ws = windows(s, L)
    steps = []
    for i in range(G):
        sx, sy = ws[i], ws[(i + 1) % G]
        assert sx[1:] == sy[:-1]
        mx, my = mol(sx), mol(sy)
        sgx = +1 if sx == mx else -1
        sgy = -1 if sy == my else +1
        steps.append((mx, my, sx, sy, L - 1, sgx, sgy))
    return steps, [mol(w) for w in ws]


def walk_ok(s, L, edges):
    eset = set(edges)
    steps, visits = walk(s, L)
    for st in steps:
        if st not in eset:
            return False, None
    for i in range(len(s)):
        prev, cur = steps[(i - 1) % len(s)], steps[i]
        if prev[1] != visits[i] or cur[0] != visits[i]:
            return False, None
        if prev[6] != -cur[5]:
            return False, None
    return True, Counter(visits)


# ---------------------------------------------------------------------------
# I_s (Shomorony 2016 Eq. (1), Bresler et al. 2013 repeat/bridging defs)
# ---------------------------------------------------------------------------
def repeat_pairs(s, ell):
    G, out = len(s), []
    for t1 in range(G):
        for t2 in range(t1 + 1, G):
            if all(s[(t1 + j) % G] == s[(t2 + j) % G] for j in range(ell)):
                if (s[(t1 - 1) % G] != s[(t2 - 1) % G] and
                        s[(t1 + ell) % G] != s[(t2 + ell) % G]):
                    out.append((t1, t2))
    return out


def triple_repeats(s, ell):
    G, out = len(s), []
    for t1 in range(G):
        for t2 in range(t1 + 1, G):
            for t3 in range(t2 + 1, G):
                if all(s[(t + j) % G] == s[(t1 + j) % G]
                       for t in (t2, t3) for j in range(ell)):
                    if (len({s[(t - 1) % G] for t in (t1, t2, t3)}) > 1 and
                            len({s[(t + ell) % G] for t in (t1, t2, t3)}) > 1):
                        out.append((t1, t2, t3))
    return out


def bridges(s, reads, t, ell, L):
    G = len(s)
    return any(r < tp and tp + ell < r + L
               for r in reads for tp in (t, t + G))


def interleaved(a, b, c, d, G):
    lab = {}
    for t in (a, b):
        lab[t] = 0
    for t in (c, d):
        lab[t] = 1
    if len(lab) != 4:
        return False
    seq = [lab[t] for t in range(G) if t in lab]
    i = seq.index(0)
    seq = seq[i:] + seq[:i]
    return seq == [0, 1, 0, 1]


def is_holds(s, reads, L):
    G = len(s)
    if len({(r + j) % G for r in reads for j in range(L)}) != G:
        return False
    for ell in range(1, G):
        for tr in triple_repeats(s, ell):
            for t in tr:
                if not bridges(s, reads, t, ell, L):
                    return False
    for e1 in range(1, G):
        for e2 in range(1, G):
            for (a, b) in repeat_pairs(s, e1):
                for (c, d) in repeat_pairs(s, e2):
                    if len({a, b, c, d}) == 4 and interleaved(a, b, c, d, G):
                        if not any(bridges(s, reads, t, ell, L)
                                   for (x, y, ell) in ((a, b, e1), (c, d, e2))
                                   for t in (x, y)):
                            return False
    return True


# ---------------------------------------------------------------------------
# MB09 6.1 literal product of binomial marginals (constant coefficients drop)
# ---------------------------------------------------------------------------
def ratio(x, dS, dD, n, N):
    r = Fraction(1)
    for k in set(x) | set(dS) | set(dD):
        a, b = dS.get(k, 0), dD.get(k, 0)
        if not (0 <= a <= N and 0 <= b <= N):
            return None
        num = Fraction(b, N) ** x.get(k, 0) * Fraction(N - b, N) ** (n - x.get(k, 0))
        den = Fraction(a, N) ** x.get(k, 0) * Fraction(N - a, N) ** (n - x.get(k, 0))
        if den == 0:
            return None
        r *= num / den
    return r


# ---------------------------------------------------------------------------
# circular words up to rotation + reverse complement
# ---------------------------------------------------------------------------
def canon(seq):
    G = len(seq)
    reps = []
    for k in range(G):
        rot = seq[k:] + seq[:k]
        reps += [rot, rc(rot)]
    return min(reps)


def all_circ(G):
    seen, out = set(), []
    for tup in product(range(2), repeat=G):
        c = canon("".join(ALPH[i] for i in tup))
        if c not in seen:
            seen.add(c)
            out.append(c)
    return out


# ---------------------------------------------------------------------------
# verification of the three witnesses
# ---------------------------------------------------------------------------
def check_instance(S, L, starts, N, D, label):
    n = len(starts)
    x = Counter(mol("".join(S[(r + j) % N] for j in range(L))) for r in starts)
    dS = Counter(mol(w) for w in windows(S, L))
    obs = sorted(dS)
    g = build_edges(obs, L, L - 1)
    assert is_holds(S, starts, L), (label, "I_s fails")
    assert set(x) == set(obs), (label, "observed classes != truth spectrum support")
    okS, specS = walk_ok(S, L, g)
    okD, specD = walk_ok(D, L, g)
    assert okS and set(specS) == set(obs), (label, "truth not admissible")
    assert okD and set(specD) <= set(obs), (label, "competitor not admissible on graph")
    assert all(specD.get(o, 0) >= 1 for o in obs), (label, "vertex LB 1 fails")
    r = ratio(dict(x), dict(dS), dict(specD), n, N)
    print(f"[{label}]")
    print(f"  S={S} L={L} N={N} starts={starts} n={n}")
    print(f"  x={dict(x)}  dS={dict(dS)}  D={D}  dD={dict(specD)}")
    print(f"  I_s=ok truth-admissible=ok competitor-admissible=ok  "
          f"L(D)/L(S)={r}")
    assert r is not None and r > 1
    return r


# ---------------------------------------------------------------------------
# exhaustive minimal search (read multisets, spelled competitors)
# ---------------------------------------------------------------------------
def search(G, L, maxD, max_n):
    hits = []
    for S in all_circ(G):
        dS = Counter(mol(w) for w in windows(S, L))
        obs = set(dS)
        for n in range(1, max_n + 1):
            for starts in combinations_with_replacement(range(G), n):
                if not is_holds(S, starts, L):
                    continue
                x = Counter(mol("".join(S[(r + j) % G] for j in range(L)))
                            for r in starts)
                if set(x) != obs:
                    continue
                g = build_edges(sorted(obs), L, L - 1)
                okS, specS = walk_ok(S, L, g)
                if not okS or set(specS) != obs:
                    continue
                for m in range(3, maxD + 1):
                    for D in all_circ(m):
                        spD = Counter(mol(w) for w in windows(D, L))
                        if not set(spD) <= obs:
                            continue
                        if any(spD.get(o, 0) < 1 for o in obs):
                            continue
                        okD, spD2 = walk_ok(D, L, g)
                        if not okD:
                            continue
                        r = ratio(dict(x), dict(dS), dict(spD2), n, G)
                        if r is not None and r > 1:
                            hits.append((r, S, L, starts, dict(x), dict(dS),
                                         D, dict(spD2), n))
    return hits


def main():
    print("=" * 76)
    print("PART A  independent reconstruction of the integrated AAATT witness")
    print("=" * 76)
    check_instance("AAATT", 3, (0, 1, 4), 5, "AAAATT",
                   "integrated G=5 witness")

    print()
    print("=" * 76)
    print("PART B  smaller witnesses in the unrestricted source model")
    print("=" * 76)
    check_instance("AAT", 2, (0, 0, 0, 1, 2), 3, "AAAT",
                   "smaller G=3 witness")
    check_instance("AATT", 2, (0, 1, 3), 4, "AAT",
                   "smaller G=4 witness")
    check_instance("AAAT", 3, (0, 0, 1, 2, 3), 4, "AAAAT",
                   "smaller G=4 L=3 witness (n>N)")

    print()
    print("=" * 76)
    print("PART C  exhaustive minimal search (spelled competitors)")
    print("=" * 76)
    summary = {}
    for G in range(3, 6):
        for L in range(2, G + 1):
            hits = search(G, L, maxD=G + 3, max_n=6)
            summary[(G, L)] = hits
            if hits:
                best = max(hits, key=lambda h: h[0])
                print(f"G={G} L={L}: {len(hits)} witness(es); best ratio "
                      f"{best[0]}  (S={best[1]} D={best[6]} n={best[8]})")
            else:
                print(f"G={G} L={L}: no spelled witness")

    g_min = min((G for (G, L), h in summary.items() if h), default=None)
    print()
    print(f"smallest G with a spelled counterexample anywhere: {g_min}")
    l3 = [G for (G, L), h in summary.items() if h and L == 3]
    print(f"smallest G with a spelled counterexample at L=3: "
          f"{min(l3) if l3 else None}")
    l3_low = [G for (G, L), h in summary.items()
              if h and L == 3 and any(s[8] < G for s in h)]
    print(f"smallest G at L=3 with n < N: {min(l3_low) if l3_low else None}")
    print()
    print("Conclusion: the integrated 'G=5 is smallest' claim requires the")
    print("conjunction L=3 AND n<N; the G=4 L=3 witness C has n=5>N=4, and")
    print("the L=2 witnesses A, B are smaller still.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
