#!/usr/bin/env python3
"""
Independent audit: why the strict oriented single-strand Section 6.2
support-feasibility searches return zero, and what lies beyond their scope.

Self-contained; imports no repository search.  Exact `fractions.Fraction`.
Deterministic.  Exits non-zero on any failed assertion.

  (R)  Same-length rigidity scan.  For a scope (G, L, sigma) enumerate all
       sigma^G circular words, group them by the *support* of their length-L
       window spectrum, and count supports carrying more than one spectrum
       (non-rigid).  A word admits a same-length same-support different-spectrum
       counterpart exactly when its support is non-rigid.  Then count the
       non-rigid words that are also I_s-realizable (no Bresler triple repeat of
       length >= L-1, and every interleaved pair bridged).  The rigidity theorem
       predicts both counts are zero; the scan is a sanity check, not the proof.

  (D)  Beyond the same-length scope.  A strict oriented single-strand Section
       6.2 variable-length counterexample with support equality and I_s:
           truth S = AAATT, competitor D = AAAATT, L = 3,
           observed x = d_S + one extra AAA read (support = supp(d_S)).
       The same-length theorem does not cover it, and it beats the truth under
       both the exact multinomial and the literal fixed-N Section 6.1 product.
       It violates the per-occurrence strengthening d_D >= x, which is not the
       source Section 6.2 lower bound (that bound is per read vertex and 1).
"""
import sys, time
from collections import defaultdict, Counter
from fractions import Fraction
from itertools import product as iproduct, combinations


# ------------------------------------------------------------------ basics ---

def windows(S, L):
    G = len(S)
    return [tuple(S[(i + j) % G] for j in range(L)) for i in range(G)]


def spectrum(S, L):
    d = defaultdict(int)
    for w in windows(S, L):
        d[w] += 1
    return dict(d)


def max_occ(S, ell):
    G = len(S)
    if ell <= 0:
        return len(S)
    c = defaultdict(int)
    for i in range(G):
        c[tuple(S[(i + j) % G] for j in range(ell))] += 1
    return max(c.values(), default=0)


# -------------------------------------------------------------- I_s repeats --

def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            if len(pos) < 2:
                continue
            for p in combinations(pos, 2):
                t1, t2 = p
                if S[(t1 - 1) % G] != S[(t2 - 1) % G] and \
                   S[(t1 + ell) % G] != S[(t2 + ell) % G]:
                    if p not in seen:
                        seen.add(p)
                        out.append((ell, p))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in groups.values():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(list(p1) + list(p2)))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            for p in p2:
                lab[p] = 1
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def Is_realizable(S, L):
    """Shomorony I_s admits some read realization: coverage can be arranged and
    bridging is monotone, so it suffices that no triple repeat has length > L-2
    and every interleaved pair has a constituent repeat of length <= L-2."""
    if any(ell > L - 2 for ell, _ in triple_repeats(S)):
        return False
    for (e1, _), (e2, _) in interleaved_pairs(S):
        if min(e1, e2) > L - 2:
            return False
    return True


# ------------------------------------------------------------- scope scan ----

def scan_scope(G, L, sigma):
    groups = defaultdict(set)
    for S in iproduct(range(sigma), repeat=G):
        sp = spectrum(S, L)
        groups[frozenset(sp.keys())].add(tuple(sorted(sp.items())))
    nonrigid = {k for k, v in groups.items() if len(v) > 1}

    nonrigid_words = 0
    nonrigid_Lm1_le2 = 0
    nonrigid_Is = 0
    examples = []
    for S in iproduct(range(sigma), repeat=G):
        if frozenset(spectrum(S, L).keys()) not in nonrigid:
            continue
        nonrigid_words += 1
        S = tuple(S)
        m = max_occ(S, L - 1)
        if m <= 2:
            nonrigid_Lm1_le2 += 1
            if len(examples) < 5:
                examples.append(("Lm1<=2", "".join(map(str, S)), m))
        if Is_realizable(S, L):
            nonrigid_Is += 1
            if len(examples) < 5:
                examples.append(("Is", "".join(map(str, S)), m))
    return dict(nonrigid_supports=len(nonrigid), nonrigid_words=nonrigid_words,
                nonrigid_Lm1_le2=nonrigid_Lm1_le2, nonrigid_Is=nonrigid_Is,
                examples=examples)


def run_scopes(scopes):
    total_Is = total_Lm1 = 0
    for G, L, sigma in scopes:
        t = time.time()
        st = scan_scope(G, L, sigma)
        total_Is += st["nonrigid_Is"]
        total_Lm1 += st["nonrigid_Lm1_le2"]
        print(f"  G={G:>2} L={L} sigma={sigma}: nonrigid_supports={st['nonrigid_supports']:>5}"
              f" nonrigid_Is={st['nonrigid_Is']} nonrigid_Lm1<=2={st['nonrigid_Lm1_le2']}"
              f"  ({time.time()-t:.1f}s) {st['examples'] if st['examples'] else ''}")
    return total_Is, total_Lm1


# --------------------------------------------------- variable-length §6.2 ----

def exact_ratio_general(S, D, L, x):
    spS, spD = spectrum(S, L), spectrum(D, L)
    NS, ND = len(S), len(D)
    r = Fraction(1)
    for w, xw in x.items():
        dS, dD = spS.get(w, 0), spD.get(w, 0)
        if dS == 0 or dD == 0:
            return Fraction(0)
        r *= (Fraction(dD, ND) / Fraction(dS, NS)) ** xw
    return r


def fixedN_binomial_ratio(S, D, L, x, N):
    spS, spD = spectrum(S, L), spectrum(D, L)
    n = sum(x.values())
    r = Fraction(1)
    for w in set(spS) | set(spD):
        xw = x.get(w, 0)
        dS, dD = spS.get(w, 0), spD.get(w, 0)

        def f(d):
            return (Fraction(d, N) ** xw) * (1 - Fraction(d, N)) ** (n - xw)

        if f(dS) == 0:
            return Fraction(0)
        r *= f(dD) / f(dS)
    return r


def variable_length_witness():
    S, D, L = "AAATT", "AAAATT", 3
    spS, spD = spectrum(S, L), spectrum(D, L)
    assert set(spS) == set(spD), (spS, spD)
    assert Is_realizable(S, L)
    assert (1, (0, 1, 2)) in triple_repeats(S)
    x = Counter(spS)
    x[("A", "A", "A")] += 1                      # one extra observed AAA read
    rows = []
    for extra in range(0, 4):
        xx = Counter(spS)
        xx[("A", "A", "A")] += extra
        rows.append((extra, sum(xx.values()),
                     exact_ratio_general(S, D, L, xx),
                     fixedN_binomial_ratio(S, D, L, xx, len(S))))
    return dict(S=S, D=D, spS=spS, spD=spD, x=dict(x), rows=rows)


# --------------------------------------------------------------------- main --

_QUICK = [
    (7, 3, 2), (8, 3, 2), (14, 4, 2), (10, 3, 3), (9, 3, 4), (17, 5, 2),
]
_FULL = [
    (5, 3, 2), (6, 3, 2), (7, 3, 2), (8, 3, 2),
    (12, 4, 2), (14, 4, 2), (16, 4, 2),
    (17, 5, 2), (18, 5, 2),
    (10, 3, 3), (12, 3, 3), (13, 3, 3),
    (9, 3, 4), (10, 3, 4), (11, 3, 4),
]


def main():
    full = "--full" in sys.argv
    t0 = time.time()
    print("[R] exhaustive rigidity scan (strict oriented single-strand)")
    scopes = _FULL if full else _QUICK
    total_Is, total_Lm1 = run_scopes(scopes)
    print(f"  TOTAL nonrigid_Is={total_Is}  nonrigid_Lm1<=2={total_Lm1}")
    assert total_Is == 0, "counterexample to the rigidity theorem found"
    assert total_Lm1 == 0, "counterexample to Theorem A found"
    print("  -> zero everywhere; consistency check for the rigidity theorem")

    print()
    print("[D] variable-length strict-oriented Section 6.2 counterexample")
    w = variable_length_witness()
    print(f"  S={w['S']} (|S|={len(w['S'])})  D={w['D']} (|D|={len(w['D'])})  L=3")
    print(f"  support(spec S) = support(spec D) = {sorted(set(w['spS']))}")
    print(f"  observed x = {w['x']}")
    print("  exact / fixed-N(5) ratios vs extra observed AAA reads:")
    for extra, n, er, br in w["rows"]:
        print(f"    +{extra} AAA (n={n}): exact={er}  fixed-N={br}"
              f"  ({'beats truth' if er > 1 and br > 1 else 'does not beat'})")
    assert w["rows"][0][2] < 1          # n = N = 5 slice: truth wins
    assert w["rows"][1][2] > 1          # n = 6 > N: competitor wins (exact)
    assert w["rows"][1][3] > 1          # and fixed-N
    assert all(r[2] < Fraction(1) for r in w["rows"][:1])
    print("  -> the same-length rigidity does NOT extend to different lengths")
    print("     (per-vertex reading; the witness violates d_D >= x)")
    print()
    print("elapsed %.1fs" % (time.time() - t0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
