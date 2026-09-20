#!/usr/bin/env python3
"""
Same-length transfer of the merged Section 6.2 bridging counterexample.

The merged counterexample (PR #39 / issue #36) is the *unequal-length* instance

    truth S = AAATT (G = 5),  competitor D = AAAATT (|D| = 6),
    L = 3, reads at starts (0,1,4), x = {AAA:1, AAT:1, TAA:1}, external N = 5.

This script asks whether that instance can be converted into a *same-length*
counterexample (|D| = |S| = N) while preserving bridging (I_s), source-faithful
bidirected feasibility (a spelled §6.2 circuit, per-vertex lower bound 1), and a
strict literal §6.1 likelihood advantage.  It checks:

  (A) Merged-instance obstruction.  Over *every* (integral) same-length
      throughput vector with support exactly supp(x), the literal §6.1
      objective is maximized exactly by the permutations of d_S.  Hence no
      same-length candidate -- spelled or a general §6.2 flow -- can strictly
      beat the truth while S, the read multiset, and N are held fixed.

  (B) Length padding does not escape.  For the two literal one-letter paddings
      of AAATT to length 6 (AAATTA, AAATTT), and more generally for every
      length-G word with window-class support {AAA,AAT,TAA} for G = 6, 7, a
      bounded exhaustive search over I_s-admissible read multisets and all
      same-length competitors finds no strict improvement.

  (C) Non-uniform escape.  Once the observed multiset is non-uniform, the
      I-projection target t = N x / n is not permutation-symmetric and the
      same-length question can be won.  Under the source's per-vertex lower
      bound 1 (not the stronger per-occurrence bound), the same-length witness

          S = AAATAT,  D = AAAAAT,  G = 6,  L = 3,  starts (0,0,1,3,5)

      satisfies I_s and the bidirected-circuit check and strictly improves the
      literal §6.1 binomial (ratio 5) and the exact fixed-length multinomial
      (ratio 3).  This independently reproduces the witness recorded on the
      unmerged branch `analysis/se62-peroccurrence-slice-obstruction`.

All arithmetic is exact `fractions.Fraction`; the deterministic checks exit
non-zero on any failed assertion.  The wide exhaustive search for fixed-length
witnesses is NOT duplicated here; see
`docs/section62-fixed-length-bidirected-counterexample.md` (unmerged branch) for
the 4608-instance scope count.

Reproduce:  python3 scripts/verify_same_length_lift.py
"""
import sys
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

A, T = 0, 1
COMP = {A: T, T: A}


def rc(s):
    return tuple(COMP[c] for c in reversed(s))


def mol(s):
    return min(tuple(s), rc(tuple(s)))


def windows(seq, L):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


def spec(seq, L):
    return Counter(mol(w) for w in windows(seq, L))


def observed(S, starts, L):
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % len(S)] for j in range(L)))] += 1
    return x


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
            if len(pos) < 2:
                continue
            for pair in combinations(pos, 2):
                if (S[(pair[0] - 1) % G] != S[(pair[1] - 1) % G]
                        and S[(pair[0] + ell) % G] != S[(pair[1] + ell) % G]
                        and pair not in seen):
                    seen.add(pair)
                    out.append((ell, pair))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
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
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))), (e2, tuple(sorted(p2)))))
    return out


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L):
    if not covers_all(S, starts, L):
        return False
    for ell, pos in triple_repeats(S):
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in interleaved_pairs(S):
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def walk_is_bidirected_circuit(seq, L, obs, per_occ):
    """Direct §6.2 spelled-circuit check (same criterion as the branch packet)."""
    ws = windows(seq, L)
    for a, b in zip(ws[:-1], ws[1:]):
        if a[1:] != b[:-1]:
            return False
    classes = Counter(mol(w) for w in ws)
    if any(w not in obs for w in classes):
        return False
    if per_occ:
        return all(classes.get(w, 0) >= c for w, c in obs.items())
    return all(classes.get(w, 0) >= 1 for w in obs)


def phi(x, n, N, d):
    if d < 0 or d > N:
        return Fraction(0)
    return Fraction(d, N) ** x * Fraction(N - d, N) ** (n - x)


def binom_product(x, n, N, d):
    r = Fraction(1)
    for w, xw in x.items():
        r *= phi(xw, n, N, d.get(w, 0))
    return r


def log_obj(x, n, N, d):
    """Exact-rational proxy for the log-objective; only used for comparisons."""
    r = Fraction(1)
    for w, xw in x.items():
        dw = d.get(w, 0)
        if dw == 0 or dw == N:
            return None
        r *= Fraction(dw, N) ** xw * Fraction(N - dw, N) ** (n - xw)
    return r


def compositions(total, k, minv=1):
    if k == 1:
        if total >= minv:
            yield (total,)
        return
    for v in range(minv, total - minv * (k - 1) + 1):
        for rest in compositions(total - v, k - 1, minv):
            yield (v,) + rest


def check_merged_obstruction():
    print("(A) merged-instance same-length obstruction")
    S, D = (A, A, A, T, T), (A, A, A, A, T, T)
    L, starts, N = 3, (0, 1, 4), 5
    x = observed(S, starts, L)
    n = sum(x.values())
    dS = spec(S, L)
    supp = sorted(x)
    pS = binom_product(x, n, N, dict(dS))
    best, bestv = Fraction(0), None
    for v in compositions(N, len(supp)):
        d = dict(zip(supp, v))
        p = binom_product(x, n, N, d)
        if p > best:
            best, bestv = p, v
    ratio = best / pS
    balanced = tuple(sorted((2, 2, 1)))
    ok = (set(x) == set(dS)
          and ratio == 1
          and tuple(sorted(bestv)) == balanced
          and tuple(sorted(dS[w] for w in supp)) == balanced)
    print(f"    x={dict(x)} n={n} N={N} d_S={dict(dS)}")
    print(f"    same-length throughput maximizer (support=supp x): {bestv}")
    print(f"    best/sigma(d_S) = {ratio}  (balanced partition {balanced})")
    print(f"    {'PASS' if ok else 'FAIL'}")
    return ok


def check_padding_no_escape():
    print("(B) literal one-letter / short-word padding does not escape")
    L = 3
    support = {(A, A, A), (A, A, T), (T, A, A)}  # AAA, AAT, TAA classes
    all_ok = True
    for G in (6, 7):
        truths = [S for S in product((A, T), repeat=G) if set(spec(S, L)) == support]
        found = 0
        for S in truths:
            dS = spec(S, L)
            Ds = [D for D in product((A, T), repeat=G) if set(spec(D, L)) == support]
            for nn in range(1, G):
                for starts in combinations_with_replacement(range(G), nn):
                    if not (covers_all(S, starts, L) and check_I_s(S, starts, L)):
                        continue
                    x = observed(S, starts, L)
                    if set(x) != support:
                        continue
                    pS = binom_product(x, nn, G, dict(dS))
                    for D in Ds:
                        dD = spec(D, L)
                        if dict(dD) == dict(dS):
                            continue
                        if binom_product(x, nn, G, dict(dD)) > pS:
                            found += 1
                            break
        print(f"    G={G}: {len(truths)} support-matching truths, strict same-length wins = {found}")
        all_ok &= (found == 0)
    print(f"    {'PASS' if all_ok else 'FAIL'}")
    return all_ok


def check_same_length_witness():
    print("(C) non-uniform same-length witness under the per-vertex lower bound 1")
    S = (A, A, A, T, A, T)   # AAATAT
    D = (A, A, A, A, A, T)   # AAAAAT
    L, starts = 3, (0, 0, 1, 3, 5)
    x = observed(S, starts, L)
    n = sum(x.values())
    dS, dD = spec(S, L), spec(D, L)
    N = len(S)  # external genome size = G = 6 (ratio is N-independent anyway)
    pS = binom_product(x, n, N, dict(dS))
    pD = binom_product(x, n, N, dict(dD))
    ratio = pD / pS
    # exact fixed-length multinomial ratio
    eratio = Fraction(1)
    for w, xw in x.items():
        eratio *= Fraction(dD.get(w, 0), dS[w]) ** xw
    ok = (check_I_s(S, starts, L)
          and set(dS) == set(x) and set(dD) == set(x)
          and walk_is_bidirected_circuit(S, L, set(x), per_occ=False)
          and walk_is_bidirected_circuit(D, L, set(x), per_occ=False)
          and ratio > 1 and ratio == 5
          and eratio == 3)
    print(f"    S={''.join(map(str, S))} D={''.join(map(str, D))} starts={starts}")
    print(f"    x={dict(x)} d_S={dict(dS)} d_D={dict(dD)}")
    print(f"    I_s={check_I_s(S, starts, L)}  "
          f"bidirected S/D="
          f"{walk_is_bidirected_circuit(S, L, set(x), False)}/"
          f"{walk_is_bidirected_circuit(D, L, set(x), False)}")
    print(f"    §6.1 ratio={ratio} (5), exact multinomial ratio={eratio} (3)")
    fail = {w: (dS[w], c) for w, c in x.items() if dS[w] < c}
    print(f"    per-occurrence infeasible truth coordinates (d_S(w) < x_w): {fail}"
          f" -- the win needs the per-vertex (type) reading")
    print(f"    {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    results = [check_merged_obstruction(),
               check_padding_no_escape(),
               check_same_length_witness()]
    print()
    if all(results):
        print("ALL CHECKS PASS")
        return 0
    print("SOME CHECKS FAILED")
    return 1


if __name__ == "__main__":
    sys.exit(main())
