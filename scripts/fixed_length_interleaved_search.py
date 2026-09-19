#!/usr/bin/env python3
"""
Self-contained exhaustive search for fixed-length exact-ML counterexamples whose
truth genome exercises the *interleaved-repeat bridging* clause of the source
information-feasible set I_s (Shomorony et al. Eq. (1), Bresler et al. semantics).

Source semantics (docs/bridging-source-semantics.md):
  * maximal repeat pair: equal length-ell windows at two starts, with preceding
    symbols differing and following symbols differing;
  * triple repeat: equal windows at three starts whose preceding symbols are not
    all equal and whose following symbols are not all equal;
  * a copy at start t is bridged iff some read covers at least one base strictly
    on both sides, i.e. covers (t-1) mod G and (t+ell) mod G;
  * an interleaved pair is two maximal repeat pairs whose four starts alternate
    cyclically; it is bridged iff at least one constituent copy is bridged;
  * I_s = coverage AND every triple repeat all-bridged AND every interleaved
    pair bridged.
Objective: fixed-length exact multinomial ordering,
  L(D|x) proportional to prod_{i: x_i>0} d_D(i)^{x_i}.
All arithmetic exact (fractions.Fraction).

This file deliberately re-implements the semantics instead of importing the
reviewed v2 search, so its results are independent evidence.
"""
import argparse
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product as iterproduct

FMT = "ABCDEFGH"


def fmt(seq):
    return "".join(FMT[c] for c in seq)


def kmers(seq, L):
    G = len(seq)
    d = defaultdict(int)
    for i in range(G):
        d[tuple(seq[(i + j) % G] for j in range(L))] += 1
    return dict(d)


def covers(seq, starts, L):
    G = len(seq)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_pairs(seq):
    G = len(seq)
    out = []
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(seq[(i + j) % G] for j in range(ell))].append(i)
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
            groups[tuple(seq[(i + j) % G] for j in range(ell))].append(i)
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
            e1, p1, w1 = reps[i]
            e2, p2, w2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def copy_bridged(seq, starts, t, ell, L):
    G = len(seq)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(seq, starts, L):
    if not covers(seq, starts, L):
        return False
    for ell, tri, w in triple_repeats(seq):
        for t in tri:
            if not copy_bridged(seq, starts, t, ell, L):
                return False
    for (e1, p1, w1), (e2, p2, w2) in interleaved_pairs(seq):
        b1 = any(copy_bridged(seq, starts, t, e1, L) for t in p1)
        b2 = any(copy_bridged(seq, starts, t, e2, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def ratio(spec_S, spec_D, obs):
    r = Fraction(1)
    for w, x in obs.items():
        if spec_S.get(w, 0) == 0 or spec_D.get(w, 0) == 0:
            return Fraction(0)
        r *= Fraction(spec_D[w], spec_S[w]) ** x
    return r


def cwr(pool, r):
    """Combinations with replacement (deterministic)."""
    pool = tuple(pool)
    n = len(pool)
    if n == 0 and r:
        return
    idx = [0] * r
    while True:
        yield tuple(pool[i] for i in idx)
        for i in range(r - 1, -1, -1):
            if idx[i] != n - 1:
                break
        else:
            return
        idx[i] += 1
        for j in range(i + 1, r):
            idx[j] = idx[i]


def analyze(G, L, alpha, N):
    genomes = list(iterproduct(range(alpha), repeat=G))
    specs = [kmers(g, L) for g in genomes]
    kmer_to = defaultdict(set)
    for i, sp in enumerate(specs):
        for k in sp:
            kmer_to[k].add(i)

    same, distinct = [], []
    is_inter = 0
    for s_idx, S in enumerate(genomes):
        ilv = interleaved_pairs(S)
        if not ilv:
            continue
        has_distinct = any(w1 != w2 for (_, _, w1), (_, _, w2) in ilv)
        for starts in cwr(range(G), N):
            sl = list(starts)
            if not check_I_s(S, sl, L):
                continue
            is_inter += 1
            obs = Counter()
            for r in sl:
                obs[tuple(S[(r + j) % G] for j in range(L))] += 1
            cands = None
            for k in obs:
                cands = set(kmer_to[k]) if cands is None else cands & kmer_to[k]
                if not cands:
                    break
            if not cands:
                continue
            cands.discard(s_idx)
            best, best_c = Fraction(1), None
            for d_idx in cands:
                r = ratio(specs[s_idx], specs[d_idx], obs)
                if r > best:
                    best, best_c = r, genomes[d_idx]
            if best > 1:
                rec = (S, best_c, tuple(sorted(sl)), dict(obs), best, ilv)
                (distinct if has_distinct else same).append(rec)
    return is_inter, same, distinct


def show(rec, L):
    S, D, starts, obs, ratio_, ilv = rec
    print(f"  Truth={fmt(S)} D={fmt(D)} starts={starts} "
          f"obs={ {fmt(k): v for k, v in obs.items()} } ratio={ratio_}")
    for (e1, p1, w1), (e2, p2, w2) in ilv:
        b1 = [t for t in p1 if copy_bridged(S, list(starts), t, e1, L)]
        b2 = [t for t in p2 if copy_bridged(S, list(starts), t, e2, L)]
        tag = " <== DISTINCT WORDS" if w1 != w2 else ""
        print(f"    {fmt(w1)}(ell={e1})@{p1} bridged={b1} || "
              f"{fmt(w2)}(ell={e2})@{p2} bridged={b2}{tag}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--G", type=int, default=7)
    ap.add_argument("--L", type=int, default=3)
    ap.add_argument("--alpha", type=int, default=3)
    ap.add_argument("--N", type=int, default=None)
    ap.add_argument("--examples", type=int, default=5)
    args = ap.parse_args()
    N = args.N if args.N else args.G
    t0 = time.time()
    is_inter, same, distinct = analyze(args.G, args.L, args.alpha, N)
    print(f"G={args.G} L={args.L} alpha={args.alpha} N={N} "
          f"({time.time()-t0:.1f}s)")
    print(f"I_s pairs with interleaved repeats: {is_inter}")
    print(f"counterexamples with interleaved clause: {len(same)+len(distinct)} "
          f"(same-word: {len(same)}, distinct-word: {len(distinct)})")
    for label, recs in (("DISTINCT-WORD", distinct), ("SAME-WORD", same)):
        if not recs:
            continue
        seen, shown = set(), 0
        for rec in sorted(recs, key=lambda r: (len(r[2]), r[4], r[0])):
            key = (rec[0], rec[2])
            if key in seen:
                continue
            seen.add(key)
            shown += 1
            print(f"\n{label} example {shown}:")
            show(rec, args.L)
            if shown >= args.examples:
                break


if __name__ == "__main__":
    main()
