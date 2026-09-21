#!/usr/bin/env python3
"""Combinatorial checks for bridging conditions vs. L-mer-spectrum uniqueness.

This script is evidence for, and reproduces the witnesses in,
`mathematics/bridging-and-spectrum-uniqueness.md`.

Reproduces:
  A. `AABAB` (G=5, L=3) satisfies the full-read I_s conditions yet has a
     repeated length-L window, so I_s does not bound L-mer multiplicity.
  B. Explicit same-length, non-equivalent genome pairs with identical
     L-mer spectra (AABAC/AACAB, AABABB/AABBAB, AAABAABB/AAABBAAB).
  C. Exhaustive check that every I_s-admissible primitive genome in small
     parameter ranges has a unique L-mer spectrum up to cyclic shift.
  D. Randomized check of the same claim at larger parameters.

Everything is exact; no floating point.  Run: `python3 scripts/bridging_spectrum_uniqueness.py`.
"""

import argparse
import itertools
import random
from collections import Counter, defaultdict


# ---------- core combinatorial predicates on circular strings ----------

def windows(s, L):
    G = len(s)
    return tuple("".join(s[(i + j) % G] for j in range(L)) for i in range(G))


def canon(s):
    return min(s[i:] + s[:i] for i in range(len(s)))


def spectrum(s, L):
    return tuple(sorted(Counter(windows(s, L)).items()))


def primitive(s):
    G = len(s)
    return not any(G % d == 0 and s == s[:d] * (G // d) for d in range(1, G))


def _at(s, i):
    return s[i % len(s)]


def max_repeat_pairs(s):
    """Maximal occurrence pairs (t1 < t2, length l).

    The equal run of t1, t2 is extended maximally to the right; the pair is
    kept only if it is also left-maximal.  Fully wrapping (periodic) pairs are
    skipped.  Returns (t1, t2, l)."""
    G = len(s)
    out, seen = [], set()
    for t1 in range(G):
        for t2 in range(t1 + 1, G):
            l = 0
            while l < G and _at(s, t1 + l) == _at(s, t2 + l):
                l += 1
            if l >= G:
                continue
            if _at(s, t1 - 1) == _at(s, t2 - 1):
                continue
            if l < 1:
                continue
            key = (t1, t2, l)
            if key not in seen:
                seen.add(key)
                out.append(key)
    return out


def triple_repeats(s):
    """Maximal triple repeats: three starts with equal maximal run length l,
    preceding symbols not all equal and following symbols not all equal."""
    G = len(s)
    out = []
    for t in itertools.combinations(range(G), 3):
        l = 0
        while l < G and _at(s, t[0] + l) == _at(s, t[1] + l) == _at(s, t[2] + l):
            l += 1
        if l < 1:
            continue
        if all(_at(s, t[0] - 1) == _at(s, t[i] - 1) for i in (1, 2)):
            continue
        if all(_at(s, t[0] + l) == _at(s, t[i] + l) for i in (1, 2)):
            continue
        out.append((t, l))
    return out


def _alternate(a, b, c, d):
    labs = [x[1] for x in sorted([(a, "A"), (b, "B"), (c, "A"), (d, "B")])]
    return labs in (["A", "B", "A", "B"], ["B", "A", "B", "A"])


def is_admissible_full(s, L):
    """Whether the genome admits *some* coverage read set satisfying I_s.

    Taking one read at every circular start maximizes bridging power, so this
    is equivalent to existence of an I_s-satisfying read set.  Under the
    full read set a copy of length l is bridged iff l <= L-2, hence:
      * every triple repeat has all copies of length <= L-2;
      * every interleaved maximal-repeat pair has a constituent of length
        <= L-2.
    Returns (ok, witness)."""
    for t, l in triple_repeats(s):
        if l > L - 2:
            return False, ("triple", t, l)
    pairs = max_repeat_pairs(s)
    for i in range(len(pairs)):
        for j in range(i + 1, len(pairs)):
            t1, t2, l1 = pairs[i]
            u1, u2, l2 = pairs[j]
            if len({t1, t2, u1, u2}) < 4:
                continue
            if _alternate(t1, u1, t2, u2) or _alternate(t1, u2, t2, u1):
                if min(l1, l2) > L - 2:
                    return False, ("interleaved", pairs[i], pairs[j])
    return True, None


def has_repeated_kmer(s, L):
    return max(Counter(windows(s, L)).values()) >= 2


# ---------- spectrum sharing across all genomes of a given length ----------

def spectra_classes(alpha, L, G):
    groups = defaultdict(set)
    for p in itertools.product(alpha, repeat=G):
        s = "".join(p)
        groups[spectrum(s, L)].add(canon(s))
    return groups


def ambiguous_genomes(s, L, cap=256):
    """All circular genomes (canonical forms) realizing the same L-mer
    spectrum as `s`, obtained by enumerating Eulerian circuits of the
    de Bruijn multigraph.  Returns a set; rotations are quotiented by
    fixing the first edge."""
    G = len(s)
    edges = windows(s, L)
    adj = defaultdict(list)
    for i, e in enumerate(edges):
        adj[e[:-1]].append(i)
    start_node = edges[0][:-1]
    first = sorted(adj[start_node])[0]
    out = set()
    used = [False] * G
    seq = []

    def rec(node):
        if len(out) >= cap:
            return
        if len(seq) == G:
            if edges[seq[-1]][1:] == start_node:
                merged = edges[seq[0]]
                for i in seq[1:]:
                    merged += edges[i][-1]
                out.add(canon(merged[:G]))
            return
        for i in adj[node]:
            if used[i]:
                continue
            used[i] = True
            seq.append(i)
            rec(edges[i][1:])
            seq.pop()
            used[i] = False

    used[first] = True
    seq.append(first)
    rec(edges[first][1:])
    return out


# ---------- checks ----------

def check_A(verbose=True):
    s, L = "AABAB", 3
    ok, wit = is_admissible_full(s, L)
    d = Counter(windows(s, L))
    assert ok, wit
    assert d["ABA"] == 2
    if verbose:
        print("[A] S=AABAB G=5 L=3: I_s-admissible, d(ABA)=", d["ABA"],
              "-> I_s does not force L-mer multiplicity 1")
    return True


def check_B(verbose=True):
    cases = [("AABAC", "AACAB", 2), ("AABABB", "AABBAB", 3),
             ("AAABAABB", "AAABBAAB", 4)]
    for s1, s2, L in cases:
        assert Counter(windows(s1, L)) == Counter(windows(s2, L))
        assert canon(s1) != canon(s2)
        if verbose:
            ok, wit = is_admissible_full(s1, L)
            print(f"[B] {s1} / {s2} (L={L}): equal spectrum, non-equivalent; "
                  f"S1 I_s-admissible={ok} witness={wit}")
    return True


def check_C(configs, verbose=True):
    total_adm = total_amb = 0
    for alpha, L, Gmax in configs:
        adm = amb = 0
        for G in range(L, Gmax + 1):
            groups = spectra_classes(alpha, L, G)
            for p in itertools.product(alpha, repeat=G):
                s = "".join(p)
                if not primitive(s):
                    continue
                ok, _ = is_admissible_full(s, L)
                if not ok:
                    continue
                adm += 1
                if len(groups[spectrum(s, L)]) > 1:
                    amb += 1
                    print("  COUNTEREXAMPLE I_s-adm but ambiguous:", G, L, s)
        total_adm += adm
        total_amb += amb
        if verbose:
            print(f"[C] alpha={alpha} L={L} Gmax={Gmax}: admissible={adm} "
                  f"spectrum-ambiguous={amb}")
    if verbose:
        print(f"[C] total admissible={total_adm} ambiguous={total_amb}")
    assert total_amb == 0
    return True


def check_D(n, seed, verbose=True):
    rng = random.Random(seed)
    alphas = ["ABCDE", "ABCD"]
    tested = adm = amb = 0
    for _ in range(n):
        alpha = rng.choice(alphas)
        G = rng.randint(8, 18)
        L = rng.randint(3, min(6, G))
        s = "".join(rng.choice(alpha) for _ in range(G))
        tested += 1
        if not is_admissible_full(s, L)[0]:
            continue
        adm += 1
        if len(ambiguous_genomes(s, L, cap=4)) > 1:
            amb += 1
            print("  COUNTEREXAMPLE (random) I_s-adm but ambiguous:", G, L, s)
    if verbose:
        print(f"[D] random tested={tested} admissible={adm} "
              f"spectrum-ambiguous={amb}")
    assert amb == 0
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="smaller exhaustive ranges")
    ap.add_argument("--random", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()

    check_A()
    check_B()
    if args.quick:
        configs = [("AB", 3, 12), ("AB", 4, 12), ("ABC", 3, 8)]
    else:
        configs = [("AB", 3, 15), ("AB", 4, 14), ("ABC", 3, 10),
                   ("ABC", 4, 9), ("ABCD", 3, 8)]
    check_C(configs)
    check_D(args.random, args.seed)
    print("all checks passed")


if __name__ == "__main__":
    main()
