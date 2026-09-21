#!/usr/bin/env python3
"""Direct route: for a given word S and L, enumerate the *spelled words* of all
Eulerian circuits of its de Bruijn multigraph (parallel equal edges treated as
indistinguishable), and check that P2 => the only spelled word is S's class.

This is independent of the grouping scan: it never enumerates other words."""
import random
from collections import defaultdict
from p2_eulerian_attack import (
    canonical, spectrum_key, p2, is_primitive, lyndon_words, trf, ilf,
)


def spelled_partners(S, L, cap=100000):
    spec = spectrum_key(S, L)              # ((Lmer, mult), ...)
    # edge types keyed by (prefix, suffix, label); multiplicity
    edges = []
    for lab, mult in spec:
        edges.append((lab[:-1], lab[1:], lab, mult))
    out = defaultdict(list)
    for i, (a, b, lab, m) in enumerate(edges):
        out[a].append(i)
    verts = sorted({a for a, b, lab, m in edges} | {b for a, b, lab, m in edges})
    start = verts[0]
    total = sum(m for *_, m in edges)
    found = set()
    counts = [m for *_, m in edges]

    n = len(S)
    nlab = n - L + 1  # only the first n-L+1 labelled edges contribute new chars

    def word_from_labels(labels):
        w = list(labels[0])
        for lab in labels[1:nlab]:
            w.append(lab[-1])
        return tuple(w)

    def rec(cur, remaining, labels):
        if len(found) > 4 or remaining == 0:
            if remaining == 0 and cur == start:
                found.add(canonical(word_from_labels(labels)))
            return
        for e in out[cur]:
            if counts[e] > 0:
                counts[e] -= 1
                labels.append(edges[e][2])
                rec(edges[e][1], remaining - 1, labels)
                labels.pop()
                counts[e] += 1

    rec(start, total, [])
    return found


def main():
    # sanity: known subtlety AABAB has parallel edges but unique word
    S = tuple("AABAB")
    print("AABAB partners:", spelled_partners(S, 3))
    S2 = tuple("AABABB")
    print("AABABB partners:", spelled_partners(S2, 3))
    print("AAAAB partners:", spelled_partners(tuple("AAAAB"), 3))

    # random P2 words, larger alphabets/lengths: direct spelled-partner search
    rng = random.Random(20260921)
    tested = 0
    bad = []
    for _ in range(30000):
        q = rng.randint(2, 6)
        alpha = [chr(ord("A") + i) for i in range(q)]
        n = rng.randint(6, 26)
        w = tuple(rng.choice(alpha) for _ in range(n))
        if not is_primitive(w) or canonical(w) != w:
            continue
        L = rng.randint(2, min(n, 8))
        if not p2(w, L):
            continue
        tested += 1
        parts = spelled_partners(w, L, cap=60000)
        if parts - {canonical(w)}:
            bad.append((w, L, parts))
            print("  COUNTEREXAMPLE", w, L, parts)
        if tested >= 3000:
            break
    print(f"random direct check: {tested} primitive P2 words, "
          f"{len(bad)} with a non-rotation spelled partner")


if __name__ == "__main__":
    main()
