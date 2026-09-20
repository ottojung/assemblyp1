#!/usr/bin/env python3
"""
Reproducible verification for the uniform single-strand / oriented strand
convention of the Shomorony et al. (2016) bridging -> maximum-likelihood
question.

Two logically different statements are checked and kept separate.

  (SEQ)  Pure sequence objective.  Oriented single-strand read types (no
         reverse-complement collapse), fixed-N MB09 Section 6.1 product of
         binomial marginals, external N = G, and no overlap-graph constraint on
         the candidate.  Here the negative result SURVIVES: S = AAATT,
         D = AAAAT, G = 5, L = 3, starts (0, 1, 4), exact ratio 2.  Up to the
         alphabet rename T <-> B this is exactly the kernel-checked
         `AssemblyP1.FixedLengthExactCounterexample` instance AAABB -> AAAAB.

  (S62)  The same oriented single-strand read types, but with the MB09
         Section 6.2 spelled-circuit admissibility (vertices are the observed
         reads, per-vertex lower bound 1, i.e. support equality) imposed on both
         the truth-induced candidate and the competitor.  Here the negative
         result does NOT survive: the companion note proves that `I_s` forces
         `spec_L(S)` to be the unique positive Eulerian circulation of total G
         on its support, so every same-length Section 6.2 candidate has the
         truth's spectrum.

The script re-verifies, exactly (fractions.Fraction) and self-contained:

  1. the (SEQ) witness: spectra, support inequality, exact ratio 2, and a
     non-vacuous `I_s` certificate;
  2. the rigidity lemma on exhaustive scopes: every word all of whose
     (L-1)-mers occur at most twice is rigid;
  3. the primitive-extension lemma: a primitive word with an (L-1)-mer
     occurring at least three times has a Bresler triple repeat of length
     >= L-1;
  4. the periodic-extension lemma: a non-primitive word whose primitive period
     repeats a factor of length >= L-1 has a Bresler triple repeat of length
     >= L-1;
  5. the (S62) zero: no `I_s`-realizable word is non-rigid.

All arithmetic is exact.  Deterministic.  Exits non-zero on any failed
assertion.  `--full` widens the exhaustive scopes.
"""
import sys
import time
from fractions import Fraction
from itertools import product as iproduct, combinations
from collections import defaultdict


# ----------------------------------------------------------------- spectra --

def spectrum(S, L):
    G = len(S)
    d = defaultdict(int)
    for i in range(G):
        d[tuple(S[(i + j) % G] for j in range(L))] += 1
    return dict(d)


def occurrence_counts(S, ell):
    G = len(S)
    c = defaultdict(int)
    for i in range(G):
        c[tuple(S[(i + j) % G] for j in range(ell))] += 1
    return c


def max_Lm1_occurrence(S, L):
    if L - 1 <= 0:
        return len(S)
    c = occurrence_counts(S, L - 1)
    return max(c.values(), default=0)


# ------------------------------------------------------- repeats / I_s -------

def maximal_repeat_pairs(S):
    """Bresler/Shomorony maximal repeat pairs (two copies, both flanks differ)."""
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for _, pos in groups.items():
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
    """Bresler triple repeats: three copies, preceding and following not all equal."""
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
            four = sorted(set(list(p1) + list(p2)))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            for p in p2:
                lab[p] = 1
            seq = [lab[p] for p in four]
            if seq in ([0, 1, 0, 1], [1, 0, 1, 0]):
                key = (e1, tuple(sorted(p1)), e2, tuple(sorted(p2)))
                if key not in seen:
                    seen.add(key)
                    out.append(((e1, tuple(sorted(p1))),
                                (e2, tuple(sorted(p2)))))
    return out


def Is_realizable(S, L):
    """Does S admit any read realization in Shomorony's set I_s?

    Coverage can always be arranged by sampling starts, and adding reads is
    monotone for bridging, so `I_s` is realizable iff no triple repeat has
    length > L-2 and every interleaved pair has a constituent repeat of length
    <= L-2.
    """
    if any(ell > L - 2 for ell, _ in triple_repeats(S)):
        return False
    for (e1, _), (e2, _) in interleaved_pairs(S):
        if min(e1, e2) > L - 2:
            return False
    return True


def has_triple_repeat_at_least_Lm1(S, L):
    return any(ell >= L - 1 for ell, _ in triple_repeats(S))


# ------------------------------------------------------- (SEQ) witness -------

def check_seq_witness():
    S, D, L, N = "AAATT", "AAAAT", 3, 5
    starts = [0, 1, 4]
    x = defaultdict(int)
    for r in starts:
        x[tuple(S[(r + j) % N] for j in range(L))] += 1
    spS, spD = spectrum(S, L), spectrum(D, L)
    n = sum(x.values())
    assert n == 3
    # exact multinomial, same length: ratio = prod (d_D/d_S)^x
    ratio = Fraction(1)
    for w, xw in x.items():
        assert spS.get(w, 0) > 0 and spD.get(w, 0) > 0, (w, spS, spD)
        ratio *= Fraction(spD[w], spS[w]) ** xw
    assert ratio == 2, ratio
    # fixed-N Section 6.1 product of binomial marginals
    def binomial(a, b):
        r = Fraction(1)
        for w in set(spS) | set(spD):
            xw = x.get(w, 0)
            da, db = a.get(w, 0), b.get(w, 0)
            r *= ((Fraction(db, N) ** xw) * (1 - Fraction(db, N)) ** (n - xw)) / \
                 ((Fraction(da, N) ** xw) * (1 - Fraction(da, N)) ** (n - xw))
        return r
    bin_ratio = binomial(spS, spD)
    assert bin_ratio > 1, bin_ratio
    # I_s certificate: coverage + all-bridged length-1 triple repeat at 0,1,2
    cov = {(r + o) % N for r in starts for o in range(L)}
    assert cov == set(range(N))
    tri = triple_repeats(S)
    assert (1, (0, 1, 2)) in tri, tri
    assert Is_realizable(S, L), (S, triple_repeats(S), interleaved_pairs(S))
    # support inequality: this is a sequence-only witness, not a Section 6.2 one
    assert set(spS) != set(x) and set(spD) != set(x)
    return ratio, bin_ratio


# ------------------------------------------------- rigidity / non-rigidity ----

def non_rigid_support_set(genomes, L):
    """Supports (frozensets of window types) carrying more than one spectrum.

    A word is non-rigid on its support exactly when its support lies in this
    set, because any two words with the same support give two positive spectra
    of the same total length.
    """
    groups = defaultdict(set)
    for S in genomes:
        sp = spectrum(S, L)
        groups[frozenset(sp.keys())].add(tuple(sorted(sp.items())))
    return {k for k, v in groups.items() if len(v) > 1}


def min_period(S):
    G = len(S)
    for d in range(1, G):
        if G % d == 0 and all(S[i] == S[i % d] for i in range(G)):
            return d
    return G


def scan_scope(G, L, sigma):
    genomes = list(iproduct(range(sigma), repeat=G))
    nonrigid = non_rigid_support_set(genomes, L)
    n_all_nonrigid = 0
    n_rigid_violations = 0          # non-rigid but every (L-1)-mer <= 2
    n_is_realizable = 0
    n_s62 = 0                       # I_s-realizable and non-rigid
    n_prim_bad = 0                  # primitive, Lm1>=3, no triple >= L-1
    n_period_bad = 0                # periodic, repeated long period factor, no triple
    examples = []
    for S in genomes:
        V = frozenset(spectrum(S, L).keys())
        is_nr = V in nonrigid
        if is_nr:
            n_all_nonrigid += 1
            if max_Lm1_occurrence(S, L) <= 2:
                n_rigid_violations += 1
                if len(examples) < 5:
                    examples.append(("rigidity", "".join(map(str, S))))
        real = Is_realizable(S, L)
        if real:
            n_is_realizable += 1
            if is_nr:
                n_s62 += 1
                if len(examples) < 5:
                    examples.append(("s62", "".join(map(str, S))))
        p = min_period(S)
        # Lemma 2 (primitive extension)
        if p == G and max_Lm1_occurrence(S, L) >= 3 and \
                not has_triple_repeat_at_least_Lm1(S, L):
            n_prim_bad += 1
            if len(examples) < 5:
                examples.append(("prim", "".join(map(str, S))))
        # Lemma 3 (periodic extension): period word P repeats a factor of
        # length >= L-1, yet no long triple repeat
        if p < G:
            P = tuple(S[:p])
            # factor of P of length >= L-1 occurring at least twice in P
            repeated_long = False
            for ell in range(L - 1, p):
                c = occurrence_counts(P, ell)
                if any(v >= 2 for v in c.values()):
                    repeated_long = True
                    break
            if repeated_long and not has_triple_repeat_at_least_Lm1(S, L):
                n_period_bad += 1
                if len(examples) < 5:
                    examples.append(("period", "".join(map(str, S))))
    return dict(n_all_nonrigid=n_all_nonrigid,
                n_rigid_violations=n_rigid_violations,
                n_is_realizable=n_is_realizable,
                n_s62=n_s62, n_prim_bad=n_prim_bad,
                n_period_bad=n_period_bad, examples=examples)


_QUICK = [(12, 3, 2), (14, 3, 2), (12, 4, 2), (10, 3, 3)]
_FULL = [(12, 3, 2), (14, 3, 2), (16, 3, 2), (18, 3, 2),
         (12, 4, 2), (14, 4, 2), (16, 4, 2),
         (12, 5, 2), (14, 5, 2),
         (10, 3, 3), (11, 3, 3), (12, 3, 3),
         (10, 4, 3), (11, 4, 3),
         (8, 3, 4), (9, 3, 4), (10, 3, 4)]


def main():
    full = "--full" in sys.argv
    t0 = time.time()
    ratio, bin_ratio = check_seq_witness()
    print("[SEQ] uniform oriented single-strand sequence witness "
          "AAATT -> AAAAT")
    print(f"      exact same-length ratio = {ratio} > 1 ; "
          f"Section 6.1 binomial ratio = {bin_ratio} > 1")
    print("      I_s certificate holds; supports differ: sequence-only, not S62")
    print()

    scopes = _FULL if full else _QUICK
    print("[S62] exhaustive scan: rigidity and extension lemmas")
    fail = 0
    for G, L, sigma in scopes:
        t = time.time()
        r = scan_scope(G, L, sigma)
        line = (f"  G={G:>2} L={L} alpha={sigma}: "
                f"nonrigid={r['n_all_nonrigid']:>6} "
                f"rigidity_violations={r['n_rigid_violations']} "
                f"I_s={r['n_is_realizable']:>6} "
                f"S62={r['n_s62']} "
                f"lemma2_bad={r['n_prim_bad']} "
                f"lemma3_bad={r['n_period_bad']}")
        if r["examples"]:
            line += "  " + str(r["examples"])
        print(line + f"  ({time.time()-t:.1f}s)")
        sys.stdout.flush()
        fail += (r["n_rigid_violations"] + r["n_s62"] +
                 r["n_prim_bad"] + r["n_period_bad"])
    print()
    assert fail == 0, f"{fail} counterexample(s) to a claimed lemma/fact"
    print("[S62] all checks passed; total elapsed %.1fs" % (time.time() - t0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
