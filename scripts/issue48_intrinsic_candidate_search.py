#!/usr/bin/env python3
"""Issue #48: variable-length exact ML under *intrinsic* candidate predicates.

The issue proposes replacing the external "true length" axiom by candidate
predicates an assembler can check on the candidate itself:

  * primitiveness (the candidate is not a nontrivial whole repetition), and
  * structural read-length admissibility (the candidate has no intrinsic
    repeat obstruction that makes it unresolvable at read length L).

This script makes those predicates exact for finite strings and adversarially
rechecks the repository's known variable-length counterexamples against them,
then searches bounded ranges for the smallest surviving counterexample.

Predicates (all candidate-intrinsic, i.e. functions of the candidate alone):

  primitive(D)         D is not w^k for any k >= 2.
  SR(D, L)             spectrum-resolvable: D is the unique circular genome of
                       its length with its L-mer spectrum (Ukkonen/Pevzner
                       identifiability).  Computed here by exhaustive grouping
                       of all length-n genomes by spectrum, so it is exact.
  RRF(D, L)            read-length repetition-free: no (L-1)-mer of D occurs
                       twice (Bresler's "every maximal repeat is bridged"
                       applied intrinsically; by Lemma 1 of
                       mathematics/bridging-and-spectrum-uniqueness.md this is
                       equivalent to all length-(L-1) windows being distinct).

Two candidate classes are studied:

  P_weak   = primitive AND SR          (the literal identifiability reading)
  P_strong = primitive AND SR AND RRF  (the over-strong all-repeats-bridged
                                        reading; note it is *not* compatible
                                        with the I_s antecedent, because an
                                        I_s-feasible truth such as ABACABC
                                        need not be RRF)

Objective (Medvedev-Brudno 2009, section 6.1, candidate-dependent length n):

    L(D|x)/L(S|x) = prod_{w: x_w>0} ( G * d_D(w) / (n * d_S(w)) )^{x_w}

with ratio 0 if some observed w has d_D(w)=0.  Exact Fraction arithmetic.

Hypothesis I_s on the truth is the *strict* source predicate
(docs/copy-bridging-predicate-correction.md): coverage, every triple repeat
all-bridged, every interleaved maximal-repeat pair bridged, with a copy at t of
length l bridged iff a read starts in {t-d : 1 <= d <= L-l-1}.

Reproduce:  python3 scripts/issue48_intrinsic_candidate_search.py
"""

from __future__ import annotations

import argparse
import sys
import time
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product

FMT = "ABCDEFGH"


# --------------------------------------------------------------------------
# basic exact circular-string predicates
# --------------------------------------------------------------------------

def fmt(seq):
    return "".join(FMT[c] for c in seq)


def windows(seq, L):
    G = len(seq)
    return tuple(tuple(seq[(i + j) % G] for j in range(L)) for i in range(G))


def spectrum(seq, L):
    return dict(Counter(windows(seq, L)))


def spec_key(seq, L):
    return tuple(sorted(Counter(windows(seq, L)).items()))


def canon(seq):
    G = len(seq)
    return min(tuple(seq[i:] + seq[:i]) for i in range(G))


def primitive(seq):
    G = len(seq)
    return not any(G % d == 0 and seq == seq[:d] * (G // d) for d in range(1, G))


def read_repetition_free(seq, L):
    """No (L-1)-mer occurs twice in D (Bresler 'all repeats bridged')."""
    if L - 1 <= 0:
        return True
    return max(Counter(windows(seq, L - 1)).values()) <= 1


def covers(seq, starts, L):
    G = len(seq)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


# --------------------------------------------------------------------------
# strict source bridging / I_s
# --------------------------------------------------------------------------

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
            e1, p1, _w1 = reps[i]
            e2, p2, _w2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            labels = [0 if p in p1 else 1 for p in four]
            if labels in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append((reps[i], reps[j]))
    return out


def strict_bridged(seq, starts, t, ell, L):
    G = len(seq)
    if L - ell - 1 < 1:
        return False
    return any((t - d) % G in starts for d in range(1, L - ell))


def check_Is(seq, starts, L):
    starts = set(starts)
    if not covers(seq, starts, L):
        return False, "coverage"
    for ell, tri, _w in triple_repeats(seq):
        for t in tri:
            if not strict_bridged(seq, starts, t, ell, L):
                return False, "triple"
    for (e1, p1, _w1), (e2, p2, _w2) in interleaved_pairs(seq):
        b1 = any(strict_bridged(seq, starts, t, e1, L) for t in p1)
        b2 = any(strict_bridged(seq, starts, t, e2, L) for t in p2)
        if not (b1 or b2):
            return False, "interleaved"
    return True, "ok"


# --------------------------------------------------------------------------
# likelihood
# --------------------------------------------------------------------------

def ratio(specS, G, specD, n, obs):
    r = Fraction(1)
    for w, x in obs.items():
        a, b = specS.get(w, 0), specD.get(w, 0)
        if a == 0 or b == 0:
            return Fraction(0)
        r *= Fraction(G * b, n * a) ** x
    return r


# --------------------------------------------------------------------------
# candidate universe with exact SR via exhaustive spectrum grouping
# --------------------------------------------------------------------------

def build_info(alpha, maxn, L):
    info = {}
    for n in range(1, maxn + 1):
        groups = defaultdict(set)
        for p in product(range(alpha), repeat=n):
            groups[spec_key(p, L)].add(canon(p))
        genomes = {c for cs in groups.values() for c in cs}
        info[n] = (sorted(genomes), groups)
    return info


def is_sr(D, info, L):
    n = len(D)
    return len(info[n][1].get(spec_key(D, L), set())) <= 1


def candidate_ok(D, info, L, predicate):
    if not primitive(D) or not is_sr(D, info, L):
        return False
    if predicate == "strong" and not read_repetition_free(D, L):
        return False
    return True


# --------------------------------------------------------------------------
# known-witness classification
# --------------------------------------------------------------------------

def _enc(s):
    m = {}
    for ch in s:
        m.setdefault(ch, len(m))
    return tuple(m[ch] for ch in s)


def enc_with(s, order):
    m = {ch: i for i, ch in enumerate(order)}
    return tuple(m[ch] for ch in s)


def classify_known(alpha, _default_L):
    """Classify the repository's known variable-length witnesses."""
    print("=" * 74)
    print("A. adversarial recheck of known variable-length counterexamples")
    print("=" * 74)
    # (truth string, L, latent starts, competitor string, note)
    cases = [
        ("ACGT", 2, (0, 0, 2), "ACACGT",
         "kernel-checked exact Variant E witness"),
        ("ACGT", 2, (0, 0, 0, 0), "ACACAC",
         "universality note; single-start sample fails I_s coverage"),
        ("AACGT", 2, (0, 0, 0, 0), "AAAA",
         "length-shrinkage note; single-start sample fails I_s coverage"),
        ("ABACABC", 3, (1, 1, 1, 3, 6), "ABAC",
         "unrestricted-length lift of the interleaved witness"),
        ("ABACABC", 3, (1, 1, 1, 3, 6), "ACABACB",
         "fixed-length interleaved witness (same length G=7)"),
    ]
    for sstr, L, starts, dstr, note in cases:
        order = []
        for ch in sstr:
            if ch not in order:
                order.append(ch)
        for ch in dstr:
            if ch not in order:
                order.append(ch)
        S, D = enc_with(sstr, order), enc_with(dstr, order)
        G, nd = len(S), len(D)
        info = build_info(max(alpha, len(order)), max(G, nd), L)
        spS, spD = spectrum(S, L), spectrum(D, L)
        ok, why = check_Is(S, starts, L)
        obs = Counter(tuple(S[(r + j) % G] for j in range(L)) for r in starts)
        r = ratio(spS, G, spD, nd, obs)
        prim_s, prim_d = primitive(S), primitive(D)
        sr_s, sr_d = is_sr(S, info, L), is_sr(D, info, L)
        rrf_d = read_repetition_free(D, L)
        weak = prim_d and sr_d
        strong = weak and rrf_d
        print(f"\n  S={sstr} (G={G}) starts={starts} D={dstr} (n={nd})  "
              f"[{note}]")
        print(f"    I_s(strict)={ok} ({why}); obs="
              f"{ {fmt(k): v for k, v in obs.items()} }")
        print(f"    truth: primitive={prim_s} SR={sr_s}")
        print(f"    cand : primitive={prim_d} SR={sr_d} RRF={rrf_d}")
        print(f"    d_D(obs)={ {fmt(k): spD.get(k, 0) for k in obs} }"
              f"  d_S(obs)={ {fmt(k): spS.get(k, 0) for k in obs} }")
        print(f"    ratio={r} = {float(r):.5f}   "
              f"survives P_weak={weak and r > 1}  "
              f"survives P_strong={strong and r > 1}")


# --------------------------------------------------------------------------
# bounded exhaustive minimality search
# --------------------------------------------------------------------------

def minimal_counterexample(L, alpha, Gmax, Nmax, nmax, predicate,
                           nmin=None, require_nonvacuous=False):
    info = build_info(alpha, max(Gmax, nmax), L)
    nmin = L if nmin is None else nmin
    cands = []
    for n in range(max(1, nmin), nmax + 1):
        for p in product(range(alpha), repeat=n):
            D = canon(p)
            if D in [c for _, c in cands]:
                continue
            if candidate_ok(D, info, L, predicate):
                cands.append((n, D))

    best = None
    for G in range(L + 1, Gmax + 1):
        seen = set()
        truths = []
        for p in product(range(alpha), repeat=G):
            if not primitive(p) or not is_sr(p, info, L):
                continue
            c = canon(p)
            if c in seen:
                continue
            seen.add(c)
            if require_nonvacuous and not (triple_repeats(c) or
                                           interleaved_pairs(c)):
                continue
            truths.append(c)
        for S in truths:
            spS = spectrum(S, L)
            for N in range(1, Nmax + 1):
                seen_obs = set()
                for starts in combinations_with_replacement(range(G), N):
                    ok, _ = check_Is(S, starts, L)
                    if not ok:
                        continue
                    obs = Counter(tuple(S[(r + j) % G] for j in range(L))
                                  for r in starts)
                    key = tuple(sorted(obs.items()))
                    if key in seen_obs:
                        continue
                    seen_obs.add(key)
                    for n, D in cands:
                        if canon(D) == canon(S):
                            continue
                        r = ratio(spS, G, spectrum(D, L), n, obs)
                        if r > 1:
                            rec = (N, G, n, S, starts, tuple(sorted(obs.items())),
                                   D, r)
                            if best is None or rec[:3] < best[:3]:
                                best = rec
    return best


def report_minimal(L, alpha, ranges, predicates, nmin_variants):
    import itertools as it
    print("=" * 74)
    print("B. smallest surviving counterexample (bounded exhaustive search)")
    print("=" * 74)
    for predicate in predicates:
        for nmin_label, nmin in nmin_variants:
            for nonvac in (False, True):
                best = minimal_counterexample(
                    L, alpha, ranges["Gmax"], ranges["Nmax"], ranges["nmax"],
                    predicate, nmin=nmin, require_nonvacuous=nonvac)
                tag = (f"L={L} alpha={alpha} Gmax={ranges['Gmax']} "
                       f"Nmax={ranges['Nmax']} nmax={ranges['nmax']} "
                       f"pred={predicate} {nmin_label} "
                       f"{'nonvacuous' if nonvac else 'any'}")
                if best is None:
                    print(f"  {tag}: none found")
                    continue
                N, G, n, S, starts, obs, D, r = best
                print(f"  {tag}:")
                print(f"      N={N} G={G} n={n} S={fmt(S)} starts={starts} "
                      f"obs={ {fmt(k): v for k, v in obs} } D={fmt(D)} "
                      f"ratio={r}")


# --------------------------------------------------------------------------
# unbounded families
# --------------------------------------------------------------------------

def unbounded_families(alpha):
    print("=" * 74)
    print("C. unbounded-ratio families surviving the intrinsic predicates")
    print("=" * 74)
    L = 3
    info = build_info(alpha, 8, L)

    # (C1) weak predicate, repeat-free truth, vacuous I_s.
    S1 = _enc("AABC")
    G1 = len(S1)
    D1 = _enc("ABC")
    n1 = len(D1)
    print(f"\n  C1  weak: S={fmt(S1)} (G={G1}, repeat-free, I_s vacuous), "
          f"D={fmt(D1)} (n={n1})")
    print(f"      primitive={primitive(D1)} SR={is_sr(D1, info, L)} "
          f"RRF={read_repetition_free(D1, L)}")
    for N in [2, 4, 8]:
        starts = tuple([1] + [2] * (N - 1))
        ok, why = check_Is(S1, starts, L)
        obs = Counter(tuple(S1[(r + j) % G1] for j in range(L))
                      for r in starts)
        r = ratio(spectrum(S1, L), G1, spectrum(D1, L), n1, obs)
        expected = Fraction(4, 3) ** N
        assert ok and r == expected, (ok, why, r, expected)
        print(f"      N={N}: I_s={ok} ratio={r} = {float(r):.4f} "
              f"(= (G/n)^N = (4/3)^N)")
    print("      => ratio -> infinity; growth is exactly (G/n)^N.")

    # (C2) strong predicate with a NON-VACUOUS I_s truth.
    S2 = _enc("ABACABC")
    G2 = len(S2)
    D2 = _enc("ABAC")
    n2 = len(D2)
    print(f"\n  C2  strong: S={fmt(S2)} (G={G2}, non-vacuous I_s), "
          f"D={fmt(D2)} (n={n2})")
    print(f"      primitive={primitive(D2)} SR={is_sr(D2, info, L)} "
          f"RRF={read_repetition_free(D2, L)}")
    k = 1
    for k in [1, 2, 3, 5, 9]:
        starts = (1,) * k + (3, 6)
        ok, why = check_Is(S2, starts, L)
        obs = Counter(tuple(S2[(r + j) % G2] for j in range(L))
                      for r in starts)
        r = ratio(spectrum(S2, L), G2, spectrum(D2, L), n2, obs)
        assert ok, (ok, why)
        print(f"      k={k}: I_s={ok} obs="
              f"{ {fmt(w): v for w, v in obs.items()} } ratio={r} = "
              f"{float(r):.4f}")
    print("      ratio = (7/4)^k * (7/8)^2 -> infinity.")
    return S1, D1, S2, D2


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, default=3)
    ap.add_argument("--alpha", type=int, default=3)
    ap.add_argument("--Gmax", type=int, default=6)
    ap.add_argument("--Nmax", type=int, default=4)
    ap.add_argument("--nmax", type=int, default=6)
    ap.add_argument("--skip-minimal", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    classify_known(max(args.alpha, 4), args.L)
    unbounded_families(args.alpha)
    if not args.skip_minimal:
        report_minimal(
            args.L, args.alpha,
            {"Gmax": args.Gmax, "Nmax": args.Nmax, "nmax": args.nmax},
            ["weak", "strong"],
            [("n>=L", args.L), ("n>L", args.L + 1)])
    print(f"\ncompleted in {time.time() - t0:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
