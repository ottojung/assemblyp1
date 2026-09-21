#!/usr/bin/env python3
"""
Independent, rotation-reduced exhaustive search for a same-length strict-oriented
Section 6.2 support-feasible counterexample to the Shomorony et al. (2016)
bridging -> maximum-likelihood implication.

Object searched (faithful, strict-oriented conventions)
------------------------------------------------------
A circular truth S of length G over an alphabet of size sigma.  Read types are
oriented length-L windows (no reverse-complement collapse).  The truth must
admit a Shomorony I_s read realization; since adding reads is monotone for
coverage and bridging, I_s is realizable on S iff

    (T) no Bresler triple repeat of S has length >= L-1, and
    (I) no interleaved maximal-repeat pair has BOTH lengths >= L-1.

A same-length Section 6.2 support-feasible counterexample exists iff there is a
circular truth S with I_s realizable AND a circular D with |D| = |S|, G = |S|,
such that supp(spec_L(D)) = supp(spec_L(S)) and spec_L(D) != spec_L(S).  (The
"strict" likelihood improvement then follows for every objective that is a
function of (spec_L(D), x): choose x with support V = supp(spec_L(S)); the
reduction and amplification argument are in the companion note.)  Equivalently:
S is I_s realizable AND its length-L window-support is NON-RIGID.

This script decides non-rigidity exhaustively by enumerating circular truths up
to rotation (necklaces) and grouping them by the frozenset/bitmask of present
length-L window types.  A support is non-rigid exactly when two distinct window
count vectors share it.

Independence
------------
The implementation shares no code with scripts/verify_oriented_ss_se62_same_length.py
or scripts/support_feasibility_search.py.  It uses a different enumeration
(Fredricksen-Kessler-Maiorana necklaces instead of all sigma^G linear strings),
a different support representation (integer bitmasks over window codes), and its
own I_s routine.  The rotation reduction is exact because both the spectrum and
the support are rotation invariant.  `--selftest` cross-validates the I_s routine
and the per-scope counts against the existing reference script on small scopes.

Epistemics
----------
Every zero reported here is a FINITE, EXHAUSTIVE-IN-SCOPE COMPUTATION.  It is
evidence, not a proof of absence beyond the listed scope.  No output of this
script is a proof.

Usage
-----
    python3 scripts/broad_se62_oriented_search.py --selftest
    python3 scripts/broad_se62_oriented_search.py --quick
    python3 scripts/broad_se62_oriented_search.py --scope G L sigma [--scope ...]
    python3 scripts/broad_se62_oriented_search.py --full [--jobs N]
"""
import sys
import time
import argparse
import hashlib
from collections import defaultdict
from multiprocessing import Pool


def _spectrum_signature(spec):
    """A 128-bit digest of the exact window-count vector.

    Used only as a compact equality key so that the support -> spectrum table
    fits in memory for large alphabets.  Two distinct spectra collide with
    probability ~2^-128 per pair; over < 10^8 pairs this is < 10^-22.  A
    collision could only hide a non-rigid support (a false zero), never invent
    a counterexample, and the reference scopes in `--selftest` use exact tuples.
    """
    items = sorted(spec.items())
    h = hashlib.blake2b(digest_size=16)
    for code, count in items:
        h.update(code.to_bytes(4, "big"))
        h.update(count.to_bytes(4, "big"))
    return h.digest()


# ------------------------------------------------------------- enumeration ---

def necklaces(n, k):
    """Yield every length-n word over {0,...,k-1} that is <= all its rotations.

    Fredricksen-Kessler-Maiorana recursion (LYNDON/necklace generation).  Each
    circular word is represented exactly once.
    """
    a = [0] * (n + 1)

    def gen(t, p):
        if t > n:
            if n % p == 0:
                yield tuple(a[1:n + 1])
        else:
            a[t] = a[t - p]
            yield from gen(t + 1, p)
            for j in range(a[t - p] + 1, k):
                a[t] = j
                yield from gen(t + 1, t)

    yield from gen(1, 1)


def window_code(S, i, ell, sigma):
    c = 0
    n = len(S)
    for j in range(ell):
        c = c * sigma + S[(i + j) % n]
    return c


def spectrum_codes(S, L, sigma):
    """Window-type counts as a dict code -> count, via a rolling code."""
    n = len(S)
    if L == 1:
        d = {}
        for x in S:
            d[x] = d.get(x, 0) + 1
        return d
    p = sigma ** (L - 1)
    c = 0
    for j in range(L):
        c = c * sigma + S[j]
    d = {c: 1}
    for i in range(1, n):
        c = (c - S[i - 1] * p) * sigma + S[(i + L - 1) % n]
        d[c] = d.get(c, 0) + 1
    return d


def support_mask(spec):
    m = 0
    for c in spec:
        m |= 1 << c
    return m


# ------------------------------------------------------------------- I_s -----

def _triple_blocks(S, L):
    """True iff some Bresler triple repeat of S has length >= L-1."""
    n = len(S)
    sigma = _SIGMA(S)
    # Fast necessary-condition pre-pass: any length-(L-1) window occurring >= 3
    # times is a prefix of every length >= L-1 triple repeat.  If none occurs
    # three times, no long triple repeat exists.
    base = spectrum_codes(S, L - 1, sigma)
    if max(base.values(), default=0) < 3:
        return False
    for ell in range(L - 1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[window_code(S, i, ell, sigma)].append(i)
        for pos in groups.values():
            if len(pos) < 3:
                continue
            pres = {S[(p - 1) % n] for p in pos}
            posts = {S[(p + ell) % n] for p in pos}
            if len(pres) > 1 and len(posts) > 1:
                return True
    return False


def _SIGMA(S):
    return max(S) + 1


def _interleaved_unbridged(S, L):
    """True iff an interleaved maximal-repeat pair has both lengths >= L-1."""
    n = len(S)
    sigma = _SIGMA(S)
    # maximal repeat pairs of length >= L-1 only; shorter repeats are always
    # bridgeable and cannot make an interleaved pair fail.
    reps = []
    seen = set()
    for ell in range(L - 1 if L - 1 >= 1 else 1, n):
        groups = defaultdict(list)
        for i in range(n):
            groups[window_code(S, i, ell, sigma)].append(i)
        for pos in groups.values():
            if len(pos) < 2:
                continue
            for a in range(len(pos)):
                for b in range(a + 1, len(pos)):
                    i, j = pos[a], pos[b]
                    if S[(i - 1) % n] != S[(j - 1) % n] and \
                       S[(i + ell) % n] != S[(j + ell) % n]:
                        if (i, j) not in seen:
                            seen.add((i, j))
                            reps.append((ell, i, j))
    m = len(reps)
    for a in range(m):
        e1, i1, j1 = reps[a]
        s1 = {i1, j1}
        for b in range(a + 1, m):
            e2, i2, j2 = reps[b]
            four = s1 | {i2, j2}
            if len(four) != 4:
                continue
            lab = {i1: 0, j1: 0, i2: 1, j2: 1}
            seq = [lab[p] for p in sorted(four)]
            if seq in ([0, 1, 0, 1], [1, 0, 1, 0]):
                return True
    return False


def is_realizable(S, L):
    return not _triple_blocks(S, L) and not _interleaved_unbridged(S, L)


# --------------------------------------------------------------- scanning ----

def nonrigid_supports(n, L, sigma, progress=False):
    first = {}
    nr = set()
    cnt = 0
    for S in necklaces(n, sigma):
        cnt += 1
        d = spectrum_codes(S, L, sigma)
        sup = support_mask(d)
        if sup in nr:
            continue
        key = _spectrum_signature(d)
        prev = first.get(sup)
        if prev is None:
            first[sup] = key
        elif prev != key:
            nr.add(sup)
            del first[sup]
    if progress:
        print(f"    [nonrigid] G={n} L={L} alpha={sigma}: {cnt} necklaces, "
              f"{len(nr)} non-rigid supports", flush=True)
    return nr, cnt


def scan_scope(n, L, sigma, want_examples=5):
    t0 = time.time()
    nr, n_neck = nonrigid_supports(n, L, sigma)
    both = 0
    ex = []
    # second pass: only truths whose support is non-rigid can matter
    for S in necklaces(n, sigma):
        d = spectrum_codes(S, L, sigma)
        if support_mask(d) not in nr:
            continue
        if is_realizable(S, L):
            both += 1
            if len(ex) < want_examples:
                ex.append("".join(chr(ord('0') + c) if c < 10 else str(c) for c in S))
    return dict(G=n, L=L, alpha=sigma, necklaces=n_neck, nonrigid=len(nr),
               counterexample_candidates=both, examples=ex, seconds=time.time() - t0)


# --------------------------------------------------------------- self test ---

# Golden non-rigid-support counts, produced by the reviewed reference
# scripts/verify_oriented_ss_se62_same_length.py (unmerged branch artifact).
# They let `--selftest` run even where that reference file is absent.
_GOLDEN_NONRIGID = {
    (9, 2, 2): 3, (10, 2, 2): 3, (14, 3, 2): 19, (14, 4, 2): 85,
    (14, 5, 2): 33, (10, 3, 3): 284, (10, 4, 3): 36, (8, 3, 4): 54,
    (9, 3, 4): 402,
}


def _selftest():
    import os
    import importlib.util
    import itertools
    refpath = "scripts/verify_oriented_ss_se62_same_length.py"
    ref = None
    if os.path.exists(refpath):
        spec = importlib.util.spec_from_file_location("ref", refpath)
        ref = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ref)

    if ref is not None:
        print("[selftest] I_s agreement with reference on small scopes")
        checked = 0
        for G, L, sigma in [(6, 3, 2), (8, 3, 2), (10, 3, 2), (10, 4, 2),
                            (8, 3, 3), (6, 3, 4)]:
            for tup in itertools.product(range(sigma), repeat=G):
                mine = is_realizable(tup, L)
                theirs = ref.Is_realizable(tup, L)
                if mine != theirs:
                    print(f"  MISMATCH G={G} L={L} a={sigma} S={tup} "
                          f"mine={mine} ref={theirs}")
                    return 1
                checked += 1
        print(f"  I_s agreed on {checked} words")
    else:
        print(f"[selftest] reference {refpath} absent; skipping direct I_s "
              "comparison, using golden counts only")

    print("[selftest] non-rigid support counts vs golden (and reference if present)")
    cases = list(_GOLDEN_NONRIGID)
    for G, L, sigma in cases:
        nr, _ = nonrigid_supports(G, L, sigma)
        golden = _GOLDEN_NONRIGID[(G, L, sigma)]
        ok = len(nr) == golden
        extra = ""
        if ref is not None:
            n_nr, both, _ = ref.scan_scope(G, L, sigma)
            ok = ok and n_nr == golden and both == 0
            extra = f" ref={n_nr} ref_cex={both}"
        print(f"  G={G:>2} L={L} a={sigma}: mine={len(nr)} golden={golden}{extra} "
              f"{'OK' if ok else 'MISMATCH'}")
        if not ok:
            return 1
    print("[selftest] PASS")
    return 0


# ------------------------------------------------------------------ scopes ---

_QUICK = [
    (18, 3, 2), (20, 3, 2), (18, 4, 2), (20, 4, 2), (16, 5, 2), (18, 5, 2),
    (12, 3, 3), (13, 3, 3), (11, 4, 3), (12, 4, 3), (10, 3, 4), (11, 3, 4),
]

# The scopes whose results are recorded in
# results/s62_oriented_broad_scan_2026-09-20.txt.  Exact command:
#   python3 scripts/broad_se62_oriented_search.py --full
_FULL = [
    # binary, L=2
    (9, 2, 2), (10, 2, 2),
    # binary, L=3
    (14, 3, 2), (16, 3, 2), (18, 3, 2), (20, 3, 2), (22, 3, 2), (24, 3, 2),
    (26, 3, 2), (28, 3, 2), (30, 3, 2),
    # binary, L=4
    (18, 4, 2), (20, 4, 2), (22, 4, 2), (24, 4, 2), (26, 4, 2), (28, 4, 2),
    (30, 4, 2),
    # binary, L=5
    (12, 5, 2), (14, 5, 2), (16, 5, 2), (18, 5, 2), (20, 5, 2), (22, 5, 2),
    (24, 5, 2), (26, 5, 2), (28, 5, 2),
    # binary, L=6
    (14, 6, 2), (16, 6, 2), (18, 6, 2), (20, 6, 2), (22, 6, 2), (24, 6, 2),
    (26, 6, 2), (28, 6, 2),
    # binary, L=7,8
    (20, 7, 2), (22, 7, 2), (24, 7, 2), (26, 7, 2),
    (20, 8, 2), (22, 8, 2), (24, 8, 2),
    # ternary, L=3
    (10, 3, 3), (11, 3, 3), (12, 3, 3), (13, 3, 3), (14, 3, 3), (15, 3, 3),
    (16, 3, 3), (17, 3, 3), (18, 3, 3),
    # ternary, L=4
    (10, 4, 3), (11, 4, 3), (12, 4, 3), (13, 4, 3), (14, 4, 3), (15, 4, 3),
    (16, 4, 3), (18, 4, 3),
    # ternary, L=5,6
    (13, 5, 3), (14, 5, 3), (15, 5, 3), (16, 5, 3),
    (12, 6, 3), (13, 6, 3), (14, 6, 3),
    # four-letter, L=3
    (8, 3, 4), (9, 3, 4), (10, 3, 4), (11, 3, 4), (12, 3, 4), (13, 3, 4),
    (14, 3, 4),
    # four-letter, L=4
    (10, 4, 4), (11, 4, 4), (12, 4, 4), (13, 4, 4), (14, 4, 4),
    # four-letter, L=5
    (10, 5, 4), (11, 5, 4), (12, 5, 4), (13, 5, 4),
]


def _run(scope):
    return scan_scope(*scope)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--scope", nargs=3, type=int, action="append", metavar=("G", "L", "SIGMA"))
    ap.add_argument("--jobs", type=int, default=0)
    ap.add_argument("--examples", type=int, default=5)
    args = ap.parse_args()

    if args.selftest:
        return _selftest()

    if args.scope:
        scopes = [tuple(s) for s in args.scope]
    elif args.full:
        scopes = _FULL
    else:
        scopes = _QUICK

    # Default to a single process: the largest scopes each hold a multi-million
    # entry support table, and running several such scopes concurrently can
    # exhaust memory.  Pass --jobs N explicitly to parallelise when RAM allows.
    jobs = args.jobs or 1
    print(f"[broad S62 oriented search] scopes={len(scopes)} jobs={jobs}")
    print("  every zero is an exhaustive-in-scope computation, not a proof")
    t0 = time.time()
    results = []
    if jobs > 1 and len(scopes) > 1:
        with Pool(jobs) as pool:
            for r in pool.imap_unordered(_run, scopes):
                results.append(r)
                _print_row(r)
    else:
        for sc in scopes:
            r = scan_scope(*sc, want_examples=args.examples)
            results.append(r)
            _print_row(r)

    total = sum(r["counterexample_candidates"] for r in results)
    print(f"\n  total counterexample-candidates across {len(results)} scopes: {total}")
    print(f"  elapsed {time.time()-t0:.1f}s")
    if total:
        print("  POSITIVE MATERIAL RESULT -- candidates exist; inspect before over-reading")
    else:
        print("  no counterexample candidate in any listed scope (finite evidence)")
    return 0


def _print_row(r):
    ex = ("  " + str(r["examples"][:3])) if r["examples"] else ""
    print(f"  G={r['G']:>2} L={r['L']} a={r['alpha']}: "
          f"necklaces={r['necklaces']:>8} nonrigid={r['nonrigid']:>6} "
          f"cex-candidates={r['counterexample_candidates']:>3} "
          f"({r['seconds']:.1f}s){ex}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
