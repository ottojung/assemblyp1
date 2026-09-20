#!/usr/bin/env python3
"""
Medvedev-Brudno section 6.2 bidirected-flow feasibility of the kernel-checked
fixed-length witnesses (issues #31/#32), and a bounded exhaustive search for a
*sequence-level* section 6.2 counterexample.

Model and criterion
-------------------
Section 6.2 builds a transitively reduced *bidirected* overlap graph whose
vertices are the (double-stranded) reads, lower-bounds every read vertex by 1,
and maximizes the section 6.1 separable binomial objective over flows.  A flow
is a (possibly non-contiguous) assembly; a single circular genome corresponds to
a circuit.  Observation 7 of the source says: the number of times a walk W
visits read r equals the number of times r appears as a submolecule of the
molecule spelled by W.

Consequently a *molecule* D is spelled by a walk in the overlap graph iff every
length-L submolecule of D is an observed read and every observed read occurs in
D; i.e. support equality `supp(spec_L(D)) = supp(R)` (molecule classes, so
reverse complements are identified when a complement is supplied).  This file
uses that criterion at the sequence level and additionally imposes the
per-occurrence lower bound d_D(w) >= x_w.

Search
------
For every I_s- and S-in-F*-satisfying instance (truth S spellable, per-
occurrence lower bound satisfied), enumerate every circular molecule D over the
alphabet with |D| <= maxD and support equal to the observed support, and test
whether the literal section 6.1 binomial (fixed external N = |S|) strictly
prefers D to S.  Exhaustive for the printed scope.  Exits non-zero if any
assertion fails (the recorded scopes assert zero counterexamples).

All arithmetic is exact (fractions.Fraction).  Computational evidence only,
not a proof of absence beyond the stated bounds.
"""
import argparse, sys, time
from itertools import product as iproduct, combinations_with_replacement
from fractions import Fraction
from collections import Counter, defaultdict

# --------------------------------------------------------------------------
# I_s repeat/bridging machinery (transcribed from the repository's
# scripts/support_feasibility_search.py so this script is self-contained)
# --------------------------------------------------------------------------
from itertools import combinations


def covers_all(S, starts, L):
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_repeat_pairs(S):
    G = len(S)
    out, seen_pos = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for kmer, pos in groups.items():
            if len(pos) < 2:
                continue
            for pair in combinations(pos, 2):
                t1, t2 = pair
                if (S[(t1 - 1) % G] != S[(t2 - 1) % G]
                        and S[(t1 + ell) % G] != S[(t2 + ell) % G]):
                    if pair not in seen_pos:
                        seen_pos.add(pair)
                        out.append((ell, pair, kmer))
    return out


def triple_repeats(S):
    G = len(S)
    out, seen = [], set()
    for ell in range(1, G):
        groups = defaultdict(list)
        for i in range(G):
            groups[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for kmer, pos in groups.items():
            if len(pos) < 3:
                continue
            for tri in combinations(pos, 3):
                pre = {S[(t - 1) % G] for t in tri}
                post = {S[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(post) > 1:
                    key = tuple(sorted(tri))
                    if key not in seen:
                        seen.add(key)
                        out.append((ell, key, kmer))
    return out


def interleaved_pairs(S):
    reps = maximal_repeat_pairs(S)
    out, seen = [], set()
    for i in range(len(reps)):
        e1, p1, k1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2, k2 = reps[j]
            four = sorted(set(list(p1) + list(p2)))
            if len(four) != 4:
                continue
            lab = {}
            for p in p1:
                lab[p] = 0
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


def copy_bridged(S, t, ell, starts, L):
    G = len(S)
    for r in starts:
        rp = {(r + o) % G for o in range(L)}
        if (t - 1) % G in rp and (t + ell) % G in rp:
            return True
    return False


def check_I_s(S, starts, L, trips, inter):
    if not covers_all(S, starts, L):
        return False
    for ell, pos, _ in trips:
        for t in pos:
            if not copy_bridged(S, t, ell, starts, L):
                return False
    for (e1, p1), (e2, p2) in inter:
        b1 = any(copy_bridged(S, t, e1, starts, L) for t in p1)
        b2 = any(copy_bridged(S, t, e2, starts, L) for t in p2)
        if not (b1 or b2):
            return False
    return True


def make_comp(sigma):
    c = {}
    for i in range(0, sigma - 1, 2):
        c[i] = i + 1
        c[i + 1] = i
    if sigma % 2:
        c[sigma - 1] = sigma - 1
    return c


def mol(s, comp):
    if comp is None:
        return tuple(s)
    r = tuple(comp[c] for c in reversed(s))
    return min(tuple(s), r)


def spec_mol(seq, L, comp):
    G = len(seq)
    return Counter(mol(tuple(seq[(i + j) % G] for j in range(L)), comp)
                   for i in range(G))


def observed(S, starts, L, comp):
    G = len(S)
    x = Counter()
    for r in starts:
        x[mol(tuple(S[(r + j) % G] for j in range(L)), comp)] += 1
    return x


def literal(vals, alphabet="ABCD"):
    return "".join(alphabet[v] if isinstance(v, int) else v for v in vals)


# --------------------------------------------------------------------------
# Witness obstructions
# --------------------------------------------------------------------------
# (name, truth, competitor, L, realized starts).  B/C/G are the extra alphabet
# symbols of the fixed-length witnesses; the effective alphabet of the truth is
# {A,B} or {A,C}.
WITNESSES = [
    ("issue #31 fixed-length exact AAABB->AAAAB", "AAABB", "AAAAB", 3, [0, 1, 4]),
    ("issue #32 fixed-length binomial AAACC->AAAAC", "AAACC", "AAAAC", 3, [0, 1, 4]),
]


def to_int(s, alphabet="ABCD"):
    return tuple(alphabet.index(c) for c in s)


def report_witness(name, S_str, D_str, L, starts, comp, comp_name,
                   alphabet="ABCD"):
    S_t, D_t = to_int(S_str, alphabet), to_int(D_str, alphabet)
    x = observed(S_t, starts, L, comp)
    dS = spec_mol(S_t, L, comp)
    dD = spec_mol(D_t, L, comp)
    suppx = set(x)
    obsD = sorted(literal(w, alphabet) for w in set(dD) - suppx)
    obsS = sorted(literal(w, alphabet) for w in set(dS) - suppx)
    D_feas = (set(dD) == suppx) and all(dD.get(w, 0) >= c for w, c in x.items())
    S_feas = (set(dS) == suppx) and all(dS.get(w, 0) >= c for w, c in x.items())
    print(f"  [{comp_name}] {name}")
    print(f"    observed support : {sorted(literal(w, alphabet) for w in suppx)}")
    print(f"    spec(D) support  : {sorted(literal(w, alphabet) for w in set(dD))}"
          f"   unobserved windows: {obsD}")
    print(f"    spec(S) support  : {sorted(literal(w, alphabet) for w in set(dS))}"
          f"   unobserved windows: {obsS}")
    print(f"    D sequence-level section 6.2 feasible: {D_feas}")
    print(f"    S sequence-level section 6.2 feasible: {S_feas}")
    return D_feas, S_feas


# --------------------------------------------------------------------------
# Bounded exhaustive search for a sequence-level counterexample
# --------------------------------------------------------------------------
def search(G, L, sigma, N, maxD, comp):
    # The section 6.1 binomial ratio depends only on the candidate's window
    # spectrum, not on the molecule that realizes it, so dedupe by spectrum.
    by_support = defaultdict(dict)
    for m in range(1, maxD + 1):
        for D in iproduct(range(sigma), repeat=m):
            sp = spec_mol(D, L, comp)
            key = tuple(sorted(sp.items()))
            by_support[frozenset(sp)].setdefault(key, sp)

    truths = list(iproduct(range(sigma), repeat=G))
    trips = [triple_repeats(g) for g in truths]
    inter = [interleaved_pairs(g) for g in truths]

    n_inst = 0
    cex = []
    for s_idx, S in enumerate(truths):
        spS = spec_mol(S, L, comp)
        suppS = frozenset(spS)
        Sc = mol(S, comp)
        for starts in combinations_with_replacement(range(G), N):
            if not check_I_s(S, starts, L, trips[s_idx], inter[s_idx]):
                continue
            x = observed(S, starts, L, comp)
            if frozenset(x) != suppS:
                continue
            if any(spS.get(w, 0) < c for w, c in x.items()):
                continue
            n_inst += 1
            n = sum(x.values())
            for key, spD in by_support.get(suppS, {}).items():
                if len(key) == len(spS) and key == tuple(sorted(spS.items())):
                    continue  # same spectrum as the truth: ratio 1
                if any(spD.get(w, 0) < c for w, c in x.items()):
                    continue
                r = Fraction(1)
                bad = False
                for w, xw in x.items():
                    dd, ds = spD.get(w, 0), spS.get(w, 0)
                    if dd > N or ds > N:
                        bad = True
                        break
                    r *= Fraction(dd, N) ** xw * Fraction(N - dd, N) ** (n - xw)
                    r /= Fraction(ds, N) ** xw * Fraction(N - ds, N) ** (n - xw)
                if bad or r <= 1:
                    continue
                cex.append((G, L, sigma, "".join(map(str, S)),
                            dict((str(k), v) for k, v in spD.items()), r))
    cex.sort(key=lambda z: z[5])
    return n_inst, cex


# (G, L, sigma, maxDmult).  Candidate length bounded by maxDmult*G.
SCOPES = [
    (4, 3, 2, 2), (5, 3, 2, 2), (6, 3, 2, 3), (7, 3, 2, 2),
    (8, 3, 2, 2), (6, 4, 2, 3), (7, 4, 2, 2), (8, 4, 2, 2),
    (5, 3, 3, 2), (6, 3, 3, 2), (6, 4, 3, 2),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true",
                    help="run only the smaller scopes")
    a = ap.parse_args()

    print("=" * 78)
    print("Section 6.2 bidirected-flow feasibility of the fixed-length witnesses")
    print("=" * 78)
    both_feas = False
    for name, S, D, L, starts in WITNESSES:
        for comp_name, comp in [("single-strand", None),
                                ("revcomp (A<->B / C<->G)", make_comp(4))]:
            fD, fS = report_witness(name, S, D, L, starts, comp, comp_name)
            both_feas = both_feas or (fD and fS)
    # No kernel-checked witness has BOTH the truth and the competitor as
    # sequence-level section 6.2 molecules.  Under the real double-stranded
    # (revcomp A<->T) reading the #31 truth itself becomes feasible while its
    # competitor does not, so the witness does not transfer to section 6.2.
    assert not both_feas, "a kernel witness had both molecules sequence-feasible"

    print("\n" + "-" * 78)
    print("Copy-vector (flow) projection of the competitor")
    print("-" * 78)
    S, D, L, starts = "AAACC", "AAAAC", 3, [0, 1, 4]
    x = observed(tuple(S), starts, L, None)
    dD = spec_mol(tuple(D), L, None)
    proj = Counter({w: c for w, c in dD.items() if c > 0 and w in x})
    print(f"  S={S} D={D} observed={dict((literal(k), v) for k, v in x.items())}")
    print(f"  D projected onto observed vertices: "
          f"{dict((literal(k), v) for k, v in proj.items())}")
    print("  This projection is realizable by the open walk")
    print("    CAA -> AAA -> AAA -> AAC")
    print("  i.e. a single non-contiguous contig; it is the copy vector of D")
    print("  restricted to observed read vertices.  The molecule D itself is not")
    print("  spellable because its window ACA is unobserved.")

    print("\n" + "-" * 78)
    print("Bounded exhaustive search for a *sequence-level* section 6.2 cex")
    print("(truth AND competitor both spelled; I_s and per-occurrence lower bound)")
    print("-" * 78)
    scopes = SCOPES[:4] if a.quick else SCOPES
    total_inst = 0
    for G, L, sigma, mult in scopes:
        maxD = mult * G
        t0 = time.time()
        n_inst, cex = search(G, L, sigma, G, maxD, None)
        total_inst += n_inst
        print(f"  single-strand G={G} L={L} sigma={sigma} maxD={maxD}: "
              f"instances={n_inst} cex={len(cex)} ({time.time()-t0:.1f}s)")
        assert len(cex) == 0, f"counterexample found: {cex[:3]}"
    for G, L, sigma, mult in scopes:
        maxD = mult * G
        t0 = time.time()
        n_inst, cex = search(G, L, sigma, G, maxD, make_comp(sigma))
        total_inst += n_inst
        print(f"  revcomp        G={G} L={L} sigma={sigma} maxD={maxD}: "
              f"instances={n_inst} cex={len(cex)} ({time.time()-t0:.1f}s)")
        assert len(cex) == 0, f"counterexample found: {cex[:3]}"

    print(f"\n  total instances searched: {total_inst}")
    print("  no sequence-level section 6.2 counterexample in the recorded scope")
    print("\nALL ASSERTIONS PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
