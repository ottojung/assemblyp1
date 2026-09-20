#!/usr/bin/env python3
"""Adversarial, from-scratch source-fidelity audit of the same-length witness

    truth  S = AAATAT      competitor  D = AAAAAT      L = 3
    realized starts (0, 0, 1, 3, 5)        N = |S| = 6, n = 5 reads

against the *exact* Shomorony (2016) / Bresler et al. (2013) model that defines
the bridging hypotheses I_s.

Everything is recomputed here with no repository imports.  The script exits
non-zero if any assertion fails.

Load-bearing result
-------------------
The instance satisfies the exact I_s hypotheses (coverage; every maximal triple
repeat all-bridged; every interleaved pair bridged).  So the witness does NOT
fail on the bridging side.  It fails on the read-type side: the competitor only
beats the truth after collapsing reverse complements into Medvedev-Brudno
k-molecule classes.  Under the *oriented* length-L read types of the very model
that defines I_s (Shomorony 2016 sec.2; Bresler 2013 shotgun model), the
observed oriented read TAT is not a substring of D = AAAAAT, so D cannot have
generated the data and its likelihood is 0.  The witness is therefore a
cross-source panel (Shomorony/Bresler placement-based I_s grafted onto an MB09
reverse-complement molecule likelihood), not a counterexample in the model that
poses the open question.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations

A, T = 0, 1
BASE = "AT"
COMP = {A: T, T: A}

S = (A, A, A, T, A, T)          # AAATAT
D = (A, A, A, A, A, T)          # AAAAAT
L = 3
STARTS = (0, 0, 1, 3, 5)


def word(seq):
    return "".join(BASE[c] for c in seq)


def rc(seq):
    return tuple(COMP[c] for c in reversed(seq))


def mol(seq):
    return min(tuple(seq), rc(tuple(seq)))


def windows(seq):
    G = len(seq)
    return [tuple(seq[(i + j) % G] for j in range(L)) for i in range(G)]


# --------------------------------------------------------------------------
# Bresler 2013 repeat / bridging definitions (verbatim, primary source)
# --------------------------------------------------------------------------
def maximal_repeats(seq):
    """All maximal repeats: pairs (a,b) of equal length-ell windows with
    s(a-1)!=s(b-1) and s(a+ell)!=s(b+ell)."""
    G = len(seq)
    out = []
    for ell in range(1, G):
        grp = {}
        for i in range(G):
            grp.setdefault(tuple(seq[(i + j) % G] for j in range(ell)), []).append(i)
        for pos in grp.values():
            for a, b in combinations(pos, 2):
                if (seq[(a - 1) % G] != seq[(b - 1) % G]
                        and seq[(a + ell) % G] != seq[(b + ell) % G]):
                    out.append((ell, (a, b)))
    return out


def triple_repeats(seq):
    """All maximal triple repeats: triples of equal windows with the preceding
    symbols not all equal and the following symbols not all equal."""
    G = len(seq)
    out = []
    for ell in range(1, G):
        grp = {}
        for i in range(G):
            grp.setdefault(tuple(seq[(i + j) % G] for j in range(ell)), []).append(i)
        for pos in grp.values():
            for tri in combinations(pos, 3):
                pre = {seq[(t - 1) % G] for t in tri}
                nxt = {seq[(t + ell) % G] for t in tri}
                if len(pre) > 1 and len(nxt) > 1:
                    out.append((ell, tuple(sorted(tri))))
    return out


def interleaved_pairs(seq):
    """Pairs of maximal repeats whose four selected starts alternate cyclically
    (equiv. to Bresler's t1<t2<t3<t4 / t2<t1<t4<t3 after a suitable cut)."""
    reps = maximal_repeats(seq)
    out = []
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
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridging_reads(seq, t, ell, reads):
    """Reads that bridge copy [t, t+ell): the read covers at least one base on
    both sides, i.e. it covers (t-1) and (t+ell)."""
    G = len(seq)
    wit = []
    for r, w in reads:
        cov = {(r + o) % G for o in range(len(w))}
        if (t - 1) % G in cov and (t + ell) % G in cov:
            wit.append(r)
    return wit


def I_s(seq, reads):
    G = len(seq)
    cov = set()
    for r, w in reads:
        cov |= {(r + o) % G for o in range(len(w))}
    coverage = len(cov) == G
    tri_details, tri_ok = [], True
    for ell, tri in triple_repeats(seq):
        row = (ell, tri, [copy_bridging_reads(seq, t, ell, reads) for t in tri])
        tri_details.append(row)
        tri_ok &= all(wit for _, _, wits in [row] for wit in wits)
    int_details, int_ok = [], True
    for (e1, p1), (e2, p2) in interleaved_pairs(seq):
        b1 = {t: copy_bridging_reads(seq, t, e1, reads) for t in p1}
        b2 = {t: copy_bridging_reads(seq, t, e2, reads) for t in p2}
        int_details.append(((e1, p1), b1, (e2, p2), b2))
        int_ok &= (any(b1.values()) or any(b2.values()))
    return dict(coverage=coverage, tri=tri_details, tri_ok=tri_ok,
                inter=int_details, int_ok=int_ok,
                holds=coverage and tri_ok and int_ok)


# --------------------------------------------------------------------------
# spectra / objectives
# --------------------------------------------------------------------------
def key_of(w, collapse):
    return mol(w) if collapse else tuple(w)


def spectrum(seq, collapse):
    return Counter(key_of(w, collapse) for w in windows(seq))


def observed(reads, collapse):
    return Counter(key_of(w, collapse) for _, w in reads)


def exact_same_length_ratio(x, dS, dD):
    """prod_c (d_D(c)/d_S(c))^{x_c}; None if the truth cannot generate a read,
    Fraction(0) if the competitor cannot."""
    num = den = Fraction(1)
    for c, xc in x.items():
        if dS.get(c, 0) == 0:
            return None
        if dD.get(c, 0) == 0:
            return Fraction(0)
        num *= Fraction(dD[c]) ** xc
        den *= Fraction(dS[c]) ** xc
    return num / den


def fmt(counter):
    return "{" + ", ".join(f"{word(c)}:{n}" for c, n in sorted(counter.items())) + "}"


def main():
    reads = [(r, tuple(S[(r + j) % len(S)] for j in range(L))) for r in STARTS]
    ok = True

    def check(name, cond):
        nonlocal ok
        print(f"[{'PASS' if cond else 'FAIL'}] {name}")
        ok &= bool(cond)

    print(f"truth S = {word(S)}   competitor D = {word(D)}   L = {L}")
    print("read placements:", [(r, word(w)) for r, w in reads])
    print()

    print("== Bresler I_s on the single-strand truth ==")
    facts = I_s(S, reads)
    print("coverage:", facts["coverage"])
    for ell, tri, wits in facts["tri"]:
        print(f"  maximal triple repeat ell={ell} @ {tri}: bridging reads per copy {wits}")
    for (e1, p1), b1, (e2, p2), b2 in facts["inter"]:
        print(f"  interleaved pair ell={e1}@{p1} vs ell={e2}@{p2}: "
              f"copies {b1} / {b2}")
    check("I_s coverage", facts["coverage"])
    check("I_s every maximal triple repeat all-bridged", facts["tri_ok"])
    check("I_s every interleaved pair bridged", facts["int_ok"])
    check("I_s holds", facts["holds"])

    print()
    print("== read-type spaces ==")
    xo, dSo, dDo = observed(reads, False), spectrum(S, False), spectrum(D, False)
    xm, dSm, dDm = observed(reads, True), spectrum(S, True), spectrum(D, True)
    print("oriented   x  =", fmt(xo))
    print("oriented   d_S=", fmt(dSo))
    print("oriented   d_D=", fmt(dDo))
    ro = exact_same_length_ratio(xo, dSo, dDo)
    print("oriented   same-length exact-multinomial ratio L(D)/L(S) =", ro)
    print("molecule   x  =", fmt(xm))
    print("molecule   d_S=", fmt(dSm))
    print("molecule   d_D=", fmt(dDm))
    rm = exact_same_length_ratio(xm, dSm, dDm)
    print("molecule   same-length exact-multinomial ratio L(D)/L(S) =", rm)

    t = tuple(S[(3 + j) % len(S)] for j in range(L))
    check("observed oriented read TAT is produced by S", xo.get(t, 0) == 1)
    check("TAT is absent from the oriented spectrum of D", dDo.get(t, 0) == 0)
    check("oriented competitor likelihood is 0 (witness not valid in source model)",
          ro == 0)
    check("molecule ratio = 3 (the panel-only mechanism)", rm == 3)
    check("molecule collapse needs TAT~ATA: d_S(ATA)=3",
          dSm.get(mol(t), 0) == 3)

    print()
    print("== source-fidelity verdict ==")
    print("I_s holds, so the bridging hypotheses are met.")
    print("But the only winning competitor requires revcomp collapse, which is")
    print("NOT a Shomorony/Bresler read type; under the oriented source read")
    print("types the competitor has likelihood 0. The witness is a cross-source")
    print("panel, not a counterexample in the model that poses the question.")
    print()
    print("ALL AUDIT CHECKS PASS" if ok else "AUDIT CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
