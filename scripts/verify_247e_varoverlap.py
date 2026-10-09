#!/usr/bin/env python3
"""
Independent verification (issue #247, front 247e) of the claimed variable-overlap
bidirected circuit for D = AAAABABB at oMin = 1.

Re-implements, from scratch and independently of every repository script, the
exact objects of AssemblyP1/Section62BidirectedFlow.lean:
  strands / reverse-complement molecule classes and representatives (`rep`),
  `overlapEdges`, the literal `isReducibleB`, the repository
  `isReducibleLongerB`, a Myers spelling-equality reduction, signed incidences
  and `OppositeAtInterior`, vertex `throughput`, and Observation 7.

Exact integers/strings; deterministic; exits non-zero on a failed assertion.
"""

from collections import Counter
from fractions import Fraction

A, B = "A", "B"


def comp(c):
    return B if c == A else A


def rc(w):
    return "".join(comp(c) for c in reversed(w))


def code(w):
    return int("".join("0" if c == A else "1" for c in w), 2)


def rep(w):
    return w if code(w) <= code(rc(w)) else rc(w)


def strands_of(verts):
    return list(verts) + [rc(v) for v in verts]


# ------------------------------------------------------------------- graph
def overlap_edges(verts, readLen, oMin):
    edges = []
    for length in range(readLen):
        if length < oMin:
            continue
        for sx in strands_of(verts):
            for sy in strands_of(verts):
                if sx[len(sx) - length:] == sy[:length]:
                    edges.append(dict(sx=sx, sy=sy, len=length,
                                      sgnX=1 if sx == rep(sx) else -1,
                                      sgnY=-1 if sy == rep(sy) else 1))
    return edges


def max_overlap(a, b, readLen):
    return max([l for l in range(readLen) if a[len(a) - l:] == b[:l]] or [0])


# -------------------------------------------------------------- reductions
def is_reducible_B(e, verts, readLen):
    for m in strands_of(verts):
        for l1 in range(readLen):
            for l2 in range(readLen):
                if (max_overlap(e["sx"], m, readLen) == l1
                        and max_overlap(m, e["sy"], readLen) == l2
                        and 0 < l1 and 0 < l2 and l1 < e["len"] and l2 < e["len"]
                        and l1 + l2 - readLen == e["len"]):
                    return True
    return False


def is_reducible_longer_B(e, verts, readLen):
    for m in strands_of(verts):
        if (max_overlap(e["sx"], m, readLen) > e["len"]
                and max_overlap(m, e["sy"], readLen) > e["len"]):
            return True
    return False


def myers_spelled_reducible(e, verts, readLen):
    """Myers (2005) spelling-equality transitive reduction (single intermediate
    read u): direct string sx + sy[len:]; path sx -> u -> sy with overlaps
    l1 = maxOverlap(sx,u) > len and l2 = maxOverlap(u,sy) > len, placing u at
    offset readLen - l1, must spell the identical string.  Incidence at a single
    intermediate read is automatically opposite (checked in `opposite` below)."""
    direct = e["sx"] + e["sy"][e["len"]:]
    for m in verts:
        for u in (m, rc(m)):
            l1 = max_overlap(e["sx"], u, readLen)
            l2 = max_overlap(u, e["sy"], readLen)
            if l1 <= e["len"] or l2 <= e["len"]:
                continue
            off = readLen - l1
            if off + readLen > len(direct):
                continue
            if direct[off:off + readLen] == u:
                return True, (m, u, l1, l2)
    return False, None


# ------------------------------------------------------------------- walks
def spell_walk(strands, overlaps):
    """Spell the cyclic molecule of a variable-overlap strand walk.
    Appends reads 0..m-2, then verifies the wrap and truncates the final
    overlap.  Returns (spelled, length, wrap_ok)."""
    assert len(strands) == len(overlaps)
    m = len(strands)
    s = strands[0]
    for i in range(m - 1):
        nxt = strands[i + 1]
        ov = overlaps[i]
        assert s[len(s) - ov:] == nxt[:ov], (s, nxt, ov)
        s += nxt[ov:]
    last_ov = overlaps[m - 1]
    wrap_ok = (s[len(s) - last_ov:] == strands[0][:last_ov])
    genome = s[:len(s) - last_ov]
    return genome, len(genome), wrap_ok


def molecule_visits(strands):
    return Counter(rep(x) for x in strands)


def molecule_spectrum(genome, readLen):
    n = len(genome)
    return Counter(rep("".join(genome[(i + j) % n] for j in range(readLen)))
                   for i in range(n))


def oriented_spectrum(genome, readLen):
    n = len(genome)
    return Counter("".join(genome[(i + j) % n] for j in range(readLen))
                   for i in range(n))


def full_walk(genome, readLen):
    n = len(genome)
    strands = ["".join(genome[(i + j) % n] for j in range(readLen)) for i in range(n)]
    return strands, [readLen - 1] * n


def walk_edges(strands, overlaps, graph):
    out = []
    m = len(strands)
    for i in range(m):
        sx, sy, ov = strands[i], strands[(i + 1) % m], overlaps[i]
        match = [e for e in graph if e["sx"] == sx and e["sy"] == sy and e["len"] == ov]
        out.append(match[0] if match else None)
    return out


def opposite_at_interior(edges):
    m = len(edges)
    bad = []
    for i in range(m):
        prev, cur = edges[(i - 1) % m], edges[i]
        if cur is None or prev is None or cur["sgnX"] != -prev["sgnY"]:
            bad.append(i)
    return not bad, bad


def walk_flow(edges):
    """Flow = multiset of traversals of each distinct edge."""
    f = Counter()
    for e in edges:
        f[(e["sx"], e["sy"], e["len"])] += 1
    return f


def balance(f, graph, verts):
    """MB09 §3.4 signed-incidence balance at each molecule, per the Lean
    `balCore` with rep applied to each endpoint."""
    bal = {v: 0 for v in verts}
    for e in graph:
        n = f.get((e["sx"], e["sy"], e["len"]), 0)
        if n:
            vx, vy = rep(e["sx"]), rep(e["sy"])
            bal[vx] = bal.get(vx, 0) + n * e["sgnX"]
            bal[vy] = bal.get(vy, 0) + n * e["sgnY"]
    return bal


def throughput(f, graph, verts):
    th = {v: 0 for v in verts}
    for e in graph:
        n = f.get((e["sx"], e["sy"], e["len"]), 0)
        if n:
            vx = rep(e["sx"])
            th[vx] = th.get(vx, 0) + n
    return th


# ---------------------------------------------------------------- likelihood
def exact_multinomial_ratio(dS, dD):
    from math import factorial
    def prod_fact(d):
        p = 1
        for v in d.values():
            p *= factorial(v)
        return p
    return Fraction(prod_fact(dS), prod_fact(dD))


def fixed_N_binomial_ratio(dS, dD, x, N):
    r = Fraction(1)
    for c in set(dS) | set(dD) | set(x):
        ds, dd, xx = dS.get(c, 0), dD.get(c, 0), x.get(c, 0)
        def f(d):
            if d == 0:
                return Fraction(1) if xx == 0 else Fraction(0)
            return (Fraction(d, N) ** xx) * (Fraction(N - d, N) ** (12 - xx))
        if f(ds) == 0:
            continue
        r *= f(dd) / f(ds)
    return r


# ========================================================================
def main():
    L, readLen = 3, 3
    truth, comp_genome = "AAABBABB", "AAAABABB"
    starts = list(range(8)) + [0, 0, 0, 0]

    def windows(g, r):
        n = len(g)
        return "".join(g[(r + j) % n] for j in range(L))

    obs_list = [windows(truth, r) for r in starts]
    obs_oriented = Counter(obs_list)
    obs_reps = sorted(set(rep(w) for w in obs_list))
    obs_molecules = Counter(rep(w) for w in obs_list)
    print("oriented observed x :", dict(sorted(obs_oriented.items())))
    print("molecule reps       :", obs_reps)
    print("molecule observed x :", dict(sorted(obs_molecules.items())), " n =", sum(obs_molecules.values()))

    # ---- molecule-model graph at oMin = 1
    verts = obs_reps
    graph = overlap_edges(verts, readLen, 1)
    graph2 = overlap_edges(verts, readLen, 2)
    print(f"\nmolecule graph oMin=1 : {len(graph)} edges ; oMin=2 : {len(graph2)} edges")

    # ---- D full-overlap walk (genuine §6.2 circuit)
    print("\n### D =", comp_genome, "full-overlap (L-1) window walk")
    ws, wo = full_walk(comp_genome, readLen)
    gD, lD, wrapD = spell_walk(ws, wo)
    eD = walk_edges(ws, wo, graph)
    okD, badD = opposite_at_interior(eD)
    print("strands    :", ws)
    print("spelled    :", gD, "length", lD, "wrap", wrapD)
    print("visits     :", dict(sorted(molecule_visits(ws).items())))
    print("spectrum   :", dict(sorted(molecule_spectrum(comp_genome, L).items())))
    print("Obs7 visits==spectrum :", molecule_visits(ws) == molecule_spectrum(comp_genome, L))
    print("all steps present     :", all(e is not None for e in eD))
    print("bidirected circuit    :", okD, "bad idx", badD)
    fD = walk_flow(eD)
    print("flow balance (mol)    :", balance(fD, graph, verts))
    print("flow throughput (mol) :", throughput(fD, graph, verts))

    # ---- S full-overlap walk
    print("\n### S =", truth, "full-overlap (L-1) window walk")
    wsS, woS = full_walk(truth, readLen)
    gS, lS, wrapS = spell_walk(wsS, woS)
    eS = walk_edges(wsS, woS, graph)
    okS, badS = opposite_at_interior(eS)
    print("visits     :", dict(sorted(molecule_visits(wsS).items())))
    print("spectrum   :", dict(sorted(molecule_spectrum(truth, L).items())))
    print("Obs7       :", molecule_visits(wsS) == molecule_spectrum(truth, L),
          "| circuit", okS, "| steps present", all(e is not None for e in eS))

    # ---- the board's variable-overlap walk
    print("\n### board variable-overlap walk (oMin=1)")
    vw = ["AAA", "AAA", "AAB", "BAB", "ABB", "BBA", "BAA"]
    vo = [2, 2, 1, 2, 2, 2, 2]
    gV, lV, wrapV = spell_walk(vw, vo)
    eV = walk_edges(vw, vo, graph)
    okV, badV = opposite_at_interior(eV)
    print("strands    :", vw)
    print("overlaps   :", vo)
    print("spelled    :", gV, "length", lV, "wrap", wrapV, "== D:", gV == comp_genome)
    print("sum(L-ov)  :", sum(L - o for o in vo))
    print("visits     :", dict(sorted(molecule_visits(vw).items())))
    print("spectrum   :", dict(sorted(molecule_spectrum(comp_genome, L).items())))
    print("Obs7 visits==spectrum :", molecule_visits(vw) == molecule_spectrum(comp_genome, L))
    print("all steps present     :", all(e is not None for e in eV))
    print("bidirected circuit    :", okV, "bad idx", badV)

    print("\nper-step reduction of the board walk (molecule graph):")
    for i in range(len(vw)):
        e = eV[i]
        if e is None:
            print(f"  step {i}: {vw[i]}->{vw[(i+1)%len(vw)]} ov={vo[i]} ABSENT")
            continue
        lit = is_reducible_B(e, verts, readLen)
        lng = is_reducible_longer_B(e, verts, readLen)
        my, wit = myers_spelled_reducible(e, verts, readLen)
        print(f"  step {i}: {e['sx']:>3}->{e['sy']:<3} ov={e['len']} "
              f"isReducibleB={lit} isReducibleLongerB={lng} myers_spelled={my} wit={wit}")

    # ---- likelihood, both models
    dS_mol = molecule_spectrum(truth, L)
    dD_mol = molecule_spectrum(comp_genome, L)
    x_mol = obs_molecules
    dS_or = oriented_spectrum(truth, L)
    dD_or = oriented_spectrum(comp_genome, L)
    x_or = obs_oriented
    print("\n### likelihood")
    print("molecule: exact multinomial L(D)/L(S) =", exact_multinomial_ratio(dS_mol, dD_mol))
    print("molecule: fixed-N=8 binomial L(D)/L(S) =", fixed_N_binomial_ratio(dS_mol, dD_mol, x_mol, 8))
    print("oriented: exact multinomial L(D)/L(S) =", exact_multinomial_ratio(dS_or, dD_or))
    print("oriented: fixed-N=8 binomial L(D)/L(S) =", fixed_N_binomial_ratio(dS_or, dD_or, x_or, 8))

    # ---- verdict assertions
    print("\n### verdict")
    assert gV == comp_genome and lV == 8 and wrapV
    assert molecule_visits(ws) == molecule_spectrum(comp_genome, L)      # D genuine via full walk
    assert molecule_visits(vw) != molecule_spectrum(comp_genome, L)      # board walk fails Obs7
    assert not is_reducible_B(eV[2], verts, readLen)                    # literal reduction vacuous
    assert is_reducible_longer_B(eV[2], verts, readLen)                 # repo alt reduction removes it
    assert myers_spelled_reducible(eV[2], verts, readLen)[0]            # Myers spelling removes it
    print("REFUTED: board variable-overlap walk is not a genuine §6.2 flow for D")
    print("  - molecule throughput", dict(sorted(molecule_visits(vw).items())),
          "!= D spectrum", dict(sorted(molecule_spectrum(comp_genome, L).items())))
    print("  - overlap-1 edge AAB->BAB is Myers-spelled-reducible via observed molecule ABA = rc(BAB)")
    print("CONFIRMED: D is a genuine §6.2 molecule candidate via the full-overlap window walk")
    print("\nALL ASSERTIONS PASS")


if __name__ == "__main__":
    main()
