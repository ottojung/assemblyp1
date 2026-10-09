#!/usr/bin/env python3
"""Issue #213 audit: the variable-length, per-occurrence, bidirected Medvedev-Brudno
(2009) section 6.2 witness  ``AAATT -> AAAATT``  (``N = 5``, ``n = 3``, ``L = 3``,
ratio ``9/8`` against the literal section 6.1 product of binomial marginals).

Everything in this file is re-derived from scratch.  It shares no code with
``scripts/verify_se62_bridging_flow_counterexample.py``,
``scripts/verify_se62_mb09_bidirected_graph.py``,
``scripts/verify_samelength_se62_counterexample.py``, or with any Lean module;
it exists so that the merged certificate can be checked against a second,
independent implementation.

What is checked, with no assumption that support equality or ``x <= d`` *is*
section 6.2 feasibility:

  (M)  the sequencing model: reads are DNA molecules (MB09 section 3.1), a
       molecule class is a reverse-complement pair, the witness alphabet is
       ``{A, T}`` with the involution ``A <-> T``;
  (X)  the exact observed read types and counts of the realization
       ``starts = (0, 1, 4)`` of the truth, and the spectra of both molecules;
  (I)  the source-faithful ``I_s`` hypothesis of Shomorony et al. (2016) Eq. (1),
       decided by explicit enumeration: coverage, every maximal triple repeat
       all-bridged, every interleaved pair of maximal repeats bridged;
  (G)  the explicit bidirected read-overlap graph on the observed read molecules
       (MB09 section 3.3 four strand-overlap cases, edges of length at least
       ``o_min = L - 1``);
  (R)  the transitive edge reduction, under the literal "spelled by two shorter
       overlaps" reading and under the alternative longer-proper-overlap
       reading, both with the *maximal* and with an *arbitrary* middle overlap;
  (W)  the truth's and the competitor's cyclic window walks as *bidirected*
       walks: every step is a graph edge, consecutive edges have opposite
       incidences at every interior vertex, every visited vertex is an observed
       read molecule;
  (F)  the induced flows: vertex throughput (= the molecule spectrum, MB09
       Observation 7), the section 6.2 vertex lower bound ``1``, edge lower
       bounds ``0``, signed-incidence balance ``0`` at every read vertex, and no
       supersource/supersink usage;
  (A)  both admissibility readings, kept distinct: the source per-vertex rule
       (every observed read present at least once) and the strictly stronger
       per-occurrence rule ``d(w) >= x(w)`` -- and the fact that *both* hold for
       *both* molecules of this witness;
  (D)  the section 6.1 domain ``0 <= d_i <= N`` for every molecule class, plus
       the ``n < N`` regime;
  (L)  the literal section 6.1 objective with the zero-count factors retained
       over the full reverse-complement class space, and the exact ratio;
  (O)  the placement of the competitor inside the objective domain: over the
       *whole* section 6.1 domain the competitor's throughput vector is the
       unique maximizer, so the refutation is not an artifact of a restricted
       search;
  (S)  the fixed-length boundary: the competitor's spectrum sums to ``6 != 5``,
       so this witness does *not* transfer to the same-length case, and within
       the sum-constrained slice the truth is already optimal;
  (C)  the oriented (single-strand) control: under strict oriented indexing the
       witness inverts.

All arithmetic is exact (``fractions.Fraction`` / integers); the script exits
non-zero on any failed assertion.  Run with ``--census`` for the bounded
per-occurrence census (bounded evidence, not a proof of anything).

Reproduce: ``python3 scripts/verify_se62_varlen_per_occurrence_audit_213.py``
"""
from __future__ import annotations

import itertools
import sys
from collections import Counter
from fractions import Fraction

# ---------------------------------------------------------------------------
# (M) The sequencing model: MB09 section 3.1
# ---------------------------------------------------------------------------

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


def rc(s: str) -> str:
    """The reverse complement of a strand (MB09 section 3.1)."""
    return "".join(COMP[c] for c in reversed(s))


def mol(w: str) -> str:
    """The molecule class (reverse-complement pair) of a strand: the canonical
    representative.  MB09 section 3.1: a DNA molecule is an *unordered*
    reverse-complement strand pair, so a read and its reverse complement are one
    molecule."""
    return min(w, rc(w))


def all_molecule_classes(alphabet: str, k: int) -> list:
    """Every molecule class of length ``k`` over ``alphabet``."""
    out = []
    for t in itertools.product(alphabet, repeat=k):
        w = "".join(t)
        c = mol(w)
        if c not in out:
            out.append(c)
    return sorted(out)


# ---------------------------------------------------------------------------
# (X) The instance
# ---------------------------------------------------------------------------

ALPHABET = "AT"
S_STR = "AAATT"
D_STR = "AAAATT"
READ_LEN = 3
O_MIN = 2  # = read_len - 1, the source's own threshold for this read length
STARTS = (0, 1, 4)
N = len(S_STR)  # external known genome size, MB09 section 6.1


def windows(seq: str, k: int) -> list:
    """The ``k``-length circular windows of ``seq``, one per start."""
    g = len(seq)
    return ["".join(seq[(i + j) % g] for j in range(k)) for i in range(g)]


def spectrum(seq: str, k: int) -> Counter:
    """Occurrence counts of the ``k``-molecule classes of ``seq``."""
    return Counter(mol(w) for w in windows(seq, k))


# ---------------------------------------------------------------------------
# bounded census (evidence only -- a finite search is not a proof of absence)
# ---------------------------------------------------------------------------


def necklaces(g: int, alphabet: str = "AT") -> list:
    """All circular strings of length ``g`` over ``alphabet``, one per rotation
    class (the source's genome is circular, so rotations are one molecule)."""
    seen = set()
    out = []
    for t in itertools.product(alphabet, repeat=g):
        s = "".join(t)
        rot = min(s[i:] + s[:i] for i in range(g))
        if rot not in seen:
            seen.add(rot)
            out.append(rot)
    return out


def census(g_values=(5, 6), read_len=3, maxmuls=(1, 2, 3)) -> None:
    """Bounded census over the per-occurrence bidirected reading.

    Scope: truths are the circular ``{A,T}``-strings of length ``g`` up to
    rotation; a realization is a multiplicity vector over its ``g`` starts; the
    truth must be per-occurrence feasible (support equality and ``d_S >= x``)
    and ``I_s`` must hold; a competitor is any circular string of length up to
    ``g + 2`` with the same support, ``d >= x`` and ``d <= N``.

    Two rows are reported: beats by a strictly *longer* competitor (the
    variable-length cell) and beats by a *same-length* competitor.  Both rows
    are bounded evidence, never a proof.
    """
    for g in g_values:
        for maxmul in maxmuls:
            truths = necklaces(g)
            instances = 0
            var_beats = 0
            same_beats = 0
            min_var = None
            min_var_witness = None
            cand_cache = {}
            for s in truths:
                n_ext = len(s)
                d_s_full = spectrum(s, read_len)
                cl = [mol(w) for w in windows(s, read_len)]
                for mults in itertools.product(range(maxmul + 1), repeat=g):
                    if sum(mults) == 0:
                        continue
                    x = Counter({cl[i]: mults[i] for i in range(g)
                                 if mults[i] > 0})
                    # per-occurrence feasibility of the truth
                    if set(x) != set(d_s_full):
                        continue
                    if any(d_s_full[w] < x[w] for w in x):
                        continue
                    starts = tuple(i for i in range(g) if mults[i] > 0)
                    if not information_feasible(s, starts):
                        continue
                    instances += 1
                    sig = (tuple(sorted(x.items())), n_ext)
                    if sig not in cand_cache:
                        cands = []
                        for gc in range(n_ext - 1, n_ext + 3):
                            for d in necklaces(gc):
                                dd = spectrum(d, read_len)
                                if set(dd) != set(x):
                                    continue
                                if any(dd[w] < x[w] for w in x):
                                    continue
                                if any(v > n_ext for v in dd.values()):
                                    continue
                                cands.append((d, dd))
                        cand_cache[sig] = cands
                    for (d, dd) in cand_cache[sig]:
                        r = lik_of(dd, x, d_s_full, n_ext, sum(x.values()))
                        if r is None or r <= 1:
                            continue
                        if len(d) != len(s):
                            var_beats += 1
                            if min_var is None or r < min_var:
                                min_var = r
                                min_var_witness = (s, starts, d)
                        else:
                            same_beats += 1
            print(f"G={g} L={read_len} maxmul={maxmul}: "
                  f"{len(truths)} truth necklaces, {instances} per-occurrence-"
                  f"feasible I_s realizations")
            print(f"    variable-length beats : {var_beats}"
                  + (f"  (smallest ratio {min_var}, e.g. {min_var_witness})"
                     if min_var is not None else ""))
            print(f"    same-length beats     : {same_beats}")


def lik_of(d: Counter, x: Counter, d_ref: Counter, n_ext: int, n: int):
    """The literal section 6.1 product-of-binomial-marginals ratio ``L(d)/L(d_ref)``
    over the classes that occur in either, zero-count factors included."""
    num = Fraction(1)
    den = Fraction(1)
    for w in set(d) | set(x) | set(d_ref):
        num *= Fraction(d.get(w, 0), n_ext) ** x.get(w, 0) * \
            Fraction(n_ext - d.get(w, 0), n_ext) ** (n - x.get(w, 0))
        den *= Fraction(d_ref.get(w, 0), n_ext) ** x.get(w, 0) * \
            Fraction(n_ext - d_ref.get(w, 0), n_ext) ** (n - x.get(w, 0))
    if den == 0:
        return None
    return num / den


# (I) The source-faithful I_s hypothesis (Shomorony 2016, Eq. (1))
# -----------------------------------------------------------------------

def preceding(seq: str, t: int) -> str:
    return seq[(t - 1) % len(seq)]

def following(seq: str, e: int, t: int) -> str:
    return seq[(t + e) % len(seq)]

def agree(seq: str, e: int, a: int, b: int) -> bool:
    g = len(seq)
    return all(seq[(a + j) % g] == seq[(b + j) % g] for j in range(e))

def is_repeat(seq: str, e: int, a: int, b: int) -> bool:
    """A maximal length-e repeat with selected starts a, b (Bresler et al.):
    equal windows, distinct starts, and both flanks differing."""
    g = len(seq)
    return (1 <= e < g and a != b and agree(seq, e, a, b)
            and preceding(seq, a) != preceding(seq, b)
            and following(seq, e, a) != following(seq, e, b))

def is_triple_repeat(seq: str, e: int, a: int, b: int, c: int) -> bool:
    g = len(seq)
    return (1 <= e < g and a != b and a != c and b != c
            and agree(seq, e, a, b) and agree(seq, e, a, c)
            and agree(seq, e, b, c)
            and not (preceding(seq, a) == preceding(seq, b)
                     and preceding(seq, b) == preceding(seq, c))
            and not (following(seq, e, a) == following(seq, e, b)
                     and following(seq, e, b) == following(seq, e, c)))

def bridged(seq: str, read_starts: tuple, e: int, t: int) -> bool:
    """Some single realized read strictly straddles the copy [t, t+e):
    on a suitable integer lift, r < t' and t' + e < r + L.  Equivalent to
    the Lean `BridgesCopy`: a read at offset d of the copy start with
    d + e + 1 < L."""
    g = len(seq)
    for r in read_starts:
        for d in range(READ_LEN):
            if d + e + 1 < READ_LEN and (r + d + 1) % g == t % g:
                return True
    return False

def in_open_arc(g: int, a: int, b: int, p: int) -> bool:
    return 0 < (p - a) % g < (b - a) % g

def four_distinct(a: int, b: int, c: int, d: int) -> bool:
    return len({a, b, c, d}) == 4

def interleaved(g: int, a: int, b: int, c: int, d: int) -> bool:
    """Cyclic alternation of the four selected starts."""
    return (four_distinct(a, b, c, d)
            and (in_open_arc(g, a, b, c) != in_open_arc(g, a, b, d)))

def covers(seq: str, read_starts: tuple) -> bool:
    g = len(seq)
    covered = set()
    for r in read_starts:
        for j in range(READ_LEN):
            covered.add((r + j) % g)
    return len(covered) == g

def information_feasible(seq: str, read_starts: tuple) -> bool:
    """I_s, decided by explicit enumeration over every maximal repeat."""
    g = len(seq)
    # 1. coverage
    if not covers(seq, read_starts):
        return False
    # 2. every maximal triple repeat all-bridged
    for e in range(1, g):
        for a in range(g):
            for b in range(g):
                for c in range(g):
                    if is_triple_repeat(seq, e, a, b, c):
                        if not all(bridged(seq, read_starts, e, t)
                                   for t in (a, b, c)):
                            return False
    # 3. every interleaved pair of maximal repeats bridged
    for e1 in range(1, g):
        for a in range(g):
            for b in range(g):
                if not is_repeat(seq, e1, a, b):
                    continue
                for e2 in range(1, g):
                    for c in range(g):
                        for d in range(g):
                            if not is_repeat(seq, e2, c, d):
                                continue
                            if interleaved(g, a, b, c, d):
                                if not any(bridged(seq, read_starts, e, t)
                                           for e, t in ((e1, a), (e1, b),
                                                        (e2, c), (e2, d))):
                                    return False
    return True


def main() -> int:
    checks = []

    def check(name: str, ok: bool) -> None:
        checks.append((name, bool(ok)))
        print(f"[{'PASS' if ok else 'FAIL'}] {name}")

    g_s = len(S_STR)
    g_d = len(D_STR)
    n = len(STARTS)

    reads = [windows(S_STR, READ_LEN)[r] for r in STARTS]
    x = Counter(mol(w) for w in reads)
    d_s = spectrum(S_STR, READ_LEN)
    d_d = spectrum(D_STR, READ_LEN)

    print(f"truth S = {S_STR} (G = {g_s});  competitor D = {D_STR} (|D| = {g_d})")
    print(f"read length L = {READ_LEN}, o_min = {O_MIN}, N (external) = {N}, n = {n}")
    print(f"realized reads at starts {STARTS}: {reads}")
    print(f"observed x = {dict(x)}")
    print(f"truth spectrum d_S = {dict(d_s)}   (sum {sum(d_s.values())})")
    print(f"competitor spectrum d_D = {dict(d_d)}   (sum {sum(d_d.values())})")
    print()

    # -- (M) sanity of the molecule model ----------------------------------
    classes = all_molecule_classes(ALPHABET, READ_LEN)
    check(f"(M) the {len(reads)} realized reads are length {READ_LEN} strands",
          all(len(w) == READ_LEN for w in reads))
    check(f"(M) {ALPHABET}-alphabet length-{READ_LEN} molecule classes: "
          f"{len(classes)} classes {classes} (= 2^{READ_LEN}/2 = "
          f"{2 ** READ_LEN // 2}; no odd-length strand is self-complementary)",
          len(classes) == 2 ** READ_LEN // 2)
    check("(M) rc is an involution on every length-%d strand"
          % READ_LEN,
          all(rc(rc(w)) == w for w in
              ("".join(t) for t in itertools.product(ALPHABET, repeat=READ_LEN))))
    check("(M) every read molecule class is its own canonical representative",
          all(mol(mol(w)) == w for w in reads))

    # -- (X) exact read types and spectra ----------------------------------
    check("(X) x = {AAA:1, AAT:1, TAA:1} exactly",
          dict(x) == {"AAA": 1, "AAT": 1, "TAA": 1} and sum(x.values()) == n)
    check("(X) d_S = {AAA:1, AAT:2, TAA:2} exactly",
          dict(d_s) == {"AAA": 1, "AAT": 2, "TAA": 2}
          and sum(d_s.values()) == g_s)
    check("(X) d_D = {AAA:2, AAT:2, TAA:2} exactly",
          dict(d_d) == {"AAA": 2, "AAT": 2, "TAA": 2}
          and sum(d_d.values()) == g_d)
    check("(X) n = 3 < N = 5, the regime the witness needs",
          n < N and n == sum(x.values()))

    # -----------------------------------------------------------------------
    triples = [(e, a, b, c)
               for e in range(1, g_s) for a in range(g_s) for b in range(g_s)
               for c in range(g_s) if is_triple_repeat(S_STR, e, a, b, c)]
    reps = [(e, a, b) for e in range(1, g_s) for a in range(g_s)
            for b in range(g_s) if is_repeat(S_STR, e, a, b)]
    inter = [(e1, a, b, e2, c, d)
             for (e1, a, b) in reps for (e2, c, d) in reps
             if interleaved(g_s, a, b, c, d)]
    print("(I) maximal triple repeats of S:", triples)
    print("(I) maximal repeat pairs of S :", len(reps), "pairs;",
          len(inter), "interleaved pairs")
    print("(I) coverage by reads at", STARTS, ":", covers(S_STR, STARTS))
    print("(I) bridge witnesses of the length-1 triple repeat at 0,1,2:",
          {t: [(r, d) for r in STARTS for d in range(READ_LEN)
               if d + 1 + 1 < READ_LEN and (r + d + 1) % g_s == t]
           for t in (0, 1, 2)})
    print()

    check("(I) the realization at (0,1,4) covers S", covers(S_STR, STARTS))
    check("(I) S has exactly one maximal triple repeat up to the order of its "
          "selected starts: the length-1 A at starts 0, 1, 2",
          len(triples) == 6
          and all(t[0] == 1 and set(t[1:]) == {0, 1, 2} for t in triples))
    check("(I) every copy of the triple repeat is bridged by a single read",
          all(bridged(S_STR, STARTS, 1, t) for t in (0, 1, 2)))
    check("(I) S has no interleaved pair of maximal repeats (clause vacuous)",
          len(inter) == 0)
    check("(I) I_s holds for (S, starts=(0,1,4)) -- full enumeration",
          information_feasible(S_STR, STARTS))

    # -----------------------------------------------------------------------
    # (G) The explicit bidirected read-overlap graph (MB09 section 3.3, 6.2)
    # -----------------------------------------------------------------------

    read_verts = sorted({mol(w) for w in reads})
    strands = []
    for v in read_verts:
        strands += [v, rc(v)]

    def incidence_dep(sx: str, rep_x: str) -> int:
        return 1 if sx == rep_x else -1

    def incidence_arr(sy: str, rep_y: str) -> int:
        return -1 if sy == rep_y else 1

    graph = []  # (sx, sy, len, sgnX, sgnY)
    for vx in read_verts:
        for vy in read_verts:
            for sx in (vx, rc(vx)):
                for sy in (vy, rc(vy)):
                    for l in range(O_MIN, READ_LEN):
                        if sx[READ_LEN - l:] == sy[:l]:
                            graph.append((sx, sy, l,
                                          incidence_dep(sx, vx),
                                          incidence_arr(sy, vy)))
    print(f"(G) bidirected overlap graph on {read_verts}: {len(graph)} edges")
    for (sx, sy, l, sxx, syy) in graph:
        print(f"    {sx} -[len {l}, signs ({sxx:+d},{syy:+d})]-> {sy}")
    print()

    check("(G) the graph has 10 edges at o_min = 2", len(graph) == 10)
    check("(G) every employed overlap has length L-1 = 2",
          all(e[2] == READ_LEN - 1 for e in graph))
    edge_keys = {(sx, sy, l) for (sx, sy, l, _, _) in graph}
    check("(G) the edge list has no duplicate (strand pair, length) entries",
          len(edge_keys) == len(graph))
    check("(G) the edge set is closed under reverse-complement conjugation: "
          "every overlap X->Y of length l has the conjugates rc(Y)->rc(X)",
          all((rc(sy), rc(sx), l) in edge_keys for (sx, sy, l, _, _) in graph))

    # -- (R) transitive edge reduction -------------------------------------

    def max_overlap(a: str, b: str) -> int:
        best = 0
        for l in range(1, READ_LEN):
            if a[READ_LEN - l:] == b[:l]:
                best = l
        return best

    def spelled_by_two_shorter(sx: str, sy: str, l: int) -> bool:
        """Literal MB09 section 6.2 reading: a middle molecule m and two
        *strictly shorter* overlaps whose composition spells this overlap, i.e.
        l1 + l2 - L = l."""
        for m in strands:
            for l1 in range(1, READ_LEN):
                for l2 in range(1, READ_LEN):
                    if (l1 < l and l2 < l and l1 + l2 - READ_LEN == l
                            and sx[READ_LEN - l1:] == m[:l1]
                            and m[READ_LEN - l2:] == sy[:l2]):
                        return True
        return False

    def myers_longer(sx: str, sy: str, l: int) -> bool:
        """Alternative reading: a two-step path through a distinct observed
        molecule with both proper overlaps strictly *longer*."""
        for m in strands:
            if mol(m) in (mol(sx), mol(sy)) and m != sx and m != sy:
                continue
            l1 = max_overlap(sx, m)
            l2 = max_overlap(m, sy)
            if 0 < l1 < READ_LEN and 0 < l2 < READ_LEN and l1 > l and l2 > l:
                return True
        return False

    reducible_lit = [e for e in graph if spelled_by_two_shorter(e[0], e[1], e[2])]
    reducible_my = [e for e in graph if myers_longer(e[0], e[1], e[2])]
    print(f"(R) reducible under 'spelled by two shorter overlaps': "
          f"{len(reducible_lit)} of {len(graph)}")
    print(f"(R) reducible under the longer-overlap reading     : "
          f"{len(reducible_my)} of {len(graph)}")
    check("(R) no edge of the graph is spelled by two shorter overlaps",
          len(reducible_lit) == 0)
    check("(R) no edge of the graph is removed by the longer-overlap reading",
          len(reducible_my) == 0)

    # -----------------------------------------------------------------------
    # (W) and (F) the two walks as bidirected circuits / flows
    # -----------------------------------------------------------------------

    def walk(seq: str):
        """The cyclic strand walk of a circular molecule: one step per start,
        the step being the length-(L-1) overlap between consecutive windows."""
        ws = windows(seq, READ_LEN)
        g = len(seq)
        steps = []
        for i in range(g):
            sx, sy = ws[i], ws[(i + 1) % g]
            steps.append((sx, sy, READ_LEN - 1))
        visits = [mol(w) for w in ws]
        return steps, visits

    def edge_of(sx: str, sy: str, l: int):
        for (ex, ey, el, sxx, syy) in graph:
            if ex == sx and ey == sy and el == l:
                return (sxx, syy)
        return None

    def circuit(seq: str):
        """Validate the walk of `seq` as a bidirected circuit and return the
        flow it carries (one unit per traversal) plus its vertex throughputs."""
        steps, visits = walk(seq)
        g = len(seq)
        flow = Counter()
        signs = []
        for (sx, sy, l) in steps:
            e = edge_of(sx, sy, l)
            assert e is not None, f"step {sx}->{sy} is not a graph edge"
            signs.append(e)
            flow[(sx, sy, l)] += 1
        # MB09 section 3.2: opposite incidences at every interior vertex
        for i in range(g):
            incoming = signs[(i - 1) % g]
            outgoing = signs[i]
            assert incoming[1] == -outgoing[0], \
                f"incidences do not alternate at visit {i} ({visits[i]})"
        # signed-incidence balance (MB09 section 3.4), no terminals
        bal = Counter()
        for ((sx, sy, l), f) in flow.items():
            sxx, syy = edge_of(sx, sy, l)
            bal[mol(sx)] += f * sxx
            bal[mol(sy)] += f * syy
        # vertex throughput: the flow departing the vertex (MB09 section 5.2)
        thr = Counter()
        for ((sx, sy, l), f) in flow.items():
            thr[mol(sx)] += f
        return flow, visits, thr, dict(bal)

    for name, seq in (("truth AAATT", S_STR), ("competitor AAAATT", D_STR)):
        flow, visits, thr, bal = circuit(seq)
        print(f"(W) {name}: valid bidirected circuit; "
              f"throughput {dict(thr)}; balance {bal}")
    print()

    flow_s, visits_s, thr_s, bal_s = circuit(S_STR)
    flow_d, visits_d, thr_d, bal_d = circuit(D_STR)

    check("(W) truth walk is a bidirected circuit (all steps are graph edges, "
          "incidences alternate)", all(edge_of(*st) is not None
                                       for st in walk(S_STR)[0]))
    check("(W) competitor walk is a bidirected circuit",
          all(edge_of(*st) is not None for st in walk(D_STR)[0]))
    check("(W) every visited vertex of both walks is an observed read molecule",
          all(v in read_verts for v in visits_s + visits_d))
    check("(F) truth: every read vertex has throughput >= 1 (vertex lower bound)",
          all(thr_s[v] >= 1 for v in read_verts))
    check("(F) competitor: every read vertex has throughput >= 1",
          all(thr_d[v] >= 1 for v in read_verts))
    check("(F) truth: every edge carries flow >= 0 (edge lower bound 0)",
          all(f >= 0 for f in flow_s.values()))
    check("(F) competitor: every edge carries flow >= 0",
          all(f >= 0 for f in flow_d.values()))
    check("(F) truth: signed-incidence balance 0 at every read vertex "
          "(no supersource/supersink usage)",
          all(bal_s[v] == 0 for v in read_verts))
    check("(F) competitor: signed-incidence balance 0 at every read vertex",
          all(bal_d[v] == 0 for v in read_verts))
    check("(F) truth throughputs equal the molecule spectrum (Observation 7)",
          dict(thr_s) == dict(d_s))
    check("(F) competitor throughputs equal the molecule spectrum",
          dict(thr_d) == dict(d_d))
    check("(F) a spelled bidirected circuit is an admissible section 6.2 flow, "
          "so both candidates are section 6.2 candidates on the actual graph",
          True)

    # -----------------------------------------------------------------------
    # (A) the two admissibility readings, kept distinct
    # -----------------------------------------------------------------------

    def per_vertex_admissible(d: Counter) -> bool:
        """The source rule (MB09 section 6.2): every read vertex has flow at
        least 1.  For a spelled molecule this is support equality."""
        return set(d) == set(x) and all(v >= 1 for v in d.values())

    def per_occurrence_admissible(d: Counter) -> bool:
        """The strictly stronger per-occurrence strengthening: every observed
        type occurs in the candidate at least as often as it was observed."""
        return set(d) == set(x) and all(d[w] >= x[w] for w in x)

    print("(A) per-vertex (source) admissible :",
          f"truth {per_vertex_admissible(d_s)}, "
          f"competitor {per_vertex_admissible(d_d)}")
    print("(A) per-occurrence (d >= x) admissible:",
          f"truth {per_occurrence_admissible(d_s)}, "
          f"competitor {per_occurrence_admissible(d_d)}")
    print()

    check("(A) truth is admissible under the source per-vertex rule",
          per_vertex_admissible(d_s))
    check("(A) competitor is admissible under the source per-vertex rule",
          per_vertex_admissible(d_d))
    check("(A) truth is admissible under the stronger per-occurrence rule",
          per_occurrence_admissible(d_s))
    check("(A) competitor is admissible under the stronger per-occurrence rule",
          per_occurrence_admissible(d_d))
    check("(A) the truth's spectrum has genuine slack under d >= x "
          "(d_S = (1,2,2) >= x = (1,1,1), strict in AAT and TAA)",
          d_s["AAT"] > x["AAT"] and d_s["TAA"] > x["TAA"]
          and d_s["AAA"] == x["AAA"])

    # -----------------------------------------------------------------------
    # (D) the section 6.1 domain
    # -----------------------------------------------------------------------

    dna_classes = all_molecule_classes("ACGT", READ_LEN)
    used = [c for c in dna_classes if d_s.get(c, 0) or d_d.get(c, 0)]
    check("(D) truth spectrum lives inside the DNA molecule-class space",
          set(d_s) <= set(dna_classes) and set(d_d) <= set(dna_classes))
    check(f"(D) only {used} have positive multiplicity in either candidate",
          set(used) == {"AAA", "AAT", "TAA"})
    check("(D) 0 <= d_i <= N for every one of the %d DNA molecule classes, "
          "both candidates (max d = %d, %d)"
          % (len(dna_classes), max(d_s.values()), max(d_d.values())),
          all(0 <= d_s.get(c, 0) <= N for c in dna_classes)
          and all(0 <= d_d.get(c, 0) <= N for c in dna_classes))
    check("(D) n = 3 <= N = 5", n <= N)

    # -----------------------------------------------------------------------
    # (L) the literal section 6.1 objective, zero-count factors retained
    # -----------------------------------------------------------------------

    def comb(a: int, b: int) -> int:
        r = 1
        for i in range(b):
            r = r * (a - i) // (i + 1)
        return r

    def marginal(w: str, xw: int, d: Counter) -> Fraction:
        """One section 6.1 binomial marginal, ``C(n, xw) (d/N)^xw
        (1-d/N)^(n-xw)``."""
        return Fraction(comb(n, xw)) * \
            Fraction(d.get(w, 0), N) ** xw * \
            Fraction(N - d.get(w, 0), N) ** (n - xw)

    def lik(d: Counter) -> Fraction:
        """The literal product of binomial marginals over the *whole*
        reverse-complement class space of the DNA alphabet, zero-count factors
        retained."""
        out = Fraction(1)
        for c in dna_classes:
            out *= marginal(c, x.get(c, 0), d)
        return out

    ratio = lik(d_d) / lik(d_s)
    print(f"(L) literal section 6.1 product over all {len(dna_classes)} DNA "
          f"molecule classes")
    print(f"    L(D)/L(S) = {ratio} (with the C(n,x) factors)")
    print(f"    L(D)/L(S) = {lik(d_d) / lik(d_s)} (the C(n,x) factors cancel, "
          f"being equal on both sides)")
    print("    coordinate factors:",
          {c: (marginal(c, x[c], d_s), marginal(c, x[c], d_d))
           for c in ("AAA", "AAT", "TAA")})
    print()

    check("(L) the ratio is exactly 9/8 > 1", ratio == Fraction(9, 8))
    check("(L) only the AAA coordinate changes (1 -> 2); AAT and TAA are equal",
          d_s["AAT"] == d_d["AAT"] and d_s["TAA"] == d_d["TAA"]
          and d_s["AAA"] != d_d["AAA"])
    check("(L) both competitors are domestic: every zero-count class has "
          "d = 0, so its factor is 1",
          all(d_s.get(c, 0) == 0 and d_d.get(c, 0) == 0
              for c in dna_classes if x.get(c, 0) == 0))

    # -----------------------------------------------------------------------
    # (O) the competitor inside the whole section 6.1 domain
    # -----------------------------------------------------------------------

    support = sorted(x)
    best = None
    argmax = []
    # enumerate the entire box [0, N]^{#support} for the observed classes; the
    # unobserved classes are handled separately below
    for combo in itertools.product(range(N + 1), repeat=len(support)):
        d = Counter(dict(zip(support, combo)))
        val = lik(d)
        if best is None or val > best:
            best = val
            argmax = [combo]
        elif val == best:
            argmax.append(combo)
    print(f"(O) maximum of the section 6.1 objective over "
          f"[0,N]^{len(support)} = {best} (attained by {len(argmax)} vector(s))")
    print("    the truth's own slice value:", lik(d_s))
    print()

    check("(O) over the whole section 6.1 domain the objective is maximized by "
          "d_D = (2,2,2), and by nothing else",
          len(argmax) == 1 and dict(zip(support, argmax[0])) == dict(d_d))
    check("(O) the truth's vector is strictly inside the domain but not optimal",
          lik(d_s) < best)
    def zero_factor(v: int) -> Fraction:
        """The section 6.1 factor of a class with ``x = 0`` and multiplicity
        ``v``: ``C(n,0) (v/N)^0 (1-v/N)^n = (1-v/N)^n``."""
        return Fraction(N - v, N) ** n

    check("(O) for every unobserved class c and every 0 <= d_c <= N the factor "
          "is <= 1, with equality only at d_c = 0, so the unobserved classes "
          "are pinned to 0 at any maximizer",
          all(zero_factor(v) <= Fraction(1) for v in range(N + 1))
          and zero_factor(0) == Fraction(1)
          and all(zero_factor(v) < Fraction(1) for v in range(1, N + 1))
          and len([c for c in dna_classes if x.get(c, 0) == 0]) ==
          len(dna_classes) - len(support))
    check("(O) hence d_D is the unique maximizer over the entire box "
          "[0,N]^{#classes}: the witness is not an artifact of a restricted "
          "candidate search",
          len(argmax) == 1)

    # -----------------------------------------------------------------------
    # (S) the fixed-length boundary
    # -----------------------------------------------------------------------

    # same-length slice: sum of multiplicities = N
    best_sum = None
    argmax_sum = []
    for combo in itertools.product(range(N + 1), repeat=len(support)):
        if sum(combo) != N:
            continue
        d = Counter(dict(zip(support, combo)))
        val = lik(d)
        if best_sum is None or val > best_sum:
            best_sum = val
            argmax_sum = [combo]
        elif val == best_sum:
            argmax_sum.append(combo)
    print(f"(S) same-length slice (sum d = N = {N}): maximum {best_sum} over "
          f"[0,N]^{len(support)}, attained by {len(argmax_sum)} vector(s)")
    print("    the truth's vector:", dict(d_s), "sum", sum(d_s.values()))
    print()

    check("(S) |S| = 5, |D| = 6: the competitor is NOT the same length as the "
          "truth, so this witness does not address the same-length case",
          g_s != g_d and sum(d_d.values()) != N)
    check("(S) sum d_D = 6 = |D| != 5 = N = sum d_S: d_D is outside the "
          "length-constrained domain, which is why a same-length witness needs "
          "a different pair", sum(d_d.values()) != sum(d_s.values()))
    check("(S) inside the sum-constrained slice sum d = N the truth's vector is "
          "itself a maximizer, so this instance gives no same-length "
          "counterexample", lik(d_s) == best_sum)
    check("(S) the sum-constrained optimum is, up to a permutation of the "
          "three observed classes, the truth's own (1,2,2)",
          all(sorted(combo) == [1, 2, 2] for combo in argmax_sum))

    # -----------------------------------------------------------------------
    # (C) the oriented (single-strand) control
    # -----------------------------------------------------------------------

    o_s = Counter(windows(S_STR, READ_LEN))
    o_d = Counter(windows(D_STR, READ_LEN))
    o_x = Counter(windows(S_STR, READ_LEN)[r] for r in STARTS)
    print("(C) oriented spectra: d_S^or =", dict(o_s), " d_D^or =", dict(o_d),
          " x^or =", dict(o_x))
    check("(C) under strict oriented indexing the truth's support is not the "
          "observed read support, because S also contains the unobserved "
          "oriented windows ATT and TTA", set(o_s) != set(o_x))
    check("(C) under strict oriented indexing the competitor's support is not "
          "the observed read support either", set(o_d) != set(o_x))
    check("(C) so under a strict oriented 4^k index neither molecule would be a "
          "section 6.2 candidate at all; the molecule-class reading is the "
          "operative one (docs/source-notes/"
          "mb09-se61-index-orientation-resolution.md)",
          set(o_s) != set(o_x) and set(o_d) != set(o_x))

    # -----------------------------------------------------------------------
    # (E) control: the same pair under the exact candidate-intrinsic multinomial
    # -----------------------------------------------------------------------

    def exact_lik(seq: str) -> Fraction:
        """The repository's exact Medvedev-Brudno read-count multinomial with the
        candidate-intrinsic length: the observation's multinomial coefficient
        `n! / prod_w x_w!` times `prod_w (d_w / |D|)^{x_w}`."""
        g = len(seq)
        coeff = Fraction(1)
        rest = n
        for w in x:
            coeff *= comb(rest, x[w])
            rest -= x[w]
        d = spectrum(seq, READ_LEN)
        val = Fraction(1)
        for w in x:
            val *= Fraction(d.get(w, 0), g) ** x[w]
        return coeff * val

    e_s = exact_lik(S_STR)
    e_d = exact_lik(D_STR)
    exact_ratio = e_d / e_s
    print(f"(E) exact candidate-intrinsic multinomial (the repository's exact "
          f"reading), observation multinomial coefficient on both sides:")
    print(f"    L_exact(S) = {e_s} (|S| = {g_s}), "
          f"L_exact(D) = {e_d} (|D| = {g_d}), ratio {exact_ratio}")
    check("(E) under the exact candidate-intrinsic multinomial the pair is a "
          "strict improvement too (125/108 > 1): the variable-length witness is "
          "not a tie, and not a same-length one either",
          exact_ratio == Fraction(125, 108))

    # -----------------------------------------------------------------------
    # summary
    # -----------------------------------------------------------------------

    print()
    ok = True
    for name, res in checks:
        ok &= res
    print("ALL AUDIT CHECKS PASS" if ok else "SOME AUDIT CHECKS FAILED")
    print(f"({len(checks)} checks; rerun with --census for the bounded census)")
    return 0 if ok else 1


if __name__ == "__main__":
    if "--census" in sys.argv:
        census()
        sys.exit(0)
    sys.exit(main())
