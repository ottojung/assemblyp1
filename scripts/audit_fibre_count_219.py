#!/usr/bin/env python3
"""Independent audit of the exact same-length complete-spectrum fibre count.

Audited results (docs/exact-same-length-spectrum-fibre-count.md and the
#219 research-assistant shortcuts):

  COUNTING (Mobius):   N(c) = sum_{h|g} P_h,
                       P_h  = sum_{d|h} (mu(d)/d) * B_{h/d},
                       B_k  = tau_r(k*c0) * prod_v (d_v(k)-1)! / prod_e (k*c0_e)!

  COUNTING (totient):  N(c) = sum_{k|g} phi(g/k)/(g/k) * B_k
                                = (1/g) sum_{k|g} k * phi(g/k) * B_k

  SINGLETON CRITERION (no Mobius):
    - nonbranching support                -> N = 1 (unique) for every gcd
    - branching support, g = gcd(c) > 1   -> N >= 2 (nonunique)
    - branching support, g = 1            -> N = 1 iff tau_r(c)*prod(d_v-1)! = prod c_e!

This script checks every claim against brute-force enumeration:
  * all binary circular words of length 1..GMAX, for L = 2 and L = 3;
  * the fibre size per spectrum = number of distinct rotation classes;
  * the primitive count P_h per level-h capacity vector h*c0;
  * root independence of tau_r (balanced + strongly connected);
  * self-loop handling (diagonal excludes self-loops, factorial includes them);
  * the totient formula against the Mobius formula on every spectrum.

Exact arithmetic throughout (Fraction, integer determinant via Bareiss).
"""

from fractions import Fraction
from itertools import product
from math import factorial, gcd
from functools import reduce


# --------------------------------------------------------------------------
# Arithmetic helpers
# --------------------------------------------------------------------------

def mobius(n):
    if n == 1:
        return 1
    p, m, factors = 2, n, 0
    while p * p <= m:
        if m % p == 0:
            m //= p
            factors += 1
            if m % p == 0:
                return 0
        p += 1
    if m > 1:
        factors += 1
    return -1 if factors % 2 else 1


def totient(n):
    result = n
    p = 2
    m = n
    while p * p <= m:
        if m % p == 0:
            while m % p == 0:
                m //= p
            result -= result // p
        p += 1
    if m > 1:
        result -= result // m
    return result


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


# --------------------------------------------------------------------------
# General edge-type multigraph
# --------------------------------------------------------------------------

class Graph:
    """Directed multigraph with typed edges and a capacity per edge type."""

    def __init__(self, vertices, edges, tail, head, capacity):
        self.verts = list(vertices)
        self.edges = list(edges)
        self.tail = dict(tail)
        self.head = dict(head)
        self.cap = dict(capacity)

    @property
    def support(self):
        return [e for e in self.edges if self.cap[e] > 0]

    def out_deg_incl(self, u):
        return sum(self.cap[e] for e in self.support if self.tail[e] == u)

    def out_deg_excl(self, u):
        return sum(self.cap[e] for e in self.support
                   if self.tail[e] == u and self.head[e] != u)

    def in_deg(self, u):
        return sum(self.cap[e] for e in self.support if self.head[e] == u)

    def is_balanced(self):
        return all(self.in_deg(u) == self.out_deg_incl(u) for u in self.verts)

    def is_strongly_connected(self):
        if not self.verts:
            return True
        adj = {u: set() for u in self.verts}
        radj = {u: set() for u in self.verts}
        for e in self.support:
            adj[self.tail[e]].add(self.head[e])
            radj[self.head[e]].add(self.tail[e])
        start = self.verts[0]
        seen, stack = {start}, [start]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        if len(seen) != len(self.verts):
            return False
        seen, stack = {start}, [start]
        while stack:
            u = stack.pop()
            for v in radj[u]:
                if v not in seen:
                    seen.add(v)
                    stack.append(v)
        return len(seen) == len(self.verts)

    def is_nonbranching(self):
        """No vertex has two distinct outgoing edge types."""
        for u in self.verts:
            outs = {e for e in self.support if self.tail[e] == u}
            if len(outs) >= 2:
                return False
        return True

    def scale(self, k):
        return Graph(self.verts, self.edges, self.tail, self.head,
                     {e: k * self.cap[e] for e in self.edges})


def graph_from_spectrum(spec, L):
    """Build the edge-type graph of an L-mer spectrum.

    Edge types are L-mers; vertices are (L-1)-mers; tail(e)=e[:-1],
    head(e)=e[1:].
    """
    support = [e for e in sorted(spec) if spec[e] > 0]
    verts = set()
    for e in support:
        verts.add(e[:-1])
        verts.add(e[1:])
    tail = {e: e[:-1] for e in support}
    head = {e: e[1:] for e in support}
    cap = {e: spec[e] for e in support}
    return Graph(sorted(verts), support, tail, head, cap)


# --------------------------------------------------------------------------
# Weighted in-arborescence count tau_r (Matrix-Tree, self-loops excluded)
# --------------------------------------------------------------------------

def det_bareiss(M):
    n = len(M)
    if n == 0:
        return 1
    A = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            piv = next((i for i in range(k + 1, n) if A[i][k] != 0), None)
            if piv is None:
                return 0
            A[k], A[piv] = A[piv], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
        for i in range(k + 1, n):
            A[i][k] = 0
    return sign * A[n - 1][n - 1]


def tau_root(g, root):
    support = g.support
    n = len(g.verts)
    if root not in g.verts:
        return 0
    if n == 1:
        return 1
    others = [u for u in g.verts if u != root]
    idx = {u: i for i, u in enumerate(others)}
    L = [[0] * (n - 1) for _ in range(n - 1)]
    for e in support:
        t, h = g.tail[e], g.head[e]
        if t == h or t == root:
            continue
        w = g.cap[e]
        L[idx[t]][idx[t]] += w
        if h != root:
            L[idx[t]][idx[h]] -= w
    return det_bareiss(L)


def tau_all_roots(g):
    return {r: tau_root(g, r) for r in g.verts}


# --------------------------------------------------------------------------
# BEST / Mobius / totient formulas
# --------------------------------------------------------------------------

def B_value(g, root=None):
    """B = tau_r(c) * prod_v (d_v-1)! / prod_e c_e!  (exact Fraction)."""
    if root is None:
        root = g.verts[0]
    tau = tau_root(g, root)
    num = tau
    for u in g.verts:
        num *= factorial(g.out_deg_incl(u) - 1)
    den = 1
    for e in g.support:
        den *= factorial(g.cap[e])
    return Fraction(num, den)


def gcd_of_graph(g):
    return reduce(gcd, [g.cap[e] for e in g.support])


def _base_graph(g):
    """Return (c0_graph, gval) where c0 = g.cap / gval and gval = gcd."""
    gval = gcd_of_graph(g)
    c0 = Graph(g.verts, g.edges, g.tail, g.head,
               {e: g.cap[e] // gval for e in g.edges})
    return c0, gval


def B_at_level(g, k, root=None):
    """B_k: the weighted BEST quantity at level-k capacity k*c0."""
    c0, _ = _base_graph(g)
    return B_value(c0.scale(k), root)


def primitive_count_mobius(g, h, root=None):
    """P_h = sum_{d|h} (mu(d)/d) * B_{h/d}."""
    total = Fraction(0)
    for d in divisors(h):
        total += Fraction(mobius(d), d) * B_at_level(g, h // d, root)
    return total


def necklace_count_mobius(g, root=None):
    """N(c) = sum_{h|g} P_h."""
    _, gval = _base_graph(g)
    return sum((primitive_count_mobius(g, h, root) for h in divisors(gval)),
               Fraction(0))


def necklace_count_totient(g, root=None):
    """N(c) = sum_{k|g} phi(g/k)/(g/k) * B_k  (Burnside form)."""
    _, gval = _base_graph(g)
    total = Fraction(0)
    for k in divisors(gval):
        total += Fraction(totient(gval // k), gval // k) * B_at_level(g, k, root)
    return total


def singleton_numerator(g):
    """tau_r(c) * prod_v (d_v-1)!  (the 'numerator' of B at level 1)."""
    root = g.verts[0]
    num = tau_root(g, root)
    for u in g.verts:
        num *= factorial(g.out_deg_incl(u) - 1)
    return num


def singleton_denominator(g):
    den = 1
    for e in g.support:
        den *= factorial(g.cap[e])
    return den


def singleton_criterion(g):
    """Shortcut A: complete yes/no singleton test, no Mobius.

    Returns (is_singleton, reason).
    """
    if not g.is_balanced():
        raise ValueError("not balanced")
    if not g.is_strongly_connected():
        raise ValueError("support not strongly connected")
    if g.is_nonbranching():
        return True, "nonbranching: directed cycle, unique spelling"
    gval = gcd_of_graph(g)
    if gval > 1:
        return False, f"branching + gcd={gval}>1: periodic vs primitive orbits"
    num = singleton_numerator(g)
    den = singleton_denominator(g)
    if num == den:
        return True, "branching + gcd=1: tau*prod(d_v-1)! == prod c_e!"
    return False, f"branching + gcd=1: tau*prod(d_v-1)! = {num} != {den} = prod c_e!"


# --------------------------------------------------------------------------
# Brute-force enumeration of cyclic spellings
# --------------------------------------------------------------------------

def enumerate_spellings(g):
    """All cyclic edge-type spelling orbits of g (brute force).

    Returns a set of canonical (minimal-rotation) cyclic words over edge
    types, where each edge type e is used exactly cap[e] times and consecutive
    types are incidence-compatible.
    """
    support = g.support
    cap = dict(g.cap)
    n = sum(cap.values())
    if n == 0:
        return set()
    orbits = set()
    words = []

    def rec2(word, remaining):
        if len(word) == n:
            if g.head[word[-1]] == g.tail[word[0]]:
                words.append(tuple(word))
            return
        if not word:
            allowed = [e for e in support if remaining[e] > 0]
        else:
            v = g.head[word[-1]]
            allowed = [e for e in support if remaining[e] > 0 and g.tail[e] == v]
        for e in allowed:
            remaining[e] -= 1
            word.append(e)
            rec2(word, remaining)
            word.pop()
            remaining[e] += 1

    rec2([], cap)
    for w in words:
        best = w
        for i in range(1, n):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        orbits.add(best)
    return orbits


def enumerate_primitive_spellings(g):
    """Primitive cyclic spelling orbits (those that are not proper powers)."""
    all_orbits = enumerate_spellings(g)
    prim = set()
    for w in all_orbits:
        n = len(w)
        is_prim = True
        for k in range(1, n):
            if n % k == 0 and all(w[i] == w[i % k] for i in range(n)):
                is_prim = False
                break
        if is_prim:
            prim.add(w)
    return prim


# --------------------------------------------------------------------------
# L-mer spectrum enumeration (binary words)
# --------------------------------------------------------------------------

def spectrum_of_word(word, L):
    G = len(word)
    spec = {}
    for r in range(G):
        w = tuple(word[(r + i) % G] for i in range(L))
        spec[w] = spec.get(w, 0) + 1
    return spec


def canonical_rotation(word):
    n = len(word)
    best = word
    for i in range(1, n):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def is_primitive_word(word):
    n = len(word)
    return not any(n % k == 0 and all(word[i] == word[i % k] for i in range(n))
                   for k in range(1, n))


def enumerate_fibres(GMAX, L):
    fibres = {}
    primitive_fibres = {}
    for G in range(1, GMAX + 1):
        for bits in product((0, 1), repeat=G):
            word = tuple(bits)
            spec = spectrum_of_word(word, L)
            key = frozenset(spec.items())
            canon = canonical_rotation(word)
            fibres.setdefault(key, set()).add(canon)
            if is_primitive_word(word):
                primitive_fibres.setdefault(key, set()).add(canon)
    return fibres, primitive_fibres


# --------------------------------------------------------------------------
# Explicit hand-computed tests (the note's checks + the #219 shortcuts)
# --------------------------------------------------------------------------

def explicit_tests():
    print("=== Explicit hand-computed convention tests ===")
    # Note example 1: one vertex, two loop types cap (2,2).  B=3/2, N=2.
    g = Graph(['v'], ['A', 'B'], {'A': 'v', 'B': 'v'}, {'A': 'v', 'B': 'v'},
              {'A': 2, 'B': 2})
    assert B_value(g) == Fraction(3, 2), B_value(g)
    assert necklace_count_mobius(g) == 2, necklace_count_mobius(g)
    assert necklace_count_totient(g) == 2, necklace_count_totient(g)
    assert len(enumerate_spellings(g)) == 2
    print("  one-vertex loops (2,2): B=3/2, N=2  [OK]")

    # Note example 2: two vertices AB=BA=2.  B=1/2, N=1.
    g = Graph(['A', 'B'], ['AB', 'BA'], {'AB': 'A', 'BA': 'B'},
              {'AB': 'B', 'BA': 'A'}, {'AB': 2, 'BA': 2})
    assert B_value(g) == Fraction(1, 2), B_value(g)
    assert necklace_count_mobius(g) == 1
    assert necklace_count_totient(g) == 1
    assert len(enumerate_spellings(g)) == 1
    print("  two-vertex AB=BA=2: B=1/2, N=1  [OK]")

    # Note example 3: AA=BB=1, AB=BA=2.  N=2.
    g = Graph(['A', 'B'], ['AA', 'BB', 'AB', 'BA'],
              {'AA': 'A', 'BB': 'B', 'AB': 'A', 'BA': 'B'},
              {'AA': 'A', 'BB': 'B', 'AB': 'B', 'BA': 'A'},
              {'AA': 1, 'BB': 1, 'AB': 2, 'BA': 2})
    assert necklace_count_mobius(g) == 2
    assert necklace_count_totient(g) == 2
    print("  AA=BB=1, AB=BA=2: N=2  [OK]")

    # Self-loop diagonal convention: AA=AB=BA=1, tau_A=tau_B=1, N=1.
    g = Graph(['A', 'B'], ['AA', 'AB', 'BA'],
              {'AA': 'A', 'AB': 'A', 'BA': 'B'},
              {'AA': 'A', 'AB': 'B', 'BA': 'A'},
              {'AA': 1, 'AB': 1, 'BA': 1})
    taus = tau_all_roots(g)
    assert taus['A'] == 1 and taus['B'] == 1, taus
    assert necklace_count_mobius(g) == 1
    print("  AA=AB=BA=1: tau_A=tau_B=1, N=1  [OK]")

    # Shortcut A: nonbranching -> unique at every gcd.
    # Single vertex, one loop type cap 5.
    g = Graph(['v'], ['A'], {'A': 'v'}, {'A': 'v'}, {'A': 5})
    ok, why = singleton_criterion(g)
    assert ok and "nonbranching" in why, (ok, why)
    assert necklace_count_mobius(g) == 1
    print("  nonbranching single loop cap 5: singleton  [OK]")

    # Directed cycle on 3 vertices, each edge cap 3 (nonbranching).
    g = Graph(['A', 'B', 'C'], ['AB', 'BC', 'CA'],
              {'AB': 'A', 'BC': 'B', 'CA': 'C'},
              {'AB': 'B', 'BC': 'C', 'CA': 'A'},
              {'AB': 3, 'BC': 3, 'CA': 3})
    ok, why = singleton_criterion(g)
    assert ok, why
    assert necklace_count_mobius(g) == 1
    assert necklace_count_totient(g) == 1
    print("  directed 3-cycle cap 3 each: singleton, N=1  [OK]")

    # Shortcut A: branching + gcd>1 -> nonunique.
    # Two vertices, two loops each cap (2,2) at a single vertex is branching
    # but not strongly connected; use branching on a 2-vertex graph:
    # A has loops AA and self... build branching strongly connected:
    # edges: AB, BA (the cycle) plus AA (a loop at A).  Branching at A (AB, AA).
    g = Graph(['A', 'B'], ['AB', 'BA', 'AA'],
              {'AB': 'A', 'BA': 'B', 'AA': 'A'},
              {'AB': 'B', 'BA': 'A', 'AA': 'A'},
              {'AB': 2, 'BA': 2, 'AA': 2})
    gval = gcd_of_graph(g)
    assert gval == 2
    ok, why = singleton_criterion(g)
    assert not ok and "gcd=2" in why, (ok, why)
    n_mob = necklace_count_mobius(g)
    n_tot = necklace_count_totient(g)
    assert n_mob == n_tot and n_mob >= 2, (n_mob, n_tot)
    # brute force
    bf = len(enumerate_spellings(g))
    assert n_mob == bf, (n_mob, bf)
    print(f"  branching+gcd=2 (AB=BA=AA=2): nonunique, N={n_mob} (brute {bf})  [OK]")

    # Shortcut A: branching + gcd=1 unique case.
    # AB=BA=AA=1: branching at A, gcd 1, N=1 (unique).
    g = Graph(['A', 'B'], ['AB', 'BA', 'AA'],
              {'AB': 'A', 'BA': 'B', 'AA': 'A'},
              {'AB': 'B', 'BA': 'A', 'AA': 'A'},
              {'AB': 1, 'BA': 1, 'AA': 1})
    ok, why = singleton_criterion(g)
    assert ok and "gcd=1" in why, (ok, why)
    assert necklace_count_mobius(g) == 1
    print("  branching+gcd=1 (AB=BA=AA=1): unique  [OK]")

    # Shortcut A: branching + gcd=1 nonunique case.
    # Need tau*prod(d_v-1)! != prod c_e!.  Try AB=BA=1, AA=2:
    # d_A = out(A) = AA+AB = 3, d_B = BA = 1.  tau_A = 1 (B picks BA).
    # num = 1 * 2! * 0! = 2. den = 2!*1!*1! = 2.  Equal -> unique!  Not this.
    # Try AB=2, BA=2, AA=1: d_A=3, d_B=2.  tau_A=2 (B picks one of 2 BA).
    # num = 2 * 2! * 1! = 4. den = 2!*2!*1! = 4.  Equal -> unique!
    # Try AB=1, BA=1, AA=3: d_A=4, d_B=1. tau_A=1. num=1*3!*0!=6. den=3!=6.
    # Equal -> unique.
    # Try a genuinely nonunique branching gcd-1: two vertices A,B with
    # AB, BA and a loop AA, loop BB: AB=BA=1, AA=BB=1.
    # d_A=2 (AA,AB), d_B=2 (BB,BA).  tau_A: B picks BB or BA; BB stuck, so BA.
    # tau_A=1. num=1*1!*1!=1. den=1*1*1*1=1. Equal -> unique?!  Check brute.
    g = Graph(['A', 'B'], ['AB', 'BA', 'AA', 'BB'],
              {'AB': 'A', 'BA': 'B', 'AA': 'A', 'BB': 'B'},
              {'AB': 'B', 'BA': 'A', 'AA': 'A', 'BB': 'B'},
              {'AB': 1, 'BA': 1, 'AA': 1, 'BB': 1})
    n = necklace_count_mobius(g)
    bf = len(enumerate_spellings(g))
    ok, why = singleton_criterion(g)
    print(f"  AB=BA=AA=BB=1: N={n} (brute {bf}), singleton={ok} ({why})")
    assert n == bf
    # This is the gcd-1 branching case; criterion must agree with brute force.
    assert ok == (n == 1)

    print("  all explicit tests passed")


# --------------------------------------------------------------------------
# Full enumeration audit
# --------------------------------------------------------------------------

def audit(GMAX, L):
    print(f"=== Enumeration audit: binary words length 1..{GMAX}, L={L} ===")
    fibres, primitive_fibres = enumerate_fibres(GMAX, L)
    mismatches = root_mismatches = crit_mismatches = totient_mismatches = 0
    prim_mismatches = 0
    total = self_loop_cases = 0
    for key in sorted(fibres, key=lambda k: (len(k), sorted(k))):
        spec = dict(key)
        g = graph_from_spectrum(spec, L)
        n_formula = necklace_count_mobius(g)
        n_totient = necklace_count_totient(g)
        n_brute = len(fibres[key])
        total += 1
        has_self_loop = any(e[:-1] == e[1:] for e in spec)
        if has_self_loop:
            self_loop_cases += 1
        if n_formula != n_brute:
            mismatches += 1
            print(f"  N MISMATCH {spec}: mobius={n_formula} brute={n_brute}")
        if n_totient != n_brute:
            totient_mismatches += 1
            print(f"  N MISMATCH {spec}: totient={n_totient} brute={n_brute}")
        taus = tau_all_roots(g)
        if len(set(taus.values())) > 1:
            root_mismatches += 1
            print(f"  ROOT MISMATCH: {spec} -> {taus}")
        ok, why = singleton_criterion(g)
        if ok != (n_brute == 1):
            crit_mismatches += 1
            print(f"  CRITERION MISMATCH {spec}: crit={ok} brute_singleton={n_brute == 1}")
        # primitive count at each level h | g
        gval = gcd_of_graph(g)
        c0, _ = _base_graph(g)
        for h in divisors(gval):
            p_formula = primitive_count_mobius(g, h)
            ch = {e: c0.cap[e] * h for e in c0.support}
            pf = primitive_fibres.get(frozenset(ch.items()), set())
            p_brute = len(pf)
            if p_formula != p_brute:
                prim_mismatches += 1
                print(f"  PRIM MISMATCH {spec} h={h}: {p_formula} vs {p_brute}")
    print(f"  spectra checked: {total}")
    print(f"  N (mobius) mismatches:    {mismatches}")
    print(f"  N (totient) mismatches:   {totient_mismatches}")
    print(f"  root mismatches:          {root_mismatches}")
    print(f"  criterion mismatches:     {crit_mismatches}")
    print(f"  primitive mismatches:      {prim_mismatches}")
    print(f"  self-loop spectra:         {self_loop_cases}")
    return mismatches + totient_mismatches + root_mismatches + crit_mismatches + prim_mismatches


if __name__ == "__main__":
    explicit_tests()
    print()
    a = audit(9, 2)
    b = audit(9, 3)
    print()
    if a + b == 0:
        print("AUDIT PASSED: all claims verified against brute force.")
    else:
        print(f"AUDIT FAILED: {a + b} mismatches.")
