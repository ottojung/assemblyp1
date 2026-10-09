#!/usr/bin/env python3
"""Cross-variant transfer table for the finite AssemblyP1 statement (issue #216).

The computational half of the implication lattice documented in
`docs/implication-lattice-216.md`.  Self-contained, exact (`fractions.Fraction`),
deterministic, exits non-zero on any failed assertion.

Sections
  A. The witnesses already on `main`, plus the #88 dominance instance and the
     #88 correction's membership asymmetry, recomputed under every panel.
  B. The five new `I_s`-certified witnesses introduced by this issue, each of
     which separates variant panels that the witnesses on `main` do not
     separate.
  C. The transfer-table assertions (strictness by panel, tie semantics, the
     exact/fixed-N conversion identity).
  D. A bounded census count of each transfer category, over a declared range.
     Counts are **bounded evidence**, never proofs; a zero count inside a range
     is a *negative search result*, not a theorem.
  E. The transfer table, rendered: the candidate-universe inclusion edges and
     the witness x interpretation-cell matrix, so that the prose note
     `docs/implication-lattice-216.md` quotes this output verbatim.

Objective family (panel = strand convention)
  E      exact multinomial, candidate-intrinsic `N(D)`   (contract Variant E)
  A'     fixed-`N` multinomial factors, external `N`      (contract Variant A,
         factor part)
  A_lit  literal §6.1 product of binomial marginals       (contract Variant A)

The observation-only multinomial coefficient cancels in every ratio below.

Primary sources
  P. Medvedev, M. Brudno, *Maximum Likelihood Genome Assembly*, J. Comput. Biol.
    16(8) (2009) 1101-1116, §6.1, §6.2, §3.1, §4.1.
  I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse, *Information-optimal
    genome assembly via sparse read-overlap graphs*, Bioinformatics 32(17)
    (2016) i494-i502, §2, §3, §5.
  `docs/ml-formalization-contract.md` (Variants E/A/F),
  `docs/source-notes/conclusion-semantics-determination.md` (conclusion schemas).
"""

import sys
from fractions import Fraction
from itertools import product
from math import comb

# --------------------------------------------------------------------------
# 0.  Alphabet, reverse complement, read-type conventions
# --------------------------------------------------------------------------

COMP = {'A': 'T', 'T': 'A', 'C': 'G', 'G': 'C'}


def rc(w):
    """DNA reverse complement of a word."""
    return ''.join(COMP[c] for c in reversed(w))


def types(L, alpha):
    """All oriented length-`L` words over `alpha`."""
    return [''.join(p) for p in product(alpha, repeat=L)]


def ori_spec(g, L, alpha):
    """Oriented read-type multiplicities: the number of start positions whose
    circular length-`L` window is `w`."""
    d = {t: 0 for t in types(L, alpha)}
    for i in range(len(g)):
        w = ''.join(g[(i + j) % len(g)] for j in range(L))
        d[w] += 1
    return d


def rep(w):
    """Representative of the reverse-complement class of `w`."""
    return min(w, rc(w))


def mol_counts(d, alpha, L):
    """Aggregate multiplicities over reverse-complement classes (MB09 §3.1)."""
    out = {}
    for t, v in d.items():
        out[rep(t)] = out.get(rep(t), 0) + v
    return out


def obs_counts(x, alpha, L):
    """Aggregate an oriented observation over reverse-complement classes."""
    out = {}
    for t, v in x.items():
        if v > 0:
            out[rep(t)] = out.get(rep(t), 0) + v
    return out


# --------------------------------------------------------------------------
# 1.  The objective family in each strand panel
# --------------------------------------------------------------------------

def counts(g, L, panel, alpha):
    """Candidate multiplicities, indexed by the panel's read types."""
    d = ori_spec(g, L, alpha)
    if panel == 'oriented':
        return d
    return mol_counts(d, alpha, L)


def ratio_E(gS, gD, L, x, panel, alpha):
    """`E(D)/E(S)`, exact multinomial with candidate-intrinsic `N(D)`."""
    dS, dD = counts(gS, L, panel, alpha), counts(gD, L, panel, alpha)
    xc = x if panel == 'oriented' else obs_counts(x, alpha, L)
    num = den = Fraction(1)
    for t, v in xc.items():
        if v > 0:
            num *= Fraction(dD[t], len(gD)) ** v
            den *= Fraction(dS[t], len(gS)) ** v
    return num / den


def ratio_Aprime(gS, gD, L, x, N, panel, alpha):
    """`A'(D)/A'(S)`, fixed-`N` multinomial factors, external `N`."""
    dS, dD = counts(gS, L, panel, alpha), counts(gD, L, panel, alpha)
    xc = x if panel == 'oriented' else obs_counts(x, alpha, L)
    num = den = Fraction(1)
    for t, v in xc.items():
        if v > 0:
            num *= Fraction(dD[t], N) ** v
            den *= Fraction(dS[t], N) ** v
    return num / den


def ratio_Alit(gS, gD, L, x, N, panel, alpha):
    """`A(D)/A(S)`, literal §6.1 product of binomial marginals."""
    dS, dD = counts(gS, L, panel, alpha), counts(gD, L, panel, alpha)
    xc = x if panel == 'oriented' else obs_counts(x, alpha, L)
    n = sum(xc.values())
    idx = (types(L, alpha) if panel == 'oriented'
           else sorted(set(xc) | set(dS) | set(dD)))
    num = den = Fraction(1)
    for t in idx:
        xi = xc.get(t, 0)
        pS, pD = Fraction(dS.get(t, 0), N), Fraction(dD.get(t, 0), N)
        den *= comb(n, xi) * (pS ** xi) * ((1 - pS) ** (n - xi))
        num *= comb(n, xi) * (pD ** xi) * ((1 - pD) ** (n - xi))
    return num / den


def obs_of(S, L, starts):
    """Observation realised by the multiset of latent starts on `S`."""
    x = {}
    for s in starts:
        w = ''.join(S[(s + j) % len(S)] for j in range(L))
        x[w] = x.get(w, 0) + 1
    return x


# --------------------------------------------------------------------------
# 2.  The corrected source-faithful bridging predicate `I_s`
#     (transcribed from AssemblyP1/SourceFaithfulIs.lean; deliberately *not*
#      imported, so that this script is an independent check)
# --------------------------------------------------------------------------

def information_feasible(S, L, R):
    """`R ∈ I_s`: coverage, every triple repeat all-bridged, every interleaved
    pair of repeats bridged.

    A copy at start `t` of a repeat of length `e` is bridged by the read at `r`
    iff that read *strictly straddles* the occurrence: on a suitable lift
    `r < t'` and `t' + e < r + L` (Bresler et al. 2013, Fig. 5; Shomorony et
    al. 2016 §3/Fig. 6).  Transcribed as: the copy starts at offset `d + 1` of
    the read at `r` and `d + e + 1 < L`.
    """
    G = len(S)
    cycl = lambda i: S[i % G]
    win = lambda e, r: tuple(cycl(r + d) for d in range(e))
    pre = lambda t: cycl(t + G - 1)
    fol = lambda e, t: cycl(t + e)

    def is_repeat(e, a, b):
        return (1 <= e < G and a != b and win(e, a) == win(e, b)
                and pre(a) != pre(b) and fol(e, a) != fol(e, b))

    def is_triple(e, a, b, c):
        return (1 <= e < G and len({a, b, c}) == 3
                and win(e, a) == win(e, b) == win(e, c)
                and not (pre(a) == pre(b) == pre(c))
                and not (fol(e, a) == fol(e, b) == fol(e, c)))

    def read_covers(r, p):
        return any((r + d) % G == p % G for d in range(L))

    def bridges_copy(e, t):
        for r in R:
            for d in range(L):
                if d + e + 1 < L and (r + d + 1) % G == t:
                    return True
        return False

    if not all(any(read_covers(r, p) for r in R) for p in range(G)):
        return False, 'coverage'
    for e in range(1, G):
        for a in range(G):
            for b in range(G):
                for c in range(G):
                    if is_triple(e, a, b, c) and not (
                            bridges_copy(e, a) and bridges_copy(e, b)
                            and bridges_copy(e, c)):
                        return False, ('clause2', e, a, b, c)

    reps = [(e, a, b) for e in range(1, G) for a in range(G) for b in range(G)
            if is_repeat(e, a, b)]

    def in_open_arc(a, b, p):
        return 0 < (p + G - a) % G < (b + G - a) % G

    for (e1, a, b) in reps:
        for (e2, c, d) in reps:
            if len({a, b, c, d}) < 4:
                continue
            if in_open_arc(a, b, c) != in_open_arc(a, b, d) and not (
                    bridges_copy(e1, a) or bridges_copy(e1, b)
                    or bridges_copy(e2, c) or bridges_copy(e2, d)):
                return False, ('clause3', e1, e2, a, b, c, d)
    return True, None


# --------------------------------------------------------------------------
# 3.  Equivalence orbits and §6.2 support spelling
# --------------------------------------------------------------------------

def rot(w):
    return w[1:] + w[0]


def rots(w):
    s, c = set(), w
    for _ in range(len(w)):
        s.add(c)
        c = rot(c)
    return s


def dihedral(w):
    return rots(w) | rots(rc(w))


def support(g, L, alpha, panel='oriented'):
    return {w for w, v in counts(g, L, panel, alpha).items() if v > 0}


def spelled(g, x, L, alpha, panel):
    """`g` spells exactly the observed read types of `panel`: the *necessary*
    condition for membership in the literal §6.2 class, which
    `AssemblyP1/SameLength62Maximizer.genuine62_molecule_eq` derives from a
    genuine §6.2 certificate."""
    xc = x if panel == 'oriented' else obs_counts(x, alpha, L)
    return support(g, L, alpha, panel) == set(xc)


# --------------------------------------------------------------------------
# 4.  The witnesses
# --------------------------------------------------------------------------

DOC_WITNESSES = [
    ('#31 fixed-length exact', 'AAABB', 'AAAAB', 3, [0, 1, 4], 'AB',
     'docs/fixed-length-exact-counterexample.md'),
    ('#32 fixed-length binomial', 'AAACC', 'AAAAC', 3, [0, 1, 4], 'AC',
     'docs/fixed-length-binomial-counterexample.md'),
    ('#24 free-length exact', 'ACGT', 'ACACGT', 2, [0, 0, 2], 'ACGT',
     'docs/exact-variant-e-counterexample.md'),
    ('#43 §6.2 same-length', 'AAATAT', 'AAAAAT', 3, [0, 0, 1, 3, 5], 'AT',
     'docs/section62-same-length-bidirected-counterexample.md'),
    ('#40 §6.2 free-length', 'AAATT', 'AAAATT', 3, [0, 1, 4], 'AT',
     'docs/bridging-se62-flow-ml-counterexample.md'),
    ('#88 §6.2 dominance', 'AABB', 'ABAB', 2, [1, 3], 'AB',
     'docs/same-length-exact-ml-88-refutation.md'),
]

NEW_WITNESSES = [
    ('W-sigma', 'AATT', 'AAAT', 2, [0, 1, 3], 'AT'),
    ('W-upsilon', 'AAT', 'AATT', 2, [0, 0, 1], 'AT'),
    ('W-lambda1', 'AAT', 'AT', 2, [1, 1, 2], 'AT'),
    ('W-lambda2', 'AT', 'ATAT', 2, [0, 1, 2], 'AT'),
    ('W-tau', 'AAT', 'ATT', 2, [1, 1, 2], 'AT'),
]


def evaluate(tag, S, D, L, starts, alpha, source):
    """Evaluate one witness.  `alpha` may be a non-DNA abstract alphabet
    (`#31` uses `A,B`), in which case the molecular panel is *not defined* and
    the genome equivalence is rotation only."""
    G, m, x = len(S), len(D), obs_of(S, L, starts)
    R = sorted(set(starts))
    ok_is, why = information_feasible(S, L, R)
    is_dna = set(alpha) <= set(COMP)
    equiv_disjoint = (not (dihedral(S) & dihedral(D)) if is_dna
                      else not (rots(S) & rots(D)))
    r = dict(tag=tag, S=S, D=D, L=L, x=x, R=R, G=G, m=m, alpha=alpha,
             n=sum(x.values()), source=source, ok_is=ok_is, why=why,
             is_dna=is_dna,
             spellS=spelled(S, x, L, alpha, 'oriented'),
             spellD=spelled(D, x, L, alpha, 'oriented'),
             spellS_mol=(spelled(S, x, L, alpha, 'molecular') if is_dna else None),
             spellD_mol=(spelled(D, x, L, alpha, 'molecular') if is_dna else None),
             disjoint=equiv_disjoint,
             rE_or=ratio_E(S, D, L, x, 'oriented', alpha),
             rAp_or=ratio_Aprime(S, D, L, x, G, 'oriented', alpha),
             rAl_or=ratio_Alit(S, D, L, x, G, 'oriented', alpha))
    if is_dna:
        r.update(rE_mol=ratio_E(S, D, L, x, 'molecular', alpha),
                 rAp_mol=ratio_Aprime(S, D, L, x, G, 'molecular', alpha),
                 rAl_mol=ratio_Alit(S, D, L, x, G, 'molecular', alpha))
    else:
        r.update(rE_mol=None, rAp_mol=None, rAl_mol=None)
    return r


def show(r):
    print("  %-24s S=%-7s D=%-7s G=%d m=%d L=%d n=%d R=%s" %
          (r['tag'], r['S'], r['D'], r['G'], r['m'], r['L'], r['n'], r['R']))
    mol = ("(mol: %s,%s)" % (r['spellS_mol'], r['spellD_mol'])
           if r['spellS_mol'] is not None else "")
    print("      x=%-34s I_s=%-5s spells(S,D)=(%s,%s) %s dihedral-disjoint=%s"
          % (str(r['x']), r['ok_is'], r['spellS'], r['spellD'], mol, r['disjoint']))
    print("      %-10s E=%-10s A'=%-10s A_lit=%-10s strictE=%s"
          % ('oriented', r['rE_or'], r['rAp_or'], r['rAl_or'], r['rE_or'] > 1))
    if r['is_dna']:
        print("      %-10s E=%-10s A'=%-10s A_lit=%-10s strictE=%s"
              % ('molecular', r['rE_mol'], r['rAp_mol'], r['rAl_mol'], r['rE_mol'] > 1))


# --------------------------------------------------------------------------
# 5.  Bounded census
# --------------------------------------------------------------------------

def allwords(G, alpha):
    return [''.join(p) for p in product(alpha, repeat=G)]


def realizations(G, n):
    if n == 0:
        yield []
        return
    for r in range(G):
        for rest in realizations(G, n - 1):
            yield [r] + rest


CATEGORIES = {
    'strand flip (oriented E strict, molecular E not)':
        lambda P: P['e_or'] > 0 and P['e_mol'] <= 0 and P['L'] >= 2,
    'strand flip (molecular E strict, oriented E not)':
        lambda P: P['e_mol'] > 0 and P['e_or'] <= 0 and P['L'] >= 2,
    'length axis (E strict, A\' not, |D|<G)':
        lambda P: P['e_or'] > 0 and P['a_or'] <= 0 and len(P['D']) < P['G'] and P['L'] >= 2,
    'length axis (A\' strict, E not, |D|>G)':
        lambda P: P['a_or'] > 0 and P['e_or'] <= 0 and len(P['D']) > P['G'] and P['L'] >= 2,
    'same length (E strict, A_lit not)':
        lambda P: P['e_or'] > 0 and P['l_or'] <= 0 and len(P['D']) == P['G'] and P['L'] >= 2,
    'same length (A_lit strict, E not)':
        lambda P: P['l_or'] > 0 and P['e_or'] <= 0 and len(P['D']) == P['G'] and P['L'] >= 2,
    'same length (E strict and A_lit strict)':
        lambda P: P['e_or'] > 0 and P['l_or'] > 0 and len(P['D']) == P['G'] and P['L'] >= 2,
    'tie (same length, D not a rotation of S)':
        lambda P: P['e_or'] == 0 and len(P['D']) == P['G'] and P['D'] not in rots(P['S']) and P['L'] >= 2,
    'molecular tie (same length, not dihedral-equivalent)':
        lambda P: P['e_mol'] == 0 and len(P['D']) == P['G'] and P['L'] >= 2
        and not (rots(P['S']) & rots(P['D'])) and P['D'] not in rots(rc(P['S'])),
}


def census(alpha, Gmax, Dmax, nreads, require_is=True):
    """Count transfer categories over binary genomes with `G <= Gmax`,
    competitors with `|D| <= Dmax`, and realisations of at most `nreads` reads.

    Every admissible candidate must be able to spell the observation
    (`key_S(D, x) > 0`) and must keep every read probability admissible
    (`d_w <= N`), since a fixed-`N` binomial probability above `1` is not a
    probability.  I_s is required at the faithful start set `R = range(rho)`.
    """
    counts_ = {k: 0 for k in CATEGORIES}
    spelled_ = {k: 0 for k in CATEGORIES}
    spelled_any_ = {k: 0 for k in CATEGORIES}
    examples = {}
    feasible = 0
    for G in range(2, Gmax + 1):
        for L in range(1, G + 1):
            for t in allwords(G, alpha):
                for rho in realizations(G, nreads):
                    R = sorted(set(rho))
                    if require_is:
                        ok, _ = information_feasible(t, L, R)
                        if not ok:
                            continue
                    feasible += 1
                    x = obs_of(t, L, rho)
                    n = sum(x.values())
                    for m in range(1, Dmax + 1):
                        for D in allwords(m, alpha):
                            if m < L:
                                continue
                            dS, dD = ori_spec(t, L, alpha), ori_spec(D, L, alpha)
                            if any(dD.get(w, 0) == 0 for w in x):
                                continue  # candidate cannot spell the observation
                            if any(v > G for v in dD.values()):
                                continue  # keeps fixed-N probabilities admissible
                            P = dict(S=t, D=D, L=L, x=x, G=G, m=m, n=n,
                                     e_or=(key(D, x, L, alpha, 'oriented') * G ** n
                                           - key(t, x, L, alpha, 'oriented') * m ** n))
                            P['e_mol'] = (key(D, x, L, alpha, 'molecular') * G ** n
                                          - key(t, x, L, alpha, 'molecular') * m ** n)
                            P['a_or'] = (key(D, x, L, alpha, 'oriented')
                                         - key(t, x, L, alpha, 'oriented'))
                            P['l_or'] = (keyA(D, x, L, G, alpha)
                                         - keyA(t, x, L, G, alpha))
                            P['spell'] = (spelled(t, x, L, alpha, 'oriented')
                                          and spelled(D, x, L, alpha, 'oriented'))
                            P['spell_mol'] = (spelled(t, x, L, alpha, 'molecular')
                                              and spelled(D, x, L, alpha, 'molecular'))
                            # a candidate class flag: is the pair §6.2-admissible
                            # in at least one strand panel?
                            P['spell_any'] = P['spell'] or P['spell_mol']
                            for k, w in CATEGORIES.items():
                                if w(P):
                                    counts_[k] += 1
                                    if P['spell']:
                                        spelled_[k] += 1
                                    if P['spell_any']:
                                        spelled_any_[k] += 1
                                    examples.setdefault(k, (t, D, L, x, G, m, R))
    return counts_, spelled_, spelled_any_, examples, feasible


def key(g, x, L, alpha, panel):
    """Integer key `prod_t d_t ^ x_t` over the panel's read types.

    `E(D) > E(S)` iff `key(D) * G^n > key(S) * m^n`, and
    `A'(D) > A'(S)` iff `key(D) > key(S)`; the length factors are the only
    difference, which is the conversion identity checked in section C.
    """
    d = counts(g, L, panel, alpha)
    xc = x if panel == 'oriented' else obs_counts(x, alpha, L)
    p = 1
    for t, v in xc.items():
        if v > 0:
            p *= d[t] ** v
    return p


def keyA(g, x, L, N, alpha):
    """Integer key `prod_t d_t^x_t (N-d_t)^(n-x_t)` for the literal binomial."""
    d = counts(g, L, 'oriented', alpha)
    n = sum(x.values())
    p = 1
    for t in types(L, alpha):
        p *= d[t] ** x.get(t, 0) * (N - d[t]) ** (n - x.get(t, 0))
    return p


# --------------------------------------------------------------------------
# 6.  Main
# --------------------------------------------------------------------------

def main():
    docs = [evaluate(t, S, D, L, st, al, src) for (t, S, D, L, st, al, src) in DOC_WITNESSES]
    new = [evaluate(t, S, D, L, st, al, 'this script')
           for (t, S, D, L, st, al) in NEW_WITNESSES]

    print("=" * 78)
    print("A. Witnesses already on main, recomputed under every panel")
    print("=" * 78)
    for r in docs:
        show(r)
    print()
    print("=" * 78)
    print("B. New I_s-certified witnesses")
    print("=" * 78)
    for r in new:
        show(r)

    checks = []

    def check(name, cond):
        checks.append((name, bool(cond)))
        print("  [%s] %s" % ('ok ' if cond else 'FAIL', name))

    print()
    print("=" * 78)
    print("C. Transfer-table assertions")
    print("=" * 78)
    by = {r['tag']: r for r in docs}
    nb = {r['tag']: r for r in new}

    print("  documented strictness by panel:")
    for r in docs:
        print("    %-24s E(or)=%-9s E(mol)=%-9s A'(or)=%-9s A_lit(or)=%-9s"
              % (r['tag'], r['rE_or'],
                 r['rE_mol'] if r['rE_mol'] is not None else 'n/a',
                 r['rAp_or'], r['rAl_or']))

    w43 = by['#43 §6.2 same-length']
    check("#43: I_s certified", w43['ok_is'])
    check("#43: molecular E ratio = 3", w43['rE_mol'] == 3)
    check("#43: molecular A_lit ratio = 5", w43['rAl_mol'] == 5)
    check("#43: oriented E(D)=0 (not an oriented-panel witness)", w43['rE_or'] == 0)
    check("#43: truth and competitor §6.2-spelled (molecular panel)",
          w43['spellS_mol'] and w43['spellD_mol'])
    check("#43: NOT spelled in the oriented panel", not (w43['spellS'] and w43['spellD']))
    check("#43: dihedral orbits disjoint", w43['disjoint'])

    w24 = by['#24 free-length exact']
    check("#24: I_s certified", w24['ok_is'])
    check("#24: E strict, oriented (32/27)", w24['rE_or'] == Fraction(32, 27))
    check("#24: E ties, molecular (1)", w24['rE_mol'] == 1)

    w40 = by['#40 §6.2 free-length']
    check("#40: E ratio equal in both panels (125/108)",
          w40['rE_or'] == w40['rE_mol'] == Fraction(125, 108))

    w31 = by['#31 fixed-length exact']
    w32 = by['#32 fixed-length binomial']
    check("#31: E ratio = 2 (same length)", w31['rE_or'] == 2)
    check("#31: abstract alphabet, molecular panel undefined", w31['rE_mol'] is None)
    check("#31: A' ratio = 2 (same-length transfer)", w31['rAp_or'] == 2)
    check("#32: E ratio = 2", w32['rE_or'] == 2)
    check("#32: A_lit ratio = 1125/512", w32['rAl_or'] == Fraction(1125, 512))
    check("#31/#32: not §6.2-spelled (do not transfer to the §6.2 class)",
          not (w31['spellS'] or w31['spellD']))

    ws = nb['W-sigma']
    check("W-sigma: I_s certified", ws['ok_is'])
    check("W-sigma: same length", ws['G'] == ws['m'])
    check("W-sigma: oriented E strict (= 2)", ws['rE_or'] == 2)
    check("W-sigma: molecular E ties (= 1)", ws['rE_mol'] == 1)
    check("W-sigma: oriented A_lit strict (512/243)", ws['rAl_or'] == Fraction(512, 243))
    check("W-sigma: molecular A_lit ties (= 1)", ws['rAl_mol'] == 1)
    check("W-sigma: not dihedral-equivalent", ws['disjoint'])

    wl1 = nb['W-lambda1']
    check("W-lambda1: I_s certified", wl1['ok_is'])
    check("W-lambda1: E strict (27/8)", wl1['rE_or'] == Fraction(27, 8))
    check("W-lambda1: A' ties (1)", wl1['rAp_or'] == 1)
    check("W-lambda1: A_lit strict (27/8)", wl1['rAl_or'] == Fraction(27, 8))
    check("W-lambda1: competitor shorter (|D| < G)", wl1['m'] < wl1['G'])

    wu = nb['W-upsilon']
    check("W-upsilon: I_s certified", wu['ok_is'])
    check("W-upsilon: molecular E strict (27/16)", wu['rE_mol'] == Fraction(27, 16))
    check("W-upsilon: oriented E NOT strict (27/64 < 1)",
          wu['rE_or'] == Fraction(27, 64))
    check("W-upsilon: molecular A' strict (4)", wu['rAp_mol'] == 4)
    check("W-upsilon: oriented A' ties (1)", wu['rAp_or'] == 1)
    check("W-upsilon: molecular A_lit strict (2)", wu['rAl_mol'] == 2)
    check("W-upsilon: oriented A_lit NOT strict (8/27 < 1)",
          wu['rAl_or'] == Fraction(8, 27))
    check("W-upsilon: competitor longer, dihedral-disjoint",
          wu['m'] > wu['G'] and wu['disjoint'])
    check("W-upsilon: conversion identity holds in both panels",
          wu['rE_mol'] == Fraction(wu['G'], wu['m']) ** wu['n'] * wu['rAp_mol']
          and wu['rE_or'] == Fraction(wu['G'], wu['m']) ** wu['n'] * wu['rAp_or'])

    wl2 = nb['W-lambda2']
    check("W-lambda2: I_s certified", wl2['ok_is'])
    check("W-lambda2: A' strict (8)", wl2['rAp_or'] == 8)
    check("W-lambda2: E ties (1)", wl2['rE_or'] == 1)
    check("W-lambda2: A_lit(D) = 0 (d_w = N at an unobserved type)", wl2['rAl_or'] == 0)
    check("W-lambda2: truth and competitor both §6.2-spelled (oriented)",
          wl2['spellS'] and wl2['spellD'])
    check("W-sigma: truth and competitor §6.2-spelled (molecular)",
          ws['spellS_mol'] and ws['spellD_mol'])
    check("#40: truth and competitor §6.2-spelled (molecular)",
          by['#40 §6.2 free-length']['spellS_mol']
          and by['#40 §6.2 free-length']['spellD_mol'])

    wt = nb['W-tau']
    check("W-tau: I_s certified", wt['ok_is'])
    check("W-tau: E ties in both panels", wt['rE_or'] == 1 and wt['rE_mol'] == 1)
    check("W-tau: A_lit ties (oriented)", wt['rAl_or'] == 1)
    check("W-tau: same length, D not a rotation of S",
          wt['G'] == wt['m'] and wt['D'] not in rots(wt['S']))
    check("W-tau: D is the reverse complement of S (molecular panel)",
          wt['D'] == rc(wt['S']))

    # -- the #88 cross-check, recomputed in this evaluator ------------------
    w88 = by['#88 §6.2 dominance']
    check("#88: I_s certified at the faithful start set {1,3}", w88['ok_is'])
    check("#88: E strict (ratio 4)", w88['rE_or'] == 4)
    check("#88: A' strict (ratio 4)", w88['rAp_or'] == 4)
    check("#88: truth NOT §6.2-spelled (membership antecedent false)",
          not w88['spellS'])
    check("#88: competitor §6.2-spelled (strict witness inside the class)",
          w88['spellD'])
    check("#88: truth's support strictly larger than the observation's",
          set(support(w88['S'], w88['L'], w88['alpha']))
          > set(w88['x']))
    check("#88: not dihedral-equivalent (still a strict, not a tie, witness)",
          w88['disjoint'])

    print("  conversion identity  E(D)/E(S) = (G/|D|)^n * A'(D)/A'(S):")
    for r in docs + new:
        for panel, re_, rap in (('oriented', 'rE_or', 'rAp_or'),
                                ('molecular', 'rE_mol', 'rAp_mol')):
            if r[rap] is None:
                continue
            lhs = r[re_]
            rhs = (Fraction(r['G'], r['m']) ** r['n']) * r[rap]
            check("    %-24s %-10s" % (r['tag'], panel), lhs == rhs)

    print()
    print("=" * 78)
    print("D. Bounded census (binary alphabet; counts are evidence, not proofs)")
    print("=" * 78)
    cnt, spl, splany, ex, feas = census("AT", 4, 5, 3)
    print("  I_s-certified (S,L,rho) instances in range: %d" % feas)
    print("  %-52s %6s %8s %8s" % ("category", "all", "spelled(or)", "spelled(any)"))
    for k in CATEGORIES:
        print("  %-52s %6d %8d %8d" % (k[:52], cnt[k], spl[k], splany[k]))
    print("  smallest instance per non-empty category:")
    for k, v in ex.items():
        print("    %-52s %s" % (k[:52], v))
    # The census must contain the new witnesses themselves.
    ok = all(cnt[k] > 0 for k in
             ['strand flip (oriented E strict, molecular E not)',
              'length axis (E strict, A\' not, |D|<G)',
              'length axis (A\' strict, E not, |D|>G)',
              'tie (same length, D not a rotation of S)'])
    check("census contains one instance of each direction the lattice declares open", ok)
    check("census finds no same-length E/A_lit disagreement (bounded)",
          cnt['same length (E strict, A_lit not)'] == 0
          and cnt['same length (A_lit strict, E not)'] == 0)

    print()
    print("=" * 78)
    print("E. The transfer table, rendered (every STRICT is a certified ratio > 1)")
    print("=" * 78)

    # E1. candidate-universe inclusion.  Which direction transfers what.
    #      `strict_up` is the negative-transfer lemma (a subclass witness
    #      refutes any superclass); `max_lift` is its failing converse.  The
    #      last row records that the literal flow-feasible class is NOT
    #      contained in the support-spelled class (a literal flow may visit
    #      only a *subset* of the observed read types), so the three §6.2
    #      readings branch instead of nesting.
    print("  E1. candidate-universe inclusion edges")
    print("  %-36s %-20s %-20s" % ("edge (sub ⊂ super)",
                                   "strict witness", "maximizer theorem"))
    for sub, sup, inclusion, note in [
            ("length-G candidates", "free length", True,
             "same-length witness reaches the free class"),
            ("§6.2-spelled candidates", "free length", True,
             "#24/#40 reach every superset"),
            ("genuine §6.2 candidates", "§6.2-spelled", True,
             "genuine62_support_eq gives the bridge"),
            ("literal §6.2 flow class", "free length", True,
             "the #88 witness ABAB reaches the free class"),
            ("§6.2-spelled candidates", "literal §6.2 flow class", False,
             "no inclusion either way: they branch")]:
        if inclusion:
            strict, lift = "TRANSFERS outward", "does NOT lift"
        else:
            strict, lift = "no transfer (no incl.)", "does NOT lift"
        print("  %-36s %-20s %-20s %s" % ("%s -> %s" % (sub, sup), strict, lift,
                                          note))

    # E2. per-witness status in every interpretation cell.
    cells = [(obj, panel) for obj in ("E", "A'", "A_lit")
             for panel in ("oriented", "molecular")]
    print("  E2. witness x interpretation cell")
    print("  %-24s %-5s | %s" % ("witness", "|D|=G",
                                " ".join("%-9s" % ("%s/%s" % c) for c in cells)))
    for r in docs + new:
        row = []
        for obj, panel in cells:
            suffix = 'or' if panel == 'oriented' else 'mol'
            v = {'E': 'rE', "A'": 'rAp', 'A_lit': 'rAl'}[obj]
            val = r[v + '_' + suffix]
            if val is None:
                row.append('n/a')
            elif val == 0:
                row.append('D=0')
            elif val > 1:
                row.append('STRICT')
            elif val == 1:
                row.append('tie')
            else:
                row.append('<1')
        print("  %-24s %-5s | %s" % (r['tag'], r['G'] == r['m'],
                                    " ".join("%-9s" % s for s in row)))
    print("  n/a  = panel undefined (abstract alphabet: no complement map)")
    print("  D=0  = the competitor cannot spell an observed read type under")
    print("         that panel, so its likelihood there is 0 (not a witness)")
    print("  <1   = the competitor is strictly *worse* (not a counterexample)")

    # E3. the four conclusion schemas, per witness: which one does this
    #     witness refute?  STRICT refutes all four; a tie refutes only
    #     uniqueness-up-to-r, and only when r does not identify D with S.
    print("  E3. schema reach of each witness")
    print("      (dominance / maximizer-with-membership / conditional /")
    print("       uniqueness-up-to-rotation / uniqueness-up-to-dihedral)")
    for r in docs + new:
        strict = any(v is not None and v > 1 for v in
                     (r['rE_or'], r['rE_mol'], r['rAp_or'], r['rAp_mol'],
                      r['rAl_or'], r['rAl_mol']))
        tied = any(v == 1 for v in
                   (r['rE_or'], r['rE_mol'], r['rAp_or'], r['rAp_mol'],
                    r['rAl_or'], r['rAl_mol']))
        if strict:
            reach = "all five: strictness alone refutes every schema"
        elif tied:
            if r['disjoint']:
                reach = ("uniqueness only, under BOTH equivalences "
                         "(D is neither a rotation nor an rc of S)")
            elif r['D'] in rots(r['S']):
                reach = ("uniqueness only under ROTATION; refuted there, "
                         "and refuted under dihedral too")
            elif r['is_dna'] and r['D'] == rc(r['S']):
                reach = ("uniqueness only under ROTATION: refuted by the "
                         "rotation-only equivalence, NOT by dihedral (D = rc(S))")
        else:
            reach = "none: the competitor is strictly worse in every panel"
        print("  %-24s %s" % (r['tag'], reach))

    print()
    failed = [n for n, c in checks if not c]
    print("checks passed: %d / %d" % (len(checks) - len(failed), len(checks)))
    if failed:
        print("FAILED:")
        for n in failed:
            print("   ", n)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
