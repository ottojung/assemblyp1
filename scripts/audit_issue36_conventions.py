#!/usr/bin/env python3
"""Issue #36 convention audit for the AAATT -> AAAATT witness.

Exact-integer/Fraction, deterministic, self-contained. Exits non-zero on any
failed assertion. See docs/source-notes/issue36-convention-audit-aaatt.md.
"""
from fractions import Fraction as F
from itertools import product

COMP = {'A': 'T', 'T': 'A'}

def rc(w):
    return ''.join(COMP[c] for c in reversed(w))

def mol(w, collapse):
    if not collapse:
        return w
    r = rc(w)
    return w if w <= r else r

def windows(s, L):
    G = len(s)
    return [''.join(s[(i + j) % G] for j in range(L)) for i in range(G)]

def spec(s, L, collapse):
    d = {}
    for w in windows(s, L):
        k = mol(w, collapse)
        d[k] = d.get(k, 0) + 1
    return d

def binom_lik(d, x, N, n):
    val = F(1)
    for k in set(d) | set(x):
        dk = F(d.get(k, 0), N)
        xk = x.get(k, 0)
        if dk == 0 and xk > 0:
            return F(0)
        val *= dk ** xk * (1 - dk) ** (n - xk)
    return val

def exact_lik(d, x, G):
    val = F(1)
    for k in set(d) | set(x):
        dk = F(d.get(k, 0), G)
        xk = x.get(k, 0)
        if dk == 0 and xk > 0:
            return F(0)
        val *= dk ** xk
    return val

def dihedral_orbit(s):
    G = len(s)
    out = set()
    for base in (s, rc(s)):
        for i in range(G):
            out.add(''.join(base[(i + j) % G] for j in range(G)))
    return out

def rotations(s):
    G = len(s)
    return {''.join(s[(i + j) % G] for j in range(G)) for i in range(G)}

S, L, N, n = 'AAATT', 3, 5, 3
starts = (0, 1, 4)
assert len(S) == N == 5
obs = {}
for i in starts:
    obs[mol(windows(S, L)[i % len(S)], True)] = \
        obs.get(mol(windows(S, L)[i % len(S)], True), 0) + 1
assert obs == {'AAA': 1, 'AAT': 1, 'TAA': 1}, obs

dS = spec(S, L, True)
assert dS == {'AAA': 1, 'AAT': 2, 'TAA': 2}, dS
LS = binom_lik(dS, obs, N, n)
assert LS == F(5184, 1953125), LS

# --- (1) Circular vs linear: the start-4 read wraps -------------------------
lin_starts = range(N - L + 1)  # 0,1,2 for linear length-5 strings
assert 4 not in lin_starts
# linear truth AAATT has windows AAA,AAT,ATT only; TAA absent
lin_obs = [''.join(S[i + j] for j in range(L)) for i in lin_starts]
assert 'TAA' not in lin_obs, lin_obs

# --- (2) Reverse-complement read-type collapse is load-bearing -------------
dS_oriented = spec(S, L, False)
assert set(dS_oriented) == {'AAA', 'AAT', 'ATT', 'TTA', 'TAA'}, dS_oriented
assert not set(dS_oriented) <= set(obs), (dS_oriented, obs)
assert {'ATT', 'TTA'} & set(obs) == set()

# --- (3) Known genome length: no length-5 competitor beats the truth -------
def maximize(G, lik, base):
    best, best_set = None, []
    for s in map(''.join, product('AT', repeat=G)):
        d = spec(s, L, True)
        r = lik(d) / base
        if best is None or r > best:
            best, best_set = r, [(s, d)]
        elif r == best:
            best_set.append((s, d))
    return best, best_set

assert N == 5
best5, ties5 = maximize(5, lambda d: binom_lik(d, obs, N, n), LS)
assert best5 == 1, best5
tie_strings = {s for s, _ in ties5}
assert tie_strings == dihedral_orbit(S), (sorted(tie_strings),
                                          sorted(dihedral_orbit(S)))
assert len(tie_strings) == 10
assert len(tie_strings & rotations(S)) == 5
# every length-5 tie is revcomp/rotation of S, i.e. equivalent under dihedral
# but AATTT is a non-cyclic-shift tie
assert 'AATTT' in tie_strings and 'AATTT' not in rotations(S)
assert 'AATTT' == rc(S)

# same for the exact candidate-intrinsic-length objective at G = 5
LE = exact_lik(dS, obs, N)
best5e, ties5e = maximize(5, lambda d: exact_lik(d, obs, N), LE)
assert best5e == 1 and {s for s, _ in ties5e} == dihedral_orbit(S)

# --- (4) The 9/8 witness needs |D| = 6 > N; it is strict -------------------
D = 'AAAATT'
dD = spec(D, L, True)
assert dD == {'AAA': 2, 'AAT': 2, 'TAA': 2}, dD
LD = binom_lik(dD, obs, N, n)
assert LD / LS == F(9, 8), (LD, LS)
assert len(D) == 6 and len(D) != N

# the oriented (4^k) reading kills the witness: truth support not observed
assert not set(dS_oriented) <= set(obs)

# --- (5) Ties vs strict: 9/8 is strict, so both schemas are refuted --------
assert LD > LS  # truth is not a maximizer over variable-length candidates

# --- (6) §6.2 spellability of the length-5 ties ---------------------------
# All ties have support within the observed classes, so each is spellable on
# the observed-read overlap graph (molecule classes).
for s in sorted(tie_strings):
    d = spec(s, L, True)
    assert set(d) <= set(obs), (s, d)

print("AAATT convention audit: all assertions passed")
print("  observed x            :", obs)
print("  d_S                   :", dS)
print("  d_D (D=AAAATT)        :", dD)
print("  §6.1 ratio D/S        :", LD / LS)
print("  G=5 best ratio (binom):", best5, " ties:", len(tie_strings),
      "= dihedral orbit of S")
print("  non-rotation tie      : AATTT = rc(AAATT)")
print("  oriented window set   :", sorted(dS_oriented))
