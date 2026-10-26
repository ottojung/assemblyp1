#!/usr/bin/env python3
"""Issue #261 new slice: o_min=1 spelled-circuit maximality under EXACT iid likelihood.

Cell (distinct from the o_min=2 non-spelled fixed-N cell of 7e31395):
  - Alphabet {A,T}, RC involution A<->T, read length L=3.
  - Overlap threshold o_min=1 (< L-1=2): genuine variable-overlap graph
    (both len-1 and len-2 edges); transitive reduction is NON-vacuous here.
  - Truth S = AAATT (G=5); realized starts (0,0,1,4), n=4,
    observed x = {AAA:2, AAT:1, TAA:1} (molecule classes).
  - Candidate class: SPELLED closed-walk circuits (vertices may repeat) with
    m <= 6 steps; each spells its own circular genome of length
    G = sum of advances (variable length universe, G in 1..12).
  - Truth admission: the truth window walk is a closed walk in G1 (verified).
  - Likelihood: EXACT iid prod_c (d_c/G)^{x_c} with per-candidate N=G
    (cross-length comparable); fixed-N=5 binomial reported secondarily for the
    G=5 sub-universe only (fixed-N is undefined across lengths).
  - Length universe: variable per-candidate spelled length (not fixed N).

Scope: bounded (m<=6). Exhaustive closed-walk enumeration, exact Fractions.
Exit nonzero on any failed assertion.
"""
from fractions import Fraction as Q

comp = {'A': 'T', 'T': 'A'}

def rc(w):
    return ''.join(comp[c] for c in reversed(w))

def cls(w):
    return min(w, rc(w))

reps = ['AAA', 'AAT', 'TAA']
strands = ['AAA', 'AAT', 'TAA', 'TTT', 'ATT', 'TTA']

def suffix_pre_match(a, b, ln):
    return a[3 - ln:] == b[:ln]

def graph(o_min):
    E = []
    for sx in strands:
        for sy in strands:
            for ln in range(o_min, 3):
                if suffix_pre_match(sx, sy, ln):
                    E.append((sx, sy, ln))
    return E

G1 = graph(1)
print(f"G1 edges: {len(G1)} (expect 28)")
assert len(G1) == 28

# --- transitive reduction: keep max-ln edge per ordered pair ---
def reduced(edges):
    best = {}
    for (sx, sy, ln) in edges:
        if (sx, sy) not in best or ln > best[(sx, sy)]:
            best[(sx, sy)] = ln
    return sorted((sx, sy, ln) for (sx, sy), ln in best.items())

R1 = reduced(G1)
print(f"reduced G1 edges: {len(R1)}")
assert len(R1) < len(G1), "reduction vacuous: not the intended non-vacuous cell"
removed = [e for e in G1 if e not in R1]
print(f"  removed {len(removed)} len-1 edges shadowed by len-2 edges, e.g. {removed[:3]}")

# --- spelling: closed walk -> circular genome ---
def spell(walk):
    # walk: list of (sx, sy, ln); must be closed (last sy == first sx)
    s = walk[0][0]
    for (sx, sy, ln) in walk:
        s += sy[ln:]
    A = len(s) - 3
    assert A >= 1
    return s[:A]  # circular genome of length A... verify closure below

def windows_circ(g, L=3):
    n = len(g)
    return [''.join(g[(t + j) % n] for j in range(L)) for t in range(n)]

def spectrum(g):
    from collections import Counter
    return Counter(cls(w) for w in windows_circ(g))

# truth walk spells AAATT (up to rotation)
truth_steps = [('AAA', 'AAT', 2), ('AAT', 'ATT', 2), ('ATT', 'TTA', 2),
               ('TTA', 'TAA', 2), ('TAA', 'AAA', 2)]
for e in truth_steps:
    assert e in G1
gS = spell(truth_steps)
print(f"truth walk spells: {gS}")
assert sorted(gS) == sorted('AAATT') and len(gS) == 5, gS  # rotation of AAATT
# closure check: spelled genome's windows must contain the walk vertices
ws = windows_circ(gS)
assert all(sy in ws for (_, sy, _) in truth_steps), "walk not a window-walk of spelled genome"
print("1. truth admitted as spelled closed walk at o_min=1: OK")

# observed counts (molecule classes)
x = {'AAA': 2, 'AAT': 1, 'TAA': 1}
n = 4

def exact_score(d, G):
    s = Q(1)
    for c, cnt in x.items():
        s *= Q(d.get(c, 0), G) ** cnt
    return s

dS = spectrum(gS)
sS = exact_score(dS, 5)
print(f"2. truth spectrum {dict(dS)}, exact-iid score = {sS} = {float(sS):.6f}")

# --- exhaustive closed-walk enumeration, m <= 6 ---
from collections import defaultdict
adj = defaultdict(list)
for e in G1:
    adj[e[0]].append(e)

MMAX = 6
outcomes = {}  # (G, sorted spectrum tuple, reduced-reachable) -> example walk
def dfs(start, cur, depth, walk):
    if depth >= 1 and cur == start:
        g = spell(walk)
        G = len(g)
        d = spectrum(g)
        key = (G, tuple(sorted(d.items())))
        if key not in outcomes:
            outcomes[key] = (list(walk), g)
    if depth == MMAX:
        return
    for e in adj[cur]:
        walk.append(e)
        dfs(start, e[1], depth + 1, walk)
        walk.pop()

for s0 in strands:
    dfs(s0, s0, 0, [])
print(f"3. distinct (G, spectrum) outcomes from closed walks m<={MMAX}: {len(outcomes)}")

# score all outcomes
ranked = sorted(outcomes.items(), key=lambda kv: exact_score(dict(kv[0][1]), kv[0][0]), reverse=True)
best_key, (best_walk, best_g) = ranked[0]
best_score = exact_score(dict(best_key[1]), best_key[0])
print(f"4. exact-iid winner in scope: G={best_key[0]} genome={best_g} "
      f"spectrum={dict(best_key[1])} score={best_score} (truth={sS})")
print(f"   winner walk ({len(best_walk)} steps): {best_walk}")

beaters = [(k, v) for k, v in ranked
           if exact_score(dict(k[1]), k[0]) > sS]
print(f"5. spelled beaters of truth in scope (m<={MMAX}, exact iid): {len(beaters)}")
for k, (w, g) in beaters[:10]:
    print(f"    G={k[0]} genome={g} spectrum={dict(k[1])} "
          f"score={exact_score(dict(k[1]), k[0])} steps={len(w)}")

# --- reduction invariance: which outcomes survive on the reduced graph? ---
adjR = defaultdict(list)
for e in R1:
    adjR[e[0]].append(e)
rout = {}
def dfsR(start, cur, depth, walk):
    if depth >= 1 and cur == start:
        g = spell(walk)
        G = len(g)
        d = spectrum(g)
        key = (G, tuple(sorted(d.items())))
        if key not in rout:
            rout[key] = (list(walk), g)
    if depth == MMAX:
        return
    for e in adjR[cur]:
        walk.append(e)
        dfsR(start, e[1], depth + 1, walk)
        walk.pop()
for s0 in strands:
    dfsR(s0, s0, 0, [])
print(f"6. distinct outcomes on REDUCED graph (m<={MMAX}): {len(rout)} "
      f"(full: {len(outcomes)})")
rranked = sorted(rout.items(), key=lambda kv: exact_score(dict(kv[0][1]), kv[0][0]), reverse=True)
rbest = rranked[0]
print(f"   reduced-graph winner: G={rbest[0][0]} genome={rbest[1][1]} "
      f"score={exact_score(dict(rbest[0][1]), rbest[0][0])}")
red_same_winner = (rbest[0] == best_key)
print(f"   reduction preserves exact-iid winner in scope: {red_same_winner}")
rbeaters = [k for k in rout if exact_score(dict(k[1]), k[0]) > sS]
print(f"   spelled beaters of truth on reduced graph: {len(rbeaters)}")
truth_in_reduced = any(spell(truth_steps)[:5] == spell(truth_steps)[:5] for _ in [0])
# truth uses only len-2 edges -> survives reduction
assert all(e in R1 for e in truth_steps), "truth walk must survive reduction"
print("   truth walk survives transitive reduction (all len-2 edges): OK")

# --- fixed-N=5 sub-universe (secondary): only G=5 candidates comparable ---
g5 = [(k, v) for k, v in ranked if k[0] == 5]
print(f"7. G=5 spelled sub-universe: {len(g5)} distinct spectra")
for k, (w, g) in sorted(g5, key=lambda kv: exact_score(dict(kv[0][1]), 5), reverse=True)[:5]:
    print(f"    genome={g} spectrum={dict(k[1])} exact5={exact_score(dict(k[1]), 5)}")

# --- transfer: does the o_min=1 winner survive at o_min=L-1=2? ---
G2 = graph(2)
print(f"8. G2 edges: {len(G2)} (expect 10)")
assert len(G2) == 10
win_len1 = [e for e in best_walk if e[2] == 1]
print(f"   winner len-1 steps: {win_len1}")
assert len(win_len1) >= 1, "winner uses no len-1 edge: transfer question vacuous"
assert all(e not in G2 for e in win_len1), "winner len-1 step present at o_min=2?!"
print("   winner uses len-1 edges absent from G2: o_min=1 beater does NOT transfer")
print("   to o_min=2 (no candidate-set inclusion)")

print("VERDICT recorded above (bounded scope m<=6; open beyond).")
print("ALL CHECKS PASSED")
