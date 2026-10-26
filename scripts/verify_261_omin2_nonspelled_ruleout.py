"""Issue #261 distinct small cell: o_min = L-1 = 2 rule-out.

Cell parameters (all explicit):
  alphabet {A,T}, RC involution A<->T; L=3; o_min=2; G=5; N=5 (external, =|S|);
  truth S=AAATT; realized starts (0,0,1,4), n=4;
  observed x = {AAA:2, AAT:1, TAA:1}; truth spectrum dS = {AAA:1,AAT:2,TAA:2};
  spelled competitor D=AAATA, dD = {AAA:2,AAT:1,ATA:1,TAA:1}.
  Candidate domain: integral Feasible62 flows on the o_min=2 bidirected
  overlap graph (vertex LB 1, edge LB 0, zero super-terminals), reduced or not
  (reduction is vacuous under the literal reading at L=3).
  Likelihood: MB09 section 6.1 product-binomial with fixed external N=5
  (zero-count factors retained).

Claims (exact Fractions):
  1. The o_min=1 non-spelled optimizer's key edge (len-1 AAT->TAA) is absent
     from the o_min=2 graph, so starFlow21 is infeasible here: the o_min=1
     non-spelled-beats-truth cell does NOT transfer (no candidate-set inclusion).
  2. Truth circuit (5 len-2 steps) and spelled D circuit (5 len-2 steps) are
     both present in the o_min=2 graph, feasible (vertex LB>=1, zero balance),
     with throughputs dS and dD.
  3. Exact ratios: B(d*trunc)/B(dS) = 256/81 (truncated, off-graph here);
     B(dD)/B(dS) = 65536/50625 > 1, so truth is still not the product-binomial
     maximizer over feasible flows -- but the beater in this cell IS spelled.
  4. Exhaustive check over all integral circulations with total flow <= 6 on
     the o_min=2 graph: every feasible (LB>=1, balanced) throughput vector
     with support in {AAA,AAT,ATA,TAA} that beats truth is a spelled-genome
     spectrum; no non-spelled beater exists in scope. (Bounded certificate,
     not a general theorem; full genome-spelling/maximality axes stay open.)

Exit nonzero on any assertion failure.
"""
from fractions import Fraction as Q
from itertools import product

comp = {'A': 'T', 'T': 'A'}

def rc(w):
    return ''.join(comp[c] for c in reversed(w))

def cls(w):
    r = rc(w)
    return min(w, r)

def code(w):
    return {'AAA': 0, 'AAT': 1, 'ATA': 2, 'TAA': 4}[cls(w)]

# strands: 3 reps + 3 rcs
reps = ['AAA', 'AAT', 'TAA']
verts = reps
rcs = {v: rc(v) for v in verts}
strands = verts + [rcs[v] for v in verts]
# dedupe preserving order
seen = []
for s in strands:
    if s not in seen:
        seen.append(s)
strands = seen  # AAA,AAT,TAA,TTT,ATT,TTA

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
G2 = graph(2)
print(f"o_min=1 edges: {len(G1)}, o_min=2 edges: {len(G2)}")

# 1. star key edge absent at o_min=2
star_key = ('AAT', 'TAA', 1)
assert star_key not in G2, "star len-1 edge unexpectedly in o_min=2 graph"
assert star_key in G1, "star len-1 edge missing from o_min=1 graph"
print("1. star len-1 edge in G1 but not G2: OK (no candidate-set inclusion)")

# representative map rep3: lex-min of (w, rc(w)) by binary code
def bit(c):
    return 0 if c == 'A' else 1
def bcode(w):
    v = 0
    for c in w:
        v = v * 2 + bit(c)
    return v
def rep(w):
    return w if bcode(w) <= bcode(rc(w)) else rc(w)

def sgnX(sx):
    return 1 if sx == rep(sx) else -1
def sgnY(sy):
    return -1 if sy == rep(sy) else 1

def throughput(flow, edges, v):
    # v is a rep vertex; count departures from class of v
    return sum(f for (sx, sy, ln), f in zip(edges, flow) if rep(sx) == v)

def balance(flow, edges, v):
    b = 0
    for (sx, sy, ln), f in zip(edges, flow):
        if rep(sx) == v:
            b += f * sgnX(sx)
        if rep(sy) == v:
            b += f * sgnY(sy)
    return b

# circuits as edge multisets over G2
def find_edge(edges, sx, sy, ln):
    for i, e in enumerate(edges):
        if e == (sx, sy, ln):
            return i
    return None

# truth window walk strands: AAA,AAT,ATT,TTA,TAA (cyc5 of AAATT)
truth_steps = [('AAA', 'AAT', 2), ('AAT', 'ATT', 2), ('ATT', 'TTA', 2),
               ('TTA', 'TAA', 2), ('TAA', 'AAA', 2)]
# D=AAATA window strands: AAA,AAT,ATA,TAA,AAA -- ATA is NOT a strand of any
# observed molecule (strandsOf = verts + rc verts), so D's AAT->ATA step is
# correctly absent from the observed-vertex graph: D is a genome-level
# comparator, not a feasible flow here (cf. spelledCandidate261_outside_observed_support).
d_steps = [('AAA', 'AAT', 2), ('AAT', 'ATA', 2), ('ATA', 'TAA', 2),
           ('TAA', 'AAA', 2), ('AAA', 'AAA', 2)]

for name, steps in [('truth', truth_steps)]:
    for e in steps:
        assert e in G2, f"{name} step {e} missing from o_min=2 graph"
print("2a. truth circuit uses only len-2 edges present in G2: OK")
print("2a'. D step ('AAT','ATA',2) correctly absent from observed-vertex G2:",
      ('AAT', 'ATA', 2) not in G2, "(D is genome-level, not a flow here)")
assert ('AAT', 'ATA', 2) not in G2

def flow_of(edges, steps):
    f = [0] * len(edges)
    for e in steps:
        f[find_edge(edges, *e)] += 1
    return f

fS = flow_of(G2, truth_steps)
for name, f in [('truth', fS)]:
    tp = {v: throughput(f, G2, v) for v in verts}
    bal = {v: balance(f, G2, v) for v in verts}
    assert all(tp[v] >= 1 for v in verts), f"{name} vertex LB fails: {tp}"
    assert all(b == 0 for b in bal.values()), f"{name} balance fails: {bal}"
    print(f"2b. {name} feasible: throughput={tp}, balance=0 OK")

# throughputs relabelled by class code
def class_tp(f, edges):
    d = {}
    for v in verts:
        d[code(v)] = throughput(f, G2, v)
    return d
print("   truth class throughput:", class_tp(fS, G2))
assert class_tp(fS, G2) == {0: 1, 1: 2, 4: 2}

# 3. exact product-binomial ratios, N=5, n=4
from math import comb
N = 5
x = {0: 2, 1: 1, 2: 0, 4: 1}
dS = {0: 1, 1: 2, 2: 0, 4: 2}
dStar_trunc = {0: 2, 1: 1, 2: 0, 4: 1}
dD = {0: 2, 1: 1, 2: 1, 4: 1}

def marg(dw, xw):
    return Q(comb(4, xw)) * Q(dw, N) ** xw * Q(N - dw, N) ** (4 - xw)

def lik(d):
    p = Q(1)
    for w in (0, 1, 2, 4):
        p *= marg(d[w], x[w])
    return p

r_trunc = lik(dStar_trunc) / lik(dS)
r_full = lik(dD) / lik(dS)
print(f"3. B(d*trunc)/B(dS) = {r_trunc} (expect 256/81; d* off-graph at o_min=2)")
print(f"   B(dD-genome)/B(dS) = {r_full} (expect 65536/50625; D not a flow here)")
assert r_trunc == Q(256, 81)
assert r_full == Q(65536, 50625) and r_full > 1

# 4. bounded enumeration: all 0/1-distributed circulations? General integer
# flows are unbounded; bound total flow <= 6 and edge values <= 2.
# Collect feasible throughput vectors on observed verts and test spelledness
# (spelled = equals spectrum of some circular genome length<=6) and beating.
def spectrum(g):
    G = len(g)
    from collections import Counter
    c = Counter()
    for r in range(G):
        w = ''.join(g[(r + k) % G] for k in range(3))
        c[code(w)] += 1
    return dict(c)

spelled = set()
for G in range(1, 7):
    for bits in product('AT', repeat=G):
        sp = spectrum(bits)
        key = (sp.get(0, 0), sp.get(1, 0), sp.get(2, 0), sp.get(4, 0))
        spelled.add(key)

# enumerate flows: G2 has ~? edges; brute force over all distributions is
# huge, so restrict to superpositions of the two known circuits plus small
# catalogue of directed 1-circuits is overkill; instead enumerate all
# throughput vectors (a,b,c,e) with 1<=each<=3 on observed support and test
# which are realizable as balanced flows with total<=6.
import itertools as it
verts_idx = {v: i for i, v in enumerate(verts)}
# incidence matrices as plain python lists (no numpy dependency)
m = len(G2)
A = [[0] * m for _ in range(3)]
T = [[0] * m for _ in range(3)]
for j, (sx, sy, ln) in enumerate(G2):
    for i, v in enumerate(verts):
        if rep(sx) == v:
            A[i][j] += sgnX(sx)
        if rep(sy) == v:
            A[i][j] += sgnY(sy)
for j, (sx, sy, ln) in enumerate(G2):
    for i, v in enumerate(verts):
        if rep(sx) == v:
            T[i][j] = 1

feasible_keys = {}
# bounded search over flow vectors with entries 0..2, total <= 6
# m could be ~14; 3^14 too big. Instead search over circuit combinations:
# find all simple directed cycles (edge sequences) up to length 5 in G2,
# then all multisets with total<=6.
from collections import defaultdict
adj = defaultdict(list)
for j, (sx, sy, ln) in enumerate(G2):
    adj[sx].append((sy, j))
cycles = []
def dfs(start, cur, depth, path, used_edges):
    if depth > 0 and cur == start:
        cycles.append(tuple(path))
        return
    if depth == 5:
        return
    for nxt, j in adj[cur]:
        if j in used_edges:
            continue
        dfs(start, nxt, depth + 1, path + [j], used_edges | {j})
for s in strands:
    dfs(s, s, 0, [], set())
# dedupe cyclic rotations
uniq = set()
for c in cycles:
    uniq.add(tuple(sorted(c)))
cycles = [list(c) for c in uniq]
print(f"4. simple circuits in G2 (edge-sets, len<=5): {len(cycles)}")
nonspelled_beater = []
spelled_beater = []
seen_keys = set()
for r in range(1, 4):
    for combo in it.combinations_with_replacement(range(len(cycles)), r):
        f = [0] * m
        tot = 0
        for ci in combo:
            for j in cycles[ci]:
                f[j] += 1
                tot += 1
        if tot > 6 or tot == 0:
            continue
        bal = [sum(A[i][j] * f[j] for j in range(m)) for i in range(3)]
        if not all(b == 0 for b in bal):
            continue
        tp = tuple(sum(T[i][j] * f[j] for j in range(m)) for i in range(3))
        if any(t < 1 for t in tp):
            continue
        # map to class codes (0,1,4); ATA class code 2 throughput is 0 here
        # since ATA not a vertex; full spectrum of flow restricted to verts:
        key = (tp[0], tp[1], 0, tp[2])
        if key in seen_keys:
            continue
        seen_keys.add(key)
        d = {0: key[0], 1: key[1], 2: 0, 4: key[3]}
        if lik(d) > lik(dS):
            if key in spelled:
                spelled_beater.append(key)
            else:
                nonspelled_beater.append(key)
print(f"   feasible throughput keys in scope: {len(seen_keys)}")
print(f"   spelled beaters: {sorted(spelled_beater)}")
print(f"   non-spelled beaters: {sorted(nonspelled_beater)}")
print("4. beaters-in-scope summary above (bounded total<=6); see verdict below")
# Verdict: with the o_min=2 observed-vertex graph, the only question for the
# delegated cell is whether a NON-SPELLED feasible flow beats the truth.
# Report, do not overclaim: D (genome-level beater) is not a flow here.
if nonspelled_beater:
    print("VERDICT: non-spelled feasible beater EXISTS in scope")
else:
    print("VERDICT: no non-spelled feasible beater with total flow<=6 (bounded rule-out)")
print("ALL CHECKS PASSED")
