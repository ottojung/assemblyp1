#!/usr/bin/env python3
"""Single-instance graph-to-score adapter for issue #261.

Instance: verts=[0,1], edges e0:0->1, e1:1->0, len=1=L-1, sgnX=+1, sgnY=-1,
zero terminals, vertexLB=1, edgeLB=0, external N=2.
Checks literal Admissible clauses, reduction vacuity, truth admission,
exact feasible fiber in box [0,3]^2, and fixed-N binomial non-defeat
over all full-support samples with n<=5.
"""
from itertools import product

N = 2
VERTS = [0, 1]
# edges: (src_class, tgt_class, sgnX, sgnY)
EDGES = [(0, 1, 1, -1), (1, 0, 1, -1)]
READLEN = 2

def throughput(f):
    d = {v: 0 for v in VERTS}
    for (s, t, sx, sy), val in zip(EDGES, f):
        d[s] += val
    return d

def balcore(f):
    b = {v: 0 for v in VERTS}
    for (s, t, sx, sy), val in zip(EDGES, f):
        b[s] += val * sx
        b[t] += val * sy
    return b

def admissible(f):
    if any(v < 0 for v in f):
        return False
    d = throughput(f)
    if any(d[v] < 1 for v in VERTS):
        return False
    b = balcore(f)
    if any(b[v] != 0 for v in VERTS):
        return False
    return True

# 1. reduction vacuity: isReducibleB needs 0 < len_j < e.len = 1 -> impossible
for e in EDGES:
    assert not any(0 < l1 < 1 and 0 < l2 < 1 for l1 in range(READLEN) for l2 in range(READLEN))
print("reduction-vacuous: OK")

# 2. enumerate box
feas = [f for f in product(range(4), repeat=2) if admissible(f)]
assert feas == [(1, 1), (2, 2), (3, 3)], feas
print("feasible-in-box [0,3]^2:", feas)

# 3. truth admission
truth = (1, 1)
assert admissible(truth)
dstar = throughput(truth)
assert dstar == {0: 1, 1: 1}, dstar
print("truth-admitted: f*=(1,1) d*=(1,1)")

# 4. probability-domain fiber
fiber = [f for f in feas if all(throughput(f)[v] <= N for v in VERTS)]
assert fiber == [(1, 1), (2, 2)], fiber
print("probability-domain fiber:", fiber)

def K(d, x):
    # d,x dicts; n = sum x
    n = sum(x.values())
    tot = 1
    for v in VERTS:
        tot *= (d[v] ** x[v]) * ((N - d[v]) ** (n - x[v]))
    return tot

def q(d, i):
    p = d[i]
    for j in VERTS:
        if j != i:
            p *= (N - d[j])
    return p

# 5. q-factorization identity K(d;x) = prod q_i(d)^{x_i} on samples
for d in ({0: 1, 1: 1}, {0: 2, 1: 2}):
    for n in range(2, 6):
        for x0 in range(1, n):
            x = {0: x0, 1: n - x0}
            assert K(d, x) == q(d, 0) ** x[0] * q(d, 1) ** x[1], (d, x)
print("q-factorization: OK")

# 6. non-defeat over all full-support samples n<=5
A = {0: 1, 1: 1}
for Bf in fiber:
    B = throughput(Bf)
    for n in range(2, 6):
        for x0 in range(1, n):
            x = {0: x0, 1: n - x0}
            assert K(B, x) <= K(A, x), (B, x, K(B, x), K(A, x))
print("truth sample-uniformly maximal over fiber (n<=5, full support): OK")

# 7. m-check inequalities P_B q_B(k)^t <= P_A q_A(k)^t
PA = q(A, 0) * q(A, 1)
for Bf in fiber:
    B = throughput(Bf)
    PB = q(B, 0) * q(B, 1)
    for t in range(0, 4):
        for k in VERTS:
            assert PB * (q(B, k) ** t) <= PA * (q(A, k) ** t), (B, t, k)
print("extreme-sample m-checks: OK")
print("ALL CHECKS PASS")
