#!/usr/bin/env python3
"""Connectivity-filtered I_s census for issue #272 (connected decoder gap).

Ports the elementary distinct-read overlap-connectivity filter from
docs/source-notes/issue272-connected-decoder-gap.md (tutelage handoff,
commit 4ae4b28) into a runnable repo enumerator. Bounded census
(G in {4,5,6}, k in {2,3} with k^G<=3000), plus a separately bounded
G=7,k=2 census: certainty-holding I_s failures
split total/connected, plus the concrete connected triple-clause witness
(AAAB, L=3, R=(1,2,3), Y={AAB,ABA,BAA}, directed 3-cycle).

Connectivity here is elementary length-(L-1) overlap, NOT the pruned 2016
read-overlap graph; no claim about literal Not-So-Greedy output is made.
Run: python3 scripts/verify_272_connected_census.py
"""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_272_is_necessity import (window, readset, all_windows, canon,
    failing_clause, is_triple_occurrence, bridges_copy, match_starts,
    historical_covers)

def connected(Y, L):
    Y = list(Y)
    if len(Y) <= 1:
        return True
    adj = {a: set() for a in Y}
    for i, a in enumerate(Y):
        for b in Y[i+1:]:
            if a[1:] == b[:-1] or b[1:] == a[:-1]:
                adj[a].add(b); adj[b].add(a)
    seen, stack = {Y[0]}, [Y[0]]
    while stack:
        x = stack.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); stack.append(y)
    return len(seen) == len(Y)

# witness assertions: AAAB, L=3, R=(1,2,3)
s = (0,0,0,1); L = 3; R = (1,2,3)
Y = readset(s, L, R)
print("Y =", sorted(Y))
assert Y == frozenset({(0,0,1),(0,1,0),(1,0,0)}), Y
assert failing_clause(s, L, R) == "triple", failing_clause(s, L, R)
assert connected(Y, L), "witness must be connected"
# directed cycle check
def edge(a,b): return a[1:] == b[:-1]
assert edge((1,0,0),(0,0,1)) and edge((0,0,1),(0,1,0)) and edge((0,1,0),(1,0,0))
# singleton fibre
real = [t for t in itertools.product(range(2), repeat=4) if Y <= all_windows(t, L)]
assert {canon(t) for t in real} == {canon(s)} and len(real) == 4, real
print("witness OK: connected triple-failing singleton-fibre (directed 3-cycle)")

# disconnected check of old witness R=(0,2)
Yold = readset(s, L, (0,2))
print("old Y =", sorted(Yold), "connected =", connected(Yold, L))

# G<=6 filtered census (iterate over canonical non-constant genomes, all nonempty R)
tot = {"coverage":0,"triple":0,"interleaved":0}
con = {"coverage":0,"triple":0,"interleaved":0}
for G in (4,5,6):
    for k in (2,3):
        if k**G > 3000: continue
        gs = list(itertools.product(range(k), repeat=G))
        can = {t: canon(t) for t in gs}
        wins = {}
        for t in gs:
            for L2 in range(2, G):
                wins[(t,L2)] = all_windows(t, L2)
        for s2 in gs:
            if can[s2] != s2 or len(set(s2)) == 1: continue
            for L2 in range(2, G):
                for r in range(1, 2**G):
                    R2 = tuple(i for i in range(G) if r & (1 << i))
                    fc = failing_clause(s2, L2, R2)
                    if fc is None: continue
                    Y2 = readset(s2, L2, R2)
                    cs2 = can[s2]
                    if all(not (can[t] != cs2 and Y2 <= wins[(t,L2)]) for t in gs):
                        tot[fc] += 1
                        if connected(Y2, L2): con[fc] += 1
print("total     :", tot)
print("connected :", con)
assert (tot["coverage"],tot["triple"],tot["interleaved"]) == (3807,4584,0), tot
assert con["interleaved"] == 0
print("COUNTS MATCH handoff: total 3807/4584/0; connected triple>0, interleaved 0")

# Separately bounded G=7 binary extension (same canonical-genome,
# nonconstant, nonempty-start-subset, all-length filter as above).
G = 7; k = 2
gs = list(itertools.product(range(k), repeat=G))
can = {t: canon(t) for t in gs}
wins = {(t, L2): all_windows(t, L2) for t in gs for L2 in range(2, G)}
tot7 = {"coverage":0,"triple":0,"interleaved":0}
con7 = dict.fromkeys(tot7, 0)
for s2 in gs:
    if can[s2] != s2 or len(set(s2)) == 1: continue
    for L2 in range(2, G):
        for r in range(1, 2**G):
            R2 = tuple(i for i in range(G) if r & (1 << i))
            fc = failing_clause(s2, L2, R2)
            if fc is None: continue
            Y2 = readset(s2, L2, R2); cs2 = can[s2]
            if all(not (can[t] != cs2 and Y2 <= wins[(t, L2)]) for t in gs):
                tot7[fc] += 1
                if connected(Y2, L2): con7[fc] += 1
print("G=7,k=2 total:", tot7)
print("G=7,k=2 connected:", con7)
assert (tot7["coverage"], tot7["triple"], tot7["interleaved"]) == (396, 2100, 0)
assert (con7["coverage"], con7["triple"], con7["interleaved"]) == (228, 810, 0)
