#!/usr/bin/env python3
"""Exact checks of source-faithful selected repeats and RC-class ambiguity.

This is finite evidence, not a replacement for a general mathematical proof
and not Lean kernel-checking. See docs/rc-p2-molecule-ambiguity.md.
"""
from collections import Counter, defaultdict
from itertools import combinations

COMPLEMENT = str.maketrans("ACGT", "TGCA")

def rc(word):
    return word.translate(COMPLEMENT)[::-1]

def rotations(word):
    return {word[i:] + word[:i] for i in range(len(word))}

def windows(word, length):
    n = len(word)
    return ["".join(word[(i + j) % n] for j in range(length))
            for i in range(n)]

def rc_classes(word, length):
    return Counter(min(w, rc(w)) for w in windows(word, length))

def maximal_pair(word, length, a, b, ws):
    n = len(word)
    return (a != b and ws[a] == ws[b]
            and word[(a - 1) % n] != word[(b - 1) % n]
            and word[(a + length) % n] != word[(b + length) % n])

def maximal_triple(word, length, a, b, c, ws):
    n = len(word)
    return (len({a,b,c}) == 3 and ws[a] == ws[b] == ws[c]
            and len({word[(i-1)%n] for i in (a,b,c)}) > 1
            and len({word[(i+length)%n] for i in (a,b,c)}) > 1)

def interleaved(n,a,b,c,d):
    if len({a,b,c,d}) < 4:
        return False
    arc = lambda x: 0 < (x-a)%n < (b-a)%n
    return arc(c) != arc(d)

def p2_and_long_repeats(word, L):
    n=len(word)
    long_pairs=[]
    long_triples=[]
    all_long_repeats=[]
    for e in range(L-1,n):
        ws=windows(word,e)
        groups=defaultdict(list)
        for i,w in enumerate(ws):
            groups[w].append(i)
        for w,starts in groups.items():
            for a,b in combinations(starts,2):
                all_long_repeats.append((e,w,a,b))
                if maximal_pair(word,e,a,b,ws):
                    long_pairs.append((e,a,b))
            for a,b,c in combinations(starts,3):
                if maximal_triple(word,e,a,b,c,ws):
                    long_triples.append((e,a,b,c))
    bad_interleavings=[
        (p,q) for p,q in combinations(long_pairs,2)
        if interleaved(n,p[1],p[2],q[1],q[2])
    ]
    return not long_triples and not bad_interleavings, all_long_repeats

def check(L):
    assert L >= 2
    source="A"*L+"C"+"T"*(L-1)
    competitor="A"*L+"G"+"T"*(L-1)
    assert len(source)==len(competitor)==2*L
    for word in [source,competitor]:
        assert all(word != word[:d]*(len(word)//d)
                   for d in range(1,len(word)) if len(word)%d==0)
    assert competitor not in rotations(source)
    assert competitor not in rotations(rc(source))
    assert Counter(windows(source,L)) != Counter(windows(competitor,L))
    assert rc_classes(source,L)==rc_classes(competitor,L)
    for word in [source,competitor]:
        holds,all_long_repeats=p2_and_long_repeats(word,L)
        assert holds, (L,word)
        assert all_long_repeats == [(L-1,"A"*(L-1),0,1)],(
            L,word,all_long_repeats)
    return source,competitor

if __name__ == "__main__":
    for L in range(2,13):
        S,D=check(L)
        print(f"L={L}: {S} vs {D}: primitive P2 and RC-law twins")
    print("primitive P2 reverse-complement-class ambiguity: PASS")
