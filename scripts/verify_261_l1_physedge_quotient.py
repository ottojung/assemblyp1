#!/usr/bin/env python3
"""
L1 source-graph correspondence cross-check for #261.

Candidate mapping (the increment under test): the PHYSICAL RC overlap multigraph
edge is identified with a reversal orbit (PhysEdge quotient) of tagged signed
edges, preserving edge multiplicity and signed self-loop incidence.

Model (content-tracking interpretation of `Tagged W = W x Bool`):
  * a tagged strand is (word, bit);  cls (w,b) = (w,0) is the class
    representative, flip (w,b) = (w,1-b) is the other strand of the class;
  * the STRING content of a tagged strand is `word` when bit = 0 and `rc word`
    when bit = 1  (this is the content-tracking `toList`: the bit records
    whether the reverse complement has been taken);
  * a tagged edge is (sx, sy, len, sgnX, sgnY)  (BdEdge);
  * bdEdge rep sx sy len has sgnX = +1 iff sx is the class representative
    (bit 0) and sgnY = -1 iff sy is the class representative;
  * reverseEdge (sx,sy,len,sgnX,sgnY) = (flip sy, flip sx, len, sgnY, sgnX);
  * posHalf/negHalf count signed half-incidences at a class, separately at each
    endpoint (so a mixed-sign loop contributes one of each);
  * overlapEdges enumerates (sx, sy, len) with oMin <= len < readLen and
    suf(content sx, len) = pre(content sy, len).

The physical edge is the reversal orbit.  The check verifies, exhaustively on a
bounded family of small overlap graphs (few edges, multiplicities 1-2, signed
self-loops included):

  W1  well-definedness: every tagged edge in one orbit determines the same
      (unordered endpoint classes, length, sign at each endpoint class);
  W2  fibre size: every orbit has exactly 1 or 2 tagged representatives;
  W3  loop incidence: for a loop orbit, (posHalf, negHalf) at the class is
      constant on the orbit and lies in {(1,1),(2,0),(0,2)};
  W4  multiplicity: the set of orbits between two classes with a fixed length
      equals the set of physical strand-overlap edges (counted independently as
      RC-classes of ordered strand pairs);
  W5  every non-loop orbit has fibre size 2, and the two mixed-type edges
      between distinct classes are DISTINCT orbits;
  W6  sign-at-endpoint is a function of the orbit (not of the representative).

Exit 0 iff all checks pass.  Any failure prints the minimal failing instance.
"""

from itertools import combinations, product

# ---------------------------------------------------------------------------
# Literal transcription of the Lean model (content-tracking)
# ---------------------------------------------------------------------------

def rc_word(w):
    return ''.join('1' if c == '0' else '0' for c in reversed(w))

def content(s):
    """String content of a tagged strand: rc applied when the bit is 1."""
    return rc_word(s[0]) if s[1] == 1 else s[0]

def cls(s):
    return (s[0], 0)

def flip(s):
    return (s[0], 1 - s[1])

def sgn_rep(s):
    return 1 if s[1] == 0 else -1

def sgn_tgt(s):
    return -1 if s[1] == 0 else 1

def bd_edge(sx, sy, length):
    return (sx, sy, length, sgn_rep(sx), sgn_tgt(sy))

def reverse_edge(e):
    sx, sy, length, sgnX, sgnY = e
    return (flip(sy), flip(sx), length, sgnY, sgnX)

def pos_half(e, v):
    sx, sy, _l, sgnX, sgnY = e
    return ((1 if cls(sx) == v and sgnX == 1 else 0)
            + (1 if cls(sy) == v and sgnY == 1 else 0))

def neg_half(e, v):
    sx, sy, _l, sgnX, sgnY = e
    return ((1 if cls(sx) == v and sgnX == -1 else 0)
            + (1 if cls(sy) == v and sgnY == -1 else 0))

def overlap_edges(reads, o_min, read_len):
    """Literal transcription of Section62Flow.overlapEdges (strandsOf included).

    strandsOf rc verts = verts ++ verts.map rc, lifted to Tagged W as
    (w,0) and (w,1) with content-tracking toList.
    """
    strands = []
    for w in reads:
        strands.append((w, 0))
        strands.append((w, 1))
    edges = []
    for length in range(read_len):
        if length < o_min:
            continue
        for sx in strands:
            for sy in strands:
                if content(sx)[read_len - length:] == content(sy)[:length]:
                    edges.append(bd_edge(sx, sy, length))
    return edges

# ---------------------------------------------------------------------------
# Orbit (PhysEdge quotient) construction
# ---------------------------------------------------------------------------

def rev_rel(e, e2):
    return e2 == e or e2 == reverse_edge(e)

def orbits_of(edges):
    """Partition the tagged edge list into reversal orbits (RevRel classes)."""
    remaining = list(edges)
    orbits = []
    while remaining:
        seed = remaining[0]
        orb = [e for e in remaining if rev_rel(seed, e)]
        orbits.append(orb)
        remaining = [e for e in remaining if not rev_rel(seed, e)]
    return orbits

def orbit_key(e):
    """The physical-edge invariant: (unordered classes, len, sign at each class).

    For a non-loop this is ('edge', w1, w2, len, sign_at_w1, sign_at_w2) with
    w1 <= w2.  For a loop it is ('loop', w, len, pos, neg).
    """
    sx, sy, length, sgnX, sgnY = e
    c1, c2 = cls(sx), cls(sy)
    if c1 == c2:
        return ('loop', c1[0], length, pos_half(e, c1), neg_half(e, c1))
    lo, hi = (c1[0], c2[0]) if c1[0] <= c2[0] else (c2[0], c1[0])
    s_lo = sgnX if c1[0] == lo else sgnY
    s_hi = sgnY if c2[0] == hi else sgnX
    return ('edge', lo, hi, length, s_lo, s_hi)

# ---------------------------------------------------------------------------
# Independent physical-edge count (RC-classes of ordered strand pairs)
# ---------------------------------------------------------------------------

def physical_edge_keys(c1, c2, read_len, length):
    """Independently count physical edges between classes c1,c2 at this length.

    A physical edge is an RC-class of ordered strand pairs (ax,bx) with
    suf(content ax,len)=pre(content bx,len).  For distinct classes there are 4
    RC-classes (fibre 2 each); for a loop there are 3 (fibres 2,1,1).
    """
    s1, n1 = (c1, 0), (c1, 1)
    s2, n2 = (c2, 0), (c2, 1)
    if c1 != c2:
        classes = [
            ((s1, s2), (n2, n1)),
            ((s1, n2), (s2, n1)),
            ((n1, s2), (n2, s1)),
            ((n1, n2), (s2, s1)),
        ]
    else:
        classes = [
            ((s1, s1), (n1, n1)),
            ((s1, n1),),
            ((n1, s1),),
        ]
    def satisfies(ax, bx):
        return content(ax)[read_len - length:] == content(bx)[:length]
    keys = set()
    for cl in classes:
        if any(satisfies(ax, bx) for (ax, bx) in cl):
            ax, bx = cl[0]
            e = bd_edge(ax, bx, length)
            keys.add(orbit_key(e))
    return keys

# ---------------------------------------------------------------------------
# Checks
# ---------------------------------------------------------------------------

def check_instance(reads, o_min, read_len, stats):
    edges = overlap_edges(reads, o_min, read_len)
    orbits = orbits_of(edges)
    classes = [(w, 0) for w in reads]

    # W1 + W6: well-definedness of the orbit key
    for orb in orbits:
        keys = {orbit_key(e) for e in orb}
        if len(keys) != 1:
            return f"W1/W6 FAIL reads={reads} o_min={o_min}: orbit {orb} has keys {keys}"

    # W2: fibre size 1 or 2
    for orb in orbits:
        if len(orb) not in (1, 2):
            return f"W2 FAIL reads={reads} o_min={o_min}: orbit size {len(orb)}: {orb}"

    # W3: loop incidence
    for orb in orbits:
        key = orbit_key(orb[0])
        if key[0] == 'loop':
            c = (key[1], 0)
            pn = {(pos_half(e, c), neg_half(e, c)) for e in orb}
            if len(pn) != 1:
                return f"W3 FAIL reads={reads} o_min={o_min}: loop orbit {orb} incidences {pn}"
            if next(iter(pn)) not in {(1, 1), (2, 0), (0, 2)}:
                return f"W3 FAIL reads={reads} o_min={o_min}: loop incidence not in {{(1,1),(2,0),(0,2)}}: {orb}"

    # W4: multiplicity -- orbit keys between two classes at a fixed length
    # equal the independently counted physical edges.
    def key_classes_len(k):
        if k[0] == 'loop':
            return {k[1]}, k[2]
        return {k[1], k[2]}, k[3]
    for i, c1 in enumerate(classes):
        for c2 in classes[i:]:
            for length in range(o_min, read_len):
                orb_keys = set()
                for orb in orbits:
                    k = orbit_key(orb[0])
                    cs, ln = key_classes_len(k)
                    if cs == {c1[0], c2[0]} and ln == length:
                        orb_keys.add(k)
                phys_keys = physical_edge_keys(c1[0], c2[0], read_len, length)
                if orb_keys != phys_keys:
                    return (f"W4 FAIL reads={reads} o_min={o_min} classes=({c1[0]},{c2[0]}) "
                            f"len={length}: orbits={orb_keys} physical={phys_keys}")

    # W5: every non-loop orbit has fibre size 2; the two mixed edges between
    # distinct classes are distinct orbits.
    for orb in orbits:
        key = orbit_key(orb[0])
        if key[0] == 'edge' and len(orb) != 2:
            return f"W5 FAIL reads={reads} o_min={o_min}: non-loop orbit size {len(orb)}: {orb}"
    mixed = [orbit_key(orb[0]) for orb in orbits
             if orbit_key(orb[0])[0] == 'edge'
             and {orbit_key(orb[0])[4], orbit_key(orb[0])[5]} == {1, -1}]
    if len(mixed) != len(set(mixed)):
        return f"W5 FAIL reads={reads} o_min={o_min}: mixed orbits not distinct: {mixed}"

    stats['instances'] += 1
    stats['edges'] += len(edges)
    stats['orbits'] += len(orbits)
    stats['loops'] += sum(1 for orb in orbits if orbit_key(orb[0])[0] == 'loop')
    return None

# ---------------------------------------------------------------------------
# Exhaustive driver
# ---------------------------------------------------------------------------

def main():
    stats = {'instances': 0, 'edges': 0, 'orbits': 0, 'loops': 0}
    failures = []

    # Family A: binary reads of length 3, all subsets of size 1..3, o_min in {1,2}.
    reads3 = [''.join(p) for p in product('01', repeat=3)]
    for k in (1, 2, 3):
        for subset in combinations(reads3, k):
            for o_min in (1, 2):
                err = check_instance(list(subset), o_min, 3, stats)
                if err:
                    failures.append(err)

    # Family B: binary reads of length 4, all subsets of size 1..2, o_min in {1,2,3}.
    reads4 = [''.join(p) for p in product('01', repeat=4)]
    for k in (1, 2):
        for subset in combinations(reads4, k):
            for o_min in (1, 2, 3):
                err = check_instance(list(subset), o_min, 4, stats)
                if err:
                    failures.append(err)

    # Family C: the audit's length-3 witness molecules {AAA,AAT,TAA} mapped to
    # binary {000,001,011} (A->0, T->1), o_min in {1,2}.
    for o_min in (1, 2):
        err = check_instance(['000', '001', '011'], o_min, 3, stats)
        if err:
            failures.append(err)

    print(f"instances checked : {stats['instances']}")
    print(f"tagged edges       : {stats['edges']}")
    print(f"physical orbits    : {stats['orbits']}")
    print(f"loop orbits        : {stats['loops']}")
    if failures:
        print(f"\nFAILURES: {len(failures)}")
        for f in failures[:10]:
            print("  " + f)
        raise SystemExit(1)
    print("\nALL CHECKS PASSED (W1-W6)")

if __name__ == '__main__':
    main()
