#!/usr/bin/env python3
"""Exact Q(sqrt(73)) dual certificate and finite Eulerian approximants.

No external packages. Checks the full DNA de Bruijn graph, not just
the truth's positive read support.
"""
from collections import Counter
from fractions import Fraction as R
from itertools import product
from math import log


class Q:
    """Elements a+b*sqrt(73), with rational a,b."""
    def __init__(self, a=0, b=0):
        self.a, self.b = R(a), R(b)

    @staticmethod
    def cast(x):
        return x if isinstance(x, Q) else Q(x)

    def __add__(self, other):
        x = self.cast(other)
        return Q(self.a + x.a, self.b + x.b)

    __radd__ = __add__

    def __neg__(self):
        return Q(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-self.cast(other))

    def __rsub__(self, other):
        return self.cast(other) - self

    def __mul__(self, other):
        x = self.cast(other)
        return Q(self.a*x.a + 73*self.b*x.b,
                 self.a*x.b + self.b*x.a)

    __rmul__ = __mul__

    def __truediv__(self, other):
        x = self.cast(other)
        den = x.a*x.a - 73*x.b*x.b
        assert den
        return self * Q(x.a/den, -x.b/den)

    def __rtruediv__(self, other):
        return self.cast(other) / self

    def __eq__(self, other):
        x = self.cast(other)
        return self.a == x.a and self.b == x.b

    def positive(self):
        a, b = self.a, self.b
        if a >= 0 and b >= 0:
            return a > 0 or b > 0
        if a <= 0 and b <= 0:
            return False
        return 73*b*b > a*a if b > 0 else a*a > 73*b*b

    def __float__(self):
        return float(self.a) + float(self.b)*73**.5


def spectrum(word, length):
    return Counter("".join(word[(i+k) % len(word)]
                           for k in range(length))
                   for i in range(len(word)))


truth = "AAACAC"
L = 3
observed = spectrum(truth, L) + Counter({"AAC": 1})
assert observed == Counter({"AAA": 1, "AAC": 2, "ACA": 2,
                             "CAA": 1, "CAC": 1})
assert len(observed) == 5 and sum(observed.values()) == 7
q = {
    "AAA": Q(R(1, 7)),
    "AAC": Q(R(17, 42), -R(1, 42)),
    "ACA": Q(R(19, 84), R(1, 84)),
    "CAA": Q(R(17, 42), -R(1, 42)),
    "CAC": Q(-R(5, 28), R(1, 28)),
}
assert sum(q.values(), Q()) == Q(1)
assert all(v.positive() for v in q.values())
assert q["AAC"] == q["CAA"]
assert q["ACA"] == q["CAA"] + q["CAC"]
assert q["AAC"].b != 0   # No finite genome can have this law.

# Full directed de Bruijn balance on all 16 double-letter vertices.
vertices = ["".join(t) for t in product("ACGT", repeat=2)]
edges = ["".join(t) for t in product("ACGT", repeat=3)]
for v in vertices:
    assert sum((q.get(e, Q()) for e in edges if e[:2] == v), Q()) == sum(
        (q.get(e, Q()) for e in edges if e[1:] == v), Q())

# Exact KKT dual with strict slack on every unobserved edge.
phi = {v: Q() for v in vertices}
phi["AC"] = Q(7) - 2/q["AAC"]
phi["CA"] = 1/q["CAA"] - 7
assert (Q(3) + phi["AC"]).positive()    # -3 < phi_AC < 0
assert (Q(3) + phi["CA"]).positive()    # -3 < phi_CA < 0
assert (-phi["AC"]).positive() and (-phi["CA"]).positive()
for edge in edges:
    dual = Q(7) + phi[edge[:2]] - phi[edge[1:]]
    if edge in observed:
        assert Q(observed[edge]) / q[edge] == dual, edge
    else:
        assert dual.positive(), edge

# Realizable rational positive circulations approach the irrational law.
def spell(a, b, c):
    adj = {"AA": ["AA"]*a + ["AC"]*b,
           "AC": ["CA"]*(b+c),
           "CA": ["AC"]*c + ["AA"]*b}
    stack, trail = ["AA"], []
    while stack:
        v = stack[-1]
        if adj[v]:
            stack.append(adj[v].pop())
        else:
            trail.append(stack.pop())
    trail.reverse()
    assert len(trail) == a+3*b+2*c+1
    return "".join(v[-1] for v in trail[:-1])


def log_likelihood(p):
    return sum(n*log(p[e]) for e, n in observed.items())


sup = log_likelihood({e: float(v) for e, v in q.items()})
for k in (100, 1000, 10000):
    a = round(k*float(q["AAA"]))
    b = round(k*float(q["AAC"]))
    c = round(k*float(q["CAC"]))
    genome = spell(a, b, c)
    sp = spectrum(genome, 3)
    assert sp == Counter({"AAA": a, "AAC": b, "CAA": b,
                          "ACA": b+c, "CAC": c})
    assert log_likelihood({e: sp[e]/len(genome) for e in observed}) <= sup + 1e-9
    if k == 10000:
        assert sup - log_likelihood({e: sp[e]/len(genome) for e in observed}) < 1e-6

print("Full 64-edge exact KKT certificate: PASS")
print("Irrational uniquely optimal read law and rational approximants: PASS")
print("No maximizing circular genome: PROVED by dual + irrationality")
print("Log-likelihood supremum:", sup)
