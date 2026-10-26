# Bounded non-loop throughput-sign census (#263)

This note records an exact finite census extending the loop-only observation
without claiming a theorem for arbitrary incidence matrices. The executable
verifier is [`scripts/verify_issue263_nonloop_census.py`](../scripts/verify_issue263_nonloop_census.py).

## Exact matrix and sign conventions

For a directed graph with vertices `V` and listed directed edges `E`, vectors
`x ∈ ℤ^E` are in the tested kernel when

```
balance_v(x) = Σ_(tail(e)=v) x_e - Σ_(head(e)=v) x_e = 0  (all v)
total(x) = Σ_e x_e = 0.
```

The lift is source-oriented outflow `T_v(x) = Σ_(tail(e)=v) x_e`. A nonzero
kernel vector `g` is called Graver here exactly when no nonzero kernel vector
`h ≠ g` satisfies `h_e g_e ≥ 0` and `|h_e| ≤ |g_e|` for every edge. A
decomposition is conformal when all its summands obey the same coordinatewise
condition against the displacement. Lift-sign compatibility requires each
`T_v(g)` to have the sign of `T_v(delta)` or be zero, for every vertex.

All checks are integer-exact. For each displacement `delta` with coordinates
in `[-2,2]`, the verifier restricts candidate summands to the coordinate box
between zero and `delta`. It tests kernel membership for every such vector,
filters the conformal-minimal ones, and recursively enumerates all unordered
Graver decompositions (allowing repeated summands). Thus the result is a
complete census for the stated finite boxes and matrices, not random sampling.

## Result

The census covers all 63 nonempty simple directed graphs on three labeled
vertices (all subsets of the six non-loop arcs), with displacement radius 2.
No displacement in any graph lacks a throughput-sign-compatible conformal
Graver decomposition. Sixteen graphs in this class have at least one nonzero
kernel displacement. On the complete bidirected three-vertex graph specifically
the verifier checks 34 displacements and all 40 conformal Graver
decompositions; every displacement has at least one compatible decomposition.

Controls include the loop-free two-vertex directed 2-cycle, whose tested
balance-plus-total kernel has no nonzero displacements, and a changed-edge-list
mutation of the three-vertex graph, independently re-enumerated (36
displacements, 36 decompositions, none failing). These finite observations do
not prove the claim for multigraphs, larger vertex sets, larger displacements,
or arbitrary integer matrices. No part of the one-vertex loop-only pairing
proof is reused as a general argument.

## Reproduction

```
python3 scripts/verify_issue263_nonloop_census.py
```

This is a bounded computational result; it is not a Lean theorem and does not
close the general augmented-throughput decomposition gap. Extended-real
likelihood boundaries and the direct #261 historical candidate adapter remain
separate.
