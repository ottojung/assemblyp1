# Capacitated edge-type Eulerian spellings: a forced-safe-transition criterion

**Issue:** #83  
**Branch:** `agent/capacitated-criterion-83`  
**Scope:** same-length complete oriented spectra  
**Epistemic class:** mathematical proofs, except the literature-status paragraph, which is a source fact

## 1. Exact object

Let \(H=(V,E)\) be a finite directed multigraph. An edge type is a pair
\[
e=(u,v)\in V\times V,
\]
with a positive integer capacity \(c(e)\). Parallel labelled copies of the
same pair are indistinguishable.

A **capacitated edge-type spelling** is a cyclic sequence
\[
(e_0,\ldots,e_{G-1})
\]
such that

1. each edge type \(e\) occurs exactly \(c(e)\) times;
2. \(t(e_i)=s(e_{i+1})\), with indices modulo \(G\).

For an \(L\)-mer, use the order-\((L-1)\) de Bruijn graph. The pair
\((x_1\cdots x_{L-1},x_2\cdots x_L)\) is the edge type \(x_1\cdots x_L\),
and \(c(x_1\cdots x_L)\) is its spectrum multiplicity. Thus the usual
de Bruijn correspondence gives the exact same-length equivalence

> a singleton spectrum fibre modulo rotation is equivalent to a singleton
> capacitated edge-type spelling modulo rotation.

This part is a graph-theoretic restatement, not a new uniqueness theorem.
The substantive question is how to recognize the singleton.

## 2. Residual states and safe edge types

Fix a prefix of a spelling and let \(R\) be the residual capacitated
multigraph after deleting the prefix. By construction, \(R\) is balanced on
its support and has an Eulerian spelling beginning at the current vertex.
The state is \(R\), not merely the current vertex: a choice can be forced by
the residual edge multiplicities elsewhere in the graph.

For an available edge type \(e:v\to w\), call \(e\) **safe at \(R\)** when the
ordinary residual multigraph \(R-e\) has an Euler trail from \(w\) to \(v\).
Equivalently, the standard directed Euler-trail feasibility test succeeds:
the degree imbalance is \(+1\) at \(w\), \(-1\) at \(v\), and zero elsewhere,
and all residual edges lie in the required connected/reachable component of
that trail. The current graph is balanced, so the first conditions follow
automatically after deletion; connectivity and the endpoint-reachability
condition are the substantive test.

**Interpretation.** An edge type is safe exactly when some complete residual
spelling can begin with that type. Two copies of one safe type are one choice,
not two.

## 3. Forced-safe-transition theorem

> **Theorem.** Suppose \(C\) is the unique capacitated cyclic spelling. For
> every residual state \(R\) on the traversal of \(C\), exactly one available
> edge type is safe.

Equivalently, without assuming a known traversal:

> **Recognition theorem.** The capacitated edge-type spelling is unique up to
> rotation if and only if the residual-safe-choice procedure below never has
> two safe edge types at a reachable state.

The procedure starts with any known spelling \(C\). At the current state
\(R=(v,r)\), test every distinct outgoing edge type at \(v\).

- If there is exactly one safe type, traverse it and replace \(r(e)\) by
  \(r(e)-1\).
- If there are at least two safe types, report non-unique.
- If there is no safe type, the input was not a valid residual spelling.

Continue until every edge is consumed.

### Proof

**Recognition theorem.** Suppose at a reachable state two distinct edge types
\(e,f\) are safe. There are residual spellings \(C_e\) and \(C_f\) beginning
with the same prefix but with different next types. Appending the common
prefix to these words gives two edge-type spellings with the same edge-type
multiplicities. Since the next types differ at the same position, the words
are different even before taking rotation orbits. Hence the spelling is not
unique.

Conversely, suppose the procedure encounters no state with two safe types.
Every complete spelling beginning with the fixed prefix must start with a
safe type: its first edge, followed by the rest of that spelling, is an Euler
trail of the corresponding residual multigraph. Thus at every position the
next edge type is uniquely determined. Induction on the remaining capacity
shows that the entire spelling is determined. Since any cyclic spelling can
be rotated to begin at the chosen position, it is unique modulo rotation. ∎

The theorem is immediate as a recognition statement, but the forcedness
conclusion is stronger than “one known tour works”: it says that each next
type is present in **every** completion of the prefix.

### Complexity

For an ordinary multigraph of \(G\) edge instances, each Euler-trail
feasibility test is a linear-time degree/reachability test. A single state has
at most the current out-degree distinct types, and the unique safe path has
at most \(G\) states. With a fresh reachability test at each state, this gives
a polynomial-time procedure. This implementation does not establish the
linear running time of the labelled-edge theorem of Acosta--Tomescu. The
criterion also gives an early ambiguity certificate: the first state with two
safe types, together with the two feasible Euler-trail completions, is enough
to witness two spellings.

This is a safe-walk argument, not a claim of novelty. Acosta and Tomescu,
“Simplicity in Eulerian Circuits: Uniqueness and Safety”
(arXiv:2208.08522v2), give a linear-time forced-consecutive-edge
characterization for the ordinary labelled directed graph. The present proof
uses the standard residual Euler-trail test and adapts it to the quotient by
identical parallel edge instances. No source located in this packet was
found to state the adapted criterion, but absence of a located source is not
a novelty claim.

## 4. Natural forced-transition criteria

### 4.1 A single available type is sufficient, but far from necessary

If the current vertex has only one available outgoing edge type, that type is
forced. This ignores its residual capacity and is polynomial to check. It is
not an iff criterion: the binary example below has out-degree two at a
residual visit and still has a unique spelling.

### 4.2 The last-exit property is sufficient, but not necessary

A standard last-exit argument applies to labelled edges: after the last
departure from a vertex, all outgoing edges except the one used then must
already have been consumed. The familiar condition that all but one outgoing
edge have been removed is therefore sufficient to force the last exit.

For edge types, it must be stated for **types**, not copies. For example,
requiring a multiplicity to be one is unnecessarily strong: two copies of a
single available type are still one choice. The residual-safe criterion is
strictly more permissive because it can force a choice before all other
copies of competing types are exhausted.

### 4.3 A local degree or support condition is insufficient by itself

Balanced degrees, strong connectivity, and positive capacity do not force
uniqueness. At a single vertex, take two loop types \(a,b\) with capacities
two and one. The graph is strongly connected and balanced, but its cyclic
type words are `aab` and `aba` modulo rotation.

Capacities are decisive even on a small type support. Capacities \((2,1)\) on
loops \(a,b\) give two rotation orbits; capacities \((2,2)\) also give two;
capacities \((2,0)\) give one. Scaling all capacities need not preserve
uniqueness. On three loop types, \((2,2,1)\) and \((1,1,3)\) have different
numbers of type words. These one-vertex examples are abstract capacitated
graph witnesses. A de Bruijn graph has the more restricted property that two
edge instances with the same tail and head have the same edge type; the
binary example below is a direct de Bruijn witness.

## 5. Transparent de Bruijn example: branching is not ambiguity

Take \(L=2\), alphabet \(\{A,B\}\), and circular word `AABB`. Its
order-one de Bruijn multigraph has capacity-one edge types

\[
a:AA,\quad b:AB,\quad c:BB,\quad d:BA.
\]

The cyclic spelling is

\[
a\,b\,c\,d.
\]

At the visit to \(B\), both `b` and `d` leave. Nevertheless `d` is not safe
after prefix `ab`: it reaches \(A\), whose only incident edge `a` has already
been consumed, while `c` remains stranded. Every completion therefore has to
choose `b`; then `c` and `d` are forced. The result is unique modulo
rotation.

This refutes the tempting criterion “a branching vertex creates spectrum
ambiguity.” The relevant fact is residual completability, not current
out-degree.

## 6. Why labelled Euler-tour criteria need not transfer

Consider a one-vertex graph with two indistinguishable loop copies of the
same edge type. The capacitated type word is simply `aa`, uniquely up to
rotation. In the labelled multigraph there are multiple Euler tours obtained
by exchanging the two loop instances. A criterion demanding that the labelled
Euler circuit itself be unique is therefore too strong.

This also blocks the shortcut “divide the BEST count by the factorials of
parallel multiplicities.” Such a quotient is heuristically aligned with
labelling identical copies, but a rooted labelled count and a count modulo
rotation both carry symmetry/stabilizer conventions. The safe-transition
criterion avoids that counting issue entirely. Any exact count refinement
would need an explicit treatment of cyclic stabilizers, especially for
nonprimitive circular words.

## 7. Forced transitions versus feasible rearrangements

The criterion above is local at a residual state, but it still compares
global completions. This is a useful structural/algorithmic boundary, not a
static degree criterion. Two more static proposals are not established here:

- “every residual outgoing type is forced” is too strong, as `AABB` shows;
- “the support graph has one undirected cycle” is not necessary, because
  balanced directed graphs can have many undirected cycles.

A potentially sharper successor-allocation characterization is available but
not claimed as a new theorem: fix one cyclic spelling and index each edge
occurrence by its successor. A competitor is a permutation of the edge
occurrences that respects the tail/head vertex condition and is a single
cycle, while forgetting the identities of parallel copies. Uniqueness asks
whether this constrained permutation object has one orbit. An exact useful
polynomial criterion from that formulation would need to avoid enumerating
capacity-vector states.

## 8. Consequence for issue #83

The capacitated criterion now has a precise sufficient-and-necessary
recognition rule:

> follow one spelling; at every residual state, the next edge type is forced
> precisely when it is the unique safe outgoing type. Two safe types certify
> two completions.

This materially advances the graph-theoretic packet but does not characterize
bridging or settle the published maximum-likelihood problem. The residual
state may have exponentially many capacity vectors, although the procedure
itself visits only \(G\) states along a unique tour. A sharper static
characterization in terms of cut vertices, arborescences, or transition
systems remains open.

No Lean formalization is recommended from this note alone. The definitions
and proofs are mature at the research-note level, but the result is an
adaptation of a general Eulerian algorithm and is not yet a source-faithful
final theorem for the open problem.
