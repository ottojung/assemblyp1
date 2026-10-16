# The corrected oriented-strand §6.2 source model and its ML classification (#261)

_Status: representation repair + scoped ML classification, kernel-checked
2026-10-16 (agent `dc33fee413ff`).  Independent exact-arithmetic verifier:
`scripts/verify_261_oriented_strand_source_model.py`._

This note records the repair of a **representation defect** in the historical
MB09 §6.2 model `AssemblyP1/Section62BidirectedFlow.lean` on RC-palindromic
molecule classes, and the ML-maximality classification that the corrected model
supports.  It builds directly on the 2026-10-16 finding that `sgnRep`/`sgnTgt`
infer orientation from strand *word* equality with the molecule representative,
so a palindrome's two physical orientations receive the same signs and cannot be
distinguished even after duplicate list entries are erased.

## 1. The defect (source fact + kernel-checked witness)

The historical model enumerates strands by

```text
strandsOf rc verts = verts ++ verts.map rc
```

and derives incidences by

```text
sgnRep s mx = if s = mx then 1 else -1        (departure)
sgnTgt s my = if s = my then -1 else 1        (arrival)
```

For a molecule with `rc w = w` (an RC-palindrome), the two orientations have the
same word, so `strandsOf rc [w] = [w, w]` repeats the same strand value.  The
four strand-pair overlaps therefore collapse to a single `BdEdge` *value*, and
both physical orientations receive departure `+1` and arrival `-1`.  The opposite
signs are unrepresentable, and because `BdFlow = BdEdge → ℕ` is keyed by edge
value while `throughput`/`balCore` fold over the edge *list*, a single unit of
flow is counted four times.

Kernel-checked on the length-4 palindrome `ATAT` (`pal4`), `readLen = 4`,
`oMin = 2`:

| Fact | Declaration |
|---|---|
| historical graph is four copies of one edge value | `historical_pal_graph_quadruple` |
| historical sign pairs are `(+1,-1)` four times | `historical_pal_sign_pairs` |
| historical throughput of one shared-flow unit is `4` | `historical_pal_throughput_four` |
| the one-copy candidate is **infeasible** historically | `historical_pal_not_feasible_one` |

## 2. The repair (source-faithful representation)

An oriented strand keeps the *orientation* separate from the *word*:

```text
OStrand W = W × Bool                 -- (molecule-class representative, orientation bit)
oWord s   = if s.2 then rc s.1 else s.1
oRc  s    = (s.1, !s.2)              -- reverse-complement orientation flip
oRep s    = (s.1, false)             -- canonical class representative
depSign s = if s.2 then -1 else 1    -- incidence DERIVED FROM THE BIT
arrSign s = if s.2 then 1 else -1
```

The corrected graph is the **historical construction reused at the tagged strand
type**:

```text
oEdges toListW rcW readLen oMin verts
  = overlapEdges A (OStrand W) (oTo toListW rcW) oRep oRc readLen oMin (oVerts verts)
```

so `overlapEdges`, `Feasible62`, `throughput`, `balance`, `Spelling` and the
flow-to-count-vector adapter all apply verbatim.  The crucial identity is that
the historical sign function becomes the bit-derived sign:

```text
sgnRep s (oRep s) = depSign s        (sgnRep_oRep)
sgnTgt s (oRep s) = arrSign s        (sgnTgt_oRep)
```

and hence every corrected edge carries bit-derived incidences
(`bdEdge_oRep_sgnX`, `bdEdge_oRep_sgnY`).  The tagged enumeration is the two
orientations of every class exactly once (`strandsOf_oVerts`), even for a
palindrome.

### Palindrome semantics (kernel-checked, `pal4 = ATAT`)

| Fact | Declaration |
|---|---|
| both orientations have the same word | `oWord_pal` |
| the two orientations are distinct `OStrand` values | `oRep_ne_self_rc` |
| the corrected graph is `Nodup` (four distinct edges) | `corrected_pal_graph_nodup` |
| the four sign pairs are all combinations | `corrected_pal_sign_pairs` |
| all four edges carry the palindrome word | `corrected_pal_graph_words` |
| unit throughput is `1`, balance is `0` | `corrected_pal_throughput_one`, `corrected_pal_balance_zero` |
| the one-copy candidate is **feasible** | `corrected_pal_feasible_one` |

### Non-palindrome semantics (kernel-checked, `np3 = ATT`)

For a non-palindromic class the word map is a bijection between the two tagged
orientations and the two historical strands, and the signs agree:

| Fact | Declaration |
|---|---|
| equal edge counts | `nonpal_graph_lengths_eq` |
| equal sign pairs | `nonpal_sign_pairs_eq` |
| equal edge words | `nonpal_words_eq` |
| both graphs `Nodup` | `nonpal_corrected_nodup`, `nonpal_historical_nodup` |

### Labelling the historical model

The historical `AssemblyP1.Section62Flow` construction is **bounded /
non-faithful for RC-palindromic molecule classes**: `historical_pal_sign_collision`
and `historical_pal_edge_collision` show that the two physical orientations
collapse to one edge value and one sign pair, and `historical_pal_not_feasible_one`
exhibits a spelled one-copy candidate it cannot represent.  On non-palindromic
classes it agrees with the corrected model (above), so the repair is strictly a
palindrome fix.

## 3. ML maximality classification in the corrected domain

Module `AssemblyP1/Section62OrientedMLClassification.lean`.  It **reuses** the
merged `AssemblyP1.Section62FlowCountVectorAdapter` and
`AssemblyP1.Section62SpelledFlowMaximality`, and the #269 objective separation
`AssemblyP1.Section62FlowGenomeSeparation` is respected (the exact oriented
genome likelihood is not a function of the throughput).

**Well-defined class.**

* **Candidates** are corrected §6.2 zero-terminal feasible *flows*
  (`orientedFeasibleFlowSet = feasibleFlowSet oRep (oVerts verts) (oEdges …)`):
  vertex lower bound `1`, edge lower bound `0`, infinite upper bounds,
  signed-incidence balance `0`, zero supersource/supersink usage.  Not spelled
  circuits, not circular genomes.
* **Truth** is admitted (any element of the domain).
* **Likelihood / read model**: any score `(OStrand W → ℕ) → ℚ` that is a function
  of the corrected throughput `orientedThroughput`.  This covers the MB09 §6.1
  fixed-external-`N` separable product-binomial on the throughput vector, the
  `Section62BinomialCriterion` count-vector criteria, and the fixed-`n`
  extreme-sample criterion `Section62FiniteNExtremeSamples`.  It does **not**
  cover the exact oriented genome likelihood (#269 separation).
* **Length universe**: flows are unconstrained in length (the throughput records
  molecule counts); spelled sub-candidates range over all `n ≥ 1`.

**Classification theorems.**

| Statement | Declaration |
|---|---|
| exact reduction: flow maximality ⇔ throughput-image maximality | `oriented_maximal_iff_image` |
| spelled visit vectors lie in the corrected image | `oriented_spelled_visits_mem_image` |
| **necessary**: flow maximality ⇒ spelled-sub-class maximality | `oriented_spelled_maximal_of_flow_maximal` |
| negative transfer: a spelled dominator kills flow maximality | `oriented_flow_not_maximal_of_spelled_witness` |
| **necessary and sufficient under image equality** | `oriented_maximal_iff_spelled_maximal_of_image_eq` |

The exact answer to "when does the truth maximize the finite likelihood?" is
therefore: **iff its corrected throughput vector maximizes the chosen
throughput-factoring score over the corrected feasible throughput image**
(`oriented_maximal_iff_image`).  The spelled test is equivalent to this exactly
under the identity `Θ(orientedFeasibleFlowSet) = spelledVisitSet`
(`oriented_maximal_iff_spelled_maximal_of_image_eq`); that identity is the
remaining incidence/Graver obligation and stays **OPEN** in general.

## 4. Remaining OPEN subclaims (unchanged in kind)

* **OPEN-1 throughput image** of the corrected feasible set (incidence/Graver).
  The spelled *inclusion* is resolved in the corrected domain
  (`oriented_spelled_visits_mem_image`); the converse is not.
* **OPEN-3 general non-spelled-flow maximality criterion**: no structural
  criterion is known; the `AAATT` obstruction remains.
* **OPEN-4 transitive reduction** interaction with ML: untouched here; owned by
  the #284 front.
* **OPEN-5 orientation/RC class**: the *representation* defect is repaired and
  the palindrome/non-palindrome semantics are kernel-checked here; the remaining
  question is the interaction of the corrected incidence signs with the
  transitive reduction and with the RC-quotient of candidate genomes.
* **OPEN-6 sample realizability** at arbitrary `o_min`.
* **Source fidelity**: the §6.1 product-binomial surrogate is not the exact iid
  likelihood (#269), and the §6.2 objective is not the circular-genome
  likelihood.

## 5. Artifacts

* `AssemblyP1/Section62OrientedStrandFlow.lean` — the corrected model.
* `AssemblyP1/Section62OrientedMLClassification.lean` — the classification.
* `AssemblyP1/Section62OrientedStrandFlowAudit.lean` — `#print axioms` audit.
* `scripts/verify_261_oriented_strand_source_model.py` — independent exact
  verifier (18 checks), wired into CI `research-docs`.
* This note.

## 6. Reproduce

```sh
lake build AssemblyP1.Section62OrientedStrandFlowAudit --wfail
lake env leanchecker AssemblyP1.Section62OrientedStrandFlow
lake env leanchecker AssemblyP1.Section62OrientedMLClassification
lake env axiom-audit --allow propext,Classical.choice,Quot.sound \
    --root AssemblyP1 --modules-from AssemblyP1
python3 scripts/verify_261_oriented_strand_source_model.py
```

Axioms for every new declaration are within
`[propext, Classical.choice, Quot.sound]`; there is no `sorry` / `admit` /
`axiom` / `native_decide`.
