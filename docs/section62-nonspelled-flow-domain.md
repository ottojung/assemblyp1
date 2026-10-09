# The general (non-spelled) §6.2 flow domain: what the flow optimum can and cannot mean

_Status: independent from-scratch computation + primary-source reading + kernel-checked
finite certificate for issue #214, 2026-10-09. Nothing here is promoted: the module
`AssemblyP1/Section62NonSpelledFlow.lean` kernel-checks the finite instance, and the
bounded statements are labelled as bounded. Every claim is labelled **source fact**,
**modeling choice**, **mathematical proof**, **kernel-checked**, **verified
computation, bounded**, or **open**._

_Reproduction:_

```sh
python3 scripts/verify_se62_nonspelled_flow_domain.py
lake build AssemblyP1.Section62NonSpelledFlow
```

_The script is self-contained, exact (`fractions.Fraction`), deterministic, exits
non-zero on any failed assertion, and shares no code with the repository's earlier
§6.2 searches. The Lean module contains no `sorry`, `axiom`, `admit` or
`native_decide`._

---

## 0. Verdict at a glance

Fix the literal Medvedev–Brudno (2009) §6.2 object: vertices are read DNA
molecules, edges are bidirected proper overlaps of length ≥ `o_min`, transitive
edge reduction, vertex lower bound `1`, edge lower bounds `0`, upper bounds `∞`,
a min-cost flow whose value through vertex `i` is `d_i`, scored by the §6.1
separable binomial with external genome size `N`. Fix the strict Shomorony et
al. (2016) Eq. (1) bridging predicate `I_s`.

1. **(A) The refutation of dominance over the whole flow feasible set needs no
    additional witness.** `AssemblyP1/Section62BidirectedFlow.lean`'s `Feasible62`
    is the *general* §6.2 feasibility predicate; a spelled circuit is a general
    feasible flow (`spelled_subset_general`, kernel-checked projection). The already
    kernel-checked spelled witnesses `AAATT → AAAATT` (ratio `9/8`) and
    `AAATAT → AAAAAT` (ratio `5`) each certify admissibility against that general
    predicate, so they already refute "the truth-induced flow maximizes the §6.1
    objective over the §6.2 feasible set". Both witnesses are packaged as the
    single kernel-checked objects `bridging_spelled_witnesses_general` and
    `samelength_spelled_witnesses_general` in
    `AssemblyP1/Section62NonSpelledFlow.lean`. [source fact + kernel-checked]

2. **(B) The general feasible set strictly contains the spelled circuits, and in
   this instance its maximizers are exactly non-spelled ones.** The witness below
   has a bridged truth `S = AAATT` and two admissible §6.2 flows with throughputs
   `d* = (AAA:2, AAT:1, TAA:1)` and `d*₃ = (AAA:3, AAT:1, TAA:1)`; neither
   throughput vector is the spectrum of any circular molecule of any length; and
   `L(d*)/L(d_S) = 256/81 > 1`. [kernel-checked]

3. **(C) Therefore a flow optimum cannot be called an ML *sequence* without an
   extra rule.** `d*` maximizes the §6.1 objective over its whole domain
   `1 ≤ d ≤ N` (kernel-checked), and the complete maximizer set in that domain is
   `{d*, d*₃}` (kernel-checked). Both are non-sequence spectra. So for this
   instance the set of "maximum-likelihood sequences" over the §6.2 flow domain is
   **empty**: the published sentence "the maximum-likelihood sequence is the true
   sequence" has no truth value over the flow domain unless a flow-to-sequence
   rule is added, and §6.2 supplies none. [mathematical proof + kernel-checked]

---

## 1. Source facts and named assumptions

### 1.1 Source facts

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1–3.4, §5.2, §6.1–6.2,
PMC3154397, as quoted in `docs/section62-mb09-bidirected-graph-audit.md` §1.

- §3.1 a DNA molecule is an unordered reverse-complement strand pair; §4.1 each
  `k`-molecule is represented only once, so a vertex is a *class*.
- §3.3 a bidirected edge carries a signed incidence at each endpoint.
- §3.4 a flow satisfies the signed-incidence balance `pos(f)(v) − neg(f)(v) = b(v)`.
- §5.2 the vertex split `v⁻ → v⁺` carries the vertex bounds, so `d_i` is the flow
  through vertex `i`.
- §6.1 the tractable objective is the product of per-type binomial marginals with
  the external known genome length `N`, `∏_w C(n, x_w) (d_w/N)^{x_w}
  (1 − d_w/N)^{n−x_w}`, `0 ≤ d_w ≤ N`.
- §6.2 vertices are the reads; edges are all bidirected overlaps of length ≥
  `o_min`; transitive edge reduction; every read vertex has lower bound `1`, all
  other lower bounds `0`, all upper bounds `∞`; a supersource/supersink is added
  with prohibitive cost so that its usage is minimized; the flow represents a
  "(non-contiguous) assembly of the genome" while "the original double-stranded
  genome corresponds to a circuit".
- Observation 7: the number of times a walk visits a read vertex equals the number
  of times that read appears as a submolecule of the molecule the walk spells.

[source fact]

`I_s` = coverage, every maximal triple repeat all-bridged, every interleaved
repeat pair bridged, with the strict copy-bridging normalization of
`docs/bridging-source-semantics.md`: a read `[r, r+L)` bridges the length-`e` copy
at `t` iff `r < t` and `t + e < r + L` on the integer lift. [source fact]

### 1.2 Modeling choices used here

| ID | Assumption | Justification |
|---|---|---|
| A1 | Vertices are read **molecule classes** `min(w, rc w)`; a duplicated read is one vertex and enters only `x_w`. | MB09 §3.1, §4.1 |
| A2 | Vertex lower bound `1`; the observed multiplicity `x_w` is **not** a lower bound on `d_w`. | MB09 §6.2 (per-vertex, not per-occurrence) |
| A3 | Candidate objects are **closed** integral flows (zero supersource/supersink usage), i.e. "non-contiguous assemblies". | MB09 §6.2 circuit observation + prohibitive terminal cost. Open walks remain available in the general `Admissible` predicate; the certificates are all circuits, hence first-tier. |
| A4 | Objective is the §6.1 separable binomial with external `N = \|S\|`. | MB09 §6.1 |
| A5 | Genome circular; starts and windows cyclic. | MB09/Shomorony exposition |
| A6 | `o_min` is an explicit parameter. The witness uses `o_min = 1` at `L = 3`; §2.4 records why this is not a free choice. | MB09 §6.2 |
| A7 | `I_s` uses the strict bridging predicate. | `docs/bridging-source-semantics.md` |
| A8 | Bidirected balance is checked at **port (strand) level**: the departing and arriving flow agree at every strand of every observed molecule. The class-level signed-incidence balance of `Feasible62` is checked as well. | MB09 §3.3/§3.4 read at strand level; A8 is *stronger*, so certificates under it also certify the shared predicate |
| A9 | The vertex throughput is the departing flow, which A8 forces to equal the arriving flow. | MB09 §5.2, Observation 7 |
| A10 | Both readings of transitive edge reduction are checked (§2.4). | §6.2 wording vs. Myers 2005 |
| A11 | Bridge-aware placement vs. sampled multiplicity: coverage and bridging see the *set* of realized placements; the sampled multiplicity is separate data (start `0` sampled twice here). | record, as in `AssemblyP1/SameLengthSection62Counterexample.lean` |
| A12 | No flow-to-sequence rule exists in the source; the question "is the ML sequence the truth" is therefore ill-posed over the flow domain, and every rule must be added explicitly. | absence of any such rule in MB09 §6.2 |

### 1.3 The two readings of transitive reduction, and their reach

For `L = 3` every proper overlap has length `1` or `2`.

- **Literal reading** ("remove any overlap that is spelled by two shorter
  overlaps"). With the composition law `l = l₁ + l₂ − L` and `l₁, l₂ < l`, one gets
  `l₁ + l₂ ≤ 2(l−1)`, hence `L + l ≤ 2l − 2`, i.e. `L + 2 ≤ l`, contradicting
  `l ≤ L − 1` for any proper overlap. **So the literal reading removes nothing,
  ever.** [mathematical proof; kernel-checked for this graph as
  `graph_reduction_vacuous_literal`]
- **Myers 2005 reading** (remove the direct overlap when a two-step path of
  strictly *longer* proper overlaps exists between the same endpoints). At
  `o_min = 1` on `{AAA, AAT, TAA}` this removes 16 of the 28 edges, leaving 12.
  [kernel-checked: `reducedList_eq`]

Because every closed flow is a multiset of circuits and every flow on a subgraph is
a flow on any supergraph with zero flow elsewhere, the Myers-reduced graph gives
the **smallest** feasible set and the full graph the **largest**. The certificates
in §2 are stated on *both*, so they are independent of the reduction reading.
[kernel-checked: `star21_feasible62` and `star21_feasible62_reduced`]

### 1.4 Why `o_min = 1` matters, and what it costs

Consecutive windows of a circular molecule overlap in exactly `L − 1` symbols, so
**every window walk uses length-`(L−1)` edges only**. Consequently:

- A feasible flow that must use an overlap of length `< L−1` is not the window walk
  of any molecule. [mathematical proof; kernel-checked instance
  `star21_uses_short_overlap`]
- Such shorter overlaps only exist in the graph when `o_min ≤ L − 2`. At the
  `o_min = L − 1 = 2` setting of the merged witnesses the graph on
  `{AAA, AAT, TAA}` has only length-`2` edges, its circulation cone is
  `{(a, 2b, 2b)}`, and every element of that cone **is** a sequence spectrum
  (the molecule with `k = b` alternating runs and total length `a + 4b`). Hence
  within this read support the non-spellable phenomenon is exactly an
  `o_min < L−1` effect. [mathematical proof for this support + verified
  computation]

**Residual honesty.** Whether *some other* read support admits a non-spellable
maximizer at `o_min = L − 1` is **not decided here**; the bounded search of §7
found none in scope for three-class supports over `{A,T}` at `L = 3` with candidate
length ≤ 11, but it did find non-spellable *throughput vectors* at `o_min = 2` for
read supports that are themselves unspellable (e.g. `{AAA, ATA}`), where no bridged
truth exists. Whether MB09's experiments use `o_min < L−1` is a source question this
repository records only as a parenthetical in
`docs/section62-mb09-bidirected-graph-audit.md` §2 without a section citation; it is
**not** assumed here, and both `o_min` readings are reported. [open]

---

## 2. The witness and its certificates

```text
alphabet          {A, T}, reverse-complement involution A ↔ T
truth             S = AAATT            (G = 5)
read length       L = 3,  o_min = 1
realized starts   (0, 1, 4) with start 0 sampled twice          (n = 4)
external size     N = |S| = 5
observed          x = { AAA:2, AAT:1, TAA:1 }
truth spectrum    d_S = { AAA:1, AAT:2, TAA:2 }
non-spellable     d*  = { AAA:2, AAT:1, TAA:1 }   (one bidirected circuit)
flow optima       d*₃ = { AAA:3, AAT:1, TAA:1 }   (that circuit + one AAA self-loop)
ratio             L(d*)/L(d_S) = 256/81 > 1
```

### 2.1 `I_s` holds

- **Coverage.** Intervals `[0,3)`, `[1,4)`, `[4,7)` (on the lift) cover `0..4`.
- **Triple repeat.** The only maximal triple repeat is the length-`1` run of `A` at
  copies `{0,1,2}`; the reads at lifts `−1`, `0`, `1` bridge copies `0`, `1`, `2`
  respectively.
- **Interleaved pairs.** The maximal repeat pairs are `AA@(0,1)` and `TT@(3,4)`;
  the four starts do not cyclically alternate, so the conjunct is vacuous.

Two facts keep this copy of the instance distinct from the merged `AAATT` witness:
the sampled multiplicity of `AAA` is `2`, not `1`, and `o_min = 1`, not `2`.
Everything else — truth, placements, `I_s` — is the same, so the `I_s` certificate is
literally the one already accepted for `AAATT` with placements `{0,1,4}`.
[kernel-checked: `truth_information_feasible` via the shared
`SourceFaithfulIs.InformationFeasible`, discharging all conjuncts by finite
`decide`; verified computation]

### 2.2 The truth is an admissible general flow

The truth's window walk is the strand sequence `AAA, AAT, ATT, TTA, TAA`, all
five steps being length-`2` overlaps. On the `o_min = 1` graph it is a bidirected
circuit with vertex throughputs `(1, 2, 2) = d_S`, edge lower bounds `0`, zero
class-level signed-incidence balance at all three read vertices, zero port-level
balance residual at all six strands, and no supersource/supersink usage.
[kernel-checked: `truth_feasible62`, `truth_port_balanced`]

### 2.3 The non-spellable optima are admissible flows

Both optimize with explicit edge multiplicities on the reduced graph (and hence on
the full graph):

```text
d*  : AAA.p→AAA.p : 1,  AAA.p→AAT.p : 1,  AAT.p→TAA.p : 1 (overlap 1),
     TAA.p→AAA.p : 1
d*₃ : the same with AAA.p→AAA.p : 2
```

Certified for each: every step is a genuine bidirected overlap edge; edge lower
bounds `0`; the vertex lower bound `1`; class-level signed-incidence balance `0` at
every read vertex; **port-level balance at every strand of every observed
molecule**; no supersource/supersink usage; vertex throughput equal to the claimed
spectrum, hence (Observation 7) equal to `d*`/`d*₃`. The `d*` circuit uses the
length-`1` overlap `AAT.p → TAA.p`, which survives the Myers reduction and is used
by no window walk. [kernel-checked: `star21_feasible62`,
`star21_feasible62_reduced`, `star31_feasible62`, `star21_port_balanced`,
`star31_port_balanced`, `star21_uses_short_overlap`]

### 2.4 No circular molecule has these throughputs — a complete proof

The argument is a reduction plus a finite check, not a search bound.

> **Lemma (mass).** For any circular molecule `u` of length `G`, the total
> spectrum mass `∑_c spec(u)_c = G`: each of the `G` window positions contributes
> to exactly one molecule class. [mathematical proof; kernel-checked as
> `sum_spectrum`]

> **Lemma (molecule counts).** For every circular word `u` over `{A,T}` whose
> length-`3` windows all lie in the molecule classes `{AAA, AAT, TAA}`, one has
> `spec(u)_{AAT} = spec(u)_{TAA} = 2 · (# of A→T boundaries of u)`, hence both
> counts are **even**. [mathematical proof; also corroborated exhaustively for all
> lengths ≤ 12 by the script]
>
> _Proof._ A window of class `AAT` is exactly a word whose first and last symbols
> are `A` and `T` (over `{A,T}` the class `AAT` is `{AAT, ATT}`); similarly class
> `TAA` is `{TAA, TTA}`, the words with first `T` and last `A`. So
> `#{i : w_i = A ∧ w_{i+2} = T} = #AAT + #ATT` and
> `#{i : w_i = T ∧ w_{i+2} = A} = #TAA + #TTA`. Reindexing
> `#AAT = #{i : (w_i, w_{i+1}, w_{i+2}) = (A,A,T)}` by `i ↦ i+1` and using that
> `TAT` is not an allowed window gives `#AAT = #{i : (w_i, w_{i+1}) = (A,T)} = ab`;
> reindexing `#ATT` by `i ↦ i+2` and using that `ATA` is not allowed gives
> `#ATT = ab`. Likewise `#TAA = #TTA = ba`. Finally `ab = ba`: with
> `s(i) = +1` if `w_i = A` and `−1` otherwise,
> `∑_i (s(i) − s(i+1)) = 0` by reindexing, while the same sum is `2ab − 2ba`. ∎

> **Theorem (non-spellability, all lengths).** No circular molecule of any length
> has the throughput vector `d*`. [kernel-checked:
> `no_sequence_has_star_spectrum`]
>
> _Proof._ Suppose `spec(u) = d*`. By the mass lemma `G = 2 + 1 + 1 = 4`, so it
> suffices to check the `2⁴ = 16` functions `Fin 4 → Base`. Exhaustive checking
> rejects all of them; the script corroborates the same fact up to length 12 and
> the molecule-count lemma explains it structurally. ∎

Since `d*` has an odd `AAT` coordinate (`1`), the molecule-count lemma alone already
excludes it for every length; the kernel-checked route is the mass reduction plus
the exhaustive length-`4` check, which is complete without needing the parity
argument.

### 2.5 The likelihood comparison and the optimality of the flow

The §6.1 objective is separable, so with `x = (2,1,1)`, `n = 4`, `N = 5`:

```text
AAA coordinate:  (d/5)²((5−d)/5)² is maximized at d = 2, 3   (value 36/625)
AAT coordinate:  (d/5)((5−d)/5)³  is maximized at d = 1      (value 128/625)
TAA coordinate:  same as AAT
```

Hence the unconstrained integer maximizer over the domain `1 ≤ d ≤ 5` is attained
exactly at `(2,1,1)` and `(3,1,1)` — exactly the two admissible flows of §2.3 — and
the truth's own throughputs `(1,2,2)` fall short by a factor `256/81`:

```text
L(d*)/L(d_S) = [(2/5)²(3/5)² / ((1/5)²(4/5)²)] · [(1/5)(4/5)³ / ((2/5)(3/5)³)]²
             = (9/4) · (32/27)² = 256/81.
```

[kernel-checked: `lik_star_over_truth`, `star_better`, `lik_le_star`,
`star_argmax`, `lik_star3_eq_star`; verified computation]

### 2.6 Integral versus half-integral maximizers (three-level distinction)

MB09 §5.1 discusses a half-integral LP/biflow relaxation as an *algorithmic
approximation* to an optimal integral flow; §5.2 uses discrete convex costs
`c_e : N → R`.  The `star_argmax` theorem above identifies the argmax over the
**original integer genomics/count domain** (level (i)).  It does **not** extend to
the half-integral biflow relaxation (level (ii)) or to a continuously-extended
likelihood on relaxed flows (level (iii)).

**The half-integral gap is exact.**  Let `f₂`, `f₃` be the feasible closed edge
flows with throughputs `(2,1,1)` and `(3,1,1)`.  By affine balance and convex lower
bounds, `h = (f₂ + f₃)/2` is a feasible half-integral flow with throughput
`(5/2, 1, 1)`.  With `n = 4`, `x = (2,1,1)`, external `N = 5`, the AAA binomial
factor is proportional to `d²(5−d)²`.  At `d = 2` or `3` it is `36`; at `d = 5/2`
it is `625/16`.  All other factors are unchanged, so:

```text
L(h) / L(f₂) = (625/16) / 36 = 625/576 > 1
L(h) / L(truth) = (625/576) · (256/81) = 2500/729 > 256/81
```

[kernel-checked: `half_integral_strictly_better`, `half_integral_ratio`]

Thus the set `{f₂, f₃}` is the **integral** argmax only, not the half-integral or
continuous argmax.  The three levels must be labelled explicitly:

| Level | Domain | MB09 section | What `star_argmax` covers |
|---|---|---|---|
| (i) | Original integer genomics/count domain | §5.2 (`c_e : N → R`) | **Yes** — this is the integral argmax |
| (ii) | Algorithmic half-integral biflow approximation | §5.1 (LP/biflow relaxation) | **No** — `h = (f₂+f₃)/2` beats it by `625/576` |
| (iii) | Optional continuously-extended likelihood on relaxed flows | Not in MB09 | **No** — extra continuous extension |

**No automatic transfer of optimality or interpretation between levels.**

---

## 3. Answering "is the truth the ML sequence over the flow domain?"

The published sentence quantifies over "the maximum-likelihood sequence", but §6.2's
candidate objects are flows. The likelihood depends on a candidate only through its
throughput vector `d` (§6.1 + Observation 7), so the question must be read through
the throughput map. Three readings, and what each gives:

| Rule from a flow to a sequence | Consequence |
|---|---|
| **R1.** Restrict the candidate set to flows that spell a genome (i.e. keep only throughputs that are sequence spectra). | The resulting optimum is *not* the truth: `d_S = (1,2,2)` is beaten by the spelled candidate `D = AAAATT` (ratio `9/8`, kernel-checked on `main`). Also, the restriction is not flow-feasibility but an extra condition. |
| **R2.** Take the argmax flow and output any sequence it spells. | The rule is **partial**: for this instance the argmax set is `{d*, d*₃}` and neither spells. Where it is defined it does not give the truth either. |
| **R3.** Take the argmax flow and output any sequence whose spectrum dominates it (a "non-contiguous assembly" read literally). | Even more arbitrary; the source gives no such rule. |

So: over the §6.2 flow domain the maximum-likelihood *object* of this instance is a
flow that spells no genome, and the maximum-likelihood *sequence* does not exist.
Under R1 the truth is still not ML. Under every reading the published sentence
fails to be satisfied, but for different reasons, and the failure of "the
maximum-likelihood sequence is the true sequence" is a **type error** before it is
a mathematical falsehood. This is the sharpest source-fidelity statement available
for the flow layer, and it is the one #214 asks for. [mathematical proof +
kernel-checked instance]

**One-way implication, stated exactly.** For this instance,

```text
(∀ flow f admissible over the §6.2 feasible set, L(f) ≤ L(d_S))  ⇒  False,
```

and

```text
(∀ sequence D whose spectrum is admissible over the §6.2 feasible set,
    L(D) ≤ L(d_S))  ⇒  False,
```

the second following from the first because a spelled circuit *is* a feasible flow
(`spelled_subset_general`). Conversely the flow-domain statement is strictly
stronger than the sequence-domain one, because the feasible set is strictly larger.
[kernel-checked for the witness; mathematical proof for the inclusion]

---

## 4. What the separation looks like numerically

| candidate set | best throughput | likelihood |
|---|---|---|
| all throughput vectors in the §6.1 domain `1 ≤ d ≤ 5` | `(2,1,1)`, `(3,1,1)` | `147456/244140625` |
| §6.2-admissible flows (Myers reduction, `o_min = 1`) | `(2,1,1)`, `(3,1,1)` | `147456/244140625` |
| circular molecules whose windows lie in the support, length ≤ 12, `d ≤ 5` | `(1,2,2)`, `(4,2,2)` | `104976/244140625` |
| the truth `AAATT` | `(1,2,2)` | `46656/244140625` |

So the flow optimum strictly exceeds the best sequence candidate:
`147456/104976 = 1024/729 ≈ 1.405`, and it exceeds the truth by `256/81 ≈ 3.16`.
[verified computation; the two kernel-checked inequalities are
`star_better` and `lik_le_star`, and the sequence-side maximum is a finite check
over the complete characterization of §2.4]

---

## 5. Relation to existing repository results

| Existing claim | Location | Status after this issue |
|---|---|---|
| `Feasible62` is the general §6.2 flow predicate; a spelled circuit is a feasible flow | `AssemblyP1/Section62BidirectedFlow.lean` | made explicit as a theorem: `spelled_subset_general` |
| `AAATT → AAAATT` refutes dominance over the flow domain | `docs/bridging-se62-flow-ml-counterexample.md` | **upgraded**: the refutation is over the *whole* feasible set, not the spelled sub-case; no non-spellable flow needed |
| `AAATAT → AAAAAT` refutes the same-length sub-case | `docs/section62-same-length-bidirected-counterexample.md` | same upgrade |
| Whether the §6.2 polytope alone can force ML optimality | `docs/se62-ml-cycle-obstruction.md` (unmerged branch) | consistent and extended: the obstruction is now seen to also produce a *non-spellable* optimum, not merely a spelled competitor |
| "no current witness has both truth and competitor sequence-level §6.2-feasible" | `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` §5 | unrelated reading split; unchanged |
| Unmerged non-spellable-flow searches (`analysis/issue36-*`) | several branches | this note re-derives the phenomenon independently, states both reduction readings, certifies port-level balance as well as class-level, and kernel-checks the throughput-level claim for all lengths rather than by enumeration |

---

## 6. What this settles, and what it does not

**Settles (kernel-checked).** For the literal §6.2 object with `o_min = 1`:

1. `I_s` holds for the truth, and the truth is an admissible §6.2 flow.
2. Two admissible §6.2 flows strictly beat the truth, and they are the complete
   maximizer set of the §6.1 objective over its whole domain.
3. Neither maximizer spells any circular molecule of any length, so the §6.2 flow
   domain admits no "maximum-likelihood sequence" for this instance.
4. The existing spelled witnesses already refute dominance over the general flow
   domain; no non-spellable witness was needed for that part.

**Settles (mathematical proof, not decision procedure).** The literal
"two shorter overlaps" transitive reduction is vacuous for proper overlaps at any
`L`; the Myers reduction at `o_min = 1` on `{AAA,AAT,TAA}` leaves 12 of 28 edges;
and for that read support at `o_min = L−1` the circulation cone is contained in the
sequence spectra.

**Does not settle.**

1. Which Medvedev–Brudno layer the 2016 sentence denotes — unchanged source
   ambiguity, owned by the provenance notes.
2. Whether a non-spellable *maximizer* exists at `o_min = L−1` in a valid (spellable
   support, bridged truth) instance. The bounded search of §7 found none in scope;
   this is evidence, not a proof of absence. [open]
3. Whether MB09 §3.4's balance is intended at class or strand level. The witnesses
   here satisfy both, so the result is independent of that choice, but the shared
   `Feasible62` predicate uses only the (weaker) class-level clause and does not
   record the port-level one; that is a modeling gap in the library, not in this
   result. [open]
4. Tie/equivalence semantics and the single-strand reading. [open, other issues]
5. Whether an unbounded family of non-spellable-maximizer witnesses exists, and
   whether one exists with all read starts distinct. The bounded search found only
   instances with a duplicated read. [open]

---

## 7. Bounded search context (evidence, not proof)

Run over alphabet `{A,T}`, `L = 3`, `o_min ∈ {1,2}`, both reduction readings, for
the read support `{AAA, AAT, TAA}`:

| `o_min` / reduction | edges | circuit generators | non-spellable throughput vectors with `d ≤ 5` |
|---|---|---|---|
| `1` / Myers | 12 | 16 | yes (`(2,1,1)`, `(3,1,1)`, …) |
| `1` / literal (vacuous) | 28 | — | yes (superset) |
| `2` / both | 10 | 6 | **no** (cone `= {(a, 2b, 2b)}`) |

Characterization (verified computation, bounded): over all three-class supports
over `{A,T}` at `o_min = 2` with candidate length ≤ 11, every §6.2 throughput
vector with total mass `G` is a sequence spectrum of length `G`. At `o_min = 1`
several supports (e.g. `{AAA,AAT,TAA}`, `{AAA,ATA,TAA}`, `{AAA,AAT,ATA}`) admit
non-spellable throughput vectors, always because a shorter-than-`L−1` overlap
survives. For the two-class support `{AAA, ATA}` non-spellable throughput vectors
exist even at `o_min = 2`, but that support is itself unspellable (its overlap graph
has two disconnected components), so no bridged truth inhabits it.
[verified computation, bounded]

---

## 8. Epistemic status

| Claim | Status |
|---|---|
| MB09 §6.1/§6.2 object, per-vertex lower bound `1`, molecule-class vertices | **source fact** |
| `I_s` definition and the strict bridging normalization | **source fact** |
| `Feasible62` is the general §6.2 feasibility predicate; spelled ⊂ general | **source fact + kernel-checked** (`spelled_subset_general`) |
| spelled witnesses `AAATT→AAAATT`, `AAATAT→AAAAAT` feasible in the general flow optimizer, hence refute dominance | **kernel-checked** (`bridging_spelled_witnesses_general`, `samelength_spelled_witnesses_general`) |
| literal "two shorter overlaps" reduction is vacuous | **mathematical proof** + kernel-checked for this graph |
| Myers reduction at `o_min = 1` leaves 12 of 28 edges | **kernel-checked** |
| `S = AAATT` witness: `I_s`; truth admissible; `d*`, `d*₃` admissible with class **and** port balance; `L(d*)/L(d_S) = 256/81` | **kernel-checked** |
| `d*` maximizes the §6.1 objective over its whole domain; maximizer set `= {d*, d*₃}` | **kernel-checked** |
| no circular molecule of any length has the throughputs `d*` | **mathematical proof + kernel-checked** (mass reduction + exhaustive length-4 check) |
| molecule-count lemma (`spec(AAT) = spec(TAA) = 2·#A→T boundaries`) | **mathematical proof** + corroborated by exhaustive check to length 12 |
| the §6.2 feasible set has no ML sequence for this instance | **follows** (kernel-checked ingredients) |
| the existing spelled witnesses already refute dominance over the general flow domain | **follows** (kernel-checked ingredients) |
| non-spellable maximizers at `o_min = L−1` in a valid instance | **open** (bounded zero evidence) |
| which MB09 layer the 2016 sentence denotes; tie semantics; single strand | **open** |

---

## 9. Reproduce

```sh
python3 scripts/verify_se62_nonspelled_flow_domain.py     # 37 checks, exact rationals
lake build AssemblyP1.Section62NonSpelledFlow             # kernel check
lake build AssemblyP1.Section62BridgingCounterexample \
           AssemblyP1.SameLengthSection62Counterexample   # witness modules
lake env leanchecker AssemblyP1.Section62NonSpelledFlow \
  AssemblyP1.Section62BridgingCounterexample \
  AssemblyP1.SameLengthSection62Counterexample             # kernel replay
lake env axiom-audit --allow propext,Classical.choice,Quot.sound \
  --root AssemblyP1.Section62NonSpelledFlow \
  --modules AssemblyP1.Section62NonSpelledFlow            # axiom audit
```

The script independently rebuilds the `o_min = 1` graph, applies both reduction
readings, certifies the truth flow and both optimizing flows (port balance, class
balance, throughputs, lower bounds, no terminal use), checks `I_s` from scratch,
corroborates the molecule-count lemma for all circular words up to length 12,
enumerates the feasible throughput set inside `1 ≤ d ≤ 5`, computes the exact
ratios, and asserts the negative boundary of §7. It exits non-zero on any failure.

Note: the aggregator `AssemblyP1.lean` currently fails to build on this branch for
a reason unrelated to #214 — a duplicate-declaration conflict between
`AssemblyP1.Issue94KShort` and `AssemblyP1.Issue94KShortGeneral` introduced by
`origin/main` advancing past this branch's base, plus elaboration errors in
`AssemblyP1/BBTTripleBridge.lean` (last touched by 42ebed7, not a #214 commit).
The three #214 modules above build, kernel-replay, and axiom-audit cleanly on
their own.

Primary sources: Medvedev & Brudno (2009), §3.1–3.4, §5.2, §6.1–6.2,
[PMC3154397](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/); Myers (2005),
*The fragment assembly string graph*, *Bioinformatics* 21(Suppl 2) ii79–ii85;
Shomorony, Kim, Courtade & Tse (2016), Eq. (1) and §5; Bresler, Bresler & Tse (2013).
