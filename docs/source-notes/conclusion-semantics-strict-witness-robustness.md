# Conclusion semantics and equivalence-robustness of the integrated strict witnesses

_Status: focused source + logical determination for issue #36, 2026-09-20, on
branch `semantics/conclusion-strict-witness-robust-2026-09-20` based on
`origin/main` at `8182e1b` (the PR #43 merge). Scope: resolve the conclusion
semantics of “the maximum-likelihood sequence is the true sequence” only as far
as it bears on whether any unresolved equivalence convention could invalidate
the integrated strict counterexample. It does **not** re-synthesize the
Medvedev–Brudno referent, the probability-object convention, or the
sample-size regime; those are cited where needed. Every claim is labelled
**source fact**, **mathematical fact**, **verified computation**,
**kernel-checked**, **interpretation**, or **source gap**._

## 0. Bottom line

1. **The sources do not fix the maximizer-vs-uniqueness reading** and state no
   tie rule or uniqueness theorem at the open-question sentence. [source fact]
2. **The two source-faithful conclusion schemas** are exactly the repository's
   `MaximizerSchema` (`∀ candidate, L(candidate) ≤ L(truth)`) and
   `UniqueSchema` (`MaximizerSchema ∧` every tied candidate is equivalent to the
   truth). The weak schema contains **no equivalence relation and no tie
   rule**. [source fact + modeling fact]
3. **Strictness is equivalence-proof.** A competitor with strictly greater
   likelihood falsifies the weak schema, hence every stronger schema, for
   *every* genome equivalence `≈` and *every* tie convention. Tie/equivalence
   semantics can only decide the fate of a *tied* competitor. [mathematical fact]
4. **The integrated strict witnesses are strict.** The same-length witness
   `AAATAT → AAAAAT` (PR #43) is kernel-checked to satisfy
   `lik obs dS < lik obs dD` and improves by `5` (§6.1 binomial) and `3`
   (exact multinomial); the variable-length witness `AAATT → AAAATT` (PR #40)
   improves by `9/8` and `125/108`. [kernel-checked + verified computation]
5. **No unresolved equivalence convention can invalidate them.** Under cyclic
   shift and/or reverse complement — the only genome equivalences the cited
   sources support — the truth and competitor orbits are disjoint; and even a
   hypothetical coarser equivalence cannot restore the weak schema because the
   strict competitor already violates it. The one logical loophole (reading the
   sentence as “some maximizer is equivalent to the truth”, dropping
   maximality of the truth) has no source support and is not the plain meaning
   of the phrase. [mathematical fact + source gap]
6. Consequently, **tie semantics are irrelevant to the negative verdict on the
   integrated witnesses**, and the remaining obstacles to *settling the
   published open problem* are the ones already documented — referent,
   objective, candidate class/strand, and regime — **not** the equivalence
   convention. [interpretation]

## 1. Primary sources and verification

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Medvedev–Brudno (2009), published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |

The three hashes were recomputed for this note and match the ledger in
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md).
Text was extracted with `pypdf`; the quotations below were re-located in the
extracted text. [source fact]

## 2. What the sources do and do not fix

### 2.1 The open-question sentence adds no tie or uniqueness clause

Shomorony et al. (2016), Discussion (accepted typeset p. i501; source fact):

> “Understanding whether bridging conditions can be used to guarantee that the
> maximum-likelihood sequence is the true sequence is currently an open
> question.”

The same paragraph says only that reconstruction is guaranteed but “there is no
guarantee that this sequence corresponds to the solution of an optimization-based
formulation”. It does not define a tie-break, say the optimum is unique,
quantify over every optimum, or name an equivalence relation. The singular “the
maximum-likelihood sequence” therefore cannot distinguish a selected maximizer
from a unique maximizer. This is the finding of
[`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md), whose
consequence for the repository is two retained schemas. [source fact + interpretation]

Medvedev–Brudno (2009) is no more explicit: §6.1 says “we attempt to assemble
the genome with the maximum global read-count likelihood”, the abstract says
the framework assembles the genome that is “the most likely source of the
reads”, and neither supplies a tie rule or a uniqueness theorem at that point.
[source fact]

### 2.2 Cyclic shift is the one equivalence the exposition forces

Shomorony et al. define the reconstruction target as a cycle `c` with
“`st(c) = s` up to cyclic shifts”, and both Theorem 1 and Corollary 1 repeat
“up to cyclic shifts”. The data-generating model is a circular genome
`st(c) = s` with `s[t+G] = s[t]`. [source fact]

Reverse complement is **not** an identification in the theory. It enters only
as experimental preprocessing: “before running NOT-SO-GREEDY, we preprocess the
set of reads to include each read and its reverse complement.” Under the
circular-window likelihood, rotating a candidate preserves its length and its
circular length-`L` window multiset, so the likelihood is invariant under
rotation. [source fact + mathematical fact]

Medvedev–Brudno §3.1 makes a read a DNA *molecule*, “an unordered pair of
strings … that are reverse complements of each other”, and §4.1 represents
“each `k`-molecule … only once”. Under a molecule-class index set, the
likelihood is additionally invariant under reverse complement of a candidate.
So the read-type convention and the equivalence convention are one coupled
choice: oriented read types support cyclic shift only; molecule read types
support the dihedral quotient. This coupling is derived independently in the
concurrent unmerged note
`analysis/issue36-equiv-ties-wp:docs/source-notes/equivalence-and-tie-wellposedness.md`
(§4, Facts 3–4) and is not re-derived here. [source fact + mathematical fact]

## 3. The decisive logical point

Let `W` be the weak schema and `S` the strong schema:

```text
W :  ∀ candidate, L(candidate) ≤ L(truth)
S :  W ∧ ∀ candidate, (L(candidate) = L(truth) → candidate ≈ truth)
```

**Fact (strict witness defuses all tie/equivalence choices; mathematical fact).**
If some candidate `D` has `L(D) > L(truth)`, then `W` is false, hence `S` is
false for every `≈`. The equivalence relation appears only in the antecedent of
`S`'s uniqueness conjunct, which is reached only by candidates tied with the
truth. A strictly better candidate never enters it. ∎

Two consequences:

- **Equivalence conventions act only on the tie set.** Changing `≈` cannot
  change the truth value of `W`, and cannot make a strict competitor stop
  violating `W`.
- **Tie semantics are irrelevant to a strict witness.** If every top candidate
  were tied, then the choice between “merely a maximizer” and “unique up to `≈`”
  would matter; a strict competitor makes that distinction moot for that
  instance.

The integrated witnesses are strict, so Fact applies to them directly. This is
also the mechanism recorded (independently) in
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
for negative transfer across candidate classes, and in
[`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
§6. [mathematical fact]

## 4. Applied to the integrated strict witnesses

### 4.1 The two witnesses

- **Same length (PR #43, currently on `main`):** truth `S = AAATAT` (`G = 6`),
  `L = 3`, starts `(0,0,1,3,5)` (`n = 5`), `N = 6`; competitor
  `D = AAAAAT`, `|D| = 6`; observed molecule classes
  `x = {AAA:2, AAT:1, ATA:1, TAA:1}`; `d_S = {AAA:1, AAT:1, ATA:3, TAA:1}`,
  `d_D = {AAA:3, AAT:1, ATA:1, TAA:1}`. [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
- **Variable length (PR #40):** truth `S = AAATT` (`G = 5`), `L = 3`, starts
  `(0,1,4)`, `N = 5`; competitor `D = AAAATT`, `|D| = 6`; `x = {AAA:1, AAT:1,
  TAA:1}`; `d_S = {AAA:1, AAT:2, TAA:2}`, `d_D = {AAA:2, AAT:2, TAA:2}`.
  [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)

### 4.2 Kernel-checked strictness

On `main`:

- `AssemblyP1.SameLengthSection62Counterexample.samelength_se62_counterexample`
  proves `lik obs dS < lik obs dD` and `exactLik dD obs / exactLik dS obs = 3`,
  with no `sorry`/`axiom`/`admit`/`native_decide` and only the three standard
  axioms;
- `AssemblyP1.Section62BridgingCounterexample.se62_bridging_flow_counterexample`
  proves `lik obs dS < lik obs dD` (the `9/8` variable-length witness).

So both integrated witnesses are strict, not tie-based. [kernel-checked]

### 4.3 Independent robustness recomputation

`scripts/verify_conclusion_semantics_witness_robustness.py` (added with this
note) checks, with exact `fractions.Fraction` arithmetic:

| Witness | §6.1 binomial ratio | exact multinomial ratio | truth orbit | competitor orbit | disjoint |
|---|---|---|---|---|---|
| same-length, `AAATAT → AAAAAT` | `5` | `3` | 12 | 12 | yes |
| variable-length, `AAATT → AAAATT` | `9/8` | `125/108` | 10 | 12 | yes |

It also checks that both objectives are invariant under every cyclic shift and
the reverse complement of each candidate (molecule-class index set), and that
the competitor's dihedral orbit is disjoint from the truth's. Exit status is
non-zero on any failure. [verified computation]

The exact-multinomial ratios use the candidate-intrinsic `N(D)` of MB09 §6.1;
the §6.1-binomial ratios use the external `N`, matching the source reading.
[source fact]

## 5. Could any unresolved equivalence convention invalidate the witness?

**No, on the source-supported conventions.** [mathematical fact + verified computation]

1. `D` is not a cyclic shift and not a reverse complement (nor any cyclic shift
   of one) of `S` in either witness: the dihedral orbits are disjoint
   (§4.3). These are the only genome identifications the cited sources describe
   — Shomorony’s “up to cyclic shifts” and MB09’s molecule (reverse-complement)
   convention. So `D ≉ S` under either panel.
2. Even if one adopted a coarser equivalence that happened to relate `D` and
   `S`, the weak schema `W` would still be false, because `W` has no
   equivalence in it. Only the `UniqueSchema` uniqueness conjunct could change
   truth value — and `UniqueSchema` is `W ∧ …`, so it stays false.
3. The likelihood comparison is well defined on equivalence classes: rotating
   or reverse-complementing a candidate leaves both objectives unchanged
   (§4.3). So quotienting the candidate universe by `≈` does not affect the
   strict inequality.

**The one logical loophole, and why it does not apply.** If the published
conclusion were read as the bare conjunct “some maximizer is equivalent to the
truth” (dropping the requirement that the truth itself be a maximizer), then a
sufficiently coarse `≈` could make the witness consistent. That reading has no
source support: the sentence’s plain content is that the truth be a
maximum-likelihood sequence, and `W` is the minimal formalization of that
content. No cited source proposes an equivalence that identifies
different-composition words like `AAATAT`/`AAAAAT`, and the repository’s
`UniqueSchema` is defined as `W ∧ …`, not as the bare uniqueness conjunct.
[source gap + interpretation]

**What equivalence still cannot fix.** Equivalence is independent of the
already-documented load-bearing axes: the Medvedev–Brudno object/objective
(exact vs §6.1 binomial vs §6.2 flow), candidate length, the read-type/strand
convention, and the sample-size regime. Those remain the real obstacles to
calling the published problem settled; the equivalence convention does not add
a new one for these strict witnesses. [interpretation]

## 6. What this changes in the repository

- `MaximizerSchema` and `UniqueSchema` remain both correct to state; the open
  English sentence still does not select between them. Nothing here selects a
  published schema.
- For the *integrated strict witnesses*, the tie/equivalence question is now
  answered: they refute `W` and therefore `UniqueSchema`, for every genome
  equivalence, under both objectives tested. The clause “does not address the
  tie/equivalence semantics” in the witness notes can be replaced by a pointer
  to this note.
- The maximizer-vs-uniqueness ambiguity remains live for **positive** claims
  and for any candidate instance with no strict competitor; this note does not
  narrow that for the source question.
- The concurrent unmerged note
  `analysis/issue36-equiv-ties-wp:docs/source-notes/equivalence-and-tie-wellposedness.md`
  establishes the same general invariance/coupling facts (Lemmas 1–2,
  Facts 3–5). It should be reconciled and, if accepted, integrated so the
  repository does not carry this determination only on a branch. This note is
  its application to the witnesses currently on `main` and is written to be
  self-contained should that integration be deferred. [interpretation]

## 7. Epistemic status

| Claim | Status | Basis |
|---|---|---|
| Shomorony 2016 sentence states no tie rule, uniqueness, or equivalence | source fact | accepted PDF, Discussion p. i501 |
| MB09 §6.1/abstract state no tie rule or uniqueness | source fact | JCB 16(8), §6.1 and abstract |
| Shomorony target is `s` up to cyclic shifts; model is circular | source fact | accepted PDF, §2 |
| Reverse complement is preprocessing in Shomorony, not an identification | source fact | accepted PDF, §4.1 / results |
| MB09 reads are reverse-complement molecule pairs, represented once | source fact | JCB 16(8), §3.1, §4.1 |
| Read-type convention and genome equivalence are coupled | source fact + mathematical fact | MB09 §3.1/§4.1; concurrent wellposedness note |
| Strict competitor falsifies `W` and every stronger schema for any `≈` | mathematical fact | §3 |
| Same-length witness strict (`5`, `3`) | kernel-checked | `SameLengthSection62Counterexample` |
| Variable-length witness strict (`9/8`, `125/108`) | kernel-checked + verified computation | `Section62BridgingCounterexample`; §4.3 |
| Truth/competitor dihedral orbits disjoint; both objectives dihedral-invariant | verified computation | §4.3 script |
| No source-supported equivalence relates the witness pairs | mathematical fact + verified computation | §5, §4.3 |
| The bare-uniqueness loophole is not the published reading | source gap + interpretation | §5 |
| Which ML object / objective / regime the sentence intends | source gap | referent notes (not re-opened here) |

## 8. Reproduce

```sh
python3 scripts/verify_conclusion_semantics_witness_robustness.py
lake build AssemblyP1.SameLengthSection62Counterexample
lake build AssemblyP1.Section62BridgingCounterexample
```

The Python script is self-contained, exact, deterministic, uses only the
standard library, and exits non-zero on any failed assertion.

## 9. Cross-references

- [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md):
  the maximizer-vs-uniqueness source ambiguity.
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md):
  the two conclusion schemas and the `genomeEquiv`-as-parameter rule.
- [`../section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
  and [`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md):
  the integrated strict witnesses (PR #43, PR #40).
- [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md):
  negative transfer across candidate classes.
- `analysis/issue36-equiv-ties-wp:docs/source-notes/equivalence-and-tie-wellposedness.md`
  (unmerged branch): concurrent derivation of the invariance/coupling facts.
- `AssemblyP1/Model.lean`, `AssemblyP1/OpenProblem.lean`: the abstract schemas.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2, §4.1, §5, DOI
`10.1093/bioinformatics/btw450`; Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1,
§4.1, §6.1–6.2, DOI `10.1089/cmb.2009.0047`.
