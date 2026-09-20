# Well-posedness of the 2016 ML conclusion: forced cyclic shift and read-type/equivalence coupling

_Status: primary-source and mathematical note for issue #36, 2026-09-20. It
records source facts, proves two elementary invariance lemmas, and derives what
they force about the genome equivalence appearing in the stronger conclusion
schema. It does not settle which Medvedev–Brudno layer the 2016 sentence
intends, nor the maximizer-vs-uniqueness reading. Every claim is labelled
**source fact**, **mathematical fact**, **verified computation**,
**interpretation**, or **source gap**._

## 0. Bottom line

1. **Forced cyclic shift (mathematical fact).** The exact read-count likelihood
   of Medvedev–Brudno (2009) §6.1 is invariant under cyclic rotation of a
   circular candidate, under either read-type convention, because rotation
   preserves the candidate length and the multiset of circular read windows.
   Consequently the stronger conclusion schema ("every maximizer is the truth
   up to genome equivalence") can only be satisfiable if the equivalence
   relation identifies cyclic shifts. That part of `genomeEquiv` is not a free
   modeling parameter.
2. **Read-type/equivalence coupling (mathematical fact).** Under oriented read
   types, reverse-complementing the candidate permutes the type counts through
   `t ↦ rc(t)`; the candidate and its reverse complement therefore tie for all
   observations only when read types are collapsed into reverse-complement
   classes. Hence MB09's `k`-molecule convention forces reverse-complement into
   the equivalence, while Shomorony's oriented `length-L`-substring convention
   does not. The two issue-#36 choices "read-type space" and "genome
   equivalence" are one coupled choice, not two independent ones.
3. **Witness consequence (mathematical fact).** Equivalence conventions affect
   only tie-based arguments. A competitor with *strictly* greater likelihood
   refutes both schemas regardless of the equivalence; a tied competitor that
   is a cyclic shift of the truth never refutes the strong schema; a tied
   reverse-complement competitor does so only under the oriented/cyclic-only
   panel.
4. **Not settled (source gap).** Which read type the 2016 sentence intends (and
   hence which equivalence), and the accepted supplementary ZIP, remain
   unresolved. See [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md)
   for the independent maximizer-vs-uniqueness ambiguity.

## 1. Primary sources and verification

| Artifact | Locator | SHA-256 |
|---|---|---|
| Shomorony et al., OUP-typeset article | `https://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf` | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Shomorony et al., author-accepted manuscript | `https://people.eecs.berkeley.edu/~courtade/pdfs/NSG.pdf` | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Shomorony et al., earlier preprint + supplement | `https://web.stanford.edu/~gkamath/nsgIlan.pdf` | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno (2009), published JCB PDF | `https://medvedevgroup.com/papers/jcb09.pdf` | `bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3` |

All four hashes were recomputed this run and match the ledger already on `main`
(`shomorony-mb-formulation-provenance.md` and `ml-sequence-contemporary-denotation.md`,
the latter a branch artifact). The publisher supplement remains HTTP 403 and
uninspected.

## 2. Source facts

### 2.1 Shomorony et al. 2016: circular single strand, cyclic shift, no revcomp in the theory

§2 (accepted typeset, PDF p. 2; source fact):

> "For ease of exposition, we will assume that `s` is a circular sequence of
> length `G`; i.e. `s[t + G] = s[t]` for any `t`. This way we will avoid edge
> effects and a read `x ∈ R` can correspond to any substring
> `s[t : t + L − 1]`, for `t = 1, …, G`."

> "each of the `N` reads is drawn independently and uniformly at random from
> the set of length-`L` substrings of `s`."

§2.1 (source fact): the reconstruction target is a cycle `c` on the read-overlap
graph with `st(c) = s` **"up to cyclic shifts"**; Theorem 1 and Corollary 1
repeat the phrase. There is no reverse-complement quotient in the theory.

§4.1 (source fact): reverse complement enters only as experimental
preprocessing — "In order to handle the fact that reads can come from both
strands of the genome, before running NOT-SO-GREEDY, we preprocess the set of
reads to include each read and its reverse complement." The double-strand
implementation "contains two rings, each corresponding to a cyclic contig"
(§results, PDF p. 8; source fact). It adds orientation nodes; it does not
identify a read with its reverse complement.

### 2.2 Medvedev–Brudno 2009: molecules and oriented counts

§3.1 (PDF p. 3; source fact):

> "A DNA molecule is an unordered pair of strings (also called strands) that
> are reverse complements of each other. … A `k`-molecule is a DNA molecule
> whose corresponding strings have length `k`."

§4.1 (source fact): in the bidirected de Bruijn graph "each `k`-molecule is
represented only once."

§6.1 (source fact):

> "Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … the probability that
> the outcome of a single trial is `i` is simply `d_i/N(D)`. … **There are `4^k`
> such variables** …"

`4^k` is the number of oriented `k`-mers, whereas the number of `k`-molecule
classes is `(4^k + p_k)/2` (with `p_k` the count of self-reverse-complement
`k`-mers). The formula's index count and the model's molecule vocabulary are in
tension; this is already recorded as a source-internal tension in the
repository's reverse-complement audit. It does not change the lemmas below: the
coupling holds whichever of the two literal readings is chosen.

§9 (PDF p. 15; source fact): MB's own retrospective label is "a maximum
likelihood framework for **sequence assembly**," even though §6.2 returns a
"(non-contiguous) assembly." This is additional evidence that the ML object is
sequence-valued.

## 3. Two invariance lemmas

Fix an alphabet `Σ` with a reverse-complement involution `rc` on words, a
circular word `D` of length `n = N(D)`, and a read length `L ≤ n`. For an
oriented word `t` of length `L`, let `occ(D, t)` be the number of start
positions `p ∈ {0, …, n−1}` whose circular length-`L` window equals `t`. The
MB09 §6.1 exact likelihood for an observed oriented count vector `x` is

```text
L(D; x) = (n! / ∏_t x_t!) · ∏_t (occ(D, t) / N(D))^{x_t}.
```

(Under the molecule convention the index set is reverse-complement classes and
`occ` is the class count.)

**Lemma 1 (cyclic-shift invariance; mathematical fact).** If `ρD` is any cyclic
rotation of `D`, then `occ(ρD, t) = occ(D, t)` for every `t` and
`N(ρD) = N(D)`; hence `L(ρD; x) = L(D; x)` for every observation `x`, under
either read-type convention. _Proof._ A rotation is a bijection of the `n`
positions commuting with the map "position ↦ its circular length-`L` window";
it preserves both the multiset of windows and `n`. ∎

**Lemma 2 (reverse-complement relabelling; mathematical fact).** For every
oriented `t`, `occ(rc(D), t) = occ(D, rc(t))`, and `N(rc(D)) = N(D)`.
Consequently `L(rc(D); x) = L(D; rc·x)`, where `(rc·x)_t := x_{rc(t)}`.
_Proof._ Writing `rc(D)[j] := comp(D[n−1−j])`, the window of `rc(D)` starting at
`q` is `rc` of the window of `D` starting at `n − L − q` (mod `n`), and
`q ↦ n − L − q` is a bijection on start positions. ∎

**Corollary 2′ (molecule invariance; mathematical fact).** If read types are
reverse-complement classes and `occ_class(D, C) := Σ_{t∈C} occ(D, t)`, then
`occ_class(rc(D), C) = occ_class(D, C)` for every class `C`; hence
`L(rc(D); x) = L(D; x)` for class-indexed observations. _Proof._
`occ_class(rc(D), C) = Σ_{t∈C} occ(rc(D), t) = Σ_{t∈C} occ(D, rc(t))`, and
`t ↦ rc(t)` permutes the reverse-complement-closed class `C`. ∎

**Remark 2″ (oriented types are not reverse-complement-symmetric;
mathematical fact + verified computation).** The set of all oriented `L`-mers
*is* closed under `rc`, so the failure in Lemma 2 is not a failure of index-set
closure: it is that the statistic distinguishes `t` from `rc(t)`. Concretely,
for `D = AAAT` and `L = 1`, `occ(D) = {A: 3, T: 1}` while
`occ(rc(D)) = occ(TTTA) = {A: 1, T: 3}`. Lemma 1 (rotation), Lemma 2 (relabelling),
Corollary 2′ (molecule invariance), and this non-symmetry witness were checked
exhaustively over all circular words of length `≤ 6` over `{A, T}` and length
`≤ 5` over `{A, C, G, T}`, for all read lengths (7014 word/read-length pairs),
by `scripts/verify_equivalence_coupling.py` (verified computation).

## 4. What this forces about the conclusion schemas

Write `W`: "the truth is a maximizer" (`∀ candidate, L(candidate) ≤ L(truth)`)
and `S`: "every maximizer is the truth up to `≈`"
(`W ∧ ∀ candidate, L(candidate) = L(truth) → candidate ≈ truth`). These are the
repository's two schemas ([`../ml-formalization-contract.md`](../ml-formalization-contract.md) §"Conclusion variants").

**Fact 3 (cyclic shift is mandatory for `S`; mathematical fact).** The weak
schema `W` contains no equivalence relation and is unaffected by Lemmas 1–2.
For `S`, if `≈` does not relate some rotation of the truth to the truth, then
that rotation is a distinct candidate with equal likelihood by Lemma 1, and `S`
is false **for every instance with a non-rotation-fixed truth, independently of
any bridging hypothesis**. So a faithful strong statement must include the
cyclic-shift relation in `≈`. (`Model.lean` currently calls this an expectation;
Fact 3 upgrades it to a requirement for `S`.)

**Fact 4 (reverse-complement equivalence is coupled to the read-type
convention; mathematical fact).** Under oriented read types, `rc(truth)` ties
the truth for all observations only if the oriented count vector is
reverse-complement-symmetric, which fails in general (Remark 2″); so `S` under
oriented types does not require reverse complement in `≈`. Under the molecule
convention, `rc(truth)` always ties the truth (Corollary 2′) while generally
being a different word, so `S` under molecules **does** require reverse
complement in `≈`. Therefore:

```text
oriented read types  ⇒  cyclic shift suffices; rc is an extra identification
molecule read types  ⇒  cyclic shift + reverse complement (dihedral) is forced
```

The equivalence relation and the read-type space are one coupled choice. This
refines the repository's earlier framing of them as independent unresolved
parameters ([`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §8.2–8.3,
[`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md)).

**Fact 5 (equivalence affects only tie arguments; mathematical fact).** If
`L(candidate) > L(truth)` strictly, the competitor refutes `W` and therefore
`S` under any `≈`. The choice of `≈` can only decide whether a *tied* candidate
counts as a counterexample to `S`. This matters because the repository's
same-length witnesses are strict-inequality witnesses and are therefore
equivalence-robust; a purely tie-based argument would not be.

## 5. Application to the published source forks

- **Shomorony-faithful panel.** Read types are oriented length-`L` substrings
  (§2.1) and the theory's target is `s` up to cyclic shifts. By Fact 4 the
  natural equivalence is **cyclic shift only**; reverse complement is not an
  identification in the theory and appears only as §4.1 preprocessing that
  *adds* orientation nodes.
- **Medvedev–Brudno-faithful panel.** §6.1 counts `k`-molecules and §4.1
  represents each molecule once; by Fact 4 the equivalence is **dihedral**.
- **The 2016 sentence** cites MB09 for the likelihood but is stated about
  Shomorony's information-feasible instance. So the read-type convention that
  fixes the equivalence is precisely one of the unresolved issue-#36 choices;
  it is not an additional independent degree of freedom. A reader who imports
  MB09's molecules into the 2016 question thereby imports reverse-complement
  equivalence; a reader who stays in Shomorony's oriented model does not.

This does not decide which is intended. It narrows the source fork: selecting
"the ML sequence" and "the true sequence" up to an equivalence is selecting the
read-type convention, and vice versa.

## 6. Consequence for witness panels

Every counterexample or positive instance must declare the pair (read-type
convention, genome equivalence), and the declaration is constrained by Lemma 1
and Fact 4:

1. A tied maximizer that is a **cyclic shift** of the truth is never a
   counterexample to `S` once cyclic shift is in `≈`, and is irrelevant to `W`.
2. A tied maximizer that is **`rc(truth)`** refutes `S` only under the oriented
   / cyclic-only panel; under the molecule / dihedral panel it is equivalent to
   the truth and is not a counterexample.
3. A **strictly** more likely competitor refutes both schemas under either
   panel (Fact 5), so the existing same-length strict witnesses need only the
   candidate-class and length declarations already required by the contract,
   not an equivalence declaration.

## 7. What remains unresolved

1. **Which read type the 2016 sentence intends**, and therefore which
   equivalence: source gap; see [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
   and [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md).
2. **The exact multinomial vs the §6.1 fixed-`N` approximation vs the §6.2 flow**:
   unchanged; see the referent reconciliation.
3. **Maximizer vs uniqueness semantics**: unchanged; see
   [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md).
4. **The `4^k` vs `k`-molecule class count** in MB09 §6.1: unchanged
   source-internal tension.
5. **The accepted supplementary ZIP**: unretrieved (HTTP 403).

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Shomorony §2: circular `s`, oriented length-`L` read substrings, no revcomp in theory | source fact | accepted PDF, §2, §2.1 |
| Shomorony theory target is `s` up to cyclic shifts | source fact | accepted PDF, §2.1, Theorems |
| Shomorony §4.1 adds reverse complements for implementation, yielding two rings | source fact | accepted PDF, §4.1 and results |
| MB09: reads are DNA molecules (`rc`-pair classes), each represented once | source fact | MB09 §3.1, §4.1 |
| MB09 §6.1 counts `k`-molecules but writes `4^k` variables | source fact / source-internal tension | MB09 §6.1 |
| MB09 §9 calls the framework "sequence assembly" | source fact | MB09 §9 |
| Exact §6.1 likelihood is invariant under cyclic rotation of the candidate | mathematical fact | Lemma 1 |
| Reverse-complementing the candidate relabels oriented counts by `t ↦ rc(t)` | mathematical fact | Lemma 2 |
| Molecule-class counts are reverse-complement invariant | mathematical fact | Corollary 2′ |
| Small-case exhaustiveness of Lemmas 1–2 and Remark 2″ | verified computation | `scripts/verify_equivalence_coupling.py` |
| The strong schema requires cyclic shift in the equivalence | mathematical fact | Fact 3 |
| Reverse-complement equivalence is forced iff the molecule convention is used | mathematical fact | Fact 4 |
| Equivalence conventions can change only tie-based conclusions | mathematical fact | Fact 5 |
| The 2016 read-type convention (and hence equivalence) is unresolved | source gap | §5, §7 |

## 9. Cross-references

- [`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
  and [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md):
  the four Medvedev–Brudno referents.
- [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
  and [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md):
  candidate class and length semantics.
- [`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md):
  maximizer vs uniqueness, independent of this note.
- [`../ml-formalization-contract.md`](../ml-formalization-contract.md) §"Shared
  formal substrate" item 6 and §"Constraints" item 6: `genomeEquiv` as a
  parameter; this note sharpens what that parameter is coupled to.
- `AssemblyP1/Model.lean`: the two schemas and the `genomeEquiv` field.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502, §2–§5, DOI
`10.1093/bioinformatics/btw450`; Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, J. Comput. Biol. 16(8) (2009) 1101–1116, §3.1,
§4.1, §6.1, §9, DOI `10.1089/cmb.2009.0047`.
