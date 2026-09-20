# Issue #36 convention audit for the `AAATT → AAAATT` witness

_Status: source reading + complete finite computation, 2026-09-20. This note
audits the six convention axes named for issue #36 — circular vs linear,
rotation, reverse complement, known genome length, ties vs strict maximizer, and
the meaning of "true sequence" — **against the specific `AAATT → AAAATT` witness**
on `main`
([`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)).
It does not introduce a new witness and does not settle which Medvedev–Brudno
object the 2016 sentence denotes. Every claim is labelled **source fact**,
**mathematical proof**, **verified computation**, **interpretation**, or
**open**._

_Reproduction: `python3 scripts/audit_issue36_conventions.py` (self-contained,
exact `fractions.Fraction`, deterministic; exits non-zero on any failed
assertion). The cited `9/8` certificate and the §6.2 graph/flow certificate are
reproduced by the `main` scripts named in those two notes._

## 0. Verdict at a glance

The claim "the `AAATT → AAAATT` instance settles Shomorony et al. 2016" is
**convention-contingent**. The witness refutes the published implication only
under one conjunction of conventions, and it fails or mutates under two of the
named axes.

| convention | role for this witness | verdict |
|---|---|---|
| circular (not linear) | **load-bearing** | the realized read `TAA` at start `4` only exists under circular indexing; a linear length-`5` truth cannot produce it |
| rotation (cyclic shift) | not load-bearing for the strict refutation; decisive for *uniqueness* phrasing | the `9/8` inequality is rotation-invariant; rotations of the competitor also win |
| reverse complement | **two distinct roles** | (a) read-*type* collapse is load-bearing; (b) genome-*equivalence* is not load-bearing for `9/8`, but decides uniqueness |
| known genome length | **load-bearing; witness fails** | competitor has length `6 ≠ N = 5`; no length-`5` candidate beats the truth (complete check), so the fixed-length reading is **not** refuted by this instance |
| ties vs strict maximizer | not a blocker for this witness | `9/8` is **strict**, so both schemas (`truthIsML` and `mlIsTruthUpToEquiv`) fall |
| true-sequence meaning | follows | since a strictly better candidate exists, the truth is not *a* maximizer, so "the ML sequence is the true sequence" is false in the witness's regime |

**Net.** In its own regime (circular, molecule-collapsed read types,
variable-length, §6.1 product-of-binomial-marginals over spelled §6.2 circuits,
per-instance) the witness is a genuine negative result and the tie ambiguity is
irrelevant because the inequality is strict. It does **not** transfer to the
known-length/candidate-length-`N` reading (the reading supported by the
contemporaneous literature) or to the oriented-`4^k` read-type space. Those are
the remaining conventions that a settlement claim must name.

## 1. The objects and the instance

### 1.1 Source objects

- **Shomorony et al. (2016)**, Eq. (1) and §5 (accepted text): the information
  feasible set `I_s` (coverage; all triple repeats all-bridged; interleaved
  pairs bridged) and the open question about "the maximum-likelihood sequence"
  and "the true sequence." [source fact, as reconstructed in
  [`../bridging-source-semantics.md`](../bridging-source-semantics.md)]
- **Medvedev–Brudno (2009)** §6.1: circular candidate `D`, `d_i` the copy count
  of `k`-molecule `i` in `D`, observed counts `x_i` over `n` reads, external
  known genome size `N`, tractable objective the product of per-type binomial
  marginals with `0 ≤ d_i ≤ N`. §6.2: read DNA-molecule vertices, all
  bidirected overlaps of length `≥ o_min`, transitive reduction (Myers), vertex
  lower bound `1`, edge lower bounds `0`, upper bounds `∞`, signed-incidence
  balance, supersource/sink at prohibitive cost. [source fact, quoted with
  locators in [`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md)
  §1 and [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §2]

### 1.2 The instance (verified computation)

```text
alphabet            {A, T};  rc: A ↔ T
truth               S = AAATT            (G = 5)
read length         L = 3
realized starts     (0, 1, 4)            (n = 3 reads)
external size       N = 5
observed molecules  x = { AAA:1, AAT:1, TAA:1 }
truth spectrum      d_S = { AAA:1, AAT:2, TAA:2 }     (Σ d_S = 5)
competitor          D = AAAATT           (|D| = 6)
competitor spectrum d_D = { AAA:2, AAT:2, TAA:2 }     (Σ d_D = 6)
§6.1 ratio          L_{6.1}(D) / L_{6.1}(S) = 9/8 > 1
```

Both `S` and `D` are admissible spelled §6.2 bidirected circuits on the
transitively reduced overlap graph of the observed molecules, `I_s` holds, and
the strict inequality is kernel-checked in
`AssemblyP1.Section62BridgingCounterexample` (the graph/flow certificate is the
companion Python script). [verified computation + kernel-checked; see the two
`main` notes above]

## 2. Circular vs linear

**Source fact.** Shomorony et al. fix a **circular** true sequence of length `G`
("For ease of exposition, we will assume that `s` is a circular sequence of
length `G`"); reads are the `G` circular length-`L` substrings. MB09 candidates
`D` are circular genomes. [source fact]

**Verified computation.** The witness is circular-load-bearing. Under a
**linear** length-`5` truth with `L = 3` there are only `G − L + 1 = 3` window
starts (`0,1,2`), and the start-`4` read `TAA` does not exist. Hence the
realized read set `{AAA, AAT, TAA}` — in particular `TAA` — is not producible
by the linear model, and the bridging certificate (which needs the wrap-around
read at start `4` to bridge the `A` triple repeat) does not carry over.

**Determination.** Circularity is **load-bearing and source-faithful** for this
witness: the accepted model and the cited MB09 objective are both circular. A
linear-model reading would invalidate the instance rather than refute the
claim, and the 2016 paper does not pose the question for a linear genome here.
[source fact + verified computation]

## 3. Rotation (cyclic shift)

**Source fact.** Shomorony's reconstruction target is "up to cyclic shifts"
(Theorem 1, Corollary 1); MB09 outcomes are circular molecules, so a spelled
sequence has no canonical origin. [source fact]

**Verified computation / mathematical fact.** The `9/8` comparison is a
function of the candidate's `L`-mer **spectrum**, which is invariant under
rotating the candidate. So:

1. every rotation of `D = AAAATT` is an equally winning competitor; and
2. rotating the truth does not change `L_{6.1}(S)`.

Therefore the **rotation convention is not load-bearing** for the strict
negative result: whether one regards genomes up to cyclic shift or as labelled
words, the witness still exhibits a strictly more likely candidate.
[mathematical proof + verified computation]

**Remaining role (uniqueness).** Rotation enters only the *strong* conclusion.
The kernel-checked Lean statement compares explicit linear arrays, so it models
labelled words rather than equivalence classes; harmless for the strict
inequality, but relevant to any "unique up to equivalence" phrasing. [source
fact about the formalization]

## 4. Reverse complement

The witness uses the reverse complement in **two independent ways**; they must
not be conflated.

### 4.1 Read-type collapse (load-bearing)

**Verified computation.** Under the **oriented** read-type space (MB09 §6.1's
literal "there are `4^k` such variables"), the truth's oriented windows are
`{AAA, AAT, ATT, TTA, TAA}`, while the observed oriented support is
`{AAA, AAT, TAA}`. The windows `ATT` and `TTA` are unobserved, so the truth is
not supported and the witness **does not exist**. It exists only after
collapsing each word with its reverse complement to a `k`-molecule class
(MB09 §3.1/§4.1: "each `k`-molecule is represented only once"), giving
`ATT ↦ AAT` and `TTA ↦ TAA`.

**Determination.** The revcomp **read-type collapse is load-bearing**. The two
primary sources are in tension here (MB09's molecule vocabulary vs its `4^k`
count), recorded already in
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md) §8.2;
the witness silently requires the molecule-class side. [source fact +
verified computation]

### 4.2 Genome equivalence (not load-bearing for `9/8`)

**Mathematical fact.** Because `D` strictly beats `S`, no equivalence relation
that identifies `D` with a maximizer can rescue the truth-is-maximizer claim
unless it identifies `D` with `S` itself — impossible, since equal-length
equivalent circular words have equal spectra and equal likelihood, while
`L_{6.1}(D) > L_{6.1}(S)`. So whether genome equivalence is cyclic-shift only
or dihedral (cyclic shift + revcomp) does **not** affect the strict refutation
for the variable-length reading. [mathematical proof]

**Remaining role (uniqueness).** Genome equivalence becomes decisive for the
strong schema in the **known-length** panel of §5. There, the exact-multinomial
and binomial length-`5` maximizers are exactly the ten words
`{AAATT, AATTA, ATTAA, TAAAT, TTAAA, AATTT, ATTTA, TAATT, TTAAT, TTTAA}`:

- these are precisely the **dihedral orbit** of `AAATT` (five rotations plus
  their five reverse complements), so under **dihedral** equivalence the truth
  is the unique maximizer up to equivalence;
- but `AATTT = rc(AAATT)` is a tie that is **not** a cyclic shift, so under
  **cyclic-shift-only** equivalence the truth is **not** the unique maximizer
  up to equivalence.

[verified computation, exhaustive over `{A,T}^5`]

## 5. Known genome length

**Source fact.** MB09 §6.1 says the approximation replaces `N(D)` by the
external `N`, "the length of the actual genome," and "**For our experiments, we
assume that the genome size is known.**" The §6.1 binomial domain is
`0 ≤ d_i ≤ N`; it does **not** impose `Σ_i d_i = N`. A contemporaneous
ML-assembly formulation (Ghodsi, arXiv:1302.4391v3, cited for the sequencing
model to MB09) fixes the candidate length to the known genome length `L` and
gives the scale-invariance reason (a free length makes the objective admit
infinitely many equal-value rescalings). [source facts; the Ghodsi quotations
are recorded in the repository branch note `ml-sequence-contemporary-denotation.md`
and the MB09 text in `mb-formulation-referent-reconciliation.md` §2]

**Verified computation (complete for this instance).** The `9/8` witness uses
`|D| = 6 ≠ N = 5`. If one adds the **known-length restriction** `|D| = N = 5`,
the witness is inadmissible. A complete enumeration of all `2^5 = 32` circular
length-`5` candidates under the same §6.1 product-of-binomial-marginals
objective (`N = 5`, `n = 3`, `x = {AAA:1, AAT:1, TAA:1}`) gives:

- **maximum ratio `1`**, attained by the truth `AAATT` itself;
- exactly ten maximizers, namely the dihedral orbit of `AAATT` (see §4.2);
- **no** length-`5` candidate with ratio `> 1`.

The same holds for the exact candidate-intrinsic-length multinomial objective
at `G = 5` (the ten maximizers are again the dihedral orbit).

**Determination.** The known-genome-length convention is **load-bearing and the
witness fails it**: the `AAATT → AAAATT` instance does **not** refute the
fixed-length/candidate-length-`N` reading; in this instance the truth is in fact
a maximizer. Because the check is exhaustive over length-`5` candidates, this is
stronger than the bounded-search evidence recorded in
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)
§10.2, but it is still an **instance-level** fact, not a proof that no
fixed-length witness exists. The general fixed-length sub-question remains
**open**. [verified computation + open]

**Reconciliation note.** This sharpens the existing "candidate length" register:
[same-length-witnesses-candidate-set-inclusion.md](same-length-witnesses-candidate-set-inclusion.md)
correctly observes that *same-length* witnesses transfer negatively to the
unrestricted class. That transfer runs one way. The `AAATT` witness runs the
other way (unrestricted competitor), so it does **not** transfer *down* to the
length-`N` class.

## 6. Ties vs strict maximizer

**Source fact.** Neither Shomorony et al. nor MB09 supplies a tie-breaking
rule; the repository keeps two schemas distinct
([`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md)):
`truthIsML` (truth attains the maximum) and `mlIsTruthUpToEquiv`
(`truthIsML ∧` every maximizer is equivalent to the truth).

**Mathematical fact.** The witness ratio is `9/8 > 1`, i.e. **strict**. A
strictly better candidate exists, so the truth is not a maximizer:

- `truthIsML` fails, and hence
- `mlIsTruthUpToEquiv` fails as well (it contains `truthIsML`).

**Determination.** The tie/equivalence ambiguity is **not a blocker for this
witness**: within the variable-length, molecule-class, §6.1-binomial, §6.2-
spelled-circuit regime, the strict inequality settles the published conclusion
negatively under *both* schemas. Tie semantics only re-enter once the
known-length restriction of §5 is imposed, where the revcomp tie
`AATTT = rc(AAATT)` makes the *uniqueness* phrasing depend on the equivalence
convention. [source fact + mathematical proof]

## 7. Meaning of "the true sequence"

**Source fact.** The 2016 sentence: "whether bridging conditions can be used to
guarantee that the maximum-likelihood sequence is the true sequence." On the
literal reading, this asserts that (some/the) ML-optimal sequence coincides with
the truth (up to the intended genome equivalence).

**Determination.** In the witness's regime the assertion is **false**: there is
a candidate `D = AAAATT` with strictly larger §6.1 likelihood than the truth, so
no ML-optimal sequence can be "the true sequence" here. This is the strongest
negative form — it does not rely on a tie, a non-unique maximizer, or an
equivalence-convention choice. [source fact + mathematical proof]

**Boundary.** The statement is *not* refuted for the known-length reading (the
truth is a maximizer there, §5) nor for the oriented read-type space (the
instance is not realizable there, §4.1). Consequently "AAATT settles Shomorony
2016" must be read as shorthand for "under the variable-length, molecule-class,
§6.1-binomial, spelled-§6.2 reading." [interpretation]

## 8. What the witness settles and what it does not

| question | answer |
|---|---|
| Refutes `truthIsML` / `mlIsTruthUpToEquiv` under variable-length, molecule-class, §6.1-binomial, spelled-§6.2 | **yes** (strict `9/8`) |
| Depends on circular indexing | **yes** (start-`4` wrap; §2) |
| Depends on reverse-complement read-type collapse | **yes** (`ATT`, `TTA` collapse; §4.1) |
| Depends on rotation convention | **no** for the strict refutation; **yes** for uniqueness phrasing (§3) |
| Depends on genome-equivalence convention | **no** for the strict refutation; **yes** for uniqueness phrasing (§4.2) |
| Refutes the known-length (`|D| = N`) reading | **no**; not applicable, and this instance is consistent with the truth being the unique-up-to-dihedral maximizer (§5) |
| Refutes the oriented-`4^k` read-type reading | **no**; witness not realizable (§4.1) |
| Refutes the linear-genome reading | **no**; witness not realizable (§2) |
| Settles which MB09 object the 2016 sentence denotes | **no** (source ambiguity; unchanged) |

## 9. Epistemic classification

| claim | status |
|---|---|
| Shomorony model is circular; reconstruction is up to cyclic shift | **source fact** (accepted text §2, §3, Theorem 1) |
| MB09 candidates are circular; §6.1 binomial replaces `N(D)` by known `N`, domain `d_i ≤ N` | **source fact** (MB09 §6.1) |
| MB09 reads are molecules; `k`-molecules are revcomp classes | **source fact** (MB09 §3.1, §4.1) |
| MB09 §6.1 writes `4^k` oriented variables (source-internal tension) | **source fact** |
| Contemporaneous ML-assembly fixes the candidate length to the known genome length | **source fact** (Ghodsi arXiv:1302.4391v3 §2, Appendix B) |
| The `AAATT` instance has `x`, `d_S`, `d_D`, ratio `9/8` as stated | **verified computation + kernel-checked** (main notes) |
| The realized `TAA` read requires circular indexing | **verified computation** (§2) |
| The oriented-`4^k` reading makes the truth unsupported | **verified computation** (§4.1) |
| `9/8` is strict and rotation/equivalence-invariant for the refutation | **mathematical fact** (§3, §4.2, §6) |
| No length-`5` candidate beats `AAATT`; the ten maximizers are its dihedral orbit | **verified computation, exhaustive** (`{A,T}^5`) |
| The general fixed-length sub-question | **open** |
| Which MB09 object the 2016 sentence denotes | **source ambiguity, unchanged** |

## 10. Reproduce and locators

```sh
python3 scripts/audit_issue36_conventions.py
```

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, "Information-optimal genome assembly via sparse read-overlap graphs,"
*Bioinformatics* 32(17) (2016) i494–i502, §2, Eq. (1), Theorem 1, §5, DOI
`10.1093/bioinformatics/btw450`; Paul Medvedev, Michael Brudno, "Maximum
Likelihood Genome Assembly," *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1,
§3.3–3.4, §4.1, §5.2, §6.1–6.2, PMC3154397; Mohammadreza Ghodsi,
"Constructing a genome assembly that has the maximum likelihood,"
arXiv:1302.4391v3, §1–§3, Appendix B.

Repository anchors (on `main`):
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md),
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md),
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
[`../ml-formalization-contract.md`](../ml-formalization-contract.md),
[`../literature/ml-tie-semantics.md`](../literature/ml-tie-semantics.md),
`AssemblyP1/Section62BridgingCounterexample.lean`.
