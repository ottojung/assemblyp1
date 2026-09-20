# Does the integrated `AAATT → AAAATT` §6.2 witness survive the most faithful
# Shomorony 2016 conventions?

_Status: independent primary-source reading + exact finite computation,
2026-09-20. This note audits the **write-up-merged** witness on `main`
([`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md),
[`../section62-mb09-bidirected-graph-audit.md`](../section62-mb09-bidirected-graph-audit.md))
against the published Shomorony et al. (2016) model, axis by axis, and
reconciles the result with the earlier branch audit
([`issue36-aaatt-convention-audit.md`](issue36-aaatt-convention-audit.md), same
branch). Every claim is labelled **source fact**, **mathematical fact**,
**verified computation**, **interpretation**, or **open**._

_Reproduction:
`python3 scripts/verify_issue36_aaatt_faithful_conventions.py` (self-contained,
exact `Fraction`, deterministic, exits non-zero on any failed assertion). The
witness's own `9/8` and graph/flow certificate are reproduced by the `main`
scripts named in the two `main` notes above._

## 0. Verdict

**The integrated `AAATT → AAAATT` witness is not robust across the conventions
that the published paper itself fixes.** It is a genuine strict negative result
in exactly one panel — circular, **variable**-length candidate, reverse-complement
**molecule-class** read types, MB09 §6.1 product-of-binomial-marginals with
external `N = |S|`, per-instance `n < N` — and it is inapplicable or false in
the panels obtained by restoring the two axes Shomorony's own text fixes:

| panel | circular | candidate length | read types | candidate class / objective | integrated witness |
|---|---|---|---|---|---|
| A (the `main` claim) | yes | **variable** (`\|D\| = 6 ≠ N = 5`) | revcomp **molecule classes** | §6.2 spelled circuits / §6.1 binomial with external `N` | **works**: `9/8 > 1` |
| B | yes | **fixed `G = 5`** | revcomp molecule classes | circular sequences / §6.1 exact and binomial | **inapplicable**; truth is a maximizer (10 tie maximizers) |
| C | yes | **fixed `G = 5`** | **single-strand oriented** (`4^k`) | circular sequences / §6.1 exact and binomial | **inapplicable**; truth is *beaten* at length `5` by `AAAAT` etc. |

Panels B and C use the sequence-level §6.1 objective over **all** circular
candidates of length `G`; they do not restrict to §6.2-spellable circuits. The
distinction matters: panel C's winners contain the unobserved oriented window
`ATA`, so they are not §6.2-spellable on the observed-read graph, but they are
perfectly admissible circular candidate genomes for the exact and §6.1-binomial
objectives. The integrated witness is the only one of the three that tests the
**§6.2-flow-restricted** candidate class. [interpretation]

[verified computation + source facts]

Two consequences sharpen the record:

1. **The witness cannot be carried to the most faithful Shomorony panel.** Under
   Shomorony's own model the truth is a single circular sequence of length `G`
   (`G = 5`), and its theory is single-strand; the witness's competitor has
   length `6`, and the witness's truth is unsupported under oriented read types.
   [source facts + verified computation]
2. **Its failure does not rescue the published implication.** Under the same
   most-faithful single-strand, fixed-`G` panel, the truth `AAATT` is *already*
   refuted by a same-length oriented candidate (`AAAAT` and four rotations), and
   the repository's kernel-checked same-length witnesses (#31/#32) refute the
   fixed-length exact/binomial objectives independently. So the integrated
   witness is a **convenience artifact**, not the load-bearing negative result.
   [mathematical fact + verified computation + kernel-checked, elsewhere]

## 1. Primary-source semantics

### 1.1 Shomorony et al. 2016

All quotes are from the accepted typeset article (DOI
`10.1093/bioinformatics/btw450`; retrieved text `InfoOptimalAssy.pdf`,
previously hash-pinned in `shomorony-ml-reference.md`).

- **Circular, fixed length `G`.** §2: “For ease of exposition, we will assume
  that `s` is a circular sequence of length `G`; i.e. `s[t + G] = s[t]` for any
  `t`. … each of the `N` reads is drawn independently and uniformly at random
  from the set of length-`L` substrings of `s`, `{s[t : t+L-1] : t = 1, …, G}`.”
  [source fact]
- **Single strand in the theory.** Reads are substrings of the one sequence `s`;
  reverse complements are **not** in the model. §4.1 then adds them only as
  experimental preprocessing: “In order to handle the fact that reads can come
  from both strands of the genome, before running NOT-SO-GREEDY, we preprocess
  the set of reads to include each read and its reverse complement.” This adds
  orientation nodes; it does not quotient `x` with `revcomp(x)`. [source fact]
- **Reconstruction target is cyclic shift only.** §3/Theorem 1/Corollary 1:
  “up to cyclic shifts.” No reverse-complement equivalence is asserted.
  [source fact]
- **Bridging conditions.** `R ∈ I_s` means coverage plus all triple repeats
  all-bridged and all interleaved pairs bridged, and the paper's theorem is that
  NOT-SO-GREEDY then recovers `s` “up to cyclic shifts.” That is an
  **algorithmic reconstruction** guarantee, not an ML-optimality guarantee.
  [source fact]
- **The open sentence.** §5 (Discussion): “Understanding whether bridging
  conditions can be used to guarantee that the maximum-likelihood sequence is
  the true sequence is currently an open question.” It carries no section,
  equation, or formula pointer into Medvedev–Brudno (2009). [source fact]

### 1.2 Medvedev–Brudno 2009

From the full text (PMC3154397; `mb09.txt` line references below).

- **Reads are molecules.** §3.1: “A DNA molecule is an unordered pair of strings
  (also called strands) that are reverse complements of each other. … A
  `k`-molecule is a DNA molecule whose corresponding strings have length `k`.”
  §4.1: “each `k`-molecule is represented only once.” [source fact]
- **§6.1 is internally tense on read types.** “Let `D` be a circular genome of
  length `N(D)`, and let `d_i` denote the number of times the `k`-molecule `i`
  appears in `D`. … Let the random variable `X_i` denote the number of trials
  whose outcome is `i`. **There are `4^k` such variables** …” The model
  vocabulary is molecule classes; the index count is oriented `k`-mers. This is
  the recorded source-internal tension (also audited in the branch note
  `reverse-complement-strand-convention.md`, §2.2, on
  `analysis/source-bridging-witness-reconstruction-0920`). [source fact]
- **§6.1 exact vs approximation.** Exact: `L(D|x) ∝ ∏_i (d_i/N(D))^{x_i}` with
  the candidate's own length. The approximation replaces `N(D)` by the external
  known actual genome length `N` and assumes the genome size is known. The
  product runs over all read types, so a type with `x_i = 0` contributes the
  factor `(1 − d_i/N)^n`. [source fact]
- **§6.2 object.** “The vertices of this graph are the reads, and the edges are
  all possible bidirected overlaps of length at least `o_min`.” “Each vertex has
  a lower bound of 1 … All other lower bounds are 0 and all upper bounds are
  infinity.” The genome is a circuit. The candidate is a **flow** (a possibly
  non-contiguous assembly), and `§6.2` is MB09's *algorithm*, not a
  sequence-valued “formulation.” [source fact]

### 1.3 What the two sources jointly fix, and what they do not

The published question is Shomorony's, and the model in which it is posed is
Shomorony's: **circular, fixed `G`, single-strand, cyclic-shift equivalence**.
The ML formulation it points at is MB09's, whose read-type and candidate-length
semantics are a separate, partly self-tense matter. The “most faithful”
conjunction is therefore neither trivially Shomorony's nor trivially MB09's, but
any robust negative witness should survive the axes both papers agree on:
**circular indexing** and **fixed candidate length `G`**. The integrated witness
survives the first and not the second. [interpretation]

## 2. Panels A–C, computed

Instance throughout: truth `S = AAATT` (`G = 5`), `L = 3`, realized starts
`(0,1,4)`, so `n = 3` observed reads. The read set satisfies Shomorony's `I_s`
under the strict bridging predicate (coverage; the unique maximal triple repeat
`A@{0,1,2}` is all-bridged; the interleaving conjunct is vacuous), independently
of the read-type axis, as certified in
[`../bridging-se62-flow-ml-counterexample.md`](../bridging-se62-flow-ml-counterexample.md)
§3.1 and kernel-checked by `AssemblyP1/Section62BridgingCounterexample.lean`.
[verified computation + kernel-checked]

### 2.1 Panel A — variable-length + molecule classes (the `main` claim)

Molecule-class spectra: `x = {AAA:1, AAT:1, TAA:1}`,
`d_S = {AAA:1, AAT:2, TAA:2}`, competitor `D = AAAATT` with
`d_D = {AAA:2, AAT:2, TAA:2}`. Both have support `{AAA, AAT, TAA}`, so all
zero-count §6.1 factors are `1`; the only changing factor is `AAA` (`1 → 2`),
giving `[(2/5)(3/5)^2]/[(1/5)(4/5)^2] = 9/8`. [verified computation;
kernel-checked on `main`]

### 2.2 Panel B — fixed length `G = 5` + molecule classes

Exhaustive over all `2^5 = 32` circular length-5 candidates under both the exact
candidate-intrinsic multinomial and the §6.1 fixed-`N` binomial:

- maximum ratio `1`, attained by the truth;
- exactly ten maximizers, the full dihedral orbit of `AAATT`
  (`AAATT, AATTA, ATTAA, TAAAT, TTAAA` and their reverse complements).

So in panel B the **truth is a maximizer** (indeed the unique one up to dihedral
equivalence), and the length-6 witness is inadmissible. This reproduces the
earlier branch audit's §5. [verified computation, exhaustive]

### 2.3 Panel C — fixed length `G = 5` + oriented single-strand

This is the axis combination the earlier audit did **not** compute. Under the
oriented read-type space (Shomorony single-strand, and MB09 §6.1's literal
`4^k`), the truth's windows are `{AAA, AAT, ATT, TTA, TAA}` while the observed
windows are `{AAA, AAT, TAA}`; `ATT` and `TTA` are unobserved but **present in
the truth**, and each contributes the §6.1 zero-count factor `(1 − 1/5)^3`, or
is simply absent from the exact multinomial.

Exhaustive over all `2^5 = 32` circular length-5 candidates:

- **exact candidate-intrinsic multinomial:** best ratio `2`, attained by
  `{AAAAT, AAATA, AATAA, ATAAA, TAAAA}` (the five rotations of `AAAAT`);
- **§6.1 fixed-`N` product of binomial marginals** (`N = 5`, `n = 3`): best
  ratio `1125/512 ≈ 2.197`, attained by the same five words;
- every winner keeps the three observed oriented types and has `d(AAA) = 2`.

So under the most faithful Shomorony panel the fixed-length implication is
**already false**, without the length-6 competitor and without reverse-complement
collapse. [verified computation, exhaustive]

## 3. What the bridging conditions actually guarantee

`I_s` constrains the *realized read set* relative to the truth: coverage and
repeat bridging. The 2016 theorem turns that into exact reconstruction “up to
cyclic shifts” by a specific algorithm. Neither paper derives from `I_s` any
statement about an arbitrary competing candidate's likelihood. This is why the
hypothesis can hold while the ML conclusion fails in panels A and C, and why
“bridging conditions guarantee …” must be read as algorithmic reconstruction,
not ML optimality. [source fact + interpretation]

## 4. Determination

1. **The integrated `AAATT → AAAATT` witness does not survive the most faithful
   conventions.** It requires (i) a candidate of length `6` while Shomorony fixes
   the genome length to `G = 5`, and (ii) reverse-complement molecule classes
   while Shomorony's theory is single-strand (and MB09 §6.1's literal index set
   is oriented `4^k`). Restoring either axis removes the witness: panel B has the
   truth as a fixed-length maximizer, and panel C has the truth unsupported under
   oriented types. [source facts + verified computation]
2. **The witness is nevertheless a legitimate panel-A result.** In its named
   panel it is a strict `9/8` negative result and settles the
   §6.2-restricted implication left open by the pre-#40 branches. It must be
   cited with its panel, never as “AAATT settles Shomorony 2016.”
   [mathematical fact + verified computation]
3. **The negative conclusion is panel-robust, the witness is not.** Panel C
   supplies same-length oriented counterexamples for this very truth (`AAAAT`,
   ratio `2` exact / `1125/512` binomial), and the repository's kernel-checked
   #31/#32 same-length witnesses cover the fixed-length exact/binomial
   objectives by candidate-set inclusion. So nothing about the settlement of the
   per-instance negative result depends on promoting the merged witness past its
   panel. [mathematical fact + verified computation]

## 5. Reconciliation with existing artifacts

- The earlier branch audit
  ([`issue36-aaatt-convention-audit.md`](issue36-aaatt-convention-audit.md))
  reaches the same conclusions for circularity, rotation, reverse-complement
  read-type collapse, known length (panel B), and ties. Its §5 “known-length
  reading is not refuted” is correct **for molecule-class read types**; §2.3
  here shows that under the oriented read-type axis the fixed-length reading is
  refuted, so “known length” and “strand/read-type” are not independent axes.
  This note is the cross-axis correction. [source fact + verified computation]
- `main`'s witness note already flags both boundaries (“Candidate length” and
  “Strand reading” in §0, and the two open items in §10); this note supplies the
  exhaustive fixed-length numbers behind the second boundary and the panel-C
  counterexample. [repository fact]
- [`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md)
  covers the fixed-length positive/negative transfer logic for #31/#32; the
  panel-C result is a concrete same-length oriented instance of that logic on the
  `AAATT` truth. [mathematical fact]
- The branch note `issue36-finite-vs-asymptotic-regime.md` (on
  `analysis/source-bridging-witness-reconstruction-0920`) records the
  per-instance/high-coverage fork; the panels here are all per-instance
  (`n = 3 < N = 5`). [source fact]

## 6. Epistemic status

| claim | status |
|---|---|
| Shomorony model: circular, fixed `G`, single-strand, cyclic-shift target; revcomp only preprocessing | **source fact** (§2, §3, §4.1, Theorem 1) |
| Bridging ⇒ NOT-SO-GREEDY reconstruction up to cyclic shift, not ML optimality | **source fact** (Theorem 1; §5) |
| MB09 molecule read types; §6.1 `4^k` literal count; §6.1 exact `N(D)` vs external `N`; §6.2 lower bound `1` | **source fact** (§3.1, §4.1, §6.1–6.2) |
| Panel A: variable-length molecule-class §6.1 binomial ratio `9/8` | **verified computation** + kernel-checked on `main` |
| Panel B: fixed-`G` molecule-class max ratio `1`; ten dihedral-orbit maximizers | **verified computation, exhaustive** `{A,T}^5` |
| Panel C: fixed-`G` oriented best ratio `2` (exact) / `1125/512` (binomial), winners the five rotations of `AAAAT` | **verified computation, exhaustive** `{A,T}^5` |
| The integrated witness is inapplicable in panels B and C | **source fact + verified computation** |
| The most faithful conjunction includes fixed candidate length `G` | **interpretation** (Shomorony fixes `G`; MB09's exact objective does not, its approximation assumes known `N`) |
| Which MB09 object / length / strand the 2016 sentence denotes | **open**, unchanged |

## 7. Reproduce

```sh
python3 scripts/verify_issue36_aaatt_faithful_conventions.py
```

The script re-derives the instance, `x`, `d_S`, `d_D`, the `9/8` panel-A ratio,
the exhaustive panel-B and panel-C optima under both objectives, and the
oriented-support obstruction, using only Python integers and
`fractions.Fraction`.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, “Information-optimal genome assembly via sparse read-overlap graphs,”
*Bioinformatics* 32(17) (2016) i494–i502, §2, §3, §4.1, §5, DOI
`10.1093/bioinformatics/btw450`; Paul Medvedev, Michael Brudno, “Maximum
Likelihood Genome Assembly,” *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1,
§4.1, §6.1–6.2, PMC3154397.

Repository anchors: `main` `docs/bridging-se62-flow-ml-counterexample.md`,
`docs/section62-mb09-bidirected-graph-audit.md`,
`AssemblyP1/Section62BridgingCounterexample.lean`,
`AssemblyP1/FixedLengthExactCounterexample.lean`,
`AssemblyP1/FixedLengthBinomialCounterexample.lean`; same branch
`docs/source-notes/issue36-aaatt-convention-audit.md`.
