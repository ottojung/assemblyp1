# Uniform strand conventions and the bridging-to-ML frontier

_Status: independent from-scratch computation + source reading, 2026-09-20;
reconciled with `origin/main` (`cf6c357`, which adds the strict oriented
single-strand §6.2 rigidity theorem on top of `8b2f0fc`'s §6.1
index-orientation and conclusion-semantics work) on 2026-09-21. All claims are
labelled **source fact**, **mathematical argument**,
**verified computation**, **bounded computation**, or **open**. This note does
not settle the Shomorony et al. (2016) open question; it isolates exactly which
strand convention each existing witness needs and records the bounded-search
frontier for the strictly single-strand convention._

_Objective attribution. This note distinguishes two objectives that must not be
fused (see §1.3): the repository's **exact candidate-intrinsic multinomial**
(Variant E, the exact global read-count likelihood with the candidate's own
length `N(D)`) and the **literal MB09 §6.1 separable fixed-`N` binomial
approximation** (Variant A, `N(D)` replaced by an externally supplied genome
size `N`). Both are objects in MB09 §6.1: the exact candidate-intrinsic
multinomial is its first model, and the separable fixed-`N` binomial is the
approximation the paper then adopts for the flow algorithm. Neither is called
"the MB09 §6.1 objective" without qualification or substituted for the other.
Every witness and bounded-search table below is computed under the exact
candidate-intrinsic multinomial unless it explicitly says otherwise; the bounded
searches are **not** run under the fixed-`N` binomial reading. See
[`../ml-formalization-contract.md`](../ml-formalization-contract.md) (Variants E
and A), [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md)
§1-2, [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§2.1-2.2, and [`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md)._

_Reproduction:_

```sh
python3 scripts/uniform_strand_semantics_search.py --witness
python3 scripts/uniform_strand_semantics_search.py --search
python3 scripts/uniform_strand_semantics_search.py --bresler-ds
```

_The script is self-contained, exact (`fractions.Fraction`), deterministic, and
exits non-zero on any failed assertion._

---

## 0. Result at a glance

1. **The latest integrated kernel-checked witness is not uniform
   single-strand.** `AAATAT → AAAAAT`, starts `(0,0,1,3,5)`, kernel-checked on
   `main` (`AssemblyP1/SameLengthSection62Counterexample.lean`), is a genuine
   counterexample only under the Medvedev-Brudno **read-molecule** convention
   (reverse complements collapsed: `TAT ~ ATA`). Under the strictly
   single-strand oriented convention the same read set makes the competitor
   have likelihood **zero**: the observed oriented type `TAT` is absent from
   `D = AAAAAT`. [verified computation]

2. **A strict uniform single-strand counterexample does exist at the
   sequence level.** `S = AAATT`, `D = AAAAT`, `G = 5`, `L = 3`, starts
   `(0,1,4)`, exact-multinomial ratio exactly `2` (fixed-`N` binomial ratio
   `1125/512`), with a non-vacuous all-bridged triple repeat. It uses oriented
   windows only; no reverse complement occurs anywhere. It is an alphabet
   rename of the kernel-checked `AAABB → AAAAB` of
   `FixedLengthExactCounterexample.lean`, so it is not a new theorem, but it
   *is* the uniform-convention witness the `AAATAT` pair is often mistaken
   for. [verified computation; mathematical argument]

3. **Under strict single-strand semantics together with the §6.2
   spelled-circuit support condition, no same-length counterexample exists —
   and this is now a theorem on `main`, not merely a bounded search.** The
   bounded search recorded here is zero at binary
   `(G,L) ∈ {(5,3),(6,3),(6,4),(7,3)}` with start
   multiplicity up to `4`, and at ternary/quaternary `(5,3),(6,3)` up to
   multiplicity `2`. `main`'s
   [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
   proves the general statement: under `I_s` (in fact only its triple-repeat
   clause) the truth's spectrum is the unique positive circulation of total
   `G` on its window-support graph, so every same-length §6.2 spelled
   candidate ties the truth under both objectives, for every `G`, `L`, and
   alphabet. §6.2 forces every oriented window type of the truth to be
   observed, which removes the reverse-complement multiplicity that the
   `AAATAT` witness uses. [theorem on `main`; bounded computation here]

4. **The molecule (double-strand, reverse-complement-collapsed) convention
   reproduces `main`'s witness and admits larger ones.** Beyond `main`'s
   `(G,L) = (6,3)`, the same support-equality reading has a witness at
   `(G,L) = (8,3)`: `AAATTATT → AAAATAAT`, exact-multinomial ratio
   `1024/729 > 1` (and `5` at `(6,3)` under the fixed-`N` binomial reading,
   versus `3` under the exact multinomial). `G = 5` and `G = 7` are zero in
   scope. [bounded computation]

5. **The Bresler et al. (2013) double-strand remap is a different
   double-strand convention and yields no exact-multinomial counterexample in
   scope.** In that
   remap the genome is the length-`2G` concatenation `u · revcomp(u)`, each
   read is doubled, and the single-strand `I_s` applies to the length-`2G`
   sequence. For binary `G ≤ 6` no strict counterexample was found; at
   `G = 3` and `G = 5` the remapped `I_s` is already **unsatisfiable** in the
   searched multiplicities. [bounded computation]

---

## 1. Conventions, stated exactly

Throughout, the true genome is a circular word, reads are error-free, and the
data-generating model is independent uniform sampling over circular starts.

### 1.1 Single-strand (Shomorony 2016, §§2-3)

- **Read type.** The oriented length-`L` window `S[t..t+L)`. No reverse
  complement is taken. [source fact: the theory is a circular string `s`, and
  §4.1 treats reverse complements as experimental preprocessing only]
- **Candidate.** A circular word `D`; the evaluation compares the truth to `D`
  through their oriented window-count vectors. [source fact]
- **Equivalence.** Cyclic shift only. [source fact]

### 1.2 Double-strand molecule (Medvedev-Brudno 2009, §§3.1, 4.1, 6.2)

- **Read type.** The unordered reverse-complement class `{w, revcomp(w)}`
  ("a `k`-molecule is represented only once"). Multiplicity of a class is the
  number of sampled reads in the class. [source fact]
- **Candidate.** A circular word, scored through its class-grouped window
  counts. [source fact + source-supported inference]
- **Lower bound.** §6.2's per-read-vertex lower bound `1`, i.e. (for a spelled
  candidate) support equality `supp(d_D) = supp(x)`. [source fact; the
  per-occurrence strengthening `d ≥ x` is a different, stronger condition]

### 1.3 Objectives (two distinct models, never fused)

Both strand conventions below are scored, in this note, under the **exact
candidate-intrinsic multinomial** (the repository's Variant E). The **literal
MB09 §6.1 separable fixed-`N` binomial approximation** (Variant A) is a
different objective and is stated separately. Neither may be called "the MB09
§6.1 objective" without qualification.

**(a) Exact candidate-intrinsic multinomial (Variant E).** The exact global
read-count likelihood of Medvedev-Brudno §6.1's *first* model is multinomial
with the candidate's own length,

```text
L_E(D|x) = n! / (∏_c x_c!) · ∏_c (d_D(c)/N(D))^{x_c}.
```

For same-length candidates (`N(D) = N(S) = G`) the denominators and the
observation-only coefficient cancel and the ratio is
`∏_c (d_D(c)/d_S(c))^{x_c}`. This is what
`scripts/uniform_strand_semantics_search.py` computes (`exact_ratio`), and it is
the repository's fixed-length exact variant when competitors are restricted to
length `G`. [source fact for the exact multinomial; repository variant for the
fixed-length restriction]

**(b) Literal MB09 §6.1 separable fixed-`N` binomial approximation (Variant
A).** MB09 §6.1 then *abandons* the multinomial's coupling `N(D) = Σ_c d_c` for
separability and replaces `N(D)` by an externally supplied genome size `N` (the
length of the actual source genome; "we assume that the genome size is known").
The resulting objective is a product of binomial marginals,

```text
L_A(D|x) = ∏_c C(n, x_c) (d_c/N)^{x_c} (1 - d_c/N)^{n - x_c},
```

whose per-type cost is `c_c(d_c) = -(x_c log d_c) - (n - x_c) log(N - d_c)`.
This retains the zero-count factors `(1 - d_c/N)^{n-x_c}` and is **not**
`∏_c d_c^{x_c}`; even at same length it is not the fixed-length exact
multinomial. `scripts/uniform_strand_semantics_search.py` implements it as
`binomial_ratio` for the witness cross-checks only and does **not** run the
bounded searches under it. [source fact for §6.1 Variant A; see
[`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md) §2
and [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md)
§2.2]

Neither objective is selected by the Shomorony et al. (2016) sentence, and the
§6.2 flow algorithm operates on Variant A's fixed-`N` costs. Whether a
same-length ratio computed for Variant E has a corresponding Variant A result is
recomputed, not assumed, below.

### 1.4 `I_s` bridging (Bresler et al. 2013; Shomorony et al. 2016, Eq. (1))

Coverage, all-bridged maximal triple repeats, and bridged interleaved pairs,
with a read `[r,r+L)` bridging a copy `[t,t+ell)` iff on the integer lift
`r < t` and `t + ell < r + L`. Bridging is a property of the read's
*placement* on the true genome and is therefore orientation-agnostic under
either convention. [source fact + repository normalization]

---

## 2. The integrated `AAATAT → AAAAAT` witness is molecule-only

Integrate `main`'s witness data:

```text
truth S = AAATAT, G = 6, L = 3, starts (0, 0, 1, 3, 5)
competitor D = AAAAAT
```

| quantity | single-strand (oriented) | molecule (reverse complements collapsed) |
|---|---|---|
| `d_S` | `AAA:1, AAT:1, ATA:2, TAT:1, TAA:1` | `AAA:1, AAT:1, ATA:3, TAA:1` |
| `x` | `AAA:2, AAT:1, TAT:1, TAA:1` | `AAA:2, AAT:1, ATA:1, TAA:1` |
| `d_D` | `AAA:3, AAT:1, ATA:1, TAA:1` | `AAA:3, AAT:1, ATA:1, TAA:1` |
| support `d_S = x`? | **no** | yes |
| exact-multinomial ratio `L_E(D)/L_E(S)` | **0** (`TAT` observed, absent from `D`) | **3** |
| fixed-`N` binomial ratio `L_A(D)/L_A(S)` | **0** (`TAT` observed, absent from `D`) | **5** |

Under single-strand the observed type `TAT` is simply not produced by
`D = AAAAAT`, so the competitor has likelihood zero under either objective; and the truth is not even
a §6.2 candidate because `TAT` (a truth window) is observed but the truth is
scored on oriented types consistently, giving `supp(d_S) ≠ supp(x)` for the
spelled-circuit test. Collapsing `TAT = ATA` supplies the fourth class, makes
the truth support-feasible, and moves one unit of class multiplicity from the
over-represented `ATA` to the observed-heavy `AAA`, raising the exact-multinomial
ratio to `3` (and the fixed-`N` binomial ratio to `5`).
This is the cross-source panel discussed in
[`section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md)
§1.1-1.2 and §5: Shomorony's placement-based `I_s` combined with
Medvedev-Brudno's molecule read types. [verified computation; source-supported
inference]

---

## 3. Uniform single-strand: what actually holds

### 3.1 Sequence-level counterexample (no §6.2 feasibility)

```text
S = AAATT   (G = 5)
D = AAAAT   (same length)
L = 3,  starts (0, 1, 4)
x        = { AAA:1, AAT:1, TAA:1 }
d_S      = { AAA:1, AAT:1, ATT:1, TTA:1, TAA:1 }
d_D      = { AAA:2, AAT:1, ATA:1, TAA:1 }
exact-multinomial ratio L_E(D)/L_E(S) = 2
fixed-N binomial ratio  L_A(D)/L_A(S) = 1125/512
```

`I_s` is non-vacuous: coverage holds, and the maximal length-`1` triple repeat
`A@{0,1,2}` is all-bridged by the reads at starts `4, 0, 1` (copies `0, 1, 2`
respectively); there is no interleaved pair. The window `ATA` of `D` is **not**
observed, which is why this witness is not §6.2-spellable. [verified
computation]

This witness is `AAABB → AAAAB` under `T ↦ B`; the kernel-checked Lean module
[`FixedLengthExactCounterexample.lean`](../../AssemblyP1/FixedLengthExactCounterexample.lean)
already covers it, under the exact candidate-intrinsic multinomial. The bounded
search finds the same phenomenon across the real DNA alphabet: over
`{A, C, G, T}`, `(G,L) = (5,3)` has `12` substantive counterexample truth-orbits,
all at exact-multinomial ratio `2` (for example `AAACC → AAAAC`).
`G = 6, L = 3` over `{A,T}` has none in scope. [bounded computation]

### 3.2 Single-strand plus §6.2 support equality

Requiring `supp(d_S) = supp(x) = supp(d_D)` (the §6.2 spelled-circuit support
condition) removes the witnesses and leaves **no same-length counterexample**
under the exact candidate-intrinsic multinomial in the following scopes:

| alphabet | `G` | `L` | start multiplicity `≤` | `I_s` instances | exact-multinomial same-length beats |
|---|---|---|---|---|---|
| `{A,T}` | 5 | 3 | 3 | 3222 | **0** |
| `{A,T}` | 6 | 3 | 3 | 16956 | **0** |
| `{A,T}` | 6 | 3 | 4 | 73616 | **0** |
| `{A,T}` | 7 | 3 | 3 | 34452 | **0** |
| `{A,T}` | 5 | 4 | 3 | 3474 | **0** |
| `{A,T}` | 6 | 4 | 3 | 22842 | **0** |
| `{A,C,T}` | 6 | 3 | 2 | 12024 | **0** |
| `{A,C,G,T}` | 5 | 3 | 2 | 7376 | **0** |

These scopes are exhaustive within their stated bounds and were recorded here as
evidence before `main` proved the general statement. `main`'s
[`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md) now
proves that under `I_s` and the §6.2 support condition no strict same-length
counterexample exists for any `G`, `L`, or alphabet, under the exact
candidate-intrinsic multinomial and the fixed-`N` §6.1 binomial alike; the
bounded search here is corroborating evidence for the listed scopes, not the
proof. Because the search imposes only the necessary support condition (not the
full bidirected-circuit/transitive-reduction test), "zero under support
equality" also implies zero under the stronger §6.2 spelled-circuit test.
These searches use only the exact candidate-intrinsic multinomial; the literal
fixed-`N` binomial reading is not searched. [theorem on `main`; verified
computation, bounded here]

This is the sharp contrast with the molecule convention: collapse of
`TAT ~ ATA` is not a presentational choice here, it is the mechanism that
creates the multiplicity the winning competitor needs. Under strict
single-strand semantics no such mechanism was found.

---

## 4. Molecule convention: the frontier

With reverse complements collapsed and §6.2 support equality, same-length
counterexamples exist under the exact candidate-intrinsic multinomial:

| `G` | `L` | start multiplicity `≤` | exact-multinomial beats | representative (exact / fixed-`N` binomial) |
|---|---|---|---|---|
| 5 | 3 | 4 | 0 | — |
| **6** | **3** | **4** | **960** (orbit of one pair) | `AAATAT → AAAAAT`, `3` / `5` (main, kernel-checked) |
| 7 | 3 | 4 | 0 | — |
| 6 | 4 | 4 | 0 | — |
| **8** | **3** | **3** | **4540** | `AAATTATT → AAAATAAT`, `1024/729 ≈ 1.4047` / not computed |

The `G = 8` pair was re-verified by hand from the printed data: `I_s` holds
(coverage plus bridged triple and interleaved obligations, all satisfied), both
truth and competitor have support equal to the observed support, and the exact
same-length ratio is `1024/729`. It is recorded as **bounded computation**; it
has not been checked against the full bidirected graph/transitive-reduction
certificate the way the `G = 6` pair has on `main`. [bounded computation]

The occurrence of a `G = 8` frontier also shows that the `G = 7` zero on `main`
is not a structural threshold; the property is scattered across `(G,L)`.

---

## 5. Bresler double-strand extension: 2G remap

Bresler, Bresler and Tse (2013), *BMC Bioinformatics* 14(Suppl 5):S18, give the
double-strand extension explicitly in "Discussions and extensions":

> "DNA is double-stranded and consists of a length-`G` sequence `u` and its
> reverse complement `u~`. Each read is either sampled from `u` or `u~`. This
> more realistic scenario can be mapped into our single-strand model by defining
> `s` as the length-`2G` concatenation of `u` and `u~`, transforming each read
> into itself and its reverse complement so that there are `2N` reads.
> Generalized Ukkonen's conditions hold verbatim for this problem …"
> [source fact, retrieved from PMC3706340]

So the Bresler double-strand convention is **not** the Medvedev-Brudno molecule
collapse: it keeps oriented reads but doubles the genome and the read set. Under
this remap, with the single-strand `I_s` applied to the length-`2G` sequence and
a length-`G` candidate strand `v` represented by `v · revcomp(v)`. The search
below uses the exact candidate-intrinsic multinomial on the length-`2G` sequence
(`N(D) = 2G`), not the literal fixed-`N` binomial approximation:

| `G` | `L` | start multiplicity `≤` | `I_s` instances | exact-multinomial beats |
|---|---|---|---|---|
| 3 | 2 | 4 | 0 | 0 |
| 4 | 2 | 5 | 1000 | 0 |
| 4 | 3 | 4 | 496 | 0 |
| 5 | 3 | 6 | 0 | 0 |
| 5 | 4 | 6 | 0 | 0 |
| 6 | 3 | 7 | 228487 | 0 |
| 6 | 4 | 6 | 100512 | 0 |

Two features stand out. First, for `G = 3` and `G = 5` the remapped `I_s` is
**unsatisfiable** in scope (the reverse-complement junction creates triple
repeats whose copies the doubled reads cannot all bridge); the question is
therefore vacuous there, not positively answered. Second, at `G = 6`, where
`I_s` is heavily satisfiable, the truth still wins every time in scope. This is
a genuinely different behavior from the molecule convention, and it means the
"double-strand" question splits into at least two inequivalent formalizations.
[source fact + bounded computation]

---

## 6. Honest scope and status

| claim | status |
|---|---|
| Shomorony 2016 theory is single-strand, cyclic-shift-only; `I_s` is Bresler et al.'s placement condition | **source fact** |
| MB09 read types are reverse-complement molecules with per-vertex lower bound `1` | **source fact** |
| `AAATAT → AAAAAT` needs `TAT ~ ATA` collapse; single-strand exact-multinomial ratio is `0` (fixed-`N` binomial ratio also `0`) | **verified computation** |
| `AAATT → AAAAT` is a strict uniform single-strand sequence-level counterexample, exact-multinomial ratio `2` (fixed-`N` binomial ratio `1125/512`) | **verified computation** |
| No strict single-strand §6.2 same-length counterexample, any `G`, `L`, Σ, under either objective | **mathematical proof on `main`** ([`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)); the bounded search here corroborates the scopes of §3.2 |
| Molecule §6.2 has exact-multinomial same-length witnesses at `(6,3)` and `(8,3)` | **bounded computation** (the `(6,3)` one is kernel-checked on `main`) |
| Bresler 2G remap has no exact-multinomial counterexample in the scopes of §5, and is `I_s`-unsatisfiable at `G = 3,5` | **bounded computation** |
| Which strand convention the 2016 open question intends | **open** (source does not say) |
| A proof that uniform single-strand §6.2 always makes the truth a maximizer | **no longer open on `main`**: the rigidity theorem proves the same-length case for all `G`, `L`, Σ; the variable-length case remains outside its scope |

### What is *not* established

- The single-strand §6.2 same-length zero is proved on `main` (under `I_s` and
  the §6.2 support condition, for all `G`, `L`, Σ); this note's bounded search is
  only corroborating evidence for the listed scopes and is not the proof.
- The molecule `G = 8` witness has not been validated against the full
  bidirected graph / transitive-reduction certificate.
- The Bresler remap search used a candidate class of doubled strands `v ·
  revcomp(v)`; allowing arbitrary length-`2G` spelled candidates could change
  the result and was not searched.
- The bounded searches are run only under the exact candidate-intrinsic
  multinomial (Variant E). The literal MB09 §6.1 fixed-`N` binomial
  approximation (Variant A) is a different objective and is not searched here;
  only the individual witness ratios are cross-checked under it (§2, §3.1).
- Nothing here settles the tie/uniqueness semantics or which objective the 2016
  sentence intends.

---

## 7. Reproduce / cross-references

- `scripts/uniform_strand_semantics_search.py` — witnesses, bounded searches,
  Bresler remap; `exact_ratio` (Variant E) and `binomial_ratio` (Variant A).
- `main`: [`section62-same-length-bidirected-counterexample.md`](../section62-same-length-bidirected-counterexample.md),
  [`AssemblyP1/SameLengthSection62Counterexample.lean`](../../AssemblyP1/SameLengthSection62Counterexample.lean).
- `main`: [`fixed-length-exact-counterexample.md`](../fixed-length-exact-counterexample.md),
  [`AssemblyP1/FixedLengthExactCounterexample.lean`](../../AssemblyP1/FixedLengthExactCounterexample.lean).
- `main` objective/attribution notes: [`../ml-formalization-contract.md`](../ml-formalization-contract.md)
  (Variant E vs Variant A), [`medvedev-brudno-candidate-class.md`](medvedev-brudno-candidate-class.md),
  [`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
  [`mb09-se61-index-orientation-resolution.md`](mb09-se61-index-orientation-resolution.md).
- `main` single-strand §6.2 rigidity theorem (the same-length zero as a proof,
  not evidence): [`oriented-se62-rigidity-theorem.md`](oriented-se62-rigidity-theorem.md)
  and `scripts/verify_oriented_se62_rigidity.py`.

Primary sources. Guy Bresler, Ma'ayan Bresler, David Tse, "Optimal assembly for
high throughput shotgun sequencing," *BMC Bioinformatics* 14(Suppl 5):S18, 2013,
PMC3706340. Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome Assembly,"
*J. Comput. Biol.* 16(8) (2009) 1101-1116, §3.1, §4.1, §6.1-6.2, PMC3154397.
Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
"Information-optimal genome assembly via sparse read-overlap graphs,"
*Bioinformatics* 32(17) (2016) i494-i502, DOI 10.1093/bioinformatics/btw450.
