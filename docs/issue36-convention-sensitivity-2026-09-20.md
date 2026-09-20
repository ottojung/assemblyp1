# Issue #36: independent test of the reverse-complement, lower-bound, and equivalence conventions

_Status: independent primary-source retrieval + exact-rational computation,
2026-09-20. Isolated branch `analysis/issue36-conventions-0920`. Every claim is
classified as **source fact**, **source reading**, **verified computation**,
**source ambiguity**, or **open**. This note does not change any Lean
definition and does not settle the 2016 question; it determines which
convention changes are load-bearing for the repository's
counterexample/flow frontier._

_Reproduce: `python3 scripts/issue36_convention_sensitivity.py` (self-contained,
no repository imports; exact `fractions.Fraction`; asserts every recorded
number; exits non-zero on mismatch)._

---

## 0. Result at a glance

The three unresolved conventions do **not** have the same status. All three are
resolved identically by the *Medvedev–Brudno* model panel and differently by the
*Shomorony* model panel, and only the intersection that the issue #36 witness
uses is load-bearing:

| convention | value needed for the `AAATAT → AAAAAT` counterexample | effect of changing it | load-bearing? |
|---|---|---|---|
| reverse-complement reading | DNA **molecules** (reads = unordered revcomp pairs) | single-strand reading: `4608 → 0` counterexamples; also removes the #31 inversion | **yes** |
| lower bound | **per-type** (`d_D(w) ≥ 1`) | per-occurrence (`d_D(w) ≥ x_w`): `4608 → 0` | **yes** |
| genome equivalence | irrelevant to the witness | cyclic vs cyclic+revcomp: `4608 → 4608`, `0` absorbed | **no** for the count, **yes** for consistency |

1. **The counterexample lives exactly at the intersection of the
   reverse-complement reading and the per-type lower bound.** Independently
   re-derived and re-enumerated: `(revcomp, per-type)` gives `4608`
   counterexamples over 12 truths at `G=6, L=3`; each of the other three
   convention combinations gives `0` (verified computation).
2. **The equivalence convention is inert on the witness.** No winning
   competitor is a cyclic shift or reverse complement of its truth, under either
   cyclic or dihedral equivalence (verified computation). But choosing the
   reverse-complement *reading* forces the *dihedral* genome identity (a
   molecule **is** its reverse complement), which conflicts with Shomorony et
   al.'s stated `up to cyclic shifts` conclusion. So equivalence is load-bearing
   for the *consistency of the model panel*, not for the witness count.
3. **The flow frontier is affected differently by each convention.** The lower
   bound changes the §6.2 flow polytope (per-type admits strictly more flows);
   the reading changes the overlap-graph vertex set (molecule classes vs
   strings); equivalence is irrelevant to flows.
4. **Independent retrieval upgrade.** The accepted Shomorony et al. text,
   including the open-question sentence and the `up to cyclic shifts`
   conclusion, was re-retrieved independently this run from a publisher-format
   copy (provenance in §1), removing the previous "accepted open-question
   wording not independently re-verified (Oxford HTTP 403)" limitation in
   `docs/source-notes/ml-objective-candidate-class-resolution.md` §1.2.

---

## 1. Independent retrieval provenance

### 1.1 Medvedev & Brudno 2009 (MB09)

Paul Medvedev, Michael Brudno, "Maximum Likelihood Genome Assembly,"
*J. Comput. Biol.* 16(8) (2009) 1101–1116, DOI `10.1089/cmb.2009.0047`,
PMCID `PMC3154397`. Full text re-read this run from
<https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>. Equation images (`M26`–
`M33`) are part of the source; body-text quotes are verbatim.

### 1.2 Shomorony, Kim, Courtade & Tse 2016 (accepted version, independently re-retrieved)

Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C. Tse,
"Information-optimal genome assembly via sparse read-overlap graphs,"
*Bioinformatics* 32(17) (2016) i494–i502, DOI `10.1093/bioinformatics/btw450`,
ECCB 2016.

This run retrieved the publisher-format accepted article from the author's
public copy at
<http://people.eecs.berkeley.edu/~courtade/pdfs/InfoOptimalAssy.pdf>:

- size `715274` bytes;
- SHA-256 `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da`;
- 9 PDF pages; printed pages `i494`–`i502`;
- footer: `Downloaded from https://academic.oup.com/bioinformatics/article-abstract/32/17/i494/2450780 by UNIVERSITY OF CALIFORNIA, Berkeley user on 26 June 2018`.

The open-question sentence is present verbatim (§5 Discussion), so the accepted
wording is now independently confirmed:

> "The maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009), on
> the contrary, seems to be robust to these issues, and thus a good candidate
> for the 'correct' formulation. Understanding whether bridging conditions can
> be used to guarantee that the maximum-likelihood sequence is the true sequence
> is currently an open question."

### 1.3 Ghodsi et al. 2013 (adjacent, for the double-strand factor)

Mohammadreza Ghodsi et al., "De novo likelihood-based measures for comparing
genome assemblies," *BMC Research Notes* 6:334 (2013), PMCID `PMC3765854`,
<https://pmc.ncbi.nlm.nih.gov/articles/PMC3765854/>. Re-retrieved this run; the
sentence on the strand-symmetry factor is confirmed verbatim in §3.4 below.

---

## 2. What each primary source fixes

### 2.1 MB09: reads are DNA molecules; lower bound is per read vertex

Source facts (MB09 §3.1, §6.1, §6.2):

- **Reads are molecules and reverse complements are the same object.**
  > "A *DNA molecule* is an unordered pair of strings (also called strands) that
  > are reverse complements of each other."
  > "The vertices of this graph are the reads" and "Each read is represented by
  > a single node."
  > "each *k*-molecule is represented only once" (§4.1).
- **Feasible lower bound §6.2.**
  > "The first step is to build a bidirected overlap graph from the set of
  > reads, which are DNA molecules."
  > "Each vertex has a lower bound of 1 since it represents a read that must be
  > present in the genome at least once. All other lower bounds are 0 and all
  > upper bounds are infinity."
  > "Since any flow can be decomposed into a collection of walks, our flow
  > represents a (non-contiguous) assembly of the genome."
- **Exact objective §6.1** uses `d_i/N(D)` over `4^k` read types, candidate
  length `N(D)`; the binomial approximation replaces `N(D)` by the external true
  length `N` ("we assume that the genome size is known").
- MB09 makes **no** claim that the maximizer is the truth, is unique, or is
  identified up to cyclic shift or reverse complement (verified: the strings
  "maximizer", "uniqueness", "cyclic shift", "rotation" do not occur; "unique"
  appears only in unrelated senses).

### 2.2 Shomorony et al. 2016: the true genome is a single circular string; conclusion is cyclic shift only

Source facts (§2, §3, §5):

- **The model is single-strand strings.**
  > "the genome `s` is an unknown sequence of length `|s| = G` which we wish to
  > assemble from a set of `N` reads `R`."
  > "For ease of exposition, we will assume that `s` is a circular sequence of
  > length `G`; i.e. `s[t + G] = s[t]` for any `t`."
  > "each of the `N` reads is drawn independently and uniformly at random from
  > the set of length-`L` substrings of `s`."
  > "each vertex `v ∈ V` has an associated string `st(v)` from the set of reads".
- **The reconstruction target is cyclic-shift equivalence only.**
  > "we will be instead interested in finding a cycle `c = (v_1, v_2, …, v_N,
  > v_1)` on `G` such that `st(c) = s` up to cyclic shifts."
  > Theorem 1: "…a cycle `c_s` that traverses every edge and for which
  > `st(c_s) = s` up to cyclic shifts."
  > Corollary 1: "…contains a unique Eulerian cycle `c_s`, and it satisfies
  > `st(c_s) = s` up to cyclic shifts."
- **Reverse complements appear only as an experimental preprocessing step**, not
  in the theory:
  > §4.1: "In order to handle the fact that reads can come from both strands of
  > the genome, before running NOT-SO-GREEDY, we preprocess the set of reads to
  > include each read and its reverse complement."
- **The open question names no MB09 subsection, objective, candidate universe,
  length convention, tie rule, or equivalence** (independently re-confirmed; it
  is a single sentence in §5 after the phrase "the maximum-likelihood
  formulation of the AP (Medvedev and Brudno, 2009)").
- **Shomorony's `I_s`** (`R` covers `s`; all triple repeats all-bridged;
  interleaved repeats bridged) is defined on the **single-strand** `s`; a copy of
  a triple repeat is bridged if "there is a read that extends at least one base
  before and one base after the repeat segment."

### 2.3 The source tension, stated exactly

The witness needs the MB09 model panel (reads = molecules, per-vertex "set of
reads") but the published question's vocabulary is Shomorony's (a
maximum-likelihood **sequence**; reconstruction "up to cyclic shifts"). The two
panels differ on two of the three conventions:

| convention | MB09 panel | Shomorony panel |
|---|---|---|
| reverse-complement reading | molecules (revcomp identified) | strings (revcomp only in §4.1 experiments) |
| lower bound at a read vertex | 1 per **read** ("set of reads") | no flow formulation; `R` is `N` sampled reads |
| genome equivalence | molecule (revcomp pair) ⇒ dihedral | cyclic shift only |

MB09 does not state a tie rule or a uniqueness claim; Shomorony does not state a
candidate universe or a lower-bound convention. Neither source, alone, fixes the
combination the witness requires.

---

## 3. Independent computation

`scripts/issue36_convention_sensitivity.py` re-derives, without importing any
repository module, the Observation-7 sequence-level feasibility predicate
(`supp(spec_L(D)) = supp(x)` plus the chosen lower bound) and the fixed-length
exact-multinomial ratio.

### 3.1 Witness convention matrix

Witness: `S = AAATAT`, `D = AAAAAT`, `L = 3`, starts `(0,0,1,3,5)`, `N = 5`.
`I_s(S, starts) = True`.

| reading | lower bound | truth feasible | competitor feasible | exact ratio | counterexample |
|---|---|---|---|---|---|
| single-strand | per-type | no | no | — | no |
| single-strand | per-occurrence | no | no | — | no |
| revcomp-molecule | per-type | **yes** | **yes** | **3** | **yes** |
| revcomp-molecule | per-occurrence | no | yes | — | no |

Mechanism (verified):
- Under single-strand, truth's spectrum is `{AAA:1, AAT:1, ATA:2, TAT:1, TAA:1}`;
  observed `x = {AAA:2, AAT:1, TAT:1, TAA:1}`. `ATA` is unobserved, so the truth
  fails support equality.
- Under revcomp (`A↔T`), `TAT` and `ATA` are the same molecule class, so the
  truth's spectrum becomes `{AAA:1, AAT:1, ATA:3, TAA:1}` with support equal to
  `supp(x)`.
- Under per-occurrence, the truth still fails because `d_S(AAA) = 1 < x_AAA = 2`.

### 3.2 Exhaustive `G=6, L=3, σ=2` search under all conventions

Re-enumeration of all truths, all `I_s`-valid start multisets, and all
fixed-length candidates `|D| = 6` with the same spectrum support, independently
of the repository script:

| reading | lower bound | equivalence | counterexamples | distinct truths | absorbed by equivalence |
|---|---|---|---|---|---|
| single-strand | per-occ | cyclic | 0 | 0 | 0 |
| single-strand | per-occ | dihedral | 0 | 0 | 0 |
| single-strand | per-type | cyclic | 0 | 0 | 0 |
| single-strand | per-type | dihedral | 0 | 0 | 0 |
| revcomp-molecule | per-occ | cyclic | 0 | 0 | 0 |
| revcomp-molecule | per-occ | dihedral | 0 | 0 | 0 |
| revcomp-molecule | per-type | cyclic | **4608** | 12 | 0 |
| revcomp-molecule | per-type | dihedral | **4608** | 12 | 0 |

This independently reproduces the recorded `4608` of
`docs/section62-fixed-length-bidirected-counterexample.md` and shows that the
equivalence convention does not move the count.

### 3.3 The reading convention also moves the *older* frontier

The reverse-complement reading does not only create the `AAATAT` witness; it
inverts the older #31 exact witness, independently re-checked:

| witness | single-strand | revcomp-molecule (`A↔T`) |
|---|---|---|
| #31 `S=AAATT → D=AAAAT` | neither feasible | truth feasible, competitor not (witness **inverts**) |

The read-tiled witness `S=AAABCBC → D=AAAAABC` (starts `(0,0,0,1,2,5,6)`) keeps
`truth = not feasible, competitor = feasible` under every involution tested
(`none`, `A↔B`, `B↔C`): its obstruction is carried by windows (`BCB`, `CBC`) to
which no observed molecule can collapse, so it is robust to the reading.

### 3.4 Adjacent primary support for the molecule reading

Ghodsi et al. 2013, Methods §"Error-free model for fragment sequencing",
verbatim (independently re-retrieved):

> "we can compute the probability of a read `r` given the assembled sequence as
> `p_r = n_r / 2L` … The factor 2 is due to the fact that reads are sampled with
> equal likelihood from both the forward and reverse strands of a DNA molecule.
> This formulation was previously used by Medvedev et al. [26] to define an
> objective function for genome assembly."

This corroborates that the standard read-count objective in the MB09 line is
double-stranded; it is evidence for the molecule/revcomp reading but is not the
Shomorony 2016 text and does not settle the open question.

### 3.5 Alphabet-involution caveat (independent finding)

`make_comp` in the repository search pairs consecutive symbols and fixes the last
one on an odd alphabet. For `σ = 3` this fixes the third symbol, which is **not**
the DNA complement restricted to three letters. The positive witness is binary
and uses only `A↔T`, which *is* the real DNA complement, so the `4608`
counterexample is real-DNA-valid. But the repository's **ternary revcomp scopes**
(`σ = 3`, entries such as `(6,3,3,"rc","type")`) are searches under an artificial
involution, not under real DNA; their zero counts are evidence about that
artificial model, not about DNA. This does not affect the recorded `4608` but
should qualify any claim of the form "no counterexample under reverse
complement" that is drawn from a ternary scope.

---

## 4. Determination: which convention changes affect which frontier

### 4.1 Counterexample frontier (fixed-length sequence-level §6.2)

- **Reverse-complement → single-strand: frontier collapses.** The `(6,3)`
  family goes `4608 → 0`, and #31 stops being a counterexample. The reading
  convention is the single most powerful lever on this frontier.
- **Per-type → per-occurrence: frontier collapses.** `4608 → 0`. The witness's
  truth fails only the multiplicity condition `d_S(AAA) ≥ x_AAA`.
- **Cyclic → dihedral equivalence: no change to the family.** `4608 → 4608`;
  no competitor is absorbed. It matters only because the reading and equivalence
  conventions are **not independent**: adopting molecules forces dihedral
  equivalence, contradicting Shomorony's cyclic-shift conclusion. Any settlement
  must therefore name *both* the reading and the equivalence together.

### 4.2 Flow frontier (the §6.2 non-spellable-flow gap)

- **Per-type → per-occurrence: directly changes the flow polytope.** The lower
  bounds on the read vertices are the flow constraints, so per-type admits
  strictly more flows (including non-spellable ones) than per-occurrence. The
  repository's variable-length non-spellable searches
  (`docs/section62-bidirected-flow-feasibility.md` §5–§6) used the
  per-occurrence/`N = G` setting; a per-type rerun is a genuinely different
  feasible set, not a relabeling.
- **Reverse-complement → single-strand: changes the vertex set.** Building the
  overlap graph from molecules collapses revcomp reads into one vertex; building
  it from strings does not. Since `AA` and `TT` (and `ATA`/`TAT`) are one vertex
  in the molecule graph and two in the string graph, the feasible flows differ.
  This is the same mechanism that creates the counterexample.
- **Equivalence: no effect.** Flows are not genomes; cyclic/dihedral identity has
  no bearing on the flow polytope or on Observation 7.

### 4.3 What would change the conclusion

- The published question is answered negatively (for the fixed-length,
  sequence-level §6.2 reading) **iff** one adopts *(revcomp reading, per-type
  lower bound)*. Either change alone makes it open.
- It is *not* rescued by the equivalence choice: whichever equivalence is used,
  the witness stands.
- The reading that the witness needs is the one MB09 uses but Shomorony's own
  theorem does not; the per-type lower bound is the literal reading of MB09's
  "set of reads" but is not forced by MB09's multiset sampling. The issue #36
  reconciliation is therefore genuinely a *cross-source* panel choice, not a
  detail internal to either paper.

---

## 5. Epistemic status

| claim | status |
|---|---|
| MB09 reads are DNA molecules; revcomp identified; §6.2 lower bound 1 per read; output may be non-contiguous | **source fact** (PMC3154397 §3.1, §4.1, §6.2) |
| MB09 states no maximizer/uniqueness/tie/equivalence claim | **source fact** (searched body text) |
| Shomorony accepted text: single-strand circular `s`, `up to cyclic shifts`, revcomp only §4.1 preprocessing | **source fact** (independently re-retrieved, SHA-256 §1.2) |
| Accepted open-question sentence wording | **source fact**, now independently re-verified (upgrades the prior "not re-verified" status) |
| `(revcomp, per-type)` witness `S=AAATAT, D=AAAAAT`, exact ratio 3, binomial 5 | **verified computation** (independent script) |
| `4608 → 0` under either single-strand or per-occurrence; `0` absorbed by equivalence | **verified computation** (independent exhaustive `G=6,L=3,σ=2`) |
| #31 inverts under revcomp; read-tiled is reading-robust | **verified computation** (independent script) |
| Ternary revcomp scopes use an artificial involution | **verified computation** (alphabet definition) |
| Which reading/lower-bound/equivalence the 2016 open question intends | **source ambiguity** (unchanged) |
| Ghodsi factor-2 double-strand sentence | **source fact** (PMC3765854, re-retrieved) |

---

## 6. Open questions

1. **Cross-source panel selection.** No located primary source selects the
   *(revcomp, per-type, dihedral)* panel or the *(single-strand, cyclic)* panel
   for the 2016 sentence. Issue #36 remains genuinely open at the source level.
2. **Per-type variable-length non-spellable search.** The flow frontier under
   the per-type lower bound with variable-length flows is unsearched; the
   per-occurrence zero result does not transfer.
3. **Real-DNA alphabet scopes.** The ternary revcomp scopes should be rerun with
   the true `A↔T, C↔G` involution (or restricted to alphabets closed under it)
   before their zero counts are relied upon.
4. **Tie semantics** and the **accepted supplement** remain as recorded in
   `docs/source-notes/ml-objective-candidate-class-resolution.md`.

## 7. Reproduce

```sh
python3 scripts/issue36_convention_sensitivity.py
```

Self-contained, deterministic, exact `fractions.Fraction`; prints the witness
matrix and the eight exhaustive `(reading, lower-bound, equivalence)` rows, and
asserts `4608` only for `(revcomp, per-type)` and `0` absorbed by equivalence.

Primary sources: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) 1101–1116, §3.1, §4.1, §6.1–6.2, PMC3154397;
Shomorony, Kim, Courtade & Tse, *Information-optimal genome assembly via sparse
read-overlap graphs*, Bioinformatics 32(17) (2016) i494–i502 (accepted copy,
SHA-256 in §1.2); Ghodsi et al., *De novo likelihood-based measures …*,
BMC Res. Notes 6:334 (2013), PMC3765854.

Cross-references: `docs/section62-fixed-length-bidirected-counterexample.md`,
`docs/section-6-2-feasible-set-membership.md`,
`docs/section62-bidirected-flow-feasibility.md`,
`docs/source-notes/ml-objective-candidate-class-resolution.md`.
