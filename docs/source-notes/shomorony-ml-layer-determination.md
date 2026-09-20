# Which Medvedev–Brudno maximum-likelihood layer does Shomorony et al. most faithfully reference?

_Status: focused source-fidelity determination for issue #36, 2026-09-20.
Independently re-reads the primary sources and reconciles three prior,
mutually inconsistent repository conclusions
(`shomorony-open-question-referent.md` on unmerged branch
`agent/shomorony-ml-semantics`; `shomorony-mb-formulation-provenance.md` on
`main`; and the 2026-09-20 issue #36 reconciliation comment)._

_Every claim is labelled **source fact**, **source analysis / interpretation**,
or **unresolved**. This note does not settle the published open problem and does
not by itself select a formal target; it fixes the most defensible reading of
Shomorony's citation and records the residual uncertainty. It does not change
`docs/open-problem.md` or any Lean definition._

## 0. Determination at a glance

**Most faithful reading (source analysis):** Shomorony's phrase
“the maximum-likelihood formulation of the AP (Medvedev and Brudno, 2009)”
denotes Medvedev–Brudno's maximum-likelihood **objective**, not an algorithm.
Within Medvedev–Brudno (2009), the canonical statement of that objective is the
**§6.1 global read-count likelihood**: the exact multinomial with per-trial
probability `d_i / N(D)` and candidate-dependent length `N(D) = Σ_i d_i`
(repository Variant E). The binomial product is explicitly introduced as an
**approximation** of that objective, and the §6.2 bidirected flow is explicitly
introduced as Medvedev–Brudno's **algorithm**.

| Reading of “the maximum-likelihood formulation” | Assessment |
|---|---|
| MB09's ML objective; canonical §6.1 exact global read-count likelihood (*Variant E*) | **Most faithful** (source analysis) |
| MB09's ML objective; §6.1 fixed-`N` separable/binomial approximation (*Variant A*) | **Serious rival**, not excluded (source analysis) |
| MB09's §6.2 bidirected-flow feasible optimization (*Variant F*) | **Least faithful** as a denotation of “formulation” (source analysis) |
| A broad ML principle the paper leaves underspecified | **Also literal**, but it does not select a layer (source analysis) |

**Residual uncertainty (unresolved):** the accepted 2016 text gives no section,
equation, or page pointer into Medvedev–Brudno; it contains no `multinomial`,
no `binomial`, and no candidate-length or flow discussion (source fact, §3.5).
Therefore *no* reading is proved. The fixed-`N` rival has genuine support from
“what MB actually implemented,” and the issue #36 comment's lean toward it is
not refuted here — it is weighed and kept live.

## 1. Question and method

Issue #36 asks whether the published open question most faithfully means the
exact multinomial with candidate-intrinsic `N(D)`, the fixed-`N` approximation,
the §6.2 flow set, or a broad principle. It also asks whether the existing
kernel-checked fixed-length witnesses suffice or whether §6.2 feasibility
remains essential.

Method: direct reading of the cached byte-identical primary artifacts already
ledgered in `primary-provenance-verification.md` and
`shomorony-mb-formulation-provenance.md`:

| Artifact | SHA-256 |
|---|---|
| Accepted Shomorony article, OUP typeset (`InfoOptimalAssy.pdf`, 9 pp.) | `ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043acfce3c4da` |
| Author-accepted manuscript (`NSG.pdf`, 8 pp.) | `daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c` |
| Earlier author-hosted preprint (`nsgIlan.pdf`, 23 pp.) | `f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a` |
| Medvedev–Brudno (2009) full text (`PMC3154397`) | HTML body + GIF equation assets |

The publisher supplement (sections A–G) remains unretrieved (OUP HTTP 403) and
is the one uninspected primary artifact that could change the determination.

## 2. Source facts: what the 2016 sentence says and does not say

### 2.1 The sentence and its paragraph

Accepted article, Section 5 (Discussion), final paragraph (printed p. i501–i502),
read end to end:

> “Another direction for future work, from a more theoretical standpoint, is
> understanding whether, in information-feasible instances of the AP, the output
> of NOT-SO-GREEDY coincides with the solution of a combinatorial optimization
> problem. Notice that while Theorem 1 guarantees the reconstruction of the true
> sequence `s`, there is no guarantee that this sequence corresponds to the
> solution of an optimization-based formulation of the AP such as those
> considered by Nagarajan and Pop (2009) and Medvedev and Brudno (2009). As
> mentioned by Medvedev and Brudno (2009), parsimony-based formulations tend to
> encourage an over-collapsing of the repeats, and the optimal solution is in
> general different from the true underlying sequence. **The maximum-likelihood
> formulation of the AP (Medvedev and Brudno, 2009), on the contrary, seems to
> be robust to these issues, and thus a good candidate for the ‘correct’
> formulation. Understanding whether bridging conditions can be used to
> guarantee that the maximum-likelihood sequence is the true sequence is
> currently an open question.**”

### 2.2 Three source facts about the phrase

1. It is used to contrast **formulations of the AP**: “parsimony-based
   formulations” versus “the maximum-likelihood formulation.” The word
   *formulation* names an objective/problem, not an algorithm.
2. It gives **no** subsection, equation, figure, or page pointer into
   Medvedev–Brudno.
3. A full-text scan of the accepted article finds exactly three occurrences of
   `likelihood` — the two in this paragraph plus the Medvedev–Brudno reference
   title — and zero occurrences of `multinomial` or `binomial`, no likelihood
   formula, and no candidate-length, flow, equivalence, or tie discussion.

### 2.3 The authors' own formulation/algorithm vocabulary

The same author group's earlier preprint (an earlier version, not the accepted
text) writes (Introduction, `nsgIlan.pdf` pp. 1–2):

> “To circumvent this issue, [8] proposed a maximum likelihood (ML)
> formulation for assembly. While such a formulation prevents the
> over-collapsing of repeats, devising algorithms to find the ML sequence
> given the read data is a daunting task, and existing approaches rely on the
> assumption of high coverage [8].”

Reference `[8]` is the same Medvedev–Brudno paper. This is direct evidence that
in this research line “the ML formulation” is the **objective**, explicitly
distinguished from “algorithms to find the ML sequence.”

## 3. Source facts: what Medvedev–Brudno designate

### 3.1 The abstract frames one ML framework, then an algorithm “in this setting”

> “Furthermore, we propose a maximum likelihood framework for assembling the
> genome that is the most likely source of the reads, in lieu of the standard
> maximum parsimony approach (which finds the shortest genome subject to some
> constraints). **In this setting**, we give a bidirected network flow-based
> algorithm that, by taking advantage of high coverage, accurately estimates the
> copy counts of repeats in a genome.”

### 3.2 §1.2 names the objective as the formulated problem

> “We formulate the problem of genome assembly as maximizing the likelihood of
> the observed read frequencies, rather than minimizing the length of the
> genome. This problem can be formulated as a minimum cost bidirected flow
> (biflow) problem with convex costs …”

### 3.3 §6.1 defines the objective, then an approximation, then §6.2 the algorithm

> “In this section, we describe our maximum likelihood framework for genome
> assembly, and give an algorithm that, given a set of reads (DNA molecules),
> finds the genome that maximizes the global read-count likelihood.”

Then the exact objective:

> “Let `D` be a circular genome of length `N(D)`, and let `d_i` denote the
> number of times the `k`-molecule `i` appears in `D`. … For a given `i`, the
> probability that the outcome of a single trial is `i` is simply `d_i/N(D)`.
> … When taken together, their joint distribution is exactly the multinomial
> distribution … we can consider the likelihood of the parameters of the
> distribution `(d_i)` given the outcome of the trials `(x_i)`, which we call
> the **global read-count likelihood**.”
>
> “In our approach, we attempt to assemble the genome with the maximum global
> read-count likelihood.”

Then the approximation, explicitly labelled:

> “Because the number of trials (sampled `k`-molecules) is typically large, we
> can **approximate** the multinomial distribution as the product of the
> individual binomial distributions of each `X_i`. Since in the binomial
> approximation the length of the genome `N(D)` is a constant that is
> independent of each `d_i`, we can replace it by `N`, which is the length of
> the actual genome from which the reads were sampled. … For our experiments,
> we assume that the genome size is known.”

Then §6.2, explicitly the algorithm:

> “We are now ready to describe our algorithm for predicting copy counts. The
> first step is to build a bidirected overlap graph from the set of reads …
> Each vertex has a lower bound of 1 … Since any flow can be decomposed into a
> collection of walks, our flow represents a **(non-contiguous) assembly** of
> the genome …”

### 3.4 §8.2 confirms the *algorithm* consumes a genome-length estimate

> “Our algorithm relies on having an estimate on the length of the genome, and
> we tested to what extent the accuracy is affected when the length is
> mis-estimated.”

Note the subject: the **algorithm**, not the objective. This is the strongest
single piece of Medvedev–Brudno-internal evidence for the fixed-`N` reading.

### 3.5 There are three distinct objects

| Object | Probability model | Normalizer | Role in MB09 |
|---|---|---|---|
| Exact global read-count likelihood (§6.1) | multinomial over `4^k` read types | candidate-intrinsic `N(D)=Σ_i d_i` | the named objective |
| Binomial/separable approximation (§6.1) | product of independent binomials | external constant `N` (true/estimated length) | explicitly an approximation, for tractable convex flow |
| §6.2 bidirected biflow | vertex-flow costs from the approximation | external `N` | explicitly the algorithm; output is a “(non-contiguous) assembly” |

## 4. Source analysis: which layer is the most faithful referent?

### 4.1 The phrase denotes an objective, so §6.2 is the weakest fit

Shomorony use *formulation* to contrast objectives, and their own earlier
preprint distinguishes “the ML formulation” from “algorithms to find the ML
sequence” (source facts §2.2–2.3). Medvedev–Brudno call §6.2 “our algorithm”
and describe its output as a non-contiguous assembly, not a sequence (source
fact §3.3). Therefore reading the citation as specifically designating the §6.2
flow feasible set requires treating an algorithm as a formulation and a flow as
“the maximum-likelihood sequence.” That is the least faithful of the three
concrete Medvedev–Brudno layers.

### 4.2 Of the two objectives, the exact §6.1 likelihood is the canonical one

Medvedev–Brudno name the exact multinomial “the global read-count likelihood,”
state the assembly goal as maximizing it, and introduce the binomial product with
the word “approximate” (source facts §3.3). Under the ordinary reading of “the
maximum-likelihood formulation,” an approximation to the likelihood is not the
formulation; it is a computational stand-in. The same authors again distinguish
the formulation from the algorithm that finds the solution (source fact §2.3).
Hence, if one concrete layer must be named, the **exact §6.1 global read-count
likelihood (Variant E)** is the most faithful.

Two further supporting observations:

- Shomorony's robustness claim (“robust to … over-collapsing”) is a property of
  the ML *principle* of counting repeat copy frequencies; it does not require the
  approximation. The exact objective embodies that principle directly.
- The sentence's subject is “the maximum-likelihood **sequence**,” a
  sequence-level object. Both §6.1 objectives are functions of a sequence's
  copy-count vector; the §6.2 flow output need not be any sequence.

### 4.3 Why the fixed-`N` rival is serious and cannot be dismissed

The strongest counter-argument: Medvedev–Brudno never optimize the exact
multinomial — they declare it non-separable and immediately approximate it — and
what they actually construct is a fixed-`N` approximation solved by §6.2. A
reader who identifies “the MB formulation” with the method MB actually propose
lands on the fixed-`N` layer. This is reinforced by:

- Medvedev–Brudno §8.2 making genome-size estimation a stated algorithmic
  requirement (source fact §3.4); and
- Howison, Zapata & Dunn (2013), §5, an independent contemporary source:

> “In fact, a maximum likelihood genome assembler was already proposed based on
> similar principles (Medvedev et al., 2009). … Also, it requires as a parameter
> the accurate size of the target genome, which is not available in all de novo
> assembly projects. A related design for maximum likelihood assembly (Varma et
> al., 2011) uses a different formulation that starts from an approximate size
> and estimates the actual size during the optimization.”

Howison's “Medvedev et al., 2009” resolves to the same Medvedev–Brudno paper.
This is a source fact about how a contemporary reader characterized the MB *ML
assembler*: by its external genome-size parameter. It supports treating the
fixed-`N` layer as part of what the MB method *is*, and it is the main reason the
issue #36 comment leans that way.

The counter to the counter: Howison describes the **assembler/algorithm**, not
the formulation, and “requires the accurate size of the target genome” is a
statement about the likelihood normalizer, not an assertion that competing
genomes must have length `N`. Medvedev–Brudno say “`N` … is the length of the
actual genome,” and §6.1's per-coordinate domain is `0 ≤ d_i ≤ N`; no constraint
`Σ_i d_i = N` appears (source fact §3.3, and cf.
`mb09-objective-semantics.md` §4). So the fixed-`N` strength is about the
method, which is exactly the level the word *formulation* does not name.

### 4.4 The broad-principle reading is literal but underdetermined

The phrase can be read as denoting the ML principle as opposed to parsimony,
with no commitment to exact-versus-approximate. This reading is literally safe
and is what `shomorony-mb-formulation-provenance.md` ranks first. It is
compatible with §4.2: the principle's canonical statement is the exact §6.1
objective. Its practical cost is that it does not by itself tell a formalization
which objective to state.

## 5. Reconciliation of the three prior conclusions

| Prior conclusion | Its actual claim | Reconciles as |
|---|---|---|
| `shomorony-open-question-referent.md` (branch `agent/shomorony-ml-semantics`): exact §6.1 multinomial is the most plausible referent | answers “which objective is the formulation” | Consistent with §4.2; this note restates it with the fixed-`N` rival weighed more explicitly |
| `shomorony-mb-formulation-provenance.md` (`main`) §6.5: exact §6.1 is *least* supported; broad principle first | answers “what did MB actually formulate-and-solve” | Not a contradiction: it ranks the **operative method**, where the approximation dominates. The disagreement is the question being asked, not the primary facts |
| Issue #36 comment (2026-09-20): fixed-`N`/flow reading weighs strongest; §6.2 feasibility still needed | answers “what method is likely the target of a settling theorem” | Consistent with §4.3; this note keeps that rival live and does not claim the fixed-length §6.1 witness alone settles the question |

All three prior notes agree on every primary-source fact: the three MB objects,
the absence of a pointer in the 2016 text, the external-`N` assumption in the
approximation and algorithm, and the unretrieved supplement. The disagreement is
over which level of “formulation” the citation names.

## 6. Explicit uncertainty register

1. **No pointer.** The 2016 sentence names no section/equation, so no referent
   is proved. The determination in §4 is source analysis.
2. **Exact vs fixed-`N`.** The exact §6.1 objective is the most faithful reading
   of “the formulation” as a likelihood; the fixed-`N` approximation is the most
   faithful reading of “the method MB actually propose and solve.” Both remain
   live. This is the principal residual ambiguity for issue #36.
3. **Candidate universe.** §6.1 states no competitor universe; §6.2 is a genuine
   restriction to read-graph flows. Whether a settling theorem must place its
   witnesses in the §6.2 feasible class therefore depends on (2), not on (1).
4. **Genome equivalence.** Cyclic shift is required by the 2016 circular model;
   whether reverse complement is quotiented is not resolved by the 2016 text.
5. **Conclusion and tie semantics.** “The maximum-likelihood sequence” does not
   distinguish truth-is-a-maximizer from all-maximizers-are-truth; neither paper
   supplies a tie rule.
6. **Supplement.** Publisher supplement sections A–G remain uninspected; the
   accepted text's cross-references point only to graph/reconstruction, not to a
   likelihood section.

## 7. Consequence for the counterexample program (source analysis)

- If the citation denotes the **exact §6.1 objective over circular candidates**
  (the most faithful reading of §4.2), the existence and candidate-universe
  assumptions of the fixed-length exact witness matter, and the unrestricted
  exact Variant E remains the cleanest target.
- If it denotes the **fixed-`N` approximation**, the fixed-length binomial
  witness is directly relevant, subject to the candidate-universe question.
- If it denotes the **§6.2 flow class**, the witnesses settle nothing unless
  placed in that class — the §6.2 feasibility work remains essential, exactly as
  `section62-bidirected-flow-feasibility.md` concludes.

So the source trace does **not** license the claim that the existing same-length
witnesses already settle the published question. This is consistent with the
issue #36 comment and with `shomorony-mb-formulation-provenance.md` §7.

## 8. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| Accepted 2016 text names MB only by bibliography; no formula/section/length/flow/tie | **Source fact** | `InfoOptimalAssy.pdf` §5 + full-text scan; `NSG.pdf` |
| “AP” is the paper's abbreviation for the Assembly Problem | **Source fact** | `InfoOptimalAssy.pdf` Introduction |
| Earlier preprint distinguishes “ML formulation” from “algorithms to find the ML sequence” | **Source fact** | `nsgIlan.pdf` §1 |
| MB09 propose an ML framework, then a flow algorithm “in this setting” | **Source fact** | MB09 abstract |
| MB09 §6.1 defines exact multinomial `d_i/N(D)`, `N(D)=Σd_i`; then labels the binomial product an approximation with external `N`; §6.2 is “our algorithm,” output a non-contiguous assembly | **Source fact** | MB09 §6.1–§6.2 |
| MB09 §8.2 says the algorithm relies on a genome-length estimate | **Source fact** | MB09 §8.2 |
| Howison et al. (2013) §5 describe the MB ML assembler as requiring accurate target-genome size | **Source fact** | `Howison2013.pdf` §5 |
| “Formulation” names an objective, so §6.2 is the least faithful referent | **Source analysis** | §4.1 |
| Exact §6.1 global read-count likelihood is the most faithful concrete layer | **Source analysis** | §4.2 |
| Fixed-`N` approximation is a serious rival via the “method MB actually propose” reading | **Source analysis** | §4.3 |
| No reading is proved; supplement uninspected; candidate universe unresolved | **Unresolved** | §6 |

## 9. Correction carried forward from prior work

The 2026-09-20 issue #36 comment cites the Shomorony et al. paper as
`DOI 10.1093/bioinformatics/btw267`. That DOI belongs to “Genome assembly from
synthetic long read clouds,” *Bioinformatics* 32(17), i216–i224. The paper under
discussion here is `10.1093/bioinformatics/btw450` (*Bioinformatics* 32(17),
i494–i502), as printed in its own reference list. The `btw267` DOI is a
transcription error and should not be propagated.

## References

1. I. Shomorony, S. H. Kim, T. A. Courtade, D. N. C. Tse. “Information-optimal
   genome assembly via sparse read-overlap graphs.” *Bioinformatics* 32(17),
   2016, i494–i502. DOI <https://doi.org/10.1093/bioinformatics/btw450>.
2. P. Medvedev, M. Brudno. “Maximum Likelihood Genome Assembly.” *Journal of
   Computational Biology* 16(8), 2009, 1101–1116. DOI
   <https://doi.org/10.1089/cmb.2009.0047>. Full text
   <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/>.
3. M. Howison, F. Zapata, C. W. Dunn. “Toward a statistically explicit
   understanding of de novo sequence assembly.” *Bioinformatics* 29(23), 2013,
   2959–2963. DOI <https://doi.org/10.1093/bioinformatics/btt525>.
4. G. Bresler, M. Bresler, D. Tse. “Optimal assembly for high throughput
   shotgun sequencing.” *BMC Bioinformatics* 14(Suppl 5):S18, 2013. DOI
   <https://doi.org/10.1186/1471-2105-14-S5-S18>.
