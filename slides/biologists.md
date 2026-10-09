---
theme: default
title: "AssemblyP1 for Biologists"
info: |
  What short-read sequencing can and cannot reveal, and where a
  reconstruction procedure and a likelihood score can disagree.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# Reading a genome from its fragments

### What sequencing can reveal, and where likelihood can disagree

<div class="pt-8 opacity-70">
AssemblyP1 · for biologists, genomicists, and bioinformaticians
</div>

<HomeLink label="Choose another audience" />

---
layout: default
---

# Sequencing reads the genome in pieces

A circular genome is copied and read as many short, overlapping fragments.

```
source:  A C G T T A C G A T
reads:   ACGTT   TTACG   CGATA
```

<div class="pt-6 text-lg">
The <b>assembly problem</b>: infer the circular source genome from the fragments alone.
</div>

<div class="pt-4 text-sm opacity-70">
This is the computational core of every genome project — from bacterial genomes to the Human Genome Project.
</div>

---
layout: default
---

# Overlaps are the basic signal

Without repeats, shared sequence links fragments into a consistent source.

```
ACGTT
   GTTAC
      TACGA
```

<div class="pt-6 text-lg">
<b>Overlap evidence</b> says: these pieces came from the same place.
</div>

<div class="pt-4 text-sm opacity-70">
Overlap-layout-consensus (OLC) assemblers — Celera Assembler, Canu — build on exactly this principle.
</div>

---
layout: default
---

# Repeats create genuine ambiguity

<div class="text-xl pt-6 font-mono">

`...A `**`CGCG`**` T...`
`...G `**`CGCG`**` C...`

</div>

A read lying entirely inside a repeated block cannot tell which copy it came from.

<div class="pt-8 text-amber-600 text-lg">
This is ambiguity in the data itself — not a shortcoming of a particular assembler.
</div>

<div class="pt-4 text-sm opacity-70">
Real genomes are full of repeats: transposons, segmental duplications, ribosomal RNA arrays. A human genome is ~50% repetitive.
</div>

---
layout: default
---

# Bridging reads resolve repeats

```
genome:   —————————[ repeat copy ]—————————
read:        ————————————————>
```

A single read that extends beyond **both** ends of a repeat carries the context needed to place it.

<div class="pt-6 text-lg">
<b>Bridging conditions</b> were introduced precisely to rule out the repeat configurations that make assembly ill-posed.
</div>

<div class="pt-4 text-sm opacity-70">
Shomorony, Kim, Courtade & Tse (2016) formalized when bridging is sufficient — and left a key question open.
</div>

---
layout: default
---

# The question that started this project

<div class="text-2xl text-center pt-10">

if the reads contain enough structural information to reconstruct the genome,

<div class="text-4xl py-4">⇓ ?</div>

does maximum likelihood recover the true genome?

</div>

<div class="pt-8 text-base opacity-80">
Shomorony, Kim, Courtade & Tse (2016) left this implication open.
</div>

---
layout: default
---

# Reconstruction and likelihood are different questions

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Reconstruction**

Can a candidate genome explain every observed read?

</div>
<div>

**Maximum likelihood**

Which candidate gives the observed read counts the highest probability?

</div>
</div>

<div class="pt-8 text-amber-600">
A genome can be structurally consistent with the reads yet not be the most likely explanation of their frequencies.
</div>

<div class="pt-4 text-sm opacity-70">
This distinction — structure vs. frequency — is the central insight of the AssemblyP1 project.
</div>

---
layout: default
---

# Structure and frequency are separable effects

- **Structural ambiguity** — repeats make several genomes fit the same reads.
- **Frequency effects** — even with no ambiguity, finite samples can favor the wrong genome.

<div class="pt-6 text-lg">
These are different mechanisms and need different arguments.
</div>

<div class="pt-4 text-sm opacity-70">
A useful analogy: structural ambiguity is like having two maps that both fit the landmarks; frequency effects are like one map being more likely given how often you visited each landmark.
</div>

---
layout: default
---

# A surprising finite example

Oriented reads of length `L = 3`, comparing:

- truth `S = AAATT` (length 5)
- decoy `D = AAAATT` (length 6)

<div class="grid grid-cols-2 gap-8 pt-4">
<div>

**Candidate-intrinsic likelihood** (n = 6 reads)

$$
\frac{\mathcal{L}(D)}{\mathcal{L}(S)} = \frac{15625}{11664} > 1
$$

the decoy scores higher

</div>
<div>

**Full-start sample** (n = 5 reads)

$$
\frac{\mathcal{L}(D)}{\mathcal{L}(S)} = \frac{3125}{3888} < 1
$$

the truth scores higher

</div>
</div>

<div class="pt-6 opacity-80">
The winner depends on how we model the sampling — a caution for any finite-read claim.
</div>

---
layout: default
---

# Why the reversal happens

<div class="pt-4 text-lg">
The decoy `AAAATT` has an extra `A`, so it produces the read `AAA` from <b>two</b> start positions.
</div>

<div class="pt-4">
When the sample happens to contain extra `AAA` reads, the decoy's higher `AAA` probability is rewarded.
</div>

<div class="pt-6 text-amber-600">
This is a <b>frequency-skew</b> effect: the same structural comparison gives different answers at different sample sizes.
</div>

<div class="pt-4 text-sm opacity-70">
The exact ratio 15625/11664 is kernel-checked in Lean (AssemblyP1.OrientedVariableLengthSe62).
</div>

---
layout: default
---

# A positive result: structural rigidity

Model the reads as a **support graph**:

- **vertices** = the length-`(L-1)` prefixes and suffixes,
- **edges** = the distinct length-`L` reads.

<div class="pt-6 text-lg text-emerald-600">
Repeat structure imposes genuine combinatorial rigidity — a positive, not merely negative, result.
</div>

<div class="pt-4 text-sm opacity-70">
Under the bridging conditions, the graph's possible read spectra are tightly constrained. Not every distribution of read counts is achievable.
</div>

---
layout: default
---

# The support graph in detail

<div class="pt-4">
For `L = 3`, each read `XYZ` is an **edge** from vertex `XY` to vertex `YZ`.
</div>

```
        AAA
       ↙   ↘
     AA ———— AT
     ↓  ↘   ↓
     AT ———— TT
       ↘   ↙
        TTA
```

<div class="pt-4 text-sm">
Each vertex's in-degree equals its out-degree in any valid assembly — a <b>balanced circulation</b>.
</div>

<div class="pt-4 text-sm opacity-70">
This is the de Bruijn graph construction, fundamental to modern assemblers (SPAdes, ABySS, MEGAHIT).
</div>

---
layout: default
---

# What rigidity gives us

<div class="pt-4 text-lg">
The support graph's structure constrains which read-count spectra are achievable by <b>any</b> candidate genome.
</div>

<div class="pt-4">
This is a <b>positive</b> combinatorial result: the repeat structure of the truth limits the possible explanations.
</div>

<div class="pt-6 text-sm opacity-70">
Formally: under the bridging hypothesis, the set of feasible spectra is a strict subset of all non-negative integer vectors on the support.
</div>

---
layout: default
---

# Idealized population model

Replace one finite draw by the exact distribution of reads.

<div class="pt-4">
Then the expected log-likelihood is maximized exactly when the candidate predicts the same normalized read spectrum as the truth (a Gibbs / KL statement).
</div>

<div class="pt-6 text-amber-600 text-lg">
The statistical noise disappears; what remains is a clean identifiability question.
</div>

<div class="pt-4 text-sm opacity-70">
This is the "population" limit: infinitely many reads, so frequencies are exact.
</div>

---
layout: default
---

# Population uniqueness

For oriented circular genomes that are

- **primitive** (not a whole-genome repetition), and
- **P2 / Ukkonen-admissible** at the read length,

the population maximum-likelihood genome is unique up to circular rotation.

<div class="pt-6 text-base">
"Primitive" means the genome is not a repeated block. "P2" is a candidate-checkable repeat condition at the read length. Rotation is the same circular genome read from a different origin.
</div>

<div class="pt-4 text-base">
This result is verified by a machine-checked proof (Lean), not only by computation.
</div>

---
layout: default
---

# What P2 means biologically

<div class="pt-4 text-lg">
<b>P2</b> (Ukkonen-admissible) rules out two pathological repeat configurations:
</div>

<div class="pt-4">
1. <b>Triple repeats</b> — a sequence appearing three or more times, which creates irreducible ambiguity.
</div>

<div class="pt-4">
2. <b>Interleaved repeats</b> — two repeats that alternate, preventing clean separation.
</div>

<div class="pt-6 text-sm opacity-70">
These are the same repeat structures that cause real assemblers to produce fragmented or misassembled contigs.
</div>

---
layout: default
---

# What is proved, and how strongly

| Claim | Status |
| --- | --- |
| Structural rigidity of the support graph | proved |
| Explicit finite likelihood reversals | proved / computed exactly |
| Population ML uniqueness up to rotation | machine-checked proof |
| Same-length finite uniqueness | machine-checked, conditional |

<div class="pt-6 text-sm opacity-80">
Machine-checked means a computer verified every logical step from the stated assumptions; it does not by itself settle how the historical paper intended those assumptions.
</div>

---
layout: default
---

# Honest limitations

- The genome is **circular**, reads are **error-free**, and every read has the **same length**.
- Start positions are **uniformly random**; real libraries are not so clean.
- The finite counterexamples are about idealized models, **not** evidence that real assemblies fail.
- Results are about **identifiability in principle**, not about any specific assembler's output.

<div class="pt-6 text-lg">
The theorems are exact statements about a deliberately simple model.
</div>

---
layout: default
---

# What this means for practice

- Repeats set a hard **structural** limit on what reads can reveal.
- Likelihood adds a **frequency** dimension that can disagree with structure.
- Bridging conditions help with structure, but do not by themselves remove sampling effects.
- Population-level reasoning isolates the part of the problem that is genuinely combinatorial.

<div class="pt-6 text-sm opacity-70">
For working genomics: long reads (PacBio, Oxford Nanopore) and linked reads (10x) directly attack the repeat problem by providing more bridging information.
</div>

---
layout: default
---

# Take-aways

<div class="text-lg">

1. Assembly is reconstruction from fragments; repeats create real ambiguity.
2. Maximum likelihood is a distinct, frequency-based test.
3. Finite samples can reverse the comparison; idealized population models remove that accident.
4. Under explicit structural conditions, the population-likelihood genome is unique up to rotation.
5. These are exact, machine-checked results about a simple model — with clear limits.

</div>

---
layout: end
---

# Thank you

<div class="pt-6 opacity-80">
Two audience-specific decks share one GitHub Pages site.
</div>

<HomeLink label="Choose another audience" />

---
layout: default
---

# Backup: the model in full

- Circular genome over `A/C/G/T`.
- Reads of fixed length `L`, uniformly random start positions.
- Error-free reads, as in the 2016 information-theoretic model.
- Two genomes that differ only by circular rotation are the same oriented genome.

<div class="pt-6 text-sm opacity-70">
The model follows Medvedev & Brudno (2009) and Shomorony et al. (2016).
</div>

---
layout: default
---

# Backup: primary sources

<div class="text-sm">

**Medvedev & Brudno (2009).** "Maximum Likelihood Genome Assembly." *Journal of Computational Biology* 16(8), 1101–1116.

**Bresler, Bresler & Tse (2013).** "Optimal assembly for high throughput shotgun sequencing." *BMC Bioinformatics* 14(Suppl 5):S18.

**Shomorony, Kim, Courtade & Tse (2016).** "Information-optimal genome assembly via sparse read-overlap graphs." *Bioinformatics* 32(17), i494–i502.

**Ukkonen (1992).** "Approximate string-matching with q-grams and maximal matches." *Theoretical Computer Science* 92(1), 191–211.

</div>

<div class="pt-6 text-sm opacity-70">
Full formalization: <a href="https://github.com/ottojung/assemblyp1">github.com/ottojung/assemblyp1</a>
</div>
