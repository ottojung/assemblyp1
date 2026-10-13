---
theme: default
title: "AssemblyP1 for Programmers"
info: |
  How short reads become a graph, how Not-So-Greedy reconstructs a
  genome, and what we proved about maximum likelihood with Lean.
class: text-center
highlighter: shiki
lineNumbers: false
drawings:
  persist: false
transition: slide-left
routerMode: hash
mdc: true
---

# Assembling a genome is a graph problem

### From short DNA reads to reconstruction, likelihood, and machine-checked theorems

<div class="pt-10 text-lg opacity-80">
A concrete algorithmic story · AssemblyP1
</div>

<HomeLink label="Choose another audience" />

<!--
The core question is how a collection of short strings can determine one circular string.
We will build and traverse a tiny graph, then see how repeat information and likelihood change the question.
-->

---

# One circular genome, many short reads

Imagine a **circular** DNA word, with read length \(L=3\).

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**Hidden source**

\[
S=\texttt{ACGTA}
\]

Start at each position, take three letters, wrap around at the end.

</div>
<div>

| Start | Observed read |
|---:|:---|
| 0 | `ACG` |
| 1 | `CGT` |
| 2 | `GTA` |
| 3 | `TAA` |
| 4 | `AAC` |

</div>
</div>

<div class="pt-6 text-lg">
The assembler sees the **reads**, not the source or their start positions.
</div>

---

# An operational assembly algorithm

One useful construction is the **de Bruijn graph**.

For read length \(L\), turn every read into an edge:

- vertex = its \((L-1)\)-letter prefix or suffix;
- edge = one observed length-\(L\) read, from prefix to suffix;
- retain multiplicities when the same read occurs more than once.

<div class="pt-6">

\[
\texttt{ACG}: \quad \texttt{AC} \longrightarrow \texttt{CG}
\]

\[
\texttt{CGT}: \quad \texttt{CG} \longrightarrow \texttt{GT}
\]

</div>

<div class="pt-6 opacity-75 text-sm">
This is a teaching example of spectrum-based reconstruction. Not-So-Greedy, introduced shortly, constructs a different graph: a read-overlap graph.
</div>

---

# Traverse the graph; spell the genome

With all five circular windows, the graph is one directed cycle.

```text
 AC --ACG--> CG --CGT--> GT
 ^                       |
 |                       GTA
 AAC                     |
 |                       v
 AA <--TAA-- TA <--------+
```

Start with `AC`, append the last character of each edge:

```text
AC → ACG → ACGT → ACGTA → ACGTAA → ACGTAAC
```

The two extra letters close the circle: **`ACGTA`**, up to rotation.

<div class="pt-4 text-lg">
Assembly becomes an **Eulerian traversal**: use every edge with its required multiplicity.
</div>

<!--
The graph's edges, not vertices, represent windows. The final two letters repeat
the first two because the source is circular.
-->

---

# Repeats create genuine ambiguity

Two distinct circular genomes can have exactly the same short-read spectrum.

<div class="grid grid-cols-2 gap-6 pt-5">
<div>

**Genome S**

```text
AAABAB
```

</div>
<div>

**Genome D**

```text
AABAAB
```

</div>
</div>

Both have the identical circular 2-mer counts:

| Read | `AA` | `AB` | `BA` |
|:---|---:|---:|---:|
| Count | 2 | 2 | 2 |

<div class="pt-6 text-lg">
Same edges, same multiplicities, different cyclic spellings. More computation cannot recover information absent from the reads.
</div>

---

# The missing information: bridging a repeat

A read **bridges** a repeat copy when it extends beyond **both** ends of that copy.

```text
genome     ...G [ A C G A ] T ...
read          G [ A C G A ] T
              ^             ^
          left context   right context
```

The flanking bases attach this copy to its context.

<div class="pt-6 grid grid-cols-2 gap-8">
<div>

**Triple repeats**

Three copies of one sequence can create alternative routes. Bridging *every copy* supplies the required context.

</div>
<div>

**Interleaved repeat pairs**

Alternating occurrences can also allow two different circular arrangements. Their bridging condition rules out the ambiguity.

</div>
</div>

<div class="pt-4 text-lg">
This is the information-theoretic heart of the 2016 reconstruction theorem.
</div>

---

# A second graph: reads as vertices

The 2016 **Not-So-Greedy** algorithm uses a **read-overlap graph**, not the de Bruijn graph from our toy example.

<div class="grid grid-cols-2 gap-8 pt-6">
<div>

**De Bruijn**

- vertices: \((L-1)\)-mers
- edges: \(L\)-mers
- reconstruct by traversing window edges

</div>
<div>

**Read-overlap**

- vertices: entire observed reads
- edges: compatible suffix-to-prefix overlaps
- edge weights: overlap lengths
- reconstruct by spelling an overlap walk

</div>
</div>

```text
read A: ACGTT
            |||
read B:     TTACG
```

<div class="pt-4 opacity-80">
The second representation makes the original algorithm's operations understandable.
</div>

---

# Why ordinary greedy assembly is not enough

A greedy graph keeps only each read's **longest suffix-prefix extension**.

<div class="pt-5 text-lg">
But a read can lie in a repeated region and need to be visited more than once.
</div>

**Not-So-Greedy keeps more useful structure:**

1. Keep the longest-overlap successor.
2. Also keep the first alternative whose extension **disagrees** with the greedy extension.
3. Perform the symmetric construction for predecessors, then intersect the edge sets.

<div class="pt-5 text-lg">
Every read now has at most **two incoming and two outgoing edges**.
</div>

<!--
Second edge means the first conflicting extension in decreasing overlap order;
it does not simply mean the second-longest overlap.
-->

---

# From a sparse graph to an Eulerian reconstruction

<div class="grid grid-cols-3 gap-6 pt-7">
<div>

### Construct

Keep the greedy and first genuinely different extensions.

Result: bounded degree.

</div>
<div>

### Prune

Use **effective overlaps** to remove spurious links or transform equal-overlap hourglass structures.

Result: a graph carrying a compatible genome walk.

</div>
<div>

### Solve

Choose edge multiplicities to turn the required walk into an Eulerian cycle.

Traverse it and spell the circular genome.

</div>
</div>

<div class="pt-9 text-lg">
The surprising move: exchange a difficult general read-ordering problem for an efficiently solvable **Eulerian** one.
</div>

<!--
This is the conceptual overview of the two phases and supplementary
multiplicity modification in Shomorony et al. 2016, Section 3 and supplement F.
-->

---

# Not-So-Greedy: the guarantee

Under the 2016 paper's information-feasibility conditions:

- the reads **cover** the true circular genome;
- **every copy** of every triple repeat is bridged;
- **every interleaved repeat pair** is bridged;

<div class="pt-8 text-2xl text-center">
The constructed multigraph has a **unique Eulerian cycle**, whose spelling is the true genome **up to circular rotation**.
</div>

<div class="pt-8 text-lg">
Construction and reconstruction take \(O(NL)\) time for \(N\) reads of length \(L\).
</div>

<div class="pt-3 text-sm opacity-65">
Shomorony, Kim, Courtade & Tse, <i>Bioinformatics</i> (2016), Theorem 1 and Corollary 1.
</div>

---

# A new question: reconstruction versus likelihood

The theorem answers:

> Can the reads determine the genome, and can an algorithm reconstruct it?

AssemblyP1 investigates a different question:

> Does the **true** genome give the **highest probability** to the particular reads we observed?

<div class="pt-7 text-center text-2xl">
\[
\widehat D_{\rm ML}
  = \underset{D}{\operatorname{arg\,max}}\;
    \Pr(R\mid D)
\]
</div>

<div class="pt-5 text-lg">
Structural reconstruction uses **which overlaps fit**; likelihood also rewards **how frequently each read appears**.
</div>

---

# Read multiplicities change likelihood

For a candidate circular genome \(D\), uniformly sampled error-free reads have type probabilities

\[
p_D(w)=\frac{\#\{\text{starts of word }w\text{ in }D\}}{|D|}.
\]

If the observed count of read \(w\) is \(x(w)\), its candidate-dependent likelihood factor is

\[
\mathcal L(D;x)\ \propto\ \prod_w p_D(w)^{x(w)}.
\]

<div class="pt-7 text-lg">
A candidate gets a higher score if it places more probability on read types that happened to be **over-represented in the sample**.
</div>

---

# Result I: an exact finite likelihood reversal

For oriented reads with \(L=3\), one verified example compares:

<div class="grid grid-cols-2 gap-10 pt-6">
<div>

**True genome**

\[
S=\texttt{AAATT}\quad(|S|=5)
\]

</div>
<div>

**Competitor**

\[
D=\texttt{AAAATT}\quad(|D|=6)
\]

</div>
</div>

<div class="pt-6 text-center text-3xl">
\[
\frac{\mathcal L(D;x)}{\mathcal L(S;x)}
=\frac{15625}{11664}>1
\]
</div>

<div class="pt-5 text-lg">
The six observed reads are <code>AAA, AAA, AAT, ATT, TTA, TAA</code>. The competitor has two starts producing <code>AAA</code> instead of one, so the twice-observed read gets extra probability and wins this likelihood contest.
</div>

<div class="pt-4 text-sm opacity-70">
Exact rational certificate in Lean; a mathematical finding about finite samples, not a reconstruction-algorithm failure.
</div>

---

# Result II: bridging imposes spectrum rigidity

A genome's **complete \(L\)-mer spectrum** assigns a multiplicity to each read type.

In the de Bruijn support graph, a valid circular spelling gives a balanced integer flow:

\[
\forall v:\quad \mathrm{in}(v)=\mathrm{out}(v).
\]

<div class="pt-5 text-lg">
Our rigidity theorem shows that, under the stated bridging hypotheses, the true spectrum is the **unique positive balanced integer flow** of total length \(|S|\) on its complete window-support graph.
</div>

<div class="pt-5">
**Consequence:** for oriented **same-length** spelled candidates using that full window support, no strictly better likelihood competitor exists; with the complete-spectrum uniqueness step, the spelling is the truth up to rotation.
</div>

<div class="pt-3 text-sm opacity-65">
This is an AssemblyP1 theorem about the complete-spectrum graph, distinct from the 2016 algorithm's observed-read graph.
</div>

---

# Result III: population likelihood has a simple optimum

Now imagine the exact read distribution is known, instead of a noisy finite sample.

Expected log-likelihood becomes

\[
\ell_S(D)=\sum_w p_S(w)\log p_D(w).
\]

The key identity:

\[
\ell_S(D)-\ell_S(S)
=-D_{\mathrm{KL}}(p_S\,\|\,p_D)\leq 0.
\]

<div class="pt-6 text-xl">
The truth is **always** a population maximum-likelihood genome, for any candidate class that contains it.
</div>

<div class="pt-4 opacity-75">
Equality means identical read distributions. Whether the genome itself is identifiable is a separate combinatorial question.
</div>

---

# Result IV: when is that optimum unique?

Suppose the true genome and admissible competitors are:

- **primitive** — not repetitions of a shorter circular word;
- **P2 / Ukkonen-admissible** — excluding the problematic triple and interleaved repeat structures at the chosen read length.

<div class="pt-7 text-2xl text-center">
If a candidate has the same population read distribution, it must be a **rotation of the truth**.
</div>

<div class="pt-6 text-lg">
Thus the **population maximum-likelihood genome is unique up to circular rotation** within the oriented primitive P2 class.
</div>

<div class="pt-3 text-sm opacity-70">
The complete-spectrum uniqueness argument is the deep combinatorial ingredient; the KL inequality supplies optimality.
</div>

---

# How we checked the mathematics

<div class="grid grid-cols-2 gap-8 pt-5">
<div>

### Formal statement

Model circular strings, read spectra, graph flows, and repeat predicates explicitly.

### Proof

Reduce broad claims to smaller lemmas and construct Lean proof terms.

</div>
<div>

### Mechanical verification

Lean's type checker verifies the theorem against its exact hypotheses.

```lean
theorem and_comm
    (p q : Prop) :
    p ∧ q → q ∧ p :=
  fun h => ⟨h.2, h.1⟩
```

</div>
</div>

<div class="pt-7 text-lg">
The interesting achievement is not just finding a plausible theorem — it is producing one that can be **re-checked mechanically**.
</div>

---

# How the research was organized

```text
Research questions
       |
       v
Independent agents: literature, examples, graph lemmas
       |
       v
Formal definitions + Lean proofs + exact computations
       |
       v
Independent review → CI → integrated repository
```

<div class="pt-6 text-lg">
Agents explore mathematical alternatives in parallel; the final, persistent artifact is a set of exact propositions, proofs, tests, and a paper.
</div>

<!--
This is a concise architecture slide, not a postmortem.
-->

---

# One problem, four kinds of progress

<div class="grid grid-cols-2 gap-8 pt-5">
<div>

**Algorithm**

A sparse overlap graph and Eulerian traversal reconstruct a genome when bridging information suffices.

**Combinatorics**

Bridging imposes strong constraints on feasible complete-read spectra.

</div>
<div>

**Statistics**

Finite read counts can change a maximum-likelihood ranking.

**Formal methods**

Population uniqueness and the finite examples are supported by kernel-checked Lean development.

</div>
</div>

<div class="pt-6 text-lg">
The same reads can be studied as **paths, integer flows, probability distributions, and formal theorems**.
</div>

---

layout: end
---

# Reads → graphs → theorems

<div class="pt-6 text-xl">
Overlaps make reconstruction possible.
<br>
Bridging resolves repeats.
<br>
Likelihood exposes a second, statistical dimension.
<br>
Lean makes the mathematical claims checkable.
</div>

<div class="pt-9 text-sm opacity-70">
<a href="https://github.com/ottojung/assemblyp1">github.com/ottojung/assemblyp1</a>
· Shomorony et al., <i>Information-optimal genome assembly via sparse read-overlap graphs</i> (2016)
</div>

<HomeLink label="Choose another audience" />
