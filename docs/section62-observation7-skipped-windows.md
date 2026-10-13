# Observation 7: exact skipped-window criterion

**Status (2026-10-13):** proved here as an elementary combinatorial argument for an *oriented, error-free, fixed-read-length, circular-spelling model*. A separate exhaustive finite regression checks all 3,456 valid edges arising from all nonempty subsets of binary length-3 words. **Not yet a Lean-kernel theorem.** A strand/reverse-complement adapter, general circular-walk certificate, and exact source-algorithm equivalence remain open (Antonina #284, #261, #285).

## What the original papers actually say

Medvedev–Brudno (2009), [Maximum Likelihood Genome Assembly, §6.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC3154397/), describes reducing a bidirected read-overlap graph by removing overlaps spelled by two “shorter overlaps.” It then states Observation 7 for *a read and a walk* in the transitively reduced graph: the number of visits to that read equals its occurrences in the molecule spelled by the walk. **The wording quantifies over walks generally**, not only over flows satisfying lower bounds at every observed vertex.

Myers (2005), [The fragment assembly string graph](https://www.cs.utoronto.ca/~brudno/csc2427/myers.pdf), measures an edge by its *appended string label*; for equal-length reads, its length is L minus the shared-nucleotide overlap. Hence *shorter extension labels* imply **longer shared-nucleotide overlaps**. The direct wording of the two papers is not literally equivalent when “overlap length” is interpreted as shared nucleotides. The algebra below isolates a sound spelling-preserving predicate, without claiming equivalence of all algorithm details.

Shomorony et al. (2016), [Information-optimal genome assembly via sparse read-overlap graphs](https://academic.oup.com/bioinformatics/article/32/17/i494/2450780), discusses the ML formulation as an open direction rather than specifying one unique probability objective/candidate universe. This note is not a resolution of that underdetermined sentence.

## The setting and the exact counting identity

Let **L ≥ 2** be the common read length; each read is a word of length L. Take an oriented circular walk

    u₀ —ell₀→ u₁ —ell₁→ … —ell_(m−1)→ u₀,

where every edge is a genuine suffix-prefix overlap of length 0 ≤ ell_j < L, and ell_j is at least the graph threshold oMin. There are m ≥ 1 edges; every extension length d_j = L − ell_j is **strictly positive**.

Assume the overlap spellings are coherent through the circular seam and define a circular word D of length

$$
G = \sum_{j=0}^{m-1} d_j.
$$

Put s₀=0 and s_j = sum_{a<j} d_a, so 0=s₀<s₁<⋯<s_(m−1)<G. Assume the oriented read visited at position j is precisely the circular length-L window of D starting at s_j. These are the spelling hypotheses; they should be formalized separately rather than inferred from a bare list of graph vertices.

For any length-L read word c, let V(c) count visited vertices equal to c and C_D(c) count **all G length-L cyclic genomic windows** equal to c.

Every genomic start i in the integer interval [0,G) lies uniquely in exactly one half-open interval [s_j, s_j+d_j). The first start of that interval contributes the visited read u_j; the remaining d_j−1 starts are internal positions that the overlap step skips. Consequently,

$$
\boxed{C_D(c)=V(c)+
  \sum_{j=0}^{m-1}\sum_{t=1}^{d_j-1}
  \mathbf 1\!\left[D[s_j+t:s_j+t+L]_{\rm circular}=c\right].}
  \tag{1}
$$

All terms in the second summand are nonnegative integers. Hence, for any selected observed read-word set S,

$$
\boxed{
  \bigl(\forall c\in S,\ C_D(c)=V(c)\bigr)
  \iff
  \text{no internal skipped length-L window belongs to S}.
}
  \tag{2}
$$

This **iff criterion** is the exact occurrence-count content needed for Observation 7. It does *not* require every overlap to have length L−1. If S is the complete set of length-L windows of D, (2) instead forces every d_j=1 by counting total starts; that stronger completeness assumption is usually absent from a graph of observed reads.

## Spelling-preserving reduction eliminates observed skipped windows

Take a direct edge u→v with proper nucleotide overlap ell, so its direct spelling is u followed by the last d=L−ell letters of v. Suppose a length-L window m is entirely inside that spelled word, starting at internal offset 0<t<d, **and m is an observed graph read strand**. Then define

$$
\ell_1=L-t,\qquad \ell_2=\ell+t.
$$

Both lie strictly between ell and L; because ell≥oMin, both are at least oMin. Elementary substring identities give genuine overlaps u→m of length ell₁ and m→v of length ell₂, with

$$
\ell_1+\ell_2=L+\ell.
$$

Thus the two-leg path spells *exactly the same word* as the direct overlap. In the project's implemented **isReducibleSpellingB** predicate (AssemblyP1/Section62SpellingReductionCandidate.lean), this is an explicit witness of reducibility. Therefore:

**No surviving edge in transitivelyReducedSpelling can skip an observed oriented read strand.**

Combining this per-edge result with (1) proves the oriented circular-walk version of Observation 7 for the *spelling-preserving candidate reduction*. If reads are represented by reverse-complement molecule classes, first transfer an internal observed molecule to the correct strand in strandsOf and then sum visit counts by representative. The **RC/sign orientation adapter and the general Lean theorem remain to be written**. Do not transfer the result to the full original Myers implementation without checking contained reads, parallel overlaps, reverse complement, minimum-overlap policies and other details.

## Why the literal shorter-nucleotide-overlap reading fails

If a proper direct nucleotide overlap has length ell < L, while two detour nucleotide overlaps ell₁,ell₂ are each **strictly shorter** than ell, then

$$
\ell_1+\ell_2 < 2\ell < L+\ell.
$$

They cannot satisfy the spelling composition equation ell₁+ell₂=L+ell. Thus this literal reading makes spelling-preserving two-hop reduction vacuous for equal-length proper reads. The following explicit circular walk then violates the unrestricted Observation 7 claim.

Let L=3 and observed oriented graph read vertices S={AAA,AAT,ATA,TAA}. Take the four-edge circuit

    AAA -(2)-> AAA -(2)-> AAT -(1)-> TAA -(2)-> AAA.

Its extension lengths are (1,1,2,1), and its spelled circular word is **AAAAT** (a cyclic rotation of AAATA). Its five length-3 circular windows are **AAA, AAA, AAT, ATA, TAA**, but the walk visits **AAA, AAA, AAT, TAA** only. Hence V(ATA)=0 while C_D(ATA)=1. Every edge survives the *literal* shorter-nucleotide-overlap reduction; with the spelling-preserving predicate, **AAT→TAA** is instead removed by the two-leg detour via the observed read **ATA**, both leg overlaps length 2.

**Scope restriction:** This particular walk violates a *separate* optimization lower-bound constraint requiring every observed read vertex to be visited at least once. That does **not** rescue an Observation 7 assertion expressly quantified over every walk, but this example must not be described as a feasible optimum violating the stronger constrained-flow proposition. The two models must be kept separate.

Also distinguish this four-vertex walk from the genuine same-length AAATA candidate in the project's #179/#182 result: that candidate's *actual observed read set* omits ATA, so the skip does **not** contradict (2) on its observed vertices. This is precisely why a read-overlap circuit may spell a genome while omitting some *unobserved* read-type counts from its flow-vector support.

## Reproducible finite regression

Run:

    python3 scripts/verify_observation7_skipped_windows.py

The script enumerates all nonempty subsets of the 8 oriented binary length-3 read strings, all their genuine proper overlap edges (with oMin=1), and every possible intermediate observed read strand. It verifies for **all 3,456 such edge instances** that (i) literal shorter-overlap reduction is vacuous and (ii) an edge is spelling-preservingly reducible **iff** its direct spelling contains an observed internal length-3 window. It also checks every edge of the four-read circular witness, its spelled cyclic word, the full genomic window counts, and the exact partition into visited and skipped starts.

This is **finite computational evidence**, not a Lean proof of the general statement; the algebra above supplies the general oriented proof sketch.

## Small Lean obligations, without duplicating existing work

1. **Internal factorization.** For fixed u,v,L,ell,t and a verified proper overlap, show that the internal window of spellDirect beginning at t yields the suffix/prefix identities and ell₁=L−t, ell₂=ell+t. Derive isReducibleSpellingB by inserting this intermediate strand and explicit lengths. Existing spellPath_eq_spellDirect and overlapEdges_mem_iff can help.
2. **Surviving-edge exclusion.** If e∈transitivelyReducedSpelling, no internal offset window can be in strandsOf rc verts. This theorem is local and should not depend on probability, flow, or circularity.
3. **Circular interval partition.** Under a coherent oriented closed SignedPath spelling, prove the exact Finset/count identity (1) and then the iff (2). Handle positive extensions, the circular seam, and repeated read words explicitly.
4. **Bidirected class lift.** Adapt the oriented theorem to signs, representatives, and reverse complements, checking exactly which strand windows correspond to a molecule occurrence. Keep the literal-MB09 counterexample and Myers predicate source comparison as a distinct audit.

These results would complete a positive **candidate-model** proof of Observation 7, not by themselves a proof that MB09's source graph is identical to that model or that flow costs equal full genome ML outside the graph's observed read panel.
