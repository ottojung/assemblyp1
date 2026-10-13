# Spelled same-length challenger for the MB09 binomial approximation

**Status:** independent exact arithmetic AND Lean-kernel certificates for the full candidate score, exact iid tie, surviving circuit edges and signed seams. Antonina #259/#261/#284. This is a source-model research note, not a declaration that the 2016 open sentence is settled.

## Setup

Use the two-symbol DNA alphabet with complement A↔T and reverse-complement-collapsed length-3 read molecule classes, as in AssemblyP1/Section62NonSpelledFlow.lean. True circular genome S=AAATT, genome length G=5, read length L=3, n=4 independent uniformly sampled starts (0,0,1,4). They produce AAA, AAA, AAT, TAA. The existing Lean theorem truth_information_feasible checks the actual project bridging predicate for those distinct placements.

Consider a candidate circular genome D=AAATA of the SAME length G=5. Its complete molecule-class spectrum differs from the truth; cyclic rotation or reverse complement preserves the spectrum, so this is a genuinely different candidate.

| Molecule class | Observed x | Truth S | Candidate D |
|---|---:|---:|---:|
| AAA | 2 | 1 | 2 |
| AAT (≡ ATT) | 1 | 2 | 1 |
| ATA (≡ TAT) | 0 | 0 | 1 |
| TAA (≡ TTA) | 1 | 2 | 1 |

Both genome-spectrum columns sum to five circular start positions.

## The observed-read circuit really spells D

The four visited oriented reads are AAA, AAA, AAT, TAA, back to AAA. The successive overlap lengths are 2,2,1,2. Adjacent suffixes/prefixes match; their total circular extension is

$$
(3-2)+(3-2)+(3-1)+(3-2)=5.
$$

The resulting circular word is AAATA, with full length-3 windows AAA,AAT,ATA,TAA,AAA. The **unobserved ATA** is an internal window skipped by the length-1 overlap AAT→TAA. Hence the connected flow's observed-read vertex throughput vector d*=(AAA:2,AAT:1,TAA:1) is accurate ON THE OBSERVED VERTICES, but **is not the full genome spectrum** because it incorrectly treats the new ATA type as absent. This is compatible with the existing kernel-checked no_sequence_has_star_spectrum theorem: it precludes a genome whose COMPLETE vector equals d*, not the existence of the spelled genome D.

## Exact product-binomial comparison

For external known genome size N=5 and candidate complete molecule spectrum d, the Medvedev–Brudno (2009) §6.1 separable approximation is

$$
B(d\mid x)=\prod_w\binom{4}{x_w}
  \left(\frac{d_w}{5}\right)^{x_w}
  \left(1-\frac{d_w}{5}\right)^{4-x_w}.
$$

The existing Lean flow-only truncated optimum has B(d*|x)/B(d_S|x)=256/81. Restoring the extra unobserved ATA count 1 adds its zero-observation binomial factor (1−1/5)^4=256/625. Thus the **full spelled candidate genome** still strictly beats the information-feasible truth for this particular sample:

$$
\boxed{\frac{B(d_D\mid x)}{B(d_S\mid x)}
=\frac{256}{81}\frac{256}{625}
=\frac{65536}{50625}>1.}
$$

The **exact iid multinomial** candidate likelihood, however, is tied for the same sample:

$$
\frac{\mathcal L_{\rm iid}(D;x)}{\mathcal L_{\rm iid}(S;x)}
=(2/1)^2(1/2)(1/2)=1.
$$

Do not conflate the approximation with exact multinomial ML.

## Reproduction and next proof obligations

Run the independent exact-arithmetic verifier:

    python3 scripts/verify_spelled_binomial_witness_261.py

The verifier enumerates circular windows, RC-collapsed molecule classes, the oriented string overlaps at the sequence level, and all relevant binomial marginals with fractions.Fraction. It checks the explicit ratio and the full-vs-truncated spectrum distinction. This independent arithmetic script supplements the finite kernel-checked Lean theorems named below.

**New Lean verification:** The repository now proves dSpelled261_0/1/2/4, dSpelled261_off, spelledCandidate261_binomial_ratio, spelledCandidate261_binomial_better, spelled_candidate_reversal_with_bridging, spelledCandidate261_iid_tie, spelledCandidate261_circuit_edges_survive, and spelledCandidate261_circuit_signed in AssemblyP1.Section62NonSpelledFlow. The mathematical score and actual finite reduced edges plus all circular signed seams are therefore kernel-checked, not just reproduced by Python. A GENERAL theorem connecting arbitrary signed circuits to the complete internal-window spectrum is still a separate problem. Source-fidelity remains open: the exact MB09 surrogate and iid exact likelihood should not be conflated, and the 2016 sentence does not unambiguously select one referent.

**Scope relative to the earlier positive theorem:** Interpretation-matrix row R7 concerns genuine same-length section-6.2 candidates whose flow throughputs represent the observed-read vertex support. D contains the UNOBSERVED ATA molecule and lies outside that restricted candidate class; the Lean lemma spelledCandidate261_outside_observed_support makes the support mismatch explicit. A circuit spelling a word need not encode its complete genome spectrum. Thus this result is NOT a counterexample to the established R7 positive theorem or a selection of the 2016 paper's ambiguous ML referent.

This is a narrow technical manuscript result; the public presentations should continue foregrounding positive reconstruction and rigorous guarantees rather than a negative example.
