# Parametric counterexample families for fixed-length exact multinomial ML

_Status: mathematical analysis. Not a Lean result. All claims classified by epistemic class._

---

## 1. Scope and purpose

This note gives self-contained exact formulas for parametric counterexample families under **fixed-length exact multinomial** ML (Variant E, |D| = G). For every family member we:
1. State the exact occurrence-count vectors.
2. Prove the exact likelihood-ratio formula.
3. **Explicitly verify bridging conditions** (coverage + all-bridged triple repeats + bridged interleaved repeats).
4. State the Eulerian amplification bound.
5. Show the ratio grows without bound as sample concentration increases.

Complements: mathematics/parametric-variant-e-families.md (unrestricted-length), docs/fixed-length-ml-objective-analysis.md (optimization analysis).

---

## 2. Setup

- True circular genome S, length G, alphabet Sigma, read length L.
- N error-free reads drawn i.i.d. uniformly from G circular starts.
- Observed multiset: type i appears x_i times, sum x_i = N.
- Candidate D of same length G: d_D(i) = count of circular L-window positions equal to type i.

Fixed-length exact multinomial ordering reduces to: argmax_D prod d_D(i)^{x_i}.

Log-likelihood difference: Delta(D) = sum_i x_i log(d_D(i)/d_S(i)).

Bridging I_s: coverage + all-bridged triple repeats + bridged interleaved repeats (Shomorony et al. 2016; Bresler et al. 2013).

Eulerian realizability R1-R3: sum d(i) = G; degree balance; connectivity.

---

## 3. Family I: Self-loop amplification (L = 2)

**Truth.** Repeat-free S, G >= 4. Dominant k-mer: self-loop k = (a,a).

**Competitor.** D = a^G. d_D(a,a) = G, all others 0.

**Bridging.** S repeat-free => no repeats => no triple/interleaved repeats. I_s vacuous. Coverage by construction.

**Eulerian check.** D = a^G: single self-loop edge, balance automatic.

**Ratio.** Sample {AA: n}: R = G^n. Independent of all other parameters.

---

## 4. Family II: Heterologous amplification (L = 2)

**Truth.** Repeat-free S, G >= 4. Dominant k-mer: k = (a,b), a != b.

**Competitor.** D = (ab)^{floor(G/2)} (fill for odd G). d_D(a,b) = floor(G/2), d_D(b,a) = floor(G/2).

**Eulerian check.** Vertex a: out = in = floor(G/2). Vertex b: out = in = floor(G/2). Sum = G.

**Bridging.** S repeat-free => I_s vacuous.

**Ratio.** Sample {AB: n}: R = floor(G/2)^n.

For G = 4: R = 2^n. Matches kernel-checked ACGT instance for single-type sample.

---

## 5. Family III: AABB to ABAB (G = 4, L = 2)

**Truth.** S = AABB. d_S: AA=1, AB=1, BB=1, BA=1. All distinct.

**Competitor.** D = ABAB. d_D: AB=2, BA=2.

**Eulerian check.** A: out=in=2. B: out=in=2.

**Bridging.** All 4 2-mers distinct => no repeats => I_s vacuous.

**Ratio.** Sample {AB: n1, BA: n2}: R = 2^{n1+n2} = 2^N.

**Mechanism.** AB and BA alternate perfectly, doubling both counts. Eulerian balance maintained.

---

## 6. Family IV: Substantive bridging AAABB to AAAAB (G = 5, L = 3)

**Truth.** S = AAABB. Positions: 0:A,1:A,2:A,3:B,4:B.
3-mers: AAA(0), AAB(1), ABB(2), BBA(3), BAA(4). All 5 distinct.
Triple repeat of A at (0,1,2), l=1: preceding {B,A,A} not all equal, following {A,A,B} not all equal.

**Competitor.** D = AAAAB. Positions: 0:A,1:A,2:A,3:A,4:B.
3-mers: AAA(0), AAA(1), AAB(2), ABA(3), BAA(4). d_D(AAA)=2, AAB=1, ABA=1, BAA=1.

**Eulerian check (L=3).** Truth: AA out=in=2, AB out=in=1, BB out=in=1, BA out=in=1. Competitor: AA out=in=3, AB out=in=1, BA out=in=1.

**Bridging (explicit).** Reads from starts [0,1,4]:
- Coverage: {0,1,2} U {1,2,3} U {4,0,1} = {0,1,2,3,4}. All covered.
- Copy t=0: needs start at 4. Read BAA at start 4. Bridged.
- Copy t=1: needs start at 0. Read AAA at start 0. Bridged.
- Copy t=2: needs start at 1. Read AAB at start 1. Bridged.
I_s satisfied SUBSTANTIVELY (not vacuously).

**Ratio.** Sample {AAA: n, AAB: 1, BAA: 1}: R = 2^n.

---

## 7. Family V: Extended substantive bridging (G = 7, L = 3)

**Truth.** S = AAABCBC. Positions: 0:A,1:A,2:A,3:B,4:C,5:B,6:C.
3-mers: AAA(0), AAB(1), ABC(2), BCB(3), CBC(4), BCA(5), CAA(6). All 7 distinct.

**Competitor.** D = AAAAABC. Positions: 0:A,1:A,2:A,3:A,4:A,5:B,6:C.
3-mers: AAA(0,1,2), AAB(3), ABC(4), BCA(5), CAA(6). d_D(AAA)=3, others 1.

**Eulerian check.** AA: out=in=4, AB: out=in=1, BC: out=in=1, CA: out=in=1.

**Bridging.** Triple repeat of A at (0,1,2) with l=1: same mechanism as Family IV. Each copy bridged by read at start t-1 mod 7. I_s substantive.

**Ratio.** Sample {AAA: n, AAB: 1, BCA: 1, CAA: 1}: R = 3^n.

G=7 permits d_D(AAA)=3 (vs 2 at G=5) because Eulerian balance allows more self-loop concentration with 7 positions.

---

## 8. Eulerian amplification bounds (exact)

### L = 2

- Self-loop (a,a): d_D(max) = G. Achieved by a^G.
- Heterologous (a,b), a!=b: d_D(max) = floor(G/2). Achieved by (ab)^{floor(G/2)}.
  Proof: each (a,b) requires one (b,a) for Eulerian balance, using 2 positions. Max = floor(G/2).

### L = 3 (alphabet {A,B})

- Self-loop AAA: d_D(max) = 2 for G in {5,6}, = 3 for G in {7,8}.
  The jump at G=7 reflects relaxed Eulerian constraints.

### General L = 2 over sigma-letter alphabet

The bounds are INDEPENDENT of alphabet size for sigma >= 2. The self-loop and heterologous bounds depend only on G.

---

## 9. Unified ratio formula

For repeat-free S of length G, L = 2, single-type sample {k: n}:

  R = d_D(max, k)^n

where d_D(max, k) is the Eulerian amplification bound for k-mer type k:
  - Self-loop: G
  - Heterologous: floor(G/2)

For fixed-length with substantive bridging (L >= 3), the same formula applies with the L-specific Eulerian bound:
  - G=5, L=3: d_D(max, AAA) = 2 => R = 2^n
  - G=7, L=3: d_D(max, AAA) = 3 => R = 3^n

The ratio grows without bound as n increases, for every (G, L) where d_D(max) >= 2.

---

## 10. Epistemic status

| Family | Ratio formula | Bridging type | Eulerian verified | Status |
|--------|--------------|---------------|-------------------|--------|
| I: self-loop L=2 | G^n | Vacuous | Yes | Proven |
| II: hetero L=2 | floor(G/2)^n | Vacuous | Yes | Proven |
| III: AABB-ABAB | 2^N | Vacuous | Yes | Proven |
| IV: AAABB-AAAAB | 2^n | Substantive | Yes | Proven |
| V: AAABCBC-AAAAABC | 3^n | Substantive | Yes | Proven |

| Claim | Status |
|-------|--------|
| Ratio unbounded in sample concentration | Proven (d_D(max) >= 2 for G >= 4) |
| Bridging asymmetry (S constrained, D not) | Proven (Theorem 2, bridging-likelihood-obstructions.md) |
| Variant E (fixed) refuted | Proven (families III-V) |
| Variant F (flow-feasible) | OPEN |

---

## Source citations

| Fact | Source |
|------|--------|
| Exact multinomial | Medvedev-Brudno 2009, section 6.1 |
| Bridging conditions | Shomorony et al. 2016, Eq. (1); Bresler et al. 2013 |
| Eulerian realizability | Classical graph theory |
| Asymmetry theorem | Proven in repository |
