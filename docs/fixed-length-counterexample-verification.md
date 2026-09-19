# Independent verification: fixed-length Variant E counterexample

_Status: independent verification, 2026-09-19. Confirms the existing fixed-length counterexample is correct. Includes Lean formalization._

## Scope

Independently verify the fixed-length Variant E counterexample from `docs/bridging-likelihood-obstructions.md` (§Counterexample 2): truth `AACAGG` vs competitor `AAAGGC`, both length 6, exact multinomial likelihood. Formalize in Lean and kernel-check.

## 1. Primary source grounding

### What is being refuted

Fixed-length exact Variant E (Medvedev–Brudno §6.1 restricted to |D| = G): bridging conditions guarantee that the true genome is an ML maximizer among all length-G circular candidates.

### Source definitions used

- **Exact multinomial:** L(D|x) = N!/(∏ x_i!) · ∏ (d_D(i)/G)^{x_i} — Medvedev–Brudno §6.1 (PMC3154397)
- **Fixed-length restriction:** |D| = G for all candidates — not source-justified for exact ML (§6.1 first half uses candidate-dependent N(D)), but is a named subproblem per `docs/ml-formalization-contract.md`
- **Bridging/I_s:** Coverage ∧ all-bridged triple repeats ∧ bridged interleaved repeats — Shomorony Eq. (1), attributed to Bresler et al. (2013)
- **Circular genome:** Both primary papers model circular genomes — Shomorony §2, Medvedev–Brudno §6.1

### Epistemic status

This counterexample refutes fixed-length Variant E with the information-feasible hypothesis. It does NOT refute:
- Unrestricted-length Variant E (covered by `ExactVariantECounterexample.lean`)
- Variant A (binomial approximation)
- Variant F (flow feasible set)
- The published open question (per `docs/audit-variant-e-settlement.md`)

## 2. Independent verification

### Truth genome

S = AACAGG (G=6, L=2). Length-2 circular windows:

| Position | 2-mer |
|----------|-------|
| 0 | AA |
| 1 | AC |
| 2 | CA |
| 3 | AG |
| 4 | GG |
| 5 | GA |

All 6 windows distinct: S is repeat-free. Spectrum: {AA:1, AC:1, CA:1, AG:1, GG:1, GA:1}.

### Observed sample

x = {AA:5, CA:1, GG:1} (N=7). Latent starts [0, 0, 2, 0, 0, 4, 0] or equivalent.

**Coverage:** AA reads at starts {0, 1, 3, 5, 6} cover positions {0,1}, {1,2}, {3,4}, {5,0}, {0,1}. CA read at start 2 covers {2,3}. GG read at start 4 covers {4,5}. All 6 positions covered. ✓

**Bridging:** S is repeat-free ⇒ no repeats ⇒ no triple/interleaved repeats ⇒ bridging conditions vacuously satisfied. ✓

### Competitor genome

D = AAAGGC (G=6, L=2). Length-2 circular windows:

| Position | 2-mer |
|----------|-------|
| 0 | AA |
| 1 | AA |
| 2 | AG |
| 3 | GG |
| 4 | GC |
| 5 | CA |

Spectrum: {AA:2, AG:1, GG:1, GC:1, CA:1}.

### De Bruijn graph balance (independently verified)

For circular string AAAGGC with alphabet {A, C, G, T}:

| Vertex | Out-degree | In-degree | Balanced? |
|--------|-----------|-----------|-----------|
| A | d(AA)+d(AG) = 2+1 = 3 | d(AA)+d(CA) = 2+1 = 3 | ✓ |
| G | d(GG)+d(GC) = 1+1 = 2 | d(AG)+d(GG) = 1+1 = 2 | ✓ |
| C | d(CA) = 1 | d(GC) = 1 | ✓ |
| T | 0 | 0 | ✓ |

AAAGGC is a valid length-6 circular string. ✓

### Observed types positivity

All observed types {AA, CA, GG} have d_D > 0: d_D(AA)=2, d_D(CA)=1, d_D(GG)=1. ✓

### Likelihood comparison (exact rational arithmetic)

Fixed-length exact multinomial, comparing ∏ d(i)^{x_i}:

```
f(S) = d_S(AA)^5 · d_S(CA)^1 · d_S(GG)^1 = 1^5 · 1^1 · 1^1 = 1
f(D) = d_D(AA)^5 · d_D(CA)^1 · d_D(GG)^1 = 2^5 · 1^1 · 1^1 = 32
```

Ratio: f(D)/f(S) = 32.

Including the full multinomial with denominator G^N = 6^7:
```
L(S|x) ∝ 1/6^7
L(D|x) ∝ 32/6^7
```

Ratio = 32. ✓

## 3. What this counterexample establishes

**Kernel-checked conclusion:** There exists a true circular genome S = AACAGG of length 6 with read length 2, observed reads satisfying coverage and the information-feasible hypothesis (vacuous bridging), such that a competitor D = AAAGGC of the same length has exactly multinomial likelihood 32 times higher than S.

This refutes: "For fixed-length exact Variant E with |D| = G, the information-feasible hypothesis R ∈ I_s implies truth is an ML maximizer."

## 4. Lean formalization

The corrected counterexample is formalized in `AssemblyP1/FixedLengthVariantECounterexample.lean` with kernel-checked proofs of:
- Repeat-freeness of AACAGG
- Coverage by the realized sample
- Vacuous bridging
- De Bruijn graph validity of AAAGGC
- Exact likelihood ratio of 32
- The fixed-length counterexample theorem

## 5. Source citations

| Claim | Primary source | Repository anchor |
|-------|---------------|-------------------|
| Exact multinomial with N(D) | Medvedev–Brudno §6.1 (PMC3154397) | `docs/source-notes/medvedev-brudno-candidate-class.md:16-44` |
| Fixed-length restriction not source-justified for exact ML | Medvedev–Brudno §6.1 | `docs/source-notes/candidate-genome-class-resolution.md:97-103` |
| Repeat-free vacuous bridging | Bresler et al. (2013); Shomorony Eq. (1) | `docs/bridging-source-semantics.md:45-61` |
| Coverage via latent starts | Shomorony §2 | `docs/bridging-source-semantics.md:53-61` |
| De Bruijn graph Eulerian balance | Pevzner (2000); standard de Bruijn graph theory | `docs/fixed-length-ml-objective-analysis.md:75-84` |
| I_s definition | Shomorony Eq. (1) | `docs/bridging-source-semantics.md:53-61` |
