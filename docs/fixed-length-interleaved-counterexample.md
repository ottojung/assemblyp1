# Fixed-length exact-ML counterexample exercising the interleaved-repeat clause

_Status: computational counterexample + exact arithmetic, independently verified
by a second, self-contained implementation. Not a Lean result. Does not settle
the source-ambiguous Shomorony et al. open question, and does not address
unrestricted-length exact ML (issue #24 / PR #25)._

## Scope and why this note exists

The existing kernel-checked fixed-length counterexample
(`docs/fixed-length-exact-counterexample.md`,
`AssemblyP1/FixedLengthExactCounterexample.lean`) uses the truth `S = AAABB`,
whose reads satisfy coverage and whose **only** repeat obligation is a single
all-bridged triple repeat. Its truth has **no interleaved repeat pair**, so the
third conjunct of the source information-feasible set `I_s` is satisfied only
vacuously there.

That leaves a real objection open: perhaps the interleaved-repeat bridging
condition is exactly what rescues maximum-likelihood optimality, and the
existing refutation only exploits a degenerate case. This note closes that gap.
It exhibits fixed-length exact counterexamples whose truth genome has a
**non-vacuously bridged interleaved repeat pair**, verified against the source
semantics of `docs/bridging-source-semantics.md`.

The headline witness additionally has a non-vacuous all-bridged triple repeat,
so **both** nontrivial conjuncts of `I_s` are exercised simultaneously.

## Source/model assumptions

These are exactly the assumptions of the existing fixed-length variant and are
kept explicit so the claim cannot be read as settling a different variant.

- **Circular genome** of length `G` over a finite alphabet, with length-`L`
  circular windows (`read types`).
- **Reads** are error-free and length-`L`; the realized sequencing is a
  multiset of `N` latent start positions. Coverage and bridging are properties
  of `(S, latent starts)`; the likelihood sees only the observed read-type
  counts `x_i`.
- **Candidate universe (fixed length):** every circular genome `D` with
  `len(D) = G`. This is the named "fixed-length" restriction, not the literal
  Medvedev–Brudno exact multinomial over all candidate lengths.
- **Objective (Variant E, fixed length):**
  `L(D | x) ∝ ∏_i (d_D(i)/G)^{x_i}`, where `d_D(i)` is the number of circular
  length-`L` windows of `D` equal to read type `i`; the multinomial coefficient
  is observation-only and cancels. `L(D|x) > L(S|x)` therefore means
  `∏_{i: x_i>0} d_D(i)^{x_i} > ∏_{i: x_i>0} d_S(i)^{x_i}`.
- **Hypothesis `I_s` (Shomorony et al. Eq. (1), attributed to Bresler et al.):**
  (1) the reads cover `S`; (2) every maximal triple repeat of `S` is
  all-bridged; (3) every interleaved pair of maximal repeat pairs of `S` is
  bridged. "Maximal", "bridged" (strict two-sided extension), triple-repeat and
  interleaving follow `docs/bridging-source-semantics.md`, including
  origin-independence of interleaving on the circle.

## Headline witness: both nontrivial conjuncts exercised

```text
truth       S = A B A C A B C        (G = 7)
competitor  D = A C A B A C B        (G = 7)
read length L = 3
latent starts = (1, 1, 1, 3, 6)      (N = 5)
observed types = { BAC: 3, CAB: 2 }
```

### Coverage

Reads at starts `1, 3, 6` occupy positions

- `1 -> {1,2,3}`, `3 -> {3,4,5}`, `6 -> {6,0,1}`,

whose union is all of `{0,...,6}`. Coverage holds.

### Repeat / bridging certificate

Circular 3-mer counts:

```text
S: ABA=1 BAC=1 ACA=1 CAB=2 ABC=1 BCA=1
D: ACA=1 CAB=1 ABA=1 BAC=2 ACB=1 CBA=1
```

Maximal repeat pairs of `S` (equal word, preceding symbols differ, following
symbols differ):

```text
length 1: A @ (0,2)   and  A @ (2,4)
length 3: CAB @ (3,6)
```

Triple repeats of `S` (three-copy maximality):

```text
length 1: A @ (0,2,4)      (preceding C,B,C not all equal; following B,C,B not all equal)
```

Interleaved pair (four starts alternate on the circle):

```text
A @ (2,4)  ||  CAB @ (3,6)      cyclic order 2,3,4,6 -> A, CAB, A, CAB
```

Bridging witnesses under `starts = (1,1,1,3,6)`, `L = 3`:

```text
A @ 0  bridged by read at 6   (covers 6,0,1)
A @ 2  bridged by read at 1   (covers 1,2,3)
A @ 4  bridged by read at 3   (covers 3,4,5)
```

Thus every copy of the triple repeat `A@(0,2,4)` is bridged (all-bridged), and
the interleaved pair is bridged via the `A@(2,4)` copy. Both nontrivial `I_s`
conjuncts hold non-vacuously.

### Exact likelihood comparison

Observed types only (`x_i > 0`) are `BAC:3, CAB:2`.

```text
d_S(BAC)=1, d_S(CAB)=2
d_D(BAC)=2, d_D(CAB)=1

L(D)/L(S) = (2/1)^3 * (1/2)^2 = 8/4 = 2 > 1.
```

So `D` is strictly more likely than the truth under the fixed-length exact
objective, while the truth satisfies the full source `I_s` including a
non-vacuous bridged interleaved repeat.

## Minimal interleaved-clause witness

The smallest instance found (fewest reads) whose truth has a bridged
interleaved pair uses four reads:

```text
truth       S = A A A B A C C        (G = 7)
competitor  D = A A A A B A C        (G = 7)
read length L = 3
latent starts = (0, 1, 3, 6)          (N = 4)
observed types = { AAA:1, AAB:1, BAC:1, CAA:1 }
d_S = 1 for each observed type;  d_D(AAA)=2, others 1
L(D)/L(S) = 2.
```

Here the interleaved structure is two length-1 repeat pairs of the **same**
word `A`, `A@(0,2) || A@(1,4)`, both copies bridged. It is included as the
minimal-size interleaved witness; the headline witness above is preferred
because its interleaved pair uses two **distinct** repeat words and it also
exercises the triple-repeat clause.

## Search boundary: no interleaved counterexample at G <= 6

An exhaustive search over the following ranges found **zero** same-length
counterexamples whose truth has a bridged interleaved repeat pair:

| `G` | `L` | alphabet | `N` | I_s pairs with interleaved repeats | interleaved counterexamples |
|-----|-----|----------|-----|-----------------------------------|-----------------------------|
| 4   | 3,4 | 3        | 4..8 | 0 | 0 |
| 5   | 3,4 | 3        | 4..8 | 0 | 0 |
| 6   | 3   | 2        | 6,7 | 252 / 672 | 0 |
| 6   | 3   | 3        | 5..15 | > 1M total | 0 |
| 6   | 3   | 4        | 6,7,8 | > 400k total | 0 |
| 6   | 4   | 3        | 5..8 | > 300k total | 0 |
| 6   | 4   | 4        | 6 | 217872 | 0 |
| 6   | 5   | 3        | 5..8 | > 500k total | 0 |
| 7   | 3   | 2        | 5,6 | 0 | 0 (no I_s interleaved structures) |
| 7   | 3   | 3        | 4 | 1764 | **84** (all same-word) |
| 7   | 3   | 3        | 5 | 9198 | **462** (42 with distinct words) |
| 7   | 3   | 3        | 6 | 32088 | **1470** (210 distinct) |
| 7   | 3   | 3        | 7 | 88830 | **3528** (588 distinct) |

At `G >= 7` interleaved counterexamples exist; at `G <= 6` the tested space has
none even though `I_s`-satisfying interleaved structures are plentiful (for
example `G=6, L=3, alpha=3, N=6` has 11592 such pairs and 900 counterexamples,
**all** of which have no interleaved repeat). At `G=5` no `I_s`-satisfying
instance with interleaved repeats exists in the tested range, so the clause is
vacuous there.

**Epistemic status of the boundary:** bounded computational evidence from
exhaustive enumeration, not a proof. The counts above are exact; the absence of
a witness is only established within the stated finite ranges. It suggests (but
does not establish) a structural lemma of the form "at `G=6` every bridged
interleaved repeat configuration blocks same-length amplification", which is
left as an open target.

## Relation to existing artifacts

- Strengthens `docs/fixed-length-exact-counterexample.md`: it shows the
  interleaved conjunct of `I_s` does not rescue fixed-length exact ML
  optimality, so the source-faithful hypothesis as a whole is refuted, not just
  its degenerate sub-case.
- Consistent with `docs/exhaustive-small-instance-search-v2.md`; the v2
  "substantive" counterexamples all have triple repeats but no interleaved
  repeats. This note supplies the missing interleaved samples.
- Does **not** touch unrestricted-length exact Variant E (already refuted by
  PR #25), the separable/binomial approximation (issue #32), or the Section 6.2
  flow-feasible set (Variant F), and does not resolve which variant Shomorony et
  al. intended.

## Reproducibility

All arithmetic is exact rational (`fractions.Fraction`). Both the verifier and
the search script are self-contained: they re-implement repeat/triple-repeat/
interleaving/bridging from the source semantics instead of importing the
reviewed `scripts/fixed_length_bridging_search_v2.py`, so agreement with that
script is independent evidence. During development the same boundary counts
were also reproduced through the reviewed v2 search.

```bash
# Independent, self-contained verification of all witnesses in this note.
python3 scripts/verify_interleaved_counterexample.py

# Exhaustive search for interleaved-clause counterexamples and minimality.
python3 scripts/fixed_length_interleaved_search.py --G 7 --L 3 --alpha 3 --N 4
python3 scripts/fixed_length_interleaved_search.py --G 7 --L 3 --alpha 3 --N 5

# G<=6 boundary: many I_s interleaved pairs, zero interleaved counterexamples.
python3 scripts/fixed_length_interleaved_search.py --G 6 --L 3 --alpha 3 --N 6
python3 scripts/fixed_length_interleaved_search.py --G 6 --L 4 --alpha 4 --N 6
```

## Epistemic status

| Claim | Status |
|-------|--------|
| Witness `ABACABC` / `ACABACB` satisfies full source `I_s` (coverage, all-bridged triple repeat, bridged interleaved pair) | **Verified**, exact finite check by two independent implementations |
| `L(D)/L(S) = 2 > 1` for that witness | **Verified**, exact rational arithmetic |
| Minimal interleaved witness at `G=7, N=4` | **Computational evidence**, exhaustive in stated range |
| No interleaved counterexample at `G<=6` in tested ranges | **Computational evidence** (bounded), not a proof |
| Fixed-length exact `I_s => truth ML` is false | **Refuted** (already by G=5 witness; re-confirmed here including the interleaved clause) |

Primary sources: Medvedev & Brudno, *Maximum Likelihood Genome Assembly*,
J. Comput. Biol. 16(8) (2009) §6.1; Shomorony, Kim, Courtade, Tse,
*Information-optimal genome assembly via sparse read-overlap graphs*,
Bioinformatics 32(17) (2016) i494–i502 Eq. (1); Bresler, Bresler, Tse,
*Optimal assembly for high throughput shotgun sequencing*,
BMC Bioinformatics 14(Suppl 5):S18 (2013).
