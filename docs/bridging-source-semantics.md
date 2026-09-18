# Source semantics for repeats and bridging

This note records the hypothesis-side source semantics needed for the AssemblyP1 open problem. It is source/model reconstruction, not a proof strategy and not a claim that the bridging hypotheses imply maximum-likelihood recovery.

Primary sources:

- Guy Bresler, Ma'ayan Bresler, and David Tse, “Optimal assembly for high throughput shotgun sequencing,” *BMC Bioinformatics* 14(Suppl 5):S18, 2013. DOI: https://doi.org/10.1186/1471-2105-14-S5-S18
- Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, and David N. C. Tse, “Information-optimal genome assembly via sparse read-overlap graphs,” *Bioinformatics* 32(17), 2016, i494–i502. DOI: https://doi.org/10.1093/bioinformatics/btw450

## Circular indexing and repeat occurrences

**Source fact.** Bresler et al. work with a circular DNA sequence and use length-`ℓ` substrings beginning at positions on that circle. A length-`ℓ` repeat is a substring occurring at two start positions `t₁,t₂` and is required to be maximal on both sides: the symbols immediately preceding the two copies differ and the symbols immediately following the two copies differ. A *copy* is one occurrence of the repeated substring.

**Source fact.** Their triple-repeat definition uses three starts `t₁,t₂,t₃` with equal length-`ℓ` substrings. Its maximality condition is the three-copy analogue: the preceding symbols are not all equal and the following symbols are not all equal. The paper explicitly notes that a substring repeated more than three times gives rise to multiple repeats and triple repeats; “triple repeat” therefore should not be modeled as “a substring whose total multiplicity is exactly three.” See Bresler et al., the repeat-definition paragraph surrounding Fig. 4 (published article p. 5).

This is important for Lean: a repeat/triple-repeat object should identify selected occurrences and carry the relevant maximality condition, rather than being defined only by the total number of occurrences of a word.

## Bridging a copy

**Source fact.** Bresler et al. define a length-`ℓ` substring occurrence to be bridged iff at least one observed read covers at least one base on **both** sides of that occurrence (Fig. 5 and the paragraph immediately before Theorem 1). Shomorony et al. use the same strict extension convention in §3/Fig. 6: a read extends at least one base before and at least one base after the repeat segment.

Thus “contains the repeated substring” is not sufficient if the read starts exactly at the copy or ends exactly at its last base. In a zero-based half-open interval normalization, a read interval `[r,r+L)` bridges a chosen lifted occurrence interval `[t,t+ℓ)` exactly when

`r < t` and `t + ℓ < r + L`.

For a circular genome this interval formula is a **modeling normalization**, not source notation: it should be interpreted on a suitable integer lift of the circle, so occurrences/reads crossing the chosen origin are not treated differently.

## Bridged repeats and interleaving

**Source fact.** Bresler et al. use the following abbreviations after Theorem 1:

- a repeat (and likewise a triple repeat) is *bridged* if at least one of its copies is bridged;
- a pair of interleaved repeats is *bridged* if at least one of the two repeats is bridged.

Combining those clauses, an interleaved pair is bridged iff at least one selected copy among the two repeats is bridged by some read.

**Source fact.** For two repeats with selected starts `t₁,t₃` and `t₂,t₄`, respectively, Bresler et al. call the pair interleaved when their starts alternate around the sequence, written in their linearized convention as either `t₁ < t₂ < t₃ < t₄` or `t₂ < t₁ < t₄ < t₃`. The length of an interleaved pair is the shorter repeat length.

Because the genome is circular, the inequalities depend on choosing an origin. The source-level invariant is cyclic alternation of the four selected starts. A Lean definition should therefore either use a cyclic-order predicate directly or prove that an existential choice of rotation/linearization is equivalent. Treating the displayed inequalities as absolute natural-number order without rotation would introduce an origin artifact.

## All-bridged triple repeats

**Source fact.** Bresler et al.'s MultiBridging sufficient condition requires **all triple repeats to be all-bridged**, meaning every selected copy of each triple repeat is bridged. Their Theorem 6 states the three sufficient conditions as: all interleaved repeats are bridged; all triple repeats are all-bridged; and the sequence is covered by the reads.

Shomorony et al. repeat the same convention in §3 and Fig. 6: a triple repeat is all-bridged if each of its copies is bridged. Their Eq. (1) uses exactly this condition in `I_s`.

This must remain distinct from merely calling a triple repeat “bridged,” which in Bresler et al.'s shorthand means at least one copy is bridged. The latter is enough for the ambiguity lower-bound statement, but is weaker than the all-bridged hypothesis used by MultiBridging and by `I_s`.

## Coverage and the complete `I_s` hypothesis

**Source fact.** Shomorony et al. define the information-feasible set `I_s` in Eq. (1) by three conditions on the observed read collection `R`:

1. `R` covers `s`;
2. triple repeats in `s` are all-bridged;
3. interleaved repeats in `s` are bridged.

In the same section, “covers” is explained as every base of the circular sequence being read by at least one read. Theorem 1 itself assumes coverage plus all-bridged triple repeats; immediately after it, Eq. (1) adds bridged interleaved repeats to identify the information-feasible region inherited from Bresler et al.

Therefore the hypothesis side most directly suggested by the 2016 open-question sentence is not a generic predicate named `bridging`; it is the conjunction represented by `R ∈ I_s`, unless later source work establishes that the Discussion sentence intentionally refers to a different subset of those conditions.

## Proposed Lean-facing surface

The following is **modeling organization**, not quoted source notation. It keeps source-sensitive distinctions explicit:

- `RepeatOccurrencePair g ℓ`: two selected starts with equal length-`ℓ` windows plus the source maximality condition;
- `TripleRepeat g ℓ`: three selected starts with equal windows plus the three-copy maximality condition, without requiring total multiplicity exactly three;
- `BridgesCopy reads t ℓ`: some observed read strictly extends beyond the selected copy on both sides, expressed invariantly on the circle;
- `BridgedRepeat`: at least one selected copy is bridged;
- `Interleaved r₁ r₂`: the four selected starts alternate in cyclic order;
- `BridgedInterleavedPair`: at least one constituent repeat is bridged;
- `AllBridgedTriple`: every selected copy is bridged;
- `Covers reads g`: every genome position lies in at least one observed read occurrence;
- `InformationFeasibleHypothesis g reads`: coverage ∧ every triple repeat is all-bridged ∧ every interleaved pair is bridged.

The observed read strings/multiplicities and the latent start positions used to witness coverage/bridging must not be conflated. PR #10 already records this distinction on the likelihood side: likelihood is a function of the observable read multiset, whereas bridging is a property of the realized placements relative to the true genome.

## Remaining source-fidelity checks

Before these predicates become stable Lean API, independently verify two details against the exact primary-source text/supplement used by Shomorony et al.:

1. whether every repeat object relevant to Eq. (1) inherits Bresler et al.'s maximal-repeat convention or whether the 2016 supplement restates a broader occurrence notion; and
2. the cleanest origin-independent treatment of interleaving when a selected repeat occurrence crosses the arbitrary circular cut.

These are representation/correspondence checks, not evidence against the high-level `I_s` conjunction above. Any mismatch discovered in the supplement should be preserved as an explicit source fork rather than silently normalized away.
