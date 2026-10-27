# Finite-sample likelihood: pairwise criterion

For a fixed finite admissible candidate class `C`, observed data `x`, and
likelihood `L(S; x)`, truth `S` is a (not necessarily unique) maximum-likelihood
candidate precisely when

`∀ T ∈ C, L(S; x) ≥ L(T; x)`.

This elementary pairwise criterion is formalized in
`AssemblyP1/FiniteLikelihood.lean`. The module also proves that multiplying
every candidate score by the same nonnegative factor preserves the set of
maximizers. In an exact multinomial likelihood this covers dropping the common
multinomial coefficient when comparing candidates.

The criterion is exact but not a structural assembly characterization: it
still quantifies over the candidate class and depends on the particular
observation. It asserts neither uniqueness nor truth maximality for every
possible sample. It does not choose between oriented and reverse-complement
molecule types, exact multinomial and fixed-N binomial objectives, equal and
variable lengths, spelled genomes and MB09 §6.2 bidirected flows/overlap floors,
truth candidacy, or historical versus project placement `I_s`. All substantive
classifications on those axes remain open.
