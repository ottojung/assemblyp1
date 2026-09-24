# Complete-spectrum identifiability converse search

## Question

In the fixed-orientation, complete integer `L`-spectrum model, is the project P2/Ukkonen condition necessary for unique identification up to rotation among same-length circular genomes?

## Exact bounded model

A candidate is a circular binary word with fixed orientation; rotation is the only genome equivalence. At a fixed `(L,n)`, the script enumerates every primitive length-`n` binary word, identifies its complete ordered `L`-mer multiplicity spectrum, and groups candidates by that exact spectrum. It then selects the first candidate in increasing `(L,n)` whose spectrum group contains one canonical rotation but whose P2 predicate is false.

For each length `1 <= ell <= L-1`, the P2 predicate detects a maximal triple repeat or an interleaved pair of maximal repeats:

- a repeat is maximal when at least one of its preceding symbols and at least one of its following symbols differ among the copies;
- the interleaving check requires four distinct starts ordered with labels `ABAB` or `BABA`.

The alphabet restriction is a search bound, not part of the universal uniqueness proof. Genome equivalence does not include reversal or reverse complement. Candidates are constrained to the same length as the truth.

## Reproduce

```sh
python3 scripts/search_spectrum_identifiability_converse.py \
  --max-length 2 --max-size 4 > results-scope-minimal.json
python3 scripts/search_spectrum_identifiability_converse.py \
  --max-length 2 --max-size 6
```

The checked-in result records the exact bounds, model, counts, first hit, and evidence class.

## Result

The first hit is

```text
S = AAAB,  L = 2,  |S| = 4,
spec_2(S) = {AA:2, AB:1, BA:1}.
```

`AAAB` is primitive. Starts `0,1,2` are the three occurrences of `A`; their preceding symbols are `B,A,B` and their following symbols are `A,A,B`, so the length-`1` repeat is a maximal triple repeat. Since `1=L-1`, P2 fails.

The order-`1` de Bruijn multigraph has two loop edges `AA -> AA` and the forced chain `AA --AB--> BA --BA--> AA`. Any Eulerian circuit traverses the non-loop chain and then the two loops, so its circular edge spelling is forced. Therefore the displayed spectrum has only the circular spelling `AAAB`. This is a mathematical proof of uniqueness over every finite alphabet, not merely the searched binary scope.

The exhaustive computation is evidence of minimality in the stated ordered finite scope: no smaller `(L,n)` was found. It is not a proof of minimality over arbitrary alphabets, where longer examples can relabel symbols. **[computational evidence, exhaustive only for the stated scope; witness uniqueness: mathematical proof]**

## Boundary

This refutes the converse of the bare P2/Ukkonen repeat condition, not its sufficiency. It does not establish finite-read maximum-likelihood uniqueness, uniform recovery, population-ML identifiability, or identifiability among variable-length candidates. Those statements require separately stated quantifiers and models.
