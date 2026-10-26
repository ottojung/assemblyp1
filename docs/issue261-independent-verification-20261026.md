# Issue #261 independent verification (2026-10-26)

## Repository and revision

Verified remote: `https://github.com/ottojung/assemblyp1.git`.
The fresh clone fetched `research/261-rc-orientation-ascertain` at
`3567c33976444c618d7091f24fe9c151601ac5cf`; local `HEAD` and the fetched remote
tracking ref matched. `main` was `234f3480d7589c8fc4e056c91dda91343fe64ece`.
The predecessor checkpoint `f334a5661c75a666ac5a00034a5ac987e1333cc8` is not
the current issue-branch tip. The current tip includes
`docs/issue261-class-transfer-checkpoint-20261026.md`.

## Independent rerun

From the clean fresh checkout, all commands exited successfully:

* `python3 scripts/verify_261_rc_orientation_class.py` — exact iid ratio is 0
  for oriented reads and 1 after RC-class quotient; confirms only the stated
  pairwise verdict change.
* `python3 -m py_compile scripts/verify_261_rc_orientation_class.py` — pass.
* `python3 scripts/verify_spelled_binomial_witness_261.py` — exact rational
  assertions pass; full-binomial ratio `65536/50625`, truncated-flow ratio
  `256/81`, exact iid multinomial ratio `1`.
* `python3 scripts/verify_oriented_molecule_bridging.py` — all assertions pass,
  including the candidate-model boundary and bounded-search caveats.
* `python3 scripts/check-research-docs.py` — research documentation integrity
  checks pass.
* `git diff --check` — pass (clean tree).

No Lean files changed; these checks provide executable corroboration, not a new
kernel-checked theorem.

## Scoped next open subclaim

Resolve the whole-candidate-set relation between oriented circular-genome
spectra and reverse-complement molecule-class spectra for exact uniform-start
iid likelihood. The verified AAATT/AAATA example establishes a pairwise tie
after quotient, but does not characterize either candidate set's global
maximizers or transfer maximality. Preserve the distinction from fixed-external-
`N` product-binomial flow objectives.
