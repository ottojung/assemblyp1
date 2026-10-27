# Issue #255: fixed-x exact-rational result/open matrix

This matrix reconciles the fixed-`x` exact-multinomial artifact only. It is
not an umbrella resolution; all conclusions below are scoped to the stated
candidate universe and objective.

| Claim | Status | Evidence and exact scope |
|---|---|---|
| For finite oriented read types `E`, positive common length `G`, and spectra `A,B : E → ℕ` of mass `G`, compare exact multinomial likelihoods at fixed counts `x`. | **Proved (kernel-checked)** | `AssemblyP1/FixedXExactML.lean`: `specLik_le_iff_likProduct` cancels the common positive denominator and fixed multinomial coefficient; `fixedX_classification_iff` makes truth maximal over a finite candidate set iff each candidate's integer product is at most truth's. Zero-probability observed types are included without logarithms. See `docs/issue255-fixedx-fixed-candidate-criterion.md`. |
| In the `AAABBB`, `G=6`, `L=2` four-spectrum instance, truth wins, ties, and loses for explicit samples. | **Proved (kernel-checked; exact integer comparisons)** | `fixedX_four_chamber_iff_258`; the independent rational verifier `scripts/verify_255_fixedx_fourchamber.py` checks the reported chambers. |
| Structure alone determines whether truth maximizes at a particular `x`. | **Refuted as a general inference** | The fixed-candidate criterion depends on `x`; `docs/issue255-fixedx-vs-everysample-separation.md` and `scripts/verify_255_fixedx_vs_everysample.py` give same truth/candidate with one strict-win and one strict-loss sample. This is a bounded witness, not a universal classification. |
| Pairwise-product criterion classifies all fixed-`x` cases beyond finite candidate comparison. | **Open** | The criterion is necessary and sufficient once the finite type set and candidate class are specified, but no general structural simplification or genome-realizability criterion is established. |
| Transfer to reverse-complement molecule types, fixed-`N` binomial objective, variable length, historical read-string `I_s`, or MB09 §6.2 bidirected flows/overlap floor. | **Open / not asserted** | These are different axes or candidate/objective domains. The cited Lean theorem is for oriented same-length spectra and exact multinomial likelihood; the fixed-candidate note explicitly marks these boundaries. |
| Every-admissible-sample (B) maximality follows from this fixed-`x` result. | **Not proved** | A fixed-`x` iff can be quantified over samples only after specifying the admissible sample domain. Existing full-start-covered exact-iid results are a distinct scoped theorem; they do not identify historical `I_s` with that domain. |

**Verification performed in this checkout:** `python3 scripts/verify_255_fixedx_vs_everysample.py`,
`python3 scripts/verify_255_fixedx_second_witness.py`,
`python3 scripts/verify_255_fixedx_fourchamber.py`, and
`python3 scripts/check-research-docs.py` all passed. The `python` executable is
not installed here; the same scripts ran successfully under `python3`.
