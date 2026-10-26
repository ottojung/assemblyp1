# RC quotient changes the AAATT candidate-pair verdict (#261)

**Status: exact finite witness; not a maximality theorem.** This note isolates an
orientation/RC choice on the existing reduced overlap graph at `L=3`, `o_min=1`.
The two candidates are circular genomes of length `N=5`:

* truth `AAATT`, admitted to the candidate set;
* competitor `AAATA`, also admitted.

The observed four reads are oriented windows of the truth at starts
`(0,0,1,2)`: `AAA, AAA, AAT, ATT`. In an oriented-read alphabet, the candidate
probability is the circular length-3 window frequency. The exact iid likelihood
ratio (competitor/truth) is zero because `ATT` occurs in the sample but not in
`AAATA`. Thus truth strictly beats this competitor.

If both observations and candidate spectra are instead indexed by
reverse-complement molecule classes, `AAT` and `ATT` collapse to class `AAT`.
The truth spectrum is `{AAA:1,AAT:2,TAA:2}` and the competitor molecule spectrum
is `{AAA:2,AAT:1,ATA:1,TAA:1}`. The resulting exact iid likelihood ratio is
`(2/1)^2 (1/2)^2 = 1`: the same truth/competitor pair ties. Consequently the
pairwise verdict changes under the RC quotient. This establishes only a tie in
the quotient model, not a global maximizing or uniqueness claim.

The candidates in this witness are spelled circular genomes (up to rotation for
the oriented convention, and up to rotation plus reverse-complement for the
quotient convention). They are **not arbitrary feasible flows**. Both have
length 5 and contain the observed vertex `ATA` in their length-3 spectrum, so
their windows lie in the ordinary reduced graph obtained by deleting
non-maximal overlaps from the full `o_min=1` graph. The evidence is an exact
source-model arithmetic witness; the source distinction is the oriented
single-strand versus molecule-class indexing. The exact likelihood is the iid
uniform-start product, not the fixed-external-`N` binomial surrogate.

An independent rational verifier is `scripts/verify_261_rc_orientation_class.py`.
It asserts both spectra and the two likelihood ratios without importing Lean.
It does not settle whether arbitrary flows or circular genomes have the same
maximality verdict, nor provide a general RC-invariance/maximality criterion.
Those #261 axes remain OPEN; #255 remains open.
