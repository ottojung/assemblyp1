# Exact circular-read likelihood: common model and witness adapters

This is the proof-level entry point for source-faithful read likelihoods. The
definitions are **not interchangeable** with the source's physical
reverse-complement molecule/flow objective.

## Canonical oriented model

[ExactReadLikelihood.lean](../AssemblyP1/ExactReadLikelihood.lean) reads
`SourceFaithfulIs.Genome` directly. It defines:
- `readCount S L w`: the number of genome start positions spelling `w`,
  including wraparound windows and cases where the read is longer than the
  genome.
- `readMass S L w = readCount S L w / |S|`: the read probability
  under a uniform start, with a proof that the rational value agrees with
  the real-valued `FiniteReadRecoveryGenome.circularReadPMF`.
- `iidLikelihood`: probability of an *ordered* read tuple.
- `observedCount` and `multinomialFactor`: the observed multiset count
  and its candidate-independent factorial coefficient.
- `exactMultinomialLikelihood`: the exact unordered-read score, i.e.
  the observed multiset factor times the iid ordered likelihood.
- `binomialMarginal` / `productBinomialLikelihood`: the separate,
  fixed-external-`N` product-of-binomial-marginals surrogate. Crucially it
  retains the complement factors for read types with zero observed count.

No reference genome length `N` is supplied to the exact model; it uses
each candidate's own `|S|`. The binomial surrogate takes `N` explicitly.
The generic definitions do not restrict candidate length.

## Verified adapters, without changing the historical witnesses

[ExactReadLikelihoodAdapters.lean](../AssemblyP1/ExactReadLikelihoodAdapters.lean)
provides two model-specific adapters:

| Witness | Existing scoring definition | Shared scoring definition | Check |
|---|---|---|---|
| [FixedLengthExactCounterexample](../AssemblyP1/FixedLengthExactCounterexample.lean) | exact multinomial coefficient times three read probabilities | `exactMultinomialLikelihood` at L=3 and n=3, using candidate-intrinsic length | `Exact.likelihood_shared` proves pointwise equality for **every** candidate |
| [FixedLengthBinomialCounterexample](../AssemblyP1/FixedLengthBinomialCounterexample.lean) | full product-of-binomial marginals, including unseen read types | `productBinomialLikelihood` at L=3, n=3, external N=5 | `Binomial.likelihood_shared` proves pointwise equality for **every** candidate |

Each adapter additionally proves literal equality of its bespoke `window`
and `occ` definitions to `Genome.window` and `readCount`. Thus both the
original `I_s` hypothesis and the scored reads genuinely refer to the same
underlying circular windows; we need not rewrite already verified proofs or
assume an unproved modeling correspondence.

Other specialized witness modules belong to different observation models
(reverse-complement molecule classes, bidirected physical edge orbits,
source-specific signed walks, or variable-length source approximations).
Their scores are **not** equal to the oriented exact likelihood without
new hypotheses, and should not be silently folded into this interface.
Keep each in its own explicitly named model and retain the corresponding
mapping/audit in `docs/verification.md`.

## Other verified model bridges

The shared interface is also checked against the other oriented read model
representations:

- \`Issue209EAudit\`: shared circular multiplicities, observed counts, each
  binomial marginal and the entire fixed-external-N product score agree for
  **every** genome and any external N. This score can become negative outside
  its admissible N-domain; the existing audit states that limitation.
- \`OrientedRigidity\`: its generic circular window and complete multiplicity
  spectrum are literally equal to the source-faithful window and shared
  \`readCount\`, for arbitrary genome and read length.
- \`OrientedVariableLengthSe62\`: its length-three oriented window agrees
  for **every** positive genome length, including the 5-versus-6 witness.

Two remaining independent read-window interfaces are not definitionally
identical: \`GenomeOrbitAdapter\` indexes starts by \`ZMod G\` (rather
than \`Fin G\`), and \`Section62CircularWindowAdapter\` spells list-based
overlap-graph walks, including physical reverse-complement conventions.
They require their own proved equivalences and are not assertions about the
generic oriented iid law. They are kept distinct, as are physical molecule
classes and signed bidirected flow domains.

## Headline theorem navigation

[Headlines.lean](../AssemblyP1/Headlines.lean) imports and re-exports the
checked endpoints of the paper's central oriented positive and negative
theorems. These declarations keep the complete hypotheses of the underlying
theorems, including P2 admissibility of *every* competitor and the
truth's additional candidacy assumption in the same-length theorem.
The historical interpretations and independent computations remain
paper-level claims or source facts; they are never exported as Lean theorems.

## Audit of old root-level research files

The main `lakefile.lean` builds the `AssemblyP1` subtree and not
standalone root `AxiomAudit*.lean` files or scratch directories. These
paths were audited before proposing deletion; absence from that build does
**not** imply they are disposable.

| Path(s) | Evidence and disposition |
|---|---|
| `AxiomAudit257.lean`, `AxiomAudit271.lean` | Referenced in research notes, and in the latter case an in-tree Lean module. **Preserve**. |
| `scratch94/`, `scratch257/`, `scratch261/`, `audit94/` | Referenced by notes and some compiled-module source comments. **Preserve** historical proof provenance. |
| `AxiomAudit211.lean`, `AxiomAudit300.lean` | Standalone, auditable axiom listings; the latter names still-current short-read witnesses. **Preserve** as independent checks even though excluded from the library glob. |
| `scratch247c/Audit.lean`, `scratch260/Audit.lean` | Tiny, historical model/witness audits; no direct path references in the searched sources. **Preserve** to avoid silently erasing historical evidence; moving is optional only with links/history retained. |
| `acceptance-shots/` | UI acceptance screenshots rather than theorem modules. **Preserve** as visual regression artifacts; not expected to be built by Lean. |

The audit searched 432 source, documentation, and script files for literal
path references. This is **not** a transitive proof of reachability or
obsolescence; it is intentionally insufficient evidence for destructive
cleanup. No path is deleted by this change.

To verify: `lake build AssemblyP1.ExactReadLikelihoodAdapters
AssemblyP1.Headlines`, then the repository's standard `lake build --wfail`,
kernel replay, and axiom audit.
