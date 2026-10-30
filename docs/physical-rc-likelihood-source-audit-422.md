# Physical reverse-complement molecule likelihood: source-faithful audit (#422)

_Status: audit + precise boundaries, paper-level; not a new Lean theorem._

## Scope of the audit
This note audits MB09/source conventions relevant to issue #422:
- read orientation and strand identity,
- parallel matches / multiple overlaps of the same class,
- palindrome classes,
- transitive reduction,
- actual candidate restrictions (support/lower bounds),
against existing `AssemblyP1/Section62*` statements. It distinguishes oriented
and physical (reverse-complement molecule) read laws.

## Conventions (source facts)
- MB09 §1.1/§3.1/§4.1/§6.2: a read is a DNA molecule (unordered RC pair);
  each read/molecule is a vertex once; the objective indexes molecule classes
  (see `docs/source-notes/mb09-se61-index-orientation-resolution.md`).
- The §6.1 formula's literal `4^k` is the oriented alphabet count but the
  model wiring is molecular; the operative index set is molecule classes.
- Palindromes: a self-complementary molecule class has one representative word
  but represents two physical strands; naive list enumeration can alias
  incidences (repaired in `AssemblyP1/Section62OrientedStrandFlow.lean` by
  explicit orientation tags). See `docs/issue261-oriented-strand-source-model.md`.
- Parallel overlaps/matches: genuine parallel edges can arise; reduction
  rules (transitive reduction) must be applied as specified; see
  `docs/edge-type-obligation-94.md`, `docs/section62-mb09-bidirected-graph-audit.md`.
- Candidate restrictions: in the §6.2 molecule reading, vertices present
  as observed reads carry lower bound `1`; support equality is not the
  general §6.2 feasibility definition but is the equal-support/candidate-class
  restriction relevant to some comparisons (see
  `AssemblyP1/FullOverlapMoleculeML.lean`).

## What is not the same: oriented vs physical/RC-collapsed
- Oriented read strings form a different observable than RC molecule classes
  (collapse is not injective). See `AssemblyP1/W1W2RcOrientedRepresentation271.lean`.
- Population uniqueness under oriented P2 does **not** transfer to the
  strand-collapsed molecule class law in general.
- The `AAATAT → AAAAAT` counterexample is valid in the molecule class
  reading under the stated hypotheses; transferring to other strand
  conventions requires explicit source correspondence (see
  `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`).

## Precise counterexample (strand-collapsed)
For every $L\ge2$, $S_L=\texttt{A}^L\texttt{C}\texttt{T}^{L-1}$, $D_L=\texttt{A}^L\texttt{G}\texttt{T}^{L-1}$
are primitive, satisfy P2 at length $L$, dihedrally inequivalent, but have identical
length-$L$ reverse-complement class laws. Proof/verification: `docs/rc-p2-molecule-ambiguity.md`,
`scripts/verify_rc_p2_ambiguity.py` (L=2..12 PASS). This is a paper-level
result, not Lean formalized; it does **not** identify this law with the full
MB09 bidirected physical likelihood without a verified transport theorem.
No claim of oriented=physical equivalence is made.

## Graph reduction / parallel matches / palindromes
- Transitive reduction: behavior depends on reading (maximal overlap vs
  path-of-shorter/longer overlaps); see MB09 audit. Not all reductions are
  equivalent in general.
- Parallel matches/edges can occur; orbit counting must respect physical
  identity (see `AssemblyP1/Section62OrientedStrandFlow.lean` ATAT witness,
  `AssemblyP1/Section62PhysicalEdgeOrbit.lean`).
- Palindromes create aliasing in naive oriented enumerations; use tagged
  orientations to preserve physical incidences.

## Remaining open questions (#422)
1. Exact correspondence between the strand-collapsed class law above and
   the full physical MB09 molecule likelihood (including vertex lower bounds,
   transitive reduction, circuit/spelling constraints) for P2 or general cases.
2. When parallel matches/palindromes interact with transitive reduction,
   does the physical likelihood coincide with oriented surrogates?
3. Precise candidate restrictions under which the collapsed law is
   well-posed (support conditions, genome equivalence classes).
4. Find Lean-checked small witnesses where useful, without inferring
   oriented=physical equivalence.

## Verification
- `python3 scripts/verify_rc_p2_ambiguity.py` (PASS)
- Related audits: `docs/rc-p2-molecule-ambiguity.md`,
  `docs/source-notes/mb09-se61-index-orientation-resolution.md`,
  `docs/section62-mb09-bidirected-graph-audit.md`,
  `docs/source-notes/oriented-to-double-strand-bridging-transfer-2026-10-09.md`


## Precise correspondence analysis (historical MB09)
### Molecule indexing vs oriented display
- **Source (§6.1):** the multinomial displays variables indexed up to $4^k$ and writes $d_1,\ldots,d_{4^k}$; the text says “there are $4^k$ such variables”. 
- **Source (§1.1,§3.1,§4.1,§6.2):** reads are DNA molecules (unordered RC pairs), each read/molecule is a vertex once, $d_i$ is the flow/value through vertex $i$ (molecule). 
- **Resolution:** the operative index set is molecule classes (vertices). The $4^k$ is the oriented alphabet size of the predecessor/oriented display; the molecular wiring is what determines the actual model. (See `docs/source-notes/mb09-se61-index-orientation-resolution.md`.)

### Candidate restrictions (MB09 §6.2)
- **Vertex lower bound:** “Each vertex has a lower bound of 1 since it represents a read that must be present in the genome at least once.” Other bounds 0/∞; edges from/to supersource/sink carry large cost. 
- **Flow/circuit:** the genome corresponds to a circuit/walk; $d_i$ are vertex throughputs (Observation 7). 
- **Support/equality:** support-equality $x\!\le\! d$ componentwise with same support is a *sufficient* finite certificate in some comparisons but not the general §6.2 feasibility definition. `AssemblyP1/FullOverlapMoleculeML.lean` treats the equal-support/candidate-class restriction as a case; general feasibility is bidirected flow feasibility on the transitively reduced graph.

### Palindromes
- A self-complementary molecule class has one vertex/orbit representative but represents two physical strands. Naive oriented enumeration aliases incidences. 
- **Consequence:** departure/throughput counting must be orbit/invariance-aware. `AssemblyP1/Section62OrientedStrandFlow.lean` uses explicit orientation tags; `AssemblyP1/Section62PhysicalEdgeOrbit.lean` shows inherited departure throughput on oriented representatives is not physically faithful for palindromes (e.g. ATAT gives orbit count 3 but naive departure counting gives throughput 2) — physical throughput must come from half-incidences/orbit structure, not oriented-departure surrogates.

### Parallel matches/edges
- Genuine parallel overlaps/edges can arise (same endpoints/classes in different overlap relations) and must not be identified by reversal alone if they differ in other properties; quotienting by RC reversal must preserve distinct parallel cases. `Section62PhysicalEdgeOrbit` notes $\mathrm{RevRel}$ only identifies an edge with its own reverseEdge (preserving length) so genuinely distinct parallel overlaps are not identified.
- Transitive reduction interacts with parallel/overlap structure; different reduction readings are not obviously equivalent.

### Transitive reduction
- MB09 §6.2 performs transitive edge reduction (“remove any overlap that is spelled by two shorter overlaps”). 
- Audits (`docs/section62-mb09-bidirected-graph-audit.md`, `Section62Reduction*`, `Section62GlobalSpellingPreservation.lean`) show reduction behavior depends on reading and that spelling-preservation/transport is nontrivial; not all reduction policies are equivalent in general.

### Likelihood correspondence
- Under the molecule (§6.2) reading with external $N$ and vertex lower bounds as in §6.1’s separable/binomial approximation, the natural objective is over molecule classes/vertices (the “global read-count likelihood” in molecule form). 
- The strand-collapsed RC class law is exactly this molecule-class observation space. However, **identity of the class-law distributions across genomes is not sufficient to conclude identity of the full physical MB09 likelihood values under all candidate restrictions and reduction policies** — feasibility (support/lower bounds, spelling/circuit constraints, reduction effects) and palindrome/orbit/parallel details can break transfer.
- The P2+RC-class ambiguity family ($S_L=A^L C T^{L-1}, D_L=A^L G T^{L-1}$) gives identical RC-class laws and both satisfy P2; whether they remain tied or become distinguishable under the full §6.2 molecule likelihood with exact constraints is the transport question (open). No oriented=physical equivalence is asserted.

## Small precise claims (checkable)
1. **Molecule indexing:** operative domain is RC/molecule classes, not oriented $4^k$ atoms as independent vertices. (Source-supported.)
2. **Palindrome orbit:** physical throughput for self-complementary classes requires orbit/half-incidence counting (naive oriented departure counting is not faithful). (Kernel-checked by `Section62PhysicalEdgeOrbit.lean` ATAT witness.)
3. **Parallel edges:** RC reversal quotient must not conflate genuinely distinct parallel overlaps. (Stated in `Section62PhysicalEdgeOrbit.lean`.)
4. **Reduction dependence:** transitive reduction is policy-dependent; spelling/flow transport is not automatic. (Documented in audits.)
5. **Collapsed-class ambiguity is necessary but not obviously sufficient to transfer:** identical RC-class spectra do not by themselves force identical §6.2 flow likelihoods across all feasible candidates under all reduction policies — candidate restrictions and structural constraints may separate them. (Conjectural/needs case analysis.)

## Counterexample status
- **RC-class P2 ambiguity:** primitive-P2 genomes with identical length-$L$ RC-class laws exist for all $L\ge2$ (paper-level proof + `scripts/verify_rc_p2_ambiguity.py` PASS). This is *not* shown to be a counterexample to the full physical MB09 §6.2 molecule likelihood — correspondence remains unverified. 
- **MB09 §6.2 bridging counterexamples:** separate finite witnesses exist in the molecule/§6.2 bidirected flow setting (e.g. `Section62BridgingCounterexample.lean`) under stated hypotheses; they concern the bridging/likelihood comparison under §6.2 feasibility, different from the pure class-law indistinguishability question.
