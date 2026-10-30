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

## Notes on exact correspondence points (source-faithful reading)
- **Molecule indexing (not oriented).** Per MB09 §6.1/§6.2 and the source notes, the operative index set is observed read molecules / k-molecule classes (one vertex per read molecule). The literal `4^k` in §6.1 is the oriented alphabet count of the multinomial display but is not consistent with "vertices are reads/molecules"; the molecule wiring is the operative one.
- **Support/lower bounds.** In the §6.2 molecule reading, vertices present as observed reads carry lower bound `1`. The equal-support candidate restriction is the case treated in `AssemblyP1/FullOverlapMoleculeML.lean` (not the general feasibility definition for all candidates in all readings). 
- **Transitive reduction.** MB09 §6.2 states "we then perform transitive edge reduction..." The behavior depends on reading (maximal overlap vs path of shorter/longer overlaps / spelling-preserving). Our codebase models multiple readings (`Section62BidirectedFlow`, `Section62SpellingReductionCandidate`, etc.) and treats transport across reduction as open in general.
- **Palindromes and parallel edges.** Palindromes create orbit aliasing if not handled carefully; parallel matches can occur. The orbit-based treatment in `AssemblyP1/Section62PhysicalEdgeOrbit.lean` (and tagged orientations in `Section62OrientedStrandFlow.lean`) shows that naive departure counting on oriented representatives is not physically faithful.
- **No automatic transfer.** The strand-collapsed RC class law is strictly weaker/structurally different from oriented iid laws. The P2 counterexample family above shows primitive-P2 uniqueness fails for the collapsed class law; this does not imply failure of the full bidirected physical likelihood without a verified transport theorem showing the class law matches that likelihood under the exact model constraints (support, reduction, spelling/circuit constraints).

## Concrete next steps (narrow, verifiable)
1. **Model specification:** Write a precise definition of "full physical MB09 molecule likelihood" (reads = molecule classes/vertices with lower bounds, sampling/model for molecules, handling of palindromes, reduction policy) and state assumptions explicitly. Do not guess.
2. **Transport lemma candidates:** Under exact equal-support + spelling-preserving reduction assumptions, can the class-law ambiguity appear? Or is it ruled out? Need careful analysis.
3. **Witness search:** If correspondence holds under some restrictive policy, find a small counterexample in that exact model; if it fails under source constraints, prove it.
