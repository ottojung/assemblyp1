# #89: the P2 / Ukkonen complete-spectrum uniqueness theorem

This note records the state of the one step that
`paper/sections/05-population.tex` (`thm:BBT`) takes from
Bresler--Bresler--Tse and that `AssemblyP1.PopulationUniqueness` still takes
as a caller-supplied premise (`hBBTS`, `hBBTD`).

Everything below is on the **current `main`** state of the library (the branch
`agent/issue89-spectrum-uniq` at `001039d` + this work), where
`AssemblyP1.P2.lean` does not yet exist and the old `PopulationUniqueness`
takes the uniqueness implication as a parameter.

## 1. What is now kernel-checked

New module: `AssemblyP1/P2SpectrumUniqueness.lean`. No `axiom`, `sorry` or
`admit`; `lake build` is clean.

| name | statement | premise |
| --- | --- | --- |
| `P2`, `Ukkonen`, `mkGenome` | the actual `def:P1P2` and `thm:BBT` conditions, stated through `SourceFaithfulIs.IsTripleRepeat` / `IsRepeat` / `Interleaved` | – |
| `P2.imp_Ukkonen` | P2 at `L` implies Ukkonen at `K = L - 1` (the paper's alignment sentence) | none |
| `EulerCircuit` | a cyclic closed trail in the `(L-1)`-de Bruijn graph with prescribed edge multiplicities (concrete: `winPrefix`/`winSuffix`, `Finset.filter … .card`) | – |
| `TrailEquiv` | cyclic shift of a trail | – |
| `window_isEulerCircuit` | the `L`-windows of a circular word form an Eulerian circuit of its `L`-spectrum | none |
| `rotEquiv_of_trailEquiv` | shift-equivalent window trails ⟹ rotation-equivalent words | none |
| `P1`, `P1.node_injective` | no length-`(L-1)` word occurs more than once ⟹ the node map of `S` is injective | none |
| **`p1_spectrum_unique_up_to_rotation`** | **`P1` + equal complete `L`-spectrum + same length ⟹ `RotEquiv`** | **none** |
| `nodeWindow_eq_of_agree`, `nodeCount_ge_two` | agreeing starts with `L-1 ≤ e` share their `(L-1)`-window; two distinct such starts force node multiplicity `≥ 2` | none |
| **`P1.imp_P2`** | **P1 implies P2** (the paper's "P1 is stronger than P2"), kernel-checked | none |
| `p2_of_p1_spectrum_unique_up_to_rotation` | the `P1` sub-case phrased in the actual P2 language | none |
| `UniqueEulerCircuit` | the multigraph of `c` has a single Eulerian circuit up to shift | – |
| `NodeCrossing` | the occurrence pairs of doubly-occurring `(L-1)`-mers do not interleave (concrete, decidable) — **not** a consequence of `P2`; see §3 and `cex_not_NodeCrossing` | – |
| `p2_spectrum_unique_up_to_rotation` | primitive P2 truth + equal complete `L`-spectrum + same length ⟹ `RotEquiv` | `hUnique : UniqueEulerCircuit …` |

### 1b. Also kernel-checked: the (R1)/(R2) genome side, with two corrections

New module: `AssemblyP1/P2RepeatResidual.lean`. No `axiom`, `sorry` or `admit`.

| name | statement | premise |
| --- | --- | --- |
| `IsPrimitive.shiftPrimitive` | the `_hPrimS` of `p2_spectrum_unique_up_to_rotation` (`PopulationReduction.IsPrimitive`, "not a nontrivial power") implies the shift-invariance primitivity `RepeatAdapter.IsPrimitive` that the repeat theory needs (Euclidean reduction `s ↦ G mod s`) | – |
| `isTripleRepeat_of_maximalTriple` | `RepeatAdapter.IsMaximalTriple` at `ℕ`-starts *is* a source-faithful `Genome.IsTripleRepeat` at the residues | – |
| `P2.imp_noLongTripleRepeat` | **actual `P2` ⟹ `¬ HasLongTripleRepeat` at `L`** (clause 1 of `def:P1P2`, no primitivity needed) | – |
| `P2.imp_nodeCount_le_two` | **actual `P2` + primitivity ⟹ every `(L-1)`-mer occurs at most twice**, i.e. every node of the `(L-1)`-de Bruijn multigraph has multiplicity `≤ 2` | primitivity |
| `maxPair_isRepeat` | **(R1) for `n = 2`**: two distinct agreeing starts on a primitive circle extend to a `Genome.IsRepeat` of length `e` with `ℓ ≤ e < G`, at the **shifted** starts | primitivity |
| `ExtCrossing` | the corrected (R2b): the maximal extensions of two interleaving double-node pairs do not interleave | – |
| `P2.imp_ExtCrossing` | **actual `P2` + primitivity ⟹ `ExtCrossing`** | primitivity |
| `P2.imp_nodeCount_le_two_of_powerPrimitive`, `P2.imp_ExtCrossing_of_powerPrimitive` | the same two consequences under the primitivity actually carried by `p2_spectrum_unique_up_to_rotation` | – |
| `cex_is_shiftPrimitive`, `cex_is_p2`, `cex_not_NodeCrossing`, `cex_pair_agrees`, `cex_not_maximalRepeat_at_same_starts` | the counterexample of §3 below, on `S = AABAB`, `G = 5`, `L = 3` | – |

**The residual (R1) and (R2) as written in §3 are false, and the module proves
the corrected versions instead of the stated ones.** Both failures come from the
same wrong step — that a maximal extension stays at the selected starts.

`P1.imp_P2` matters for the status claim: because P1 is *proved* to imply the
repository's actual `P2`, the premise-free theorem above applies to a subclass
of the `P2` class itself, and is not a statement about a different condition.
Its proof uses no maximal-extension argument: a maximal repeat (or maximal
triple repeat) of length `≥ L - 1` has its two (or three) selected starts
carrying the same `(L-1)`-window, which `P1` forbids.

`p1_spectrum_unique_up_to_rotation` is a **fully proved, premise-free**
complete-spectrum uniqueness theorem: for circular genomes of the same
length, no repeated `(L-1)`-mer on the truth plus equality of the complete
oriented length-`L` spectrum forces rotation equivalence. This is the
"no repeat of length `≥ K`" case of the Bresler uniqueness theorem at
`K = L - 1`, i.e. the classical `P1` regime, and it is *not* a retreat to the
caller-supplied `hBBT` of `OrientedFinalRigidity`: no uniqueness premise
appears in its statement.

`p2_spectrum_unique_up_to_rotation` is exactly `thm:BBT` at `K = L - 1` minus
the multigraph lemma. The only remaining premise is a statement about a
multigraph, not about genomes, spectra or repeats.

## 2. The exact residual lemma

```lean
def UniqueEulerCircuit (hG : 0 < G) (c : (Fin L → α) → ℕ) (T : Fin G → Fin L → α) : Prop :=
  EulerCircuit hG c T ∧ ∀ U, EulerCircuit hG c U → TrailEquiv hG U T
```

with

```lean
def EulerCircuit (hG : 0 < G) (c : (Fin L → α) → ℕ) (T : Fin G → Fin L → α) : Prop :=
  (∀ j : Fin G, winSuffix (T j) = winPrefix (T ⟨(j.val + 1) % G, _⟩))
    ∧ (∀ w : Fin L → α, (Finset.univ.filter (fun j : Fin G => T j = w)).card = c w)
```

This is the paper's "the `K`-mer graph has a unique Eulerian cycle, which
spells the genome up to cyclic rotation", with the graph given explicitly
(vertices `Fin (L-1) → α`, edges `Fin L → α`, edge multiplicity `c`, edge
`w` running from `winPrefix w` to `winSuffix w`) and with the second half of
the sentence proved: a cyclic Eulerian trail is a cyclic shift of the truth's
window trail, and that is rotation equivalence of the genomes
(`rotEquiv_of_trailEquiv`). It is not a restatement of "equal spectrum
implies rotation": it mentions neither `specCount`, nor `RotEquiv`, nor any
repeat predicate.

**It is not proved here.** Closing it for the P2 hypothesis needs the three
sub-lemmas of §3, which together are a substantial repeat-theoretic plus
multigraph development; this note and the module give the exact statements.

## 3. The three missing sub-lemmas, precisely

Write `K = L - 1`, `V = Fin (L-1) → α`, `E = Fin L → α`, and for a circular
word `S` let `m_S v = nodeCount hG S v` be the number of starts whose `(L-1)`
window is `v` (the in-degree = out-degree of `v` in the multigraph).

**(R1) Simultaneous maximal extension (repeat theory). — CORRECTED.** As
written, this said "there are `E` and **the same starts**". That is false, and
the corrected statement is the one proved in `AssemblyP1.P2RepeatResidual.lean`.
If `S` is primitive (minimal period `G`), `1 ≤ ℓ ≤ G`, and starts `a ≠ b` carry
a common `ℓ`-window, then there are `E`, `β` and shifted starts
`a' ≡ a + G - β`, `b' ≡ b + G - β` (`0 ≤ β ≤ G`) with

* `ℓ ≤ E < G`, all the `E`-windows at `a'`, `b'` equal,
* the two symbols preceding the copies differ,
* the two symbols following the copies differ,

i.e. exactly `Genome.IsRepeat E a' b'`. Construction (`pairBack`, `pairFwd`):
take the maximum `β ≤ G` for which the *nested blocks*
`[a + G - β, a + G)` and `[b + G - β, b + G)` agree, then the maximum `γ ≤ G`
for which `[a', a' + γ)` and `[b', b' + γ)` agree, and take `E = γ`; the two
maximality conditions are the one-step failures at `a' - 1` and at `a' + γ`.
Primitivity is needed exactly to know the maxima are `< G`: agreement on `G`
consecutive positions at two distinct residues is a shift invariance.

For `n = 3`, the same conclusion (a source-faithful `Genome.IsTripleRepeat` of
length `≥ ℓ`) is what `RepeatAdapter.extend_triple` already constructs at
shifted starts; `isTripleRepeat_of_maximalTriple` proves that its `ℕ`-start
formulation is the same predicate as the source-faithful one, which is all
that was missing to feed it to `P2`.

**The "same starts" version is false.** Kernel-checked
(`cex_not_maximalRepeat_at_same_starts`): on the primitive word
`S = AABAB` (`G = 5`) at `L = 3`, the starts `2, 4` carry the common `2`-mer
`10` (`cex_pair_agrees`), but no `e` with `2 ≤ e < 5` makes them a maximal
repeat: they are preceded by the same symbol, so the pair is never
left-maximal at those starts.

**(R2) From P2 to the graph hypotheses.**

* **PROVED** (`P2.imp_nodeCount_le_two`): `P2` (clause 1, no triple repeat of
  length `≥ L-1`) + primitivity gives `∀ v, m_S v ≤ 2` for **all** `(L-1)`-mers,
  not just those in the node set. Three starts with the same `(L-1)`-window
  would produce a maximal triple repeat of length `≥ L-1`.
* **CORRECTED** (`ExtCrossing`, `P2.imp_ExtCrossing`): `P2` (clause 2) + (R1)
  with `n = 2` does **not** give `NodeCrossing`. It gives that the *maximal
  extensions* of the two pairs do not interleave: if `a ≠ b` and `c ≠ d` each
  carry a common `(L-1)`-mer and `Interleaved a b c d`, then `E`-maximal repeats
  at the two *shifted* pairs have lengths `≥ L-1 > L-2`, so clause 2 forbids
  `Interleaved` of the four extended starts (in either ordering of the first
  pair). `NodeCrossing` itself — about the *unshifted* occurrence pairs — is
  **false for `P2`**.

  Kernel-checked counterexample (`cex_not_NodeCrossing`): `S = AABAB`, `G = 5`,
  `L = 3` satisfies actual `P2` (`cex_is_p2`; its only repeated `2`-mers are `01`
  at starts `1, 3` and `10` at starts `2, 4`, so there is no maximal triple
  repeat of length `≥ 2` at all, and neither pair is a maximal repeat, so clause
  2 is vacuous), yet the two occurrence pairs interleave:
  `Interleaved 1 3 2 4`. This is the smallest such example over primitive
  circular words.

  Numerical support for the correction (primitive binary words, `4 ≤ G ≤ 10`,
  all `2 ≤ L ≤ G`): 4838 interleaving double-node configurations, 2534 of them
  on `P2` words; 1320 configurations have interleaving *maximal extensions*, and
  **0** of those lies on a `P2` word.

**(R3) The multigraph combinatorics.** If `S` is primitive, every node has
`m_S v ≤ 2`, and the occurrence pairs of the double nodes are pairwise
non-interleaved, then `UniqueEulerCircuit hG (specCount hG S) (window hG S)`.

Proof route (verified numerically, see §4): at a node with `m v = 1` the
successor edge is forced; at a node with `m v = 2` the traversal induces one of
two bijections between the two in-copies and the two out-copies, and a valid
(bijection) choice is one that makes the deterministic traversal a single
cycle. A choice differing from the truth's on a set `X` of double nodes is
valid iff the "flip set" is consistent; if no two double nodes interleave the
chords are laminar, and each additional flip strictly increases the number of
cycles, so only the empty `X` is valid and the circuit is unique up to shift.
The interference case (interleaved double nodes) is exactly what clause 2 of
`P2` forbids, which is why the P2 condition (and not merely `P1`) is the
correct hypothesis.

`p2_spectrum_unique_up_to_rotation` follows from (R2) + (R3) with no further
work: `P2.imp_Ukkonen` is already proved, and the two genome directions are
already proved.

## 4. Evidence that P2 at `L` really does suffice

Exhaustive search over circular words up to rotation, grouped by the complete
length-`L` spectrum (occurrence counts). A fiber with two rotation classes is a
genuine ambiguity (two distinct circular words of the same length with the
same complete `L`-spectrum). For each ambiguous fiber we test whether some
member is primitive and satisfies the repository's P2 at that `L`.

| search | ambiguous fibers | with a primitive P2 member |
| --- | --- | --- |
| `|Σ| ≤ 3`, `L ≤ 5`, `|S| ≤ 11` | 10208 | **0** |
| `|Σ| ≤ 4`, `L ≤ 4`, `|S| ≤ 11` | 157878 | **0** |
| `|Σ| ≤ 5`, `L ≤ 3`, `|S| ≤ 9` | 93003 | **0** |
| `|Σ| = 2`, `L ≤ 8`, `|S| ≤ 16` | 6071 | **0** |

So P2 at `L` is not refuted anywhere in this range, and the ambiguity is
frequent without it (e.g. 157878 ambiguous fibers over `|Σ| ≤ 4`, `L ≤ 4`),
which is exactly why the repeat condition is doing real work. This is finite
evidence, not a proof; it is recorded as evidence only.

The same probes confirm the two maximal-extension statements used in (R1): for
primitive circular words with `|Σ| ≤ 3`, `|S| ≤ 11` and `K ≤ 4`, there is no
counterexample to "three occurrences of a `K`-mer give a maximal triple repeat
of length `≥ K`", nor to the two-occurrence version. (Zero failures.)

Probe scripts: kept out of the library; they are pure Python over
`itertools.product` with the P2 test transcribed from
`AssemblyP1.SourceFaithfulIs`.

## 4b. (R3) as a genome-side statement, and what it still needs

New module: `AssemblyP1/P2EulerAdapter.lean`.  It removes the multigraph layer
from the (R3) residual and proves the transfer to it.

**The transfer, kernel-checked.**  The classical route matches the two
traversals of the `(L-1)`-de Bruijn multigraph start by start and needs a
*bijection* of the starts.  That is unnecessary: equal complete `L`-spectra give
a *choice* `τ : Fin G → Fin G` with `window S (τ j) = window E j`
(`exists_startChoice`), and for such a choice the node-step condition

```text
nodeWindow hG L S (τ j + 1) = nodeWindow hG L S (τ (j + 1))
```

is **automatic** (`nodeStep_of_choice`): both sides are the `(L-1)`-suffix of
the same length-`L` read type.  Also `E j = S (τ j)` (`symbol_of_choice`).  So
the whole spectrum-to-traversal step is proved with no premise and no bijectivity.

**The exact residual.**  `NodeStepUnique hG L S` says: every map of the starts
satisfying `NodeStep` spells the truth up to cyclic shift.  It mentions only
`nodeWindow`, `Fin G` and the successor map.  `p2_of_nodeStepUnique` proves

```text
specCount hG L S = specCount hG L E  ->  NodeStepUnique hG L S  ->  RotEquiv hG E S
```

so `NodeStepUnique` **replaces** the `hUnique : UniqueEulerCircuit …` premise of
§2's `p2_spectrum_unique_up_to_rotation` by a single decidable combinatorial
statement about the truth alone: no `EulerCircuit`, no `TrailEquiv`, no
multigraph, no `UniqueEulerCircuit`, no `specCount`, no BBT/Ukkonen premise.

**Which hypothesis `NodeStepUnique` needs — kernel-checked.**  It cannot be
derived from "node multiplicity `≤ 2`" alone.  With `G = 6`, `L = 3`,
`S = 0 0 1 0 1 1` and `E = 0 0 1 1 0 1`:

| fact | name |
| --- | --- |
| every length-`2` word of `S` occurs at most twice | `cex_nodeCount_le_two` |
| `S` and `E` have the same complete length-`3` spectrum | `cex_spec` |
| `E` is not a cyclic shift of `S` | `cex_not_rotEquiv` |
| the only maximal repeats of length `≥ L - 1 = 2` are at starts `1, 3` and `2, 5` | `cex_interleaved_long_repeats` |
| those two pairs interleave, so `S` is not `P2` at `L = 3` | `cex_not_p2` |

So the two traversals of the multigraph are separated by exactly one interleaved
pair of **maximal repeats** of length `≥ L - 1`, i.e. by clause 2 of `P2`.
`noInterleavedLongRepeat` is clause 2 in exactly the form the (R3) combinatorics
consumes: it ranges over `SourceFaithfulIs.Genome.IsRepeat` (maximal on *both*
sides) and **not** over the un-extended node pairs, which §3(R2) shows is false
for `P2`.  Note that this is the maximal-repeat form, not `ExtCrossing`: the two
are consequences of the same clause, but they are stated on different starts
(`ExtCrossing` is about the shifted starts of `maxPair_isRepeat`), and the
counterexample above shows the *unshifted* version is false.

**`NodeStepUnique` is not proved.**  The remaining step is the (R3)
combinatorial theorem: for a primitive `P2` truth whose `(L-1)`-mers each occur
at most twice, every `NodeStep` map is a rotation up to the truth's symbols.
The table above shows this is a genuine statement and identifies the hypothesis
it must use; it is the laminar-chord / block-coherence argument of §3(R3) and
`docs/bbt-chord-rematch-89.md` §4, and it is not attempted in this packet.

## 5. Honest status

* Closed in the kernel: the P1 complete-spectrum uniqueness theorem, the
  P2 ⟹ Ukkonen alignment, the genome ⟺ Eulerian-circuit translation, and the
  reduction of the P2 statement to `UniqueEulerCircuit`.
* Closed in the kernel since `agent/issue89-repeat-adapter`: the genome-side
  (R1) (`maxPair_isRepeat`, plus the `n = 3` bridge) and (R2) (`P2` ⟹ node
  multiplicity `≤ 2`, `P2` ⟹ `ExtCrossing`), together with kernel-checked
  counterexamples showing that the (R1)/(R2) statements of §3 as previously
  written are false, and the corrected `ExtCrossing` that replaces
  `NodeCrossing` for the chord worker.
* Closed in the kernel since this packet: the spectrum-to-traversal transfer
  (no bijectivity needed), and the reduction of the (R3) residual to
  `NodeStepUnique` — a genome-side statement with no multigraph, no
  `UniqueEulerCircuit` and no BBT premise — together with a kernel-checked
  instance showing node multiplicity `≤ 2` is insufficient and that clause 2
  (in maximal-repeat form) is the load-bearing hypothesis.
* **Not** closed: `NodeStepUnique` for a `P2` truth, i.e. the combinatorial
  core of (R3). Consequently `p2_spectrum_unique_up_to_rotation` still takes
  `hUnique`, and the `PopulationUniqueness` chain still takes
  `hBBTS`/`hBBTD`; but the residual is now a single decidable statement about
  `nodeWindow` alone, with the exact hypothesis it needs identified and
  separated by a kernel-checked counterexample.
* No `axiom`, `sorry` or `admit` was introduced; nothing in the library was
  weakened to make a theorem provable; the P1 theorem is a proved sub-case,
  not a replacement of the P2 statement by a weaker one.
* Scope, as in the paper: the oriented single-strand spectrum model only.
