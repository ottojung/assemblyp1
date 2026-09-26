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
| `UniqueEulerCircuit` | the multigraph of `c` has a single Eulerian circuit up to shift | – |
| `NodeCrossing` | the occurrence pairs of doubly-occurring `(L-1)`-mers do not interleave (concrete, decidable) | – |
| `p2_spectrum_unique_up_to_rotation` | primitive P2 truth + equal complete `L`-spectrum + same length ⟹ `RotEquiv` | `hUnique : UniqueEulerCircuit …` |

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

**(R1) Simultaneous maximal extension (repeat theory).** If `S` is primitive,
`1 ≤ e₀ < G`, and starts `r₁, …, rₙ` (`n ∈ {2, 3}`, pairwise distinct) carry a
common `e₀`-window, then there are `E` and the same starts with

* `e₀ ≤ E < G`, all the `E`-windows at the starts equal,
* the `n` symbols preceding the copies are not all equal,
* the `n` symbols following the copies are not all equal.

This is exactly `Genome.IsRepeat` (`n = 2`) and `Genome.IsTripleRepeat`
(`n = 3`) at length `E`. The construction is the one in the `Q1`/`Q2` probes:
shift the common window one step left, take the maximum `e` for which the
shifted family still agrees, and use maximality for both maximality
conditions. Primitivity is needed exactly to know the maximum is `< G`: a
family agreeing on `G-1` or more positions forces two of the starts to
coincide.

**(R2) From P2 to the graph hypotheses.**

* `P2` (clause 1, no triple repeat of length `≥ K`) + (R1) with `n = 3` gives
  `∀ v, m_S v ≤ 2`: three starts with the same `(L-1)`-window would produce a
  maximal triple repeat of length `≥ L-1`.
* `P2` (clause 2) + (R1) with `n = 2` gives `NodeCrossing`: if `m_S u = 2` and
  `m_S v = 2` at starts `a, b` and `c, d`, the corresponding maximal repeats
  have lengths `≥ K = L-1 > L-2`, so clause 2 forbids `Interleaved a b c d`.

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

## 5. Honest status

* Closed in the kernel: the P1 complete-spectrum uniqueness theorem, the
  P2 ⟹ Ukkonen alignment, the genome ⟺ Eulerian-circuit translation, and the
  reduction of the P2 statement to `UniqueEulerCircuit`.
* **Not** closed: `UniqueEulerCircuit` under the P2 hypothesis, i.e. (R1),
  (R2), (R3) of §3. Consequently
  `p2_spectrum_unique_up_to_rotation` still takes `hUnique`, and the
  `PopulationUniqueness` chain on `main` still takes `hBBTS`/`hBBTD`.
* No `axiom`, `sorry` or `admit` was introduced; nothing in the library was
  weakened to make a theorem provable; the P1 theorem is a proved sub-case,
  not a replacement of the P2 statement by a weaker one.
* Scope, as in the paper: the oriented single-strand spectrum model only.
