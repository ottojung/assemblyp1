# A same-length per-occurrence counterexample on the real DNA alphabet: `ATATACAC → ATACACAC`

_Status: independent from-scratch computation + kernel-checked finite
certificate, 2026-10-09. Front #217 integrated the evidence produced by leaf
#212 (agent `cedd79adfeae`, registered worktree
`/workspace/assemblyp1-finite-212`). All claims are labelled **source fact**,
**source-supported inference**, **editorial choice**, **mathematical argument**,
**verified computation**, **kernel-checked**, or **open**._

_Reproduction:_

```sh
python3 scripts/verify_peroccurrence_dna_samelength_212.py           # witness
python3 scripts/verify_peroccurrence_dna_samelength_212.py --search  # + bounded census
lake build AssemblyP1.PerOccurrenceSameLengthCounterexample
```

_The Python script is self-contained (standard library only: `fractions`,
`itertools`, `collections`, `math` — it imports nothing from this repository),
exact (`fractions.Fraction`), deterministic, and exits non-zero on any failed
assertion. The Lean module contains no `sorry`, `axiom`, `admit`, or
`native_decide`; its endpoint theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`._

---

## 0. Verdict at a glance

This note resolves row **R13** of
[`source-notes/interpretation-matrix-217.md`](source-notes/interpretation-matrix-217.md),
the only determinate row that was open on `main`: molecule read types,
same-length candidates, under the **per-occurrence strengthening** `Focc` of the
§6.2 candidate rule. R13 is **FALSE**.

The strengthened statement

> **(P_occ)** `I_s` holds **and** the truth is a per-occurrence-feasible MB09
> §6.2 spelled candidate **and** the competitor is a spelled molecule `D` with
> `|D| = |S|` that is also per-occurrence feasible ⇒ the truth maximizes the
> likelihood,

fails. The witness is

```text
alphabet          {A, C, G, T}, reverse complement A <-> T, C <-> G
                  (no self-complementary base: every 3-mer pairs with a
                   distinct reverse complement)
truth             S = ATATACAC          (G = 8)
competitor        D = ATACACAC          (G = 8, SAME LENGTH)
read length       L = 3,  o_min = 2
realized starts   (1, 3, 4, 5, 6, 7)     (n = 6 reads, all distinct)
external size     N = |S| = 8
observed          x = { ATA/TAT:1, TAC/GTA:1, ACA/TGT:2, CAC/GTG:1, CAT/ATG:1 }
truth spectrum    d_S = { ATA/TAT:3, TAC/GTA:1, ACA/TGT:2, CAC/GTG:1, CAT/ATG:1 }
competitor spec   d_D = { ATA/TAT:1, TAC/GTA:1, ACA/TGT:3, CAC/GTG:2, CAT/ATG:1 }
```

Both same-length objectives strictly improve:

```text
exact candidate-intrinsic multinomial (Variant E)   L_E(D)/L_E(S) = 3/2
literal §6.1 product of binomial marginals (Variant A) L_A(D)/L_A(S) = 9/5
```

Both candidates satisfy the **source** per-vertex rule (support equality) and the
**strengthened** per-occurrence rule. Because the improvement is strict and the
ratio is `> 1`, `W` (truth is a maximizer) is refuted, and therefore so is `S`
(the uniqueness schema) for every equivalence `≈` and every tie convention.
**[M]**, see
[`conclusion-semantics-strict-witness-robustness.md`](source-notes/conclusion-semantics-strict-witness-robustness.md).

---

## 1. Source semantics

### 1.1 The per-occurrence strengthening is not the source's rule

Primary source: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §3.3, §3.4, §4.1,
§6.1–6.2, PMC3154397.

- §3.1: "A DNA molecule is an unordered pair of strings (also called strands)
  that are reverse complements of each other."
- §4.1: "each `k`-molecule is represented only once."
- §6.2: vertices are the reads, "which are DNA molecules"; "each vertex has a
  lower bound of `1` since it represents a read that must be present in the
  genome at least once"; "all other lower bounds are `0` and all upper bounds
  are infinity"; supersource/supersink at prohibitive cost.
- Observation 7: the number of visits of a walk to a read vertex equals the
  number of times that read is a submolecule of the spelled molecule.

**Source-supported inference.** A duplicated observed molecule is a *single*
vertex; the observed multiplicity `x_w` enters only the §6.1 likelihood; and the
lower bound is **per vertex**. For a spelled candidate this is exactly support
equality `supp(spec_L(D)) = supp(x)`.

**Editorial choice.** Requiring in addition `d_D(w) ≥ x(w)` for every observed
type is the **per-occurrence strengthening** `Focc`. It is strictly stronger
than the source rule and is **not** the §6.2 definition. It is the repository's
own assumption surface, and it is what row R13 tests. It is therefore *outside*
the class of source-supported interpretations of the 2016 sentence; refuting it
is a mathematical service, not a reading of the paper. [source fact +
editorial choice]

### 1.2 Why a new witness is needed

The merged same-length witness `AAATAT → AAAAAT`
([`section62-same-length-bidirected-counterexample.md`](section62-same-length-bidirected-counterexample.md),
row R11) refutes the source per-vertex reading, but its **truth is not
per-occurrence feasible**: `d_S(AAA) = 1 < x_AAA = 2`. So that refutation does
not transfer to R13, and R13 could not be closed by transfer. Something has to
raise the truth's own multiplicity in every observed coordinate.

The `A ↔ T`, `C ↔ G` reverse-complement involution is what does it. The earlier
witness searched an alphabet with a self-complementary base (`A ↔ T` over a
binary alphabet), which limits how far a genome can out-count its own
observation; the real DNA alphabet has no self-complementary base, so every
3-mer pairs with a *distinct* reverse complement and the truth can be
per-occurrence feasible while still not read-tiled. Here `x_{ACA/TGT} = 2` and
`d_S(ACA/TGT) = 2` — tight, but `x_{ATA/TAT} = 1 < d_S(ATA/TAT) = 3`, so
`n = 6 < G = 8` and the strengthening genuinely does not collapse to
read-tiling. **[K]** `truth_peroccurrence`, `competitor_peroccurrence`,
`not_read_tiled`.

### 1.3 Shomorony `I_s`

Shomorony, Kim, Courtade, Tse (2016), Eq. (1), attributed to Bresler, Bresler &
Tse (2013): a read realization `R ∈ I_s` iff it covers the circular truth, every
triple repeat is all-bridged, and every interleaved repeat pair is bridged. A
copy at `t` of a repeat of length `ℓ` is bridged by a read occupying
`[r, r+L)` iff `r < t` and `t + ℓ < r + L`. Recorded and sourced in
[`bridging-source-semantics.md`](bridging-source-semantics.md). The certified
predicate is the shared, authoritative `SourceFaithfulIs.InformationFeasible`
quantified over all repeat lengths and all selected starts, discharged by
finite `decide` — no clause is assumed. **[K]**.

---

## 2. Independent verification

Two independent layers, neither of which is the sole check.

**Exact recomputation.** `scripts/verify_peroccurrence_dna_samelength_212.py`
shares no code with the repository: it recomputes the windows, the molecule
classes, `x`, `d_S`, `d_D`; re-checks `I_s` under the strict source bridging
predicate *and* under the older endpoint-only reading (both hold here); checks
support equality and the per-occurrence lower bounds on both sides; builds the
explicit 16-edge bidirected overlap graph at `o_min = 2` (MB09 §3.3 four
strand-overlap cases) with every edge's incidence signs; verifies that both
cyclic window walks are genuine bidirected circuits (every step a real edge,
opposite incidences at every interior vertex, vertex lower bound `1`,
per-occurrence throughputs, zero read-vertex balance, no supersource/supersink);
checks the transitive edge reduction vacuous under both readings; and evaluates
both objectives. It exits non-zero on any failure. **[V]**

**Independent re-derivation.** Front #217 additionally re-derived the
observation, both spectra, the support and per-occurrence conditions, and both
exact ratios from the two strings alone, with no reference to either the leaf
script or the Lean module. All values agree. **[V]**

**Kernel check.** `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean`
kernel-checks, for this concrete data, the literal MB09 §6.2 feasibility of
**both** candidates via `AssemblyP1.Section62BidirectedFlow`: the explicit
16-edge overlap graph proved equal (`graph_eq`) to the generated `overlapEdges`,
the transitive reduction vacuous under both the literal and the longer-overlap
reading, edge lower bounds `0`, vertex lower bound `1`, §3.4 signed-incidence
balance `0` at every read vertex, no supersource/supersink usage, every visited
vertex an observed read molecule, every step a real edge surviving the
reduction, and vertex throughput equal to the candidate's own molecule spectrum
(the hand-written certificate flows are proved equal to the walks' own flows).
**[K]**

---

## 3. The endpoint

```text
AssemblyP1.PerOccurrenceSameLengthCounterexample.peroccurrence_samelength_se62_bidirected_flow_counterexample
  : SourceFaithfulIs.InformationFeasible truthGenome 3 realizedStarts ∧
    (genomeLength truth = genomeLength competitor) ∧
    (PerOccurrenceFeasible dS obs ∧ PerOccurrenceFeasible dD obs) ∧
    SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts spellTruth
      truthCircuitFlow noTerm dS' ∧
    (SpelledFeasible62 Base W3 toList3 rep3 rc3 readLen oMin readVerts
        spellCompetitor competitorCircuitFlow noTerm dD' ∧
      (lik obs dS < lik obs dD ∧ exactLik dD obs / exactLik dS obs = 3 / 2))

AssemblyP1.PerOccurrenceSameLengthCounterexample.peroccurrence_samelength_maximality_refuted
  : ¬ PerOccurrenceSameLengthMaximality
```

`PerOccurrenceSameLengthMaximality` is the strengthened sentence stated as a
`Prop` **[C]**; it was never a theorem, so refuting it introduces no definition
change. `#print axioms` on both endpoints and on the `Prop` reports exactly
`[propext, Classical.choice, Quot.sound]`. **[K]**

Verification actually performed by front #217 in `/workspace/assemblyp1-finite-217`:

| check | command | result |
|---|---|---|
| build | `LEAN_NUM_THREADS=4 lake build AssemblyP1.PerOccurrenceSameLengthCounterexample` | **Build completed successfully (8926 jobs)** |
| kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker AssemblyP1.PerOccurrenceSameLengthCounterexample`, one module per process | **exit 0**; control `leanchecker AssemblyP1.NoSuchModuleXYZ` exits 1 with `Could not find any oleans for: …`, so the pass is non-vacuous |
| axioms | `lake env lean` with `#print axioms` on the two endpoints and the `Prop` | `[propext, Classical.choice, Quot.sound]` |
| witness script | `python3 scripts/verify_peroccurrence_dna_samelength_212.py` | **ALL CHECKS PASS** (46 assertions) |
| census | `python3 scripts/verify_peroccurrence_dna_samelength_212.py --search` | **ALL CHECKS PASS**, see §4 |
| independent re-derivation | a separate from-first-principles script over the two strings | `x`, `d_S`, `d_D`, both supports, both per-occurrence conditions, ratios `3/2` and `9/5` all reproduced |

The whole-library `lake build --wfail`, whole-library kernel replay, and
`axiom-audit --modules-from` are deliberately left to CI.

---

## 4. Bounded census, and why it is still only evidence

`--search` enumerates an exhausted scope over truths, read placements and
multiplicities, requiring `I_s`, per-occurrence feasibility of both sides, and a
strict same-length improvement. With `sigma` the alphabet size (`sigma = 4` is
the real DNA alphabet, `3` one self-complementary base, `2` a two-letter
alphabet):

| `G` | `L` | `sigma` | truths | instances | both-objective beats | distinct `(S,D)` pairs |
|---|---|---|---|---|---|---|
| 6 | 3 | 2 | 9 | 82 | 0 | 0 |
| 7 | 3 | 2 | 10 | 70 | 0 | 0 |
| 8 | 3 | 2 | 22 | 260 | 0 | 0 |
| 6 | 3 | 3 | 74 | 575 | 0 | 0 |
| 7 | 3 | 3 | 171 | 717 | 0 | 0 |
| 8 | 3 | 3 | 444 | 1480 | 4 | 1 |
| **8** | **3** | **4** | 4179 | 33274 | **16** | **4** |
| 6 | 4 | 3 | 74 | 916 | 0 | 0 |
| 8 | 4 | 3 | 444 | 9558 | 0 | 0 |

The four distinct beating pairs at `(G,L,sigma) = (8,3,4)` are
`ATATACAC → ATACACAC`, `ATATAGAG → ATAGAGAG`, `ACACGCGC → ACACACGC`,
`AGAGCGCG → AGAGAGCG` — all in the orbit of the certified instance.

Two things must be kept apart:

* The **witness** is a single finite instance with a kernel-checked certificate.
  That settles R13: a strict counterexample refutes the strengthened sentence,
  exactly as a counterexample settles `∀ n, P n`. Its status does not depend on
  any search being complete. **[K]**
* The **census** is bounded evidence about *how common* the mechanism is. Zero
  rows are computational evidence bounded by the stated scope, **not** a proof
  of absence. Nothing here is a claim that every instance in every scope has been
  enumerated. **[V] bounded**

---

## 5. Why it works

1. **The real DNA alphabet makes the truth per-occurrence feasible.** With no
   self-complementary base, a length-`8` circular genome can contain every
   observed molecule class at least as often as it was observed, while still
   containing some class strictly more often (`d_S(ATA/TAT) = 3 > x = 1`) — so
   the strengthening is genuinely satisfied and genuinely stronger than
   read-tiling.
2. **Same length means equal total mass.** `sum(d_S) = sum(d_D) = G = 8`, so
   improving the objective is a pure redistribution of multiplicity across
   observed classes, with no length term to pay for.
3. **`n = 6 < N = 8` makes redistribution strictly profitable.** Moving a unit
   of multiplicity from the over-represented `ATA/TAT` to the observation-heavy
   `ACA/TGT` (and from `CAC/GTG` to `ACA/TGT`) raises the exact factor from
   `3·2` to `1·3` on the moved coordinates; the tight coordinate
   `ACA/TGT` (`x = d_S = 2`) is exactly where the strengthening binds, which is
   why the earlier binary-alphabet search could not produce one.
4. **Both candidates are literal §6.2 flows**, so no part of the certificate
   rests on the support-equality proxy. The mechanism uses only source-level
   features: reverse-complement molecule classes, per-vertex lower bound `1`, and
   the §6.1 objective.

---

## 6. What this does and does not settle

**Does.** It closes row R13: under the per-occurrence strengthening, molecule
read types, same-length §6.2 candidates, both objective variants, the ML
maximizer claim is **false**, by a strict, equivalence-and-tie-robust,
kernel-checked witness.

**Does not.** It does not settle which Medvedev–Brudno object the Shomorony
et al. (2016) sentence intends; that referent selection remains a **source
gap**. It does not address single-strand (oriented) indexing, the
variable-length case, or tie/equivalence semantics as a positive result. It does
not extend to row R16 (the Bresler–Bresler–Tse doubled-strand `2G` convention,
a different paper's convention, still bounded evidence only) or to row R17 (the
unspecified general principle, not a determinate proposition). And it does not
claim that a census is a proof of absence anywhere.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| §6.2 per-vertex lower bound `1`; reads are molecule classes, each `k`-molecule once; Observation 7 | **source fact** (MB09 §3.1, §4.1, §6.2, Obs. 7) |
| per-occurrence `d_D(w) ≥ x(w)` is a strengthening, not §6.2 | **source-supported inference** + **editorial choice** |
| `S = ATATACAC`, `D = ATACACAC`: `I_s` (strict and endpoint-only), both supports equal to `x`, both per-occurrence feasible, same length, exact ratio `3/2`, binomial ratio `9/5` | **verified computation** + **kernel-checked** |
| both candidates are literal §6.2 bidirected circuits (16-edge graph, vacuous reduction, balance, throughput = own spectrum) | **kernel-checked** |
| the strict improvement refutes `W` and `S` for every `≈` and tie rule | **mathematical fact** |
| the census table of §4 | **verified computation**, bounded — not a proof of absence |
| row R13 of the interpretation matrix is resolved to FALSE | follows from the kernel-checked witness |
| which MB09 object the 2016 sentence denotes | **source gap, unchanged** |
| the publisher supplementary ZIP | still uninspected — **source gap** |

---

## 8. Provenance

The witness, the Lean module, and the exact-verification and census script were
produced by leaf **#212** (agent `cedd79adfeae`, registered worktree
`/workspace/assemblyp1-finite-212`, branch `agent/board-212-37b45b`), whose
script is committed there as `6aeb95e`. Front #217 read that worktree
**read-only**: it was not written to, its `cwd` was never reused, and no
cherry-pick, merge, or deletion was performed. The module and the script were
**copied** into this worktree (SHA-256 `96e44d42…ba7b2` and
`8c30c2ef…9c700` respectively) and then rebuilt, replayed, re-axiom-checked and
re-run **here**, on `main` at `cc0aa8a`, before any matrix row was changed. Leaf
#212's two shared dependencies `AssemblyP1.SourceFaithfulIs.lean` and
`AssemblyP1.Section62BidirectedFlow.lean` are byte-identical in both worktrees,
so the module could not have been checking a different predicate.

Primary sources: Paul Medvedev, Michael Brudno, *Maximum Likelihood Genome
Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1, §3.3, §3.4, §4.1,
§6.1–6.2, PMC3154397; Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade,
David N. C. Tse, *Information-optimal genome assembly via sparse read-overlap
graphs*, *Bioinformatics* 32(17) (2016) i494–i502, Eq. (1) and §5.
