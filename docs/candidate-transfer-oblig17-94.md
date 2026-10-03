# Obligation 17 — the candidate-side transfer (front E, board 94)

Branch `research/94-oblig17`, base `9abe44c`. Front E of the reconciliation plan
item E in `/workspace/BOARD94-RECONCILE-NEXT.md` §5.

**Status: stated, not discharged.** This note and the one new module
`AssemblyP1/BBTCandidateTransfer.lean` make the obligation precise and checkable.
No Lean proof is attempted, no `lake build` was run, no branch was moved.

---

## 1. What obligation 17 is, in the repository's own vocabulary

The dependency recorded by the audit is

```text
Endpoint L                                        (BBTEndpoint94.lean:119)
  -> Residual L = BBTEulerian.EulerianCycleObstruction (α:=α) L   (BBTEulerian.lean:400)
       -> {14, 15, 16, 17}
```

Obligations 14, 15 and 16 are all *support-side* statements: they quantify a
successor map `θ` on the **truth** `S` and derive a violation of `Ukkonen` on
`S` (`BBTSupportInvariant.SupportDichotomy` :200,
`SelectedTriple_obstruction` :211, `SelectedInterleaved_obstruction` :223, fed to
`orbitVertexEq_of_dichotomy` :254).

None of them mentions a **candidate** genome. Yet the conclusion that the
endpoint consumes is about a candidate: `bbtCompleteSpec_of_obstruction`
(`BBTEulerian.lean:441`) concludes `RotEquiv hK E S` for a second word `E`.

**The transfer** is the passage

```text
   an equal-spectrum pair (S, E) with E a rotation of S
        <-->   the truth-side presentation pullback hK L S E σ is an Eulerian
                 cycle of S spelling S's own vertex cycle
```

concretely realised by three existing pieces of infrastructure:

* `BBTChords.exists_matching` (`BBTChords.lean:375`) — equal complete spectra
  give a bijection `σ` with `Matching`;
* `BBTCondense.pullback` (`BBTCondense.lean:462`) — the candidate-to-truth map;
* `BBTEulerian.pullback_isEulerianCycle` (`BBTEulerian.lean:257`) — the pull-back
  is an Eulerian cycle of the **truth's** condensed graph;
* `BBTEulerian.rotEquiv_of_vertexCycleEq` (`BBTEulerian.lean:294`) — a
  rotational vertex cycle of that presentation makes the candidate a rotation
  of the truth. **This is the only `VertexCycleEq → RotEquiv` theorem in the
  tree** (verified by `git grep -n VertexCycleEq AssemblyP1/` — the sole caller
  of `rotEquiv_of_vertexCycleEq` is `BBTEulerian.lean:450`).

So the forward direction is discharged and in the build graph. What is **not
stated anywhere in the repository** is the reverse reading, and it is the
reading that any attack on the residual has to go through: to prove
`EulerianCycleObstruction` one must start from a *non*-rotational `E` and
manufacture the bad presentation on `S`. That is the contrapositive of clause 2
below, and nothing in the tree provides it.

**Source lemma (target of the transfer):**
`AssemblyP1.P2.BBTCompleteSpectrumUniqueness` (`P2.lean:154`), instantiated at
the candidate side and consumed as `BBTUniqueAt` (`P2.lean:165`) by
`AssemblyP1.PopulationUniqueness.population_unique_ML_up_to_rotation`
(lines 185, 190, 191, 196) via
`BBTEulerian.bbtUniqueAt_of_obstruction` (`BBTEulerian.lean:455`).

**Target lemma (hypothesis of the transfer):**
`AssemblyP1.BBTEulerian.EulerianCycleObstruction` (`BBTEulerian.lean:400`), whose
quantifier structure is *truth-side only*:

```lean
∀ (K) (hK) (S), Ukkonen hK L S → ∀ σ, EulerianCycle hK L S σ →
    VertexCycleEq hK L S σ refl ∨ LongObstruction hK L S
```

The asymmetry is the whole point: `EulerianCycleObstruction` says nothing about
`E`, yet it is used to conclude something about `E`. The transfer is what makes
that legitimate, and it is currently implicit in `bbtCompleteSpec_of_obstruction`.

---

## 2. What was written

One new file, `AssemblyP1/BBTCandidateTransfer.lean`, containing **one** new
definition:

```lean
def CandidateTransfer (L : ℕ) : Prop :=
  -- (1) forward BBT, hypothesis-free on the candidate
  (∀ (K) (hK) (W E : Fin K → α), Ukkonen hK L W →
     specCount (L := L) hK W = specCount (L := L) hK E → RotEquiv hK E W) ∧
  -- (2) the presentation transfer, in both directions
  (∀ (K) (hK) (W E : Fin K → α) (σ : Fin K → Fin K), Matching (L := L) hK W E σ →
     (VertexCycleEq hK L W (pullback hK L W E σ.1) (Equiv.refl (α := Fin K))
        ↔ RotEquiv hK E W)) ∧
  -- (3) support-side recovery from a non-rotational candidate
  (∀ (K) (hK) (W E : Fin K → α), Ukkonen hK L W →
     specCount (L := L) hK W = specCount (L := L) hK E → ¬ RotEquiv hK E W →
     ∃ θ : Fin K → Fin K, Function.Bijective θ ∧ FibrePreserving hK L W θ ∧
       OneCycle hK θ ∧ ¬ OrbitVertexEq hK L W θ)
```

Clause (1) is the shape `bbtCompleteSpec_of_obstruction` already provides and is
**discharged** (conditional on the residual inhabitant, which is the open
question). Clauses (2) and (3) are the obligation. Neither is proved.

Clause (3) is the precise statement of what obligations 14/15/16 are *for*: they
are stated for a truth-side `θ`, so somebody has to show that a bad candidate
produces such a `θ`. That somebody does not exist yet in the tree.

The docstring records honestly: (a) `2 ≤ L` is not assumed inside the
definition, matching `bbtCompleteSpec_of_obstruction` which takes it separately;
(b) equal length is a *consequence* of the #70 reduction
(`PopulationReduction.population_uniqueness_primitive_P2_words`,
`PopulationReduction.lean:1834`), not an extra assumption, so folding it into
clause 1 is honest; (c) no hypothesis is placed on `W` in clause (3) because
obligations 14/15/16 are candidate-free and this front does not restate them.

---

## 3. Sub-steps already discharged elsewhere

| step | statement | where | status |
| --- | --- | --- | --- |
| equal spectra → matching | `BBTChords.exists_matching` | `BBTChords.lean:375` | kernel-checked |
| candidate → truth start map | `BBTCondense.pullback`, `pullback_window`, `pullback_isEquiv` | `BBTCondense.lean:462,467,477,481` | kernel-checked |
| pull-back is an Eulerian cycle of `S` | `BBTEulerian.pullback_isEulerianCycle` | `BBTEulerian.lean:257` | kernel-checked |
| rotational vertex cycle ⇒ candidate rotates | `BBTEulerian.rotEquiv_of_vertexCycleEq` | `BBTEulerian.lean:294` | kernel-checked — **this is the forward half of clause 2** |
| `VertexCycleEq σ refl ↔ OrbitVertexEq (succOf σ)` | `BBTEulerianSearch.vertexCycleEq_iff_orbit` | `BBTEulerianSearch.lean:263` | kernel-checked — converts clause 2 into clause 3's last conjunct |
| `succOf σ` is bijective / fibre-preserving / one-cycle | `succOf_bijective` :204, `fibrePreserving_succOf` :208, `oneCycle_succOf` :214 | `BBTEulerianSearch.lean` | kernel-checked — the three side conditions of clause 3, already available |
| `Ukkonen` ⇒ no `LongObstruction` | `not_longObstruction_of_Ukkonen` | `BBTEulerian.lean:372` | kernel-checked |
| `P2` ⇒ `Ukkonen` | `P2.imp_Ukkonen` | `P2.lean:104` | kernel-checked |
| `EulerianCycleObstruction` ⇔ `UniqueEulerianCycle` | `uniqueEulerianCycle_of_obstruction` :408, `obstruction_of_uniqueEulerianCycle` :416 | `BBTEulerian.lean` | kernel-checked |
| `Residual` is the sole non-kernel hypothesis of the endpoint | `BBTEndpoint94.lean:138` | `BBTEndpoint94.lean` | **NOT verified by this front** — file is owned by live front 94c07 and was not read |

Commit provenance for the entries above: all of these are on the base commit
`9abe44c` or its ancestors and were verified by reading the source in this
worktree, not from the audit. I did **not** verify which commit introduced each
one; `git log -L` was not run.

## 4. What is open

1. **Clause 2, `←` direction** (i.e. `¬ RotEquiv hK E W → ¬ VertexCycleEq (pullback σ) refl`).
   No statement exists. Searched: `git grep -n VertexCycleEq AssemblyP1/`.
   The only other `RotEquiv` result on a pull-back is
   `BBTCondense.pullback_rotation_RotEquiv` (`BBTCondense.lean:709`), whose
   hypothesis is `IsRotation hG (pullback ...)` — about the pull-back as a
   *permutation of starts*, not about `VertexCycleEq` of the presentation. The
   two are not interchangeable and no bridge is proved.
2. **Clause 3 in full.** Needs clause 2 plus the fact that the *pull-back* of an
   equal-spectrum matching, viewed as a successor map, satisfies the three side
   conditions. The side conditions are available for any `EulerianCycle σ`
   (`succOf_bijective` etc.) and `pullback_isEulerianCycle` gives exactly that,
   so clause 3 is expected to be clause 2 plus `vertexCycleEq_iff_orbit`. **No
   Lean was run to confirm that**; see §7.
3. **The residual inhabitant itself.** Out of scope for this front.

## 5. What a counterexample attempt looks like

`scripts/board94_candidate_transfer_check.py` (new, this front). It re-derives
`window`, `specCount`, `vtx`, `Matching`, `pullback`, `VertexCycleEq`,
`RotEquiv`, `EulerianCycle`, `succOf`, `FibrePreserving`, `OneCycle`,
`OrbitVertexEq`, `IsRepeat`, `IsTripleRepeat`, `Interleaved`, `LongObstruction`
and `Ukkonen` from scratch and enumerates, for every binary `S`, every binary
`E` with an equal complete `L`-spectrum, and **every** bijection `σ` (not just
generated matchings), checking

* **Q1** `VertexCycleEq(pullback σ) refl → RotEquiv E S` (the discharged half),
* **Q2** `RotEquiv E S → VertexCycleEq(pullback σ) refl` (clause 2, open),
* **Q3** `RotEquiv E S → OrbitVertexEq (succOf (pullback σ))` (clause 3, open).

Instance counts are printed for every question, because a checker that selects
no cases proves nothing.

Measured at `G ≤ 6, L ∈ {2,3}`, binary alphabets:

```text
L=2  words=126  equal-spectrum (S,E) pairs=726  matchings tested=6784
     of which EulerianCycle=3832  RotEquiv instances=5920     Q1=0 Q2=0 Q3=0
L=3  words=126  equal-spectrum (S,E) pairs=654  matchings tested=3270
     of which EulerianCycle=2734  RotEquiv instances=3198     Q1=0 Q2=0 Q3=0
TOTAL  equal-spectrum pairs=1380  matchings=10054  RotEquiv instances=9118
       Q1=0  Q2=0  Q3=0
```

**Reading: no counterexample to clauses 2 and 3 at `G ≤ 6`.** This is
evidence, not proof, and the completeness of the enumeration is not proved.
Q1 = 0 is a sanity check on the re-derivation (it should be 0, and is).

Note the counts are far above what a "no cases selected" bug would produce:
9118 `RotEquiv` instances were actually evaluated.

## 6. The pitfall, and a correction to its recorded witness

Front 94d23 recorded: `S = 0001`, `G = 4`, `L = 2`; `IsTripleRepeat 1 0 1 2`
holds; **"all three candidate pairs fail `IsRepeat 1`"**; so `0001` is not
`Ukkonen` at `L = 2`.

The conclusion reproduces. The middle clause does **not**, on re-derivation from
`SourceFaithfulIs.Genome.IsRepeat` (`SourceFaithfulIs.lean:111`) and
`IsTripleRepeat` (`SourceFaithfulIs.lean:122`):

```text
IsRepeat 1 0 2 on S = [0,0,0,1]:
  1 <= 1, 1 < 4, 0 != 2                                   ok
  Agree 1 0 2 : S[0] = 0 = S[2]                            ok
  Preceding 0 = S[3] = 1  !=  Preceding 2 = S[1] = 0       ok
  Following 1 0 = S[1] = 0  !=  Following 1 2 = S[3] = 1   ok
=> IsRepeat 1 0 2 HOLDS.
```

So `0001` *does* contain a maximal repeat pair at `e = 1`. The correct witness
for the three-copy reading is the triple itself: `IsTripleRepeat 1 0 2 1` with
preceding `1,0,0` and following `0,1,0`, neither triple all equal.

The **substantive lesson survives intact** and my checker implements it: the
three-copy clause of `IsTripleRepeat` is
`¬(Preceding a = Preceding b ∧ Preceding b = Preceding c)`, i.e. "not all three
equal", strictly weaker than pairwise distinctness of the three two-sided
maximality conditions, so triple repeats are **not** enumerable only inside
maximal repeat pairs. My checker enumerates triples directly (Q4) and counts
`11040` triple instances at `G ≤ 6`, alphabets `{0,1,2}`, with `0` containing no
maximal `e`-pair — consistent with 94d23's warning.

The checker aborts before running any census unless the pitfall **conclusion**
reproduces, and prints the pair list so the discrepancy stays visible.

## 7. Cheapest evaluator that could change this obligation's priority

`scripts/board94_candidate_transfer_check.py` is already it: seconds of Python,
no Lean, no Mathlib. Raising the bound to `G = 8` (alphabet `{0,1,2}`,
`L ∈ {2,3}`) is the first thing a successor should do, and it is the only
evaluator that could *refute* clause 2 or 3.

For the forward direction there is already a kernel-checked finite evaluator in
the tree: `AssemblyP1.BBTEulerianFinite` (`BBTEulerianFinite.lean`, with
`FiniteBinary 4 6` at :135), which checks `EulerianCycleObstruction` on a finite
binary class. That checks the residual directly and does **not** go through the
transfer, so it says nothing about clauses 2 and 3.

If a successor wants a Lean-level evaluator, the cheapest honest target is a
`decide`-backed finite instance of clause 2 at `G = 5, L = 3`, mirroring
`BBTEulerianFinite.finiteBinary_4_6`. That would need `lake build`, which this
front is fenced from; the orchestrator should assign it, not this front.

## 8. What I did not verify

* **No Lean was compiled.** There is no `.lake` directory in this worktree, so
  even a single-file `lake env lean` typecheck is not available here. The new
  module `AssemblyP1/BBTCandidateTransfer.lean` is therefore **unverified** and
  is deliberately not imported by `AssemblyP1.lean` (fence: I must not edit that
  import list). It should be read as a statement of intent, not as
  kernel-checked text. If `Matching`, `pullback`, `VertexCycleEq`,
  `FibrePreserving`, `OneCycle` or `OrbitVertexEq` do not resolve under the
  namespace openings used, elaboration will fail and the module will need
  repair. I checked each name and each namespace by reading the `open`
  directives in `BBTEulerian.lean:106-111` and `BBTSupportInvariant.lean:86-92`,
  but *reading is not checking*.
* `BBTEndpoint94.lean` was **not read** (owned by live front 94c07). The claim
  "`Residual L = EulerianCycleObstruction` at `BBTEndpoint94.lean:138`" is
  adopted from the reconciliation audit, not re-derived here.
* `BBTSupportInvariant.lean` was read but **not modified**. Its
  `SelectedTriple_obstruction` at :211 is noted as the kernel-checked **false**
  statement that front 94d22 is handling; this front neither cites nor depends
  on it, and clause 3 of `CandidateTransfer` does not mention it.
* `case1_landing` is **not** cited, and `CandidateTransfer` does not depend on
  it. It has been refuted (G = 5, M = 3, S = 00101) and the retraction is in
  flight with another front.
* Commit provenance per row of §3's table was not established.
* The Q2/Q3 census is evidence only; the enumeration's completeness is unproved.