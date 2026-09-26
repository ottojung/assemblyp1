# #88 audit: the refutation is correct but narrower than claimed, and the repaired positive theorem

This note records an independent audit of the #88 deliverable at `b6cedf0`, the
corrections it forced, and a new positive theorem. Two claims in the previous
commit message did not survive the audit and are corrected here. The kernel-level
counterexample itself is sound and is retained unchanged.

## Summary of the audit

| claim at `b6cedf0` | verdict |
| --- | --- |
| full source-faithful `I_s` holds for `AABB`, `L = 2`, starts `{1,3}` | **true**, re-verified independently |
| `ABAB` is a genuine same-length `Section62Flow.SpelledFeasible62` candidate | **true**, all five conjuncts |
| truth `1/16` vs competitor `1/4` under the exact finite objective | **true** |
| candidate-length parameter match (`N = g.len` on both sides) | **true** |
| no duplicated-read convention abuse | **true**, one read per distinct start, coupling proved |
| graph spelling corresponds to the claimed competitor | **was unproved**; now `genuine62` correspondence, kernel-checked |
| `Is62MaximumLikelihood` is a *maximizer* statement | **false**; it is a *dominance* statement with no membership conjunct |
| the #88 maximizer claim (with membership) is refuted | **not established**; the membership antecedent is false at this instance |

## 1. What is sound

`AssemblyP1.SameLengthExactMLCounterexample` is correct. Independently re-checked:

* `realized_reads : truthGenome.window 2 1 = observedAB ∧ truthGenome.window 2 3 = observedBA`
  holds, so the hypothesis and the observation come from *one* realization, not
  two configurations.
* `truth_information_feasible` is `decide` on the full predicate. Reading the
  clauses by hand: coverage holds because the read at start `1` covers `{1,2}`
  and the read at start `3` covers `{3,0}`; there is no triple repeat at any
  length `1 ≤ e < 4` (`A` occupies `{0,1}`, `B` occupies `{2,3}`, both of size
  two); and the only two repeats, at starts `(0,1)` and `(2,3)`, do not
  interleave. Clauses 2 and 3 are genuinely vacuous — clause 1 is the only
  load-bearing one.
* `competitor_spelledFeasible62` discharges all five conjuncts. The arithmetic
  is right: `d_truth(AB) = d_truth(BA) = 1`, `d_competitor(AB) = d_competitor(BA) = 2`,
  `N = 4` on both sides, so `(1/4)² = 1/16 < (2/4)² = 1/4`.

The `N = g.len` normaliser is candidate-intrinsic in both the truth and the
comparator, so there is no parameter mismatch: this is a genuine *same-length*
comparison, which is the case the pre-existing
`AssemblyP1.ExactVariantECounterexample` does not cover.

The earlier harness bug noted in the previous commit (observations keyed by
spectrum count, giving vacuous "0 counterexamples") is real and the correction
is genuine; nothing in this audit reuses that harness.

## 2. Defect 1: the spelling↔genome correspondence was asserted, not proved

`Section62Flow.SpelledFeasible62` certifies an abstract object: a cyclic word of
strands `sp : Spelling A W n`, a flow, terminals and a throughput vector. It
contains no statement that this object is the window walk of any genome. The
previous module supplied `competitorSpelling` by hand and proved it was feasible,
but nothing connected it to `competitorGenome`. The claim "the graph spelling
corresponds to the claimed competitor" therefore rested on prose.

This is now a definition and a hypothesis in
`AssemblyP1/SameLength62Maximizer.lean`:

* `Represents62 C sp` — `n = C.len` and, at every cyclic read position, the
  strand is exactly `C`'s own length-`L` window there;
* `Is62Candidate62` — a representing spelling, a literal `SpelledFeasible62`
  certificate, **and** `f = sp.flow rep L`, i.e. the flow is the traversal
  multiset of the walk itself.

The last clause is the natural reading of MB09 §6.2 (the candidate's flow is its
own circuit's traversal multiset) and it is what makes the coverage clause bite;
see §4.

## 3. Defect 2: the refuted predicate is dominance, not maximizer

`Is62MaximumLikelihood` in the previous module is

```lean
def Is62MaximumLikelihood (g c) L reads :=
  ∀ n sp f t d, n = c.len → SpelledFeasible62 … sp f t d →
    sameLengthExactLik c L reads ≤ sameLengthExactLik g L reads
```

This is a statement that **`c` is dominated by the truth**, quantified over
certificates. It has **no** conjunct saying the truth is itself a §6.2
candidate. The commit message described it as "the circular candidate `c`
maximises the exact objective over every same-length §6.2-feasible spelled
candidate, relative to the truth `g`", and the note described the refutation as
settling "the §6.2 acceptance boundary". Both overclaim.

The reason is a genuine asymmetry, and the previous module did record it
(`truth_not_spelled_on_observed`) but then drew the wrong conclusion from it.
Re-verified independently in Lean: the truth's own window walk
`AA → AB → BB → BA` **fails** `VisitsObserved` at `AA`, because
`observedVerts = [AB, BA]` and `AA` was never observed. So:

* the **dominance** claim is refuted. `ABAB` is a genuine same-length §6.2
  candidate and beats `AABB`. This is a real counterexample and it is retained.
* the **maximizer-with-membership** claim — "the truth is a §6.2 candidate *and*
  maximises" — is *not* refuted, because its membership antecedent is `False` at
  this instance. A statement with a false antecedent cannot be refuted by
  exhibiting a good member of the class.

So the correct reading of the `AABB`/`ABAB` witness is: **the truth is not even a
member of the §6.2 candidate class here, and the class contains a member that
beats it anyway.** Both facts are useful; together they say the §6.2 restriction
is *not* a restriction the truth satisfies, so it cannot be the setting in which
a maximizer statement about the truth is well posed. This is a sharper and more
interesting statement than "§6.2 does not rescue the claim", and it is what the
repository now asserts.

Corollary of the asymmetry, and the reason the search below comes out empty: if
the truth *is* a §6.2 candidate, then by §4 below the observed read set is the
truth's window support, so any §6.2 candidate has the *same* window support as
the truth, and the §6.2 class collapses to the
`IsSameLengthSpelledCandidate` class of the mature rigidity chain. The
`AABB`/`ABAB` pair escapes precisely because `ABAB` has a *strictly smaller*
window support than `AABB` — it is feasible only because the truth is not.

## 4. The repaired positive theorem

`AssemblyP1.SameLength62Maximizer.lean` proves the maximizer statement under the
candidate class the literal §6.2 model actually admits.

### The bridge

`genuine62_molecule_eq` is the load-bearing lemma and it is **proved**, not
assumed:

```
Is62Candidate62 C  ⟹  ∀ w, (∃ r, rep (C.window L r) = w) ↔ w ∈ verts
```

* **Forward** (`VisitsObserved` read through `Represents62`): every window of `C`
  is an observed read molecule class.
* **Backward** (the §6.2 vertex lower bound of `1`): every observed read must
  carry flow, so some walk step departs its class, so `C` spells it. The single
  step is isolated as `visited_of_positive_throughput`, which uses only a
  *lower* bound on throughput and so is robust to the edge-list duplication of
  strict single-strand mode (`strandsOf rc verts = verts ++ verts.map rc`
  enumerates each class once per strand slot, which is why the AABB/ABAB witness
  needs `d = 8` rather than `2`).

Hence **two same-length genuine §6.2 candidates have the same window support**
(`support62_eq_of_genuine62`, `oriented_support_eq_of_genuine62`), and each has
the observed read set as its support. In the oriented single-strand reading
`rep = id`, so this is literally equality of oriented window supports, and
`genuine62_is_spelled_candidate` composes it into exactly
`AssemblyP1.OrientedSameLengthML.IsSameLengthSpelledCandidate`.

**This is the substantive point: the §6.2 candidate restriction is not a
different class from the one the mature rigidity chain consumes. It is the same
class, read off the literal §6.2 flow model.** The previous work had to *assume*
`IsSameLengthSpelledCandidate`; here it is *derived*.

### The theorem

```lean
theorem informationFeasible_62_maximizer
    (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G)
    (S D : Fin G → α) (ρ : Realization G n) (R : Finset (Fin G))
    (_hR : ∀ i, ρ i ∈ R)
    (_hfeas : InformationFeasible ⟨G,hG,S⟩ L R)
    (hno : ¬ HasLongTripleRepeat hG S L)
    (hwx : ∀ w, 0 < observedOf hG S ρ w → w ∈ verts)
    (hStruth : Is62Candidate62 ⟨G,hG,S⟩ verts toList id id oMin)
    (hCand   : Is62Candidate62 ⟨G,hG,D⟩ verts toList id id oMin) :
    exactLik hG D (observedOf hG S ρ) ≤ exactLik hG S (observedOf hG S ρ)
```

### The residual regime is isolated, and it is non-empty

`hno` is the long-standing interface hypothesis of
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`. It is an
explicit premise and is **not** claimed to follow from `InformationFeasible`,
because it does not, and this is provable rather than merely suspected:

> **Counterexample to the discharge.** Truth `AAAAB`, `G = 5`, `L = 3`, read at
> all five starts. Verified: clause 1 (coverage) holds; the only triple repeat
> of length `e ≥ L - 1 = 2` is `(2, 0, 1, 2)`, and all three copies are
> bridged, so clause 2 holds; there is no interleaved repeat pair, so clause 3
> holds. All four length-`3` windows are observed, so by §4 the truth *is* a
> genuine §6.2 candidate. Yet `¬ HasLongTripleRepeat` is `False`.

So the wraparound regime of `AssemblyP1.BridgingBridge` is reachable even by a
truth-feasible, full-`I_s` realization. That is why `hno` is left visible in the
statement instead of being discharged. In this particular instance the truth
nevertheless *is* a maximiser over every same-support length-`5` competitor, so
the regime contains no counterexample there — but no theorem is claimed about it.

## 5. An audit finding that strengthens the theorem: `I_s` is not needed

`_hfeas` and `_hR` are unused, and Lean's linter says so; they are underscore-
prefixed to keep it visible. This is structural, not an accident:
`genuine62_molecule_eq` derives the candidate class entirely from the §6.2
certificate, using only `VisitsObserved` and the vertex lower bound of `1`.

So the honest reading of the theorem is stronger than "full `I_s` plus a
certificate suffices":

* the **§6.2 support-spelling restriction, read literally and on its own, is
  enough** to make the truth an exact maximum-likelihood same-length candidate
  over the §6.2-feasible class; and
* the only residual hypothesis is `¬ HasLongTripleRepeat`, a pre-existing
  interface boundary — **not** an `I_s`-derived conclusion.

This relocates where the open difficulty lies. It is not in transferring `I_s`
into the §6.2 candidate class; that transfer is automatic and needs no bridging
theory. It is not in the coverage interpretation either. It is entirely in the
long-triple-repeat regime of `AssemblyP1.BridgingBridge`, and in
`AssemblyP1.BridgingBridge.informationFeasible_tripleRepeat_ge_G_sub_L`'s
unresolved band `max (L-1) (G-L) ≤ e < G`.

## 6. Search evidence for the repaired theorem

The repaired theorem restricted to truth-feasible realizations is consistent with
everything searched, and the search had to be done carefully to mean anything.

An initial formulation with one read per start is **structurally incapable** of
finding a counterexample: with `x_w` = number of starts in `R` carrying `w`, one
has `x_w ≤ d_S(w)` always, and the likelihood is `∏_w (d_C w/N)^{x w}`, so the
truth's own multiplicities dominate. That is why the first search returned
nothing regardless of what was searched. The model allows repeated reads at the
same start, so `x` ranges over all vectors `≥ 1` on the support, and the right
question is whether any same-support competitor `C` has `d_C(w) > d_S(w)` for
some observed `w` — the necessary condition for beating the truth in this class.

Searched that way, over binary truths with `G ≤ 9`, `L ≤ 6`, requiring full
`I_s`, requiring the truth to be feasible (every window type observed, which by
§4 is exactly the honest "truth is a genuine §6.2 candidate" condition), and
requiring the competitor to have the same window support: **no instance found**.
Also searched `G ≤ 7`, `L ≤ 5` over a ternary alphabet: none.

This is evidence, not a completeness proof, and the completeness of the search is
not proved. It is recorded as such.

## 7. What the repository now asserts, and what it does not

**Asserted (kernel-checked, `propext`/`Classical.choice`/`Quot.sound` only):**

* the `AABB`/`ABAB` counterexample, unchanged, as a **negative** theorem about
  the *unrestricted* same-length class;
* `¬ Is62MaximumLikelihood truth competitor`, correctly read as a refutation of
  the **dominance** claim over the §6.2-feasible class;
* the truth is **not** a member of the §6.2 class at that instance;
* the bridge `genuine62_molecule_eq`, `support62_eq_of_genuine62`, and
  `genuine62_is_spelled_candidate`: the §6.2 restriction *equals* the
  spelled-candidate class;
* `informationFeasible_62_maximizer`, the positive same-length maximizer theorem
  over genuine §6.2 candidates, modulo the isolated
  `¬ HasLongTripleRepeat`.

**Not asserted:**

* that the maximizer-with-membership claim of #88 is refuted. It is not, by this
  witness; the membership antecedent fails.
* that `InformationFeasible` implies `¬ HasLongTripleRepeat`, even restricted to
  truth-feasible realizations. `AAAAB` refutes it.
* anything about the residual long-triple-repeat regime beyond its
  non-emptiness.
