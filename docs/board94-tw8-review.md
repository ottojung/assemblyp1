# INDEPENDENT REVIEW — board issue 94, front tw8 (`94-tw8-contraction`, `cd430b4`)

**VERDICT: CHANGES-REQUIRED — `card_contractNodes_lt`, the induction measure and the module's headline
lemma, contains two independent term-level type errors (lines 126 and 146) against the pinned Mathlib
/Lean-core signatures, so the committed source cannot be the source that reported
"`lake build --wfail`: exit 0, 8984 jobs, zero errors".**

Reviewer: front `94-tw8-review`. Reviewer has no stake in the work. **I did not compile.** Everything
below is a static verdict; §"COULD NOT SETTLE" names each remaining gap and the exact command.

---

## 0. WHAT I DID, AND WHAT IT COST

* Read the source **first**, declaration by declaration, then the report.
* Re-derived every line number I cite from the checked-out file (544 lines, matches the commit).
* For the term-level findings I did **not** guess: I fetched, from the exact pinned revisions
  (`mathlib` `5ed2965256430c3649e86755f9576b54eca72435`, `lean4` `v4.34.0`, per `lake-manifest.json`
  and `lean-toolchain`), the source of every lemma whose argument order/unification I rely on:
  `Mathlib/Data/Finset/Disjoint.lean`, `Mathlib/Algebra/Order/BigOperators/Group/Finset{,/Basic}.lean`,
  `Mathlib/Data/Finset/Card.lean`, `Init/Data/Nat/Basic.lean`, `Init/Data/Nat/Lemmas.lean`.
* I also re-fetched the *paper* (ar5iv render of arXiv:1301.0068) even though the brief said not to
  rely on network, purely to check the quoted LaTeX character-by-character. It matched.
* I did not run `lake`, `lean`, `elan` or `make`; I did not create or populate `.lake`; I did not
  read or touch `/workspace/assemblyp1-94-tw7-altf` or any other worktree; I edited no `.lean` file.

**What not compiling cost me.** Three things, stated plainly:

1. I cannot *prove* my two type-error findings; I can only show that the elaborated term has a type
   that is not the goal. The evidence is strong (pinned-source signatures, quoted verbatim in the
   findings) but it is static. A build settles it in one command and I am obliged to say so.
2. I cannot confirm the *positive* instance `GA_ab_contractible` at all: it depends on
   `twiceTraversed_contractible`, which depends on the two theorems containing the errors. Whether
   `by decide` closes the eleven `§6` goals — those need a `Decidable` instance for `Finset.sum` over
   concrete finsets, which I could not locate in the files I read — is unverified.
3. I cannot run `#print axioms`, so the axiom audit below is a *static grep*, not a kernel answer.
   It is a weaker instrument and I have weighted it as such.

---

## 1. DECLARATION-BY-DECLARATION VERIFICATION

`VERIFIED` = I read the step and it is correct at the pinned revisions. `BROKEN` = it does not
elaborate. `PLAUSIBLE` = correct in intent, but rests on something I could not confirm statically.

| lines | declaration | verdict | note |
| --- | --- | --- | --- |
| 22–28 | `length_drop_le'` | VERIFIED | standard; `omega` on `drop` length, no truncated-subtraction issue |
| 31 | `Merge` | VERIFIED as *a* definition, **but a narrowed transcription** | see F3 |
| 35–38 | `structure SeqGraph` + `deriving DecidableEq` | PLAUSIBLE (risk) | see F8 |
| 41–42 | `WellFormed` | VERIFIED | |
| 45–50 | `outEdges`, `inEdges` | VERIFIED | |
| 53–56 | `outDeg`, `inDeg` | VERIFIED | |
| 58–64 | `mem_outEdges`, `mem_inEdges` | VERIFIED | `simp [outEdges]` closes `e.1 = u` by `rfl` |
| 66–76 | `Contractible` | VERIFIED (faithful) | see §2 |
| 79–80 | `contractNodes` | VERIFIED | node set matches the source's merge-and-erase |
| 83–84 | `contractEdges` | VERIFIED *as written*; the source's step 2 is missing | see F2 |
| 88–90 | `Contract` | BROKEN **as a transcription of `Defn. d:condensed`** | see F2 |
| 92–94 | `mem_contractNodes_merge` | VERIFIED | `Finset.mem_union.mpr (Or.inr …)` after delta of `contractNodes` |
| 96–99 | `mem_contractNodes_of_mem` | VERIFIED | `mem_erase.mpr ⟨hxv, mem_erase.mpr ⟨hxu, hx⟩⟩` |
| 102–104 | `edges_contract_subset` | VERIFIED | |
| 107–109 | `mem_contractEdges_of_ne` | VERIFIED | `⟨he, h1, h2⟩` is `And (And …)`; correct |
| 113–118 | `merge_not_mem_erase` | VERIFIED | |
| **121–146** | **`card_contractNodes_lt`** | **BROKEN — two errors, lines 126 and 146** | see **F1** |
| 150–162 | `card_contractNodes_le` | VERIFIED | `card_union_le _ _` then `Nat.le_refl`; fine, and weaker than the `lt` version |
| 166 | `Mult` | VERIFIED as a def; **vacuous parameter** | see F9 |
| 169–174 | `nodeMult`, `inMult` | VERIFIED | |
| 178–179 | `Balanced` | VERIFIED | |
| 181–187 | `nodeMult_ge_of_mem`, `inMult_ge_of_mem` | VERIFIED | `Finset.single_le_sum` = `to_additive` of `single_le_prod [MulLeftMono N] (hf : ∀ i ∈ s, 1 ≤ f i) {a} (h : a ∈ s)`; the two-argument lambda and the trailing membership are the right shape |
| 190–198 | `nodeMult_ge_add` | VERIFIED | `Nat.add_le_add_left (h) k : k + n ≤ k + m` (adds on the **left**, core `Basic.lean:484`) — so this is right, and the `(sum_erase_add …).symm.trans (Nat.add_comm _ _)).symm` chain ends exactly at the calc goal |
| 200–208 | `inMult_ge_add` | VERIFIED | same |
| 211–212 | `EdgeSurj` | VERIFIED | |
| 216–217 | `NoTriple` | VERIFIED | a plain graph-level `Prop`; see §4 |
| 220–241 | `twiceTraversed_outDeg_eq_one` | VERIFIED *modulo F1* | the `by_contra` + card-positivity + `erase`-card + `Nat.add_le_add` + `omega` chain is arithmetically sound and uses no primitivity |
| 244–268 | `twiceTraversed_inDeg_eq_one` | VERIFIED *modulo F1* | `rw [← hBal v …]` transfers the cap correctly |
| 273–278 | `twiceTraversed_contractible` | VERIFIED *modulo F1* | see §3 |
| 282–289 | `not_twiceTraversed_of_not_contractible` | VERIFIED | `Nat.lt_or_ge`; the `(by simp)` at 289 legitimately closes `¬ m e ≤ 1` from the in-scope `h : 2 ≤ m e` |
| 449–453 | `na`, `nb`, `nc` | VERIFIED | |
| 460–467 | `GA`, `mA` | VERIFIED as data | |
| 469 | `GA_nodes` (`:= rfl`) | PLAUSIBLE | |
| 470–476 | `wellFormed_GA` | PLAUSIBLE | depends on `simp` closing `na ∈ GA.nodes`; should close |
| 478–484 | `balanced_GA` | VERIFIED *mathematically* (I checked: 2 = 2 at each node) | `by decide` unverified — see §COULD NOT SETTLE |
| 486–489 | `edgeSurj_GA` | VERIFIED *mathematically* | same caveat |
| 491–494 | `noTriple_GA` | VERIFIED *mathematically* (2 ≤ 2, exactly at bound) | same caveat |
| 497–513 | `mA_ab`, `outDeg_GA_a`, `inDeg_GA_b`, `GA_nodes_three`, `GA_ab_contractible` | PLAUSIBLE | the three `decide`s are arithmetically right; `GA_ab_contractible` is dead while F1 stands |
| 522–526 | `GB`, `mB` | VERIFIED as data | |
| 528–530 | `outDeg_GB_a = 2`, `mB_ab = 3`, `nodeMult_GB_a = 4` | VERIFIED arithmetically | `outEdges GB na = {(na,nb),(na,nc)}`, `3+1=4` ✓ |
| 534 | `not_outDeg_GB_a` | VERIFIED | but see F5 — it is a standalone fact, not a mutation test |
| 537–541 | `not_noTriple_GB` | VERIFIED | `Nat.le_of_eq nodeMult_GB_a.symm` then `4 ≤ 2` by `decide` |

### 1a. The two side conditions you asked me to check specifically

**They are genuinely there, as explicit binder hypotheses, not buried.** `card_contractNodes_lt`
(line 121–123) takes `(hne : u ≠ v)` and `(hw : Merge u v ∉ G.nodes)` as *explicit arguments* of the
theorem, in the open, before the colon. They are not discharged by `simp`, not hidden in an instance,
not weakened. The commit's "stated, not hidden" is **TRUE**. Credit where due — and note that `hw`
is a real burden the source does not impose (see F3), which is a fidelity issue, not a hiding issue.

---

## 2. SOURCE FIDELITY (internal consistency, plus a text check)

I fetched the compiled v3 (ar5iv) and compared the docstring's LaTeX block (file lines 309–326)
against the paper.

* **Lines 310–318 are verbatim correct**, including `d_{\text{out}}(\mathbf{u})=d_{\text{in}}(\mathbf{v})=1`.
* **Lines 321–325 (`\begin{definition}[Condensed sequence graph]`) are verbatim correct.** The published
  number is "Definition 11"; the `.tex` label `d:condensed` is the label the file uses. Fine.
* **Lines 339–347 (the `appendix_short.tex:167` quotation) are verbatim correct**, including
  "Note that the cycle `C_0` does not traverse any node three times in `G_0`, for this would imply the
  existence of a triple repeat of length `K`, violating the hypothesis of the Lemma" and the two
  sentences "the node `u` cannot have two outgoing edges … `d⁺(u)=d⁻(v)=1`".
* **What I could NOT check: the line numbers.** The docstring cites "line 131-132" and "line 140"
  (file lines 332, 334) for parts of the quotation, and `130-141, 167` in the commit. The text is
  right; the `.tex` line numbers are unverifiable from here (the arXiv source tarball is a `.tar.gz`
  I did not unpack, and `paper/` in this repo is a different paper). I am not calling this a finding,
  but the next front should re-derive them once and record that it did.

`Contractible` (75–76) is a faithful transcription of the source's last sentence, with the edge
membership added — correct, and necessary.

So: **no silent strengthening of `Contractible`; one silent narrowing of `Merge` and one silently
dropped half of `Contract`** — F2 and F3.

---

## 3. `twiceTraversed_contractible` — is it the claimed statement, and does it smuggle primitivity?

**Statement: matches the claim.** The appendix's two sentences are: (i) `u` cannot have two outgoing
edges; (ii) `v` cannot have two incoming edges; hence `d⁺(u)=d⁻(v)=1`, hence `(u,v)` has been
contracted. `twiceTraversed_contractible` concludes `Contractible G u v`, which is the
"hence `d⁺(u)=d⁻(v)=1`" half, correctly packaged as "an edge traversed twice is contractible". The
docstring at 270–272 claims "Exactly the two sentences of the appendix's proof, as a rule about the
graph" — that is accurate, and slightly *more* modest than the source, because the final clause "and,
as prescribed in Defn. d:condensed, the edge `(u,v)` has been contracted" is a statement about the
*condensation procedure*, which this module does not run.

One honest addition the paper does not spell out: the in-degree half needs conservation, so the Lean
version takes `Balanced`. That is a correct strengthening of the hypotheses, not of the conclusion,
and the docstring's table names it. Good.

**Smuggling: none.** The proof uses `hCap : NoTriple m` as a hypothesis at 241 and 268. It does not
derive `NoTriple` from anything, does not mention primitivity, `P2`, `Ukkonen`, `deg` or a word
anywhere. Grep of the whole file for `prim|P2|Ukkonen|deg|Period|vtx|Span` returns hits only in
docstring prose (lines 374, 378, 396–399) — never in a term. I checked this carefully because it was
the highest-order risk in the brief. **It does not materialise.** See §4.

---

## 4. WHERE PRIMITIVITY ENTERS

The commit says: primitivity enters in exactly **one** hypothesis, `NoTriple`, and that hypothesis is
RELAYED from tw6.

**The count is right, and the truth is stronger and better than the claim: the number of Lean-level
primitivity dependencies is ZERO.** `NoTriple` (216–217) is `∀ u ∈ G.nodes, nodeMult G m u ≤ 2` — a
graph statement about a multiplicity function. No identifier from `Issue94TW6Lemma1` occurs anywhere
in the file. I checked what tw6 actually proves and what it claims:

* tw6 **proves** `deg_fact_of_primitive` (its line 463), `no_three_of_primitive` (479),
  `no_three_of_P2` (563), `prim_deg_le_two` (575) — each of which carries
  `hprim : ∀ d, 0 < d → d < G → ¬ Period hG S d` **as a hypothesis**, and `P2` as a hypothesis.
* tw6 **refutes** the unrestricted form at `S = 012012012`, `G = 9`, `K = 3` (its §7,
  `no_tripleRepeat_012012012` at its line 716, and the length-4 and length-8 variants at 721 and 726).
  Its §7 docstring (`Issue94TW6Lemma1.lean` lines 655–662) is in fact *honest*: it says the
  unrestricted form is false, and explains the instance via `escape_iff_leastPeriod`. Its §0
  docstring (lines 26–40) likewise announces the dichotomy rather than overclaiming.

**Therefore: if tw6's overclaim were true, tw8 would not change by one line.** This is the finding
the brief asked for and it is a *clean* one. What tw8 loses by not depending on tw6 is redundancy
and honesty of the RELAYED framing, not soundness.

**But the RELAYED framing is imprecise, and this is F4.** `prim_deg_le_two : deg hG L S v ≤ 2` is a
statement about `BBTSequenceGraph.deg` (occurrences of a `(L-1)`-mer in a circular word).
`NoTriple` is a statement about `nodeMult` (a sum of edge multiplicities in an abstract
`SeqGraph`). These are not the same predicate, and no theorem in the repository identifies them. The
docstring says so at 396–399 (§6 item 2) and the report says so in §6.14 ("this is the identification
(B3)+(B4) … and I did **not** build it"). So the module is honest; the *commit message's* wording
"`NoTriple` … i.e. tw6's `deg_fact_of_primitive` / `prim_deg_le_two`, RELAYED" overstates: nothing is
relayed at the Lean level, and the identification is the missing lemma of §6.2, not a naming
convention.

`EdgeSurj` supplies `1 ≤ m e₂` (line 239/263) exactly as the table claims — I checked the `omega` step.
`Balanced` transfers the cap to the head at 265–267 — checked.

---

## 5. THE `SeqGraph` LAYER — is it load-bearing?

**Partly. The layer is justified; the justification given is arithmetically false.**

* What `BBTSequenceGraph` actually is: a **namespace of functions**, not a graph type. It has `vtx`
  (`BBTCondense.lean:203`, type `Fin (L-1) → α`), `deg` (213, `nodeCount`), `inDeg` (213), `fibre`,
  `Branch`, `branchStarts`. There is **no node finset, no edge finset, and no contraction operation
  anywhere in the repository** — I grepped every `structure … where` in `AssemblyP1/` for a
  node/edge/graph structure: the only hits are this new `SeqGraph` and `Section62BidirectedFlow.BdEdge`.
  So a *graph-level* contraction is not expressible in the existing layer at all.
* **The stated reason is wrong.** The commit-adjacent report (lines 152, 518, 607) and the report's
  §8 item 2 say a merged node "has length `2K-1` and not `K-1`", and that this is why
  `BBTSequenceGraph`'s `Fin (L-1) → α` cannot hold it. `Merge u v = u ++ v.drop (u.length - 1)`, so
  for `|u| = |v| = K` the length is `K + (K - (K-1)) = K+1`, **not `2K-1`**. `2K-1` would be the
  length at overlap `1`; the source's overlap for consecutive `(L-1)`-mers is `K-1`. And even that
  would be no obstacle: `Fin (K+1) → α` is just as available as `Fin (K-1) → α`, so the *type* never
  blocks anything. The real reason for the new layer is the absence of an edge multiset — which is a
  good reason, and which the file never states.

See F5.

---

## 6. THE TWO `decide` INSTANCES, AND THE MUTATION CLAIM

* **Positive instance `GA`**: I verified the mathematics by hand. `GA` is a 3-cycle with every edge
  used twice. `Balanced`: 2 = 2 at every node ✓. `EdgeSurj`: `1 ≤ 2` ✓. `NoTriple`: `2 ≤ 2`, exactly
  at the bound ✓. `outDeg GA na = 1`, `inDeg GA nb = 1` ✓. The hypothesis class is non-empty and the
  conclusion is a specific, checkable value. **This instance is a genuine test** — provided the two
  `decide`s that reach it (F1) go green.
* **Negative instance `GB`/`mB`, and the "mutation goes red" claim: the claim is an ASSERTION, not an
  argument, and for the theorem it is attached to it is not even true.** This is F5 and it is the
  most important *methodological* finding after F1.

---

## 7. AXIOMS AUDIT (static substitute for `#print axioms`)

Static grep of the whole file for `sorry`, `sorryAx`, `admit`, `native_decide`, `@[implemented_by]`,
`partial`, `unsafe`, `opaque`: **no hits in any term.** The only two textual hits are the English
words inside the docstring — line 297 ("condensation step") and line 426 ("No `sorry`, no `admit`, no
`native_decide`, no new axiom").

* **`native_decide` appears nowhere in this file.** It appears nowhere in its import closure *as used
  here* either — every `decide` in the file is plain `decide` (lines 482–484, 489, 494, 497, 501, 502,
  507, 513, 528–530, 534, 539, 541); the `decide +kernel` instances the commit advertises are in
  **tw6's** file, not this one. Plain `decide` reduces through the kernel and is not an
  `implemented_by` escape hatch, so nothing here can bypass the kernel.
* **`§6` in the file says "Every numeric statement below is decided by `decide +kernel`" (line 440)
  and "Every numerical statement in §6 is `decide +kernel`" (line 426). That is FALSE as written.**
  The §6 goals are `by decide`, not `by decide +kernel`. `+kernel` only affects the display of the
  term, not its trustworthiness, so nothing is *invalidated* — but a front that writes `decide +kernel`
  when it wrote `decide` is describing a check it did not perform. See F7.
* **Declaration count.** I count **56** top-level `theorem`/`def`/`structure`/`instance`
  declarations. `AssemblyP1.lean` gains exactly **34** `#print axioms …Issue94TW8Contraction.*`
  lines. So 34 is the *audit* count, and the commit's phrase "Axioms audit for **every added
  declaration**" is literally false: 22 added declarations are unaudited, including
  `mem_outEdges`, `mem_inEdges`, `GA_nodes`, `GA_nodes_three`, and the eight data `def`s. None of
  those can carry `sorryAx` in practice, but the sentence overclaims. See F7.
* No new `axiom`, no `set_option` weakening (the file sets three *linter* suppressions, lines 7–9,
  none of which is `maxHeartbeats`/`maxRecDepth`), and no `import` of anything but existing modules.

---

## 8. ITS OWN "NOT ESTABLISHED" LIST (docstring lines 386–427) — IS IT HONEST?

**It is honest, and it is the best part of the submission.** Item-by-item:

| claimed gap (docstring) | my check |
| --- | --- |
| 1. `hPevzner` at `PopulationUniqueness.lean` **164, 217, 247** | **Line numbers are exactly right.** `(hPevzner : EulerianCycleObstruction (α := α) L) :` occurs at 164, 217, 247 (and is consumed at 194, 227, 250). It is untouched by this commit. ✓ |
| 2. word → `K`-mer bridge not proved; `NoTriple` from `prim_deg_le_two` is the missing lemma | ✓ accurate, and it is the *real* content of §4 above |
| 3. order-independence not proved; only the measure (well-foundedness half) is proved | ✓ accurate, and honest about the difference |
| 4. label/overlap half not proved | ✓ accurate but **understated** — see F2, the *unlabelled* half is also missing |
| 5. push-forward / quantitative inheritance of `l:condensed` (3) not proved | ✓ accurate |
| 6. the "at most once" conclusion in the condensed graph not proved | ✓ accurate |

So the report **understates** rather than overstates its gaps — which the brief names as the dangerous
direction for this board, and it does not happen here. The one place it understates is item 4 (F2),
and it understates in the *honest* direction (it lists a smaller gap than the real one). Two claims
*outside* the list are overstated: the `decide +kernel` claim (F7) and the axioms claim (§7).

---

## 9. THE SECTION 9 RECOMMENDATION

`nodeMult_truthMult_eq_deg` + its `NoTriple`-from-`P2` corollary as "the single most valuable next
step": **substantially right, but the "unique" claim is not established and cannot be.**

* **Right:** the bridge is genuinely the only place a word-level fact can enter this module, and the
  module is currently consumer-less. Naming `KMerGraph`/`TruthMult` as the missing objects is exactly
  the right diagnosis.
* **The uniqueness claim is overstated.** The report itself lists three further missing items
  (order-independence, the push-forward, the "at most once" conclusion) that are all *prerequisites*
  for BBT Theorem 3, and §8 item 9 of the report says outright that §6.3 and §6.5 are "pure graph
  theory on machinery that now exists". That last sentence is also **false today**: the machinery does
  not exist, because `card_contractNodes_lt` does not compile (F1). The recommendation is
  contingent on F1 being fixed first, and the report does not say so.
* **A concrete defect in the recommended signatures:** the proposed `nodeMult (KMerGraph hG L S)
  (TruthMult hG L S) v = deg hG L S v` is stated at `v : Fin (L-1) → α`, i.e. in
  `BBTSequenceGraph`'s node type, while `nodeMult` in this module takes `u : List α`. The next front
  will hit this representation mismatch before it hits any mathematics. It should be planned for.

---

## 10. THE COMMIT MESSAGE, READ AS A CLAIM

| claim | verdict |
| --- | --- |
| "disjoint from sibling front 94e8's `AltF = id` step" | **ACCEPTABLE as a plan claim, and I checked it is a plan claim.** The file contains no Eulerian-cycle machinery, no `AltF`, no chord argument. It does not cite, import or need any 94e8 artifact, and the report's §6.14 marks tw5's "`Ukkonen` + label preservation ⇒ the innermost-chord step is free" as **RELAYED, "no theorem of mine depends on it"**. So the phrase does not assert that 94e8's work exists or succeeded. It would have been a finding had it asserted a result; it does not. |
| "`Merge`, `Contractible`, `Contract` are transcriptions of `Defn. d:condensed`" | **PARTLY UNSUPPORTED.** `Merge` is a narrowed transcription, `Contract` omits the source's entire second step. F2, F3. |
| "`card_contractNodes_lt` — the induction measure: every contraction strictly decreases the node count" | **UNSUPPORTED AS WRITTEN.** The statement is right; the proof has two type errors. F1. It also measures *this module's* `Contract`, not the source's contraction (F2), so even once fixed it is the measure of a slightly different operation. |
| "`u ≠ v` and freshness … stated explicitly rather than assumed away" | **VERIFIED TRUE.** |
| "`twiceTraversed_contractible` — the appendix's two sentences, as a theorem" | **VERIFIED TRUE** modulo F1. |
| "§6, two `decide +kernel` instances … so `NoTriple` … is load-bearing" | **THE INFERENCE IS AN ASSERTION**, and for the theorem it names it does not follow. F5, F7. |
| "`NoTriple` … i.e. tw6's `prim_deg_le_two`, RELAYED and not re-derived" | **OVERSTATED** as a dependency claim; harmless as a provenance claim. F4. |
| "`hPevzner` … at lines 164, 217, 247 is untouched" | **VERIFIED TRUE**, line numbers exact. |
| "`lake build --wfail`: exit 0, 8984 jobs, zero errors, zero warnings" | **CONTRADICTED BY THE COMMITTED SOURCE.** F1. This is the finding that makes the verdict CHANGES-REQUIRED. |
| "Axioms audit for every added declaration" | **FALSE** (34 of 56). F7. |

---

## FINDINGS

### MUST-FIX

**F1 — CRITICAL — `AssemblyP1/Issue94TW8Contraction.lean:126` and `:146` — `card_contractNodes_lt`
does not typecheck. Two independent term-level errors in the module's headline lemma.**

*(a) line 124–126.*
```lean
have hdisj : Disjoint ((G.nodes.erase u).erase v) ({Merge u v} : Finset (List α)) := by
  refine Finset.disjoint_left.2 (fun {a : List α} h1 h2 => ?_)
  exact merge_not_mem_erase G u v hw (Finset.mem_singleton.mp h2 ▸ h1)
```
At the pinned Mathlib revision `5ed2965`, `Mathlib/Data/Finset/Disjoint.lean:47` reads, verbatim:
```lean
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
```
So `.2` discharges the goal down to `a ∉ ({Merge u v} : Finset (List α))`, i.e. `¬(a = Merge u v)`,
where `a` is the lambda's rigid binder. The supplied term is a different proposition:
`Finset.mem_singleton.mp h2` cannot be applied at all, because `h2 : a ∉ {Merge u v}` is the
*negation* of the `a ∈ {Merge u v}` that `mem_singleton.mp` consumes; and even granting the
`▸`, the term `merge_not_mem_erase G u v hw X` is `¬(Merge u v ∈ (G.nodes.erase u).erase v)`, which
is about `Merge u v` and about the erase set, not about `a`. There is no higher-order reading that
makes the binder `a` disappear. The goal is *true* and trivially so — `hw` alone gives
`Merge u v ∉ (G.nodes.erase u).erase v` — but the term supplied proves something else.
Repaired in one line, e.g. `exact fun hmem => hw ((Finset.mem_erase.mp ((Finset.mem_erase.mp hmem).2)))`.

*(b) line 146.*
```lean
rw [hA']
exact Nat.sub_lt hpos (show (0 : ℕ) < 1 by decide)
```
At `lean4 v4.34.0`, `Nat.sub_lt` is fixed by `Init/Data/Nat/Lemmas.lean:356–357`
(`sub_lt_of_pos_le (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b := Nat.sub_lt (Nat.lt_of_lt_of_le h₀ h₁) h₀`),
i.e. `Nat.sub_lt (h : n < n + m) (h0 : 0 < m) : n - m < n`. With the goal
`G.nodes.card - 1 < G.nodes.card` this demands a proof of `G.nodes.card < G.nodes.card + 1` in the
first slot. `hpos : 0 < G.nodes.card` is not that, and is not defeq to it. Repaired by
`Nat.sub_lt (by omega) (by decide)` or `Nat.sub_lt_of_pos_le (by decide) (Nat.le_refl _)`.

Why it matters: `card_contractNodes_lt` is the module's raison d'être — the commit's second bullet,
the docstring's second bullet, and the thing the induction of `Defn. d:condensed`'s fixpoint clause
consumes. While it fails, `hdisj` and `hA` fail, so the statement has no proof at all; and the
commit's recorded build result cannot be a build of *this* file.

Confidence: high. Evidence is pinned-source text, not recollection, and I re-derived both
signatures. But I did not compile, and I say so.

**F2 — MUST-FIX — `AssemblyP1/Issue94TW8Contraction.lean:83–90`, docstring 86–87, commit message
bullet 1 — `Contract` is not a transcription of `Defn. d:condensed`; the source's second step is
absent.**
```lean
def contractEdges (G : SeqGraph α) (u v : List α) : Finset (List α × List α) :=
  G.edges.filter (fun e => e.1 ≠ u ∧ e.2 ≠ v)
```
The source (docstring 313–318, verified verbatim against the paper) says contraction "entails two
steps: first, merging `u` and `v` along `e` to form a new node `w = …`, and, **second, edges to `u`
are replaced with edges to `w`, and edges from `v` are replaced by edges from `w`**". `contractEdges`
performs only the *erasure*; it never creates an edge incident to `w`. The contracted graph is
therefore missing every `w`-incident edge, and is not the source's condensed graph. The docstring
calls this "the source's one-step contraction `Defn. d:condensed` (§3)" and the commit message calls
`Contract` a transcription of the definition. Both are unsupported. This also means
`edges_contract_subset` / `mem_contractEdges_of_ne` (§6 item 5's "forward half") are correct about
*this* operation, not about the source's. The honest fix is either to implement the replacement step
(which needs the edge multiset and the overlap, i.e. F3) or to rename and re-document `Contract` as a
node-and-edge *reduction* and drop the transcription claim.

**F3 — MUST-FIX — `AssemblyP1/Issue94TW8Contraction.lean:30–31` — `Merge` silently hardcodes the
overlap, and the docstring's own formula does not describe the definition.**
```lean
/-- The merged node of `Defn. d:condensed`: `u_1^end v_{olap(u,v)+1}^end`. -/
def Merge (u v : List α) : List α := u ++ v.drop (u.length - 1)
```
The source's `w` depends on `olap(u,v)`, a datum of the edge. `Merge` has no overlap parameter and
silently fixes `olap(u,v) = u.length - 1` (the maximal self-overlap, which *is* the right value for
consecutive `(L-1)`-mers of a de Bruijn graph — so the intended use is unaffected, but the
definition is a narrowing of the source's rule, and the docstring quotes a formula the definition
cannot express). Related: the `hw : Merge u v ∉ G.nodes` side condition of F1's theorem has no
counterpart in the source, where `w` is a new node by fiat.

### SHOULD-FIX

**F4 — `AssemblyP1/Issue94TW8Contraction.lean:374` and commit message — "`NoTriple` … i.e. tw6's
`deg_fact_of_primitive` / `prim_deg_le_two`, RELAYED" is not accurate as a dependency statement.**
`NoTriple` bounds `nodeMult` on an abstract `SeqGraph`; `prim_deg_le_two` bounds `deg` on a
`(L-1)``-mer` multigraph of a circular word. No theorem in the repository identifies them; that
identification is the missing lemma of §6.2 / §9. Nothing from tw6 is used at the Lean level (which
is *good* — see §4), so the honest phrasing is "the hypothesis that would be discharged by
`prim_deg_le_two` once the bridge exists". Related NOTE: `import AssemblyP1.Issue94TW6Lemma1` and
`open AssemblyP1.Issue94TW6Lemma1` (lines 2, 18) are dead weight — no name from that 750-line module
is used. Dropping them would make the module's independence from tw6 structural rather than
incidental.

**F5 — `AssemblyP1/Issue94TW8Contraction.lean:509–512, 515–521, 532–534` — "the mutation goes red" is
an assertion, and for the theorem it is attached to it does not follow.** `not_outDeg_GB_a` is a
standalone `by decide` fact about `GB`. Nothing in the file discharges `WellFormed GB` or
`EdgeSurj mB`, and — decisively — **`Balanced GB mB` is FALSE**: at `na`, `nodeMult = 3 + 1 = 4` while
`inMult = 1`. So `GB`/`mB` is a valid refutation of `twiceTraversed_outDeg_eq_one` with `NoTriple`
dropped (whose hypotheses are `WellFormed`, `EdgeSurj`, `2 ≤ m (u,v)` — all satisfiable here, and
indeed the file proves the last), but it is **not** a refutation of
`twiceTraversed_contractible` with `NoTriple` dropped, because that theorem also needs `Balanced`.
The docstring at 532–533 ("Dropping `NoTriple` makes the conclusion of the rule false on this
instance") and the commit message's "so `NoTriple` … is load-bearing" both read as claims about "the
rule" (= `twiceTraversed_contractible`). As written they are only claims about the out-degree half.
This is the finding the brief specifically asked for: *would it go red if the degree fact were
removed?* — **Not as a test. Nothing was mutated.** The honest statement is "we exhibit a traversal
satisfying `WellFormed`, `EdgeSurj` and `2 ≤ m (u,v)` for which the conclusion of the out-degree half
is false and `NoTriple` fails"; a real mutation test would be a file where the *same* hypotheses are
discharged and the theorem is stated with `NoTriple` removed.

**F6 — report lines 152, 518, 607, §8 item 2 — the "length `2K-1`" justification for the new
`SeqGraph` layer is arithmetically false.** `Merge u v` has length `K+1` at `|u| = |v| = K`, not
`2K-1`; and the node *type* was never the obstacle (`Fin (K+1) → α` is as available as
`Fin (L-1) → α`). The layer **is** load-bearing, but for a different and better reason that the file
never states: `BBTSequenceGraph` is a namespace of functions with no node finset, no edge finset and
no contraction operation, so no graph-level statement is expressible there. State that instead. A
`NOTE` attached: `SeqGraph` nodes are `List α` while the whole repository speaks `Fin (L-1) → α`, so
the §9 bridge will need a conversion lemma before it can even be stated.

**F7 — `AssemblyP1/Issue94TW8Contraction.lean:426, 440` and commit message — the audit/verification
claims overstate what was done.** The file says "Every numerical statement in §6 is `decide +kernel`"
and "Every numeric statement below is decided by `decide +kernel`"; the goals are `by decide`. `+kernel`
changes only the printed form, so nothing is *invalidated*, but the text describes a check that was
not performed. The commit says "Axioms audit for **every added declaration**"; 34 of 56 added
declarations are audited. Both should be corrected to what is true.

### NOTE

**F8 — `AssemblyP1/Issue94TW8Contraction.lean:35–38` — `deriving DecidableEq` for `SeqGraph α` with no
`[DecidableEq α]` in scope.** `SeqGraph` has no instance parameter, and the file-level
`variable {α : Type} [DecidableEq α]` (line 20) is *after* nothing — it is before, at line 20, so the
instance *is* in scope at line 38 and the deriving can pick it up. I flag it only because I could not
confirm the deriving handler's behaviour for a parameter-only instance, and it is the kind of thing
that is a one-line fix if it is not.

**F9 — `AssemblyP1/Issue94TW8Contraction.lean:166` — `def Mult (G : SeqGraph α) : Type := (List α × List α) → ℕ`
ignores `G` entirely.** So `Mult GA` and `Mult GB` are the *same type*, `mA` and `mB` are
interchangeable, and every `m : Mult G` binder is really a binder over a bare function. Harmless
today; it is a trap for the §9 bridge, where `TruthMult hG L S` will be a function of `(hG, L, S)`.

**F10 — shadowing.** `outDeg`/`inDeg` shadow nothing (tw8's own namespace wins), but `inDeg` already
exists at `BBTCondense.lean:213` in the *opened* namespace `AssemblyP1.BBTSequenceGraph`, and `deg`
(and `vtx`, `inDeg`) are brought into scope by line 16. Any later edit in this file that writes a
bare `inDeg` expecting the repository's meaning will silently get tw8's. Worth a note in the module.

**F11 — what I could not break.** The mathematics of §1–§3 and §6 that I *could* check is correct and
careful. In particular: the `twiceTraversed_outDeg_eq_one` argument (contrapositive, card positivity
of the erase, the `Nat.add_le_add` step, the `absurd`) is right; the `Balanced` transfer at 265–267 is
right; `nodeMult_ge_add`'s `sum_erase_add … Nat.add_comm …` chain ends at exactly the calc goal
(I checked `Finset.sum_erase_add [DecidableEq ι] (s) (f) {a} (h : a ∈ s)` = the `to_additive` of
`prod_erase_mul`, and `Nat.add_le_add_left` really does add on the left); the side conditions are
genuinely explicit; the two quoted LaTeX blocks are verbatim; the 14 self-declared gaps are honest and
the `hPevzner` line numbers are exact. The failure is concentrated, not diffuse: three transcription
and two elaboration defects in the presentation layer, on top of correct pure graph theory.

---

## COULD NOT SETTLE STATICALLY — and the exact command for each

| # | what I could not settle | command that settles it |
| --- | --- | --- |
| C1 | **Whether F1(a) and F1(b) are really elaboration errors.** I verified the two governing signatures at the pinned revisions, but I did not run the elaborator. | `cd /workspace/assemblyp1-94-tw8-review && export PATH=/home/lubko/.elan/bin:$PATH && lake env lean AssemblyP1/Issue94TW8Contraction.lean` — expect two errors, at 126 and 146. This is the single most valuable command in this document; it takes seconds, not a build. |
| C2 | Whether the file compiles at all *as a whole* (e.g. the `deriving` of F8, the `simp`-based `wellFormed_GA`, the `decide`s). | `lake build AssemblyP1.Issue94TW8Contraction` (then `lake build` for the whole library) |
| C3 | **The axioms claim.** I did a grep; I did not run the kernel's own audit. | `lake env lean` on a scratch file containing `#print axioms AssemblyP1.Issue94TW8Contraction.<name>` for each of the 34 (or 56) names, or simply `lake build` and read `AssemblyP1.lean`'s `#print axioms` output — `lake build` prints `depends on axioms: [propext, Classical.choice, Quot.sound]` per declaration. |
| C4 | Whether the eleven `§6` `by decide` goals close, i.e. whether a `Decidable` instance is synthesised for `∑ e ∈ outEdges GA na, mA e` over a concrete `Finset`. This is the one thing in the positive instance I could not reason my way to. | `lake env lean AssemblyP1/Issue94TW8Contraction.lean` (C1) — the errors at 126/146 will be reported together with any `failed to synthesize Decidable` |
| C5 | Whether the `decide`s are *trustworthy*, i.e. whether any of them silently goes through `native_decide` via an `implemented_by` in the import closure. I grepped the file; I did not audit Mathlib. Plain `decide` cannot use `native_decide`, so the risk is low, but the audit is a file-level grep only. | `lake env lean` with `set_option debug.skipKernelTC false` and inspect; or `grep -rn "implemented_by" .lake/packages/mathlib/Mathlib | grep -i finset` |
| C6 | The `.tex` line numbers `130-141`, `167`, `131-132`, `140` cited in the docstring and commit. I verified the *text*; not the *line numbers*. | unpack the arXiv e-print and `sed -n '130,141p;167p' appendix_short.tex` |
| C7 | Whether the report's §3 baseline/build numbers (`8984 jobs`, the `1ee7db8` baseline) describe this file. Given F1, I doubt the `exit 0` does. | `git checkout 1ee7db8 && lake build` then `git checkout cd430b4` and rebuild, comparing logs |
| C8 | Whether the sibling front 94e8's worktree contains anything relevant. I did not read it, by instruction. | out of scope for this review |
| C9 | Whether the `Merge` narrowing is *benign in the intended application* — i.e. that `olap(u,v) = |u| - 1` for the actual `K`-mer multigraph's edges. It almost certainly is (consecutive `(L-1)`-mers overlap in `K-1` positions), but it is nowhere stated in the file. | a one-line lemma, or `BBTSequenceGraph.vtx`/`nextPos` inspection |

---

## NOT ESTABLISHED (not checked at all)

* I did **not** verify the report's §3 build/warning numbers, its baseline-at-`1ee7db8` claim, or any
  other measurement in it, other than as noted in C7.
* I did **not** check tw6's own correctness. I read what tw6 proves and what its docstrings claim
  (lines 26–40, 655–662, 463–584, 716–726) and used that only to answer "does tw8 depend on the
  overclaim?" — I did not audit tw6's proofs.
* I did **not** evaluate whether the *source's* contraction, as opposed to tw8's, is what BBT needs
  downstream, and I did not evaluate the §9 proposed statements' mathematical difficulty.
* I did **not** check the report's §2–§6 prose line by line; I checked the claims I was asked about
  (§6's 14 items, §7's mutation, §9's recommendation, §10's refs) and the 2K-1 claim.
* I did **not** read `/workspace/assemblyp1-94-tw7-altf`, `ottojung/antonina`, `ottojung/skrynia`,
  `ottojung/skrynia-apps` or `ottojung/volodyslav`. Read-only on all of them; I wrote no ref but my own.
* I did **not** check the other 20 issues in the repository, and make no claim about them.

---

## I DID NOT COMPILE

Stated for the record, and it is the honest boundary of this review: I ran no `lake build`, no
`lake env lean`, no `lean`, no `elan`, no `make`; I created and populated no `.lake`; I symlinked no
shared `.lake`; I did not touch any worktree other than this one. **This cost the review:** the
ability to *close* — F1 is a static argument from pinned upstream sources, not a compiler diagnostic,
and the correct epistemic label on it is "I read it and I am confident it does not elaborate", not
"I watched it fail"; the eleven `§6` `decide` goals, which I could not evaluate at all; the
`deriving` question; and any kernel-level axiom audit. A single `lake env lean
AssemblyP1/Issue94TW8Contraction.lean` — not a build, a single-file elaboration — would have converted
the central finding from a well-evidenced static claim into a certainty, and I recommend the human who
owns the compilation window run exactly that before anything else in this report is acted on.
