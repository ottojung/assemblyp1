# BOARD94-TW6-REVIEW

**Role:** INDEPENDENT REVIEW of front tw6 / agent 94d9, issue 94, tranche
`94-tw6-lemma1` at `1ee7db8143f4e3194072192d4ff2383cd65d8c2c` (base `e3fe5a5`
= `origin/94-tw5-lambda`).
**Review worktree:** `/workspace/assemblyp1-94-tw6-review`, branch
`review/94-tw6-lemma1`. No other worktree, worktree-free repo, or ref touched.
**No compilation was run** — see §4 for the hard limit this puts on the
verdict and for the exact commands a later pass must run.

---

## 0. VERDICT: **APPROVE-WITH-FINDINGS**

The tranche is mathematically sound as far as static reading and hand
arithmetic can establish. I could not break a single proof step. In
particular the counterexample is **correct** (independently re-derived by
hand, §2), the central dichotomy is genuinely proved and not resting on a
smuggled hypothesis (§1), and every file-and-line number in the author's
report that I checked is correct (§3).

Two **must-fix** findings, both documentation-honesty, neither touching a
theorem. One report claim is **false** and is the most consequential thing I
found (§1.4): the author speculated that `prim_deg_le_two` is *not* derivable
from work already in the tree; it is derivable in about five lines using the
author's own theorem. Sibling fronts must not spend effort re-deriving the
§2.4 corollaries.

Nothing here blocks merge of the code. Both must-fixes are one-sentence edits
and should be made by whoever integrates.

---

## 1. THE CLAIMS I ATTACKED, AND MY INDEPENDENT FINDING ON EACH

### 1.1 The central claim: `deg_fact` / `deg_fact_of_primitive` and corollaries

I read `AssemblyP1/Issue94TW6Lemma1.lean` line by line, with the definitions
it consumes (`BBTUniqueEulerian.lean:130-160, 300-360, 420-500, 546, 610`;
`BBTCondense.lean:201-208`; `OrientedRigidity.lean:644`; `SourceFaithfulIs.lean:90-129`;
`P2.lean:70-110`; `RepeatAdapter.lean:78-88`) open in front of me.

**Verdict: each step follows. The statement is what its name and the report
say it is.**

The load-bearing step is `max_span_tripleRepeat` (lines 276-377), and it is
correct, including the subtle part:

* `hmax` / `hlong` (282-289) encode maximality of `e* = spanMax` over **all**
  triples, and the only `omega` obligations are pure `ℕ` arithmetic on
  `spanMax` and `G` — no `Fin`-coercion atoms. Sound.
* The "following" flank (291-305) is right: `d < e* + 1` splits into
  `d = e*` (use the hypothesis) and `d < e*` (use `hag ⟨d, hd'⟩`); the
  transitivity `hcon.1.trans hcon.2` is the right composition.
* The "preceding" flank (312-376) is the interesting one and it is valid: from
  `¬(Preceding a = Preceding b ∧ Preceding b = Preceding c)` it builds a
  `TriAgreeAt` at length `e* + 1` for the back-shifted starts
  `a.val + G - 1, …`, using `cyc_back` for `d = t + 1` and `preceding_eq` for
  `d = 0`; the ℕ-starts are then pushed into `Fin G` by
  `agr3_of_triAgreeAt`, using `e* + 1 ≤ G` and the fact that
  `rotAdd hG (G-1)` is injective, so the shifted triple is still three
  pairwise distinct starts. That contradicts `hlong`. This is a genuine and
  correct avoidance of the two-sided extension engine, and it is exactly the
  loophole `docs/bbt-unique-eulerian-89.md` §4 describes. Good mathematics.
* `max_span_escape` (384-399): `spanMax ≤ G` plus `¬ spanMax < G` gives
  `spanMax = G`; `Agr3 … G` gives each pair a period `sh a b` via
  `period_of_agree_all`; `sh a b < G` (hence `0 < p < G`) follows from
  `a ≠ b` and `sh_lt`. Sound.
* `max_span_escape_congruent` (403-422) is sound, and note it recomputes
  `hdAC` twice and then *discards* the first (`hdAC'` from `sh_dvd_trans`) —
  dead intermediate, harmless.
* `deg_fact` (436-454) is exactly the disjunction it claims; `deg_fact_of_primitive`
  (463-471) is `deg_fact` with the second disjunct eliminated by the stated
  `hprim`. **No unstated primitivity assumption anywhere**: the primitivity
  hypothesis is an explicit, named argument, and `deg_fact` (the
  unrestricted form) does *not* silently carry it.
* The `Ukkonen`/`P2` corollaries (541-585) instantiate `hUkk.1` at the
  witnessed `e'` and contradict `K ≤ e'.val` with `e'.val < L - 1`; the `K = L-1`
  unification in `no_three_of_Ukkonen_L` (559) works because `hKL` becomes
  `rfl`; `prim_deg_le_two` (575-585) uses `vtx_agr3` at `L := (L-1)+1`, whose
  result type `((L-1)+1-1)` is *definitionally* `L - 1` (both reduce to
  `Nat.pred L`), so the unrewritten `exact` at 582-583 is legitimate.

Two things I checked specifically because the brief asked:

* **`omega` on `Fin`-coercion atoms.** The only three such uses in the file are
  lines **349, 354, 359** (`a.val + G - 1 = a.val + (G - 1)` and its two
  siblings). Every other `omega` in the file is on pure `ℕ` goals
  (143, 154, 169, 289, 299, 326, 362, 375, 388, 443, 445, 446, 453, 551, 559,
  579, 653). So the author's §6.11 warning is *not* violated except in three
  places — and those three are the **same shape as
  `BBTUniqueEulerian.lean:212`** (`by omega` on
  `a.val + (b.val + G - a.val) = b.val + G`), which is in the tree at `e3fe5a5`
  and therefore compiled. I judge the risk at 349/354/359 to be low; see §4.
* **A silently strengthened hypothesis.** I looked for one and found none,
  but I did find the opposite defect: **`h3 : 3 ≤ G` is unused in every
  theorem of the module** (see finding 3). No theorem is weakened; a redundant
  hypothesis is carried instead, which is harmless but should not be
  advertised as load-bearing.

### 1.2 The counterexample — **CORRECT**, independently re-derived

I did not compile anything. I read the definitions and did the arithmetic by
hand, twice, from `SourceFaithfulIs.Genome` (`cycl` is `S.sym ⟨i % S.len, _⟩`,
`window e r d = S.cycl (r.val + d.val)`, `Preceding t = S.cycl (t.val + S.len - 1)`,
`IsTripleRepeat` is the 10-conjunction at `SourceFaithfulIs.lean:122-128`) and
from `deg`/`nodeCount` (`BBTCondense.lean:207`, `OrientedRigidity.lean:644`:
`nodeCount` is the card of `{r | nodeWindow r = k}`).

`S9 = 012012012` (`![true,false,false,true,false,false,true,false,false]`,
line 665-666).

1. **Length and shape.** `G = 9`, `S9` is `0,1,2,0,1,2,0,1,2`. **Yes**, length 9,
   period 3. ✔
2. **`vtx9_three` (696-700).** `vtx hG9 4 S9 r` is the 3-mer at `r`; the
   3-mers at `0, 3, 6` are `(0,1,2) = ![true,false,false]`, `(3,4,5)`, `(6,7,8)`
   — all identical. ✔ **Three distinct starting positions really agree at
   `K = 3`.**
3. **`deg9_012` (704-705).** Starts spelling `012` are exactly those `r ≡ 0
   (mod 3)`, i.e. `{0,3,6}`; residues 1 and 2 spell `120` and `201`. So the
   card is **3**. ✔ **The node is traversed exactly three times.**
4. **`no_tripleRepeat_012012012` (715-717).** `IsTripleRepeat 3 0 3 6` requires
   `¬(Preceding 0 = Preceding 3 ∧ Preceding 3 = Preceding 6)`. `Preceding t =
   S[t - 1 mod 9]`, so `Preceding 0 = S[8] = false`, `Preceding 3 = S[2] =
   false`, `Preceding 6 = S[5] = false`. All three equal, so the maximality
   clause **fails** and the triple repeat does not exist. ✔ The `1 ≤ e`,
   `e < 9`, distinctness and three-fold `Agree` clauses all hold, so the
   failure is genuinely in the maximality clause — which is the whole point.
5. **`no_tripleRepeat4_...` and `no_tripleRepeat8_...` (720-727).** Same
   triple, same preceding symbols (`S[8] = S[2] = S[5]`), so the maximality
   clause fails at every length. ✔
6. **`leastPeriod9 = 3` and `period3_9` (731-737).** `Period 3` is
   `∀r, S(r+3) = S(r)`, which holds because the word is a 3-fold power;
   and no period in `{1,2}` works (`shift by 1` gives `S[0] = 0` vs
   `S[1] = 1`). ✔
7. **`not_IsPrimitive9` (740-743).** Follows from (6) and
   `period_iff_shiftInvariant`, which I checked (606-625) in both directions:
   forward is a `Fin.ext` on `mod_add_shl`, backward rewrites `cyc r.val` to
   `S r` by `Nat.mod_eq_of_lt r.isLt`. ✔

So the refutation of the *node/out-degree* form without primitivity is real,
and the escape disjunct of `deg_fact` fires exactly there. **The two sibling
fronts are justified in building on the primitivity hypothesis, because the
primality-necessary condition is genuinely necessary and I have confirmed the
witness by hand.** (The refuted statement is `deg_fact_node` with `hprim`
deleted; the `Agr3`-form `deg_fact` is *not* refuted — its second disjunct
absorbs the example, which is the correct design.)

### 1.3 The docstring-honesty question

`BBTUniqueEulerian.lean:71-95` ("What is still missing"). The docstring's
"missing part" is stated precisely: *"a maximal element of a set of agreement
lengths, shifted to the left frontier, is a
`SourceFaithfulIs.Genome.IsTripleRepeat`"*.

* **The docstring as it stands at `1ee7db8` is STALE, not FALSE.** Three
  reasons it is not false: (a) the fixed-triple two-sided extension that the
  statement of Lemma 1 asks for is genuinely still not proved — tw6 proves
  the *existential* form (some triple carries the maximal repeat), which is
  weaker, and the author says so in §6.3; (b) the docstring's Lemma 1 already
  contains "(in the primitive case)" and already names the `p = 3` escape and
  the `012012012` example, so nothing it asserts about the counterexample is
  contradicted; (c) Lemma 2 is untouched and the docstring's account of what
  `thm:BBT` still needs is unchanged by this tranche.
* **Replacing it wholesale would OVERSTATE.** The honest edit is narrow and
  should say, in effect: *"the `Finset`-maximum form of the two-sided maximal
  extension, and the primitive branch of the multiplicity cap, are now
  available in `Issue94TW6Lemma1` (`max_span_tripleRepeat`, `deg_fact_of_primitive`,
  `no_three_of_P2`, `prim_deg_le_two`); the **fixed-triple** form is still
  missing."* Anything that says "Lemma 1 is proved" or that deletes the
  "two-sided maximal extension" clause would be false, because the fixed-triple
  form is not in the tree (`BBTTripleBridge` does not contain it either — see
  §2.5 below).
* This is a correction to the **author's recommendation**, not to the code:
  report §6.13 and §8 point 8(a) tell 94e8 that the docstring "now overstates
  what is missing" and "should be corrected", and 94e8 was briefed to act on
  it. Read naively, 94e8 will delete the missing-part clause. See finding 2.

### 1.4 Non-vacuity: is this new content, or a second vocabulary for
`P2.imp_nodeCount_le_two`?

**Partly new. And the author's own guess about which part is new is
backwards, in a way that matters operationally.**

* `P2.imp_nodeCount_le_two` / `…_of_powerPrimitive` (`P2Multiplicity.lean:197-231`,
  namespace `AssemblyP1.P2Multiplicity`) already state, in the same
  `Fin G → α` layer and the same `nodeCount` (hence `deg`) reading, exactly
  `∀ k, nodeCount (L:=L) hG S k ≤ 2` under `IsPrimitive` + `P2` + `2 ≤ L ≤ G`.
* Report §6.9 says: *"I did not check whether `prim_deg_le_two` is derivable
  from the existing theorem (**I believe it is not**, without that bridge,
  but I did not verify either way)"* and asks the next front to decide
  whether a `HasLongTripleRepeat ↔ IsTripleRepeat` bridge is worth building.
* **That speculation is false, and the bridge is unnecessary.** `hprim` in
  tw6's own statement is *literally* `RepeatAdapter.IsPrimitive hG S`, because
  `IsPrimitive` is `∀ s, 0 < s → s < G → ¬ ShiftInvariant s`
  (`RepeatAdapter.lean:87-88`) and `Period d ↔ ShiftInvariant d` is tw6's own
  `period_iff_shiftInvariant` (line 606). So:

  ```lean
  -- the whole bridge, ~4 lines, no new mathematics
  have hprim' : RepeatAdapter.IsPrimitive hG S :=
    fun s hs0 hsG hsi => hprim s hs0 hsG ((period_iff_shiftInvariant hG S s).mpr hsi)
  exact P2.imp_nodeCount_le_two hG hL hLG S hprim' hP2 v   -- = prim_deg_le_two
  ```

  (tw6's `escape_iff_not_IsPrimitive` at 629 already packages exactly this
  equivalence.) The same argument plus `vtx_agr` gives `no_three_of_P2` from
  the existing theorem. **`no_three_of_P2` and `prim_deg_le_two` are
  corollaries of work already in the tree.** The author flagged the risk
  themselves and then guessed wrong; the guess was cheap to check and was
  worth checking before briefing a successor.
* **What *is* new and load-bearing:** the `Finset` engine (`span`, `spanMax`),
  `max_span_tripleRepeat` (the two-sided maximality by maximum-over-triples),
  `max_span_escape` / `max_span_escape_congruent`, `deg_fact`,
  `deg_fact_node` (the `deg ≥ 3` reading of BBT's own sentence),
  `escape_iff_leastPeriod` / `period_iff_shiftInvariant` /
  `escape_iff_not_IsPrimitive`, and the concrete `deg = 3` counterexample
  with its two `Decidable` instances. In particular
  `BBTTripleBridge.lean` contains **only** `escape_pair` and `escape_triple`
  (I read the whole file: 187 lines, it stops at line 187) — it has **no**
  `triple_bridge`, no `tripleBridge_primitive`, no `P2.vtx_two_of_three`,
  despite its docstring promising them. It is unimported
  (`BBTTripleBridge` appears nowhere in `AssemblyP1.lean`) and, per the
  author's report, does not compile. So tw6 does not duplicate it, and the
  *fixed-triple* form remains genuinely absent from the tree.
* **The `Decidable` prediction (§8 point 9) is CONFIRMED by the file itself:**
  `decAgree9` (673) needs `unfold …; infer_instance` and `decIsTripleRepeat9`
  (683) needs an explicit `show` of the whole 10-conjunction, with the author
  noting `rfl` fails for `Decidable (∀ a b c : Fin 9, …)`. That is exactly the
  "material is in the interfaces" pattern. I did not attempt the global
  `∀`/`∃` counterexample (that would need a compile).

### 1.5 The axioms audit

I read the source, not the log.

* The 25 `#print axioms` lines in the diff (`AssemblyP1.lean:491-515`) name 25
  distinct declarations, and **all 25 exist** in
  `Issue94TW6Lemma1.lean` — I checked each name mechanically. The count in
  report §5 ("one `import` plus 25 `#print axioms`", "26 lines") is correct,
  as is "745 lines" for the new file.
* `grep -nE "\bsorry\b|\badmit\b|native_decide|unsafe |partial |axiom|@\[implemented_by\]"`
  over `Issue94TW6Lemma1.lean` returns **exactly one line: 67**, the module
  docstring. Matches report §3 verbatim. No `axiom`, no
  `@[implemented_by]`, no `native_decide`, no `unsafe`/`partial` anywhere in
  the tranche. The two `Decidable` instances are `Decidable` instances only,
  no definition changed.
* The counterexamples use `decide +kernel`, i.e. the kernel reduction checker,
  not the compiler — the right choice, and `+kernel` is present on all eight
  `decide` uses (700, 705, 717, 722, 727, 732, 737).
* The three axioms `{propext, Classical.choice, Quot.sound}` are **RELAYED**:
  I cannot produce the log without compiling. It is *internally consistent*
  with the source — the one theorem plausibly axiom-free,
  `agr3_iff_agree3` (99-106), is a pure `Iff` between two definitions, and
  `period_iff_shiftInvariant` being listed *without* `Classical.choice` is
  consistent with its constructive proof. `span` and `spanMax` are
  `noncomputable` (133, 180), so `Classical.choice` in everything downstream
  of them is expected. `Quot.sound` presumably enters via the pre-existing
  Mathlib layer. **No `sorryAx` is possible in this file**: none of
  `sorry`/`admit` occurs, so nothing can be a `sorryAx` — that part of the
  claim is established, not relayed.

### 1.6 Provenance: what is independent of it and what is not

Established, provenance-free:

* The dichotomy `deg_fact` and everything deduced from it. It is a theorem
  about `Fin G → α` words and the repository's own `IsTripleRepeat`; the
  truth of `deg_fact` does not depend on who said it first.
* The **necessity** of the primitivity condition, by the hand computation in
  §1.2. This is a mathematical fact about the repository's definitions and
  is fully independent of BBT, of `l:Pev95`, and of arXiv.
* The characterisation of the escape condition as three equivalent readings
  (`escape_iff_leastPeriod`, `escape_iff_not_IsPrimitive`) — internal to this
  repository.
* That the *unrestricted* node-degree form is false. Independent of the paper.

Not independent (RELAYED, and the author says so):

* That "the degree fact of BBT Lemma 1" **is** `deg_fact_of_primitive` — this
  is tw5's reading of `appendix_short.tex` 157-175, taken on trust by tw6
  (§6.5 item 5), not re-read by either of us.
* That the *name* `K` in BBT is the repository's `K = L - 1`, and that the
  `deg ≥ 3` reading is BBT's intended reading of "traverses any node three
  times". `deg_fact_node` is a faithful *formalisation of a plausible
  reading*, not a verified transcription.
* `l:Pev95`'s unsourced status (earlier passes), and tw5's claim that the
  appendix has no counting argument. Unrelated to this tranche and untouched
  by it.

Net: **the mathematics of this tranche is provenance-independent; only its
attribution to BBT is not.** A successor may use `deg_fact_of_primitive` for
any reason it likes without waiting on the source question; it may not write
"BBT Lemma 1 says X" on tw6's authority.

---

## 2. DEAD CODE AND REDUNDANCY (finding list feeds off this)

Within the new file, referenced nowhere in the tree:

| declaration | line | note |
| --- | --- | --- |
| `mem_span_zero` | 167 | genuinely dead; its docstring's claim "This is where `3 ≤ G` is used" is **false** (see finding 3) |
| `max_span_escape_congruent` | 403 | exported, unconsumed; `hdAC` at 417-418 is dead inside it too |
| `no_three_of_primitive` | 476 | exported, unconsumed (it *is* the statement the report calls "the contrapositive a consumer wants") |
| `deg_fact_escape_only` | 645 | exported, unconsumed |
| `deg_fact_node` | 520 | exported, unconsumed, but this is the BBT-faithful node reading — keep |

All of these are public library theorems in a module whose purpose is to
supply a vocabulary; "unconsumed" is not a defect for them. Only
`mem_span_zero` is both dead and mis-documented.

---

## 3. NUMBER AUDIT (every number in the report, checked by me)

| report figure | my finding |
| --- | --- |
| new file "745 lines" (`§5`) | **correct** — `wc -l` = 745 |
| `AssemblyP1.lean` "26 lines: one import plus 25 `#print axioms`" (`§5`) | **correct** — diff is +1 import, +25 prints |
| 25 names in the axioms log (`§3`) | **correct**, and all 25 exist in the source |
| prohibition grep returns "one line (line 67)" (`§3`) | **correct** — one hit, line 67 |
| `Agr3` at `BBTUniqueEulerian.lean:140-142`; `Period` at 152-153; docstring Lemma 1 at 73-76; `012012012` prose at 83-86 | **all correct** (83-86 verified) |
| `SourceFaithfulIs.lean:122-128`; `BBTCondense.lean:207-208` | **correct**, quoted verbatim |
| `hPevzner` at `PopulationUniqueness.lean` 164, 217, 247; `hBBT` at 194 | **correct** — all four line numbers exact |
| `BBTTripleBridge.lean` = commit 5bb6d3c, stops after `escape_triple`, unimported | **correct** on the two checkable halves: it stops at `escape_triple` (line 127, file ends 187) and appears nowhere in `AssemblyP1.lean`. The commit id is **RELAYED** |
| `python3` absent (host fact, `§6.14`) | **confirmed** — `which python3 python` finds neither; I did not attempt to work around it |
| "8983 jobs / 8982 before / exit 0 / zero warnings / 5m34s" (`§3`) | **RELAYED** — the build log is in `/tmp/opencode/tw6/` in the author's worktree, which I did not open. Internally consistent (+1 job for +1 module) but unverified |
| the axioms log itself | **RELAYED** (see §1.5 for what I could establish statically instead) |

There is no test-suite size or mutation count in this report, so the failure
mode flagged in the brief (miscounted mutation tests) does not recur here.
The report's numbers are file-and-line based and they check out; the two
report claims that are *wrong* are both non-numeric (§1.4 non-vacuity, §4
below on `omega`).

---

## 4. WHAT I COULD NOT SETTLE WITHOUT COMPILING

This is a hard limit, not a caveat. I ran **no** `lake build`, no
`lake env lean`, no `lake clean`, no `elan`, no `lake exe`, and no
compilation of any kind, because sibling fronts 94e8 and 94e9 hold this
host's exclusive Lean compilation window. My confidence splits as follows.

**High confidence (settled by reading + hand arithmetic, would survive a
build):** every proof step of `deg_fact`, `deg_fact_of_primitive`,
`max_span_tripleRepeat`, `max_span_escape`, `deg_fact_node`,
`escape_iff_*`, `period_iff_shiftInvariant`, the `Ukkonen`/`P2` corollaries;
the counterexample's truth; the absence of `sorry`/`axiom`/`native_decide`;
the derivation of `prim_deg_le_two` from `P2.imp_nodeCount_le_two`
(finding 4); all file/line numbers.

**Genuinely un-settled, compile-only, with the exact commands:**

1. That the module elaborates at all in this pin, and the three
   `omega`-on-`Fin.val`-atom sites **349, 354, 359**. My static read says they
   are the same shape as the already-compiled `BBTUniqueEulerian.lean:212`,
   so I expect them to pass — but "I expect" is not a build.
   `lake build AssemblyP1.Issue94TW6Lemma1` (or
   `lake env lean AssemblyP1/Issue94TW6Lemma1.lean`).
2. The `Finset.one_lt_card.mp` shape at line 493 and the
   `Finset.card_erase_of_mem` rewrite at 491 (`three_mem_of_card_ge_three`) —
   Mathlib API-shape assumptions I could only check by name.
3. The definitional-unfolding steps at 508 (`deg` → `nodeCount` → the
   `Finset.univ.filter` card) and 618-624 (`cyc r.val = S r` under
   `r.isLt`), and the `Nat.pred` defeq at 582-583. All are the kind of thing
   that passes, but each is a `isDefEq` decision, not a theorem.
4. That `decide +kernel` can in fact evaluate the eight concrete
   counterexamples and `leastPeriod9` in this pin. `leastPeriod9` requires
   the kernel to reduce a `Finset.range 10 .filter (fun d => 0 < d ∧ Period
   …)` and take a `min'`; that is the single most likely thing in the file to
   be slow or to blow a heartbeat budget, and `set_option maxHeartbeats
   1000000` at line 72 is doing real work there.
5. The axioms audit (§1.5) and the `lake build --wfail` exit code / job count
   / warning count. Settle with
   `lake build --wfail 2>&1 | tee /tmp/tw6review.log; grep -cE '^(error|warning)' /tmp/tw6review.log`
   and by reading the `#print axioms` output for the 25 names.
6. Whether the two new `Decidable` instances (`decAgree9`, `decIsTripleRepeat9`,
   lines 673 and 683) perturb instance synthesis in *other* modules. They are
   scoped to `mkGenome hG9 S9`, so they should be inert, but "should be" is
   the same class of claim as everything above. Only a full-tree build
   settles it, and the author's clean-state build is the only evidence I have
   (RELAYED).

I did **not** attempt the global counterexample `∀ e a b c, ¬ IsTripleRepeat
…` that §6.7 leaves open, and I am not asking anyone to treat it as
available. (For the record my hand argument for it: in a period-3 word the
length-`e` window at `r` is determined by `r mod 3`, so three distinct
agreeing starts share a residue mod 3, hence share their preceding symbol, so
the preceding maximality clause always fails. That is a sketch, not a proof,
and it is not in the tree.)

---

## 5. FINDINGS

### Must-fix

1. **`AssemblyP1/Issue94TW6Lemma1.lean:26-29` and `:655-662` overclaim the
   counterexample's scope.** Both the module docstring ("the word has **no**
   maximal triple repeat at all") and the §7 docstring ("the word has **no**
   maximal triple repeat at any length, so it satisfies the `Ukkonen` triple
   clause and the `P2` triple clause") assert a *global* statement. What the
   file proves is `¬ IsTripleRepeat e 0 3 6` at `e = 3, 4, 8` — one triple,
   three lengths. The author's own report §6.7 admits this; the source does
   not. The global statement is very likely *true* (my argument is in §4, item
   6) but it is not in the file, and a module docstring must not assert what
   the module does not contain. Fix: either weaken the wording to "at those
   three starts" or add the `∀`/`∃` instance. Same defect, milder, in report
   §2.1 ("there is **no** maximal triple repeat") — that sentence should
   carry the same restriction.
2. **Report §6.13 / §8 point 8(a), as a *recommendation*, is unsafe and 94e8
   has been briefed on it.** The docstring of `BBTUniqueEulerian.lean` is
   **stale, not false** (§1.3), and the honest edit is the narrow one quoted
   there. A front that reads "the docstring should be corrected" as "Lemma 1
   is now proved" and deletes the missing-part clause would introduce a false
   documentation claim into the tree — the exact failure mode
   `docs/bbt-unique-eulerian-89.md` §4 and this repository's history warn
   about. Fix the recommendation, not the file. (If 94e8 has already made the
   broad edit, it should be narrowed before merge.)

### Non-blocking

3. **`h3 : 3 ≤ G` is unused throughout the module, and
   `Issue94TW6Lemma1.lean:165-166` misattributes it.** `mem_span_zero`'s
   docstring says "This is where `3 ≤ G` is used", but `deg_fact` and all its
   descendants obtain nonemptiness from `span_nonempty` (given `hex`), never
   from `mem_span_zero`; `h3` is threaded through nine theorems and used in
   none. It is genuinely redundant (three pairwise distinct elements of
   `Fin G` already force `3 ≤ G`). Non-blocking because no statement is
   weakened — but a comment claiming a hypothesis is load-bearing when it is
   not is the sort of thing this review exists to catch.
4. **Report §6.9's speculation is false: `prim_deg_le_two` and
   `no_three_of_P2` are derivable from `P2.imp_nodeCount_le_two` in ~4 lines
   via tw6's own `period_iff_shiftInvariant`.** Derivation in §1.4. No code
   change needed; the *briefing* to 94e8/94e9 must not ask them to build a
   `HasLongTripleRepeat ↔ IsTripleRepeat` bridge, and must not treat §2.4 as
   new mathematical content.
5. **Report §6.11 / §8 point 7 overstates the `omega` hazard.**
   `BBTUniqueEulerian.lean:212` is a compiled `by omega` on a goal containing
   `a.val` and `b.val`, so `omega` demonstrably handles plain `.val`
   variables in this pin; only `Fin.val ⟨…⟩` literals are the reported
   failure mode. The advice "every use of `by omega` next to a `Fin G`
   hypothesis" is wrong and would make the next front write `congrArg Fin.val`
   boilerplate it does not need. The new file's own three `.val` omegas
   (349, 354, 359) are the only exposure and they look safe.
6. **Dead code:** `mem_span_zero` (167), and the discarded `hdAC` inside
   `max_span_escape_congruent` (417-418, superseded by `hdAC'` at 421).
   `max_span_escape_congruent`, `no_three_of_primitive`,
   `deg_fact_escape_only` and `deg_fact_node` are exported and unconsumed,
   which is acceptable for a library module.
7. **No status block in `AssemblyP1.lean`.** The tranche added only an import
   and the `#print axioms` lines; the top-level "not established" narrative
   (around `AssemblyP1.lean:437`) is not updated with the new degree fact.
   Precedent is mixed (tw5 did the same), so this is a style note, but given
   the board's emphasis on durable repo state, a two-line status note would
   be worth adding at integration.
8. **`BBTTripleBridge.lean` remains a dead, non-compiling file with a
   docstring that promises `triple_bridge`, `tripleBridge_primitive` and
   `P2.vtx_two_of_three` which do not exist in it.** Not this tranche's
   fault and it correctly declined to touch it — but it is a live
   documentation-false claim in the tree, on the same pattern as finding 2,
   and it should be struck or truncated at some point.

---

## 6. RELAYED vs ESTABLISHED

| claim | status |
| --- | --- |
| every proof step in `Issue94TW6Lemma1.lean` follows | **ESTABLISHED** (static reading, def-by-def) |
| the counterexample `012012012`, `G=9`, `K=3`, `deg = 3`, no triple repeat | **ESTABLISHED** (hand arithmetic from the definitions, §1.2) |
| `hPevzner` untouched at `PopulationUniqueness.lean:164,217,247`; `hBBT` at 194 | **ESTABLISHED** (grep) |
| no `sorry`/`admit`/`native_decide`/`axiom`/`@[implemented_by]` in the tranche; the only grep hit is the docstring at line 67 | **ESTABLISHED** |
| 25 `#print axioms` names, all present in the source | **ESTABLISHED** |
| therefore no `sorryAx` is reachable | **ESTABLISHED** (no `sorry` exists) |
| `prim_deg_le_two`, `no_three_of_P2` derivable from `P2.imp_nodeCount_le_two` | **ESTABLISHED** (§1.4) |
| all file/line citations in report §1.1, §3, §4, §5 | **ESTABLISHED** |
| 745 lines / 26 lines / 25 prints / one grep hit | **ESTABLISHED** |
| `python3` absent on this host | **ESTABLISHED** |
| `BBTTripleBridge.lean` stops after `escape_triple` and is unimported | **ESTABLISHED** (commit id 5bb6d3c **RELAYED**) |
| axiom list `{propext, Classical.choice, Quot.sound}`; `agr3_iff_agree3` axiom-free | **RELAYED** (author's build log); static consistency argued in §1.5 |
| `lake build --wfail` exit 0, 8983 jobs, zero warnings, 5m34s | **RELAYED** (author's log) |
| `decide +kernel` succeeds on the eight concrete goals | **RELAYED** |
| this file compiles in this pin (esp. lines 349/354/359) | **NOT SETTLED — compile only** |
| that the degree fact *is* BBT Lemma 1 / `l:Pev95` / CPT 2011 / arXiv appendix | **RELAYED** (tw5, via tw6) and out of scope here |

---

## 7. CAN 94e8 AND 94e9 BUILD ON THIS?

Yes, with two guardrails. The mathematics they need is sound: the
`span`/`spanMax` engine, `max_span_tripleRepeat`'s two-sided maximality, the
escape characterisation, and the node-degree form `deg_fact_node` all check
out by reading, and the primitivity condition is genuinely necessary — the
`012012012` witness is correct and I re-derived it by hand, so nobody should
be tempted to state a degree fact without primitivity. Guardrail one: **the
primitivity bridge they are told to assemble (`PopulationReduction.IsPrimitive`
→ `¬∃d ∈ (0,G), Period d`) is already done**, in `period_iff_shiftInvariant`
plus `escape_iff_not_IsPrimitive`, and `P2Multiplicity.IsPrimitive.shiftPrimitive`
(`P2Multiplicity.lean:227-231`) is the population-side half; do not rebuild it.
Guardrail two: **do not treat `no_three_of_P2` and `prim_deg_le_two` as new
mathematics** — they are consequences of `P2.imp_nodeCount_le_two` already in
the tree (finding 4), and the fresh content of this tranche is the dichotomy,
the escape characterisation, and the kernel-checked counterexample. And
neither front should inherit the broad docstring edit that 94e8 was briefed on
(finding 2): the honest correction to `BBTUniqueEulerian`'s docstring is
narrow, and the fixed-triple form of Lemma 1 is still genuinely open.

---

```
$ git status --porcelain
<empty>
$ git rev-parse HEAD
<reviewed at 1ee7db8143f4e3194072192d4ff2383cd65d8c2c; this review is the
 commit that follows it, on review/94-tw6-lemma1, pushed to
 origin/review/94-tw6-lemma1>
```
