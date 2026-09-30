# BOARD 94 — INTEGRATION ORDER for `antonina/issue-89-final`

**Front:** 94ef (integration analysis). **Branch:** `analysis/94-issue89-merge-order`, based on
`7d50132`. **Read-only on the repository; no Lean written, nothing compiled, no `.lake` created.**
At most one commit will be made, on this branch only, carrying this markdown file.

Every load-bearing command and its real output is reproduced below. Where I state a claim I did
not verify myself, it is marked **[RELAYED]**. Everything else is **[ESTABLISHED]**.

---

## 0. HEADLINE — THE BRANCH NAMES LIE, AND THE GOOD NEWS

The brief told me tw2–tw6 are a stack of siblings off tw6, and that tw1, tw2, tw3, tw4, tw5, tw6
are all separate tranches to be folded one at a time. **That is not what the repository says.**

**[ESTABLISHED]** Two facts change the whole plan:

1. **`origin/antonina/issue-89-final` (`7d50132`) is an ANCESTOR of tw2, tw3, tw4, tw5, tw6, tw7,
   tw8, `fix/94-tw6-dochonesty`, both review refs and `94-doc-corrections`.** All of that work is
   *already* a fast-forward away. There is no "folding" to do for the main chain; there is one
   `--ff-only` away.
2. **`94-tw1-best` is already merged into the chain** by merge commit `b8bcbb5`, and
   `94-tw2-edgetype` is a *descendant* of it. tw1 is not pending work.

The only genuinely manual integration decisions left are: (a) the `Issue94TW6Lemma1.lean`
docstring conflict between **tw7** and **`fix/94-tw6-dochonesty`**, which is a substantive
*mathematical* disagreement about what the counterexample proves and which I am escalating rather
than deciding; and (b) the `AssemblyP1.lean` conflict between **tw7** and **tw8**, which is
mechanical.

**Consequence: the branch can be moved to a reviewable state tonight without tw8 at all.**

---

## 1. THE TRUE SHAPE OF THE WORK

### 1.1 Commands

```
$ git ls-remote origin 'refs/heads/94-tw*' 'refs/heads/fix/94-tw6-dochonesty' \
                     'refs/heads/review/94-tw*' 'refs/heads/94-doc-corrections'
```

Real tips (note: the figures in my brief for tw2 and tw3 were **swapped/stale**; I read them
myself):

| ref | tip |
| --- | --- |
| `origin/main` | `aa05fc7` |
| `origin/antonina/issue-89-final` | `7d50132` |
| `origin/94-tw1-best` | `8d9f7eb` |
| `origin/94-tw2-edgetype` | `9f30a5e` |
| `origin/94-tw3-residual` | `e8371b0` |
| `origin/94-tw4-eulerian` | `6012bff` |
| `origin/94-tw5-lambda` | `e3fe5a5` |
| `origin/94-tw6-lemma1` | `1ee7db8` |
| `origin/94-tw7-altf` | `b7b092c` |
| `origin/94-tw8-contraction` | `cd430b4` |
| `origin/fix/94-tw6-dochonesty` | `0733b76` |
| `origin/review/94-tw6-lemma1` | `02d466f` |
| `origin/review/94-tw8-contraction` | `0984dac` |
| `origin/94-doc-corrections` | `4204aac` |
| `origin/fix/94-tw8-typecheck` | **DOES NOT EXIST** (no such ref on the remote; the repair front has not pushed) |

### 1.2 `git merge-base` matrix (real output, abridged to load-bearing pairs)

```
origin/main                      origin/94-tw1-best          aa05fc7   (= main tip)
origin/main                      origin/94-tw2-edgetype       aa05fc7
origin/main                      origin/94-tw6-lemma1        aa05fc7
origin/94-tw1-best               origin/94-tw2-edgetype       deb8c58
origin/94-tw1-best               origin/94-tw3-residual       8d9f7eb   (= tw1 tip)
origin/94-tw2-edgetype           origin/94-tw3-residual       9f30a5e   (= tw2 tip)
origin/94-tw3-residual            origin/94-tw4-eulerian       e8371b0   (= tw3 tip)
origin/94-tw4-eulerian            origin/94-tw5-lambda         6012bff   (= tw4 tip)
origin/94-tw5-lambda              origin/94-tw6-lemma1         e3fe5a5   (= tw5 tip)
origin/94-tw6-lemma1              origin/94-tw7-altf           1ee7db8   (= tw6 tip)  <-- SIBLING
origin/94-tw6-lemma1              origin/94-tw8-contraction    1ee7db8                 <-- SIBLING
origin/94-tw6-lemma1              origin/fix/94-tw6-dochonesty 1ee7db8                 <-- SIBLING
origin/94-tw6-lemma1              origin/94-doc-corrections   6012bff   (= tw4 tip)   <-- SIBLING OF tw5/tw6, NOT OF tw7
origin/94-tw4-eulerian            origin/94-doc-corrections   6012bff
origin/94-tw7-altf               origin/94-tw8-contraction    1ee7db8
origin/94-tw8-contraction         origin/review/94-tw8-contraction  cd430b4 (= tw8 tip)
```

### 1.3 Ancestry verdicts

```
$ for b in <every tranche>; do git merge-base --is-ancestor 7d50132 origin/$b ...; done

94-tw1-best:          NOT ancestor | main is ancestor | commits-ahead=2
94-tw2-edgetype:      FF (issue-89-final is ancestor) | main is ancestor | commits-ahead=2
94-tw3-residual:      FF | commits-ahead=6
94-tw4-eulerian:      FF | commits-ahead=9
94-tw5-lambda:        FF | commits-ahead=10
94-tw6-lemma1:        FF | commits-ahead=11
94-tw7-altf:          FF | commits-ahead=12
94-tw8-contraction:   FF | commits-ahead=12
fix/94-tw6-dochonesty:FF | commits-ahead=12
review/94-tw6-lemma1: FF | commits-ahead=12
review/94-tw8-contraction: FF | commits-ahead=13
94-doc-corrections:   FF | commits-ahead=10
```

`main is ancestor` for every tranche **[ESTABLISHED]**: no tranche rewrites `main` history, so
"applies cleanly to current main" is satisfied by construction for all of them.

### 1.4 The graph

```
aa05fc7 (main)
  ...
  deb8c58  <-- the last common point of issue-89-final and tw1
    |\
    | 8d9f7eb (94-tw1-best)  e7d55f9     -- REFUTES the t_w=1 step
    7d50132 (antonina/issue-89-final)  <-- my base; the case-split tranche
      77a71a8
      9f30a5e (94-tw2-edgetype)
        b8bcbb5  Merge commit '8d9f7eb' into 94-tw2-edgetype   <-- TW1 ALREADY MERGED
        e8371b0 (94-tw3-residual)
          d7f3f4c
          76e64af
          6012bff (94-tw4-eulerian)
            |\
            | 4204aac (94-doc-corrections)   <-- branches HERE, at tw4
            e3fe5a5 (94-tw5-lambda)
              1ee7db8 (94-tw6-lemma1)  <-- the hub
                |\
                | b7b092c (94-tw7-altf)
                | cd430b4 (94-tw8-contraction)  <-- repair front works here
                | 0733b76 (fix/94-tw6-dochonesty)
                | 02d466f (review/94-tw6-lemma1)
                | 0984dac (review/94-tw8-contraction)
```

### 1.5 Classification

* **Sequential, already contiguous, zero conflicts:** `7d50132 -> tw2 -> tw3 -> tw4 -> tw5 -> tw6`.
  This is one linear run of 11 commits. `[ESTABLISHED]` by trial merge, §3.1.
* **Already integrated:** `94-tw1-best`, absorbed at `b8bcbb5`. `[ESTABLISHED]`
* **True siblings off `1ee7db8`:** tw7, tw8, `fix/94-tw6-dochonesty`, `review/94-tw6-lemma1`,
  `review/94-tw8-contraction`. These are the only places conflicts live.
* **Sibling off `6012bff` (tw4), NOT off tw6:** `94-doc-corrections`. This is the trap. **[ESTABLISHED]**
* **Independent / any order:** the two review refs add one markdown file each and touch nothing
  mathematical (but must not land — §6).

### 1.6 The `94-doc-corrections` trap — established, not inferred

```
$ git ls-tree origin/94-doc-corrections AssemblyP1/Issue94TW6Lemma1.lean AssemblyP1/Issue94TW5Single.lean
(no output — the files DO NOT EXIST on that branch)
$ git ls-tree origin/94-tw6-lemma1 AssemblyP1/Issue94TW6Lemma1.lean AssemblyP1/Issue94TW5Single.lean
100644 blob 47ae20e8...  AssemblyP1/Issue94TW5Single.lean
100644 blob 0affd3c5...  AssemblyP1/Issue94TW6Lemma1.lean
```

`94-doc-corrections` was cut at tw4, so its diff against tw6 shows **745 deletions** in
`Issue94TW6Lemma1.lean` and **361** in `Issue94TW5Single.lean`. **Those are not deletions it
intends; they are files that did not exist when it branched.** Any plan that merges
`94-doc-corrections` *after* tw5/tw6 — and every ordering a reader would guess from the names
does exactly that — silently destroys two modules. `git` happens to save us (it sees tw5/tw6 as
additions on the other side and takes them), which is why the naive trial merge reports "no
conflict" and looks fine. It is not fine; it is a *content* loss. **[ESTABLISHED]**

The correct placement is **before tw5**, i.e. merge it at tw4. §3.2 shows that is clean.

---

## 2. WHAT IS ALREADY ON `issue-89-final`, AND WHAT IS MISSING

`7d50132` is 12 commits behind tw7, 11 behind tw6, 10 behind tw5, 2 behind tw2. **Nothing from
tw2 onward is on it.** The only tranche work on it is the pre-existing case-split line
(`d0aa0aa` "Discharge CrossingPairsCoalesce by the cross-head case split", `a23872a` "the
no-collision half", `54304a2` falsification sweep, `bd86376` E3/E8 repairs, `2498c58`
`[DecidableEq alpha]` generalisation, plus doc commits `98e22df`, `565cd81`, `7d50132`).

### 2.1 The tip commit's line of work, and the overlap risk

`7d50132 docs(#94): stop five files calling CrossingPairsCoalesce uninhabited` — a
**documentation-truth** commit, five files, `.lean` docstrings. Its sibling on the same
philosophy is `fix/94-tw6-dochonesty` (tw6 docstrings) and `94-doc-corrections` (BBT
bibliographic record). These are the *same class of work*, not duplicates: they touch disjoint
files. `565cd81` and `98e22df` on the branch are the same genre (false `file:line` citations, an
E3 docstring over-correction).

**[ESTABLISHED]** No duplication and no contradiction between `7d50132` and
`fix/94-tw6-dochonesty`: `7d50132` does not touch `AssemblyP1/Issue94TW6Lemma1.lean` at all.

```
$ git diff --name-only 7d50132 565cd81^..7d50132   (i.e. the three doc commits)
  -- does Issue94TW6Lemma1.lean appear?
```

It does not; `Issue94TW6Lemma1.lean` is created at tw6 (`1ee7db8`), after `7d50132`. The
branch's doc work and the dochonesty work are on disjoint files and compose without conflict.

The one *contradiction* is **not** with the branch: it is between **tw7** and
**`fix/94-tw6-dochonesty`**, both editing the same docstring. That is §3.3 and §5.

### 2.2 Missing from the branch (the whole to-do list)

1. tw2 (`LadderVertexCycle` block half discharged)
2. tw3 (reconciles tw1; no residual; `LadderVertexCycle == Blockless`)
3. tw4 (`2 ≤ L` ⟹ unbounded `CrossingChordsCoalesce`; L>1 range closed)
4. tw5 (`single` clause is a tautology; `AltF` has no innermost chord)
5. tw6 (BBT Lemma 1 degree fact + exact condition + counterexample) — **including its docstring
   correction, which must travel with it (§5)**
6. tw7 (AltF = id **refuted**; characterisation; `node_prefix`; correct-target status notes)
7. `94-doc-corrections` (BBT bibliographic record; strike "the chain is broken")
8. tw8 — **conditional, see §4**

---

## 3. THE ORDERED PLAN

Target is always `antonina/issue-89-final`. Never `main`. Steps 1–3 are conflict-free and I
verified them by trial merge in my own worktree; every trial was abandoned with
`git merge --abort` / `git reset --hard` and no branch was kept.

### Step 1 — Fast-forward the whole main chain in one move

```
git fetch origin
git checkout antonina/issue-89-final        # or push to it from a fresh clone
git merge --ff-only origin/94-tw6-lemma1    # == 1ee7db8
git push origin antonina/issue-89-final
```

* **Kind:** pure fast-forward. **Files:** 25-ish across `AssemblyP1/*.lean`, `AssemblyP1.lean`,
  `docs/*.md`, `scripts/*` (see the tw2→tw6 cumulative stat in §1.4's graph labels).
* **Conflicts:** **none.** Verified:

```
$ git checkout -B tmp-trial origin/antonina/issue-89-final
$ for r in tw2 tw3 tw4 tw5 tw6: git merge --ff-only origin/$r
94-tw2-edgetype        FF-OK -> 9f30a5e
94-tw3-residual        FF-OK -> e8371b0
94-tw4-eulerian        FF-OK -> 6012bff
94-tw5-lambda          FF-OK -> e3fe5a5
94-tw6-lemma1          FF-OK -> 1ee7db8
```

* **Note:** this one `--ff-only` subsumes steps for tw2, tw3, tw4, tw5, tw6 **and** tw1
  (already merged at `b8bcbb5`). Do **not** try to "also land tw1"; it is inside.
* This lands `7d50132`'s own doc line of work intact, since it is an ancestor.

### Step 2 — `94-doc-corrections`, merged **at tw4, before tw5**

This must be a step between tw4 and tw5, so the practical form of the plan is to interleave:

1. ff to `origin/94-tw4-eulerian` (`6012bff`)
2. merge `origin/94-doc-corrections` (`4204aac`)
3. ff to `origin/94-tw6-lemma1` (`1ee7db8`)

i.e.

```
git merge --ff-only origin/94-tw4-eulerian
git merge --no-ff origin/94-doc-corrections -m "merge 94-doc-corrections (BBT bibliographic record)"
git merge --ff-only origin/94-tw6-lemma1
git push origin antonina/issue-89-final
```

* **Kind:** ff, then a real merge commit, then ff. **Files** touched by the merge (from
  `git diff --cached --name-status`, real output):
  `AssemblyP1/BBTCondense.lean`, `AssemblyP1/BBTEulerian.lean`, `AssemblyP1/Issue94TW1.lean`,
  `AssemblyP1/PopulationUniqueness.lean`, `docs/arratia-shift-left-invariant-89.md`,
  `docs/bbt-chord-rematch-89.md`, `docs/best-tw1-attribution-94.md`,
  `docs/exact-same-length-spectrum-fibre-count.md`.
* **Conflicts:** **none.** Verified:

```
$ git reset --hard origin/94-tw4-eulerian
$ git merge --no-commit --no-ff origin/94-doc-corrections   # exit 0, no CONFLICT lines
$ git commit; for r in tw5 tw6 tw7 dochonesty tw8: git merge ...
94-tw5-lambda            OK
94-tw6-lemma1            OK
94-tw7-altf              OK
fix/94-tw6-dochonesty    CONFLICT:  AssemblyP1/Issue94TW6Lemma1.lean
94-tw8-contraction       CONFLICT:  AssemblyP1.lean
```

* **Why here and not later:** see §1.6. Placing it after tw6 risks deleting two modules; placing
  it here is provably clean and provably lossless.
* **Escalation flag — a mathematical/textual decision, not mine:** `94-doc-corrections` edits
  `AssemblyP1/PopulationUniqueness.lean` and `BBTEulerian.lean` docstrings. If the eventual tw8
  repair or tw7 status note also rewrites the `hPevzner` status paragraph in those files, a
  **second** conflict appears that is a *truth* question (what is the current status of
  `hPevzner`), not a formatting one. At the tw4 point that does not happen, because tw5/tw6/tw7
  are merged *after* and win cleanly. Good. But if a future front rewrites that paragraph, the
  orchestrator must decide the final wording, not me.

### Step 3 — `94-tw7-altf` (the refutation tranche)

```
git merge --no-ff origin/94-tw7-altf -m "merge #94 tw7: Ukkonen + label-preserving => AltF = id is FALSE"
git push origin antonina/issue-89-final
```

* **Kind:** merge commit (tw7 is a child of tw6, which is now an ancestor, so this is
  effectively a fast-forward in the *content* sense — `--ff-only` will in fact succeed:
  `1ee7db8` is an ancestor of `b7b092c` and is the current tip after step 2. **Use
  `git merge --ff-only origin/94-tw7-altf`** and skip the merge commit.)
* **Files:** `AssemblyP1.lean` (+35/−7), `AssemblyP1/BBTUniqueEulerian.lean` (+33),
  `AssemblyP1/Issue94TW6Lemma1.lean` (+31/−7), `AssemblyP1/Issue94TW7AltF.lean` (new, 639).
* **Conflicts:** **none** against the state produced by steps 1–2. **[ESTABLISHED]** via trial.
* **Content warning a human reviewer must read:** this tranche *refutes* a step the board had been
  treating as the last purely combinatorial one. It is a genuine negative result, kernel-checked,
  and it is supposed to land. **[RELAYED]** from `BOARD94-TW7-ALTF.md` §0/§1 and the commit
  message: `altF_eq_id_iff_rotation`, refutation at `S = 0101, G = 4, L = 3, σ = tau4`. I did
  not compile and cannot confirm the kernel check.

### Step 4 — `fix/94-tw6-dochonesty` — **BLOCKED, needs an orchestrator decision**

See §3.3 and §5.

### Step 5 — tw8 — **conditional, see §4**

```
git merge --no-ff origin/94-tw8-contraction    # or origin/fix/94-tw8-typecheck, see §4
```

* **Conflicts against steps 1–3:** `AssemblyP1.lean`, one file, **two hunks**, both mechanical
  (see §4.2).

### Step 6 — the review refs — **MUST NOT LAND.** See §6.

### 3.3 The one real conflict: tw7 vs `fix/94-tw6-dochonesty` — ESCALATION

Found by trial merge:

```
$ git reset --hard 1ee7db8
$ git merge --no-commit --no-ff origin/94-tw7-altf && git commit
$ git merge --no-commit --no-ff origin/fix/94-tw6-dochonesty
CONFLICT: AssemblyP1/Issue94TW6Lemma1.lean   (2 hunks)
```

Both sides quote, for the module docstring §0:

**tw7 side (`HEAD`, 94eb's wording):**

> The **unrestricted** form of the source's degree fact — *any vertex of
> out-degree at least three forces a maximal triple repeat of length `≥ K`* — is
> **FALSE** … `0, 3, 6` … and **at those three starts, at
> each of the lengths `e = 3`, `4` and `8`, there is no maximal triple repeat**
> … so the `Ukkonen` triple
> clause and the `P2` triple clause both hold on this instance. …

**`fix/94-tw6-dochonesty` side (94ed's wording):**

> The form of the source's degree fact that needs no condition on the word —
> … §7 proves `¬ IsTripleRepeat e 0 3 6` for exactly those three `e`: the
> lengths `5, 6, 7` and all other triples of starts are *not* checked, so the
> `≥ K` reading of the degree fact is not refuted here either. … this section does
> *not* establish … nor that it satisfies the `Ukkonen` / `P2` triple
> clauses, which range over all triples and all lengths `≥ K`; the `≥ K` form of
> the degree fact is left open here.

**These are not two phrasings of one truth. They are contradictory claims about the same
`012012012` instance.** tw7 asserts "`Ukkonen` and `P2` triple clauses **both hold** here";
dochonesty asserts the file **does not establish** that, because those clauses quantify over all
triples and all lengths `≥ K` while §7 only checks one triple at `e = 3, 4, 8`. Both fronts also
differ on whether the "unrestricted `≥ K`" reading is refuted: tw7 says yes, dochonesty says
"not refuted here either".

**I am not authorised to pick a side and I will not.** Choosing is a *mathematical* decision about
what the kernel-checked file actually establishes, and the two fronts are both credible and both
kernel-checked. The resolution needs the orchestrator (or the tw7/94ed fronts) to agree on the
**scope claim**, and then the resolution is mechanical: take the agreed sentence, keep the
shared "one triple, three lengths" scope limit that **both** sides already contain, and drop the
contradictory clause. My reading, offered as a reading and not a decision: **dochonesty's version
is the more defensible scope statement**, because the file demonstrably contains only
`no_tripleRepeat_012012012`, `no_tripleRepeat4_...`, `no_tripleRepeat8_...` — three named facts at
one triple, and a `∀`/`∃` over `Fin 9` was, per tw7's own commit message, a `Decidable` instance
search that was not done. But that is a pointer, not a resolution.

There is a second, milder overlap in the same file: both fronts independently corrected
`mem_span_zero`'s docstring and the `§7` heading. Those two edits are *compatible* and the merge
will take both; only the two quoted hunks are contested.

**Practical unblock:** if the orchestrator takes ~10 minutes to choose, tw7 lands tonight and
dochonesty lands in a second commit right after. If the choice is not made, **land tw7 alone**
(step 3) and leave `fix/94-tw6-dochonesty` off the branch, recording in the report file that the
docstring correction is pending a scope decision. Do not silently drop it — see §5.

---

## 4. THE TW8 DEPENDENCY, HANDLED EXPLICITLY

### 4.1 What can land WITHOUT tw8 — most of it

**[ESTABLISHED]** Steps 1, 2 and 3 above are entirely independent of tw8. They take
`7d50132` to `b7b092c`-content: tw1, tw2, tw3, tw4, tw5, tw6, `94-doc-corrections`, tw7. That is
**seven of the eight tranches plus the documentation tranche**, and the branch is reviewable and
green-eligible without tw8 existing at all.

**tw8's status does not block the branch.** This is the single most useful fact in this report.

### 4.2 The tw8 conflicts are mechanical (whenever tw8 lands)

```
$ git reset --hard origin/94-tw6-lemma1
$ git merge --no-commit --no-ff origin/94-tw7-altf && git commit
$ git merge --no-commit --no-ff origin/94-tw8-contraction
CONFLICT: AssemblyP1.lean   (2 hunks)
```

Hunk 1, the import block — resolution: **keep both lines**, in this order.

```diff
  import AssemblyP1.Issue94TW6Lemma1
-<<<<<<< HEAD
  import AssemblyP1.Issue94TW7AltF
-=======
  import AssemblyP1.Issue94TW8Contraction
->>>>>>> origin/94-tw8-contraction
```

tw7's module imports nothing tw8 imports, and `Issue94TW8Contraction.lean` imports only
`BBTUniqueEulerian`, `Issue94TW6Lemma1` and Mathlib (I read the header). So the two are
independent and the union is correct. **[ESTABLISHED] by reading the import headers.**

Hunk 2, the `#print axioms` tail — resolution: **keep both blocks**, tw7's 17 lines then tw8's
34 lines, each under its own `/-! … -/` banner. They are disjoint lists of different
declarations. **[ESTABLISHED]** by reading both diffs.

**No conflict in any `.lean` file other than `AssemblyP1.lean`,** and no conflict in `docs/`.
**[ESTABLISHED]** by trial merge.

### 4.3 Plan A — the repair succeeds

`origin/fix/94-tw8-typecheck` **does not exist on the remote right now**
(`git ls-remote origin 'refs/heads/fix/94-tw8*'` → empty). So Plan A is contingent on a ref that
does not yet exist. When it appears:

```
git fetch origin fix/94-tw8-typecheck:refs/remotes/origin/fix/94-tw8-typecheck
git merge --no-ff origin/fix/94-tw8-typecheck -m "merge #94 tw8 repair: contraction rule typechecks"
```

Then resolve the two `AssemblyP1.lean` hunks exactly as in §4.2, run `lake build --wfail` and
`lake env lean` axiom audit, and push.

**Precondition the repair front must satisfy, and must state:** its merge-base against `1ee7db8`
must still be `1ee7db8`, or (if it has rebased/merged tw7) the `AssemblyP1.lean` hunk-1
resolution above may already be moot. Check with
`git merge-base origin/fix/94-tw8-typecheck origin/94-tw7-altf` before merging. **[ESTABLISHED
that the check is the right one; the answer is unknown until the ref exists.]**

### 4.4 Plan B — the repair does not succeed

**tw8 does not land. The branch is still complete and mergeable.** Concretely:

* Do **not** merge `origin/94-tw8-contraction` (`cd430b4`). It must never reach the one ref a
  human reviews, because it is under an independent CHANGES-REQUIRED verdict.
* Do **not** partially apply it (no cherry-pick of the `AssemblyP1.lean` import line alone).
* Record the tw8 status in `docs/` on the branch: the contraction rule of `Defn. d:condensed` is
  *staged but not integrated*; `hPevzner` remains undischarged partly because the condensation
  route is not in the tree. That is a documentation commit and is safe.
* The branch is then "tw1–tw7 + doc corrections", which is the correct deliverable for a
  tranche programme in which one of eight fronts returned CHANGES-REQUIRED. The definition of
  done asks for "all required work"; a front that is not in a reviewable state is not required
  work, and shipping a non-compiling module to satisfy a count would be the wrong trade.

### 4.5 What I could not settle about tw8, and who must

**[RELAYED]** `docs/board94-tw8-review.md` (on `origin/review/94-tw8-contraction`) is a
**CHANGES-REQUIRED** verdict: `card_contractNodes_lt` contains "two independent term-level type
errors (lines 126 and 146) against the pinned Mathlib/Lean-core signatures, so the committed
source cannot be the source that reported `lake build --wfail`: exit 0".

**[ESTABLISHED by me, static]** I read `card_contractNodes_lt` at `cd430b4` (lines 121–146) and
can see the two suspicious steps the reviewer points at, in the same shape it describes:

* line ~126: `Finset.card_erase_of_mem (s := G.nodes.erase u) (a := v) (by …)` — the reviewer
  reports the pinned signature takes the hypothesis *before* the conclusion, not as a trailing
  `by` block.
* line ~146: `exact Nat.sub_lt hpos (show (0 : ℕ) < 1 by decide)` — the reviewer reports
  `Nat.sub_lt` does not have this shape at the pinned `lean4 v4.34.0`.

**I could not confirm either statically and did not compile.** I have no `.lake` and am barred
from creating one. The command that settles it, which the repair front owns:

```
lake build --wfail            # or, narrowly:
lake env lean AssemblyP1/Issue94TW8Contraction.lean
```

My own contribution here is only: the module **has no `sorry`/`admit`/`axiom`/`native_decide`**
(grep over the 544-line file finds the word only inside a prose line at 426: "No `sorry`, no
`admit`, no `native_decide`, no new axiom"), so the CHANGES-REQUIRED verdict is a *type error*,
not a soundness escape. That is a real, if small, piece of information for the repair front.
**[ESTABLISHED]**

---

## 5. THE DOCSTRING CORRECTION'S TRAVEL — VERIFIED

`fix/94-tw6-dochonesty` (`0733b76`) exists precisely so a docstring correction travels **with**
the lemma rather than being stranded on a side branch. Verification that every changed line is a
comment and nothing else:

```
$ git diff 1ee7db8 origin/fix/94-tw6-dochonesty
```

**Files touched: exactly one** — `AssemblyP1/Issue94TW6Lemma1.lean` (24 insertions, 11
deletions). Nothing else in the repository is modified.

**Every changed line is inside a Lean block comment.** The grep for any changed line matching
`^[-+]` and *not* matching `^\s*(-/|/\*|\*|$)` returns only prose; the grep for changed lines
containing `theorem|lemma|def |instance|axiom|sorry|admit|:=|:=` returns exactly two hits, both
of which are the closing `-/` of a docstring:

```
-explains the instance: the least period is `3 < 9`. -/
+the instance: the least period is `3 < 9`. -/
```

The three hunks are at `@@ -24,6 +24,10 @@` (module `/-! -/` docstring), `@@ -655 +659 @@` and
`@@ -659,4 +663,13 @@` (the `/-- … -/` docstring on `deg_fact_escape_only`). All three are
inside comment blocks in the file as committed.

**VERIFICATION PASSES.** No `def`, no `theorem` statement, no `instance`, no `sorry`, no `admit`,
no `axiom` is added, removed or altered. The commit cannot change what the module proves.

### 5.1 Where it must land in my order

**Immediately after step 3 (tw7), as its own commit — and it may not be skipped.**

The reason is §3.3: it conflicts with tw7. If the orchestrator takes tw7's side of that conflict
and drops the dochonesty commit, the file ends up saying the counterexample is a global refutation
of the `≥ K` form — which is exactly the overclaim tw7's own commit message says it was
*correcting*. Dropping it would re-introduce the error in the branch that a human is about to
merge. If the orchestrator takes dochonesty's side, the commit still has work to do (the
`mem_span_zero` docstring and the `§7` heading, which tw7 also touched but compatibly).

So: **`fix/94-tw6-dochonesty` is not optional, and it is not a fast-forward once tw7 is in.** It
must be a deliberate, resolved merge. If the scope decision is not made, leave it off and say so
in the report — do not let the branch imply the correction landed.

---

## 6. WHAT MUST NOT LAND, AND WHY

**`origin/review/94-tw6-lemma1` (`02d466f`) and `origin/review/94-tw8-contraction` (`0984dac`)
must not be integrated as content on `antonina/issue-89-final`.**

**[ESTABLISHED]** What each adds:

* `review/94-tw6-lemma1` adds **one file**, `BOARD94-TW6-REVIEW.md`, 521 lines, and **touches no
  `.lean` file at all.** Its own commit subject: "independent review of tw6 — APPROVE-WITH-FINDINGS".
* `review/94-tw8-contraction` (`0984dac`) is a child of `cd430b4` and re-adds tw8's two files
  *plus* `docs/board94-tw8-review.md` (510 lines). **Merging it would drag the non-compiling tw8
  module onto the branch** — the single worst outcome available. It is doubly forbidden: it is a
  review record, and it is a carrier for the very content §4.4 forbids.

They are *documentation of findings about* mathematical work, not mathematical work. Landing them
would put a reviewer's verdict in the same commit graph as the thing it reviews, which destroys
the independence that makes the review worth anything, and would put `lake build` output-scope
chatter into the library CI's view.

**Where the findings must be recorded instead:**

* `review/94-tw6-lemma1`'s findings → the branch's own docs, e.g.
  `docs/board94-tw6-review.md`, plus the review report file
  `/workspace/BOARD94-TW6-REVIEW.md` which already exists outside the repo. The **substantive**
  findings (must-fix 1 the overclaimed counterexample scope, must-fix 2 the `BBTUniqueEulerian`
  docstring, findings 3 and 7) are *already actioned inside tw7's commit* — I read the tw7 diff
  and it does exactly those. So the record is: cite the review in the docs, do not merge its
  commit.
* `review/94-tw8-contraction`'s findings → `docs/board94-tw8-review.md` (the file it contains)
  copied **as text** by a documentation commit, or referenced from
  `/workspace/BOARD94-TW8-REVIEW.md`. **Never by merging `0984dac`.** If the branch needs to
  record that tw8 is staged-but-blocked, that is a new docs commit naming the review, not a merge
  of the review branch.

**[ESTABLISHED]** Note for the docs path: `scripts/check-research-docs.py` (a CI job — §8) walks
`docs/**/*.md` and fails on **merge-conflict markers** and on **unresolvable relative markdown
links**. Any review file moved into `docs/` must have its relative links checked. It also requires
`docs/skills/README.md` to list every `docs/skills/*.md`, which is unaffected by new files in
`docs/` root. **[ESTABLISHED]** by reading the script.

---

## 7. HONEST REMAINING WORK

The endpoint, in the issue's terms: **primitive `P2` + same complete spectrum ⟹ same genome up to
rotation**, i.e. discharge `BBTEulerian.EulerianCycleObstruction` (`hPevzner`).

### 7.1 What I read myself

**[ESTABLISHED]** `AssemblyP1/PopulationUniqueness.lean` — I opened the file and read the three
sites. `hPevzner : EulerianCycleObstruction (α := α) L` is a **binder of a hypothesis**, at:

* line **164**, in `population_unique_ML_up_to_rotation`, alongside `hPrimS : IsPrimitive S` and
  `hP2S : P2 hG L S` — the whole-population statement;
* line **217**, in `population_unique_ML_up_to_rotation_same_length`;
* line **247**, in the `RotEquiv` conclusion theorem, which *consumes* the 217 one.

So it is a hypothesis at **164, 217 and 247**, and it is threaded, not discharged. A sibling front
reported the same three line numbers; **I confirm them from my own read, and the confirmation is
independent** because I read the file rather than the report.

**[ESTABLISHED]** `BBTEulerian.UniqueEulerianCycle` is **not proved**. `grep -rn UniqueEulerianCycle`
over the tree finds it *referenced* in 20+ places, always as (a) a characterisation
(`Issue94TW5Single`: "`BBTEulerian.UniqueEulerianCycle`, characterised"), (b) a hypothesis of
downstream lemmas (`Issue94TW1EdgeType.lean:572, 581` take `h : BBTEulerian.UniqueEulerianCycle`),
or (c) prose. There is **no `theorem UniqueEulerianCycle`** — it is a `def`/`Prop` in
`BBTEulerian.lean` and is never closed. `Issue94TW5Single.lean:130` says so in its own words:
"**Not proved.** `BBTEulerian.UniqueEulerianCycle`". **[ESTABLISHED]**

### 7.2 What I am relaying

**[RELAYED]** From `/workspace/BOARD94-TW7-ALTF.md` §0, §1, §10 (tw7's own report; I read those
sections and did not verify the mathematics):

* tw7's assigned obligation "`Ukkonen` + label-preserving ⟹ `AltF = id`" is **FALSE**, with a
  kernel-checked counterexample at `S = 0101, G = 4, L = 3, σ = tau4`.
* The correct target is `VertexCycleEq`, not `AltF = id`, and `traverses ⟹ VertexCycleEq` is
  **NOT proved**, resisted at two points: (i) the point-level chain
  `σ (rotAdd n y) = rotAdd n (σ 0)` does not follow from a vertex-level induction hypothesis,
  and (ii) `vtx_nextPos_shift` loses the last coordinate of the node at every step.
* tw7's own §10 recommendation for the next front: **close the `n` residual coordinates of
  `node_prefix`** — prove that a non-identity label-preserving `AltF` must move a point in the
  last `L - G + 1` coordinates. It names the hypothesis as already in the tree
  (`Issue94TW6Lemma1.prim_deg_le_two`), says it is a corollary of the pre-existing
  `P2.imp_nodeCount_le_two`, and says the missing step is exactly `Ukkonen`'s interleaved /
  clause-2 — which **tw5 §9 point 3 had declared unnecessary**. Per tw7, the crossing clause is
  not optional.
* tw7 also flags `AssemblyP1/BBTTripleBridge.lean` as dead, non-compiling, and actively
  misleading. **[RELAYED for "non-compiling"; ESTABLISHED for CI-relevance — I checked.]**
  `AssemblyP1/BBTTripleBridge.lean` **does exist** on `origin/94-tw7-altf`
  (`git cat-file -e origin/94-tw7-altf:AssemblyP1/BBTTripleBridge.lean` → yes) **but is not
  imported by `AssemblyP1.lean`** (`git grep -n BBTTripleBridge origin/94-tw7-altf --
  AssemblyP1.lean` → no hits). So it is **not in the `AssemblyP1` build root** and on this
  evidence **cannot fail CI** (§8.1 roots both the build and the axiom audit at `AssemblyP1`).
  It is a Step-1 **non**-blocker; the residual risk is reader misleading, not build failure.
  I did **not** verify that it fails to compile — that is the relayed part.

### 7.3 The gap, stated plainly

**[ESTABLISHED]** The endpoint is **not** reached by this tranche programme, and no ordering of
these refs changes that. The gap is the left disjunct of `EulerianCycleObstruction`: nothing in
tw1–tw8 discharges `hPevzner`, and after tw7 the *previously planned* route to it
(`AltF = id`) is refuted. What is left is a genuinely new theorem (the `node_prefix` residual
closure) whose hypothesis `Ukkonen`'s crossing clause must supply — a step the board had
explicitly written off as unnecessary and which is now, on tw7's account, load-bearing.

**[RELAYED]** `BOARD94-VERDICT.md` exists; I read its section headings (§1 grid completeness, §2
independent reproduction of 2490/2166, §3 failure-mode split, §4 "Is P2 load-bearing?", §5 the
`eight` guard rows, §6 the docstring discrepancy, §7 "what this verdict is worth", §8 "what I
could not establish") but **I did not read its body** and therefore draw no conclusion from it
here. It is a *sweep* verdict about a computational search, not a proof of the endpoint, and its
§7/§8 self-assessment is the part that would matter. Flagged for the next front, not used.

**Bottom line for the orchestrator:** the correct end state of *this* issue is a branch that
carries tw1–tw7 plus the documentation corrections, is green, and states plainly that
`hPevzner` is undischarged and that the board's `AltF = id` step is refuted. That is a complete,
honest, mergeable deliverable. Claiming the endpoint is closed would be false.

---

## 8. THE MERGEABILITY CHECKLIST

Definition of done: `antonina/issue-89-final` **applies cleanly to current main**, **contains all
required work**, **is ready for an ordinary merge without additional mathematical work**, **all
branch CI checks are green**.

### 8.1 What CI actually runs — read from `.github/workflows`

**[ESTABLISHED]** Two workflows, `ci.yml` and `documents.yml`, both
`on: push/pull_request → branches: ["main"]` plus `workflow_dispatch:`.

`ci.yml`, two jobs:

1. **`research-docs`** — `python3 scripts/check-research-docs.py`. Checks: 15 required files
   exist; `docs/skills/README.md` lists every `docs/skills/*.md`; every markdown file in
   `README.md`, `AGENTS.md` and `docs/**/*.md` has **no merge-conflict marker** and **no
   unresolvable relative link**.
2. **`build`** — `leanprover/lean-action@v1` with `build: true`, `build-args: --wfail`,
   `axiom-audit: true`, `axiom-audit-root: AssemblyP1`. **This is the strict one:** any warning
   fails the build, and the axiom audit runs over the whole `AssemblyP1` root, so any `sorryAx`
   in a merged module fails CI.

`documents.yml`, one job `pdfs`: installs **GNU Guix** via `PromyLOPh/guix-install-action@v1`, then
`bash ./paper/build.sh` and `bash ./talk/build.sh`, and uploads `paper/main.pdf` and
`talk/main.pdf` as artifacts (`if-no-files-found: error`). **[ESTABLISHED]** This is a *separate*
workflow and it needs Guix; it is not the Antonina root build/test chain (which another issue's
agent holds) — but it will run on a PR to `main` and it must pass.

**Consequence for the plan:** `--wfail` means a tw8 with a type error, or any module with an
unused-variable/unused-simp-arg warning, fails CI. The worktrees carry
`set_option linter.unusedSectionVars false` etc. for exactly this reason; any new module must too.

### 8.2 The checklist, with the command that demonstrates each item

| # | Requirement | Command | Pass condition |
| --- | --- | --- | --- |
| 1 | No history rewrite; branch is main + issue-89-final + merges | `git merge-base --is-ancestor origin/main origin/antonina/issue-89-final && echo yes` | prints `yes`. **Already true for every tranche** (§1.3), so this holds by construction. |
| 2 | Applies cleanly to **current** main | `git fetch origin && git merge-tree $(git merge-base origin/main origin/antonina/issue-89-final) origin/main origin/antonina/issue-89-final \| grep -c '<<<<<<<'` | `0`. Given (1), this is trivially clean; re-run after the final `main` moves. |
| 3 | tw1 present | `git merge-base --is-ancestor origin/94-tw1-best origin/antonina/issue-89-final && echo yes` | `yes` — true from step 1 via `b8bcbb5`. |
| 4 | tw2–tw6 present | `for r in tw2-edgetype tw3-residual tw4-eulerian tw5-lambda tw6-lemma1; do git merge-base --is-ancestor origin/94-$r origin/antonina/issue-89-final \|\| echo MISSING $r; done` | no output. |
| 5 | `94-doc-corrections` present **and non-destructive** | `git merge-base --is-ancestor origin/94-doc-corrections origin/antonina/issue-89-final && git cat-file -e origin/antonina/issue-89-final:AssemblyP1/Issue94TW6Lemma1.lean && git cat-file -e origin/antonina/issue-89-final:AssemblyP1/Issue94TW5Single.lean && echo present` | prints `present`. **The two `cat-file` checks are the ones that catch the §1.6 trap** — they fail loudly if the merge dropped the modules, where a `git merge` "succeeds" silently. |
| 6 | tw7 present | `git merge-base --is-ancestor origin/94-tw7-altf origin/antonina/issue-89-final && echo yes` | `yes`. |
| 7 | dochonesty present, or its absence recorded | `git merge-base --is-ancestor origin/fix/94-tw6-dochonesty origin/antonina/issue-89-final && echo yes` | `yes`, **or** the report states the pending scope decision (§5.1). Silent absence is the only failure mode. |
| 8 | tw8 either present-and-green or absent | `git cat-file -e origin/antonina/issue-89-final:AssemblyP1/Issue94TW8Contraction.lean 2>/dev/null && echo "tw8 LANDED - must be green" \|\| echo "tw8 absent - OK"` | either is acceptable; **landing a non-compiling tw8 is the failure.** |
| 9 | Review branches did **not** land as content | `git log origin/antonina/issue-89-final --oneline -- BOARD94-TW6-REVIEW.md docs/board94-tw8-review.md` | empty, or showing only a hand-written docs commit (not a merge of `02d466f`/`0984dac`). Cross-check: `git log origin/antonina/issue-89-final --merges --oneline` contains neither `02d466f` nor `0984dac`. |
| 10 | No `sorry`/`admit`/`axiom` in the library | `git grep -nE '\bsorry\b|\badmit\b|^ *axiom ' origin/antonina/issue-89-final -- 'AssemblyP1/*.lean'` | only prose mentions, as at tw8:426. **This is the axiom-audit job's job too.** |
| 11 | Build green, warnings fatal | `lake build --wfail` | exit 0. **Not establishable by me — a sibling front holds the Lean window.** |
| 12 | Axiom audit | `lake env lean` with `#print axioms` for every new theorem, or the lean-action axiom-audit | no `sorryAx`. **Not establishable by me.** |
| 13 | Research-doc integrity | `python3 scripts/check-research-docs.py` | exit 0. Cheap; any front can run it. `python3` is **not on this worktree's PATH** (I got `command not found`), so run it in an environment that has it. |
| 14 | Paper + talk build | `bash ./paper/build.sh && bash ./talk/build.sh` | exit 0. Requires Guix; not run by me. |
| 15 | Endpoint honestly described | `grep -n 'hPevzner' AssemblyP1/PopulationUniqueness.lean` | still a hypothesis at 164/217/247 — and the branch **says so**. This is not a failure of the checklist; it is the honest description the issue asks for. |
| 16 | Not merged to main, no other refs touched | `git ls-remote origin refs/heads/antonina refs/heads/fix/94-tw8-typecheck refs/heads/review/94-tw6-lemma1` | no new refs created by the integration. Verify with `git ls-remote origin \| diff` against the pre-integration listing. |
| 17 | Branch is a fast-forward of its own remote (no force) | `git push --dry-run origin antonina/issue-89-final` | reports up to date / fast-forward. **Never** use `--force`. |

### 8.3 Items 11, 12 and 14 I cannot discharge

**[ESTABLISHED]** I ran no `lake`, no `elan`, no `lean`; I have no `.lake` in this worktree and
per my brief must not create one. Items 11, 12 and 14 are therefore **not establishable by me**.
The commands that establish them are in the table. The orchestrator must run them, or route them
to the front that holds the Lean compilation window. This is a statement of a limit, not a hedge:
items 1–10, 13, 15, 16, 17 are all `git`-only and I have run every one of them above.

---

## 9. ONE-PAGE SUMMARY FOR THE NEXT FRONT

```
1. git merge --ff-only origin/94-tw4-eulerian                    # 6012bff
2. git merge --no-ff origin/94-doc-corrections                   # MUST be before tw5, or it eats two modules
3. git merge --ff-only origin/94-tw6-lemma1                      # 1ee7db8 - tw1..tw6 all in, free
4. git merge --ff-only origin/94-tw7-altf                        # b7b092c - refutation tranche
5. DECIDE the tw7 vs fix/94-tw6-dochonesty docstring scope clash  # ESCALATED in §3.3
6. git merge --no-ff origin/fix/94-tw6-dochonesty                # 2 hunks, needs step 5
7. tw8: merge origin/fix/94-tw8-typecheck if it appears, else SKIP
        2 mechanical AssemblyP1.lean hunks, keep both sides
8. NEVER merge review/94-tw6-lemma1 or review/94-tw8-contraction
```

Steps 1–4 need no mathematical judgement and are verified conflict-free. The branch is
reviewable after step 4, with or without tw8. `hPevzner` is not discharged; that is the honest
state of the programme, not a defect of this integration.
