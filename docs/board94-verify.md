# BOARD 94 — VERIFICATION AND RECONCILIATION

**Front:** independent verifier + reconciler. **Branch:** `review/94-tw8-repair-verify2` at `769a893`.
**Worktree:** `/workspace/assemblyp1-94-tw8verify`. **Pushed ref:** `review/94-tw8-repair-verify2` only.

**Role constraints I held:** read-only on every Lean source in the repository (I edited none, and I
created no `.lake` outside my own worktree). One markdown artefact. I did not comment on, close,
create or reorder any board issue, and I ran no `antonina board collect`. I read board issue 94 only.
I did not write `/workspace/assemblyp1-94-verify` (751a48e); I read nothing from it and wrote nothing
to it.

**Tagging convention used throughout, and the orchestrator should rely on it:**

* **[MINE]** — established by me in this pass, by execution or by reading the tree/refs myself.
* **[RELAYED]** — taken from a report I did not independently check. Marked every time.
* **[REFUTED]** — a claim from a report that I checked and that does not hold.

Every `lake`/`lean` invocation in this report is preceded and followed by a real cgroup reading.

---

# PART 1 — VERIFICATION OF THE F1 REFUTATION

## 1.0 Memory discipline, every compilation

I read the cgroup before and after every `lake`/`lean` invocation. The operative figure is `anon` in
`/sys/fs/cgroup/memory.stat`. All figures in bytes; `GiB = bytes / 2^30`.

| # | command | anon before | anon after | `oom` / `oom_kill` after |
|---|---|---|---|---|
| 0 | `lake env lean --version` (toolchain check) | 7 330 279 424 | 7 391 715 328 | 20 / 12 |
| 1 | `lake env lean` on **ProbeBogus.lean** (harness validation) | 8 362 254 336 | 8 256 520 192 | 20 / 12 |
| 2 | `lake env lean` on **Base.lean** (cd430b4, byte-identical) | 7 350 059 008 | 7 363 530 752 | 20 / 12 |
| 3 | `lake env lean` on **Head.lean** (769a893, byte-identical) | 8 083 300 352 | 7 394 066 432 | 20 / 12 |
| 4 | `lake env lean` on Mechanism.lean (signature probes) | 5 875 937 280 | 5 873 905 664 | 20 / 12 |
| 5 | `lake env lean` on Mechanism2.lean (in-context `trace_state`) | 5 857 439 744 | 5 834 280 960 | 20 / 12 |
| 6 | `lake env lean` on Mechanism3.lean (isolated reproduction) | 6 648 803 072 | 6 754 533 376 | 20 / 12 |
| 7 | `lake env lean` on Mechanism4.lean (defeq probe) | 6 814 874 688 | 6 795 333 120 | 20 / 12 |
| 8 | `lake env lean` on Mechanism5.lean (defeq + `Full`) | 6 893 372 288 | 6 776 907 264 | 20 / 12 |
| 9–12 | `lake env lean` on AxiomAudit.lean, **four failed attempts** (see "What I could not establish" §17 for the four errors; all exit 1) | `anon` stayed in the band 6 780 000 000 – 6 940 000 000 across all four, read before and after each | same band | 20 / 12 after each |
| 13 | `lake env lean` on AxiomAudit.lean (**success**, `collectAxioms`) | 6 829 748 224 | 6 929 784 448 | 20 / 12 |
| 14 | `lake env lean` on HeadAudit.lean (fresh elaboration + audit) | 6 578 892 800 | 6 636 875 776 | 20 / 12 |
| 15 | `lake env lean` on **Mut.lean** (mutation test) | 6 649 131 008 | 6 430 044 160 | 20 / 12 |
| 16 | `lake build AssemblyP1.Issue94TW8Contraction` | 6 633 762 816 | — | 20 / 12 |
| 17 | `lake env lean AssemblyP1.lean` (aggregator) | 6 615 687 168 | 6 650 822 656 | 20 / 12 |
| 18 | `lake build --wfail` (first, background) | 6 643 425 280 | 6 565 904 384 | 20 / 12 |
| 19 | `lake build --wfail` (second, for a real exit code) | 6 581 620 736 | 6 617 280 512 | 20 / 12 |

**I never waited.** Peak `anon` across the whole session was 8 362 254 336 (7.79 GiB) at invocation
1, against the 20 GiB instruction threshold and the 30.00 GiB cap. I never approached the threshold,
so no compile was deferred. Reason: a warm `.lake` (see §1.1) means every invocation above is a
single-file elaboration against pre-built oleans, not a project rebuild; the two `lake build`
invocations (16, 19) re-used the olean graph copied from the repair worktree and completed in ~3 s.

**One counter I must report that the brief did not ask about.** `memory.events` `max` rose from
**853 549 to 853 849 (+300)** over the session, while `oom` stayed at 20 and `oom_kill` stayed at 12
and `oom_group_kill` stayed at 0. `max` counts events where the cgroup hit `memory.max` and had to
reclaim; it is not an OOM kill. The two counters the brief named as must-not-rise did not rise. I am
reporting the third because a later orchestrator diffing those counters will see it move and should
know it is not mine-by-kill. I did not isolate which invocation produced the +300.

## 1.1 Toolchain, established

```
$ git rev-parse --short HEAD                                   -> 769a893
$ cat lean-toolchain                                           -> leanprover/lean4:v4.34.0
$ grep -n mathlib lakefile.lean                                -> 7:require mathlib from git
                                                                     "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"
$ export PATH="$HOME/.elan/bin:$PATH"
$ lake env lean --version
Lean (version 4.34.0, x86_64-unknown-linux-gnu, commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b, Release)
version_exit=0
```

`lake` and `lean` are **not** on the default `PATH` on this host (`lake: command not found`, exit
127). They are at `$HOME/.elan/bin`. A front that reports a `lake` exit code without saying how it
put `lake` on `PATH` is one `PATH` edit away from a meaningless result. Recording this because it
is the first thing that will bite the next front.

I built `.lake` in my own worktree only: `.lake/packages` and `.lake/config` hardlinked and
`.lake/build` copied from `/workspace/assemblyp1-94-tw8-repair/.lake` (read-only use of another
worktree's directory; I wrote nothing there). Result: 8.4 G, `lake env lean --version` exit 0.

## 1.2 Step 1 — base, repair commit, byte identity

```
$ git merge-base --is-ancestor cd430b4 769a893
isancestor_exit=0

$ git log --oneline cd430b4..769a893
769a893 #94 tw8 repair: F2/F3 fidelity, F4-F7 corrections, and a machine-checked gap witness
log_exit=0

$ git show --stat 769a893
 AssemblyP1/Issue94TW8Contraction.lean | 372 +++++++++++++++++++++++++++-------
 1 file changed, 300 insertions(+), 72 deletions(-)

$ git rev-parse cd430b4:AssemblyP1/Issue94TW8Contraction.lean  -> 37ae4bfc1838e193132ce76cccf656eff8b0c596
$ git rev-parse 769a893:AssemblyP1/Issue94TW8Contraction.lean  -> 99d8a131f458aede061d6e8a0c709ec495e10007
```

**[MINE]** The repair commit changes **one file**, `AssemblyP1/Issue94TW8Contraction.lean`, +300/−72.
It is a direct child of `cd430b4`. The `+300` is documentation and added `decide` theorems; §2.5
below shows the two F1 proof terms are byte-identical between the two versions, which is the
substantive version of 94ee's "I changed no proof term".

## 1.3 Step 2 — HARNESS VALIDATION (done before any clean run was trusted)

A green elaboration on a file you expect to be broken is exactly the result to distrust, so this came
first.

```
$ git show cd430b4:AssemblyP1/Issue94TW8Contraction.lean > /tmp/opencode/tw8scratch/Base.lean
$ cp Base.lean ProbeBogus.lean
$ printf '\ntheorem _probe_bogus : (1 : Nat) = 2 := by rfl\n' >> ProbeBogus.lean
$ lake env lean /tmp/opencode/tw8scratch/ProbeBogus.lean
PROBE_EXIT=1
stdout:
  /tmp/opencode/tw8scratch/ProbeBogus.lean:546:43: error: Tactic `rfl` failed: The left-hand side
    1
  is not definitionally equal to the right-hand side
    2

  ⊢ 1 = 2
```

**The harness reports errors from this file, with a non-zero exit code.** The clean runs in §1.4 and
§1.5 are therefore real clean runs. `anon` before 8 362 254 336, after 8 256 520 192.

## 1.4 Step 3 — BASE `cd430b4`, byte-identical, elaborated

```
$ git cat-file blob cd430b4:AssemblyP1/Issue94TW8Contraction.lean | sha256sum
8df0c76912dd699ae04e0e1e30583f38660e32975b05583415de95e6426f4832  -
$ sha256sum /tmp/opencode/tw8scratch/Base.lean
8df0c76912dd699ae04e0e1e30583f38660e32975b05583415de95e6426f4832  /tmp/opencode/tw8scratch/Base.lean
$ git cat-file blob cd430b4:AssemblyP1/Issue94TW8Contraction.lean | cmp - Base.lean
CMP_IDENTICAL=yes

$ lake env lean /tmp/opencode/tw8scratch/Base.lean
BASE_EXIT=0
real 0m3.161s
--- stdout bytes: 0 ---
--- stderr bytes: 0 ---
```

**[MINE] The committed source at `cd430b4` elaborates with exit 0, no output, from a byte-identical
scratch copy.** `anon` before 7 350 059 008, after 7 363 530 752. The 3.2 s wall time is short; that
is expected because all imports resolve to pre-built oleans, and §1.3 already proved the same
invocation reports errors from this file when there are any.

## 1.5 Step 4 — HEAD `769a893`, byte-identical, elaborated

```
$ git cat-file blob 769a893:AssemblyP1/Issue94TW8Contraction.lean | cmp - /tmp/opencode/tw8scratch/Head.lean
CMP_IDENTICAL=yes
$ lake env lean /tmp/opencode/tw8scratch/Head.lean
HEAD_EXIT=0
real 0m3.642s
--- stdout bytes: 0 ---
--- stderr bytes: 0 ---
```

`anon` before 8 083 300 352, after 7 394 066 432. Both bases elaborate.

## 1.6 The mechanism of both misreadings — established from the pinned sources, not from either document

I read the pinned signatures myself and then ran four probes to find out *why* the review's reading
does not produce an error. This is the part of the brief that says the error lies in where the tactic
block sits, and it is correct, but the reason is more specific and more interesting than either
document states.

### The pinned signatures, quoted by me from the tree at this commit

```
$ sed -n '45,50p' .lake/packages/mathlib/Mathlib/Data/Finset/Disjoint.lean
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht => notMem_empty a <|
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h _ hs ht _ ha => (h (hs ha) (ht ha)).elim⟩
```

`.lake/packages/mathlib/Mathlib/Data/Finset/Disjoint.lean:47` is that line. **The review quoted
`Finset.disjoint_left` correctly.**

```
$ sed -n '356,357p' ~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Nat/Lemmas.lean
protected theorem sub_lt_of_pos_le (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b :=
  Nat.sub_lt (Nat.lt_of_lt_of_le h₀ h₁) h₀
```

**The review's citation of `Init/Data/Nat/Lemmas.lean:356-357` is wrong.** Those two lines define
`Nat.sub_lt_of_pos_le`, not `Nat.sub_lt`, and the *arguments are reversed* relative to the review's
claim: here `h₀ : 0 < a` fills the **second** slot. The review read `0 < n` as `n < n + m`.

```
$ printf '#check @Nat.sub_lt\n' ... ; lake env lean <file>
@Nat.sub_lt : ∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
@Finset.disjoint_left : ∀ {α : Type u_1} {s t : Finset α}, Disjoint s t ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
@Finset.mem_singleton : ∀ {α : Type u_1} {a b : α}, b ∈ {a} ↔ b = a
Finset.mem_singleton.mp : ?m.3 ∈ {?m.2} → ?m.3 = ?m.2
```

### F1(a), base line 126 — why `Finset.mem_singleton.mp h2` is the right term

Base line 126 is, verbatim (`sed -n '121,127p'` of the byte-identical scratch copy):

```lean
  have hdisj : Disjoint ((G.nodes.erase u).erase v) ({Merge u v} : Finset (List α)) := by
    refine Finset.disjoint_left.2 (fun {a : List α} h1 h2 => ?_)
    exact merge_not_mem_erase G u v hw (Finset.mem_singleton.mp h2 ▸ h1)
```

I put the file's own preamble (lines 1–120, which contain `Merge`, `SeqGraph`, `contractNodes`,
`merge_not_mem_erase` byte-for-byte) into a scratch file, added the same block inside an `example`,
and asked Lean for the state, both plain and with `pp.explicit`:

```
a : List α
h1 : @Membership.mem List α (Finset (List α)) … (Finset.erase … (Finset.erase (SeqGraph.nodes α G) u) v) a
h2 : @Membership.mem List α (Finset (List α)) … (@singleton … (@Merge α u v)) a
⊢ False
```

`h2` has **positive** type `a ∈ {Merge u v}`. Not `a ∉ {Merge u v}`. And I forced the question in a
second scratch file, minimal and standalone:

```lean
theorem D (s : Finset α) (m : α) (hw : m ∉ s) : Disjoint s ({m} : Finset α) := by
  refine Finset.disjoint_left.2 (fun {a : α} h1 h2 => ?_)
  have : (a ∉ ({m} : Finset α)) := h2
  trivial
```
```
Mechanism3.lean:32:35: error: Type mismatch
  h2 has type  a ∈ {m}  but is expected to have type  a ∉ {m}
```

**There is no elaboration loophole and no unsoundness here.** The resolution is a single
definitional equality that the review never checked:

```lean
example (a m : α) : ((a ∈ ({m} : Finset α)) → False) = (a ∉ ({m} : Finset α)) := rfl
```

That example **elaborates with exit 0** (Mechanism5.lean, the only error in that run was a hole I
left in a `have` of my own). So:

* the *hypothesis* `h2` has type `a ∈ {Merge u v}` — a proof of membership, which is exactly what
  `Finset.mem_singleton.mp` consumes, giving `a = Merge u v`;
* the *function* the lambda builds has type `a ∈ s → a ∈ {Merge u v} → False`, which is
  **definitionally** `∀ ⦃a⦄, a ∈ s → a ∉ {Merge u v}`, i.e. exactly the type `Finset.disjoint_left.2`
  demands. The negation lives at the **codomain** of the lambda, not in the binder.

So the error in the review's reasoning is precisely the one the brief names: it read `a ∉ t` as the
type of the hypothesis `h2` when it is the type of the whole lambda, whose two domains are
`a ∈ s` and `a ∈ t` and whose codomain is `False`. `h2 ▸ h1 : Merge u v ∈ (G.nodes.erase u).erase v`,
and `merge_not_mem_erase G u v hw` closes `False`. The proof is sound and complete.

For completeness I also checked that the review's *argument* about the negative reading is right on
its own terms, so the disagreement really is only about placement: writing the lambda with its type
written out, `have h : ∀ ⦃a⦄, a ∈ s → a ∉ {m} := fun a h1 h2 => …` and using
`Finset.mem_singleton.mp h2` inside it **does** fail (`invalid ▸ notation, argument h1 has type
a ∈ s, equality expected`). Both halves of the review's reasoning are locally correct; the
conclusion is wrong because of where the block sits. **[MINE]**

### F1(b), base line 146 — why `Nat.sub_lt hpos (show 0 < 1 by decide)` is the right term

Base line 146 is, verbatim: `  exact Nat.sub_lt hpos (show (0 : ℕ) < 1 by decide)`. It supplies
**both** hypotheses. `hpos : 0 < G.nodes.card` fills the `0 < n` slot; `show (0:ℕ) < 1 by decide`
fills the `0 < m` slot, with `m := 1`, giving exactly `G.nodes.card - 1 < G.nodes.card`. The review
transcribed the line as `Nat.sub_lt hpos` and then correctly observed that a one-argument
application cannot typecheck — against a term that is not in the file. I confirmed the failure mode
is real for the term the review described:

```
example (n : Nat) (hpos : 0 < n) : n - 1 < n := by
  exact Nat.sub_lt hpos
```
```
Mechanism.lean:44:2: error: Type mismatch
  Nat.sub_lt hpos has type  0 < ?m.15 → n - ?m.15 < n
  but is expected to have type  n - 1 < n
```

The review's *arity* claim (two hypotheses) is right; its *signature*, its *line citation* and its
*transcription of the file* are all wrong, and the conclusion drawn from them does not hold.
**[MINE]**

## 1.7 F1 VERDICT

**F1 IS REFUTED. Both of the review's "CRITICAL type errors" are misreadings, and I established the
mechanism of each myself from the pinned sources, not from either document's account.**

Three independent facts support this and all three are mine:

1. The byte-identical base elaborates with **exit 0** (§1.4), on a harness **proven able to fail**
   (§1.3).
2. The in-context `trace_state` with `pp.explicit` shows `h2 : a ∈ {Merge u v}`, and the
   `refute`-by-`have` probe shows `h2` cannot be given the type `a ∉ {m}` (§1.6).
3. `(a ∈ {m}) → False` and `a ∉ {m}` are `rfl`-equal, so the lambda's type is *exactly* the iff's
   right-hand side (§1.6).

The consequence 94ee drew — that the recorded `exit 0, 8984 jobs` build claim is consistent with the
file, and that the review's inference that it "cannot be a build of this file" is withdrawn — follows.
I checked the build number myself rather than accepting it: see §1.8.

**What F1's refutation does NOT establish, and I want this on the record before anyone reads Part 1
as an endorsement.** A compiling module is not a correct module. F1 was a *type* claim; the module's
*statements* are a separate question, and F2 and F3 are exactly that question. 94ee says this itself
and it is the right framing. F1 being false is not a reason to relax anything about F2/F3.

## 1.8 Build validation — measured by me, not relayed

```
$ lake build AssemblyP1.Issue94TW8Contraction
Build completed successfully (8933 jobs).
exit 0
```
`anon` before 6 633 762 816. Note this is the **8933** figure, matching the repair report's §4 for
the repaired tree exactly. `lake` reports the size of the whole target graph, not the number of jobs
it ran, which is why a 3 s no-op run prints a five-digit number; do not read it as work done.

```
$ lake env lean AssemblyP1.lean          # the aggregator, against the HEAD oleans
AGG_EXIT=0
382 lines of #print axioms output
grep -ci error  -> 0
grep -c  sorryAx -> 0
```
`anon` before 6 615 687 168, after 6 650 822 656. This is the check the repair could not do: it
confirms that removing `import AssemblyP1.Issue94TW6Lemma1` from the tw8 file did not break the
aggregator, and that `AssemblyP1.lean:524`'s `#print axioms …Contract` still resolves.

```
$ lake build --wfail
FULLBUILD_EXIT=0
Build completed successfully (8984 jobs).
warnings=0  errors=0  sorryAx=0
```
`anon` before 6 581 620 736, after 6 617 280 512; `oom 20 / oom_kill 12` unchanged. **The full
project build at `769a893` is green, exit 0, 8984 jobs, zero warnings under `--wfail`, and the whole
library's axiom dump contains no `sorryAx`.** The 8984 figure the repair reported is reproduced
exactly.

## 1.9 F2 — `Contract` re-documented as a REDUCTION: CONFIRMED IN THE SOURCE

**[MINE]** I read the committed text at `769a893`.

* `contractEdges` docstring (lines 135–153): states the source's second step is "**NOT implemented
  here**", quotes the step, and gives the reason (labelled multigraph, overlap labels on the
  replacement edges, multiplicity push-forward; `SeqGraph.edges` is an unlabelled `Finset` with
  multiplicity in a separate `Mult G`), and states that a bare finset replacement "would falsify
  `edges_contract_subset`".
* `Contract` docstring (lines 155–170): "**A node-and-edge REDUCTION of `G` along `(u, v)` — NOT the
  source's one-step contraction.**" It names the absent step, states the result has no edge incident
  to `w`, and says explicitly "it is not offered as a transcription of `Defn. d:condensed`, and the
  earlier claim that it was has been withdrawn."
* Module docstring line 480: "An earlier version of this docstring called `Contract` a transcription
  of `Defn. d:condensed`; that claim was wrong and has been withdrawn."
* `edges_contract_subset` (189–192) carries a caveat: "must not be read as a statement about the
  source's condensation."
* Not-established item 4 (lines 565–580) now states which halves of the one-step rule are
  formalised (degree half of the permission, merge/erase, the measure) and which are not (the
  replacement step), and names the `olap(u,v) = |u| - 1` specialisation.

**Verdict: F2 is genuinely fixed as documented, and the gap is machine-checked rather than merely
asserted.** I verified the three gap theorems exist and are `by decide`: `merge_na_nb` (680),
`contractEdges_GA_na_nb` (686), `no_w_edge_after_contract` (691), `source_replacement_edges_absent`
(698). The whole file elaborates, so they close.

**The residual the report itself names, which I confirm is real:** the name `Contract` was **not**
changed, because `AssemblyP1.lean:524` is `#print axioms AssemblyP1.Issue94TW8Contraction.Contract`
— I read that line, and the report's claim about it is accurate. `AssemblyP1.lean` was outside 94ee's
ownership. So the module still exports a name that no longer means what its name suggests. **A
rename is a one-line change in `AssemblyP1.lean`, and someone with ownership of that file must
decide whether to make it.** It is an integration action item, not a defect in `769a893`.

## 1.10 F3 — overlap explicit, narrowing proved: CONFIRMED IN THE SOURCE

**[MINE]** `sed -n '40,86p'` of the committed file at `769a893`:

* `def MergeWith (o : ℕ) (u v : List α) : List α := u ++ v.drop o` — the overlap is a parameter, and
  the docstring says the source's parameter `olap(u,v)` "is a datum of the *edge* `e = (u,v)`, not of
  the nodes".
* `def Merge (u v : List α) : List α := MergeWith (u.length - 1) u v` — the specialisation is now
  visible **in the term**, not only in prose.
* `theorem mergeWith_eq_merge {u v} {o} (h : o = u.length - 1) : MergeWith o u v = Merge u v` —
  the exact condition, proved.
* `theorem merge_narrowing_witness : MergeWith 0 [0,1] [1,1,1] ≠ Merge [0,1] [1,1,1] := by decide` —
  the kernel-checked witness that the specialisation is a real narrowing. It elaborates, so it is
  checked.
* `Merge`'s docstring gives four things the review asked for: (i) the specialisation; (ii) why
  `|u| - 1` is right for consecutive `(L-1)`-mers; (iii) where it is **not** sound (non-de-Bruijn
  edges, `k`-mers with `k < L-1`, per-edge labels); (iv) that nothing in the repository states (ii)
  in an instantiable form.
* The `hw : Merge u v ∉ G.nodes` side condition is documented at 200–205 as having **no counterpart
  in the source** ("there `w` is a new node by fiat"), with the reason it is genuine here (a `Finset`
  of existing labels can already contain `w`).

**Verdict: F3 is genuinely fixed.** The overlap is a parameter, the specialisation is in the term,
the exact condition is proved, and the narrowing is kernel-checked. I add the honest limit, which
the report also states: the claim that `olap(u,v) = |u| - 1` is *right in the intended application*
remains **prose with a justification, not a Lean hypothesis**, because the `K`-mer multigraph of a
word does not exist in this repository. That is a real remaining gap and it is now labelled as one.

## 1.11 The SHOULD-FIX and NOTE items — my own verdicts

| id | 94ee's verdict | **my independent verdict** | what I checked |
|---|---|---|---|
| **F4** `NoTriple`/tw6 "RELAYED" | FIXED | **CONFIRMED, and the strongest of the SHOULD-FIXes** | `import AssemblyP1.Issue94TW6Lemma1` and `open AssemblyP1.Issue94TW6Lemma1` are both **gone** (lines 1–16); a comment at 18–22 says why. The `hCap` row (522) says "**Nothing from `Issue94TW6Lemma1` is used at the Lean level**: this module does not import it, and no identifier from it occurs here", calls the relationship "provenance", and denies that it is "tw6's theorem, relayed". Independence is now **structural**, not incidental. |
| **F5** "mutation goes red" overclaim | FIXED, scoped to the out-degree half | **CONFIRMED** | `not_balanced_GB : ¬ Balanced GB mB` exists (line 758) and elaborates; `wellFormed_GB` (734), `edgeSurj_GB` (742), `inMult_GB_a` (754) exist. The §6 preamble (533–537) now says the `GB` instance is *not* a refutation of the whole rule and that `Balanced GB mB` is **false**. **This directly fixes the claim sweep's T8-1**, which I verified was a genuine FALSE claim at `cd430b4` (§1.13). |
| **F6** the `2K-1` justification | FIXED | **CONFIRMED** | "unrestricted" survives nowhere in the `2K-1` context; line 500 reads "a merged node of length `K+1` (this is `Merge u v` at `|u| = |v| = K`, **not** `2K-1`, which would be the length at overlap `1`)", and the `List α` vs `Fin (L-1) → α` conversion is now stated as a required bridge lemma. |
| **F7** `decide +kernel` and the axioms claim | FIXED | **CONFIRMED** | `+kernel` appears only at 592–593 and 611, both times to say it is **not** used. Line 595 scopes the aggregator's 34 declarations: "the declarations added since are audited in the repair report, not in that list". See §1.12 — I checked that scoping claim and it is accurate, with one consequence for integration. |
| **F8** `deriving DecidableEq` | settled by the build | **CONFIRMED** | `lake build --wfail` exit 0, §1.8. |
| **F9** `Mult`'s vacuous parameter | documented | **CONFIRMED** | Lines 265–272: "`G` is **ignored**: `Mult G` is literally the type `(List α × List α) → ℕ`, so `Mult GA` and `Mult GB` are the same type and `mA`, `mB` are interchangeable", flagged as a trap for the bridge. |
| **F10** `inDeg` shadowing | documented | **CONFIRMED** | Lines 21–25: names `BBTCondense.lean:213` and says a bare `inDeg` in this file means the local one. |

I found **no** SHOULD-FIX or NOTE item that 94ee claims to have fixed and has not. That is a
statement about the four items above only, and I checked each in the committed text.

## 1.12 Non-vacuity — I re-ran the mutation test myself

This is the claim most worth distrusting, because a mutation test that reports success proves
nothing. **[MINE]**

I copied the HEAD file to a scratch path **outside the repository**, applied the mutation the report
describes (delete `(hCap : NoTriple m)` from `twiceTraversed_outDeg_eq_one`'s signature, replace
`exact absurd (hCap u (hwf (u, v) he).1) (by omega)` with a bare `omega`), and confirmed the
substitutions actually applied before running the compiler (my script exits 9 if they do not):

```
$ lake env lean /tmp/opencode/mut/Mut.lean
MUT_EXIT=1
Mut.lean:347:2: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  f ≥ 0   e ≥ 3   d ≥ 1   c ≥ 2   b ≥ 2   a ≥ 2   a - e + f ≤ 0
where
 a := ↑(m (u, v))          b := ↑(outDeg G u)        c := ↑(outEdges G u).card
 d := ↑((outEdges G u).erase (u, v)).card            e := ↑(nodeMult G m u)   f := ↑(m e₂)
Mut.lean:383:48: error: Application type mismatch: The argument
  hCap has type  NoTriple m  but is expected to have type  (?m.31, ?m.32) ∈ G.edges
  in the application  twiceTraversed_outDeg_eq_one hwf m hSurj hCap
```

`anon` before 6 649 131 008, after 6 430 044 160. **The mutation goes red, at the line the report
names, with the same constraint set.** The cap is the only thing closing that proof, and the
out-degree half of the contraction rule is not a tautology. I reproduce the report's §7 result
independently.

**What non-vacuity does and does not give you here, stated precisely.** The mutation establishes
that `hCap` is load-bearing for the out-degree half. It does **not** establish the report's
second non-vacuity claim, the `GA`/`mA` instance: the report itself relabels that as
*satisfiability*, not a mutation test, and I agree with the relabelling — `GA`/`mA` discharging
`wellFormed_GA`, `balanced_GA`, `edgeSurj_GA`, `noTriple_GA` and yielding `GA_ab_contractible` shows
the hypothesis class is inhabited, which is a weaker and different fact. The report is honest about
this and I am not going to upgrade it.

**The honest limit the report states for itself, which I confirm:** the refutation of the out-degree
half minus its cap is complete on an instance (`GB`) that is **not** `Balanced`, and the file says so
(533–537) and proves it (`not_balanced_GB`). So the file does **not** exhibit a *balanced* instance
at which `NoTriple` fails. That is a real remaining weakness in the non-vacuity evidence, correctly
disclosed rather than hidden.

## 1.13 The 68-declaration axiom audit — re-derived from scratch, not counted

The report prints a list of 68 names with per-declaration axiom sets. I did not take that list. I
wrote a `run_cmd` that walks the whole environment, and I ran it **twice**: once importing the
module (against the repair's olean), and once appended to a **fresh elaboration of the byte-identical
HEAD scratch file**, so the answer does not depend on any cached artefact.

```
$ lake env lean /tmp/opencode/tw8scratch/AxiomAudit.lean
AX_EXIT=0
TOTAL_DECLARATIONS=124
SORRYAX_DECLARATIONS=0
AXIOM_UNION=#[Classical.choice, Quot.sound, propext]

$ lake env lean /tmp/opencode/tw8scratch/HeadAudit.lean     # fresh elaboration of HEAD.lean
FRESH_EXIT=0
FRESH_TOTAL_CONSTANTS=124
FRESH_SORRYAX=0
FRESH_AXIOM_UNION=#[Classical.choice, Quot.sound, propext]
```

**124** is the count of *all* constants under the namespace, including compiler-generated
`._proof_*`, `.eq_1`, `._simp_*`, structure projections, `SeqGraph.rec`/`casesOn`/`ctorIdx` and the
`instDecidableEqSeqGraph` methods. The report's **68** is the count of *user-written* top-level
declarations. Both numbers are right; they count different things, and the report should have said
so. I reconciled them myself:

```
$ grep -nE '^(@\[[^]]*\]\s*)?(theorem|def|structure|abbrev|instance|inductive) ' <HEAD file>
  -> 70 hits, minus 2 prose lines that begin "theorem also needs" and "theorem with `NoTriple`
     removed is refuted"  =  68 user-written declarations
```

Diffing my 68 extracted names against the 68 in the report: **the two sets are identical except
that the report's markdown code fence lost the prime on `length_drop_le'`** (printed as
`length_drop_le`). That is a transcription slip in the prose of the report, not a missing
declaration; `length_drop_le'` is in the file at line 37 and in my audit. One of my first passes
also appeared to show a missing `mem_contractNodes_merge` — that was **my** grep missing the
`@[simp]` attribute prefix on line 176, not a gap in the report.

**SORRYAX_DECLARATIONS = 0 on both runs, and the axiom union is exactly `{propext, Classical.choice,
Quot.sound}`.** [MINE]. Corroborated at library scale by §1.8: the whole `AssemblyP1.lean` axiom
dump, 382 lines, contains no `sorryAx` and no `error`.

**One thing the audit does not cover, and it is an integration action item.** `AssemblyP1.lean`
audits 34 of the 68. The 13 declarations the repair added — `MergeWith`,
`mergeWith_eq_merge`, `merge_narrowing_witness`, `merge_na_nb`, `contractEdges_GA_na_nb`,
`no_w_edge_after_contract`, `source_replacement_edges_absent`, `GA_nodes_three`, `wellFormed_GB`,
`edgeSurj_GB`, `inMult_GB_a`, `not_balanced_GB` — are **not** in `AssemblyP1.lean`. I checked the
aggregator's `#print axioms` list (lines 519–552) directly. The report's F7 scopes this correctly in
prose; the *file* does not. Adding those 13 lines is a one-file, no-Lean-window change for whoever
owns `AssemblyP1.lean`, and it is the only way the aggregator itself becomes the durable audit.

## 1.14 A defect in `769a893` that BOTH prior reports found and NEITHER fixed

This is the most important thing in Part 1 that is not in either report, and I am recording it as a
finding rather than as a confirmation.

The claim sweep (94d8) audited the tw8 file at `cd430b4` and reported **T8-2** as *"OVERCLAIMED,
high"*. I re-read the committed text at `769a893` and **T8-2 is still there, unfixed**:

`AssemblyP1/Issue94TW8Contraction.lean` lines 482–487, module docstring, "What this module proves":

```
* `card_contractNodes_lt`: the **induction measure**.  Every reduction strictly
  decreases the number of nodes, so "repeated until no candidate edges remain"
  is well founded.  Two side conditions (`u ≠ v` and freshness of the merged
  node; the second is *not* a source hypothesis --- there `w` is new by fiat)
  are stated explicitly, not hidden.
```

The theorem's own docstring was improved by the repair (lines 213–219 now say "This is the
well-foundedness half of the fixpoint clause … Both side conditions … are explicit binders"), but the
**module-level bullet still claims the iteration is well founded**. It is not established. The
hypothesis `hw : Merge u v ∉ G.nodes` is not implied by `Contractible` (which is only
`(u,v) ∈ G.edges ∧ outDeg G u = 1 ∧ inDeg G v = 1`), so in a genuine condensation the merged node can
already be a node, the node count need not strictly drop, and nothing in the file shows the side
conditions persist along a *sequence* of contractions. The file's not-established item 3 disclaims
**order-independence**; it says nothing about **measure persistence**, which is a separate gap.

**And a second one, of the tw6 `≥ K` class, in the same file.** The claim sweep's **T8-3** flagged
tw8 line 374 (now 522) as *"a live instance of the same defect"* that *"the correction front cannot
reach because it is in a different file"*. I checked: the word "unrestricted" occurs **once** in the
HEAD file, at line 522, and the sentence is still there:

> "…and the unrestricted word-level form is FALSE (tw6's kernel-checked counterexample at
> `S = 012012012`, `G = 9`, `K = 3`)."

That is the `≥ K` claim that 94ed is correcting in tw6 and that 94d8 proved is **not refuted** by
that instance, because the instance checks one triple of starts at lengths `3, 4, 8` only. The
repair fixed F4's *framing* elsewhere in the same table row but left this sentence. So the `≥ K`
overclaim now survives in at least **three** places in the tree after the repair: `Issue94TW6Lemma1`
on `0733b76` lines 68 and 720, and `Issue94TW8Contraction` at `769a893` line 522.

Both are comment-only edits in a file `769a893` already owns, so whoever picks up the next tw8
pass can take them without a merge. I cannot make them: I am read-only on Lean source. They belong
in the ordered plan in Part 2.

---

# PART 2 — THE ORDERED INTEGRATION PLAN

## 2.0 Which parts of this Part are mine and which are relayed

**[MINE]** — every sha, every `merge-base`, every ancestry verdict, every `git merge-tree` result,
the branch inventory, and every conflict characterisation in §2.2–§2.7. I ran these.
**[RELAYED]** — 94ef's narrative reasoning, its §7.2 content, and its reading of the CI workflow;
94d8's per-file verdicts, of which I independently re-checked the eight I name and mark as such.
Where I disagree with a report I say **[REFUTED]** and give my own command output.

## 2.1 The branch inventory — derived from `git ls-remote`, not from prose

```
$ git ls-remote --heads origin        -> 266 refs
$ grep -E "issue-89|tw[0-9]|94-|claim-sweep|merge-order|dochonesty|antonina" <that>
```

| ref | head sha | what it contains | on the integration line? |
|---|---|---|---|
| `main` | `aa05fc7` | integration of #88/#92 | ancestor of `issue-89-final` |
| `antonina/issue-89-final` | `7d50132` | **the integration target**; 75 commits ahead of `main`, 0 behind | — |
| `94-tw1-best` | `8d9f7eb` | tw1 refutation of the `t_w = 1` step | **already inside** the chain (merged at `b8bcbb5`) |
| `94-tw2-edgetype` | `9f30a5e` | `Issue94TW1EdgeType.lean`, the edge-type obligation | ancestor of `769a893` |
| `94-tw3-residual` | `e8371b0` | reconciliation, no residual | ancestor of `769a893` |
| `94-tw4-eulerian` | `6012bff` | `Issue94TW4Coalesce.lean`; closes `L > 1` | ancestor of `769a893` |
| `94-tw5-lambda` | `e3fe5a5` | `Issue94TW5Single.lean`; the `single` clause is a tautology | ancestor of `769a893` |
| `94-tw6-lemma1` | `1ee7db8` | `Issue94TW6Lemma1.lean`; BBT Lemma 1's degree fact | ancestor of `769a893` |
| `94-tw7-altf` | `b7b092c` | `Issue94TW7AltF.lean`; refutes `Ukkonen + label-preserving => AltF = id` | **sibling**, merge-base `1ee7db8` |
| `94-tw8-contraction` | `cd430b4` | the tw8 module, pre-repair | ancestor of `769a893` |
| `fix/94-tw8-typecheck` | `769a893` | **the tw8 repair** — F2/F3 fidelity, F4–F7, gap witnesses | — |
| `fix/94-tw6-dochonesty` | `0733b76` | tw6 docstring overclaim correction, comment-only | **sibling**, merge-base `1ee7db8` |
| `94-doc-corrections` | `4204aac` | BBT bibliographic record + 7 doc files | **branches at `6012bff` (tw4)** |
| `review/94-tw6-lemma1` | `02d466f` | `BOARD94-TW6-REVIEW.md` only, +521 | review artefact |
| `review/94-tw8-contraction` | `0984dac` | `docs/board94-tw8-review.md` only, +510 | review artefact |
| `board94-vertexcycle` | `5809ef8` | `BBTVertexCycleReduction.lean` + a verifier script | **NOT in either report.** merge-base `50f02ec` |
| `agent/issue94-crossing-chords` | `6d80a74` | `Issue94IterSlide.lean` + `Issue89GapMap.lean` | **NOT in either report.** merge-base `99670a7` |
| `analysis/94-issue89-merge-order` | — | **DOES NOT EXIST on the remote** | 94ef took no commit |
| `review/94-claim-sweep` | — | **DOES NOT EXIST on the remote** | 94d8 took no commit |

**Two branches named in the brief's world are absent from the remote**, confirmed with
`git ls-remote --exit-code --heads origin <b>` returning non-zero for both. 94ef's and 94d8's reports
exist only as files in `/workspace`. **Their work is not in git and will not survive a worktree
collection.** The orchestrator should decide whether to have them committed somewhere before their
worktrees are reclaimed. This is a durability risk nobody has recorded.

**Two unintegrated branches that NEITHER report mentions.** `grep -c "board94-vertexcycle\|crossing-chords"`
returns **0** in `BOARD94-MERGEORDER.md` and **0** in `BOARD94-CLAIMSWEEP.md`. Both are real #89/#94
work that is *not* on `issue-89-final` and that *will* conflict:

```
$ git rev-list --count 769a893..origin/board94-vertexcycle        -> 2
  5809ef8 #89: wire BBTVertexCycleReduction into the build; clear the BBTLadder linter warnings
  af102be #89: board 94 second front: kernel-checked reductions for LadderVertexCycle
$ git rev-list --count 769a893..origin/agent/issue94-crossing-chords -> 2
  6d80a74 #94: prove the corrected iterated slide statement on the InterK layer
  eceed45 #94: gap map for the BBTCrossingChordsCoalesce §5 reduction; refute both §5 Props as stated

$ git merge-tree --write-tree 769a893 origin/board94-vertexcycle          -> exit 1
  CONFLICT: AssemblyP1.lean  (and AssemblyP1/BBTLadder.lean)
$ git merge-tree --write-tree 769a893 origin/agent/issue94-crossing-chords -> exit 1
  CONFLICT: AssemblyP1.lean  (and AssemblyP1/Issue89GapMap.lean)
```

`BBTVertexCycleReduction.lean` and `scripts/verify_ladder_vertexcycle_89.mjs` are **absent** from
`769a893`, and `BBTLadder.lean` / `Issue89GapMap.lean` have diverged (blobs `eced3e4`/`b0e23e7` on
`769a893` vs `d7f3520`/`8b43dfd` on the branches). **This is the single largest gap in the
integration plan as it stands, and both prior reports are silent on it.**

## 2.2 The one fact that makes the whole plan short

**[MINE]**

```
$ git merge-base cd430b4 origin/antonina/issue-89-final
7d50132  docs(#94): stop five files calling CrossingPairsCoalesce uninhabited
$ git merge-base --is-ancestor 7d50132 769a893 ; echo $?
0
$ git rev-list --count 7d50132..769a893
13
```

**The merge-base of the tw8 base and the integration head *is* the integration head.** The entire
tw1…tw8 chain is a 13-commit linear run hanging off `7d50132`, and `7d50132` is a descendant of
`main` (`git rev-list --count main..issue-89-final` = 75, `issue-89-final..main` = 0). So:

* **`cd430b4` IS on the integration line.** It is a descendant of the current head of
  `antonina/issue-89-final`, and therefore a **fast-forward** away from it, not a merge.
* **To answer the brief's question directly: the tw8 repair at `769a893` requires no integration
  work at all beyond pushing it.** `git merge --ff-only origin/fix/94-tw8-typecheck` from
  `7d50132` succeeds.
* `git merge-base --is-ancestor` says **no** tranche branch is an ancestor of `7d50132` or of `main`
  (I checked all 15). Nothing has been integrated yet, and nothing is on `main` except through
  `7d50132`.

**Consequence, and this is the deliverable's headline: the branch can be moved to a reviewable state
without any conflict resolution except the one decision in §2.6.**

## 2.3 94ef's recommended order, its evidence, and where I agree and disagree

94ef's order is: **Step 1** fast-forward the whole tw2→tw6 chain; **Step 2** merge
`94-doc-corrections` *at tw4, before tw5*; **Step 3** `94-tw7-altf`; **Step 4** `fix/94-tw6-dochonesty`
— **BLOCKED, escalate**; **Step 5** tw8 conditional on the repair; **Step 6** the review refs must
not land.

**Where I agree, and on my own evidence rather than its trials:**

* **The graph and the merge-base matrix.** I re-derived it independently (§2.1) and it matches: one
  linear run `7d50132 → tw2 → tw3 → tw4 → tw5 → tw6`, with `94-tw1-best` already absorbed at
  `b8bcbb5`, and `1ee7db8` (tw6) as the hub with three true siblings hanging off it — tw7, tw8, and
  `fix/94-tw6-dochonesty`.
* **That tw8 does not block the branch.** Established by me in §2.2.
* **That `94-doc-corrections` is the ordering trap.** It does branch at `6012bff`, and a naive reader
  would merge it last. It is right that the branch point is early.
* **That the tw7/tw8 `AssemblyP1.lean` conflict is mechanical.** I produced the conflict myself
  (§2.5) and it is exactly two hunks, both "insert lines at the same position": one `import` line
  and one block of `#print axioms` lines. No semantic disagreement.
* **That the review refs must not land.** I verified the technical premise: `02d466f` adds
  `BOARD94-TW6-REVIEW.md` (+521) and nothing else; `0984dac` adds `docs/board94-tw8-review.md` (+510)
  and nothing else. Both merge into `769a893` with **exit 0**. Whether they *should* land is a
  policy call for the orchestrator, not a technical one.

**Where I [REFUTED] 94ef — and this changes the plan.** 94ef's §1.6 makes `94-doc-corrections` a
**load-bearing hazard**: *"Any plan that merges `94-doc-corrections` after tw5/tw6 … silently
destroys two modules"*, and its Step 2 must therefore interleave a merge **between tw4 and tw5**.
The evidence for that claim is a two-dot diff: `git diff 1ee7db8 4204aac` shows 745 deletions in
`Issue94TW6Lemma1.lean` and 361 in `Issue94TW5Single.lean`. But those are files that **did not exist
at the branch point**. A two-dot diff between a descendant and an ancestor that lacks the files
renders them as deletions. A real merge is three-way, and it does not do that. I ran it:

```
$ git merge-tree --write-tree --name-only 769a893 4204aac
d5eed00ad73f4d6c7c43d7b8a7ca457f5354026d
exit=0                      # CLEAN, no conflict, no conflict list
```

and then checked the resulting tree for content loss:

```
$ git ls-tree -r --name-only d5eed00 -- AssemblyP1 | grep TW
  AssemblyP1/Issue94TW1.lean  Issue94TW1EdgeType.lean  Issue94TW4Coalesce.lean
  AssemblyP1/Issue94TW5Single.lean  Issue94TW6Lemma1.lean  Issue94TW8Contraction.lean
$ for f in TW5Single TW6Lemma1 TW8Contraction AssemblyP1.lean; do ... done
  AssemblyP1/Issue94TW5Single.lean      merged=47ae20e  769a893=47ae20e  4204aac=ABSENT
  AssemblyP1/Issue94TW6Lemma1.lean      merged=0affd3c  769a893=0affd3c  4204aac=ABSENT
  AssemblyP1/Issue94TW8Contraction.lean  merged=99d8a13  769a893=99d8a13  4204aac=ABSENT
  AssemblyP1.lean                       merged=0c4131a  769a893=0c4131a  4204aac=a74922d
$ git diff --name-only 769a893 d5eed00
  BBTCondense.lean  BBTEulerian.lean  Issue94TW1.lean  PopulationUniqueness.lean
  docs/arratia-shift-left-invariant-89.md  docs/bbt-chord-rematch-89.md
  docs/best-tw1-attribution-94.md  docs/exact-same-length-spectrum-fibre-count.md
```

**No module is lost. Every TW5/TW6/TW8 blob and `AssemblyP1.lean` is byte-identical to `769a893`,
and the only 8 files that differ are exactly the 8 `4204aac` intended to change.** Independently:
`git diff --name-only 6012bff 4204aac` and `git diff --name-only 6012bff 1ee7db8` have **empty
intersection** — the two sides touch disjoint file sets.

**So Step 2's interleaving is unnecessary, and I recommend dropping it.** `94-doc-corrections` can be
merged at any point after `6012bff`, including last, with no content loss. Merging it last is
*simpler* and it keeps `issue-89-final` a fast-forward for as long as possible. (I have not tested
`94-doc-corrections` against `b7b092c` or `4204aac`-after-`b7b092c`; the intersection argument above
covers tw7 as well, since tw7's only file overlap with the `769a893` side is `AssemblyP1.lean` and
`4204aac` does not touch `AssemblyP1.lean` at all. That is an argument, not a test, and it is marked
as such.)

**Where 94ef is right and I add to it.** 94ef escalated the tw7/dochonesty conflict as *"a
mathematical decision, not mine"*. That is correct and it is the one decision that gates the plan.
§2.6.

## 2.4 What the tw8 repair must be merged in relation to

**[MINE]**

* **In relation to `antonina/issue-89-final`: a fast-forward.** `7d50132` is an ancestor of
  `769a893`, so `git merge --ff-only origin/fix/94-tw8-typecheck` from `7d50132` succeeds with no
  conflict. No merge commit, no manual resolution.
* **Its branch base `cd430b4` IS on the integration line**, and I want to be precise about what that
  means: `cd430b4` is a *descendant* of `7d50132`, not an ancestor. The integration line runs
  `main → 7d50132 → e7d55f9 → … → 1ee7db8 → cd430b4 → 769a893`. `cd430b4` is on it.
* **In relation to tw7: it conflicts, mechanically.** §2.5.
* **In relation to `fix/94-tw6-dochonesty`: it does NOT conflict at all.**
  `git merge-tree --write-tree 769a893 0733b76` → **exit 0**, clean. 94ee's plan made tw6-dochonesty
  step 4 and tw8 step 5, implying an ordering between them; there is none required. They are
  siblings of `1ee7db8` touching disjoint files (`0733b76`: only
  `AssemblyP1/Issue94TW6Lemma1.lean`; `769a893`: only `AssemblyP1.lean` and
  `AssemblyP1/Issue94TW8Contraction.lean`). **The tw6 docstring correction and the tw8 repair can
  land in either order, or together.**
* **In relation to the two unreported branches: it conflicts with both**, in `AssemblyP1.lean`, and
  those merges are the real integration work. §2.5.

## 2.5 Every conflict, characterised by me

I produced all of these with `git merge-tree --write-tree` (git 2.52.0), which writes nothing, and
read the conflicted hunks with `git merge-file -p --diff3`.

| merge | result | character |
|---|---|---|
| `769a893` + `0733b76` (tw6 doc) | **exit 0, clean** | none |
| `769a893` + `4204aac` (94-doc-corrections) | **exit 0, clean** | none, and lossless (§2.3) |
| `769a893` + `b7b092c` (tw7) | **exit 1**, `AssemblyP1.lean` | **mechanical.** 2 hunks. Hunk 1: tw7 adds `import AssemblyP1.Issue94TW7AltF`, tw8 adds `import AssemblyP1.Issue94TW8Contraction` — **keep both**. Hunk 2: tw7 adds 17 `#print axioms …Issue94TW7AltF.*` lines, tw8 adds 38 `#print axioms …Issue94TW8Contraction.*` lines — **keep both**. |
| `769a893` + `02d466f` (review tw6) | **exit 0, clean** | adds one markdown file |
| `769a893` + `0984dac` (review tw8) | **exit 0, clean** | adds one markdown file |
| `b7b092c` + `0733b76` (tw7 vs tw6 doc) | **exit 1**, `Issue94TW6Lemma1.lean` | **substantive. 2 hunks. This is the escalation.** §2.6 |
| `769a893` + `board94-vertexcycle` | **exit 1**, `AssemblyP1.lean`, `BBTLadder.lean` | unreported; `AssemblyP1.lean` is again the additive-`#print axioms` pattern, but `BBTLadder.lean` needs reading |
| `769a893` + `agent/issue94-crossing-chords` | **exit 1**, `AssemblyP1.lean`, `Issue89GapMap.lean` | unreported; needs reading |

**On 94d8's "hazard 1", which I checked and which does not materialise as a conflict.** 94d8 warned
that `0733b76` *reverts* tw7's `mem_span_zero` docstring correction, because `0733b76` was built on
`1ee7db8` and does not contain it. That is true of the *branches*. It is not a merge problem: I ran
the merge and inspected the result — `mem_span_zero` at line 196 of the merged file carries **tw7's**
text ("`h3` is genuinely redundant here, since three pairwise distinct elements of `Fin G` already
force `3 ≤ G`"), with no conflict marker, because `0733b76` did not touch that region relative to the
merge base. **The hazard is a branch-ordering artefact, not content loss, provided tw7 is merged
first.** Merging `0733b76` first and tw7 second would be the losing order.

## 2.6 The one decision that gates everything — and it is not a formatting choice

**[MINE]** I produced the tw7/dochonesty conflict and read both sides. It is a **real mathematical
disagreement about what a kernel-checked file establishes**, and 94ef was right to escalate rather
than decide.

The contested text, base `1ee7db8`, ours `b7b092c` (tw7), theirs `0733b76` (94ed):

* **tw7:** "…**at those three starts, at each of the lengths `e = 3`, `4` and `8`, there is no maximal
  triple repeat** … so the `Ukkonen` triple clause and the `P2` triple clause **both hold on this
  instance**. The unrestricted degree fact is therefore false…"
* **94ed:** "…that triple of starts is not a maximal triple repeat of length `K = 3`, nor of lengths
  `4` or `8`. §7 proves `¬ IsTripleRepeat e 0 3 6` for exactly those three `e`: the lengths `5, 6, 7`
  and all other triples of starts are *not* checked, so the `≥ K` reading of the degree fact is **not
  refuted here either**. … this section does *not* establish … nor that it satisfies the `Ukkonen` /
  `P2` triple clauses, which range over all triples and all lengths `≥ K`; the `≥ K` form of the
  degree fact is **left open here**."

**These contradict each other on two points, and both are decided by the quantifiers, not by taste:**

1. tw7 says the `≥ K` form is refuted. 94ed says it is not. The `≥ K` form quantifies over **all**
   `e ≥ K`; the file checks `e = 3, 4, 8`. Three lengths do not refute an `∀ e ≥ K`. **94ed is
   right.**
2. tw7 says the `Ukkonen` and `P2` triple clauses "both hold on this instance". Those clauses
   quantify over **all** triples of starts; the file establishes the absence of a maximal triple
   repeat at **one** triple. 94ed's version replaces the claim with an explicit denial. **94ed is
   right.**

I checked that 94d8 independently reached the same verdict on the same two sites from a different
direction (its findings T1 and T4, both marked `[E]` in its own report, on the same file at the same
branch point), which is corroboration from an independent reader.

**So my input to the decision is that the disagreement is not symmetric: 94ed's text is the one
consistent with what the file proves.** But the *choice of which text lands* is the orchestrator's,
and I am not making it. What I am establishing is that it is not a coin-flip: 94ef's own reading
("dochonesty's version is the more defensible scope statement") is, on the quantifiers, the only
defensible one, and the tw7 side's two contested sentences are the ones that would have to be
deleted. Both sides already contain the shared "one triple, three lengths" scope limit, so the
resolution is mechanical once the sentence is chosen.

**There is a third option 94ef did not name, and I think it is the best one.** Land tw7, land the
dochonesty correction, and *additionally* apply 94d8's T2 and T5 — the two sites 94ed missed **in
the same file, on its own branch**. I verified those two by hand:

```
$ git show 0733b76:AssemblyP1/Issue94TW6Lemma1.lean | sed -n '68p'
* §7 — the kernel-checked refutation of the unrestricted form, at
$ git show 0733b76:AssemblyP1/Issue94TW6Lemma1.lean | sed -n '720p'
/-- **The refutation of the unrestricted form, kernel-checked.**  The three
$ git show 0733b76:AssemblyP1/Issue94TW6Lemma1.lean | grep -c unrestricted
2
```

**The word "unrestricted" survives twice on `fix/94-tw6-dochonesty`**, at the Contents entry and at
the `no_tripleRepeat_012012012` docstring — the two sites 94d8 flagged as T2 and T5 and confirmed as
still overclaimed. 94d8's report explicitly says it did not open `0733b76`'s content itself beyond
that; I did, and I confirm both. **So "the tw6 docstring fix is done" is not true.** Whoever owns
tw6 has three sites to fix, not one, and a fourth in a different file (§1.14). All four are
comment-only and need no Lean window.

## 2.7 The ordered plan

Every step names the ref or sha it acts on. Steps 1–3 need no conflict resolution. Step 4 is the
decision. Steps 5–6 are the unreported branches. I have written no ref, merged nothing, and pushed
nothing except `review/94-tw8-repair-verify2`.

**STEP 0 — durability, before anything else.** 94ef's and 94d8's reports exist only in `/workspace`;
their branches were never pushed and do not exist on the remote (§2.1). Have both committed
somewhere durable, or accept that `/workspace/BOARD94-MERGEORDER.md` and
`/workspace/BOARD94-CLAIMSWEEP.md` are the only copies. **Do this before any worktree is reclaimed.**
This step is mine and it is not in any report.

**STEP 1 — fast-forward the tranche chain. One move. No conflicts.**
Acts on `origin/antonina/issue-89-final` = `7d50132`; target `origin/fix/94-tw8-typecheck` = `769a893`.
```
git merge --ff-only origin/fix/94-tw8-typecheck     # 7d50132 -> 769a893, 13 commits
git push origin antonina/issue-89-final
```
Brings in tw1 (already merged), tw2, tw3, tw4, tw5, tw6, tw8 + the tw8 repair: 18 files,
+4754/−16 across `AssemblyP1/*.lean`, `AssemblyP1.lean`, `docs/*.md`, `scripts/verify_tw1_94.js`.
**Independently verified green at `769a893`: `lake build --wfail` exit 0, 8984 jobs, 0 warnings,
0 errors, 0 `sorryAx` (§1.8).** This is the state a human can review tonight, and it is the state
in which the endpoint is *not* discharged (`hPevzner` at `PopulationUniqueness.lean` 164, 217, 247
— I verified all three lines).

**STEP 2 — `94-doc-corrections`. Clean, and it can go last.**
Acts on the Step 1 head; merges `origin/94-doc-corrections` = `4204aac`. `merge-tree` exit 0,
lossless, 8 files. **Contrary to 94ef's Step 2, no interleaving between tw4 and tw5 is needed
(§2.3).** Note that it edits `PopulationUniqueness.lean` and `BBTEulerian.lean` docstrings, and it is
the only branch that touches the `hPevzner` status paragraph — so merge it *before* any front
rewrites that paragraph, or a second, genuinely semantic conflict appears.

**STEP 3 — `94-tw7-altf`. One mechanical conflict, two additive hunks.**
Acts on the Step 2 head; merges `origin/94-tw7-altf` = `b7b092c`. Resolution: in
`AssemblyP1.lean`, keep **both** `import AssemblyP1.Issue94TW7AltF` and
`import AssemblyP1.Issue94TW8Contraction`, and keep **both** blocks of `#print axioms` lines. Then
`lake build --wfail`. **Merge tw7 BEFORE `fix/94-tw6-dochonesty`** — the reverse order is the losing
one (§2.5). Content warning for the reviewer: this tranche **refutes** an obligation the board had
been treating as the last purely combinatorial one. That is a real negative result and it is
supposed to land. **[RELAYED]** the refutation itself (kernel-checked at `S = 0101, G = 4, L = 3`);
I did not verify tw7's proofs.

**STEP 4 — `fix/94-tw6-dochonesty`. The gated step. Requires a decision, not a merge.**
Acts on the Step 3 head; merges `origin/fix/94-tw6-dochonesty` = `0733b76`. Conflicts with tw7 in
`Issue94TW6Lemma1.lean`, 2 hunks, both about the scope of the `012012012` counterexample (§2.6).
Three sub-items, and note that **none of them is one merge**:

* **4a. The scope decision.** Orchestrator's call. My input: 94ed's text is the one consistent with
  the file's own quantifiers; tw7's two contested sentences are the ones that must go.
* **4b. Two sites 94ed missed, in its own file.** `0733b76` lines 68 and 720 still say
  "unrestricted" (§2.6, verified). Comment-only. Whoever owns tw6 fixes these; they are not fixed
  today.
* **4c. A fourth site, in a different file.** `Issue94TW8Contraction.lean:522` at `769a893` still
  says "the unrestricted word-level form is FALSE" (§1.14). `769a893` already owns that file, so this
  is a one-line comment edit on top of the repair, no merge.
* **If 4a is not decided:** land Steps 1–3, leave `fix/94-tw6-dochonesty` off the branch, and record
  in the branch that the tw6 docstring correction is *pending a scope decision*, not *done*. Do not
  silently drop it.

**STEP 5 — `board94-vertexcycle`. Unreported; needs an owner.**
Acts on the Step 4 head; merges `origin/board94-vertexcycle` = `5809ef8` (2 commits). Conflicts in
`AssemblyP1.lean` (the usual additive `#print axioms` pattern, `BBTVertexCycleReduction` is new) and
in `BBTLadder.lean`, whose blob has diverged (`eced3e4` on `769a893` vs `d7f3520` here). **I have
NOT read the `BBTLadder.lean` conflict** — it may be substantive, since that branch also "clears the
BBTLadder linter warnings", which means it may be removing `set_option` lines that later tranches
rely on. **This step needs a reader, not a merge command.**

**STEP 6 — `agent/issue94-crossing-chords`. Unreported; needs an owner.**
Acts on the Step 5 head; merges `origin/agent/issue94-crossing-chords` = `6d80a74` (2 commits).
Conflicts in `AssemblyP1.lean` and in `Issue89GapMap.lean` (blobs `b0e23e7` vs `8b43dfd`).
`Issue94IterSlide.lean` is already present at `769a893` with different content, so this is a real
divergence and not an addition. **I have NOT read either conflict.**

**STEP 7 — the review refs. My recommendation: do not merge them; copy the two reports into the
repo as ordinary documentation if the board wants them durable.**
`review/94-tw6-lemma1` = `02d466f` adds `BOARD94-TW6-REVIEW.md`; `review/94-tw8-contraction` =
`0984dac` adds `docs/board94-tw8-review.md`. Both merge into `769a893` with exit 0 and no
mathematical content. 94ef's recommendation not to land them is reasonable — they are artefacts of
a review process, and `docs/board94-tw8-review.md` in particular is the document whose F1 finding I
have just refuted, so landing it without a correction would put a known-wrong CRITICAL finding into
the repository's own docs. **If it is landed, it must land with F1 marked refuted.** That is my
recommendation and it is a judgement, not a technical finding.

**STEP 8 — the aggregator gap, no merge required.**
`AssemblyP1.lean` audits 34 of the tw8 module's 68 declarations (§1.13). The 13 the repair added are
unaudited **in the file**, though they are audited in the repair report. Add the 13 `#print axioms`
lines. Separately, 94d8's X-7 asks for a tw8 prose section in the aggregator carrying the file's six
"not established" items: `AssemblyP1.lean:518` is a **one-line** section header
(`/-! ## #94 front tw8: the contraction rule of `Defn. d:condensed` -/`) with nothing under it, so
**94d8's phrasing "no prose section about tw8 at all" is slightly off; the substance of the finding —
that nothing is carried forward — is right.** One file, comment-only, no Lean window.

**STEP 9 — the mechanical claim sweep, no Lean window, no merge.** In rough value order, all
independently re-checked by me where marked:
* **X-1, highest downstream-misleading value in the tree [MINE, confirmed at `769a893`].**
  `BBTEulerian.lean:47` still says "Both clauses are load-bearing" and `:270` still says `single` "is
  exactly the clause an arbitrary permutation of the starts can fail". Both are **false** since
  `Issue94TW5Single` proved the `single` clause a tautology. `BBTEulerian` and `BBTUniqueEulerian`
  are the two modules every other front imports. This is the fix the tw5 front owed and did not make.
* **T8-2 [MINE, still unfixed at `769a893`]** the `card_contractNodes_lt` well-foundedness bullet,
  §1.14. Comment-only, in a file `769a893` owns.
* **T10 linter denial [MINE, confirmed, with a correction to 94d8].** `Issue94TW1.lean:129-130` and
  `Issue94TW1EdgeType.lean:141-142` both end "no linter suppression" while the same file sets
  `set_option linter.unusedSectionVars false`; `Issue94TW4Coalesce.lean:113-114` does the same and
  adds `linter.unnecessarySimpa` at 139. **94d8's T10 also lists `Issue94TW5Single.lean`, and that
  one is wrong**: its boilerplate at 136–137 reads "… no `unsafe`, no theorem statement weakened" and
  never denies a linter suppression. Three files, not four. (The tw8 file is already correct — line
  591 discloses its three linter suppressions.)
* **C-1 phantom citations [MINE, confirmed].** I checked by `git grep` at `769a893`: **no declaration
  named `vertexCycleEq_of_traverses`, `card_branchStarts_eq_sum` or `interleavedStarts_iff` exists
  anywhere in `AssemblyP1/`.** They are cited as if they existed. `vertexCycleEq_of_traverses` is
  cited at `b7b092c:AssemblyP1/Issue94TW7AltF.lean:631,634` — inside the tw7 tranche, so this is a
  tw7 defect, not a pre-existing one.
* **T8-3 / the fourth `≥ K` site** is Step 4c above.

---

# WHAT I COULD NOT ESTABLISH

Named, not hedged. Nothing below is a claim I am making.

**Claims I checked and found wanting**

1. **94ef's "`94-doc-corrections` silently destroys two modules if merged after tw6" is wrong.**
   `git merge-tree --write-tree 769a893 4204aac` exits 0 and the merged tree's TW5/TW6/TW8 and
   `AssemblyP1.lean` blobs are byte-identical to `769a893`'s. The claim rests on a two-dot
   `git diff`. I did not find a reading under which it is true as a *merge* hazard.
2. **94d8's T10 over-counts.** It lists `Issue94TW5Single.lean` among the files that deny linter
   suppression; that file's boilerplate does not deny one. Three files, not four.
3. **94d8's X-7 phrasing is slightly off.** `AssemblyP1.lean` at `cd430b4` has a one-line tw8 section
   header at line 518, so "no prose section about tw8 at all" is not literally true. The finding's
   substance stands.
4. **The repair report's "68 declarations" and my "124 constants" are both right** and count
   different things; the report should have said which. Not an error, but a reader could have gone
   badly wrong in either direction. My first pass mis-grepped and briefly believed a declaration was
   missing; that was my error, caught and corrected here.
5. **The repair report's axiom list mis-transcribes `length_drop_le'` as `length_drop_le`.** A prose
   slip in a code fence; the declaration is present and audited.

**Claims I did NOT verify, and am relaying**

6. **Everything in `BOARD94-TW7-ALTF.md`.** I did not read it. The tw7 refutation at
   `S = 0101, G = 4, L = 3, σ = tau4`, `altF_eq_id_iff_rotation`, `VertexCycleEq`, `node_prefix` — all
   **[RELAYED]**. My tw7 merge analysis is topology; the truth of tw7's mathematics is not mine.
7. **Everything mathematical in `BOARD94-TW6-CONTRACTION.md`, `BOARD94-TW6-REVIEW.md`,
   `BOARD94-TW8-CONTRACTION.md`, `BOARD94-TW8-REVIEW.md`.** I read none of these files.
8. **The 8974/8984/8933/8937 job-count family.** I reproduced 8984 (full `--wfail`) and 8933
   (targeted) myself, and the report's explanation that these are graph sizes rather than work done
   is consistent with what I saw. Any *other* job number in any report I did not run.
9. **The arXiv e-print retrieval behind the `d:condensed` line numbers (130–141 / 138–140 / 167).**
   The repair fetched `arxiv.org/e-print/1301.0068v3`, reported 1 357 427 bytes, and corrected the
   module's line numbers. **I did not fetch it and did not check a single one of those line numbers.**
   This is the source-fidelity backbone of the whole tw8 module and it is entirely **[RELAYED]**.
10. **The `.tex` line numbers the module quotes, and therefore whether `Contract`/`MergeWith`/
    `Contractible` match the source's definitions at all.** Same reason. This is a *source-fidelity*
    question and my Part 1 verdict is about *elaboration*, not about faithfulness to the paper.
11. **94d8's sub-reader findings that I did not re-check**, marked `[E-sub]` in its report: T6, T7,
    T8, T9, T11, T12, T13, T14, T15, T16 (partial), T17, T18, T19, T20, T21, T22, T23, T24, T26, T27,
    D-3, D-4, D-5, D-6, D-8, D-9, D-11, D-12, and its §6 hazard-2 text. I re-checked T1/T2/T3/T4/T5
    (via the `unrestricted` count at `0733b76`), T10, T8-1, T8-3, X-1 (two sites), X-7, X-8, C-1/D-7,
    D-8, D-9. **T9's conflicting sweep totals (`5704` vs `5142`; `756` vs `562`) I did NOT re-verify
    and do not know which is right** — 94d8 says the tree does not determine it, and I did not
    determine it either.
12. **The `hPevzner`/`EulerianCycleObstruction` status as a mathematical matter.** I verified the
    three line numbers (164, 217, 247) and that the aggregator is more honest than `BBTEulerian`
    about it. I did not and cannot verify the underlying mathematics.
13. **What CI actually runs.** 94ef read `.github/workflows` and reports a 14-item mergeability
    checklist, of which it says items 11, 12 and 14 it cannot discharge. I did not read the
    workflows and I did not run CI. My green result is a local `lake build --wfail` at `769a893`,
    not a CI result.
14. **Whether the source's condensation actually needs the `Merge` specialisation.** T8-2 and 94d8's
    §9 item 2 both flag this as a modelling question that the tree does not settle. I did not settle
    it. I only established that the module now *discloses* the question.
15. **The `BBTLadder.lean` and `Issue89GapMap.lean` conflict contents** in Steps 5 and 6. I
    established that the conflicts exist and named the files; I did not read the hunks.
16. **Whether `94-doc-corrections` merges cleanly *after* tw7.** I proved it merges cleanly into
    `769a893`, and I gave a disjoint-file-set argument that it should also be clean after `b7b092c`.
    I did not run `merge-tree` on that specific pair. The argument is not the test.

**Limits of my own method, stated plainly**

17. **Three of my four `AxiomAudit` attempts failed** (exit 1: `ConstantInfo.axioms` and
    `TheoremVal.axioms` do not exist at this Lean version; one `String` `HAdd` failure). I report
    the failures rather than only the success. The successful runs are #13 and #14 above, both
    exit 0, and they agree.
18. **The 3.2–3.8 s elaboration times are suspiciously short** and I want the next reader to
    understand why they are nonetheless real: all imports resolve to pre-built oleans copied from
    another worktree, and §1.3 proved the same invocation reports errors from this file. A short run
    is not a skipped run. If a future front gets a long run instead, that is a *cold* `.lake`, not a
    different answer.
19. **`memory.events` `max` rose by 300 during my session** and I did not isolate which invocation
    caused it. `oom` and `oom_kill` did not move from 20 and 12. I did not get OOM-killed and did not
    cause an OOM kill, as far as these counters record.
20. **I did not read the 192 earlier board comments' content in full.** I read the issue's body, its
    definition of done, and comments 185–192 in full — which is where the tw8 review, the tw8
    repair, and the commissioning of this front are recorded. Comments 0–184 I read only as
    one-line summaries. Any integration-relevant fact stated only in comments 0–184 and not in a
    report or a commit message is a fact I may have missed.
21. **I did not compile `b7b092c` (tw7) or `0733b76` or `4204aac`.** Steps 2, 3, 4, 5 and 6 of my
    plan are validated by `merge-tree` and by reading, not by a green build. Step 1 is the only step
    I have a green build for, and it is green at `769a893` specifically.

**What I am NOT deciding**

22. **Whether the tw6/tw7 scope conflict is resolved** (§2.6). I established that the disagreement
    is real and that it is not symmetric. The choice is the orchestrator's.
23. **Whether `Contract` should be renamed.** §1.9. The name is still misleading; the one-line fix is
    in `AssemblyP1.lean`, which is not mine.
24. **Whether any board issue is closed.** I have not closed, commented on, created or reordered any
    board issue, and I have run no `board collect`. That is the orchestrator's action.
