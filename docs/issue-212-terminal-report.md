# Issue #212 terminal report

_Status: TERMINAL — solved._
Front owner (board identity): `openclaw@marceline-dev`.
Worktree: `/workspace/assemblyp1-finite-212`, branch `agent/board-212-37b45b`.

**This file exists because the board comment could not be posted from this
host — see the "Reporting blocker" section. Its text is written to be copied
onto issue #212 verbatim.**

---

## 1. Progress comment that should open this front's board record

> **state: solved** — issue #212, owner `openclaw@marceline-dev`, branch
> `agent/board-212-37b45b`, ahead `origin/main` by 2 commits.
>
> **Verdict.** Finite ML maximality for `|D| = |S|` in the
> reverse-complement-collapsed MB09 bidirected spelled-flow model is **false**
> under the per-occurrence strengthening.  Exact counterexample, kernel-checked:
>
> ```text
> alphabet   {A, C, G, T}, rc A<->T, C<->G (no self-complementary base)
> truth      S = ATATACAC            (G = 8)
> competitor D = ATACACAC            (G = 8, SAME LENGTH)
> L = 3, o_min = 2, realized starts (1,3,4,5,6,7), n = 6 < G = 8, N = |S| = 8
> x      = { ACA/TGT:2, ATA/TAT:1, ATG/CAT:1, CAC/GTG:1, GTA/TAC:1 }
> d_S    = { ACA/TGT:2, ATA/TAT:3, ATG/CAT:1, CAC/GTG:1, GTA/TAC:1 }
> d_D    = { ACA/TGT:3, ATA/TAT:1, ATG/CAT:1, CAC/GTG:2, GTA/TAC:1 }
> ```
>
> **Both candidates are per-occurrence feasible** (`d_w >= x_w` for every
> class; the tight coordinate is `ACA/TGT`, where `x = d_S = 2`), so this is a
> refutation of the *strengthened* rule, not a restatement of the source one.
> `D` strictly beats `S` under both objectives:
>
> ```text
> Variant E  exact candidate-intrinsic multinomial    L(D)/L(S) = 3/2
> Variant A  literal MB09 §6.1 binomials, N = 8      L(D)/L(S) = 9/5
> ```
>
> **Labelled as required:** the per-occurrence condition `d_w >= x_w` is a
> **project-level strengthening** of the MB09 §6.2 rule, **not a source fact**.
> §6.2 gives each read *vertex* a lower bound of `1` and §4.1 says each
> `k`-molecule is represented only once; the source rule is support equality.
>
> **Evidence.**
>
> - `AssemblyP1.PerOccurrenceSameLengthCounterexample` kernel-checks the full
>   statement: `SourceFaithfulIs.InformationFeasible` at full strength (shared,
>   authoritative predicate, discharged by `decide`), `|D| = |S| = 8`,
>   `PerOccurrenceFeasible dS obs`, `PerOccurrenceFeasible dD obs`,
>   `SpelledFeasible62` for **both** molecules (explicit 16-edge bidirected
>   overlap graph on the five observed molecules, transitive reduction vacuous
>   under both readings, vertex LB `1`, edge LB `0`, §3.4 balance `0`, no
>   supersource/supersink, throughput = own spectrum, every step a real edge
>   surviving the reduction, every visited vertex observed, both walks genuine
>   bidirected circuits), `lik obs dS < lik obs dD`, and
>   `exactLik dD obs / exactLik dS obs = 3 / 2`.  Main theorems depend only on
>   `propext`, `Classical.choice`, `Quot.sound`.
> - `peroccurrence_samelength_maximality_refuted : ¬ P` where `P` is the
>   conjunction-of-hypotheses implication stated as a `Prop`.
> - True feasible flow: truth walk
>   `ATA/TAT - TAT/ATA - ATA/TAT - TAC/GTA - ACA/TGT - CAC/GTG - ACA/TGT -
>   CAT/ATG`, throughput `d_S`; competitor walk
>   `ATA/TAT - TAC/GTA - ACA/TGT - CAC/GTG - ACA/TGT - CAC/GTG - ACA/TGT -
>   CAT/ATG`, throughput `d_D`, with flow `2` on the `ACA→CAC` and `CAC→ACA`
>   edges.  Both hand-written circuits are proved equal to the flows the walks
>   themselves carry.
> - `I_s`: coverage holds; four maximal triple repeats, all of length `1`
>   (`A@{0,2,4}`, `A@{0,2,6}`, `A@{0,4,6}`, `A@{2,4,6}`), every copy bridged;
>   **two** interleaved repeat pairs, both bridged — clause 3 is non-vacuous
>   here, which not every same-length witness achieves.
> - `scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py` is a
>   from-scratch independent check (no code shared with the existing scripts)
>   that mirrors the repository's own definitions, including the strict
>   `SourceFaithfulIs.BridgesCopy`.  It re-verifies all of the above and runs
>   **negative controls**: `I_s` fails for `{1,3,4,5,6}` (coverage) and for
>   `{0,1,2,4,5}` (coverage holds, bridging clause fails); `TAC→ACA` is an edge
>   and `GTA→ACA` is not.
> - Independent comparison with
>   `docs/section62-same-length-bidirected-counterexample.md`
>   (`docs/peroccurrence-samelength-dna-counterexample-212.md` §3): the merged
>   witness's truth has `d_S(AAA) = 1 < x_AAA = 2`, so it is *not* a candidate
>   under the strengthening and the strengthened case was genuinely open.  The
>   two refutations are logically independent.
> - Bounded census (own script, `--search`): zero both-objective
>   per-occurrence beats at `G <= 7`, `L = 3`, `sigma = 4`; zero for `sigma = 2`
>   at every `G <= 10`; zero for `sigma = 3` at `G <= 7`.  At `sigma = 4`,
>   `G = 8`: exactly 4 orbit-representative beats, two combinatorial patterns up
>   to `C <-> G`.  At `sigma = 3`, `G = 8`: exactly 1, the `{A,C,G}` embedding of
>   this witness.  At `sigma = 4`, `G = 9`: 80 beats, so `G = 8` is the minimum
>   size, not the only one.  Bounded evidence; not a proof of absence.
>
> **What I fixed in the inherited state.** The untracked Lean module that came
> with this front did **not** compile (five defects: an unprovable `code3_lt`, a
> `decide` over free variables, `decide` without unfolding, a recursion-limit
> blow-up, and a docstring that claimed §6.2 graph/flow certificates the file did
> not contain).  It is rewritten and now proves what the docstring claims.
>
> **Not settled by this front:** which MB09 object the 2016 sentence intends;
> the single-strand reading; the variable-length case; tie/equivalence
> semantics.

---

## 2. Commits

| commit | content |
|---|---|
| `6aeb95e` (inherited) | `scripts/verify_peroccurrence_dna_samelength_212.py`: first independent exact verification of the witness |
| next | `AssemblyP1/PerOccurrenceSameLengthCounterexample.lean`: rewritten, kernel-checks the full statement (replaces the broken untracked file) |
| next | `scripts/verify_peroccurrence_dna_samelength_212_sourcefaithful.py`: second from-scratch verification mirroring the repository's own definitions, plus negative controls |
| next | `docs/peroccurrence-samelength-dna-counterexample-212.md`: the front note |
| next | pointer updates in `docs/bridging-se62-flow-ml-counterexample.md`, `docs/section62-same-length-bidirected-counterexample.md`, `docs/source-notes/same-length-witnesses-candidate-set-inclusion.md` |

## 3. Reporting blocker (precise)

I could not post the board comment on issue #212 from this host.  Measured
facts:

* `gh` is not installed and is not on `PATH`.
* No GitHub token exists in the environment, in `~/.git-credentials`, in
  `~/.netrc`, or via `git credential fill`; `env | grep -i token` finds only
  `LUBKO_SUPERVISOR_STATE_TOKEN`, which is an opencode supervisor token.
* The repository is private: an unauthenticated `GET
  https://api.github.com/repos/ottojung/assemblyp1/issues/212` returns
  `404 Not Found`, not `401`, so the REST API cannot be used even to read.
* `git` over SSH authenticates as `ottojung` (used to push this branch), but
  GitHub's REST API has no SSH transport.

Please post §1 verbatim on issue #212 as `openclaw@marceline-dev`.

## 4. Branch build state

`lake build AssemblyP1.PerOccurrenceSameLengthCounterexample` succeeds and the
full `lake build` is red on this branch only for reasons inherited from
`origin/main`, which my diff does not touch:

* `AssemblyP1/BBTTripleBridge.lean` fails to elaborate (first error at line 81);
  `git diff --stat origin/main -- AssemblyP1/BBTTripleBridge.lean` is empty.
* the root `AssemblyP1.lean` fails because
  `import AssemblyP1.Issue94KShortGeneral` collides with
  `AssemblyP1.Issue94KShort` in the environment; also untouched by this front.

`python3 scripts/check-research-docs.py` passes.
