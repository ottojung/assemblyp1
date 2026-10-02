# `BBTReplacementInvariant.lean` exceeds the host memory budget — HOST CONSTRAINT

Date: 2026-10-02. Branch state: untracked module + one-line addition to
`AssemblyP1.lean`, on top of `b12eae6`.

## Summary

`AssemblyP1/BBTReplacementInvariant.lean` cannot be elaborated on this host.
A single `lake env lean` invocation of the whole module was measured twice
independently (pid 20071980 at 20:08:07Z, pid 634490 at 20:08:41Z) reaching
**20.9 GB RSS before OOM-kill**, against a 30 GiB cgroup hard limit that had
three other fronts live. Both processes were SIGTERMed deliberately rather
than left for the cgroup OOM killer.

**This is a host resource constraint, not a proof failure.** Nothing in the
module was proved or refuted by these runs. No mathematical claim in the
module is in question; only whether its `decide` scripts can be checked on a
30 GiB box shared with three other agent fronts.

`oom_kill` remained 31412 across both attempts: no process was actually
reaped. Both runs died to an explicit SIGTERM.

## Why this module cannot be checked here, precisely

The module has **never been built**. There is no
`.lake/build/lib/lean/AssemblyP1/BBTReplacementInvariant.olean`, though 40+
sibling modules have their oleans from 18:34–18:38.

This makes the usual mitigation — "elaborate only the lemma in a scratch file
that imports the already-built oleans" — **impossible for this module**. There
is no olean to import, and producing one requires elaborating the whole module,
which is precisely the operation that overruns. The runaway cannot be
side-stepped at the lemma level; it is a property of the module as a unit.

## Root-cause hypothesis (from source reading; NOT yet measured)

Strong but unverified. The module is 238 lines of tiny `Fin 6` `decide`s, so
the size is not in the mathematics — it is in one specific script.

Every `decide` in the module quantifies over a *fixed* successor map or over
the concrete data, **except one**:

- `BBTReplacementInvariant.lean:133-135`

  ```lean
  theorem no_triple_mult_001011 :
      ∀ θ : Fin 6 → Fin 6, ¬ SelectedTriple (hG := hG6) (L := 3) S6 θ := by
    decide
  ```

`decide` discharges `∀ θ : Fin 6 → Fin 6` by way of
`Fintype.decidableForallFintype`, which enumerates **6⁶ = 46 656** successor
maps. For each one it must kernel-evaluate

```lean
SelectedTriple θ = ∃ v : Fin (L-1) → α, 3 ≤ (fibre hG L S v).card ∧ Selects θ v
```

(`BBTSupportInvariant.lean:163-164`)

and `(fibre _ _ _).card` carries a `Finset.card` proof term that is itself
large. Multiplying a large per-`θ` certificate by 46 656 instances is
consistent with a ~20 GiB kernel term. The other `decide` sites
(`hG6:106`, `bad_001011:123-128`, `p2_hG6_S6_L3:141-143`, and the two concrete
`SelectedInterleaved`/`SelectedTriple` goals at `:175` and `:201`) are all
over a *fixed* `T6` or a fixed vertex, so their search spaces are 6⁴ or
smaller and should be cheap.

**Why the whole-module split is still wrong regardless.** Even if the
single script were cheap, it is a kernel-evaluation cost that grows with the
shared `decide` infrastructure, and there is no way to run it in isolation
given the missing olean.

## Mitigation, ready but not yet verified

The `no_triple_mult_001011` script does not need the 46 656-fold
enumeration, because its statement is **θ-independent in its first
conjunct**:

```lean
SelectedTriple θ = (∃ v : Fin (L-1) → α, 3 ≤ (fibre hG L S v).card) ∧ (θ-dependent part)
```

More precisely, `(∃ v, 3 ≤ (fibre hG L S v).card)` mentions no `θ`. So the
refutation is: establish the `θ`-free existential is **false** — at
`S = 001011`, `L = 3` the fibres are `00 ↦ {0}`, `01 ↦ {1,3}`,
`10 ↦ {2,5}`, `11 ↦ {4}`, so no vertex has cardinality ≥ 3 — and then
eliminate on the existential. That is four small per-vertex `decide`s (or a
fully hand proof), with **no** 46 656-fold enumeration and **no** large
per-`θ` certificate.

Note this is a change of *proof method*, not of any definition or statement.
`SelectedTriple`, `FibrePreserving`, `SupportDichotomy` and every proposition
are untouched; the theorem `no_triple_mult_001011` would keep exactly its
current statement. That distinction matters under `AGENTS.md`: no definition is
being altered to make a theorem provable.

## Why the mitigation has not been applied yet

Deliberate resource gate, per operator instruction. Immediately before this
note was written:

```
grep -E "^anon " /sys/fs/cgroup/memory.stat   ->  anon 5122494464   (4.77 GiB)
cat /sys/fs/cgroup/memory.current              ->  17989312512      (16.76 GiB)
cat /sys/fs/cgroup/memory.max                  ->  32212254720      (30.00 GiB)
```

Anon was 4.38 GiB on the first reading of the session and had risen to
4.77 GiB by the second. The 4 GiB pre-launch threshold is exceeded, so **no**
Lean or Lake invocation was issued from this front, and consequently there is
no command line or peak-RSS figure to report from me — I have run nothing.

The anon consumers are not mine: `ps` shows the largest resident processes as
an `openclaw-gateway` at ~2.0 GiB plus six `opencode` agents at 0.52–0.57 GiB
each, and no `lean` or `lake` process at all.

## Collateral finding: the library currently does not build

`BBTReplacementInvariant.lean` is untracked and is wired into the library root
at `AssemblyP1.lean:4`:

```diff
 import AssemblyP1.BBTSupportInvariant
+import AssemblyP1.BBTReplacementInvariant
```

No other module imports it, and no built olean or trace references it. So the
root target transitively depends on the one module that cannot be elaborated
on this host. Until the mitigation lands and the module builds, `main` as
committed at `b12eae6` still builds (the import line is uncommitted), but the
working tree does not.

Recommended, in order:

1. Rewrite the `:133-135` script as the θ-independent fibre-count argument.
2. Elaborate **only** that lemma in a scratch file importing
   `AssemblyP1.BBTSupportInvariant` (which *does* have an olean), under a
   4 GiB watch; never re-elaborate the whole module unbounded.
3. Only then run `lake build -j4` with the core fence at 16-23.

## Standing constraints observed on this front

- No whole-module `lake env lean` and no unbounded `lake build`, ever again.
- Per-lemma scratch files against pre-built oleans, with an explicit RSS watch.
- Pre-launch `anon` check; do not start above 4 GiB.
- Kill and report any single elaboration that exceeds 4 GiB myself, without
  waiting.
- `lake build -j4`, core fence 16-23.
