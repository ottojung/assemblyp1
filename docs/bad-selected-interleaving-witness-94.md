# #94: the candidate replacement invariant is not refutable in range; the
# smallest *interesting* instance is `G = 6`, `L = 3`, and it is already the
# `001011` instance

Date: 2026-10-02. Branch `board/94-replacement`, on top of `48a3f15`.
Front: continuation front of issue #94, bounded elaboration 2315.

## 1. The question

`AssemblyP1/BBTReplacementInvariant.lean` ends with the candidate replacement
invariant left **open**, and states the shape of a refutation as a `Prop`:

```lean
def BadSelectedInterleavingWitness : Prop :=
  ∃ (G L : ℕ) (S : Fin G → Fin 2) (hG : 0 < G) (θ : Fin G → Fin G),
    P2 hG L S ∧ ¬ LongObstruction hG L S ∧
      Function.Bijective θ ∧ FibrePreserving (hG := hG) (L := L) S θ ∧
      OneCycle hG θ ∧ ¬ OrbitVertexEq (hG := hG) (L := L) S θ ∧
      SelectedInterleaved (hG := hG) (L := L) S θ
```

i.e. exactly: a `P2` genome at which a **bad** `θ` is a **selected**
interleaving.  A witness would refute
`bad θ ∧ SelectedInterleaved θ ⟹ LongObstruction`.  Front 9412 supplied the
*good*-`θ` version on `00101`; `48a3f15` refuted the `P2` hypothesis of the
*bad*-`θ` version on `001011`.  So the refutation direction has been tried twice
and failed twice, for reasons that were each local.

This note records the third attempt, and the first exhaustive one.

## 2. Kernel-checked: no witness at `G = 4`, `L = 3` — but vacuously so

`scratch/BadWitnessSearch.lean` closes, by `decide`, the negation of the witness
statement at `G = 4`, `L = 3`, over **all** `4^4 = 256` words and **all**
`4^4 = 256` successor maps:

```lean
theorem no_bad_witness_G4_L3 : ¬ ∃ (S : Fin 4 → Fin 2) (θ : Fin 4 → Fin 4), ... := by decide
```

Measured on this host: 50 s, peak `lean` RSS 11.6 GB, peak cgroup `anon` 11.5 GB,
`LEAN_NUM_THREADS=1`, no other `lean` process.

**Anti-vacuity, also kernel-checked (`scratch/AntiVacuity.lean`):**

| statement at `G = 4`, `L = 3` | verdict |
| --- | --- |
| `∃ S, P2 hG4 3 S` | **proved** by `decide` |
| `∃ S θ, SelectedInterleaved hG4 3 S θ` | **proved** by `decide` |
| `∃ S θ, Bijective θ ∧ FibrePreserving ∧ OneCycle ∧ ¬ OrbitVertexEq` | **refuted**: *no bad `θ` exists at all* |

So the `G = 4` refutation search is vacuous in the clause that matters: at
`G ≤ 4, L = 3` the vertex cycle of a one-cycle fibre-preserving successor map is
already unique.  The theorem is true, but for a stronger reason than the
invariant.

### The `G = 5` elaboration does not fit this host

The same statement at `G = 5` needs `4^5 · 5^5 = 3.2 · 10^6` pairs.  Growth is
geometric and the memory curve is monotone and unsaturated:

| `G` | pairs | wall clock | peak `lean` RSS | outcome |
| --- | --- | --- | --- | --- |
| 4 | `6.6e4` | 50 s | 11.6 GB | proved, `decide` |
| 5 | `3.2e6` | killed at 265 s | ≥ 22.4 GB, still climbing | **killed by the 21 GiB `anon` watchdog**, not by `timeout` |

Extrapolating, `G = 5` wants on the order of 40 GB and `G = 6` (`1.9e8` pairs)
far more.  This is a **host resource constraint, not a proof failure**: nothing
was proved or refuted at `G = 5`, and the instance is *not* the interesting one
anyway (see §3).  Re-`decide`ing this statement at `G ≥ 5` on a 30 GiB box is not
worth attempting; the interesting statement at `G = 6` is cheap, and is §3.

**Incidental engineering finding.** `P2` and `LongObstruction` have **no
`Decidable` instance in the library**, and instance search cannot produce one:
`Genome.len` / `Genome.sym` projections of a literal structure do not reduce at
instance-search transparency, and the nested six-fold `∀` of `P2`'s second
clause exceeds the search depth budget.  `scratch/DecInfra.lean` supplies the
missing decidability (per-atom `Decidable` by unfolding, aggregate clauses by
explicit `Nat.decidableForallFin` recursion).  If this decidability is wanted in
the library rather than in scratch, that is a separate, small PR.

## 3. Computational, exhaustive: no witness up to `G = 10`, and the smallest
interesting instance is exactly `001011`

`scratch/bad_witness_search_94.py` is a faithful transcription of the Lean
definitions (`P2`, `LongObstruction`, `FibrePreserving`, `OneCycle`,
`OrbitVertexEq`, `Selects`, `SelectedInterleaved`, `SelectedTriple`) at
`L = 3` (`K = 2`), enumerating every word and, for each, every bijective
fibre-preserving successor map `θ = f ∘ ρ` (i.e. every circuit).  `L = 3` is the
level at which `G = 6` already has a bad `θ`, so it is the first level where the
candidate invariant is non-vacuous.

| `G` | words | `P2` | bad one-cycle `θ` | bad ∧ selected-interleaved | bad ∧ selected-triple | **`BadSelectedInterleavingWitness`** | bad unexplained by (T) or (I) |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 4 | 4 | 0 | 0 | 0 | **0** | 0 |
| 3 | 8 | 8 | 0 | 0 | 0 | **0** | 0 |
| 4 | 16 | 16 | 0 | 0 | 0 | **0** | 0 |
| 5 | 32 | 22 | 0 | 0 | 0 | **0** | 0 |
| 6 | 64 | 28 | 12 | 12 | 0 | **0** | 0 |
| 7 | 128 | 16 | 28 | 28 | 0 | **0** | 0 |
| 8 | 256 | 24 | 656 | 624 | 640 | **0** | 0 |
| 9 | 512 | 8 | 5184 | 5040 | 5184 | **0** | 0 |
| 10 | 1024 | 4 | 46480 | 46120 | 46460 | **0** | 0 |

Three things follow.

1. **The refutation direction is dead in range.** No `BadSelectedInterleavingWitness`
   exists for any binary circular word with `G ≤ 10` at `L = 3`.  Together with
   `48a3f15`'s kernel-checked `¬ P2 hG6 3 S6` for `S = 001011`, the candidate
   replacement invariant now has three independent failed refutation attempts
   behind it (`00101` good-`θ`, `001011` not-`P2`, exhaustive `G ≤ 10`).
   The right next step is therefore the **proof** of
   `bad θ ∧ SelectedInterleaved θ ⟹ LongObstruction`, not a third witness hunt.
2. **The smallest interesting instance is `G = 6`, `L = 3`, and it is the
   already-analysed `001011`.** The 12 bad `θ` at `G = 6` are all selected
   interleavings, and every one of them sits on a genome with a long obstruction
   (kernel-checked at `48a3f15`).  So at the very first instance where the
   candidate invariant has teeth, the instance that supplies the teeth is
   disqualified from being `P2` by the *same* interleaved repeat that makes it
   interesting.  This is the mirror image of `docs/aaab-p2-converse-instance.md`:
   there the failure of `P2` still left the spectrum fibre a singleton; here it
   is the `P2` hypothesis itself that is lost.
3. **`SupportDichotomy` is re-verified in range** at `L = 3`, `G ≤ 10`:
   `bad_unexplained_by_T_or_I = 0` everywhere, independently of the kernel
   evidence already in `AssemblyP1.BBTSupportInvariant`.  At `G ≥ 8` both
   disjuncts are genuinely needed (at `G = 8`, 640 bad `θ` are explained by the
   three-way multiplicity clause and only 624 by the interleaved clause), which
   is the first quantitative sign that neither disjunct can be dropped.

## 4. What is *not* claimed

* The `G ≤ 10`, `L = 3` sweep is **computational evidence, not a proof**; its
  completeness is not established in Lean.  The only kernel-checked items here
  are the `G = 4` statements of §2.
* Only `L = 3` was swept.  Nothing here says anything about `L ≥ 4`.
* No definition was changed.  The Python file is a transcription, not a
  redefinition; where it and Lean could disagree, Lean is authoritative and the
  `G = 4` agreement is the only cross-check performed.

## 5. Files

* `scratch/BadWitnessSearch.lean` — `G = 4, L = 3`, closed, kernel-checked.
* `scratch/AntiVacuity.lean`, `scratch/AntiVacuity3.lean` — the three
  anti-vacuity statements of §2.
* `scratch/DecInfra.lean`, `scratch/BadWitnessGen.lean`,
  `scratch/BadWitnessG5.lean` — generic decidability infrastructure and the
  `G = 5` attempt that the watchdog killed.
* `scratch/watchdog.sh` — bounded runner (one `lean`, `timeout`, `anon` kill).
* `scratch/bad_witness_search_94.py` — the sweep of §3.