# Board 94 green restore: `Issue94EulerianTheta` is QUARANTINED, not repaired

> **SUPERSEDED (board 94 recovery front, `/workspace/BOARD94-AXIOMAUDIT-*.md`).**
> The quarantine described below was lifted at commit `a91a01e`, which rewrote
> the module (the shiftless `hwin` is withdrawn, `window_rotEquiv` with the
> `G - k` shift replaces it, and `BadThetaObstruction` is retyped to
> `σ : Fin K ≃ Fin K`) and re-added the import at `AssemblyP1.lean:59`.  The
> 11 errors catalogued below are therefore no longer the state of the tree.
>
> **What lifting the quarantine did and did not do.**  It did *not* make the
> module a load-bearing input of the endpoint: no theorem outside
> `AssemblyP1/Issue94EulerianTheta.lean` uses any of its declarations, and
> `#print axioms` for each of its twelve public declarations reports only
> `[propext, Classical.choice, Quot.sound]` — no user axiom.  §4 of the module
> still shows `BadThetaObstruction ↔ thm:BBT`, i.e. the module establishes
> that its own "new structural theorem" is the target, not a step towards it.
> The endpoint `population_unique_ML_up_to_rotation` remains conditional on the
> hypothesis `hPevzner : EulerianCycleObstruction`, which has no inhabitant
> anywhere in the library.  See `docs/edge-type-obligation-94.md` §5 for the
> current line numbers (`AssemblyP1/PopulationUniqueness.lean` lines 178, 231,
> 261; the 155/208/238 cited in an earlier revision of that file were stale).

**Disposition: QUARANTINE.**  `AssemblyP1/Issue94EulerianTheta.lean` is left
byte-identical on disk and is no longer imported by `AssemblyP1.lean`, so
`lake build --wfail` is green (exit 0) on the head of `integration/94-green-audit`
with no mathematics deleted.

## The red, reproduced

At `4fe3606` (the module registered in the aggregator) on
`/workspace/assemblyp1-94-greenaudit`:

    /home/lubko/.elan/bin/lake build      # exit 1

gives **11** source errors (the commit message's "12" counts one error header
split across two lines):

```
:77:9   Unknown identifier `cyc_congr`
:78:6   No goals to be solved
:86:9   Unknown identifier `cyc_congr`
:87:6   No goals to be solved
:99:6   Tactic `rewrite` failed: did not find `vtx hG L S (rotAdd hG k (σ i))`
:140:4  Type mismatch: `congrArg S (Fin.ext ?)` vs an `E`/`S` equation
:150:31 `⟨0, ?⟩` has type `Fin (L - 1)` but `Fin L` is expected
:150:39 omega could not prove the goal
:190:46 Invalid projection `σ.<field>` on `σ : Fin K → Fin K`
:206:5  Function expected at `hB` but it has type `BadThetaObstruction L`
:219:8  `introN` with no additional binders in the goal
```

## Why this is not a mechanical repair

* `:77`/`:86` and `:99`/`:150:31` are the mechanical class: `cyc_congr` does exist
  (`AssemblyP1/BBTFibrePeriod.lean:138`), the module just does not import it, and
  the `Fin L` / `Fin (L-1)` index slips are index bookkeeping.
* `:140`–`:150` are **not**.  That block is the proof of the intermediate claim

  ```
  have hwin : ∀ i : Fin G, window (L := L) hG E i = window (L := L) hG S i
  ```

  inside `vertexCycleEq_of_RotEquiv_pullback`.  `hwin` is **false**, and it is
  false in the most innocent instance: `G = 4`, `L = 3`, `S = S4 = 0101`, and
  `E = S4` rotated by one position, which does satisfy `RotEquiv hG4 E S4` with
  `k = 1`.  `scratch94/Probe3.lean` is the kernel-checked refutation
  (`lake env lean scratch94/Probe3.lean`, exit 0, no `sorry`/`native_decide`):

  ```lean
  theorem rot : RotEquiv hG4 E4 S4          -- hrot holds
  theorem win0_ne : ¬ window (L := 3) hG4 E4 0 = window (L := 3) hG4 S4 0  -- by decide
  theorem hwin_false : ¬ (∀ i : Fin 4, window (L := 3) hG4 E4 i = window (L := 3) hG4 S4 i)
  ```

  The true relation is `window E i = window S ((i + 3) % G)`, i.e. the shift is
  `G - k`, not `k`, and the module's proof never establishes it.  Proving it is
  new mathematics (the dead front's `scratch94/Probe1.lean` agrees), so
  "repairing" `:140`–`:150` is re-authoring a proof, not fixing a proof.
* `:190`/`:206`/`:219` are a cascade, but the root is in the **statement**:
  `BadThetaObstruction` declares `(σ : Fin K → Fin K)` and then writes
  `pullback hK L S E σ.1`, while `BBTCondense.pullback` takes a bare
  `Function.Bijective` (`:508`–`:510`).  Making §4 well-typed changes the `Prop`,
  which the repair criterion forbids.

Since not every error is mechanical *and* a claimed statement would have to
change, the mandated disposition is QUARANTINE.  What §3 says may well be true —
only its proof is wrong — and nothing here claims otherwise.

## Green, on the head left behind

    /home/lubko/.elan/bin/lake build --wfail     # exit 0
    # Build completed successfully (8992 jobs).

Note on the environment: `AssemblyP1.Issue94OrbitSearch` (pre-existing on this
head, untouched here) was SIGKILLed with exit 137 under host contention more than
once; it built and the full `--wfail` build then succeeded.