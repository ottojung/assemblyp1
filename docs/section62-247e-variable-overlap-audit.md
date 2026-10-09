# Front 247e — `AAABBABB → AAAABABB` variable-overlap walk at `oMin = 1`

_Status: independent adversarial audit, 2026-10-09. Separate worktree
`assemblyp1-247e-varoverlap` (branch `agent/board-247e-varoverlap-20261009`),
independent Python program `scripts/verify_247e_varoverlap.py`, and additive
kernel-checked module `AssemblyP1/Section62VariableOverlap247e.lean`
(`lake build` green; `leanchecker` replay exit `0`; only `propext`,
`Classical.choice`, `Quot.sound`). No existing definition, theorem or witness
was modified._

Reproduce:

```sh
python3 scripts/verify_247e_varoverlap.py
lake build AssemblyP1.Section62VariableOverlap247e
```

## 0. Verdict

1. **The proposed variable-overlap walk is refuted as a source-faithful §6.2
   flow.** In the bidirected **molecule** graph of MB09 §3.1/§4.1 the walk's
   molecule throughput is `{AAA:2, AAB:2, ABA:1, BAA:2}` while `D`'s molecule
   spectrum is `{AAA:2, AAB:2, ABA:2, BAA:2}`. The `ABA` counts differ
   (`1 ≠ 2`), so the walk violates MB09 Observation 7. Equivalently its
   overlap-`1` edge `AAB → BAB` is removed by the source's transitive edge
   reduction. [kernel-checked]

2. **`D` is nevertheless a genuine §6.2 candidate**, via the ordinary
   full-overlap (`L − 1 = 2`) window walk
   `AAA → AAA → AAB → ABA → BAB → ABB → BBA → BAA`, whose molecule throughput
   equals `D`'s molecule spectrum exactly. [kernel-checked]

3. **The "unobserved `ABA`" premise is a strand-orientation artifact.** In the
   molecule reading used by the source, `ABA = rc(BAB)` and `BAB` was sampled,
   so `ABA` *is* an observed read molecule and molecule support equality holds.
   [kernel-checked]

## 1. The two readings

| object | oriented (strand) reading | molecule reading (MB09 §3.1/§4.1) |
|---|---|---|
| reads | the 6 sampled windows `{AAA,AAB,ABB,BBA,BAB,BAA}` | the 4 classes `{AAA}, {AAB,ABB}, {BBA,BAA}, {BAB,ABA}` |
| `ABA` | genuinely unobserved | observed: it is `rc(BAB)` |
| `D` support | `⊋` observed (contains `ABA`) | `=` observed |
| `D` §6.2-feasible? | not via the proposed walk (below) | yes, via the full-overlap walk |

MB09 §6.2 says "the vertices of this graph are the reads, which are DNA
molecules", and §3.1 defines a DNA molecule as an unordered reverse-complement
strand pair; §4.1 represents each `k`-molecule only once. The molecule reading
is therefore the source reading. The board's witness is an *oriented* object,
which is why it reports `ABA` as unobserved.

## 2. The literal graph, reduction and walk

- Alphabet `{A,B}`, involution `A ↔ B`; `L = 3`; `oMin = 1`.
- Observed molecule representatives: `AAA, AAB, BAA, ABA`; `strandsOf` also
  enumerates `BBB, ABB, BBA, BAB`.
- `overlapEdges` at `oMin = 1` has **48** edges; at `oMin = 2` it has **16**.
- The proposed walk `AAA→AAA→AAB→BAB→ABB→BBA→BAA→AAA`, overlaps
  `[2,2,1,2,2,2,2]`, spells `D` (length `Σ(L−overlap) = 8`, wrap consistent)
  and is a valid bidirected strand walk (`OppositeAtInterior` holds at every
  interior vertex). Its reads are exactly `D`'s windows at offsets
  `[0,1,2,4,5,6,7]`. [kernel-checked]

### 2.1 Transitive reduction

- The literal `isReducibleB` ("two **shorter** overlaps", equation
  `len₁+len₂−readLen = e.len` with `len₁,len₂ < e.len < readLen`) is
  arithmetically unsatisfiable for proper overlaps: `len₁+len₂ ≤ 2·e.len−2`
  forces `e.len ≥ readLen+2`. It removes nothing. [audited; confirmed]
- The repository's `isReducibleLongerB` **removes** `AAB → BAB` (len `1`):
  the intermediate strand `ABA` has `maxOverlap(AAB,ABA) = 2 > 1` and
  `maxOverlap(ABA,BAB) = 2 > 1`. [kernel-checked]
- The Myers spelling-equality reduction removes it too: `AAB → ABA → BAB` with
  overlaps `2,2` spells `AABAB`, identical to the direct edge's `AABAB`. The
  intermediate `ABA` is a strand of the observed molecule `{BAB,ABA}`.
  [kernel-checked]

## 3. Observation 7 fails

`D`'s molecule spectrum `{AAA:2, AAB:2, ABA:2, BAA:2}`; the walk visits
`{AAA:2, AAB:2, ABA:1, BAA:2}`. The walk skips the offset-`3` window `ABA`,
which is a real read molecule. Hence the walk is not a flow for `D`.

## 4. `D` is a genuine §6.2 candidate

Full-overlap window walk (all overlaps `2`): strands
`AAA, AAA, AAB, ABA, BAB, ABB, BBA, BAA`; every step is a graph edge; every
interior incidence is opposite; molecule throughput
`{AAA:2, AAB:2, ABA:2, BAA:2}` equals `D`'s spectrum. [kernel-checked]

## 5. Likelihood (exact rationals)

Sampling: all `8` starts once plus `4` extra copies of start `0`
(`n = 12`). Oriented observed counts
`{AAA:5, AAB:1, ABB:2, BBA:2, BAB:1, BAA:1}`; molecule counts
`{AAA:5, AAB:3, BAA:3, ABA:1}`.

| objective | oriented reading | molecule reading |
|---|---|---|
| exact candidate-intrinsic multinomial `L(D)/L(S)` | `2` | `9/4` |
| fixed-`N=8` product-binomial `L(D)/L(S)` | `1341068619663964900807/448762029294263205888 ≈ 2.98837` | `57953201611271925373278879744/6211904899255558013916015625 ≈ 9.3303` |

The oriented values reproduce board PART 7 / message 12 exactly. Under the
source's molecule reading both objectives still strictly prefer `D`, so the
witness remains a valid **unrestricted/same-length** distinction — but the
mechanism is not variable overlaps.

## 6. Bottom line for #247

The proposed variable-overlap walk does **not** rescue `D` as a §6.2 flow, and
the premise that `D` fails §6.2 support equality is false under the source's
molecule reading. The real, still-valid content of the witness is:
(i) a same-length molecule §6.2 candidate with strictly larger exact/binomial
likelihood than the truth, and (ii) evidence that the current
`Spelling.step` hardcoding `readLen − 1` is an expressiveness gap for
`oMin < readLen − 1` — but that gap is *not* what makes this witness work.
