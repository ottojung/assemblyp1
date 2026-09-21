# The oriented single-strand same-length Section 6.2 residue

_Status: independent from-scratch computation + reduction, 2026-09-20. It
attacks the residue left explicitly open in
[`mb09-se62-relations-independent-audit-2026-09-20.md`](mb09-se62-relations-independent-audit-2026-09-20.md)
§4.3: the same-length §6.2 statement under the **oriented single-strand**
reading. All claims are labelled **source fact**, **mathematical argument**,
**verified computation**, **conjecture**, or **open**. It does not settle which
Medvedev–Brudno (2009) object the Shomorony et al. (2016) sentence intends, and
does not touch tie/equivalence semantics._

_Reproduce: `python3 scripts/verify_oriented_ss_se62_same_length.py`
(quick, ~10 s) and `... --full` (all listed scopes, several minutes).
Self-contained, exact `fractions.Fraction`, deterministic, non-zero exit on any
failed assertion._

---

## 0. Answer at a glance

The request splits into two logically different statements, and they have
opposite answers.

1. **Sequence objective (SEQ).** Oriented single-strand read types, fixed-`N`
   MB09 §6.1 product of binomial marginals, external `N = G`, **no** §6.2
   overlap-graph constraint. A same-length `I_s` witness exists: the #32
   `AAACC → AAAAC` pair (binomial ratio `1125/512 > 1`, exact ratio `2`). This
   is a **sequence-only** witness: neither the truth nor the competitor has a
   window spectrum supported inside the observation, so neither is a §6.2
   candidate.

2. **§6.2 support-equality / per-vertex restriction (S62).** Same oriented
   single-strand objective and same length, but the truth-induced candidate
   **and** the competitor must each have `supp(spec_L(·)) = supp(x)`. Here the
   attack returns a **reduction** plus a **large exhaustive zero**:

   > a strict same-length S62 counterexample exists **iff** there is a circle
   > `S` whose `I_s` is realizable **and** whose length-`L` spectrum is
   > non-rigid on its support.

   Exhaustive enumeration finds **no** such `S` in any tested scope (binary up
   to `G = 18`; ternary up to `G = 12`; four-letter up to `G = 10`; `L = 2..5`).
   Every non-rigid truth found has a triple repeat of length `≥ L-1`, which is
   exactly the length that `I_s` cannot bridge. This is recorded as a conjecture,
   not a theorem.

The distinction the task asks for is therefore sharp: the sequence objective is
refuted by an existing witness; the §6.2-restricted oriented reading is
**not** refuted, and is computationally rigid.

---

## 1. The two readings, precisely

**Read model (Shomorony et al. 2016, §2, source fact).** A circular truth `S`
of length `G`; `N` error-free reads of common length `L` drawn independently and
uniformly from the `G` circular start positions. Read types here are **oriented**
length-`L` strings (no reverse-complement collapse), matching the literal `4^k`
index of MB09 §6.1 (unmerged branch artifact `mb09-se61-index-orientation-resolution.md`, §1.2).

**Likelihood (MB09 §6.1 fixed-`N` binomial, source fact).** With observed counts
`x(w)`, `n = Σ_w x(w)`, candidate multiplicities `d(w)`, and external genome
length `N`,

```text
B(d) = ∏_w C(n, x(w)) (d(w)/N)^{x(w)} (1 − d(w)/N)^{n − x(w)}.
```

Here `N = G` is the true length and the orientation is that of the read strings.
The exact same-length multinomial ratio, with the common denominator `G`, is

```text
E(d_D)/E(d_S) = ∏_{w: x(w)>0} (d_D(w)/d_S(w))^{x(w)}.
```

**§6.2 per-vertex admissibility for a spelled molecule (source fact + inference).**
A spelled circular molecule `D` is an admissible §6.2 candidate iff
`supp(spec_L(D)) = supp(x)` (Observation 7 plus the per-vertex lower bound `1`;
see `section62-same-length-bidirected-counterexample.md` §1.1). This is the
constraint removed in the SEQ reading and imposed in the S62 reading.

**`I_s` (Shomorony et al. §5 Eq. (1), source fact).** `R ∈ I_s` iff the reads
cover `S`, every triple repeat is all-bridged, and every interleaved repeat pair
is bridged. A copy of a repeat of length `ell` is bridged by a length-`L` read
iff the read contains both flanking positions, at cyclic distance `ell + 1`;
hence a copy can be bridged only if `ell ≤ L − 2`.

---

## 2. Sequence objective: the `I_s` witness is real and is not §6.2

The #32 pair (`fixed-length-binomial-counterexample.md`) is already an oriented
single-strand, same-length, `I_s` witness. Independently recomputed here:

```text
truth       S = AAACC        G = 5
read length L = 3            external N = 5
realized starts (0,1,4)      n = 3
observed    x = { AAA:1, AAC:1, CAA:1 }
spec(S)       = { AAA:1, AAC:1, ACC:1, CCA:1, CAA:1 }
competitor  D = AAAAC        |D| = 5
spec(D)       = { AAA:2, AAC:1, ACA:1, CAA:1 }
fixed-N 6.1 binomial ratio  = 1125/512 > 1
same-length exact ratio     = 2
```

`I_s` holds: the starts cover `{0,1,2,3,4}` and the maximal length-1 triple
repeat of `A` is all-bridged. Crucially, `supp(spec(S))` contains `ACC, CCA`
which are unobserved, and `supp(spec(D))` contains `ACA` which is unobserved;
so **neither side is a §6.2 candidate**, and this witness does not transfer to
S62. [verified computation]

**Consequence.** The literal request "same-length truth and competitor with `I_s`
and strict likelihood improvement" is satisfiable at the sequence level and has
been for some time. The open part is only the §6.2 restriction.

---

## 3. The S62 reduction

Throughout, `m` denotes the multiplicity vector over start positions (not over
types); a read is placed at start `r` with multiplicity `m(r)`. `I_s` is a
property of the **support** of `m` (adding reads preserves coverage and all
bridging clauses), and `x(w) = Σ_{r: window(S,r)=w} m(r)`.

**Reduction.** For fixed `G, L, Σ`, a strict same-length S62 counterexample
exists **iff** there is a circular `S` with

- **(A)** `I_s` is realizable on `S`; and
- **(B)** some circular `D` of length `G` has
  `supp(spec_L(D)) = supp(spec_L(S))` and `spec_L(D) ≠ spec_L(S)`.

*Proof.* Write `V = supp(spec_L(S))`.

(⇐) Assume (A) and (B). By (A), taking `m(r) = 1` for every start `r` is an `I_s`
realization (all positions sampled ⇒ coverage; every bridgeable copy is
witnessed by its flanking start). Then `x(w) = d_S(w)` and `supp(x) = V`, so `S`
is S62-admissible. By (B), `d_D` and `d_S` are supported on `V`, have equal
total `G`, and differ, so some `w0` has `d_D(w0) > d_S(w0)`. Put `M` extra reads
at any start `r0` with window type `w0`. Then `x(w) = d_S(w) + M·[w = w0]`, the
support is still `V`, and

```text
E(d_D)/E(d_S) = (∏_w (d_D(w)/d_S(w))^{d_S(w)}) · (d_D(w0)/d_S(w0))^M.
```

The first factor equals `exp(−G·KL(p_S ‖ p_D)) ≤ 1`; the second tends to
`+∞` because its base exceeds `1`. Hence `E(d_D) > E(d_S)` for large `M`, and
`D` is S62-admissible by (B).

(⇒) A strict same-length S62 counterexample supplies an `I_s` realization of its
truth (giving (A)) and a `D` with `supp(spec_L(D)) = supp(x) = V` and
`spec_L(D) ≠ spec_L(S)` (else the ratio is `1`), giving (B). ∎

Condition (A) has an elementary form: a copy of length `ell` is bridgeable only
if `ell ≤ L − 2`, and adding reads is monotone, so

```text
(A)  ⇔  every triple repeat of S has length ≤ L − 2, and every interleaved
       pair contains a repeat of length ≤ L − 2.
```

This was cross-checked against the reviewed `I_s` implementation in
`scripts/fixed_length_bridging_search_v2.py` on `G ≤ 12` with zero mismatches.
[verified computation]

Condition (B) is a statement about the **rigidity** of the length-`L` spectrum
support: whether a circle's `L`-spectrum is the unique positive balanced
weighting, of the given total, on its support graph.

---

## 4. Why (A) and (B) appear incompatible: a conjecture

For two same-support spectra, `δ = d_D − d_S` is a nonzero integer circulation
on the `(L−1)`-mer de Bruijn support graph with `Σ_w δ(w) = 0`. Such a
circulation is an integer combination of directed cycles with cancelling total
length. The exhaustive search shows, in every tested scope, that any `S`
carrying such a trade also carries a **long** repeated substring:

**Conjecture C.** If `spec_L(S)` is non-rigid on its support (condition (B)),
then `S` has a triple repeat of length `≥ L − 1`.

Equivalently, `(A) ⇒ spec_L(S) is rigid on its support`. If C holds, then **no
strict same-length S62 counterexample exists for any `G, L, Σ`, under any
objective that depends only on `(d, x)`** — because an `I_s`-realizable truth
would have a unique same-support same-length competitor spectrum, forcing ratio
`1`. The fixed-`N` binomial and the exact multinomial would both be moot; this
explains why the separate multiset search of §5 finds no binomial witness
either.

C is **not proved**. The mechanism is visible in concrete cases. For
`S = 000111`, `G = 6`, `L = 3`: the support graph's cycle cone is generated by
the two self-loops `000`, `111` and the `4`-cycle `001→011→110→100`, and the
total-length constraint plus positivity pins the unique solution `(1,1,1)`
(the two self-loops are precisely the length-`3` triple repeats, unbridgeable by
length-`3` reads). [verified computation]

> **Update (2026-09-21).** C is now proved, in the sharper form
> "non-rigid ⇒ some `(L−1)`-mer occurs ≥ 3 times", together with the reduction
> `(A) ⇒ rigid`; see
> [`support-rigidity-under-bridging-2026-09-21.md`](support-rigidity-under-bridging-2026-09-21.md).
> The `(A) ⇒ rigid` sentence above is therefore a theorem, and the strict
> same-length S62 residue is closed negatively. The `(SEQ)` half of §0 is
> unaffected.

---

## 5. Exhaustive scope and completeness

`scan_scope` enumerates **all** `σ^G` circular truths, groups them by
`supp(spec_L)`, and counts the truths that are both non-rigid and
`I_s`-realizable. By the reduction this count is exactly the number of
same-length S62 counterexamples in that scope. The count is **zero** everywhere:

| alphabet | `L` | `G` range | non-rigid supports (last `G`) | S62 witnesses |
|---|---|---|---|---|
| binary | 2 | 9–10 | 3 | 0 |
| binary | 3 | 14–18 | 19 | 0 |
| binary | 4 | 14–18 | 404 | 0 |
| binary | 5 | 12–16 | 146 | 0 |
| ternary | 3 | 10–12 | 2114 | 0 |
| ternary | 4 | 10–11 | 99 | 0 |
| four-letter | 3 | 8–10 | 1538 | 0 |

Each row is **exhaustive and complete** over all `σ^G` circles in the stated
range: no truncation, no sampling. The earlier bounded zeros (`G ≤ 7`, `L ≤ 4`
in `section62-same-length-bidirected-counterexample.md` §3) are subsumed and
extended. The binary `G = 18` rows enumerate 262 144 truths; the ternary
`G = 12` row enumerates 531 441. [verified computation]

The separate **multiset** search (`oriented_ss_search.py`, kept in scratch) also
enumerates all read multisets with multiplicities, checks `I_s` and
`supp(spec(S)) = supp(x)`, and evaluates both objectives directly; it finds zero
binary witnesses for `G ≤ 8`, `L ∈ {3,4}`, all `n` up to `G+1`, and zero ternary
witnesses for `G ≤ 9`. This confirms that the reduction does not miss any
multiplicity effect, including the `(1 − d/N)^{n−x}` factors of §6.1. The
reduction is complete; the direct search is the independent check.

---

## 6. Relation to the published question

- The 2016 sentence names no MB09 section, so neither the exact multinomial, the
  fixed-`N` binomial, nor the §6.2 flow is selected by the source
  (`shomorony-referent-model-match-decision.md`). This note therefore reports a
  scoped mathematical fact, not a settlement.
- Under the strongest sequence-level referent (§6.1 exact/multinomial on
  oriented strings), the answer is negative and already witnessed (#31/#32), and
  the same-length candidate-class inclusion transfers this to the unrestricted
  candidate class (`same-length-witnesses-candidate-set-inclusion.md`).
- Under the §6.2-restricted same-length reading, the repository's earlier
  per-vertex witness (`AAATAT → AAAAAT`) needs reverse-complement collapse;
  under the strict oriented reading it inverts (unmerged branch artifact
  `mb09-se61-index-orientation-resolution.md`, §4). This note's object is precisely that vacancy: it remains vacant.
- The per-occurrence strengthening `d_D(w) ≥ x_w` is a different, strictly
  stronger reading; see `se62-peroccurrence-search-degeneracy.md`.

---

## 7. Epistemic status

| Claim | Status |
|---|---|
| Shomorony read model is oriented single-strand; MB09 §6.1 fixed-`N` product of binomials is the stated objective | **source fact** (2016 §2; MB09 §6.1) |
| #32 is a same-length oriented `I_s` witness with ratios `1125/512` (binomial) and `2` (exact) | **verified computation** |
| #32 truth and competitor are not §6.2 support-equal | **verified computation** |
| `I_s` realizable ⇔ every triple repeat `≤ L−2` and every interleaved pair has a repeat `≤ L−2` | **mathematical argument**, cross-checked against the reviewed `I_s` code |
| Reduction (§3): S62 same-length exact counterexample ⇔ (A) ∧ (B) | **proof** |
| No S62 witness in the tabulated scopes | **verified computation, exhaustive and complete in scope** |
| Conjecture C: non-rigid support ⇒ a triple repeat of length `≥ L−1` | **now proved** (sharper: some `(L−1)`-mer occurs `≥3` times); see [`support-rigidity-under-bridging-2026-09-21.md`](support-rigidity-under-bridging-2026-09-21.md) |
| `I_s` ⇒ §6.2 same-length truth is a maximizer under every `(d,x)`-objective | **proved** via the Main theorem of [`support-rigidity-under-bridging-2026-09-21.md`](support-rigidity-under-bridging-2026-09-21.md) |
| Which MB09 object the 2016 sentence denotes | **open source ambiguity** |

---

## 8. Reproduce

```sh
python3 scripts/verify_oriented_ss_se62_same_length.py          # quick, ~10 s
python3 scripts/verify_oriented_ss_se62_same_length.py --full   # all scopes
python3 scripts/verify_oriented_ss_se62_same_length.py --full   # exits 0 iff S62 zero
```

The script is self-contained (it re-implements spectra, repeats, interleaving
and `I_s` rather than importing the reviewed searches), uses exact rational
arithmetic, and asserts both the #32 sequence witness and the S62 zeros.

Primary sources: Ilan Shomorony, Samuel H. Kim, Thomas A. Courtade, David N. C.
Tse, *Information-optimal genome assembly via sparse read-overlap graphs*,
*Bioinformatics* 32(17) (2016) i494–i502, §2 and §5, DOI
`10.1093/bioinformatics/btw450`; Paul Medvedev, Michael Brudno, *Maximum
Likelihood Genome Assembly*, *J. Comput. Biol.* 16(8) (2009) 1101–1116, §3.1,
§4.1, §6.1–6.2, PMC3154397.

Cross-references:
[`mb09-se62-relations-independent-audit-2026-09-20.md`](mb09-se62-relations-independent-audit-2026-09-20.md),
[`reverse-complement-strand-convention.md`](reverse-complement-strand-convention.md),
unmerged branch artifact `mathematics/section62-peroccurrence-search-degeneracy.md`,
[`same-length-witnesses-candidate-set-inclusion.md`](same-length-witnesses-candidate-set-inclusion.md),
[`../fixed-length-binomial-counterexample.md`](../fixed-length-binomial-counterexample.md).
