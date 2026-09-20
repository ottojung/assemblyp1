# Independent audit: the exact-multinomial run-shift family

_Status: independent verification + one erratum correction, 2026-09-20._
_Audits `mathematics/exact-multinomial-run-shift-family.md` (branch
`analysis/exact-run-shift-family`) against the source model of
`docs/bridging-source-semantics.md` and the ML contract of
`docs/ml-formalization-contract.md`. Companion script:
`scripts/audit_exact_run_family_independent.py`._

## 1. Question and verdict

The proposal is that

```text
S(p,q) = A^p C^q ,   D(p,q) = A^(p+1) C^(q-1)      (|S| = |D| = p+q)
```

gives an infinite same-length family of counterexamples to the claim that the
source hypothesis `R ∈ I_s` forces truth to be an exact maximum-likelihood
sequence, under the **fixed-length exact multinomial** objective (Medvedev–
Brudno §6.1 restricted to `|D| = G`).

**Verdict: essentially confirmed, with one corrected paragraph.**

1. The family is genuinely infinite, but only on the one-parameter slice
   `q = 2`, `p = L` (read length equals the `A`-run length). There the exact
   likelihood ratio is exactly `2^x` for `x` observed copies of `A^L`, and the
   witness is `I_s`-feasible.
2. For `L >= 2` no member with `q != 2` or `p != L` is a counterexample, and
   the degradations `q >= 3`, `q = 1`, `q = 2, p != L` are real obstructions.
3. The single degenerate exception at read length `L = 1`, namely `q = 2`,
   `p in {1,2}`, is correctly recorded in the note's Corollary 7.
4. The note's §2 contained an internal mislabeling (not an arithmetic error)
   that has been corrected below.

## 2. Independent evidence

`scripts/audit_exact_run_family_independent.py` re-implements the
repeat/bridging semantics from `docs/bridging-source-semantics.md` without
importing the in-repo certificate. It provides two upgrades:

- **Direct exact likelihood.** For `L = 2..40` it evaluates the *full* exact
  multinomial probability `n!/(∏ xᵢ!) · ∏ (dᵢ/N)^(xᵢ)` under both `S` and `D`
  and confirms the ratio is exactly `2^x` (`x = 4`). This checks the ratio
  algebra against the definition rather than against the identity
  `∏ (d_D/d_S)^{xᵢ}` used in the note.
- **Larger complete search.** It extends the complete all-subsets decision
  from `p+q <= 9` to every `G = p+q <= 12`, all `L`, all nonempty latent-start
  sets, with exact integer/fraction arithmetic. The only hits with `L >= 2`
  are exactly `(p,q,L) = (2,2,2), (3,2,3), ..., (10,2,10)`, i.e. `q = 2,
  p = L`; the only non-slice hit is the recorded `L = 1` degenerate
  `(p,q,L) = (2,2,1)`.

Both checks pass. The in-repo certificate `scripts/verify_exact_run_family.py`
and the proof sketches of Theorems 2, 4, 5, 6 were also re-derived by hand and
found correct (the `C^(q-2)` middle-copy obstruction for `q >= 3`, the
`A^(p-2)` middle-copy obstruction for `q = 2, p > L`, and the ratio-`1`
degeneracy for `q = 2, p = L-1`).

## 3. Erratum in §2 of the note (corrected)

The note's §2 previously read:

> In the boundary regime `p = L`, `q = L-1` (the slice of interest), the
> spectra differ by `d_D(A^L) = 2` versus `d_S(A^L) = 1`, `D` drops the two
> types `A C^(L-1)` and `C^(L-1) A`, and creates the wrap type
> `A C^(L-2) A`; ...

This is wrong in two ways for the family actually used in §3:

- the slice is `q = 2` (not `q = L-1`), so the label `q = L-1` names a
  different, unused family;
- in the slice `D = A^(L+1) C` drops every `S`-window containing both `C`s,
  i.e. the `L-1` types `A^a C^2 A^(L-2-a)` (`a = 0, ..., L-2`), and it does
  not "create" a two-block wrap type.

The stated conclusion `L(D)/L(S) = 2^x` for
`{A^L : x, A^(L-1) C : 1, C A^(L-1) : 1}` is nevertheless correct, and the
proof in §3 never used the erroneous description. The paragraph has been
rewritten to state the slice `q = 2` and the correct dropped-type list; the
independent script checks that `D`'s missing set is exactly
`{A^a C^2 A^(L-2-a)}` for every audited `L`.

## 4. Scope remark (not a change to the note's claims)

Because the competitor is *same-length*, the witness is a counterexample in any
candidate universe containing both `S` and `D`, including the **unrestricted
length** exact Variant E (where `N(D) = N(S)` makes the length factors cancel
too). The note deliberately scopes itself to the fixed-length restriction and
does not claim this; it is worth recording only as a remark, since
unrestricted-length exact ML is addressed separately (issue #24 / PR #25). It
does not settle the source question of which ML layer the 2016 sentence
intends.

## 5. Epistemic classification

| Claim | Class | Basis |
|---|---|---|
| Infinite `I_s`-feasible slice `q=2, p=L` with exact ratio `2^x` | mathematical proof (re-derived) | note Thm 2, §3 |
| Exact ratio checked against the full multinomial definition, `L=2..40` | exact-rational computation | this audit, part (A) |
| Parameter range `q=2, p=L` for `L>=2` | mathematical proof + extended complete search `G<=12` | note Cor 7, this audit part (B) |
| §2 slice label `q=L-1` and dropped/created types were wrong | documentation erratum (corrected) | this audit §3 |
| Same witness refutes unrestricted-length exact Variant E | mathematical remark | this audit §4 |

## 6. Reproduction

```text
python3 scripts/audit_exact_run_family_independent.py 12
```
