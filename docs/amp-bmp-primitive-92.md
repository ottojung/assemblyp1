# `A^m ++ B^m`: the Fine–Wilf case, formally verified

**Issue:** #92
**Status:** kernel-checked *sufficient* variant of the Lyndon–Schützenberger step used in
`docs/scalar-primitive-spellings-83.md`; the unconditional statement remains open.

## What is proved

In `AssemblyP1/AmpBmpPrimitivity.lean`, from `Period.fineWilf`
(`AssemblyP1/WordPeriodicity.lean`) and elementary list lemmas only:

```
theorem ampbmp_commonRoot {x y z : List α} {a b c : ℕ}
    (hx : x ≠ []) (hy : y ≠ []) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 1 ≤ c)
    (h : nCopies x a ++ nCopies y b = nCopies z c)
    (hlen : (a - 1) * x.length ≥ z.length) :
    ∃ w : List α, w ≠ [] ∧ ∃ p q r : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧
      x = nCopies w p ∧ y = nCopies w q ∧ z = nCopies w r
```

This is the "easy case" of the classical proof of the Lyndon–Schützenberger word
equation `x^a y^b = z^c`: under the quantitative hypothesis `(a-1)|x| ≥ |z|`, the
concatenation has period `gcd(|x|, |z|)` on its first block, and that period propagates
to the whole word and to its two pieces.

The separator consequence — the step the graph argument of
`docs/scalar-primitive-spellings-83.md` uses — is

```
theorem ampbmp_head_eq_of_pow {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k)
    (hlen : (m - 1) * A.length ≥ U.length) : A[0]? = B[0]?
```

together with

```
theorem ampbmp_not_properPower_of_head_ne  -- and ampbmp_primitive_of_head_ne
```

which say that under the same hypotheses `A^m ++ B^m` is **not** a proper power as soon
as `A` and `B` start with different letters. The counting half of the graph argument is

```
theorem dvd_mul_letterCount_of_pow (a : α) (h : nCopies A m ++ nCopies B m = nCopies U k) :
    k ∣ m * letterCount a (A ++ B)

theorem dvd_mul_of_letterCount_eq_one (a : α) (hc : letterCount a (A ++ B) = 1)
    (h : nCopies A m ++ nCopies B m = nCopies U k) : k ∣ m
```

i.e. `k` divides `m` times every letter count of `A ++ B`. Together with
`k ≥ 2` this is the divisibility half of the argument "every edge-type multiplicity of
`A^m B^m` is divisible by `k`, so `k | gcd(m c_0) = m`".

`ampbmp_no_pow_four_example` is a small worked instance: `[0,1]^2 ++ [1,0]^2` has no
fourth root.

## Axiom audit

```
$ lake env lean /tmp/ax.lean   # #print axioms for each of the above
'AssemblyP1.ampbmp_commonRoot' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.ampbmp_head_eq_of_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.ampbmp_primitive_of_head_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.dvd_mul_of_letterCount_eq_one' depends on axioms: [propext, Quot.sound]
```

No `sorry`, no `admit`, no `sorryAx`, no new axioms. Lyndon–Schützenberger is *not*
assumed anywhere; the only imported theorem is Fine–Wilf plus a hand-proved
commutation lemma and the two-unknown case `x^e = y^f` (`pow_pow_commonRoot`), used only
to finish the exponent bookkeeping of `y^b` (see below).

## Proof structure of `ampbmp_commonRoot`

Let `W = nCopies z c = x^a ++ y^b` and `d = gcd |x| |z|`, `w = x.take d`.

1. `W` has period `|z|`, so the prefix `x^a` has period `|z|`; it also has period `|x|`.
   Fine–Wilf applies because `x.length + z.length - d ≤ |x^a|`, which is exactly the
   hypothesis `(a-1)|x| ≥ |z|` (using `a ≥ 2`). Hence `x^a` has period `d`.
2. `d | |W|`, and the letters of `W` are determined by their residues mod `d`
   (`eq_nCopies_of_period_prefix`): a `|z|`-period pushes any index into the first block,
   where the `d`-period of `x^a` decides it. Therefore `W = w^{|W|/d}`.
3. `z` is a prefix of `W` of length `|z|`, hence also residue-determined, so
   `z = w^{|z|/d}`; and `x = w^{|x|/d}` by the same argument inside `x^a`.
4. The tail `y^b = W.drop (a|x|)` is a suffix of `w^{|W|/d}` starting at a `d`-multiple
   boundary (`d | a|x|`), so `y^b = w^{m}` with `m = b|y| / d`.
5. If `m = 1` then `w = y^b`, so `y` itself is a common root of `x, y, z`. If `m ≥ 2`,
   `pow_pow_commonRoot` applied to `y^b = w^m` gives a word `v` with `y` and `w` both
   powers of `v`, and `x, z` are powers of `w`, hence of `v`.

The only genuinely word-theoretic input is step 1–2, i.e. Fine–Wilf.

## Source fidelity

* The separator hypothesis used in `ampbmp_primitive_of_head_ne` (`A[0]? ≠ B[0]?`) is the
  edge-type separator of `docs/scalar-primitive-spellings-83.md`: cutting a cyclic
  Eulerian spelling at two visits to a vertex with two distinct outgoing edge types
  produces two closed excursions whose first edge types differ. Edge-type words are
  modeled here as plain letter alphabets, so "first edge type" is "first letter".
* The counting hypothesis in `dvd_mul_of_letterCount_eq_one` is a special case of
  `gcd(c0) = 1` in the same document. The general statement (forbidding all `k ∣ m c_e`
  unless `k | m` for every edge type) is not formalised; only the single-letter case is.
* `(m-1)|A| ≥ |U|` is a proof-side hypothesis, **not** part of the published statement.
  It is exactly the region of the classical proof in which the periodicity lemma
  applies.

## Exact residual statement

What is still missing is the unconditional claim

> for nonempty `A, B` with different first letters and every `m ≥ 2`, the word
> `A^m ++ B^m` is primitive,

equivalently the full Lyndon–Schützenberger theorem for `x^a y^b = z^c` with
`a, b, c ≥ 2` (Lyndon–Schützenberger 1962, DOI `10.1307/mmj/1028998766`), which
`docs/scalar-primitive-spellings-83.md` imports as a black box.

The instances not covered here are the witnesses `A^m ++ B^m = U^k` with

```
(m - 1) * |A| < |U|  =  m * (|A| + |B|) / k ,
```

i.e. where the root is long relative to the first excursion. Since `|A| ≤ max(|A|,|B|)`,
this includes every square witness `k = 2` with `|A| = |B|`, and generally all witnesses
whose two excursions have nearly equal length. In the classical proof these are exactly
the cases handled by the remaining two arguments — the `c = 3` decomposition and the
`c = 2` induction on `|z|` — neither of which is formalised.
