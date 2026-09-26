# `A^m ++ B^m`: the Fine–Wilf case, formally verified

**Issue:** #92
**Status:** kernel-checked.  The unconditional Lyndon–Schützenberger step is now proved
in `AssemblyP1/LyndonSchutzenberger.lean`; the results below are the *conditional*
variants kept for the record, and the `_uncond` corollaries supersede them.

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

* `(m-1)|A| >= |U|` appears only in the *conditional* theorems of
  `AssemblyP1/AmpBmpPrimitivity.lean`, which are kept for the record; the `_uncond`
  corollaries in `AssemblyP1/LyndonSchutzenberger.lean` are the versions without it.
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

## The unconditional statement is now proved

`AssemblyP1/LyndonSchutzenberger.lean` closes the residual.  It contains a
self-contained proof of the full Lyndon–Schützenberger word equation, using only
Fine–Wilf (`AssemblyP1/WordPeriodicity.lean`) as external input, and then derives the
three unconditional corollaries that issue #92 needs:

```
theorem lyndonSchutzenberger {x y z : List α} {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hx : x ≠ []) (hy : y ≠ [])
    (h : nCopies x a ++ nCopies y b = nCopies z c) : x ++ y = y ++ x

theorem ampbmp_commonRoot_uncond {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k) :
    ∃ w : List α, w ≠ [] ∧ ∃ p q r : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧
      A = nCopies w p ∧ B = nCopies w q ∧ U = nCopies w r

theorem ampbmp_head_eq_of_pow_uncond {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k) : A[0]? = B[0]?

theorem ampbmp_primitive_of_head_ne_uncond {A B U : List α} {m k : ℕ}
    (hA : A ≠ []) (hB : B ≠ []) (hm2 : 2 ≤ m) (hk2 : 2 ≤ k)
    (h : nCopies A m ++ nCopies B m = nCopies U k)
    (hne : A[0]? ≠ B[0]?) : IsPrimitive (nCopies A m ++ nCopies B m)
```

The instances previously excluded by `(m-1)|A| < |U|` are now covered: the
`_uncond` corollaries carry no length hypothesis, so in particular every square witness
`k = 2` with `|A| = |B|` is included.

### Proof structure of `lyndonSchutzenberger`

Strong induction on the measure `|z| + b*|y|`, following Lyndon–Schützenberger 1965 and
Lothaire 1.3.2.  Write `d = |x|`, `e = |y|`, `f = |z|`, so `a*d + b*e = c*f`.

* **Step 0 (symmetry).** If `a*d < b*e`, apply the induction hypothesis to the reversed
  equation `(rev y)^b ++ (rev x)^a = (rev z)^c`, whose measure `f + a*d` is smaller, and
  convert back with `comm_of_rev_comm`.  Hence assume `b*e ≤ a*d`.
* **Step 1 (the periodicity lemma).** If `(a-1)d ≥ f`, the existing
  `ampbmp_commonRoot` applies directly.  If `(b-1)e ≥ f`, it applies to the reversed
  equation.  In both cases `x` and `y` are powers of a common word.
* **Step 2 (`c < 4`).** Otherwise `(a-1)d < f` and `(b-1)e < f`, whence `d < f` and
  `e < f`, so `c*f = a*d + b*e < 4*f` and `c < 4`, i.e. `c = 2` or `c = 3`.
* **Step 3 (`c = 3`, `LS_core_c3`).** From `b*e ≤ a*d`, `2 ≤ a`, `b` and
  `a*d < f + d` one first derives `a = 2` (`ls_c3_a2`), so the equation is
  `x^2 ++ y^b = z^3`.  With `d < f < 2d` the critical decomposition gives
  `u ++ w = x = w ++ p`, `z = x ++ u`, `y^b = p ++ u ++ z`; the word
  `s = u ++ w ++ p` is both `|u|`-periodic and `|y|`-periodic with `|u| + e ≤ |s|`, so
  Fine–Wilf gives the period `g = gcd |u| e`; `g` divides `|x|, |z|, |u|, |w|, |p|`, and
  hence `x`, `y^b` and `z` are all powers of the length-`g` prefix of `s`.  By
  `eqPow_commonRoot` they share a primitive root, so `x ++ y = y ++ x`.
* **Step 4 (`c = 2`, the descent).** `x^a ++ y^b = z*z`; since `|z| ≤ a*d` and
  `b*e ≤ f`, the word `z` splits both as `z = x^(a-1) ++ u` and as `z = w ++ y^b`, with
  `u ++ w = x` (cancellation in `x^(a-1) ++ (u ++ w ++ y^b) = x^(a-1) ++ (x ++ y^b)`).
  The sliding identity `w (u w)^(a-1) u = (w u)^a` then turns this into the *new*
  equation `w^2 ++ y^b = (w ++ u)^a = x^a`, whose measure `|x| + b*e` is strictly smaller
  because `d < f`.  The induction hypothesis gives `w ++ y = y ++ w`, hence
  `y ++ z = z ++ y`, and cancelling in `z^c ++ y^b = y^b ++ z^c` yields
  `x^a ++ y^b = y^b ++ x^a`; `comm_of_powComm` finishes.

### Axiom audit of the new module

```
$ lake env lean /tmp/ax.lean   # #print axioms
'AssemblyP1.lyndonSchutzenberger' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.LS_core_c3' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.ampbmp_commonRoot_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.ampbmp_head_eq_of_pow_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
'AssemblyP1.ampbmp_primitive_of_head_ne_uncond' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no `sorryAx`, no new axioms.  The only imported mathematical
input is Fine–Wilf; the AFP Isabelle formalisation of Lyndon–Schützenberger was used as
a *blueprint* for the case structure only.

## What remains

The word-combinatorics half of issue #92 is closed.  What is left on the graph side is
the argument of `docs/scalar-primitive-spellings-83.md` itself: that cutting a cyclic
Eulerian spelling at two visits to a vertex with two distinct outgoing edge types
produces two closed excursions `A`, `B` with `A[0]? ≠ B[0]?`, together with the
divisibility half already formalised as `dvd_mul_of_letterCount_eq_one`.
