# Exact fixed-length likelihood: duality, flow characterization, and a correction

_Status: mathematical analysis with proofs, plus an explicit exact-arithmetic
verification harness. Not a Lean result. All claims are classified by
epistemic class. This note corrects a characterization error present in
several earlier repository notes; see §5._

---

## 0. Scope and relation to earlier notes

This note studies the **fixed-length exact multinomial likelihood** (the
restriction `|D| = |S| = G` of Medvedev–Brudno §6.1, "Variant E"),

```text
L(D | x) = N! / (prod_i x_i!) * prod_i (d_D(i) / G)^{x_i},
```

where `x = (x_i)` is the observed L-mer count vector and `d_D = (d_D(i))` is a
candidate's circular L-mer occurrence vector. Earlier repository notes already
established the reduction `L(D|x) ∝ prod_i d_D(i)^{x_i}` and produced
counterexamples. This note does four things those notes do not:

1. reduces the comparison to a **finite polytope-normal-cone test that depends
   only on the sample direction `x/‖x‖₁`** (§2);
2. gives the exact **integer circulation (cycle-lattice) characterization** of
   all competitors and the first-order vulnerability criterion (§3);
3. **corrects** the repository's "proportionality iff optimality" claim: the
   Eulerian balance constraints are equalities, so the normal cone is
   `span{1} + rowspace(B)`, not `span{1}` (§5);
4. proves a **positivity-aware water-filling upper bound** on every competitor
   and shows it is the exact optimum of the Eulerian relaxation (§6).

Verification: `scripts/fixed_length_likelihood_duality.py`.

---

## 1. Setup and the linear-in-`x` form

Fix an alphabet `Σ` with `|Σ| ≥ 2`, read length `L ≥ 2`, and common candidate
length `G ≥ L`. Let `E = |Σ|^L` index L-mer types and `V = |Σ|^{L-1}` index
(L-1)-mer nodes of the de Bruijn graph `B(Σ, L-1)`.

For each L-mer type `i`, write `tail(i)` for its length-`(L-1)` prefix and
`head(i)` for its suffix; `i` is a directed edge `tail(i) → head(i)`.

The **degree-balance (incidence) matrix** `B` is the `V × E` integer matrix

```text
(B delta)_u = sum_{i: head(i)=u} delta_i  -  sum_{i: tail(i)=u} delta_i.
```

A circular genome of length `G` has occurrence vector `d` satisfying

```text
(1)  d ∈ Z_{>=0}^E,    1^T d = G,    B d = 0,    supp(d) connected.   (R)
```

Conversely, every integer `d` satisfying (R) is realizable by a circular genome
of length `G` (classical Eulerian-cycle theorem; see
`docs/eulerian-edge-count-formulation.md` §2).

Fix a true genome `S` with occurrence vector `d_S`, and a sample `x ≥ 0` with
`N = 1^T x > 0` and `supp(x) = O`. Define

```text
a_D := log d_D - log d_S        (componentwise, finite where d_D(i) > 0)
Phi(x) := max { <x, a_D> : d_D satisfies (R), d_D(i) >= 1 for all i in O }.
```

**Lemma 1 (log-ratio is linear in `x`).** For any candidate `D` with
`d_D(i) ≥ 1` on `O`,

```text
log L(D|x) - log L(S|x) = sum_{i in O} x_i log(d_D(i)/d_S(i)) = <x, a_D>.
```

In particular the *ordering* `S` versus `D` depends on `x` only through the
inner product with `a_D`; the multinomial coefficient and the factor `G^{-N}`
cancel.

_Proof._ Immediate from the product form; terms with `x_i = 0` contribute `0`.
`□`

**Corollary 1 (truth wins iff `Phi = 0`).** `S` is an ML maximizer for `x` iff
`Phi(x) = 0`. Moreover `Phi(x) ≥ 0` always, because `d_S` itself is feasible
(realizable, and `d_S(i) ≥ 1` on `O` since reads are drawn from `S`).

Thus "truth loses" is exactly the strict inequality `Phi(x) > 0`.

_Epistemic status: proof._

---

## 2. Reduction 1: finite normal-cone test and scale invariance

For fixed `G` the set of realizable vectors is finite. Enumerate it once as
`V_G ⊂ Z_{≥0}^E`. For a fixed support `O`, define the finite set of shifted
log-vectors

```text
C_O := conv { log d_D - log d_S : d_D ∈ V_G, d_D(i) ≥ 1 for i ∈ O } ⊂ R^E.
```

**Theorem 1 (normal-cone characterization).** For every sample `x` with support
`O`,

```text
S is an ML maximizer for x   ⟺   x ∈ N_{C_O}(0),
```

the normal cone of the polytope `C_O` at `0` (equivalently: `0` maximizes
`<x, ·>` over `C_O`).

_Proof._ `Phi(x) = max_{c ∈ C_O} <x,c>` because the maximum of a linear
functional over a finite set equals its maximum over the convex hull. By
definition of the normal cone, `0` maximizes `<x, ·>` over `C_O` iff
`x ∈ N_{C_O}(0)`. Apply Corollary 1. `□`

**Corollary 2 (scale invariance; `N` is irrelevant).** If `x` is winning then
so is `λx` for every `λ > 0`. Whether truth wins depends only on the sample
*direction* `x / ‖x‖₁`, not on the number of reads `N`.

This is a genuine reduction: it removes `N` from the problem and shows that
"concentration `N → ∞`" and "one more read" are the same question up to scale.
It also implies the vulnerability region, when nonempty, is a **finite union of
open convex cones**

```text
V_O = { x ≥ 0, supp(x) = O : <x, a_D> > 0 for some competitor D }.
```

**Corollary 3 (polyhedral decision procedure).** For fixed `(G, L, Σ)`, `x` is
winning iff the linear program `max_{c ∈ C_O} <x, c>` has value `0`. If `0` lies
in the *interior* of `C_O`, then `N_{C_O}(0) = {0}` and **no** nonzero sample
makes truth an ML maximizer.

_Epistemic status: Theorems/Corollaries 1–3 are proofs. The claim "`0` interior
to `C_O` forces no winning sample" is a proof. Whether `0` is interior for
specific `(G,L,Σ,S,O)` is a finite computation._

---

## 3. Reduction 2: integer circulation (cycle-lattice) characterization

Attainability of a competitor is an **integer lattice** condition.

**Theorem 2 (competitor = truth + integer circulation).** A vector `d_D` is a
length-`G` competitor that is positive on `O` iff

```text
d_D = d_S + δ,   δ ∈ Z^E,   1^T δ = 0,   B δ = 0,
d_S + δ ≥ 0,    (d_S + δ)_i ≥ 1  ∀ i ∈ O,   supp(d_S + δ) connected.
```

The lattice `L := {δ ∈ Z^E : 1^Tδ = 0, Bδ = 0}` is the **cycle lattice** of the
de Bruijn graph; its real span is the cycle space of dimension `E − V`.

_Proof._ Subtract the two copies of (R) for `d_D` and `d_S`. `1^T` and `B`
linearity give the constraints; nonnegativity, positivity on `O`, and
connectivity are exactly (R) for `d_D`. `□`

**Corollary 4 (exact log-ratio over circulations).**

```text
log L(D|x) - log L(S|x) = sum_i x_i log(1 + δ_i / d_S(i)).
```

**Theorem 3 (first-order vulnerability criterion).** Let `g_i := x_i / d_S(i)`
(defined for `i ∈ O`). If there exists a feasible circulation direction
`δ ∈ L` with

```text
sum_{i ∈ O} g_i δ_i > 0,
```

then `d_S` is not a local maximizer of the objective over the continuous
Eulerian polytope `{d : 1^T d = G, B d = 0, d > 0}`; consequently there are
samples (any positive scaling of `x`) for which a realizable competitor can
beat `S` whenever the direction can be realized with the required signs and
integrality.

_Proof._ For `d_S` interior, directions `δ` with `1^Tδ = 0`, `Bδ = 0` are
feasible tangents. The directional derivative of `f(d) = Σ x_i log d_i` at
`d_S` along `δ` is `Σ (x_i/d_S(i)) δ_i`. A positive directional derivative
means `d_S` is not a local maximum. `□`

**Remark (why large gains are possible).** Along a *fixed* circulation
direction `δ`, the gain `Σ_{i∈O} x_i log(1 + t δ_i/d_S(i))` grows like
`const · log t` in `t`, while negative entries `δ_i < 0` become infeasible once
`t = d_S(i)/|δ_i|`. The obstruction to unbounded amplification is therefore
the **multiplicity budget** `d_S` on the edges that the circulation must
decrease, not the positive edges. This is the precise sense in which "truth
must have enough repeated material to absorb the negative side of a
circulation"; it is the structural content of the family constructions in
`mathematics/parametric-variant-e-families.md`.

_Epistemic status: Theorem 2, Corollary 4 are proofs. Theorem 3 is a proof of
the stated implication; the final clause about realizability is a caveat, not a
claim._

---

## 4. The continuous Eulerian relaxation

It is useful to separate the **continuous relaxation**

```text
P(G,L,Σ) := { d ∈ R^E : d ≥ 0, 1^T d = G, B d = 0 },
```

from the true discrete/connected competitor set (R). Since (R) ⊂ P, any `x`
for which `d_S` maximizes `f` over `P` is certainly winning. The relaxation is
where the clean convex analysis lives; the gap between it and (R) is the
content of §6.

---

## 5. Correction: the Eulerian normal cone is `span{1} + rowspace(B)`

### 5.1 The error in earlier notes

Several repository notes state:

> "For `d_S` in the relative interior of `P`, the normal cone is
> `N_P(d_S) = span{1}`, therefore `d_S` is optimal iff `x_i / d_S(i)` is
> constant for all `i`, i.e. `x_i ∝ d_S(i)`."

See `docs/fixed-length-ml-objective-analysis.md` §4.3, §6.3 and
`mathematics/fixed-length-exact-likelihood-characterization.md` §5.4, §6.1,
and the "proportionality = optimality" theorem derived from them.

**The error.** The Eulerian balance equations `B d = 0` are **equality
constraints**, so they are active at *every* feasible point, including
relative-interior points. The tangent space at a feasible point is
`{δ : 1^Tδ = 0, Bδ = 0}`, not `{δ : 1^Tδ = 0}`. The normal cone is therefore
the full row space

```text
N_{affine}(d_S) = span{1} + rowspace(B)     (dimension V),
```

not `span{1}`. The incorrect formula would be right only for the simplex
`{d ≥ 0, 1^T d = G}` with the balance constraints dropped.

### 5.2 Correct characterization

Write `head(i)` and `tail(i)` for the suffix/prefix (L-1)-mer nodes of L-mer
`i`.

**Theorem 4 (flow-potential / corrected KKT).** Let `d_S > 0` (interior of the
simplex) and `g_i = x_i / d_S(i)` (with `g_i := 0` when `x_i = 0`). Then `d_S`
maximizes `f(d) = Σ x_i log d_i` over `P(G,L,Σ)` iff there exist a scalar
`λ ∈ R` and node potentials `μ ∈ R^V` such that

```text
g_i = λ + μ_{head(i)} - μ_{tail(i)}     for every L-mer type i.        (FP)
```

Equivalently, `g` is orthogonal to the cycle space:
`Σ_i g_i δ_i = 0` for all `δ` with `1^Tδ = 0`, `Bδ = 0`.

_Proof._ `f` is strictly concave and `P` is convex, so `d_S` is optimal iff
`∇f(d_S) = g` lies in the normal cone of `P` at `d_S`; at an interior point
(with all `d_S(i) > 0`, so the nonnegativity constraints are slack) that normal
cone is `span{1} + rowspace(B)`. A row `μ^T B` evaluated at edge `i` is
`μ_{head(i)} - μ_{tail(i)}`, which gives (FP). `□`

**Corollary 5 (proportionality is sufficient, not necessary).**
`x_i ∝ d_S(i)` (i.e. `g` constant) satisfies (FP) with `μ = 0`, so it is
sufficient. It is **not** necessary: any `g` of the graph-potential form (FP)
works, and such `g` need not be constant.

### 5.3 Explicit counterexample to the "iff"

Take `Σ = {A,C}`, `L = 2`, so edges are `AA, AC, CA, CC` and the only balance
constraint is `d_AC = d_CA`. Let `S = AACC`, so `d_S = (1,1,1,1)`. Let

```text
x = (AA:2, AC:3, CA:1, CC:2).
```

Then `g = x/d_S = (2,3,1,2)` is **not** constant, but
`g = 2·1 + 1·(e_AC − e_CA)`, i.e. (FP) holds with `λ = 2` and potential
difference `1` across the single loop. Hence `d_S` maximizes the (continuous)
likelihood over `P`, even though `x` is not proportional to `d_S`. Exact
check: `f(d)` over the affine set `d_AC = d_CA = t`, `d_AA + d_CC = 4 − 2t`
equals `4 log(2−t) + 4 log t`, maximized uniquely at `t = 1`, i.e. at
`d = (1,1,1,1)`.

The harness additionally finds, by exhaustive search over binary alphabets and
`G ≤ 6`, samples whose truth is optimal and non-proportional and whose `g`
lies in the cut space.

### 5.4 What is and is not affected

- **Not affected:** the counterexamples refuting fixed-length Variant E/A and
  their parametric families. Those rest on explicit competitors and remain
  valid. The bridging-asymmetry conclusions (bridging constrains `d_S` but not
  the competitor polytope) also remain valid.
- **Affected:** every note that uses "`x ∝ d_S` iff truth optimal" as a
  characterization, e.g. to argue a positive result for Variant F. The correct
  criterion is the flow-potential condition (FP) over the relevant polytope.
  This *weakens the necessary condition* and hence *enlarges* the set of
  samples for which a positive result is still possible.

_Epistemic status: §5.1 is a proof that the earlier statement is false
(exhibited by §5.3). §5.2 is a proof. §5.3 is an exact computation plus an
analytic check._

---

## 6. Inequality: positivity-aware water-filling bound

The relaxation `P` ignores integrality, connectivity, and — when we optimize
only over observed types — the positivity requirement. Positivity alone yields
a closed-form upper bound.

Fix `O = supp(x)` and assume `|O| ≤ G`. Define the **positivity relaxation**

```text
U(x, O, G) := max { sum_{i in O} x_i log d_i :
                    d_i ≥ 1 for i in O,   sum_{i in O} d_i ≤ G }.
```

**Theorem 5 (closed form via a threshold).** `U(x,O,G)` is attained at a
water-filling vector: there is a threshold `λ > 0` and a saturated set
`A = {i ∈ O : x_i > λ}` such that

```text
d_i = x_i / λ  for i ∈ A,     d_i = 1  for i ∈ O \ A,
λ = (sum_{i in A} x_i) / (G - |O| + |A|),
U(x,O,G) = sum_{i in A} x_i log(x_i / λ).
```

The pair `(A, λ)` is determined self-consistently by the sign conditions
`x_i > λ` on `A` and `x_i ≤ λ` off `A`; the resulting value `U` is unique.

_Proof._ `U` is a concave maximization over a convex polytope; the sum
constraint binds because the objective is increasing, and the KKT conditions
are `x_i/d_i = λ + μ_i`, `μ_i ≥ 0`, `μ_i(d_i − 1) = 0`. On `A` (where
`d_i > 1`), `μ_i = 0`, so `d_i = x_i/λ`; off `A`, `d_i = 1` and `x_i ≤ λ`.
Summing gives the displayed `λ`. `□`

**Theorem 6 (upper bound on any competitor).** For every circular `D` of
length `G` with `d_D(i) ≥ 1` for all `i ∈ O`,

```text
sum_{i in O} x_i log(d_D(i)/d_S(i))  ≤  U(x,O,G) - sum_{i in O} x_i log d_S(i).
```

In particular, **`S` must win whenever the right-hand side is `≤ 0`.**

_Proof._ Restricting `d_D` to `O` satisfies `d_D(i) ≥ 1` and
`Σ_{i∈O} d_D(i) ≤ 1^T d_D = G`, so it is feasible for `U`. Hence
`Σ_O x_i log d_D(i) ≤ U`. Subtract `Σ_O x_i log d_S(i)`. `□`

**Corollary 6 (when the positivity bound is sharp).** Since
`d_S` restricted to `O` is itself feasible for `U` (it has `d_S(i) ≥ 1` on `O`
and `Σ_O d_S(i) ≤ G`), always

```text
U(x,O,G) ≥ sum_{i in O} x_i log d_S(i),
```

so the certificate in Theorem 6 is nonnegative and **can certify truth only
when `d_S|_O` is already water-filling-optimal**. In particular:

- for a **repeat-free** truth (`d_S(i) ∈ {0,1}`), `Σ_O x_i log d_S(i) = 0` while
  `U > 0` whenever the sample is non-uniform over `O`, so the positivity bound
  **never** proves truth wins. All the difficulty is Eulerian balance,
  integrality, and connectivity.
- for a truth whose observed multiplicities already match the water-filling
  pattern, the bound is an equality theorem and truth wins outright.

The quantity `U(x,O,G) − Σ_O x_i log d_S(i) − (best realizable ratio)` is a
computable measure of how much the Eulerian/connectivity constraints cost a
competitor. The harness reports a nonzero maximum slack on small exhaustive
instances, confirming the relaxation is strict in general.

_Epistemic status: Theorems 5 and 6 and Corollary 6 are proofs. The numerical
slack figures are computations._

---

## 7. Exact criterion for repeat-free truths

Let `S` be repeat-free (`d_S(i) ∈ {0,1}`), so `f(d_S) = 0`, and let
`O = supp(x)`.

For any competitor `d_D = d_S + δ` with `δ ∈ L`, `d_S + δ ≥ 0`, and
`(d_S+δ)_i ≥ 1` on `O`, Corollary 4 gives

```text
log-ratio = sum_{i in O} x_i log(1 + δ_i)  ≥ 0,
```

with strict inequality iff some `k ∈ O` has `δ_k > 0`.

**Theorem 7 (repeat-free criterion).** `S` is an ML maximizer for the sample
`x` iff there is **no** integer circulation `δ ∈ L` with `1^Tδ = 0`,
`d_S + δ ≥ 0`, `(d_S+δ)_i ≥ 1` on `O`, and `δ_k > 0` for at least one
`k ∈ O`.

**Corollary 7 (single observed type always loses).** If `O = {k}` (single-type
sample), then `S` loses whenever some length-`G` circular genome has
`d_D(k) ≥ 2`. Explicit witnesses:

- self-loop `k = (a,a)`: `D = a^G` has `d_D(aa) = G`;
- non-self-loop `k = (a,b)`, `a ≠ b`, `G` even: `D = (ab)^{G/2}` has
  `d_D(ab) = G/2`.

For odd `G` the harness verifies, for binary alphabets and `G = 5`, that a
length-`G` witness always exists; the general odd case is an explicit finite
construction but is stated here as verified for the tested range, not proved
in general.

**Corollary 8 (complete spectrum always wins).** If `O` is the entire L-mer
spectrum of the repeat-free `S` (all `G` types observed), then any competitor
positive on `O` has `d_D(i) ≥ 1` on all `G` types, so `1^T d_D = G` forces
`d_D = d_S`; truth wins. This recovers the "complete spectrum" theorem.

_Epistemic status: Theorem 7 and Corollaries 7–8 are proofs; the odd-`G`
existence is computation over the tested range._

---

## 8. Consequences for the open question

1. **Fixed-length Variant E and fixed-length Variant A are fully refuted**, as
   already established by explicit counterexamples. Nothing in the corrected
   characterization resurrects them.

2. **The exact "must win" condition is polyhedral, not proportional:**
   `S` wins iff `x` lies in the normal cone `N_{C_O}(0)` (Theorem 1), or
   equivalently iff no improving integer circulation exists (Theorem 7 in the
   repeat-free case). Bridging conditions constrain `d_S` and the *support* of
   `x`, but they do not constrain the *direction* `x/‖x‖₁` (Lemma 1 of
   `mathematics/bridging-combinatorial-implications-for-fixed-length.md`).
   Because wins depend only on the direction (Corollary 2), and bridging leaves
   the direction free, bridging cannot force `S` into the normal cone. This is
   the asymmetry theorem re-derived from the corrected characterization.

3. **Variant F is untouched by this correction but should be re-analyzed with
   (FP) rather than proportionality.** Under Variant F the relevant polytope is
   the overlap-graph flow polytope of §6.2 of Medvedev–Brudno, not
   `P(G,L,Σ)`; the same KKT derivation applies with the corresponding incidence
   matrix, and the "proportionality" shorthand used in earlier Variant-F notes
   should be replaced by the flow-potential condition for that polytope.

4. **The positivity bound gives a cheap one-sided certificate** for any truth
   whose observed spectrum is already water-filling-optimal; it can never
   certify a repeat-free truth (Corollary 6), sharpening the statement that
   repeat-free truths are the vulnerable core.

---

## 9. Epistemic status summary

| Claim | Status | Location |
|-------|--------|----------|
| Log-ratio linear in `x`; `N` cancels | Proof | Lemma 1 |
| Truth wins iff `Phi(x)=0` | Proof | Cor. 1 |
| Normal-cone characterization over finite competitor polytope | Proof | Thm 1 |
| Scale invariance: depends only on `x/‖x‖₁` | Proof | Cor. 2 |
| Vulnerable samples form a finite union of open convex cones | Proof | Cor. 2 |
| `0` interior to `C_O` ⟹ no winning sample | Proof | Cor. 3 |
| Competitor = truth + integer circulation | Proof | Thm 2 |
| First-order vulnerability from a positive-gain circulation | Proof (implication) | Thm 3 |
| Eulerian normal cone is `span{1}+rowspace(B)`, not `span{1}` | Proof | Thm 4, §5.1 |
| Proportionality is sufficient but not necessary | Proof + exact witness | Cor. 5, §5.3 |
| Water-filling closed form | Proof | Thm 5 |
| Bound on every competitor's advantage | Proof | Thm 6 |
| Positivity bound never certifies repeat-free truth | Proof | Cor. 6 |
| Repeat-free exact criterion via cycles | Proof | Thm 7 |
| Single-type repeat-free sample always loses | Proof (even `G`, self-loop) + computation (odd `G`) | Cor. 7 |
| Complete spectrum always wins | Proof | Cor. 8 |
| Exhaustive small-instance agreement | Computation | `scripts/fixed_length_likelihood_duality.py` |

---

## 10. Verification harness

```text
python3 scripts/fixed_length_likelihood_duality.py
```

The harness, over binary alphabets with `L = 2` and `G ≤ 6`:

- exhibits the non-proportional, cut-space KKT witness and confirms by random
  sampling of `P` that `d_S` is the continuous maximizer;
- exhaustively finds non-proportional truth-optimal samples;
- checks the water-filling bound on all exhaustive instances and reports the
  Eulerian/connectivity slack;
- confirms that no repeat-free single-type sample is safe.

It uses floating-point `log` only for comparing values; all model arithmetic
(count vectors, degree balance, cut-space tests) is exact integer/rational.
The identity claims of §§1–7 are proved, not delegated to the script.

---

## 11. Source citations

| Fact | Source |
|------|--------|
| Exact multinomial likelihood | Medvedev–Brudno 2009, §6.1 |
| De Bruijn graph / Eulerian realizability | Pevzner 2000; `docs/eulerian-edge-count-formulation.md` |
| KKT / normal-cone characterization | Boyd & Vandenberghe, _Convex Optimization_, §5.5 |
| Bridging conditions `I_s` | Shomorony et al. 2016, Eq. (1); Bresler et al. 2013 |
| Prior (incorrect) proportionality claim | `docs/fixed-length-ml-objective-analysis.md` §4.3, §6.3 |
| Prior (incorrect) proportionality claim | `mathematics/fixed-length-exact-likelihood-characterization.md` §5.4, §6.1 |
| Fixed-length counterexamples | `docs/bridging-likelihood-obstructions.md` |
| Parametric Variant-E families | `mathematics/parametric-variant-e-families.md` |
| Positivity-independent bridging asymmetry | `mathematics/bridging-combinatorial-implications-for-fixed-length.md` §2 |
