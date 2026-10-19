# The dihedral (rotation + reverse-complement) orbit quotient (#269)

Antonina #269's merged Bayes/MAP certificate
(`AssemblyP1/BayesOptimalityCertificate.lean`, PR #310) quotients the finite
circular oriented read model by **rotation** only.  The merged orbit adapter
(`AssemblyP1/GenomeOrbitAdapter.lean`, PR #200) states explicitly that
reverse-complement equivalence is a *different* action and that an oriented
one-strand read distribution need not be RC invariant, so it does not claim an
RC quotient.  This note records the kernel-checked closing increment: the
dihedral quotient **under an explicit RC-invariance hypothesis**, plus the
precise obstruction showing that hypothesis is necessary.

The Lean module is `AssemblyP1/DihedralOrbitQuotient.lean`, its dedicated axiom
audit is `AssemblyP1/DihedralOrbitQuotientAudit.lean`, and the independent
exact-rational verifier is
`scripts/verify_269_dihedral_orbit_quotient.py`.

## 1. The dihedral equivalence

Fix a finite read alphabet `α` with decidable equality, a base complement
involution `c : α → α` (`c (c a) = a`), and a positive circular genome length
`G`.  Circular words are functions `ZMod G → α`.  The **reverse complement** is

```
rcWord c S = fun i => c (S (-i)).
```

Three structural facts are kernel-checked:

| Declaration | Statement |
|---|---|
| `rcWord_rotWord` | `rcWord c (rotWord S j) = rotWord (rcWord c S) (-j)` (RC conjugates rotation to inverse rotation) |
| `rcWord_involutive` | `c ∘ c = id ⟹ rcWord c ∘ rcWord c = id` |
| `rcOrbit_involutive` | the induced map `rcOrbit` on rotation-orbit classes is an involution |

`rcOrbit` is the well-defined action of `rcWord` on `Quotient (rotSetoid α G)`
(it maps a rotation class to a rotation class because RC conjugates rotation to
inverse rotation).  The **dihedral equivalence** on rotation classes is the
two-element equivalence relation `rcSetoid c hc` that identifies a class with
its reverse complement; its quotient `Quotient (rcSetoid c hc)` is the finite
dihedral orbit quotient, with `Fintype`/`DecidableEq`/`Nonempty` instances
(provided when `α` is nonempty).

## 2. The RC-invariance hypothesis and the descent

A rotation-invariant read score `p : (ZMod G → α) → (Fin L → α) → ℝ` descends to
the rotation-orbit type via `orbitScore p hrot`.  It descends further to the
dihedral quotient **exactly when it is also RC invariant**:

```
RCInvariant c := ∀ S, readPmf (rcWord c S) = readPmf S        -- for the raw read pmf
hRC           := ∀ S, p (rcWord c S) = p S                    -- for a general score
```

Under that hypothesis `dihedralScore c hc p hrot hRC` is a well-defined
class-indexed read score, and `dihedralScore_sum_one` proves that normalization
descends.

## 3. The theorems (all kernel-checked)

Over `[Nonempty α]`, `[NeZero G]`, with `c` an involution:

| Declaration | Statement |
|---|---|
| `dihedral_map_success_monotone` | `mapSuccess π p n ≤ mapSuccessSucc π p n` — prior-averaged MAP success is nondecreasing in the number of reads, every `n` including `0`, arbitrary prior on dihedral classes |
| `uniformDihedralPrior_sum_one` | the uniform dihedral prior is a probability distribution |
| `uniform_dihedral_prior_ML` | under the uniform dihedral prior, `chooseMAP` maximizes the exact iid dihedral likelihood pointwise (MAP = ML) |
| `dihedral_certificate` | a policy is `BayesOptimal` iff it is `PointwiseMAP` for the dihedral iid joint |
| `dihedral_tie_all_optimal` | explicit tie handling: a class-independent dihedral joint makes *every* constant policy optimal (MAP non-unique) |

These are the direct dihedral lifts of the merged rotation-only endpoints
(`GenomeOrbitAdapter.orbit_map_success_monotone`,
`GenomeOrbitAdapter.uniform_orbit_prior_ML`,
`BayesOptimalityCertificate.orbit_certificate`), obtained by reusing the merged
generic finite-decision and iid-monotonicity theorems
(`AssemblyP1.FiniteBayesDecision`, `AssemblyP1.IidMapMonotonicity`) rather than
reproving them.

### The raw oriented read model under RC-invariance

For the raw oriented circular read pmf `readPmf S w = mult_S(w)/|G|`
(`GenomeOrbitAdapter.readPmf`), the same three endpoints are restated under the
explicit hypothesis `RCInvariant c`:

* `readPmf_dihedral_map_success_monotone`
* `readPmf_uniform_dihedral_prior_ML`
* `readPmf_dihedral_certificate`

### The strand-symmetrized model (unconditional)

The hypothesis is satisfiable nondegenerately.  The **strand-symmetrized** read
law

```
symReadPmf c S w = (readPmf S w + readPmf (rcWord c S) w) / 2
```

models a double-stranded molecule whose sequenced strand is chosen uniformly at
random.  It is automatically rotation invariant (`symReadPmf_rotInvariant`),
RC invariant (`symReadPmf_rcInvariant`), and normalized (`symReadPmf_sum_one`),
so `sym_dihedral_map_success_monotone` and `sym_uniform_dihedral_prior_ML` hold
**unconditionally** for this model.

## 4. The precise obstruction (the hypothesis is necessary)

The raw oriented read pmf is **not** RC invariant in general.  The smallest
kernel-checked counterexample is the length-3 binary genome `001`:

| Declaration | Statement |
|---|---|
| `Obstruction.comp2_involutive` | `i ↦ 1 - i` on `Fin 2` is an involution |
| `Obstruction.mult_S3_w00` | `mult_{001}(00) = 1` |
| `Obstruction.mult_rcS3_w00` | `mult_{rc(001)}(00) = 0` |
| `Obstruction.readPmf_S3_w00` | `p_{001}(00) = 1/3` |
| `Obstruction.readPmf_rcS3_w00` | `p_{rc(001)}(00) = 0` |
| `Obstruction.readPmf_not_rcInvariant` | `¬ RCInvariant comp2` |
| `Obstruction.no_dihedral_descent` | there is **no** function on the dihedral quotient whose pullback is the raw read pmf |

`no_dihedral_descent` is the formal statement that the raw oriented model has no
dihedral quotient at all: any class function pulling back to `readPmf` would
force `p_{001} = p_{rc(001)}`, contradicting `p_{001}(00) = 1/3 ≠ 0`.  This is
why the conditional statement, not an unconditional one, is the correct and
honest scope.

## 5. What is external versus Lean

| Item | Status |
|---|---|
| dihedral equivalence, `rcOrbit` involution, descent under RC-invariance | **Lean kernel-checked**, this module |
| MAP = ML, monotonicity, certificate, tie handling on dihedral classes | **Lean kernel-checked**, this module |
| raw read pmf is not RC invariant (`001`); no dihedral descent | **Lean kernel-checked**, this module |
| strand-symmetrized model (unconditional) | **Lean kernel-checked**, this module |
| the read model, uniform start sampling, `p_G = mult_G/|G|`, base complement | **external modeling inputs** (documented in `docs/assembly-map-orbit-adapter-269.md`) |
| per-truth monotonicity | **not claimed**; refuted by `GenomeOrbitAdapter.PerTruthDrop.perTruth_true_drops` |
| §6.1 product-binomial, §6.2 feasible-flow, #266 event-conditional | **not claimed**; distinct models |
| global "ML is best algorithm" | **not claimed**; only specified prior-average accuracy for a fixed observation model |

## 6. Reproducible proof commands

```sh
lake build AssemblyP1.DihedralOrbitQuotient --wfail        # build, warnings as errors
lake build AssemblyP1.DihedralOrbitQuotientAudit --wfail   # audit module build
lake env leanchecker AssemblyP1.DihedralOrbitQuotient       # kernel replay
lake env leanchecker AssemblyP1.DihedralOrbitQuotientAudit
python3 scripts/verify_269_dihedral_orbit_quotient.py       # independent exact rational check
python3 scripts/check-research-docs.py                      # docs integrity
```

Axiom audit: every endpoint depends only on `propext`, `Classical.choice`,
`Quot.sound` (inline `#print axioms` in `DihedralOrbitQuotient.lean`, replayed by
`DihedralOrbitQuotientAudit.lean`; the CI step "Audit axioms in every theorem
module" enforces the same allow-list over the whole `AssemblyP1` tree).  No
`sorry`, `admit`, new `axiom`, `native_decide`, `implemented_by`, or `unsafe`.

## 7. Manuscript-ready proof sketch

> Let `Θ` be the finite set of dihedral orbit classes of circular genomes over a
> finite alphabet with a base-complement involution, and let `p_θ` be an
> RC-invariant oriented read pmf (or the strand-symmetrized law, which is
> RC-invariant by construction).  For iid reads `x_1,…,x_n` the joint mass is
> `π(θ) ∏_i p_θ(x_i)`.  Because RC invariance makes `p_θ` constant on dihedral
> classes, the finite Bayes/MAP decision theorem applies verbatim on the
> quotient: the MAP policy maximizes prior-averaged zero-one success against
> every policy, and under the uniform class prior MAP is exactly ML.  The
> averaged optimum is nondecreasing in `n` by the ignore-the-last-read policy.
> The hypothesis is not vacuous and not automatic: the raw oriented read pmf of
> the binary genome `001` gives `p(00) = 1/3` while its reverse complement gives
> `0`, so no dihedral quotient of the raw model exists without it.
