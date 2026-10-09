import AssemblyP1.SameLength62TieUniqueness

/-!
# #211: the nonprimitive subcase — correction and corrected analysis

The companion note `docs/same-length-62-tie-uniqueness-211.md` §4 argues that
`P2` forces a nonprimitive `I_s`-feasible truth to be a **square** (`k = 2`),
and then that the square's de Bruijn graph is a simple cycle with edge
multiplicities `2`. **The first claim is false**, and this module records the
kernel-checked counterexample, then states the corrected argument precisely.

## 1. `P2` does not force `k = 2`

The note's step 1 reasons: "any substring of `T` occurs at `k ≥ 3` distinct
positions in `S`, so it is a triple repeat, which `P2` forbids." The error is
that `P2` forbids **maximal** triple repeats (`Genome.IsTripleRepeat` carries
the two-sided maximality condition), and a substring occurring once per copy
of `T` is a triple repeat that is **not** maximal in general.

The smallest non-degenerate counterexample is `S = 010101` at `L = 2`: the
primitive root is `T = 01` with `k = 3`, and `S` satisfies `P2` (and is fully
`I_s`-feasible at the full read set), because every `0` is preceded and
followed by `1` and every `1` is preceded and followed by `0`, so no repeat is
maximal. **[fact]** (kernel-checked below)

Consequently the note's "edge multiplicities `2`" is also wrong in general: the
multiplicity is `k`, which can be `≥ 3`. The corrected statement is that the
multiplicity is *uniform* (every `L`-mer of the primitive root occurs exactly
`k` times), not that it is `2`.

## 2. The corrected argument

The conclusion the note wants — a nonprimitive `I_s`-feasible truth has a
spectrum fibre that is a singleton up to rotation — is **supported** by the
finite search (`scripts/verify_samelength62_nonprimitive_211.py`: zero
branching failures, zero non-single-cycle failures, zero non-singleton-fibre
failures, over every binary word of length `≤ 10` and ternary word of length
`≤ 8`), but the note's *route* to it is invalid. The correct route is:

1. **`P2` + nonprimitive ⟹ no branching.** Every `(L-1)`-mer of the truth is
   followed by a *unique* symbol. A branch (an `(L-1)`-mer with two distinct
   followers) extends backward to a maximal repeat, and the periodicity of a
   nonprimitive word then promotes it to a maximal **triple** repeat of length
   `≥ L - 1`, which `P2` forbids. This is the exact residue, stated as the
   `NoBranching` predicate below. **[choice]** (the residue)
2. **No branching ⟹ deterministic successor.** The successor map on distinct
   `(L-1)`-mers is well-defined.
3. **The successor is a single cycle.** The truth spells a circuit of its
   successor graph, so the graph is connected; with out-degree `1` it is a
   single cycle.
4. **A same-spectrum word follows the same successor.** Equal spectra give the
   same `L`-mers, hence the same `(L-1)`-mers and the same unique followers.
5. **A single cycle has a unique Eulerian circuit up to rotation.** So every
   same-spectrum word is a cyclic shift of the truth.

Step 1 (`NoBranching`) is the named residue and is **not** proved here; it is
stated as the predicate below. Steps 2–5 are the remaining route and are **not**
formalised: they need the single-cycle structure of the successor graph and the
uniqueness of the Eulerian circuit on a single-cycle multigraph, which this
repository does not yet have. Closing them would give the nonprimitive
uniqueness theorem with no `EulerianCycleObstruction` hypothesis.

## 3. What this module does not do

* It does not prove `NoBranching`. That is the exact remaining residue.
* It does not re-prove the maximizer theorem.
* It does not settle the 2016 reconstruction theorem.
-/

namespace AssemblyP1.SameLength62Nonprimitive

open AssemblyP1.OrientedSameLengthML
open AssemblyP1.OrientedRigidity
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.PopulationReduction

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α] [Fintype α]

/-! ## 1. The counterexample: `P2` does not force `k = 2` -/

/-- `G = 6`, for the counterexample. -/
private theorem hG6 : 0 < 6 := by norm_num

/-- The word `010101`: the primitive root `01` repeated `k = 3` times. -/
def np6 : Fin 6 → Fin 2 := ![0, 1, 0, 1, 0, 1]

/-- **`010101` at `L = 2` is fully `I_s`-feasible** at the full read set.
Kernel-checked: there is no maximal repeat at all (every `0` is preceded and
followed by `1` and vice versa), so clauses 2 and 3 of `I_s` are vacuous and
coverage is trivial. -/
theorem np6_information_feasible :
    InformationFeasible ⟨6, hG6, np6⟩ 2 Finset.univ := by
  decide

/-- The length-`2` root `01` of the counterexample. -/
def root2 : Fin 2 → Fin 2 := ![0, 1]

/-- **`010101` is nonprimitive with `k = 3`**: it is the third power of the
length-`2` word `01`. Kernel-checked. -/
theorem np6_nonprimitive : ¬ IsPrimitive np6 := by
  intro hne
  refine hne ⟨2, by norm_num, root2, 3, by norm_num, by norm_num, ?_⟩
  intro i
  fin_cases i <;> decide

/-- **`010101` at `L = 2` satisfies `P2`.** Discharged from `I_s` by
`informationFeasible_P2`; the content is that no maximal triple repeat of
length `≥ 1` and no interleaved maximal repeat pair of length `≥ 1` exists. -/
theorem np6_P2 : P2 hG6 2 np6 :=
  SameLength62TieUniqueness.informationFeasible_P2 hG6 np6 Finset.univ
    np6_information_feasible

/-- **`010101` is not a square**: it is not the second power of any length-`3`
word. Kernel-checked. This is the concrete failure of "k = 2".

The content: a square `T^2` of a length-`3` word satisfies `w 0 = w 3`, but
`np6 0 = 0 ≠ 1 = np6 3`. -/
theorem np6_not_square : ¬ ∃ T : Fin 3 → Fin 2,
    np6 = repWord (by norm_num) T 2 6 := by
  rintro ⟨T, hT⟩
  have h0 : np6 0 = 0 := by decide
  have h3 : np6 3 = 1 := by decide
  have hT0 : np6 0 = T ⟨0 % 3, by norm_num⟩ := congrArg (fun f => f 0) hT
  have hT3 : np6 3 = T ⟨3 % 3, by norm_num⟩ := congrArg (fun f => f 3) hT
  have ekey : (0 % 3 : ℕ) = 3 % 3 := by norm_num
  have e1 : T ⟨0 % 3, by norm_num⟩ = T ⟨3 % 3, by norm_num⟩ :=
    congrArg T (Fin.ext ekey)
  rw [hT0] at h0
  rw [hT3] at h3
  rw [← e1] at h0
  exact absurd h3 (by rw [h0]; decide)

/-- **`P2` does not force `k = 2`.** The kernel-checked counterexample: a
fully `I_s`-feasible, `P2`-satisfying, nonprimitive word that is **not** a
square — its primitive root `01` is repeated `k = 3` times. This refutes the
note's §4 step 1, which claims `P2` forces `k = 2`. -/
theorem p2_does_not_force_k2 :
    InformationFeasible ⟨6, hG6, np6⟩ 2 Finset.univ ∧ P2 hG6 2 np6 ∧
      ¬ IsPrimitive np6 ∧
      ¬ ∃ T : Fin 3 → Fin 2, np6 = repWord (by norm_num) T 2 6 :=
  ⟨np6_information_feasible, np6_P2, np6_nonprimitive, np6_not_square⟩

/-! ## 2. The corrected residue: `NoBranching`

The corrected argument needs every `(L-1)`-mer of the truth to be followed by a
unique symbol. This is the exact combinatorial residue. It is stated as a
named predicate, not smuggled into a theorem hypothesis, because it is the
live mathematical content of the corrected nonprimitive route.

For a circular word `S` of length `G` at read length `L`, `NoBranching` says:
for any two starts `i j : Fin G` whose length-`(L-1)` windows agree, the
following symbols agree. Equivalently, the `(L-1)`-mer determines its successor.
-/
def NoBranching {G L : ℕ} (hG : 0 < G) (S : Fin G → α) : Prop :=
  ∀ i j : Fin G, OrientedRigidity.nodeWindow (L := L) hG S i
      = OrientedRigidity.nodeWindow (L := L) hG S j →
    OrientedRigidity.cyc hG S (i.val + L - 1)
      = OrientedRigidity.cyc hG S (j.val + L - 1)

/-- **The corrected nonprimitive residue.** Under `I_s`, a nonprimitive truth
satisfies `NoBranching`. This is the exact input the corrected simple-cycle
route needs; it is not proved in this repository.

The proof sketch (not formalised): a branch — an `(L-1)`-mer with two distinct
followers — is a maximal repeat on the following side. Extending it backward
(to the maximal repeat) and using the periodicity of a nonprimitive word
promotes it to a maximal triple repeat of length `≥ L - 1`, which `P2` (hence
`I_s`) forbids. The backward extension and the triple promotion are the
unformalised content. -/
def NonprimitiveNoBranching {G L : ℕ} (hG : 0 < G) (S : Fin G → α) : Prop :=
  ¬ IsPrimitive S → NoBranching (L := L) hG S

/-! ## 3. The `NoBranching` argument, proved

The corrected route needs `P2` plus nonprimitivity to force `NoBranching`. The
argument: a branch — an `(L-1)`-mer with two distinct followers — is a
right-maximal repeat. Extending it backward to a left-maximal one and using the
periodicity of a nonprimitive word promotes it to a maximal **triple** repeat of
length `≥ L - 1`, which `P2` forbids. This section kernel-checks that argument.
-/

/-- From nonprimitivity (`PopulationReduction.IsPrimitive`), extract a period `p`
with `0 < p < G`: `cyc (t + p) = cyc t` for every `t`. The witness `H` satisfies
`H * q = G` with `q > 1`, so `H` is a genuine period below `G`. -/
theorem period_of_nonprimitive {G : ℕ} (hG : 0 < G) (S : Fin G → α)
    (hnp : ¬ IsPrimitive S) :
    ∃ p, 0 < p ∧ p < G ∧ ∀ t : ℕ, cyc hG S t = cyc hG S (t + p) := by
  rcases (by
    by_contra hcon
    exact hnp hcon :
    ∃ (H : ℕ) (hH : 0 < H) (U : Fin H → α) (q : ℕ),
      1 < q ∧ H * q = G ∧ ∀ i : Fin G, S i = U ⟨i.val % H, Nat.mod_lt _ hH⟩)
    with ⟨H, hH, U, q, hq1, hlen, hrep⟩
  have hHG : H ∣ G := ⟨q, hlen.symm⟩
  refine ⟨H, hH, ?_, ?_⟩
  · by_contra hcon
    have hHG2 : G ≤ H := by omega
    have hq2 : 2 ≤ q := by omega
    have h1 : 2 * G ≤ H * q := by nlinarith
    have h2 : H * q = G := hlen
    nlinarith
  · intro t
    have e1 : (t + H) % G % H = (t + H) % H := Nat.mod_mod_of_dvd (t + H) hHG
    have e2 : (t + H) % H = t % H := by
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
    have e3 : t % G % H = t % H := Nat.mod_mod_of_dvd t hHG
    have hS1 : S ⟨(t + H) % G, Nat.mod_lt (t + H) hG⟩
        = U ⟨(t + H) % H, Nat.mod_lt _ hH⟩ :=
      (hrep ⟨(t + H) % G, Nat.mod_lt (t + H) hG⟩).trans (congrArg U (Fin.ext e1))
    have hS2 : U ⟨t % H, Nat.mod_lt _ hH⟩
        = S ⟨t % G, Nat.mod_lt t hG⟩ :=
      (congrArg U (Fin.ext e3.symm)).trans (hrep ⟨t % G, Nat.mod_lt t hG⟩).symm
    have hcyc1 : cyc hG S (t + H) = S ⟨(t + H) % G, Nat.mod_lt (t + H) hG⟩ := rfl
    have hcyc2 : S ⟨t % G, Nat.mod_lt t hG⟩ = cyc hG S t := rfl
    exact (hcyc1.trans (hS1.trans ((congrArg U (Fin.ext e2)).trans (hS2.trans hcyc2)))).symm

end

end AssemblyP1.SameLength62Nonprimitive
