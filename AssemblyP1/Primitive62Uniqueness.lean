import AssemblyP1.SameLength62Maximizer
import AssemblyP1.OrientedFinalRigidity
import AssemblyP1.CycleSpellingRotation
import AssemblyP1.BridgingBridge

/-!
# #246: primitive §6.2 candidate uniqueness **without** the truth certificate is false

This module settles, negatively and in the kernel, the uniqueness reading of the
oriented same-length Medvedev–Brudno §6.2 question for **primitive** truths when
the truth is **not** assumed to be a genuine §6.2 candidate.

## The claim considered

`AssemblyP1.SameLength62Uniqueness.unique_62_maximizer_up_to_rotation` (#211,
the conditional theorem of PR #124) concludes that every genuine same-length
§6.2 candidate `D` is a cyclic shift of the truth `S`, under full source-faithful
`I_s` at the realized start set — but it additionally assumes `hStruth`, a
genuine §6.2 certificate for the **truth** itself. The #211 file is explicit that
`hStruth` is a nontrivial extra hypothesis: it asserts that the truth has
complete observed support.

Board #246 asks whether that extra hypothesis can be dropped when `S` is
**primitive**. The precise claim is `NoHStruthPrimitive62Uniqueness` below: for a
primitive truth `S`, with full source-faithful `I_s` at exactly the realized
start set, with the §6.2 vertex list `verts` equal to the actually observed
oriented read types, and with a same-length genuine §6.2 candidate `D`, is `D`
necessarily a cyclic shift of `S`?

## The answer: no

`noHStruthPrimitive62Uniqueness_refuted` proves the claim false. The witness is
the smallest instance, already present as a **negative** result in
`AssemblyP1.SameLengthExactMLCounterexample` for the maximizer reading:

* `S = AABB` (`0011`), `G = 4`, `L = 2`; the truth is primitive (no nonzero
  shift below `4` fixes it);
* the realization `ρ = ![1, 3]` places two reads at starts `1` and `3`, returning
  the oriented `2`-mers `AB` (`01`) and `BA` (`10`);
* `InformationFeasible ⟨4, hG, S⟩ 2 (realizedStarts ρ)` holds at full strength
  (`realizedStarts ρ = {1, 3}`), decided by computation;
* `verts = [AB, BA]` is exactly the observed read-type set;
* `D = ABAB` (`0101`) is a genuine same-length §6.2 candidate
  (`Is62Candidate62`), and `ABAB` is **not** a cyclic shift of `AABB`.

The §6.2 certificate is the one already kernel-checked in
`SameLengthExactMLCounterexample.competitor_spelledFeasible62`; the only new
content here is that its walk flow is the spelling's own flow
(`walkFlow = competitorSpelling.flow idRep 2`) and that it genuinely represents
`D = ABAB`, which together upgrade `SpelledFeasible62` to `Is62Candidate62`.

## Why `hStruth` is exactly the difference, and why primitivity does not help

`SameLength62Maximizer.genuine62_support_eq` says a genuine §6.2 candidate's
window support equals the **observed** read-type set, not the truth's window
support. Here the observed set is `{AB, BA}`, while the truth's own window
support is the strictly larger `{AA, AB, BB, BA}`. Two of the truth's windows
(`AA`, `BB`) were never observed, which is precisely the failure of `hStruth`
(`S_not_genuine` below). A word of length `4` whose windows are exactly
`{AB, BA}` need not be a rotation of `AABB`; `ABAB` is one such word, and it is a
closed walk in the observed read-overlap graph (`AB ⇄ BA`) because that graph
has no vertex for the unobserved `AA` or `BB`.

Primitivity is irrelevant to this obstruction: it constrains the truth's
period structure, but the candidate only has to be spelled by the **observed**
reads. Indeed `AABB` is not a simple cycle at `L = 2` (the node `A` has two
outgoing read types `AA` and `AB`), so the #243 support-rotation lemma
`isCyclicShift_of_isSimpleCycle_support_subset` does not apply either.

## The high-leverage positive route is also refuted here

A natural attempt to remove `hStruth` is to prove, from `I_s`, actual read
provenance and the existence of one genuine same-length candidate, that the
observed `L`-mer support equals the truth's full support, or at least that the
candidate's spectrum equals the truth's (after which the #211/#94 rigidity route
gives rotation with no truth certificate). Both intermediate claims are false at
this instance, and are refuted explicitly:

* `observed_support_ne_truth_support` — `{AB, BA} ≠ {AA, AB, BB, BA}`;
* `specCount_D_ne_S` — `d_D(AA) = 0 ≠ 1 = d_S(AA)`.

So no such support/spectrum-forcing lemma exists under these hypotheses.

## Candidate existence versus non-uniqueness

The refutation is **not** an existence failure and is **not** vacuous. The
genuine same-length §6.2 candidate class at this instance is non-empty:
`genuine_candidate_exists_not_rotation` exhibits `ABAB` in it. The failure is
genuine non-uniqueness of actual candidates. (A separate, vacuous situation is
also recorded in the repository, e.g. sparse witnesses where `hStruth` fails and
no candidate exists; that is a different phenomenon and is not what refutes the
claim here.)

## Source fidelity and objective separation

* The §6.2 object is the literal bidirected-flow feasible set of
  Medvedev–Brudno, *Maximum Likelihood Genome Assembly*, J. Comput. Biol. 16(8)
  (2009) 1101–1116, §6.2 (`AssemblyP1.Section62Flow`), with vertices = the
  observed reads, vertex lower bound `1`, and a closed circuit. See
  `docs/section62-mb09-bidirected-graph-audit.md` and
  `docs/source-notes/medvedev-brudno-candidate-class.md`.
* The published question of Shomorony et al. (2016) concerns the
  maximum-likelihood sequence; this module makes **no** claim about likelihood
  values. The ML objective is deliberately kept separate from §6.2
  admissibility: the refutation uses only admissibility (`Is62Candidate62`) plus
  non-rotation. (The same instance also happens to beat the truth in the exact
  objective, recorded separately in `SameLengthExactMLCounterexample`, but that
  is not needed here.)
* The conclusion is conditional on the same unresolved source choices the rest of
  the repository keeps explicit; no new axiom, `sorry`, or definition change is
  introduced.

## Obstacles recorded

* `hStruth` is not derivable from `I_s` at the realized starts: `I_s` clause 1 is
  *position* coverage, which does not force every length-`L` window of the truth
  to have been observed (`S_not_genuine`).
* The #243 rotation lemma needs `IsSimpleCycle S`, which primitivity does not
  provide.
* The Bresler–Bresler–Tse complete-spectrum input is not formalized, so the
  `of_bbt` uniqueness surface remains conditional.
-/

namespace AssemblyP1.Primitive62Uniqueness

open AssemblyP1.OrientedSameLengthML
open AssemblyP1.SameLength62Maximizer
open AssemblyP1.SameLengthExactMLCounterexample
open AssemblyP1.Section62Flow
open AssemblyP1.SourceFaithfulIs
open AssemblyP1.OrientedRigidity
open AssemblyP1.OrientedFinal
open Finset

set_option maxHeartbeats 800000

noncomputable section

/-- `Base` carries the two symbols of the `AABB`/`ABAB` witness. It inherits
`DecidableEq` from the #88 module; `Fintype` is supplied locally because the #88
witness module deliberately derives only the instances it needs. -/
instance : Fintype Base where
  elems := {Base.A, Base.B}
  complete := by intro x; cases x <;> simp

/-- The genome length of the witness. -/
theorem hG4 : (0 : ℕ) < 4 := by norm_num

/-- The truth `AABB` (`0011`) as a bare length-`4` circular word. -/
def S : Fin 4 → Base := truthGenome.sym

/-- The competitor `ABAB` (`0101`) as a bare length-`4` circular word. -/
def D : Fin 4 → Base := competitorGenome.sym

/-- The realized read starts: one read at start `1`, one at start `3`. -/
def rho : Realization 4 2 := ![1, 3]

/-- The unobserved truth window `AA` (`00`), used to witness `hStruth`'s failure
and the support mismatch. -/
def observedAA : Fin 2 → Base := ![Base.A, Base.A]

/-! ## The hypotheses of the claim hold at the witness -/

/-- The realized start set is exactly the two read starts `{1, 3}`. -/
theorem realizedStarts_rho : realizedStarts rho = readStarts := by decide

/-- Full source-faithful `I_s` at the *actual* realized start set. -/
theorem infoFeasible_realizedStarts :
    InformationFeasible ⟨4, hG4, S⟩ 2 (realizedStarts rho) := by
  rw [realizedStarts_rho]
  exact truth_information_feasible

/-- The truth is primitive: no nonzero shift below `4` fixes `AABB`. -/
theorem S_primitive : RepeatAdapter.IsPrimitive hG4 S := by
  intro s hs hlt hshift
  have hcases : s = 1 ∨ s = 2 ∨ s = 3 := by omega
  rcases hcases with h | h | h
  · subst h; exact absurd (hshift 1) (by decide)
  · subst h; exact absurd (hshift 0) (by decide)
  · subst h; exact absurd (hshift 0) (by decide)

/-- The read at start `1` is `AB`; it is observed with multiplicity `1`. -/
theorem observedOf_observedAB : observedOf hG4 S rho observedAB = 1 := by decide

/-- The read at start `3` is `BA`; it is observed with multiplicity `1`. -/
theorem observedOf_observedBA : observedOf hG4 S rho observedBA = 1 := by decide

/-- **The §6.2 vertex list is exactly the actually observed read-type set.** -/
theorem verts_correspondence :
    ObservedTypes observedVerts
      = (Finset.univ.filter (fun w : Fin 2 → Base => 0 < observedOf hG4 S rho w)) := by
  decide

/-- The weaker one-sided form of the correspondence used by
`SameLength62Maximizer.informationFeasible_62_maximizer`: every observed read type
is a vertex. -/
theorem hwx : ∀ w : Fin 2 → Base, 0 < observedOf hG4 S rho w → w ∈ observedVerts := by
  intro w hw
  have hmem : w ∈ (Finset.univ.filter
      (fun w : Fin 2 → Base => 0 < observedOf hG4 S rho w) : Finset (Fin 2 → Base)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  rw [← verts_correspondence] at hmem
  exact hmem

/-! ## The competitor is a genuine §6.2 candidate -/

/-- The §6.2 flow of the `ABAB` walk is the spelling's own walk flow. This is the
extra clause `f = sp.flow rep L` of `Is62Candidate62`, discharged by finite case
analysis on the two step types. -/
theorem walkFlow_eq_flow : walkFlow = competitorSpelling.flow idRep 2 := by
  funext e
  by_cases he1 : e = Section62Flow.bdEdge idRep observedAB observedBA 1
  · subst he1; decide
  · by_cases he2 : e = Section62Flow.bdEdge idRep observedBA observedAB 1
    · subst he2; decide
    · have hsteps : ∀ i : Fin 4, competitorSpelling.step idRep 2 i
          = Section62Flow.bdEdge idRep observedAB observedBA 1 ∨
          competitorSpelling.step idRep 2 i
          = Section62Flow.bdEdge idRep observedBA observedAB 1 := by
        intro i
        fin_cases i
        · left; rfl
        · right; rfl
        · left; rfl
        · right; rfl
      have hne : ∀ i : Fin 4, competitorSpelling.step idRep 2 i ≠ e := by
        intro i
        rcases hsteps i with h | h
        · exact fun heq => he1 (heq.symm.trans h)
        · exact fun heq => he2 (heq.symm.trans h)
      have hnil : (List.finRange 4).filter
          (fun i => decide (competitorSpelling.step idRep 2 i = e)) = [] := by
        refine List.filter_eq_nil_iff.mpr fun i _ => ?_
        intro hdec
        exact hne i (of_decide_eq_true hdec)
      show (if e = Section62Flow.bdEdge idRep observedAB observedBA 1 then 2
          else if e = Section62Flow.bdEdge idRep observedBA observedAB 1 then 2 else 0)
          = Section62Flow.Spelling.flow idRep 2 competitorSpelling e
      rw [ite_eq_right he1, ite_eq_right he2]
      simp only [Section62Flow.Spelling.flow, hnil, List.length_nil]

/-- **`ABAB` is a genuine same-length §6.2 candidate** for the observed read set:
a representing spelling (`Represents62`), the walk's own flow, and the literal
`SpelledFeasible62` certificate of the #88 module. -/
theorem D_is_genuine :
    Is62Candidate62 ⟨4, hG4, D⟩ observedVerts strandToList idRep idRc 1 := by
  refine ⟨4, competitorSpelling, walkFlow, Section62Flow.noTerminals W,
    candidateThroughput, ?_, ?_, competitor_spelledFeasible62⟩
  · refine ⟨rfl, ?_⟩
    intro i r hir
    fin_cases i <;> fin_cases r <;> simp_all [competitorSpelling, D] <;> decide
  · rw [walkFlow_eq_flow]

/-- **`ABAB` is not a cyclic shift of `AABB`.** -/
theorem D_not_rotation : ¬ IsCyclicShift hG4 D S := by
  rintro ⟨s, hs⟩
  have hmod : ∀ i : ℕ, OrientedRigidity.cyc hG4 S (i + s)
      = OrientedRigidity.cyc hG4 S (i + s % 4) := by
    intro i
    apply congrArg S
    apply Fin.ext
    show (i + s) % 4 = (i + s % 4) % 4
    omega
  have hs' : ∀ i : ℕ, OrientedRigidity.cyc hG4 D i
      = OrientedRigidity.cyc hG4 S (i + s % 4) := by
    intro i; rw [← hmod i]; exact hs i
  have hcases : s % 4 = 0 ∨ s % 4 = 1 ∨ s % 4 = 2 ∨ s % 4 = 3 := by omega
  rcases hcases with h | h | h | h
  · rw [h] at hs'; exact absurd (hs' 1) (by decide)
  · rw [h] at hs'; exact absurd (hs' 2) (by decide)
  · rw [h] at hs'; exact absurd (hs' 0) (by decide)
  · rw [h] at hs'; exact absurd (hs' 0) (by decide)

/-! ## The positive route through support/spectrum equality is refuted -/

/-- The observed read-type set is strictly smaller than the truth's window
support: `AA` is a window of `AABB` that was never observed. -/
theorem observed_support_ne_truth_support :
    ObservedTypes observedVerts ≠ (OrientedRigidity.support (L := 2) hG4 S : Finset (Fin 2 → Base)) := by
  intro h
  have hmem : observedAA ∈ (OrientedRigidity.support (L := 2) hG4 S : Finset (Fin 2 → Base)) := by
    decide
  rw [← h] at hmem
  exact absurd hmem (by decide)

/-- The candidate's spectrum differs from the truth's: `d_D(AA) = 0` while
`d_S(AA) = 1`. -/
theorem specCount_D_ne_S :
    ∃ w : Fin 2 → Base,
      OrientedRigidity.specCount (L := 2) hG4 D w
        ≠ OrientedRigidity.specCount (L := 2) hG4 S w :=
  ⟨observedAA, by decide⟩

/-! ## The truth is *not* a genuine §6.2 candidate (`hStruth` fails) -/

/-- **`hStruth` fails at the witness.** If the truth `AABB` were a genuine §6.2
candidate, `genuine62_support_eq` would force every one of its windows into the
observed set; but `AA` is a window of the truth and not an observed read. -/
theorem S_not_genuine :
    ¬ Is62Candidate62 ⟨4, hG4, S⟩ observedVerts strandToList idRep idRc 1 := by
  intro hS
  have hmem : observedAA ∈ ObservedTypes observedVerts :=
    (genuine62_support_eq (L := 2) (toList := strandToList) hS observedAA).mp
      ⟨⟨0, by norm_num⟩, by decide⟩
  exact absurd hmem (by decide)

/-! ## Candidate existence versus uniqueness -/

/-- **The genuine candidate class is non-empty and already non-unique.** There
is a same-length genuine §6.2 candidate (`ABAB`) that is not a rotation of the
truth. So the failure below is genuine non-uniqueness of actual candidates, not
an existence failure. -/
theorem genuine_candidate_exists_not_rotation :
    ∃ D : Fin 4 → Base,
      Is62Candidate62 ⟨4, hG4, D⟩ observedVerts strandToList idRep idRc 1 ∧
        ¬ IsCyclicShift hG4 D S :=
  ⟨D, D_is_genuine, D_not_rotation⟩

/-! ## The main refutation -/

/-- **The no-`hStruth` primitive uniqueness claim**, stated as a proposition:
for every primitive length-`4` truth `S`, every realization `ρ`, and every §6.2
vertex list `verts` that is exactly the observed oriented read-type set, any
same-length genuine §6.2 candidate `D` is a cyclic shift of `S`.

The exact-equality correspondence is the strongest reading; it implies the
one-sided `hwx` reading of
`SameLength62Maximizer.informationFeasible_62_maximizer`, so refuting this form
also refutes the weaker-hypothesis form. -/
def NoHStruthPrimitive62Uniqueness : Prop :=
  ∀ (S D : Fin 4 → Base) (ρ : Realization 4 2) (verts : List (Fin 2 → Base)),
    RepeatAdapter.IsPrimitive hG4 S →
    InformationFeasible ⟨4, hG4, S⟩ 2 (realizedStarts ρ) →
    ObservedTypes verts
      = (Finset.univ.filter (fun w : Fin 2 → Base => 0 < observedOf hG4 S ρ w)) →
    Is62Candidate62 ⟨4, hG4, D⟩ verts strandToList idRep idRc 1 →
    IsCyclicShift hG4 D S

/-- **Board #246, settled negatively.** The primitive source-faithful same-length
§6.2 uniqueness claim without `hStruth` is false. The witness is `AABB`/`ABAB`
with the realization at starts `{1, 3}`: `S` is primitive, `I_s` holds at exactly
`realizedStarts ρ`, `verts = [AB, BA]` is exactly the observed read set, `ABAB`
is a genuine same-length §6.2 candidate, and it is not a rotation of `AABB`. -/
theorem noHStruthPrimitive62Uniqueness_refuted : ¬ NoHStruthPrimitive62Uniqueness := by
  intro h
  exact D_not_rotation
    (h S D rho observedVerts S_primitive infoFeasible_realizedStarts
      verts_correspondence D_is_genuine)

#print axioms infoFeasible_realizedStarts
#print axioms S_primitive
#print axioms D_is_genuine
#print axioms D_not_rotation
#print axioms observed_support_ne_truth_support
#print axioms specCount_D_ne_S
#print axioms S_not_genuine
#print axioms genuine_candidate_exists_not_rotation
#print axioms noHStruthPrimitive62Uniqueness_refuted

end

end AssemblyP1.Primitive62Uniqueness
