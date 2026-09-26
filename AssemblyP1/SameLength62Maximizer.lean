import AssemblyP1.OrientedSameLengthML
import AssemblyP1.SameLengthExactMLCounterexample

/-!
# The repaired #88 theorem: the truth maximises over genuine §6.2 candidates

This module is the *repaired* positive result for issue #88. It is the
counterpart of `AssemblyP1.SameLengthExactMLCounterexample`: where that module
refutes the **unrestricted** same-length claim, this module proves the same-length
claim restricted to the candidate class that the **literal** §6.2 construction
of `AssemblyP1.Section62Flow` actually admits.

## What the audit found, and what this module does about it

`AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`
exhibits a same-length competitor `ABAB` satisfying the literal predicate
`Section62Flow.SpelledFeasible62` that beats the truth `AABB` (`1/4` against
`1/16`). That part is kernel-checked and correct, and it is retained unchanged as
a separate negative theorem.

The same module also records (`truth_not_spelled_on_observed`) that the truth's
length-`2` windows `AA` and `BB` were never observed, so **the truth is not
itself a §6.2 candidate**. An independent audit confirmed this in Lean: the
truth's own window walk `AA → AB → BB → BA` fails `VisitsObserved` at `AA`, so
no `SpelledFeasible62` certificate can represent the truth at
`observedVerts = [AB, BA]`.

That asymmetry has a precise consequence, and this module is built around it:

* The claim the `AABB`/`ABAB` instance actually refutes is the **dominance**
  claim — "every same-length §6.2-feasible candidate has likelihood at most the
  truth's". It is genuinely refuted: `ABAB` is such a candidate.
* The claim it does **not** refute is the **maximizer** claim *with
  membership* — "the truth is itself a §6.2 candidate, and maximises". Its
  membership antecedent is false at that instance, so the instance says nothing
  about it. The predicate `Is62MaximumLikelihood` used by the refutation module
  has no membership conjunct; the commit message advertising it as a maximizer
  statement was an overclaim, corrected in the notes.

This module therefore does three separable things.

## 1. A *genuine* representing certificate

`SpelledFeasible62` certifies an abstract object: a cyclic word of strands
`sp : Spelling A W n`, a flow, terminals and a throughput vector. It does **not**
say that object is the window walk of any genome. The original refutation
supplied the correspondence by hand and never proved it, leaving "the graph
spelling corresponds to the claimed competitor" resting on prose. Here it is a
definition and a hypothesis:

* `Represents62 C n sp` — `n = C.len` and, at every cyclic read position, the
  strand is exactly `C`'s own length-`L` window there.
* `Is62Candidate62` — a *genuine* §6.2 candidate of `C`: a representing
  spelling, a literal `SpelledFeasible62` certificate, **and** the flow is the
  flow the walk itself carries (`f = sp.flow rep L`). The last clause is the
  natural reading of MB09 §6.2, in which the candidate's flow is the traversal
  multiset of its own circuit, and it is what makes the observed-read coverage
  clause bite (`genuine62_support_eq`).

## 2. The bridge: a genuine candidate has the observed window support

`genuine62_support_eq` is the load-bearing lemma and it is **proved**, not
assumed:

```
Is62Candidate62 C  ⟹  ∀ w, (∃ r, C.window L r = w) ↔ w ∈ ObservedTypes verts
```

in both directions.

* The forward direction is `VisitsObserved`, read through `Represents62`.
* The backward direction is the §6.2 vertex lower bound of `1`. This is where
  the literal construction does real work: every observed read must carry flow,
  so some walk step departs its molecule class, so the candidate spells it.
  `visited_of_positive_throughput` isolates this step, and it uses only a
  *lower* bound on throughput, so it is unaffected by the edge-list duplication
  of strict single-strand mode (`strandsOf rc verts = verts ++ verts.map rc`
  lists each class once per strand slot).

Consequently, **if the truth also has a genuine certificate, every genuine
same-length candidate has exactly the truth's window support** — exactly
`AssemblyP1.OrientedSameLengthML.IsSameLengthSpelledCandidate`, the hypothesis
the mature rigidity chain consumes. So the §6.2 restriction is not a *different*
candidate class from the one the chain is about; it is the same class read off
the literal §6.2 model. That is the bridge, and it is the substantive content
of this module.

## 3. The maximizer theorem, with the residual regime isolated

`informationFeasible_62_maximizer` concludes the same-length likelihood
inequality from **full source-faithful** `InformationFeasible`, the truth's own
genuine certificate, and one further hypothesis, which is named in the statement
and is **not** opaque:

* `¬ RepeatAdapter.HasLongTripleRepeat hG S L` — the truth carries no Bresler
  triple repeat of length `≥ L - 1`. This is the long-standing interface
  hypothesis of `AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`
  and the exact premise consumed by
  `AssemblyP1.BridgingBridge.informationFeasible_sharp_no_long_triple_repeat`.

It is an explicit premise and is **not** claimed to follow from `InformationFeasible`
plus the truth's certificate. It does not, and that is provable rather than
merely suspected: the genome `AAAAB` of length `5` with read length `3`, read at
all five starts, satisfies full source-faithful `InformationFeasible`, has every
one of its length-`3` windows observed (so it is a §6.2 candidate in the sense of
`genuine62_support_eq`), and nonetheless carries a maximal triple repeat of
length `2 = L - 1`. The residual regime is therefore non-empty, which is exactly
why the premise is left visible here instead of being discharged. What this
module adds on top of
`AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer` is the
removal of the observation-level hypothesis: that theorem needs
`IsSameLengthSpelledCandidate` as a *premise*, whereas here it is **derived**
from the literal §6.2 model together with full `I_s`.

## Honest scope

This module does **not** settle the residual long-triple-repeat regime, and does
not claim that regime is empty. In the `AAAAB` instance the truth nonetheless
*is* a maximizer over every same-support length-`5` competitor, so the regime
contains no counterexample there; but no theorem is claimed about it.

An exhaustive search over binary truths with `G ≤ 8` and `L ≤ 5`, restricted to
genuine same-support candidates of truth-feasible `I_s` realizations, found **no**
candidate whose window multiplicity strictly exceeds the truth's on any observed
read type — the necessary condition for beating the truth in this class, since the
likelihood is `∏_w (d_C w / N)^{x w}`. That is evidence, not a completeness
proof, and is recorded as such.
-/

namespace AssemblyP1.SameLength62Maximizer

open SourceFaithfulIs

set_option maxHeartbeats 800000

noncomputable section

variable {α : Type} [DecidableEq α]

/-! ## 1. A genuine §6.2 candidate -/

/-- **A §6.2 spelling genuinely represents the genome `C`.** The spelling has
exactly `C.len` cyclic read positions, and at each of them the strand is the
length-`L` window of `C` at that position.

This is the correspondence between the §6.2 circuit and a candidate genome that
the literal predicate `SpelledFeasible62` does not itself contain. -/
def Represents62 {L : ℕ} {n : ℕ} (C : Genome α)
    (sp : Section62Flow.Spelling α (Fin L → α) n) : Prop :=
  n = C.len ∧ ∀ (i : Fin n) (r : Fin C.len), i.val = r.val →
    sp.strand i = C.window L r

/-- The observed read molecules, as a `Finset` of read types: the vertex set of
the §6.2 overlap graph, read as the set of read types the realization produced. -/
def ObservedTypes {L : ℕ} (verts : List (Fin L → α)) : Finset (Fin L → α) :=
  verts.toFinset

/-- **A genuine §6.2 candidate of the genome `C`.** A `Spelling` of `C.len`
positions genuinely representing `C` (its strand at each position is `C`'s own
window there), carrying a literal `SpelledFeasible62` certificate whose flow is
the flow the walk itself carries.

The clause `f = sp.flow rep L` is the reading of MB09 §6.2 in which the
candidate's flow is the traversal multiset of its own circuit, and it is what
makes the vertex lower bound of `1` a statement about the walk. -/
def Is62Candidate62 {L : ℕ} (C : Genome α) (verts : List (Fin L → α))
    (toList : (Fin L → α) → List α) (rep rc : (Fin L → α) → (Fin L → α))
    (oMin : ℕ) : Prop :=
  ∃ (n : ℕ) (sp : Section62Flow.Spelling α (Fin L → α) n)
    (f : Section62Flow.BdFlow α (Fin L → α))
    (t : Section62Flow.SuperTerminals (Fin L → α)) (d : (Fin L → α) → ℕ),
    Represents62 C sp ∧
      f = sp.flow rep L ∧
      Section62Flow.SpelledFeasible62 α (Fin L → α) toList rep rc L oMin verts
        sp f t d

/-! ## 2. The bridge -/

/-- A vertex with positive throughput is visited by the walk.

Isolates the single step needed to read the §6.2 vertex lower bound `1` as a
statement about the circuit. Only a *lower* bound is used, so the proof is
unaffected by the edge-list duplication of strict single-strand mode. -/
theorem foldr_pos_witness {ι : Type} (P : ι → Prop)
    [inst : ∀ e : ι, Decidable (P e)] (f : ι → ℕ) (l : List ι)
    (hpos : 0 < List.foldr (fun e (acc : ℕ) => if P e then f e + acc else acc) 0 l) :
    ∃ e ∈ l, P e ∧ (0 : ℕ) < f e := by
  induction l generalizing f with
  | nil => simp at hpos
  | cons e l ih =>
      have hcons : (0 < if P e then f e + 0 else 0) ∨
          (0 < List.foldr (fun e (acc : ℕ) => if P e then f e + acc else acc) 0 l) := by
        simp only [List.foldr_cons] at hpos
        by_cases he : P e
        · by_cases hf : (0 : ℕ) < f e
          · left; simp [he, hf]
          · right; simpa [he, hf, Nat.zero_add] using hpos
        · right; simpa [he] using hpos
      rcases hcons with hleft | hright
      · by_cases he : P e
        · by_cases hf : (0 : ℕ) < f e
          · exact ⟨e, by simp, he, hf⟩
          · simp [he, hf] at hleft
        · simp [he] at hleft
      · obtain ⟨e', he', he'P, he'f⟩ := ih f hright
        exact ⟨e', by simp [he'], he'P, he'f⟩

theorem visited_of_positive_throughput {L : ℕ} {n : ℕ}
    (toList : (Fin L → α) → List α) (rep rc : (Fin L → α) → (Fin L → α))
    (oMin : ℕ) (verts : List (Fin L → α))
    (sp : Section62Flow.Spelling α (Fin L → α) n)
    (f : Section62Flow.BdFlow α (Fin L → α)) (v : Fin L → α)
    (hwf : f = sp.flow rep L)
    (hpos : 0 < Section62Flow.throughput α (Fin L → α) rep f
      (Section62Flow.overlapEdges α (Fin L → α) toList rep rc L oMin verts) v) :
    ∃ i : Fin n, rep (sp.strand i) = v := by
  classical
  have hfold : Section62Flow.throughput α (Fin L → α) rep f
      (Section62Flow.overlapEdges α (Fin L → α) toList rep rc L oMin verts) v
      = List.foldr (fun e (acc : ℕ) => if rep e.sx = v then f e + acc else acc) 0
          (Section62Flow.overlapEdges α (Fin L → α) toList rep rc L oMin verts) := rfl
  obtain ⟨e, he, hev, hfpos⟩ :=
    foldr_pos_witness (fun e : Section62Flow.BdEdge α (Fin L → α) => rep e.sx = v)
      f (Section62Flow.overlapEdges α (Fin L → α) toList rep rc L oMin verts)
      (by rw [← hfold]; exact hpos)
  have hne : (List.finRange n).filter (fun j => decide (sp.step rep L j = e)) ≠ [] := by
    have : 0 < ((List.finRange n).filter (fun j => decide (sp.step rep L j = e))).length := by
      show 0 < sp.flow rep L e
      rw [← hwf]; exact hfpos
    rwa [List.length_pos_iff] at this
  obtain ⟨i, hi⟩ : ∃ i, i ∈ (List.finRange n).filter (fun j => decide (sp.step rep L j = e)) :=
    List.exists_mem_of_ne_nil _ hne
  have hidec : decide (sp.step rep L i = e) = true := (List.mem_filter.mp hi).2
  refine ⟨i, ?_⟩
  have hx : (sp.step rep L i).sx = sp.strand i := rfl
  rw [of_decide_eq_true hidec] at hx
  exact (hev.symm.trans (congrArg rep hx)).symm

/-- **The §6.2 molecule-class spectrum of a genuine candidate is the observed
one.** Rephrasing `genuine62_support_eq` for a general molecule-class map `rep`:
the multiset of molecule classes the candidate's read windows fall into is
exactly the observed read set, and every observed read is realised by some read
position of the candidate.

This is what the literal §6.2 model actually talks about — its vertices are
molecule classes, not oriented words. In the *oriented* single-strand reading
used throughout this repository (`rep = id`, no reverse-complement collapse)
the two coincide, and `genuine62_support_eq` below records that. -/
theorem genuine62_molecule_eq {L : ℕ} {C : Genome α} {verts : List (Fin L → α)}
    {toList : (Fin L → α) → List α} {rep rc : (Fin L → α) → (Fin L → α)}
    {oMin : ℕ} (hC : Is62Candidate62 C verts toList rep rc oMin) :
    ∀ w : Fin L → α,
      (∃ r : Fin C.len, rep (C.window L r) = w) ↔ w ∈ verts := by
  classical
  obtain ⟨n, sp, f, t, d, hrep, hflow, hfeas⟩ := hC
  have hn : n = C.len := hrep.1
  have hvis : ∀ i : Fin n, rep (sp.strand i) ∈ verts := hfeas.1
  have hlb : ∀ v ∈ verts, 1 ≤ Section62Flow.throughput α (Fin L → α) rep f
      (Section62Flow.overlapEdges α (Fin L → α) toList rep rc L oMin verts) v :=
    hfeas.2.2.2.2.1.2.1
  have key : ∀ (w : Fin L → α) (r : Fin C.len), rep (C.window L r) ∈ verts := by
    intro w r
    have hvis' : rep (sp.strand (Fin.cast hn.symm r)) ∈ verts :=
      hvis (Fin.cast hn.symm r)
    have hst : sp.strand (Fin.cast hn.symm r) = C.window L r :=
      hrep.2 (Fin.cast hn.symm r) r rfl
    rwa [hst] at hvis'
  intro w
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact key w r
  · intro hw
    obtain ⟨i, hi⟩ := visited_of_positive_throughput toList rep rc oMin verts sp f w
      hflow (lt_of_lt_of_le (by omega) (hlb w hw))
    have hstr : rep (sp.strand i) = w := hi
    have hwin : sp.strand i = C.window L (Fin.cast hn i) := hrep.2 i _ rfl
    exact ⟨Fin.cast hn i, (congrArg rep hwin).symm.trans hstr⟩

/-- **In the oriented single-strand reading the molecule classes *are* the
oriented words**, so `genuine62_molecule_eq` is the ordinary oriented
window-support statement. This is the form consumed by
`AssemblyP1.OrientedSameLengthML.IsSameLengthSpelledCandidate` and by the
rigidity chain, and it is what makes the §6.2 restriction *equal* to the
spelled-candidate class rather than an approximation of it. -/
theorem genuine62_support_eq {L : ℕ} {C : Genome α} {verts : List (Fin L → α)}
    {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hC : Is62Candidate62 C verts toList (fun y => y) (fun y => y) oMin) :
    ∀ w : Fin L → α,
      (∃ r : Fin C.len, C.window L r = w) ↔ w ∈ ObservedTypes verts := by
  intro w
  constructor
  · rintro ⟨r, hr⟩
    exact List.mem_toFinset.mpr ((genuine62_molecule_eq hC w).mp ⟨r, hr⟩)
  · intro hw
    obtain ⟨r, hr⟩ := (genuine62_molecule_eq hC w).mpr (List.mem_toFinset.mp hw)
    exact ⟨r, hr⟩

/-- A genuine §6.2 candidate's **molecule-class** support, as a `Finset` of
read types: the set of molecule classes its read windows fall into is exactly
the observed read set. -/
theorem moleculeClasses_eq_observedTypes {L : ℕ} {C : Genome α}
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α}
    {rep rc : (Fin L → α) → (Fin L → α)} {oMin : ℕ}
    (hC : Is62Candidate62 C verts toList rep rc oMin) :
    (Finset.univ.image (fun r : Fin C.len => rep (C.window L r)) : Finset (Fin L → α))
      = ObservedTypes verts := by
  classical
  ext w
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨r, _, hr⟩
    exact List.mem_toFinset.mpr ((genuine62_molecule_eq hC w).mp ⟨r, hr⟩)
  · intro hw
    obtain ⟨r, hr⟩ := (genuine62_molecule_eq hC w).mpr (List.mem_toFinset.mp hw)
    exact ⟨r, Finset.mem_univ _, hr⟩

/-- A genuine §6.2 candidate's oriented window support, as an `OrientedRigidity`
support `Finset`, in the oriented single-strand reading. -/
theorem support62_eq_observedTypes {L : ℕ} {C : Genome α}
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hC : Is62Candidate62 C verts toList (fun y => y) (fun y => y) oMin) :
    (Finset.univ.image (fun r : Fin C.len => C.window L r) : Finset (Fin L → α))
      = ObservedTypes verts := by
  classical
  ext w
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨r, _, hr⟩
    exact (genuine62_support_eq (L := L) (toList := toList) hC w).mp ⟨r, hr⟩
  · intro hw
    obtain ⟨r, hr⟩ := (genuine62_support_eq (L := L) (toList := toList) hC w).mpr hw
    exact ⟨r, Finset.mem_univ _, hr⟩

/-- Two genomes of the same length, each a genuine §6.2 candidate for the same
observed read set, have the **same** length-`L` window support. This is the
quantitative form of the bridge, and it is the exact statement the mature
rigidity chain needs. -/
theorem support62_eq_of_genuine62 {L : ℕ} {C D : Genome α}
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hC : Is62Candidate62 C verts toList (fun y => y) (fun y => y) oMin)
    (hD : Is62Candidate62 D verts toList (fun y => y) (fun y => y) oMin)
    (hlen : D.len = C.len) :
    (Finset.univ.image (fun r : Fin D.len => D.window L r) : Finset (Fin L → α))
      = Finset.univ.image (fun r : Fin C.len => C.window L r) := by
  rw [support62_eq_observedTypes (L := L) (toList := toList) hD,
    support62_eq_observedTypes (L := L) (toList := toList) hC]

/-! ## 3. Transport to the `Fin G → α` rigidity chain -/

/-- `Genome.window` and `OrientedRigidity.window` agree at the genome's own
length. This is the identification that lets the `Genome`-level §6.2 layer and
the `Fin G → α`-level rigidity chain be composed. -/
theorem window_eq_oriented {C : Genome α} (L : ℕ) (r : Fin C.len) :
    C.window L r = OrientedRigidity.window (L := L) C.len_pos C.sym r := rfl

theorem support_eq_oriented {C : Genome α} (L : ℕ) :
    (Finset.univ.image (fun r : Fin C.len => C.window L r) : Finset (Fin L → α))
      = OrientedRigidity.support C.len_pos C.sym := rfl

/-- The occurrence multiplicity `d_C w` of a read type, in the two
vocabularies. -/
theorem winCount_eq_specCount {C : Genome α} (L : ℕ) (w : Fin L → α) :
    SameLengthExactMLCounterexample.winCount C L w
      = OrientedRigidity.specCount (L := L) C.len_pos C.sym w := rfl

/-- Two same-length genomes with a genuine §6.2 certificate apiece have equal
oriented window supports, i.e. `support D = support S` in the `Fin G → α`
vocabulary that the rigidity chain speaks. -/
theorem oriented_support_eq_of_genuine62 {L : ℕ} {C D : Genome α}
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hC : Is62Candidate62 C verts toList (fun y => y) (fun y => y) oMin)
    (hD : Is62Candidate62 D verts toList (fun y => y) (fun y => y) oMin)
    (hlen : D.len = C.len) :
    OrientedRigidity.support (L := L) D.len_pos D.sym
      = OrientedRigidity.support (L := L) C.len_pos C.sym := by
  have h := support62_eq_of_genuine62 (L := L) (toList := toList) hC hD hlen
  unfold OrientedRigidity.support
  exact h


open SourceFaithfulIs


/-! ## 4. The maximizer theorem -/

/-! ## 4. The maximizer theorem -/

/-- **A genuine same-length §6.2 candidate is a strict same-length spelled
candidate of the truth.**

This is the composition of the §6.2 bridge with the observation layer, and it
is stated in exactly the form
`AssemblyP1.OrientedSameLengthML.IsSameLengthSpelledCandidate` demands: equal
oriented window supports, plus every observed read type spelled by the
candidate. The second conjunct is the vertex-lower-bound half of the bridge.

Consequently the §6.2 candidate restriction is not a *different* class from the
one the mature rigidity chain consumes — it is the same class, read off the
literal §6.2 flow model. The genomes are given at a common length `G` because
that is the vocabulary of the chain; `hlen` records that both carry it. -/
theorem genuine62_is_spelled_candidate {α : Type} [DecidableEq α] [Fintype α]
    {L : ℕ} {G : ℕ} (hG : 0 < G)
    (S D : Fin G → α)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (x : OrientedSameLengthML.ObservedReads α L)
    (hS : Is62Candidate62 ⟨G, hG, S⟩ verts toList (fun y => y) (fun y => y) oMin)
    (hD : Is62Candidate62 ⟨G, hG, D⟩ verts toList (fun y => y) (fun y => y) oMin)
    (hwx : ∀ w : Fin L → α, 0 < x w → w ∈ verts) :
    OrientedSameLengthML.IsSameLengthSpelledCandidate (L := L) hG S D x := by
  refine ⟨oriented_support_eq_of_genuine62 (L := L) (toList := toList) hS hD rfl, ?_⟩
  intro w hw
  have hwv : w ∈ verts := hwx w hw
  obtain ⟨r, hr⟩ :=
    (genuine62_support_eq (L := L) (toList := toList) hD w).mpr (List.mem_toFinset.mpr hwv)
  have hsc : w ∈ (OrientedRigidity.support (L := L) hG D : Finset (Fin L → α)) := by
    unfold OrientedRigidity.support
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hr⟩
  exact (OrientedSameLengthML.specCount_pos_iff hG D w).mpr hsc



/-- **The repaired #88 maximizer theorem.**

Let the truth `S` be a circular word of length `G` and let `R` be a set of
latent read starts carrying **full source-faithful** information feasibility at
read length `L`. Let `ρ` be a genuine realization of `n` reads on `S` whose
starts all lie in `R`, so the observation `x = observedOf hG S ρ` is the
realized read multiset. Suppose

* the truth is itself a genuine §6.2 candidate for the observed read set
  (`hStruth`), and
* every observed read type is among the observed reads (`hwx`, which a
  realization gives for free);

and let `D` be a **same-length genuine §6.2 candidate** for the same observed
read set. Then, provided the truth carries no Bresler triple repeat of length
`≥ L - 1` (`hno`), the exact same-length Medvedev–Brudno likelihood of `D` is at
most that of `S`.

The likelihood is `AssemblyP1.SameLengthExactMLCounterexample.sameLengthExactLik`
— the same objective the negative theorem
`AssemblyP1.SameLengthExactMLCounterexample.same_length_exact_ML_refutation_62`
refutes, so the two results are directly comparable.

What is *new* here relative to
`AssemblyP1.OrientedSameLengthML.informationFeasible_exactLik_maximizer` is that
`IsSameLengthSpelledCandidate` is **derived**, by
`genuine62_is_spelled_candidate`, from the literal §6.2 flow model together
with the trivial observation that realized read types are observed read types.
That theorem needed it as a premise; here it is a consequence.

**An audit finding, stated as a fact about this theorem's proof rather than as a
claim about it.** `_hfeas` and `_hR` are *not used*. Lean's linter reports this
and the names are underscore-prefixed so that it is visible. The reason is
structural: `genuine62_molecule_eq` derives the candidate class entirely from
the §6.2 certificate, using `VisitsObserved` and the vertex lower bound of `1`
(`visited_of_positive_throughput`). Neither the information-feasible predicate
nor the start set enters. So the honest reading of this theorem is:

* the §6.2 support-spelling restriction, read literally, is *by itself* enough
  to make the truth an exact maximum-likelihood same-length candidate over the
  §6.2-feasible class; and

* the residual hypothesis is only `¬ HasLongTripleRepeat`, the pre-existing
  interface boundary of the rigidity chain — **not** an `I_s`-derived
  conclusion.

This is stronger than "full `I_s` plus a certificate suffices", and it is worth
recording precisely because it relocates where the open difficulty lies: it is
not in transferring `I_s` into the §6.2 candidate class (that transfer is
automatic), and it is not in the coverage interpretation. It is entirely in the
long-triple-repeat regime of `AssemblyP1.BridgingBridge`.

`hno` is the long-standing interface hypothesis of
`AssemblyP1.OrientedFinal.oriented_same_length_spectrum_rigidity`. It is stated
explicitly and is *not* claimed to follow from `InformationFeasible`: it does
not, and `AssemblyP1.WraparoundTripleRepeat` kernel-checks a truth-feasible
full-`I_s` instance that carries such a triple repeat. See the module header
and `docs/same-length-62-maximizer.md`. -/
theorem informationFeasible_62_maximizer {α : Type} [DecidableEq α] [Fintype α]
    {G L n : ℕ} (hG : 0 < G) (hL2 : 2 ≤ L) (hLG : L ≤ G)
    (S D : Fin G → α) (ρ : OrientedSameLengthML.Realization G n)
    (R : Finset (Fin G))
    (_hR : ∀ i : Fin n, ρ i ∈ R)
    (_hfeas : SourceFaithfulIs.InformationFeasible ⟨G, hG, S⟩ L R)
    (hno : ¬ RepeatAdapter.HasLongTripleRepeat hG S L)
    {verts : List (Fin L → α)} {toList : (Fin L → α) → List α} {oMin : ℕ}
    (hwx : ∀ w : Fin L → α, 0 < OrientedSameLengthML.observedOf (L := L) hG S ρ w → w ∈ verts)
    (hStruth : Is62Candidate62 ⟨G, hG, S⟩ verts toList (fun y => y) (fun y => y) oMin)
    (hCand : Is62Candidate62 ⟨G, hG, D⟩ verts toList (fun y => y) (fun y => y) oMin) :
    OrientedSameLengthML.exactLik (L := L) hG D (OrientedSameLengthML.observedOf hG S ρ)
      ≤ OrientedSameLengthML.exactLik (L := L) hG S (OrientedSameLengthML.observedOf hG S ρ) := by
  have hD := OrientedSameLengthML.same_length_exactLik_maximizer hG S D hL2 hLG hno
    (OrientedSameLengthML.observedOf hG S ρ)
    (genuine62_is_spelled_candidate hG S D (OrientedSameLengthML.observedOf hG S ρ)
      hStruth hCand hwx)
  exact hD

end

end AssemblyP1.SameLength62Maximizer
