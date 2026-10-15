import Std

/-!
# Periodicity from a closed-walk seam

This combinatorial lemma separates the cyclic seam argument from the §6.2
bidirected graph and its RC orientation. A closed walk linearizes to a word X
of length L+G where the first L letters equal the last L letters. Then the
linearization agrees with its length-G prefix at every index modulo G.
This remains true for G<L: the seam forces repeated wraparound.

It does NOT construct a genome from an arbitrary graph flow or prove the
source Observation 7 occurrence/visit identity. Those require a graph-specific
signed-circuit seam and anchor/skipped-window proofs.
-/

namespace AssemblyP1.Section62PeriodicSeam

/-- A word X of length L+G whose initial and final L-windows agree
is periodic of period G over its entire domain. Valid for G<L. The explicit
default is never used for an in-bounds source index. -/
theorem seam_periodic {α : Type} {G L : Nat} (hG : 0 < G)
  (X : List α) (default : α) (hXlen : X.length = L + G)
  (hseam : X.take L = X.drop G) :
  ∀ i, i < X.length → X.getD i default = X.getD (i % G) default := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    by_cases hiG : i < G
    · simp [Nat.mod_eq_of_lt hiG]
    · have hg : G ≤ i := by omega
      have hig : i - G < i := by omega
      have hiRest : i - G < X.length := by omega
      have hlt : i - G < L := by omega
      have hseam_i : (X.take L).getD (i-G) default = (X.drop G).getD (i-G) default :=
        congrArg (fun xs : List α => xs.getD (i-G) default) hseam
      have h1 : (X.take L).getD (i-G) default = X.getD (i-G) default := by
        simp [List.getD, hlt]
      have h2 : (X.drop G).getD (i-G) default = X.getD (G+(i-G)) default := by
        simp [List.getD, List.getElem?_drop]
      have hiEq : G+(i-G) = i := by omega
      have hmove : X.getD i default = X.getD (i-G) default := by
        rw [h1, h2, hiEq] at hseam_i
        exact hseam_i.symm
      have hmod : (i-G)%G = i%G := by
        calc
          (i-G)%G = (G+(i-G))%G := by simp
          _ = i%G := by rw [hiEq]
      calc
        X.getD i default = X.getD (i-G) default := hmove
        _ = X.getD ((i-G)%G) default := ih (i-G) hig hiRest
        _ = X.getD (i%G) default := by rw [hmod]


/-- The aligned circular genome is the FIRST G letters of the linearization,
not generally its last G appended letters. Every linear position is its
corresponding modulo-G position in this prefix. -/
theorem seam_periodic_prefix {α : Type} {G L : Nat} (hG : 0 < G)
    (X : List α) (default : α) (hXlen : X.length = L + G)
    (hseam : X.take L = X.drop G) (i : Nat) (hi : i < X.length) :
    X.getD i default = (X.take G).getD (i % G) default := by
  have hmod : i % G < G := Nat.mod_lt _ hG
  have hpre : (X.take G).getD (i % G) default =
      X.getD (i % G) default := by
    simp [List.getD, hmod]
  exact (seam_periodic hG X default hXlen hseam i hi).trans hpre.symm

/-- The appended tail is a rotation of the aligned genome by L positions.
This shift must be accounted for when comparing first-read anchors. -/
theorem seam_tail_rotation {α : Type} {G L : Nat} (hG : 0 < G)
    (X : List α) (default : α) (hXlen : X.length = L + G)
    (hseam : X.take L = X.drop G) (j : Nat) (hj : j < G) :
    (X.drop L).getD j default =
      (X.take G).getD ((L + j) % G) default := by
  have hdrop : (X.drop L).getD j default = X.getD (L + j) default := by
    simp [List.getD, List.getElem?_drop]
  have hi : L + j < X.length := by omega
  exact hdrop.trans (seam_periodic_prefix hG X default hXlen hseam (L+j) hi)


#print axioms seam_periodic
#print axioms seam_periodic_prefix
#print axioms seam_tail_rotation

end AssemblyP1.Section62PeriodicSeam
