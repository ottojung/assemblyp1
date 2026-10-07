import Mathlib

namespace AssemblyP1.Issue94EvenPairing

def pairConsecutive : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: pairConsecutive rest
  | _ => []

def pairEndpoints : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (a, b) :: rest => a :: b :: pairEndpoints rest

theorem pairEndpoints_pairConsecutive_of_even :
    ∀ xs : List ℕ, xs.length % 2 = 0 →
      pairEndpoints (pairConsecutive xs) = xs
  | [] => by simp [pairConsecutive, pairEndpoints]
  | [x] => by
      intro h
      simp at h
  | a :: b :: rest => by
      intro h
      have hrest : rest.length % 2 = 0 := by
        simp only [List.length_cons] at h
        omega
      simp [pairConsecutive, pairEndpoints,
        pairEndpoints_pairConsecutive_of_even rest hrest]

theorem pairConsecutive_le :
    ∀ xs : List ℕ, xs.Pairwise (· ≤ ·) →
      ∀ p ∈ pairConsecutive xs, p.1 ≤ p.2
  | [] => by simp [pairConsecutive]
  | [x] => by simp [pairConsecutive]
  | a :: b :: rest => by
      intro hsorted p hp
      have hab : a ≤ b :=
        (List.pairwise_cons.mp hsorted).1 b (by simp)
      have hrest : rest.Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).2
      simp only [pairConsecutive, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hab
      · exact pairConsecutive_le rest hrest p hp

theorem fst_mem_pairEndpoints_of_mem {p : ℕ × ℕ} :
    ∀ {ps : List (ℕ × ℕ)}, p ∈ ps → p.1 ∈ pairEndpoints ps
  | [], h => by simp at h
  | (a, b) :: rest, h => by
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst p
        simp [pairEndpoints]
      · simp [pairEndpoints, fst_mem_pairEndpoints_of_mem h]

theorem snd_mem_pairEndpoints_of_mem {p : ℕ × ℕ} :
    ∀ {ps : List (ℕ × ℕ)}, p ∈ ps → p.2 ∈ pairEndpoints ps
  | [], h => by simp at h
  | (a, b) :: rest, h => by
      simp only [List.mem_cons] at h
      rcases h with h | h
      · subst p
        simp [pairEndpoints]
      · simp [pairEndpoints, snd_mem_pairEndpoints_of_mem h]


def coordinatePairs (B : Finset ℕ) : List (ℕ × ℕ) :=
  pairConsecutive (B.sort (· ≤ ·))

theorem coordinatePairs_endpoints_toFinset
    (B : Finset ℕ) (hEven : Even B.card) :
    (pairEndpoints (coordinatePairs B)).toFinset = B := by
  have hlen : (B.sort (· ≤ ·)).length % 2 = 0 := by
    rw [Finset.length_sort]
    exact Nat.even_iff.mp hEven
  have hlist :=
    pairEndpoints_pairConsecutive_of_even (B.sort (· ≤ ·)) hlen
  calc
    (pairEndpoints (coordinatePairs B)).toFinset
        = (B.sort (· ≤ ·)).toFinset := by
            exact congrArg List.toFinset hlist
    _ = B := Finset.sort_toFinset B (· ≤ ·)

theorem coordinatePairs_le
    (B : Finset ℕ) :
    ∀ p ∈ coordinatePairs B, p.1 ≤ p.2 := by
  exact pairConsecutive_le (B.sort (· ≤ ·))
    (Finset.pairwise_sort B (· ≤ ·))

theorem coordinatePairs_fst_mem
    (B : Finset ℕ) (hEven : Even B.card)
    {p : ℕ × ℕ} (hp : p ∈ coordinatePairs B) :
    p.1 ∈ B := by
  have hmem : p.1 ∈ (pairEndpoints (coordinatePairs B)).toFinset := by
    simp only [List.mem_toFinset]
    exact fst_mem_pairEndpoints_of_mem hp
  rw [coordinatePairs_endpoints_toFinset B hEven] at hmem
  exact hmem

theorem coordinatePairs_snd_mem
    (B : Finset ℕ) (hEven : Even B.card)
    {p : ℕ × ℕ} (hp : p ∈ coordinatePairs B) :
    p.2 ∈ B := by
  have hmem : p.2 ∈ (pairEndpoints (coordinatePairs B)).toFinset := by
    simp only [List.mem_toFinset]
    exact snd_mem_pairEndpoints_of_mem hp
  rw [coordinatePairs_endpoints_toFinset B hEven] at hmem
  exact hmem

theorem coordinatePair_interval_valid
    (B : Finset ℕ) (hEven : Even B.card)
    {p : ℕ × ℕ} (hp : p ∈ coordinatePairs B)
    {tailBound M : ℕ}
    (hvalid : ∀ ell ∈ B, ell + tailBound ≤ M) :
    p.1 + (p.2 - p.1) + tailBound ≤ M := by
  have hle : p.1 ≤ p.2 := coordinatePairs_le B p hp
  have hsnd := hvalid p.2 (coordinatePairs_snd_mem B hEven hp)
  rw [Nat.add_sub_of_le hle]
  exact hsnd

#print axioms AssemblyP1.Issue94EvenPairing.coordinatePairs_endpoints_toFinset
#print axioms AssemblyP1.Issue94EvenPairing.coordinatePair_interval_valid

end AssemblyP1.Issue94EvenPairing
