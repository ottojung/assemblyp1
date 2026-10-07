import AssemblyP1.Issue94P2DoubledPair

/-!
# Board 94: equal-vtx pairs cannot overlap partially under primitive P2

The component-antiderivative route needs a small local fact: two aligned ladder
swaps cannot share exactly one endpoint. The ladder geometry is not needed for
that statement. Under primitive P2 every nondegenerate equal-vtx pair is the
complete two-point fibre of its (L-1)-mer, so two such pairs sharing one point
are the same unordered pair.
-/

namespace AssemblyP1.Issue94AlignedPairs

open AssemblyP1
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTLadder
open AssemblyP1.Issue94P2DoubledPair

variable {α : Type} [DecidableEq α] {K L : ℕ}

theorem pair_eq_of_shared_endpoint
    (hK : 0 < K) (S : Fin K → α) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {a b c d : Fin K}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hvab : vtx hK L S a = vtx hK L S b)
    (hvcd : vtx hK L S c = vtx hK L S d)
    (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) :
    ({a, b} : Finset (Fin K)) = {c, d} := by
  have hdab := doubledPair_of_vtx_eq hK S hL hLK hprim hP2 hab hvab
  have hdcd := doubledPair_of_vtx_eq hK S hL hLK hprim hP2 hcd hvcd
  have hbase : vtx hK L S c = vtx hK L S a := by
    rcases hshare with hac | had | hbc | hbd
    · simpa [hac]
    · exact hvcd.trans (by simpa [had] using hvab.symm)
    · exact (by simpa [hbc] using hvab.symm)
    · exact hvcd.trans (by simpa [hbd] using hvab.symm)
  apply Finset.ext
  intro x
  constructor
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    have hvx : vtx hK L S x = vtx hK L S c := by
      rcases hx with hxa | hxb
      · simpa [hxa] using hbase.symm
      · simpa [hxb] using hvab.symm.trans hbase.symm
    exact hdcd.2.1 x hvx
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    have hvx : vtx hK L S x = vtx hK L S a := by
      rcases hx with hxc | hxd
      · simpa [hxc] using hbase
      · simpa [hxd] using hvcd.symm.trans hbase
    exact hdab.2.1 x hvx

#print axioms AssemblyP1.Issue94AlignedPairs.pair_eq_of_shared_endpoint

end AssemblyP1.Issue94AlignedPairs

namespace AssemblyP1.Issue94AlignedPairs

open AssemblyP1
open AssemblyP1.BBTSequenceGraph
open AssemblyP1.BBTLadder
open AssemblyP1.BBTChords
open AssemblyP1.OrientedRigidity

theorem ladder_pair_eq_of_shared_endpoint
    {α : Type} [DecidableEq α] {K L e : ℕ}
    (hK : 0 < K) (S : Fin K → α) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {p q : Fin K}
    (hag : ∀ d : Fin e, cyc hK S (p.val + d.val) = cyc hK S (q.val + d.val))
    (he : L - 1 ≤ e)
    {i j : ℕ}
    (hi : i + (L - 1) ≤ e) (hj : j + (L - 1) ≤ e)
    (hine : rotAdd hK i p ≠ rotAdd hK i q)
    (hjne : rotAdd hK j p ≠ rotAdd hK j q)
    (hshare :
      rotAdd hK i p = rotAdd hK j p ∨
      rotAdd hK i p = rotAdd hK j q ∨
      rotAdd hK i q = rotAdd hK j p ∨
      rotAdd hK i q = rotAdd hK j q) :
    ({rotAdd hK i p, rotAdd hK i q} : Finset (Fin K)) =
      {rotAdd hK j p, rotAdd hK j q} := by
  apply pair_eq_of_shared_endpoint hK S hL hLK hprim hP2 hine hjne
  · exact ladder_arc_eq hK S hL hag he hi
  · exact ladder_arc_eq hK S hL hag he hj
  · exact hshare

theorem ladder_distinct_pairs_no_shared_endpoint
    {α : Type} [DecidableEq α] {K L e : ℕ}
    (hK : 0 < K) (S : Fin K → α) (hL : 2 ≤ L) (hLK : L ≤ K)
    (hprim : RepeatAdapter.IsPrimitive hK S) (hP2 : P2 hK L S)
    {p q : Fin K}
    (hag : ∀ d : Fin e, cyc hK S (p.val + d.val) = cyc hK S (q.val + d.val))
    (he : L - 1 ≤ e)
    {i j : ℕ}
    (hi : i + (L - 1) ≤ e) (hj : j + (L - 1) ≤ e)
    (hine : rotAdd hK i p ≠ rotAdd hK i q)
    (hjne : rotAdd hK j p ≠ rotAdd hK j q)
    (hpairs :
      ({rotAdd hK i p, rotAdd hK i q} : Finset (Fin K)) ≠
        {rotAdd hK j p, rotAdd hK j q}) :
    rotAdd hK i p ≠ rotAdd hK j p ∧
      rotAdd hK i p ≠ rotAdd hK j q ∧
      rotAdd hK i q ≠ rotAdd hK j p ∧
      rotAdd hK i q ≠ rotAdd hK j q := by
  constructor
  · intro h
    exact hpairs (ladder_pair_eq_of_shared_endpoint hK S hL hLK hprim hP2 hag he
      hi hj hine hjne (Or.inl h))
  constructor
  · intro h
    exact hpairs (ladder_pair_eq_of_shared_endpoint hK S hL hLK hprim hP2 hag he
      hi hj hine hjne (Or.inr (Or.inl h)))
  constructor
  · intro h
    exact hpairs (ladder_pair_eq_of_shared_endpoint hK S hL hLK hprim hP2 hag he
      hi hj hine hjne (Or.inr (Or.inr (Or.inl h))))
  · intro h
    exact hpairs (ladder_pair_eq_of_shared_endpoint hK S hL hLK hprim hP2 hag he
      hi hj hine hjne (Or.inr (Or.inr (Or.inr h))))

#print axioms AssemblyP1.Issue94AlignedPairs.ladder_pair_eq_of_shared_endpoint
#print axioms AssemblyP1.Issue94AlignedPairs.ladder_distinct_pairs_no_shared_endpoint

end AssemblyP1.Issue94AlignedPairs
