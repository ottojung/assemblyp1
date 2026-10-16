import AssemblyP1.RigidityBouquet

/-!
A genuine circular DNA read-spectrum realization of the (2,3,3) bouquet
with multiplicities (2,1,1). This is a kernel-computed regression for the
genome, oriented read counts and overlap graph; the abstract bouquet theorem
itself lives in RigidityBouquet.lean.

DNA letters: 0=A, 1=C, 2=G, 3=T.
Circular genome: ACACGACTAC, G=10, L=3.
The order-2 de Bruijn graph has common vertex AC and three cycles:
 AC -> CA -> AC (length 2, multiplicity 2),
 AC -> CG -> GA -> AC (length 3, multiplicity 1),
 AC -> CT -> TA -> AC (length 3, multiplicity 1).
This does not claim every abstract bouquet is a de Bruijn graph, or that
a direct rational relaxation rules out all LP formulations.
-/

namespace AssemblyP1.RigidityBouquetGenomeWitness

def genome : List Nat := [0,1,0,1,2,0,1,3,0,1]

def readAt (i : Nat) : List Nat :=
  (List.range 3).map (fun j => genome[(i+j) % genome.length]!)

def spectrum : List (List Nat) :=
  (List.range genome.length).map readAt

theorem genome_length : genome.length = 10 := by decide

theorem exact_circular_spectrum :
    spectrum = [
      [0,1,0], [1,0,1], [0,1,2], [1,2,0], [2,0,1],
      [0,1,3], [1,3,0], [3,0,1], [0,1,0], [1,0,1]
    ] := by decide

theorem exact_read_multiplicities :
    spectrum.count [0,1,0] = 2 ∧
    spectrum.count [1,0,1] = 2 ∧
    spectrum.count [0,1,2] = 1 ∧
    spectrum.count [1,2,0] = 1 ∧
    spectrum.count [2,0,1] = 1 ∧
    spectrum.count [0,1,3] = 1 ∧
    spectrum.count [1,3,0] = 1 ∧
    spectrum.count [3,0,1] = 1 := by decide

def src (r : List Nat) : List Nat := r.take 2
def dst (r : List Nat) : List Nat := r.drop 1

theorem bouquet_three_cycles :
    src [0,1,0] = [0,1] ∧ dst [0,1,0] = [1,0] ∧
    src [1,0,1] = [1,0] ∧ dst [1,0,1] = [0,1] ∧
    src [0,1,2] = [0,1] ∧ dst [0,1,2] = [1,2] ∧
    src [1,2,0] = [1,2] ∧ dst [1,2,0] = [2,0] ∧
    src [2,0,1] = [2,0] ∧ dst [2,0,1] = [0,1] ∧
    src [0,1,3] = [0,1] ∧ dst [0,1,3] = [1,3] ∧
    src [1,3,0] = [1,3] ∧ dst [1,3,0] = [3,0] ∧
    src [3,0,1] = [3,0] ∧ dst [3,0,1] = [0,1] := by decide

#print axioms genome_length
#print axioms exact_circular_spectrum
#print axioms exact_read_multiplicities
#print axioms bouquet_three_cycles

end AssemblyP1.RigidityBouquetGenomeWitness
