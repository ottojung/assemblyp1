that is spelled by two shorter overlaps" |
| `isReducibleLonger`, `transitivelyReducedLonger`, `ReductionVacuousLonger` | the alternative "two-step path of strictly *longer* proper overlaps" reading discussed in `docs/section62-mb09-bidirected-graph-audit.md` §2.1 |
| `BdFlow`, `Admissible` clause 1 | §6.2: "All other lower bounds are 0 and all upper bounds are infinity" |
| `Admissible` clause 2, `throughput` | §6.2: "Each vertex has a lower bound of 1"; §5.2: the vertex split `v⁻ → v⁺` carries the vertex bounds, so `d_i` is the flow through vertex `i` |
| `balance`, `Admissible` clause 3 | §3.4: a flow satisfies `pos(f)(v) − neg(f)(v) = b(v)` |
| `SuperTerminals`, `absorb`, `balance_absorb` | §6.2: "We make a final change to the graph by adding a supersource and supersink … We add prohibitively large costs to the edges from/to the supersource/sink so that their usage is minimized" |
| `Spelling`, `Spelling.flow`, `Spelling.visits` | §6.2: "the original double-stranded genome corresponds to a circuit"; Observation 7: the number of times `W` visits `r` equals the number of times `r` appears as a submolecule |
| `OppositeAtInterior`, `BidirectedCircuit` | §3.2: at every interior vertex of a bidirected walk the arriving and departing incidences are opposite |

The overlap threshold `oMin` and the read length `readLen` are explicit
parameters, so the choice `oMin = readLen − 1` used by the finite witnesses is
visible rather than baked in.

## What is *not* claimed here

This module encodes the §6.2 *feasible set* (Variant F of
`docs/ml-formalization-contract.md`, "Variant F").  It does not identify that
feasible set with the candidate universe of Variant A or Variant E, and it
proves no correspondence theorem in that direction.  A theorem proved here is a
statement about feasible §6.2 flows, and says so.
-/

namespace AssemblyP1.Section62Flow

/-! ## Strands and molecule classes -/

/-! A *strand* is represented directly by the element type `W` of a strand
type.  MB09 §3.1 models a DNA molecule as an unordered reverse-complement strand
pair, so a strand is a word and the two strands of the molecule class of `w` are
`w` and `rc w`.  The `toList` argument threaded through this module is the
linearization of a strand, which is what makes suffix/prefix overlap lengths
meaningful. -/

/-- The `len`-length prefix of a list.  Used to phrase a suffix/prefix overlap. -/
def preOf {α : Type} (l : List α) (len : Nat) : List α := l.take len

/-- The `len`-length suffix of a list. -/
def sufOf {α : Type} (l : List α) (len : Nat) : List α := l.drop (l.length - len)

/-- The signed incidence of the strand `s` of the molecule class `mx` at the
*departure* endpoint of an overlap: `+1` when `s` is the class representative and
`-1` for its reverse complement.  This is MB09 §3.3's incidence at the first
endpoint. -/
def sgnRep {W : Type} [DecidableEq W] (s mx : W) : ℤ := if s = mx then 1 else -1

/-- The signed incidence of the strand `s` of the molecule class `my` at the
*arrival* endpoint of an overlap: `-1` for the class representative and `+1`
for its reverse complement.  This is MB09 §3.3's incidence at the second
endpoint. -/
def sgnTgt {W : Type} [DecidableEq W] (s my : W) : ℤ := if s = my then -1 else 1

/-! ## The bidirected overlap graph (MB09 §6.2) -/

/-- An edge of the bidirected read-overlap graph, in the sense of MB09 §3.3: an
overlap of length `len` from the strand `sx` to the strand `sy`, carrying a
signed incidence at each of the two endpoint molecule classes.  `len` is a
*proper* overlap length, so a read never spells itself. -/
structure BdEdge (A : Type) (W : Type) [DecidableEq W] where
  /-- The departure strand. -/
  sx : W
  /-- The arrival strand. -/
  sy : W
  /-- The length of the overlap; a proper overlap, hence `< readLen`. -/
  len : Nat
  /-- The signed incidence at the molecule class of `sx`. -/
  sgnX : ℤ
  /-- The signed incidence at the molecule class of `sy`. -/
  sgnY : ℤ
with both signed incidences determined by the molecule-class representatives
`rep sx` and `rep sy`. -/
def bdEdge {A : Type} {W : Type} [DecidableEq W] (rep : W → W) (sx sy : W)
    (len : Nat) : BdEdge A W where
  sx := sx
  sy := sy
  len := len
  sgnX := sgnRep sx (rep sx)
  sgnY := sgnTgt sy (rep sy)

/-- The two strands of every observed molecule class: each representative and its
reverse complement.  This is the strand enumeration that generates the four
overlap cases of MB09 §3.3. -/
def strandsOf {W : Type} (rc : W → W) (verts : List W) : List W :=
  verts ++ verts.map rc

/-- The explicit bidirected overlap graph of MB09 §6.2 on the observed read
molecules: "the vertices of this graph are the reads, and the edges are all
possible bidirected overlaps of length at least `o_min`".

Concretely, the edge set consists of the triples (a departure strand, an arrival
strand, a proper overlap length `len` with `oMin ≤ len < readLen`) such that the
`len`-length suffix of the departure strand is the `len`-length prefix of the
arrival strand.  `rep` maps a strand to the representative of its molecule class
and thereby fixes the two endpoint incidences. -/
def overlapEdges (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat) (verts : List W) :
    List (BdEdge A W) :=
  (List.range readLen).filter (fun len => oMin ≤ len) |>.flatMap fun len =>
    strandsOf rc verts |>.flatMap fun sx =>
      strandsOf rc verts |>.flatMap fun sy =>
        if sufOf (toList sx) len = preOf (toList sy) len then [bdEdge rep sx sy len]
        else []

/-! ## Transitive edge reduction (MB09 §6.2) -/

/-- The longest proper overlap between the strands `a` and `b`: the largest
`l < readLen` with `sufOf a l = preOf b l`, and `0` when there is none. -/
def maxOverlap (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (readLen : Nat) (a b : W) : Nat :=
  ((List.range readLen).filter
      (fun l => decide (sufOf (toList a) l = preOf (toList b) l))).max?.getD 0

/-- Whether the edge `e : sx → sy` of length `e.len` is *spelled by two shorter
overlaps*, in the literal MB09 §6.2 sense.

The edge is reducible when there is a strand `m` of some observed molecule class
and overlap lengths `len₁`, `len₂`, both positive and **strictly shorter** than
`e.len`, with

* `m` overlaps `sx` by `len₁` and overlaps `sy` by `len₂` (using the longest such
  overlaps, since a shorter one is always available);
* the two overlaps spell exactly the direct overlap, i.e.
  `len₁ + len₂ − readLen = e.len`.

The last identity is the composition law for overlaps: two overlaps of lengths
`len₁` and `len₂` place the outer reads at offset `len₁ + len₂`, so their
composition realizes an outer overlap of length `len₁ + len₂ − readLen`.  The
length candidates range over `List.range readLen`, which suffices because every
proper overlap is shorter than `readLen`. -/
def isReducibleB (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen : Nat) (verts : List W)
    (e : BdEdge A W) : Bool :=
  verts.any fun _my =>
    (strandsOf rc verts).any fun m =>
      (List.range readLen).any fun len₁ =>
        (List.range readLen).any fun len₂ =>
          decide (maxOverlap A W toList readLen e.sx m = len₁) &&
            decide (maxOverlap A W toList readLen m e.sy = len₂) &&
            decide (0 < len₁) && decide (0 < len₂) &&
            decide (len₁ < e.len) && decide (len₂ < e.len) &&
            decide (len₁ + len₂ - readLen = e.len)

/-- The transitive edge reduction of MB09 §6.2, read literally: "remove any
overlap that is spelled by two shorter overlaps". -/
def isReducible (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen : Nat) (verts : List W)
    (e : BdEdge A W) : Prop :=
  isReducibleB A W toList rc readLen verts e = true
idableEq W]
    (toList : W → List A) (rc : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) : List (BdEdge A W) :=
  edges.filter (fun e => !isReducibleLongerB A W toList rc readLen verts e)

/-- No edge of `edges` is spelled by two shorter overlaps, so the transitive
reduction is vacuous on `edges`. -/
def ReductionVacuous (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) : Prop :=
  edges.all (fun e => !isReducibleB A W toList rc readLen verts e) = true

/-- Likewise, no edge of `edges` is removed by the longer-overlap reading. -/
def ReductionVacuousLonger (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    (toList : W → List A) (rc : W → W) (readLen : Nat) (verts : List W)
    (edges : List (BdEdge A W)) : Prop :=
  edges.all (fun e => !isReducibleLongerB A W toList rc readLen verts e) = true

/-! ## Flows, lower bounds, balance, supersource/supersink -/

/-- A §6.2 integral flow on the bidirected overlap graph.  MB09 §6.2 leaves all
upper bounds at infinity, so no upper bound is represented; the flow is
supported on the edge list `edges`, which is the graph. -/
abbrev BdFlow (A : Type) (W : Type) [DecidableEq W] : Type := BdEdge A W → ℕ

/-- MB09 §6.2 adds a supersource and a supersink "to the graph", at prohibitively
large cost, so that a flow need not be balanced at the read vertices: the
residual is absorbed by the two new vertices.  `srcUse v` is the flow on the
supersource edge into the read vertex `v`, and `snkUse v` the flow on the
supersink edge out of it.  The prohibitive cost is what forces the terminal usage
to be minimal. -/
structure SuperTerminals (W : Type) where
  /-- Flow on the supersource edge into each read vertex. -/
  srcUse : W → ℕ
  /-- Flow on the supersink edge out of each read vertex. -/
  snkUse : W → ℕ

/-- No supersource and no supersink is used.  This is the situation for a
genuine circuit: MB09 §6.2 observes that "the original double-stranded genome
corresponds to a circuit", and a closed circuit needs no terminal. -/
def noTerminals (W : Type) : SuperTerminals W where
  srcUse := fun _ => 0
  snkUse := fun _ => 0

/-- The signed-incidence balance of the flow `f` at the read molecule class `v`,
in the sense of MB09 §3.4: `pos(f)(v) − neg(f)(v)`, where every graph edge
incident to `v` contributes `f e` times its incidence sign at `v`, and the
supersource contributes the positive incidence `srcUse v` while the supersink
contributes the negative incidence `− snkUse v`.  MB09 writes the flow condition
as `pos(f)(v) − neg(f)(v) = b(v)`; after the §6.2 supersource/supersink
conversion a feasible flow has `b(v) = 0`. -/
def balCore (A : Type) (W : Type) [DecidableEq W] (rep : W → W) (f : BdFlow A W)
    (edges : List (BdEdge A W)) (v : W) : ℤ :=
  (edges.filter (fun e => rep e.sx = v)).foldr
      (fun e acc => (f e : ℤ) * e.sgnX + acc) 0 +
    (edges.filter (fun e => rep e.sy = v)).foldr
      (fun e acc => (f e : ℤ) * e.sgnY + acc) 0

/-- The flow through the read vertex `v`: the total flow on the graph edges that
*depart* from the molecule class of `v`.  By MB09 §5.2 the vertex split
`v⁻ → v⁺` carries the vertex lower bounds, so `d_i` is precisely the flow through
vertex `i`; by Observation 7 this is the number of times a candidate visits `v`.
A self-loop departs from and arrives at the same vertex, so it is counted once,
matching the single traversal of a loop by a cyclic walk. -/
def throughput (A : Type) (W : Type) [DecidableEq W] (rep : W → W) (f : BdFlow A W)
    (edges : List (BdEdge A W)) (v : W) : ℕ :=
  edges.foldr (fun e acc => if rep e.sx = v then f e + acc else acc) 0

def balance (A : Type) (W : Type) [DecidableEq W] (rep : W → W) (f : BdFlow A W)
    (t : SuperTerminals W) (edges : List (BdEdge A W)) (v : W) : ℤ :=
  balCore A W rep f edges v + ((t.srcUse v : ℤ) - (t.snkUse v : ℤ))

t 0 _)

/-- The §6.2 circulation conversion: after adding the supersource and supersink
with the absorbing usages, the flow is balanced at every read vertex.  This is
why §6.2 may state its feasibility with `b(v) = 0` and treat terminal usage as a
residual to be minimized.  The absorbing usages cancel the *graph's* residual
`balCore`, so they do not depend on any terminal usage already present. -/
theorem balance_absorb (A : Type) (W : Type) [DecidableEq W] (rep : W → W)
    (f : BdFlow A W) (edges : List (BdEdge A W)) (v : W) :
    balance A W rep f (absorb A W rep f edges) edges v = 0 := by
  simp only [balance, absorb, cast_max_zero]
  ring_nf
  exact int_absorb _

/-- §6.2 admissibility of a flow `f` on the graph `edges` with throughput vector
`d`, over the read vertex set `verts`.

The four clauses, in order:

1. **edge lower bounds** — every edge meets its lower bound.  MB09 §6.2: "All
   other lower bounds are 0 and all upper bounds are infinity", so on overlap
   edges the lower bound is `edgeLB = 0` and the binding condition is the vertex
   clause;
2. **vertex lower bounds** — every read vertex carries flow at least `vertexLB`.
   MB09 §6.2: "Each vertex has a lower bound of 1 since it represents a read
   that must be present in the genome at least once";
3. **signed-incidence balance** — `pos(f)(v) − neg(f)(v) = 0` at every read
   vertex, after the supersource/supersink conversion.  MB09 §3.4 supplies the
   balance equation and §6.2 supplies the terminals that make it attainable;
4. **throughput** — the flow through read vertex `v` is exactly `d v`, which
   Observation 7 identifies with the number of times the candidate visits `v`. -/
def Admissible (A : Type) (W : Type) [DecidableEq W] (edgeLB vertexLB : ℕ)
    (rep : W → W) (verts : List W) (edges : List (BdEdge A W)) (f : BdFlow A W)
    (t : SuperTerminals W) (d : W → ℕ) : Prop :=
  (∀ e ∈ edges, edgeLB ≤ f e) ∧
    (∀ v ∈ verts, vertexLB ≤ throughput A W rep f edges v) ∧
    (∀ v ∈ verts, balance A W rep f t edges v = 0) ∧
    (∀ v ∈ verts, throughput A W rep f edges v = d v)

/-- The zero-terminal statement of `t = noTerminals`, used as the last conjunct of
`Feasible62`. -/
theorem noTerminals_usage_zero (W : Type) :
    ∀ v, (noTerminals W).srcUse v = 0 ∧ (noTerminals W).snkUse v = 0 :=
  fun _ => ⟨rfl, rfl⟩

/-- A §6.2 feasible candidate: a flow on the (transitively reduced) graph with
vertex lower bound `1`, edge lower bounds `0`, infinite upper bounds, balanced
after the supersource/supersink conversion, and with vertex throughputs equal to
the candidate's molecule spectrum `d`.

Two clauses make the supersource/supersink clause non-vacuous, which matters
because §6.2 achieves balance with `b(v) = 0` only *by adding* the terminals: the
balance equation `pos(f)(v) − neg(f)(v) = b(v)` of §3.4 is a statement about a
graph that already has the terminals, and `absorb`/`balance_absorb` exhibit a
terminal choice that balances *any* flow.  So if the terminal usage were left
free, the balance clause of `Admissible` would be satisfiable for every `f` and
would say nothing.  Accordingly `Feasible62` also requires

* **zero terminal usage**, which is exactly the situation of the circuit that
  §6.2 says "the original double-stranded genome corresponds to"; and

so the balance clause, read with `t = noTerminals`, is the genuine requirement
that the flow be balanced, `pos(f)(v) − neg(f)(v) = 0`, at every read vertex.
This is the reading of §6.2's "prohibitively large costs … so that their usage is
minimized" that the source's own circuit observation pins down; flows that do use
the terminals remain available in the general predicate `Admissible`, and
`absorb`/`balance_absorb` remain the conversion from a residual balance to a
circulation.

Note also that `BdFlow` is a total function on `BdEdge A W` while MB09's flow
lives on the graph; the graph is the argument `edges`, and all four clauses are
-/
def Spelling.step {A : Type} {W : Type} [DecidableEq W] {n : Nat}
    (rep : W → W) (readLen : Nat) (sp : Spelling A W n) (i : Fin n) : BdEdge A W :=
  bdEdge rep (sp.strand i) (sp.strand (next sp i)) (readLen - 1)

/-- The flow carried by the cyclic walk of a spelling: step `i` carries flow `1`
and every other edge carries `0`.  A self-loop occurring at several positions
accumulates that multiplicity, so the flow is the multiset of traversals.

Counting over `List.finRange` rather than `Finset.univ` keeps this reducible by
`decide` at finite instances. -/
def Spelling.flow {A : Type} {W : Type} [DecidableEq W] {n : Nat}
    (rep : W → W) (readLen : Nat) (sp : Spelling A W n) (e : BdEdge A W) : ℕ :=
  ((List.finRange n).filter (fun i => decide (sp.step rep readLen i = e))).length

/-- The number of times the spelling visits the read molecule class `v`.  By
MB09 Observation 7 this equals the number of times `v` appears as a submolecule
of the candidate, i.e. the coordinate of the candidate's molecule spectrum. -/
def Spelling.visits {A : Type} {W : Type} [DecidableEq W] {n : Nat} (rep : W → W)
    (sp : Spelling A W n) (v : W) : ℕ :=
  ((List.finRange n).filter (fun i => decide (rep (sp.strand i) = v))).length

/-- MB09 §3.2: a walk in a bidirected graph is a valid bidirected walk when, at
every interior vertex, the incidence at which it arrives is opposite to the
incidence at which it departs.  At interior position `i` of a cyclic spelling
the walk arrives along step `i − 1` (with that step's `sgnY`) and departs along
step `i` (with its `sgnX`). -/
def OppositeAtInterior {A : Type} {W : Type} [DecidableEq W] {n : Nat}
    (rep : W → W) (readLen : Nat) (sp : Spelling A W n) (i : Fin n) : Prop :=
  (sp.step rep readLen i).sgnX = -((sp.step rep readLen (pred sp i)).sgnY)

/-- The spelling is a bidirected circuit in the sense of MB09 §3.2 and §6.2: at
every interior vertex the arriving and departing incidences are opposite. -/
def BidirectedCircuit {A : Type} {W : Type} [DecidableEq W] {n : Nat} (rep : W → W)
    (readLen : Nat) (sp : Spelling A W n) : Prop :=
  ∀ i : Fin n, OppositeAtInterior rep readLen sp i

/-- Every step of the cyclic walk is an edge of the graph `edges`: the candidate
is spelled by the observed reads, i.e. its window walk lives on the bidirected
overlap graph. -/
def StepsInGraph {A : Type} {W : Type} [DecidableEq W] {n : Nat}
    (rep : W → W) (readLen : Nat) (sp : Spelling A W n) (edges : List (BdEdge A W)) :
    Prop :=
  ∀ i : Fin n, sp.step rep readLen i ∈ edges

/-- Every step of the cyclic walk survives the transitive edge reduction, so the
walk lives on the *transitively reduced* graph as MB09 §6.2 requires. -/
def StepsSurviveReduction (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    {n : Nat} (toList : W → List A) (rep rc : W → W) (readLen : Nat)
    (verts : List W) (sp : Spelling A W n) (edges : List (BdEdge A W)) : Prop :=
  ∀ i : Fin n,
    sp.step rep readLen i ∈ transitivelyReduced A W toList rc readLen verts edges

/-- Every position of the walk visits an observed read molecule. -/
def VisitsObserved {A : Type} {W : Type} {n : Nat} (rep : W → W)
    (sp : Spelling A W n) (verts : List W) : Prop :=
  ∀ i : Fin n, rep (sp.strand i) ∈ verts

/-- A §6.2 feasible *spelled* candidate, with `f` an explicit finite feasible
flow: the cyclic window walk of a circular molecule is a bidirected circuit in
the transitively reduced overlap graph, every step of that walk is an edge of the
overlap graph and survives the transitive reduction, every visited vertex is an
observed read molecule, and `f` is a feasible §6.2 flow on that graph with
throughput vector `d` (the candidate's molecule spectrum) and terminal usage `t`.

The flow is an explicit argument rather than `Spelling.flow` so that a witness
may hand in a written-down certificate; `truthCircuitFlow_eq_walkFlow`-style
lemmas then show that the certificate is the flow the walk itself carries. -/
def SpelledFeasible62 (A : Type) (W : Type) [DecidableEq A] [DecidableEq W]
    {n : Nat} (toList : W → List A) (rep rc : W → W) (readLen oMin : Nat)
    (verts : List W) (sp : Spelling A W n) (f : BdFlow A W) (t : SuperTerminals W)
    (d : W → ℕ) : Prop :=
  VisitsObserved rep sp verts ∧
    StepsInGraph rep readLen sp (overlapEdges A W toList rep rc readLen oMin verts) ∧
    StepsSurviveReduction A W toList rep rc readLen verts sp
      (overlapEdges A W toList rep rc readLen oMin verts) ∧
    BidirectedCircuit rep readLen sp ∧
    Feasible62 A W rep verts (overlapEdges A W toList rep rc readLen oMin verts) f t d

end AssemblyP1.Section62Flow
