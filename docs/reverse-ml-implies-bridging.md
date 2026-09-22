# Reverse direction: does ML recovery/uniqueness imply bridging or reconstructibility?

_Status: exploration note, 2026-09-22, against `origin/main` at `2efd560`.
It answers the converse of the 2016 question under the repository's current
models. Claims are labelled **mathematical fact**, **verified computation**
(brute-force over stated finite classes, not kernel-checked), or
**source-supported inference**. Nothing here modifies the forward-direction
results or the source-fidelity register._

## 0. Question and answer

Forward (2016): bridging/`I_s` ⇒ truth is (uniquely) ML.
Reverse: truth is (uniquely) ML ⇒ bridging/`I_s` holds (or the genome is
reconstructible)?

| Reverse reading | Status |
|---|---|
| Population weak: truth is a population maximizer ⇒ `I_s` | **False, trivially** (P1) |
| Finite weak: truth is a finite-sample maximizer ⇒ `I_s` | **False** (P1') |
| Population strong, fixed-length class: truth uniquely ML up to rotation ⇒ `I_s` | **False** (P2, finite witness) |
| Population strong, unrestricted lengths: unique up to rotation ⇒ `I_s` | **Vacuously true** — antecedent never holds (P3) |

## 1. Models and assumptions (exact)

- Oriented single-strand circular genomes over `{A,B}` (binary codes
  `0/1` below); read length `L`; circular length-`L` spectrum `spec_L`.
- Population objective (§6 of `maximum-likelihood-models-for-genome-assembly.md`):
  `ell_S(D) = Σ_w p_S(w) log p_D(w)`, `-inf` if some truth-positive word is
  absent from `D`. Maximizer claim is Gibbs/KL (`ell_S(D) − ell_S(S) =
  −KL(p_S‖p_D) ≤ 0`), a **mathematical fact** needing no bridging.
- Finite objective: exact multinomial ordering `Σ_i x_i log d_D(i)` (Variant E).
- Bridging/`I_s`: `docs/bridging-source-semantics.md` — coverage ∧ every maximal
  triple repeat all-bridged ∧ every interleaved maximal pair bridged, with
  strict extension (`r < t`, `t+ℓ < r+L`). Read-type space is Shomorony's
  oriented one throughout; nothing here bears on the molecule/RC panel.
- Genome equivalence: cyclic rotation only (forced for the strong schema; see
  `source-notes/conclusion-semantics-determination.md` §2.2).

## 2. Witness (used by P1, P1', P2)

Truth `S = AAAB` (`G=4`), `L=2`. Circular 2-mer spectrum (verified computation):

- `spec_2(S) = {AA:2, AB:1, BA:1}`.

Maximal triple repeat of length 1 at starts `(0,1,2)` (verified computation):
windows all `(A,)`; preceding symbols `(B,A,A)`, not all equal; following
symbols `(A,A,B)`, not all equal — hence maximal under Bresler's three-copy
condition. Bridging any copy needs `L ≥ ℓ+2 = 3`; with `L=2` no placement
bridges any copy, so under full coverage `I_s` **fails** (mathematical fact
from the strict-extension definition).

## 3. Propositions

**P1 (population weak reverse is false — trivial).** Every `S` is a population
maximizer by Gibbs with no bridging hypothesis. `S=AAAB`, `L=2` is a concrete
non-`I_s` instance. [mathematical fact]

**P1' (finite weak reverse is false).** With realized reads equal to the truth
spectrum (`x = {AA:2, AB:1, BA:1}`, placements at the true starts: coverage
holds, bridging still impossible since `L=2<3`), the truth's ordering score
`log L = 2·log 2 ≈ 1.386` is maximal over all 16 length-4 circular candidates
(exhaustive check), yet `I_s` fails as above. [verified computation]

**P2 (fixed-length strong reverse is false).** Over all circular binary
length-4 candidates, no genome besides rotations of `S` has spectrum
`{AA:2, AB:1, BA:1}` (exhaustive 16-case check), so every same-length competitor
either scores `-inf` (misses a truth-positive word) or has a different
distribution with strictly negative KL gap — the truth is the unique population
maximizer up to rotation — while `I_s` fails. Hence unique-ML does not imply
bridging, and spectrum identifiability (reconstructibility in the complete-
spectrum sense) does not imply bridging either. [verified computation]

**P3 (unrestricted-length strong reverse is vacuous).** For any `S`, the doubled
genome `S²` has `spec_L(S²) = 2·spec_L(S)`, hence `p_{S²} = p_S` and a population
tie. E.g. `(AAAB)² = AAABAAAB` has `{AA:4, AB:2, BA:2}`. So "unique up to
rotation among all lengths" never holds; the implication is vacuously true.
A non-vacuous unrestricted claim needs a restricted class (fixed length as in
P2, or primitivity — but primitivity alone does not remove power ties for the
_truth's_ competitors unless the class itself excludes non-primitive
candidates). [mathematical fact + verified instance]

## 4. What is interesting vs trivial

- Trivial: P1 (Gibbs needs no bridging); P3 (powers always tie).
- Nontrivial but small: P2 — a 16-case finite certificate separating
  identifiability from bridging. It shows bridging is sufficient but not
  necessary for spectrum uniqueness, as expected from BBT-style sufficient
  conditions, now pinned to an explicit instance.
- Genuinely open (not claimed here): whether any natural candidate class makes
  the reverse hold non-vacuously (e.g. primitive-only classes, or finite-sample
  high-probability versions); whether ML-uniqueness implies *reconstructibility
  by a specific algorithm* (Not-So-Greedy) rather than bare spectrum
  identifiability — not addressed here.

## 5. Reproduction

```sh
python3 -c "
from itertools import product
from collections import Counter
import math
def rots(s):
    n=len(s); return [tuple(s[(i+j)%n] for j in range(n)) for i in range(n)]
def canon(s): return min(rots(s))
def spec(s,L):
    n=len(s); return Counter(tuple(s[(i+j)%n] for j in range(L)) for i in range(n))
S=[0,0,0,1]; L=2; G=4; sp=spec(S,L)
print('collisions:',[c for c in set(canon(list(p)) for p in product([0,1],repeat=G)) if c!=canon(S) and spec(list(c),L)==sp])
x=dict(sp)
def ll(D):
    sd=spec(D,L); return sum(c*math.log(sd.get(k,0)) if sd.get(k,0)>0 else float('-inf') for k,c in x.items())
print('finite ML holds:',all(ll(list(c))<=ll(S)+1e-12 for c in set(canon(list(p)) for p in product([0,1],repeat=G))))
"
```

Epistemic status: computations above are brute-force evidence, not Lean
kernel-checked results. The Gibbs/KL and power-tie arguments are textbook
mathematical facts. Source-fidelity assumptions (§1) are stated exactly so a
later worker can re-scope (molecule read types, other equivalences, Variant
A/F objectives) without re-reading prose.
