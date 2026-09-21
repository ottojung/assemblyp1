# Circular `P2` / Ukkonen–Pevzner uniqueness criterion: source audit

_Search date: 2026-09-21. Scope: identify an actually citable theorem (circular
strings / multispectra, or a precise adaptation) bearing on the repository's
`P2 ⇒ circular L-spectrum uniqueness` claim, and determine whether the located
sources really imply it. No Russian-language material was used. All claims are
labelled **source fact (primary)**, **source fact (secondary restatement)**,
**mathematical fact**, **analysis**, or **gap**._

Reproduction of the repository-side computational evidence cited below:
`python3 scripts/bridging_spectrum_uniqueness.py` (checks A–D, re-run
2026-09-21, `total admissible=123906 ambiguous=0`, plus `1655` randomized
admissible genomes, `0` ambiguous).

---

## 0. The claim under audit, and the verdict

The repository's `P2` (= `WEAK(D)`, the candidate-intrinsic shadow of the strict
source hypothesis `I_s` at the full read set) is:

> **`P2(D)`**: every triple repeat of `D` has length `≤ L−2`, and every
> interleaved maximal-repeat pair of `D` has a constituent of length `≤ L−2`.
> (`docs/issue48-length-shrinkage-family.md:92-100`; equivalently
> `I_s`-admissibility, `mathematics/bridging-and-spectrum-uniqueness.md:70-78`.)

The repository conjecture connecting it to spectra is:

> **Conjecture 4.** If `S` is `I_s`-admissible, then any circular genome `D` of
> the same length `G` with the same `L`-mer spectrum is a cyclic shift of `S`.
> (`mathematics/bridging-and-spectrum-uniqueness.md:170-176`.)

Prior notes assert that this is "very likely the circular special case of a
**known theorem** (Ukkonen 1992 / Pevzner 1995)" and propose downgrading
Conjecture 4 from "conjecture" to "known source theorem", while flagging two
caveats: the exact `L−1` vs `L−2` threshold and the circular indexing
(`docs/literature/substring-spectrum-identifiability-2026-09-20.md:77-88,
`docs/source-notes/conclusion-semantics-equivalence-and-length.md:155-162`).

**Verdict.** The two flagged caveats are real and are not closed by any located
source.

1. **The classical Ukkonen–Pevzner characterization is a statement about
   `linear` words / Eulerian trails.** It is not stated for circular words, and
   its `Rotation` blocking pattern is exactly the linear prefix–suffix
   ("artificial boundary") case, which has no separate circular analogue.
   **No primary or peer-reviewed source located by this audit states a circular
   Ukkonen–Pevzner classification for the `L`-mer `multiset`.**
2. **No located source states, or implies, `P2 ⇒` circular `L`-spectrum
   uniqueness.** The nearest fully citable circular ingredients are (i) the
   `L`-mer-multiset ↔ Eulerian-circuit correspondence (Arratia–Bollobás–
   Coppersmith–Sorkin 2000) and (ii) certificates for a unique Eulerian circuit
   (Pevzner 1989; BEST; Obscura Acosta–Tomescu 2024). Passing from those to
   Conjecture 4 requires a graph-theoretic lemma about de Bruijn multigraphs
   that is not in the audited literature.
3. **Conjecture 4 must therefore remain a conjecture.** The suggestion to
   downgrade it to "known source theorem" is not supported and should not be
   adopted. The repository's `123 906`-instance exhaustive check plus `1 655`
   randomized admissible genomes (zero ambiguous) is evidence, not a source
   theorem and not a proof.

What the sources *do* supply is recorded in §§1–4; the precise boundary issue is
analysed in §5; the implication question is settled in §6.

---

## 1. Ukkonen 1992 — the exact primary statement (linear)

**Citation.** E. Ukkonen, *Approximate string-matching with `q`-grams and
maximal matches*, *Theoretical Computer Science* **92**(1):191–211, 6 Jan 1992.
DOI `10.1016/0304-3975(92)90143-4`.
Author's scanned PDF: <https://www.cs.helsinki.fi/u/ukkonen/TCS92.pdf> (image
only, no text layer; the quotes below were obtained by OCR of that PDF during
this audit and are marked accordingly).

**Setup (p. 193).** `G(x)[v]` = number of occurrences of the `q`-gram `v` in
`x` (the `q`-gram profile); `Z_q(x) = { y : G(y) = G(x) }` (same profile).

**Theorem 2.2 (p. 193) [source fact, primary, OCR].**

> "(i) Let `x = a₁a₂…aₙ` … Then `Z_q(x)` consists of all permutations of
> `a₁a₂…aₙ`. (ii) All strings in `Z_q(x)` are of length `|x|`. (iii) If `x`
> contains at most one occurrence of each `(q−1)`-gram then `|Z_q(x)| = 1`."

Part (iii) is the sufficient identifiability condition; it is the source of the
circular-sufficient statement "all `(L−1)`-mers distinct ⇒ unique" used in later
work (§3.1). It is **linear**.

**The open question and the two transformations (p. 194) [source fact, primary,
OCR].** Ukkonen writes (notation: `y` a candidate in `Z_q(x)`, `z₁,z₂` are
`(q−1)`-grams):

> **(transposition)** If `y = y₁ z₁ y₂ z₂ y₃ z₁ y₄ z₂ y₅`, then
> `y₁ z₁ y₄ z₂ y₃ z₁ y₂ z₂ y₅ ∈ Z_q(x)`. If `y = y₁ z y₂ z y₃ z y₄`, then also
> `y₁ z y₃ z y₂ z y₄ ∈ Z_q(x)`.
> **(rotation)** If `y = z₁ y₁ z₂ y₂ z₁`, then also `z₂ y₂ z₁ y₁ z₂ ∈ Z_q(x)`.
>
> "A large part of `Z_q(x)` can obviously be generated from `x` by repeatedly
> applying rules 1 and 2. **Whether or not it is possible to generate the whole
> `Z_q(x)` in this way remains open.**"

Two points matter for the repository.

- The source phrases this as an **open question**, not a numbered "Conjecture".
  [source fact, primary]
- **Linear.** The objects are finite strings with endpoints; `rotation`
  requires the word to begin *and end* with the same `(q−1)`-gram `z₁` — this is
  exactly the prefix–suffix boundary. [source fact, primary]

---

## 2. Pevzner 1995 — proved the linear classification; primary text inaccessible

**Citation.** P. A. Pevzner, *DNA physical mapping and alternating Eulerian
cycles in colored graphs*, *Algorithmica* **13**(1–2):77–105, 1995. DOI
`10.1007/BF01188582`.

**Access status [gap].** The published text is paywalled and no legitimate open
copy was located during this audit (Springer served a bot-challenge page). No
verbatim primary theorem number or wording could be verified. Everything below
is a **secondary restatement** and is labelled as such.

**Pevzner proved Ukkonen's conjecture (linear).** Multiple peer-reviewed English
sources state this:

- J. Jin, A. Kontorovich, A. Trachtenberg (ITA 2013, DOI
  `10.1109/ITA.2013.6503005`; full version arXiv:1204.3293): "Pevzner [25]
  proved that this conjecture is true", quoting the same transposition/rotation
  formulas as Ukkonen. [source fact, secondary]
- Cenzato, Franco, Lipták, Milanese, *Natural Computing* (2025), DOI
  `10.1007/s11047-025-10054-5`: "It was conjectured in Ukkonen (1992) and
  **proven in Pevzner (1995)** that two strings that have the same `q`-gram
  profile can be transformed into one another using a finite number of
  transformations of two types (called **transposition resp. rotation**)."
  [source fact, secondary]
- R. Arratia, B. Bollobás, D. Coppersmith, G. B. Sorkin, *Discrete Applied
  Mathematics* **104**(1–3):63–96, 2000, DOI `10.1016/S0166-218X(00)00190-6`:
  the equivalence is generated by **rotation**, **3-way (triple) repeat**, and
  **interlaced two-way repeat** structures, with Pevzner's transposition
  result. [source fact, secondary]

**Blocking-pattern form (linear).** E. Mossel's Simons Institute lecture
"Shotgun Assembly of Labelled Graphs" (2016) restates:

> "Ans (Ukkonen-Pevzner): Identifiability is possible if and only if none of the
> following blocking patterns appear: **Rotation:** `xαyβx ⇔ yβxαy`;
> **Triple repeat:** `···xαxβx··· ⇔ ···xβxαx···`; **Interleaved repeat:**
> `···xαy···xβy··· ⇔ ···xβy···xαy···` [`x`,`y` are `(r−1)`-tuples and `α`,`β`
> non-equal strings]", and "Identifiability is possible if and only if a unique
> Eulerian **path** (though not circuit)."
> [source fact, secondary; <https://simons.berkeley.edu/sites/default/files/docs/4837/simonsmay2016.pdf>]

The same slides reproduce a figure from Pevzner's paper at **p. 87**, "All words
with given `q`-gram composition correspond to Eulerian **paths** in directed
graph `D`; … order exchanges in `D*` correspond to Ukkonen's transpositions."
This is the only page-level anchor to the primary text this audit found; the
theorem number remains unknown. [gap]

**Summary for the repository.** The classical characterization is **linear**
(Eulerian *trails/paths*), and its three blocking patterns are `Rotation`
(prefix–suffix boundary), `Triple repeat`, `Interleaved repeat`, all at the
`(q−1)`-mer level. The `Rotation` pattern is the linear boundary artifact.

---

## 3. What is actually citable for the circular / multiset setting

### 3.1 Multiset ↔ Eulerian circuits (the correct circular frame)

**Citation.** R. Arratia, B. Bollobás, D. Coppersmith, G. B. Sorkin, *Euler
circuits and DNA sequencing by hybridization*, *Discrete Applied Mathematics*
**104**(1–3):63–96, 2000. DOI `10.1016/S0166-218X(00)00190-6`.

Direct quote (retrieved during this audit):

> "The `l`-spectrum is precisely the multiset of edges. … The Euler paths are in
> one-to-one correspondence with words having the same `l`-spectrum as
> `A₁⋯A_m`. … if there are multiple edges from vertex `A` to vertex `A′`, then
> these edges are indistinguishable."
> [source fact, secondary (direct quote from the paper)]

**Mathematical fact (repository analysis, standard).** For a circular word `S`,
build the de Bruijn multigraph `B(S)`: vertices are the occurring `(L−1)`-mer
types, edges are the length-`L` windows, from prefix to suffix, with
multiplicity `d_S(w)`. Then there is a bijection

```
{ circular words D with M_L(D) = M_L(S) }
    ↕
{ Eulerian circuits of B(S), modulo cyclic rotation and
  modulo permutations of identically-labelled parallel edges }.
```

This is the closed-circuit analogue of the Arratia et al. path statement; the
"parallel edges indistinguishable" clause is essential and is stated by them.
The correspondence automatically fixes the length (`= G`), matching Conjecture
4's same-length condition. [analysis, grounded in the quoted source]

### 3.2 Certificates for a *unique* Eulerian circuit

- **Pevzner 1989** (*l-tuple DNA sequencing: computer analysis*, *J. Biomol.
  Struct. Dyn.* **7**(1):63–73, DOI `10.1080/07391102.1989.10507752`), as stated
  by Waterman, *Introduction to Computational Biology*, Theorem 7.5:
  "Graph `G` has a unique Eulerian circuit if and only if the intersection graph
  `G_I` of simple cycles from `G` is a tree." [source fact, secondary]
- **BEST theorem** (de Bruijn, van Aardenne-Ehrenfest, Smith, Tutte): the number
  of Eulerian circuits is `t(G)·∏_v (d(v)−1)!` (`t` = arborescences).
- **N. Obscura Acosta, A. I. Tomescu**, *Simplicity in Eulerian circuits:
  uniqueness and safety*, *Inf. Process. Lett.* **183**:106421, 2024, DOI
  `10.1016/j.ipl.2023.106421` (arXiv:2208.08522): "`G` admits a unique Eulerian
  circuit if and only if `A(G) = V`", with `A(G) = { v : d(v)=1 ∨ (d(v)=2 ∧ v a
  cut node of U(G)) }`, checkable in `O(|E|)`. [source fact, secondary]
- **Caveat (word vs edge sequence).** Kingsford–Schatz–Pop, *BMC
  Bioinformatics* **11**:21, 2010, DOI `10.1186/1471-2105-11-21`: "The number of
  strings `Ω(G)` consistent with a de Bruijn graph `G` is related, but not equal
  to, the number of unique Eulerian circuits. There may be many more Eulerian
  circuits than solution strings … Parallel edges are more than a theoretical
  issue." [source fact, secondary] Hence §3.1's quotient by parallel-edge
  permutations is required; uniqueness of the Eulerian **edge sequence** is
  strictly stronger than uniqueness of the **spelled word**.

These are the strongest modern citable criteria for circular uniqueness, but
they are graph-theoretic and do **not** mention `P2`, Bresler repeats, or
triple/interleaved maximality.

### 3.3 The closest explicit *circular* theorem

**T. Ota, A. Manada**, *A Reconstruction of Circular Binary String Using
Substrings and Minimal Absent Words*, *IEICE Trans. Fund.* **E107-A**(3):
409–416, 2024, DOI `10.1587/transfun.2023TAP0015`. A necessary-and-sufficient
automaton/frequency condition for unique reconstruction of a **circular binary**
string. [source fact, secondary]

This is genuinely circular and multiset-based, but (i) it is binary-alphabet
only, (ii) its input includes **minimal absent words** in addition to substring
frequencies, so it is not a statement about the `L`-mer multiset alone, and
(iii) its condition is automaton-theoretic, not the `P2`/Bresler
triple-and-interleaved condition. It therefore cannot be cited as implying
Conjecture 4.

### 3.4 The cyclic variant is deliberately avoided in the reconstruction line

**S. Marcovich, E. Yaakobi**, *Reconstruction of Strings From Their Substrings
Spectrum*, *IEEE Trans. Inf. Theory* **67**(7):4369–4384, 2021 (arXiv:1912.11108),
Remark 2:

> "Note that by altering the definitions of multispectrum and `(L,d)`-substring
> distant strings to work with cyclic strings and cyclic multispectrum … the
> issues with the errors in the first and last `2t` entries … would have been
> solved. … However, we choose to use the acyclic definitions, since they model
> better the DNA sequencing problem."
> [source fact, secondary]

This is explicit evidence that the multiset-reconstruction community knows the
cyclic variant but does not develop it.

### 3.5 Terminological trap: "`k`-spectrum" is often the *set*

The indexing/large-`k` literature (e.g. SBWT, DOI `10.1101/2022.05.19.492613`)
defines the "`k`-spectrum" as the **set** of distinct `k`-mers. Theorems about
the set do **not** transfer to the multiset; the exact Medvedev–Brudno objective
depends on multiplicities. Any citation of "the `k`-spectrum determines the
word" must first be checked for set vs multiset. [analysis]

---

## 4. Does anything imply `P2 ⇒` circular `L`-spectrum uniqueness?

**No located source does.** The reasoning chain the repository needs, and where
each link stands:

| Link | Status |
| --- | --- |
| `P2(S)` ⇔ `S` is `I_s`-admissible (full read set) | **Mathematical fact** for the repository's own definitions (`mathematics/bridging-and-spectrum-uniqueness.md:70-78`) |
| Circular `L`-spectrum unique ⇔ `B(S)` has a unique Eulerian circuit modulo rotation and parallel edges | **Mathematical fact / standard**, grounded in Arratia et al. 2000 (§3.1) |
| "No triple/interleaved `(L−1)`-mer obstruction ⇒ unique Eulerian circuit" (circular Ukkonen–Pevzner) | **Gap**: linear only in all located sources; the circular form is folklore, not stated verbatim |
| `P2` excludes exactly the classical `(L−1)`-mer triple/interleaved obstructions | **Analysis**, not source; see the maximality mismatch below |
| `P2 ⇒` unique Eulerian circuit | **Repository conjecture**; not in the audited literature |

**The maximality mismatch (why the last two links are not free).** The classical
obstructions are stated at the exact `(L−1)`-mer level with the inequalities of
Ukkonen's conditions (2)/(3) (interleaved pairs, or three occurrences with
unequal intervening substrings). The repository's `P2`/Bresler predicates use a
*different* maximality notion: a triple repeat requires the three **preceding**
symbols not all equal **and** the three **following** symbols not all equal
(`docs/bridging-source-semantics.md:12-16`, from Bresler et al. 2013 Fig. 4,
p. 5). These are not the same condition:

- Bresler triple with following symbols not all equal ⇒ Ukkonen condition (3)
  (two of the intervening blocks start with different symbols, hence differ).
  [mathematical fact]
- The converse is **not** immediate: three occurrences of an `(L−1)`-mer with
  unequal intervening blocks need not have all three preceding (or following)
  symbols distinct in Bresler's sense. [analysis]

So "`P2` ⇔ no classical obstruction" is not established, and the direction
actually needed for Conjecture 4 (`non-unique spectrum ⇒ P2 fails`) has no
located proof. This is precisely the "careful circular-indexing check" flagged
in `docs/literature/substring-spectrum-identifiability-2026-09-20.md:88` and
`docs/source-notes/conclusion-semantics-equivalence-and-length.md:159-162`, and
it remains open.

**Computational evidence (not proof).** `scripts/bridging_spectrum_uniqueness.py`
re-run this audit: over `123 906` exhaustive `I_s`-admissible primitive genomes
(five parameter configurations, alphabets up to size 4, `G ≤ 15`) and `1 655`
randomized admissible genomes, **zero** ambiguous spectra. This is consistent
with Conjecture 4 but is a finite search, and its completeness is not proved
(per `AGENTS.md`).

---

## 5. The artificial prefix–suffix boundary after linearization

This is the specific hazard the audit was asked to address.

**Why the linear theorem cannot be applied to a linearization.**

1. **The linear `q`-gram profile depends on the cut.** For a circular `S`,
   linearize at position `0`, `W = S[0..G)`. The multiset `M_L(S)` has `G`
   windows (including the wrap window), whereas the linear profile of `W` has
   only `G−L+1` windows and omits the wrap window
   `S[G−L+1..G) + S[0..L−1)`. Two circular words with the same `M_L` can have
   different linear profiles (different wrap windows). So "equal circular
   multiset" is **not** "equal linear profile of a fixed linearization".
   [mathematical fact]
2. **`Rotation` is the boundary artifact.** Ukkonen's rotation move
   `z₁ y₁ z₂ y₂ z₁ → z₂ y₂ z₁ y₁ z₂` is available only because the linear word
   starts and ends with the same `(q−1)`-gram; it rearranges the word while
   preserving the linear profile. For a **closed** Eulerian circuit there is no
   start or end: the move reduces to the choice of initial vertex, i.e. a cyclic
   shift, which is by definition the same circular word. Thus the circular
   classification should be generated by **transpositions only** (triple and
   interleaved repeats), with `Rotation` quotiented out. Pevzner's/BEST's
   treatment of rotations as "the choice of initial vertex if the trail is
   closed" (Li–Xie, arXiv:cs/0507052 §2.1) supports this reading, but no located
   source states the resulting circular classification as a theorem.
   [source fact (secondary) + analysis]
3. **A genuine circular repeat can masquerade as a boundary event, and vice
   versa.** In the circle the prefix `(L−1)`-mer and suffix `(L−1)`-mer of a
   linearization are *adjacent* positions (separated by `G−(L−1)`), so a
   prefix = suffix match is a genuine repeated `(L−1)`-mer. A naive linear check
   can therefore either (a) invent a `Rotation` obstruction that is only the
   cyclic-shift identification, or (b) relocate a triple/interleaved structure
   that straddles the cut into a boundary shape and misclassify it. The safe
   formulation is to work on the **circle** and its de Bruijn **multigraph**
   (§3.1), with no distinguished origin. [analysis]

**Precise adaptation (stated as the repository's own claim, not as a citation).**
Define `CircUnique(S,L)` to mean `M_L` determines `S` up to cyclic shift. Then

```
CircUnique(S,L)
 ⇔ B(S) has a unique Eulerian circuit up to rotation and
   permutations of identically-labelled parallel edges
 ⇔ no "transposition obstruction" at the (L−1)-mer level
   (three occurrences of an (L−1)-mer, or two interleaved (L−1)-mer pairs,
    with unequal contexts).
```

The second equivalence is the **circular Ukkonen–Pevzner statement**. It is
well-motivated by the linear theorem plus the boundary analysis, but this audit
did not find it as a verbatim theorem in any English-language primary or
peer-reviewed source. Treating it as citable would overstate the literature.

---

## 6. Consequences for the repository's source-fidelity status

1. **Do not downgrade Conjecture 4** to "known source theorem". The classical
   theorem is linear; the circular form and the `P2` correspondence are not
   sourced. Keep Conjecture 4 as **conjecture** (with the finite evidence
   already recorded).
2. **Correct the citation in
   `docs/source-notes/conclusion-semantics-equivalence-and-length.md` §2.3**:
   the statement that two strings have the same `q`-gram profile iff connected
   by transpositions and rotations (Ukkonen/Pevzner) is a **linear** theorem;
   the `I_s` correspondence is the repository's analysis.
3. **Sharpen `docs/issue48-intrinsic-candidate-checks.md` §1/§5**: `SR`
   ("spectrum-resolvable") must not be described as resting on a circular
   "Ukkonen/Pevzner identifiability" theorem; the citable circular frame is the
   de Bruijn/Eulerian correspondence (§3.1) and the unique-circuit certificates
   (§3.2).
4. **If a citable circular statement is wanted**, the defensible citation set is
   §3 (Arratia et al. 2000; Pevzner 1989 via Waterman Thm 7.5; BEST; Obscura
   Acosta–Tomescu 2024; Ota–Manada 2024 as a nearby binary result), together
   with the linear Ukkonen/Pevzner theorem for the boundary story. The
   `P2 ⇒` unique-circuit step must be carried by the repository as a lemma to be
   proved, not cited.
5. **`P2` is the sharpest natural intrinsic predicate, but it is not obviously
   identical to the classical obstruction set** because of the maximality
   mismatch (§4). Any Lean formalization of Conjecture 4 should state the
   graph-theoretic version (§5) explicitly and prove the Bresler-to-`(L−1)`-mer
   correspondence rather than assume it.

---

## 7. Epistemic classification

| Claim | Status | Basis |
| --- | --- | --- |
| Ukkonen's two transformations and the completeness open question | **Source fact (primary, OCR)** | Ukkonen 1992, p. 194 |
| Ukkonen Thm 2.2 (at most one occurrence of each `(q−1)`-gram ⇒ unique) | **Source fact (primary, OCR)** | Ukkonen 1992, p. 193 |
| Pevzner 1995 proved the linear classification | **Source fact (secondary, multiple peer-reviewed)** | Jin–Kontorovich–Trachtenberg; Cenzato et al. 2025; Arratia et al. 2000 |
| Pevzner 1995 exact theorem number/wording | **Gap** | primary paywalled |
| Classical characterization is **linear** (Eulerian trails) | **Source fact (secondary)** | Mossel slides; Li–Xie; Cenzato et al. |
| `L`-mer multiset ↔ Eulerian circuits (parallel edges indistinguishable) | **Source fact (secondary) + mathematical fact** | Arratia et al. 2000 |
| Unique Eulerian circuit criteria | **Source fact (secondary)** | Pevzner 1989/Waterman; BEST; Obscura Acosta–Tomescu 2024 |
| No published explicit circular Ukkonen–Pevzner multiset classification found | **Gap (search result)** | this audit |
| `P2` Bresler-maximality ≠ classical intervening-substring inequalities in general | **Analysis / mathematical fact** | §4 |
| `P2 ⇒` circular spectrum uniqueness | **Conjecture (repository)**, not sourced | §§4–6 |
| `123 906` + `1 655` admissible genomes, 0 ambiguous | **Exact computation** | `scripts/bridging_spectrum_uniqueness.py`, re-run 2026-09-21 |
| Cyclic multispectrum deliberately avoided in the reconstruction line | **Source fact (secondary)** | Marcovich–Yaakobi 2021, Remark 2 |

---

## 8. References (audited)

1. E. Ukkonen. *Approximate string-matching with `q`-grams and maximal
   matches.* Theoret. Comput. Sci. 92(1):191–211, 1992.
   <https://doi.org/10.1016/0304-3975(92)90143-4> ;
   scanned PDF <https://www.cs.helsinki.fi/u/ukkonen/TCS92.pdf>
2. P. A. Pevzner. *DNA physical mapping and alternating Eulerian cycles in
   colored graphs.* Algorithmica 13(1–2):77–105, 1995.
   <https://doi.org/10.1007/BF01188582> (paywalled; not read directly)
3. P. A. Pevzner. *`l`-tuple DNA sequencing: computer analysis.* J. Biomol.
   Struct. Dyn. 7(1):63–73, 1989. <https://doi.org/10.1080/07391102.1989.10507752>
4. R. Arratia, B. Bollobás, D. Coppersmith, G. B. Sorkin. *Euler circuits and
   DNA sequencing by hybridization.* Discrete Appl. Math. 104(1–3):63–96, 2000.
   <https://doi.org/10.1016/S0166-218X(00)00190-6>
5. J. Jin, A. Kontorovich, A. Trachtenberg. *Determining the unique decodability
   of a string in linear time.* ITA 2013.
   <https://doi.org/10.1109/ITA.2013.6503005> ; arXiv:1204.3293
6. R. Cenzato, S. Franco, Zs. Lipták, S. Milanese. *The threshold `q`-gram
   distance…* Natural Computing, 2025.
   <https://doi.org/10.1007/s11047-025-10054-5>
7. N. Obscura Acosta, A. I. Tomescu. *Simplicity in Eulerian circuits:
   uniqueness and safety.* Inf. Process. Lett. 183:106421, 2024.
   <https://doi.org/10.1016/j.ipl.2023.106421> ; arXiv:2208.08522
8. T. Ota, A. Manada. *A Reconstruction of Circular Binary String Using
   Substrings and Minimal Absent Words.* IEICE Trans. Fund. E107-A(3):409–416,
   2024. <https://doi.org/10.1587/transfun.2023TAP0015>
9. S. Marcovich, E. Yaakobi. *Reconstruction of Strings From Their Substrings
   Spectrum.* IEEE Trans. Inf. Theory 67(7):4369–4384, 2021.
   arXiv:1912.11108
10. C. Kingsford, M. C. Schatz, M. Pop. *Assembly complexity of prokaryotic
    genomes using short reads.* BMC Bioinformatics 11:21, 2010.
    <https://doi.org/10.1186/1471-2105-11-21>
11. A. Çelikkanat, A. R. Masegosa, T. D. Nielsen. *Revisiting K-mer Profile for
    Effective and Scalable Genome Representation Learning.* NeurIPS 2024;
    arXiv:2411.02125. (Theorem 3.1 is a **secondary restatement for linear
    reads**; not evidence for a circular theorem.)
12. E. Mossel. *Shotgun Assembly of Labelled Graphs.* Simons Institute, 2016.
    <https://simons.berkeley.edu/sites/default/files/docs/4837/simonsmay2016.pdf>
    (lecture restatement; secondary)

---

## 9. Search provenance and gaps

- Instruments: web search plus direct retrieval; Ukkonen primary PDF OCR'd
  (image-only). Pevzner 1995 could not be read (paywalled, bot-challenged);
  its statement is reconstructed from peer-reviewed restatements only.
- **No Russian-language sources were consulted.**
- Open gaps: (i) Pevzner 1995 exact theorem/page; (ii) any English primary
  statement of the **circular** Ukkonen–Pevzner multiset classification;
  (iii) a citable statement of the `L`-mer-multiset ↔ unique-Eulerian-circuit
  equivalence as a single theorem (the components are citable, the composite is
  folklore); (iv) proof that `P2` coincides with the classical obstruction set.
- Repository-side computational evidence re-run and unchanged.
