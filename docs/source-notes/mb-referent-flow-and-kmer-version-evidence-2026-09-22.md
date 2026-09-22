# Medvedev–Brudno referent: flow-identification and k-mer/k-molecule version evidence

_Status: focused primary-source addendum for issue #36, 2026-09-22, written
against `origin/main` at `2efd560`. It adds two citable findings to the
provenance trace
[`shomorony-mb-formulation-provenance.md`](shomorony-mb-formulation-provenance.md)
and the reconciliation
[`mb-formulation-referent-reconciliation.md`](mb-formulation-referent-reconciliation.md),
which it does not revise. It does not select a referent, does not settle the
published question, and does not change any witness. Every claim is labelled
**source fact**, **mathematical fact**, **interpretation**, or **source gap**._

_Reproduction:_ `python3` with `pypdf` extracting
`http://www.cs.utoronto.ca/~brudno/medvedev_brudno_short.pdf`
(11 pages, conference version); quotations below were located in that
extraction and cross-checked against the web-search-extracted JCB text. No
repository predicate or search script was used.

## 1. Finding A: Medvedev–Brudno identify the ML problem with the flow problem in their own words

**Source fact.** Conference version, §1 (Introduction), verbatim from the
extraction:

> "We formulate the problem of genome assembly as maximizing the likelihood of
> the observed read frequencies, rather than minimizing the length of the
> genome. This problem can be formulated as a minimum cost bidirected flow
> (biflow) problem with convex costs …"

The JCB full text carries the same sentence (§1.2, "We formulate the problem
of genome assembly as maximizing the likelihood of the observed read
frequencies … This problem can be formulated as a minimum cost bidirected flow
(biflow) problem with convex costs"). The §6.1/§6.2 structure is the same in
both versions: §6.1 ("Maximizing the global read-count likelihood") defines
the exact multinomial and then the separable/binomial approximation with
external known `N`; §6.2 ("Putting it all together") builds the transitively
reduced bidirected read-overlap graph and solves the convex min-cost biflow
with vertex costs `c_i`, vertex lower bound 1, and supersource/supersink
penalties.

**Interpretation.** This is the strongest primary-text support yet for reading
(3) (§6.2 flow) as a *formulation* rather than a mere algorithm: the authors
themselves write "this problem can be formulated as" a biflow problem. It cuts
against the formulation-vs-algorithm split recorded in the provenance note §3
(preprint "ML formulation" vs "algorithms to find the ML sequence") and §6.4
(§6.2 as "MB's algorithm, not the formulation"), which remain valid
observations about Shomorony's vocabulary but are no longer the only authorial
signal. It does **not** promote reading (3) to a source fact about the 2016
sentence: Shomorony still gives no section pointer, and §6.2 returns a flow
("a (non-contiguous) assembly") while the 2016 sentence asks about "the
maximum-likelihood sequence," so the sequence-vs-flow type gap identified in
the reconciliation §4 still stands.

## 2. Finding B: the short version is oriented k-mer; the JCB version is k-molecule — read-type underdetermination across versions

**Source fact.** Conference version, §2.3 ("Maximizing the Global Read-Count
Likelihood"), verbatim from the extraction:

> "Let G be a circular genome of length N(G), and let g_i denote the number of
> times the k-mer i appears in G."

> "There are 4^k such variables …"

Both the object (`k-mer i`) and the count (`4^k`) are oriented: `4^k` is the
number of oriented length-`k` strings. There is no reverse-complement
identification in this passage.

**Source fact.** The JCB full text §6.1 instead writes `d_i` for "the number of
times the k-molecule i appears in D" while keeping the sentence "There are
`4^k` such variables." A `k`-molecule is defined (§3.1) as an unordered
reverse-complement pair ("each k-molecule … only once"), whose class count is
`(4^k + p_k)/2`, not `4^k`. The JCB text is therefore internally inconsistent
about the index set, as already recorded in the conclusion-semantics
determination §2.3 and the candidate-semantics audit §4.3.

**Interpretation.** The version comparison proves the read-type ambiguity is
not an artifact of one inconsistent sentence: the *earlier* authorial version
is coherently oriented (`k-mer`, `4^k`), and the *later* journal version moves
the vocabulary to molecules while retaining the oriented count. No available
Shomorony passage selects between them — the 2016 main text contains zero
occurrences of `multinomial`/`binomial`/`molecule` and never names `k` — so a
formalization that fixes oriented vs molecule read types is making a choice
the combined primary sources do not determine. This is orthogonal to the
length and flow axes: it changes the spectrum map `D ↦ d(D)` (hence which
candidates tie) without changing the candidate-object class (circular
sequences).

## 3. Bearing on the four readings

| Reading | Effect of findings A–B |
|---|---|
| (1) exact multinomial, candidate-intrinsic `N(D)` | Unchanged: named ideal in both versions ("maximum global read-count likelihood"); explicitly abandoned as not separable in both versions. |
| (2) fixed-`N` binomial over circular candidates | Unchanged as the operative sequence-level objective; finding B shows its index set (oriented `4^k` vs molecule classes) is version-dependent. |
| (3) §6.2 biflow | **Strengthened as a formulation-candidate** by finding A (authors' own "can be formulated as"); still blocked as a direct sequence-level referent by the flow-vs-sequence type gap (reconciliation §4, candidate-semantics audit §4.2/§5). |
| (4) broad ML principle | Unchanged: still the safest literal reading of the uncited 2016 sentence. |

## 4. What this does not claim

1. It does not resolve which object the 2016 sentence intends; the sentence
   still carries no section/equation pointer.
2. It does not change the witness-sufficiency matrix: the same-length strict
   witnesses still refute readings (1)–(2) over circular candidates by
   candidate-set inclusion, and still do not touch reading (3) without a
   flow→sequence bridge.
3. It does not inspect the accepted publisher supplement (HTTP 403); a
   likelihood or tie definition there is still not excluded.

## 5. Epistemic classification

| Claim | Status | Basis |
|---|---|---|
| MB authors write the ML problem "can be formulated as" a min-cost biflow | **source fact** | short version §1; JCB §1.2 |
| Short version §2.3 uses oriented `k-mer` with `4^k` variables | **source fact** | extraction quotes above |
| JCB §6.1 uses `k-molecule` with the same `4^k` count | **source fact** | JCB §6.1; molecule definition §3.1 |
| Read-type choice is underdetermined across the combined sources | **interpretation** | A–B plus zero disambiguating 2016 occurrences |
| Reading (3) gains formulation-level support but keeps the sequence-type gap | **interpretation** | A plus reconciliation §4 |

Primary sources: P. Medvedev, M. Brudno, _Ab Initio Whole Genome Shotgun
Assembly with Mated Short Reads_, conference version, §§1–2.3
(`http://www.cs.utoronto.ca/~brudno/medvedev_brudno_short.pdf`); P. Medvedev,
M. Brudno, _Maximum Likelihood Genome Assembly_, J. Comput. Biol. 16(8)
(2009) 1101–1116, §§1.2, 3.1, 6.1–6.2, 7; I. Shomorony et al.,
_Information-optimal genome assembly via sparse read-overlap graphs_,
Bioinformatics 32(17) (2016) i494–i502, §5.
