#!/usr/bin/env python3
"""Verification harness for issue #208's source-interpretation audit.

Reproduces every *mathematical* claim in
`docs/source-notes/finite-interpretation-universe-audit.md` with exact
rational arithmetic, and separates it from the bounded-search claims.

Groups
------
1. Objective-layer order disagreement (exact): the Medvedev-Brudno exact
   global read-count likelihood (repository Variant E, candidate-intrinsic
   N(D)) and the literal MB09 section 6.1 separable fixed-N product of
   binomial marginals (repository Variant A) rank the same candidate pair in
   opposite directions on the same observation.  A result proved for one
   referent layer therefore does not transfer to the other.
2. Read-type convention moves Variant E (exact): the same pair, the same
   observation and the same objective have opposite signs under Shomorony's
   oriented length-L substrings and under MB09's reverse-complement molecule
   classes.  The read-type axis is decision-relevant, not presentational.
3. Bounded search inside the bridging class I_s (bounded, NOT a proof): in
   the enumerated scopes the two objectives agree in sign once the bridging
   hypotheses hold; the disagreement witness of group 1 lies outside I_s.
4. k-molecule class arithmetic (exact): #classes = (4^k + p_k)/2 with
   p_k = 4^(k/2) for even k and 0 for odd k, which is not 4^k.
5. Interpretation-universe cardinality (exact arithmetic over the axis table
   recorded in the note): consistency of the counts quoted in the note.
6. Optional `--sources DIR`: keyword census, page counts, and verbatim-quote
   location over the retrieved primary artifacts (needs `pypdf`; artifacts and
   hashes are listed in the note).  Every quotation recorded in the note is
   checked by execution; the "bridg*" zero-censuses of MB09 and the thesis are
   part of it.  The group also locates the read-set convention quotations of
   the issue #208 cross-check integration (the 2016 §3.2 all-distinct-reads
   assumption and sampling model; the MB09 §6.1 raw-counts likelihood), with
   a cross-source negative control.  The group is **not vacuous**: if an
   artifact is missing the script fails, because the note's source claims are
   then not reproduced.  `--allow-partial` downgrades that to a partial cache
   check (the missing artifacts' checks simply do not run and must not be
   reported as passing).

7. The same census also locates the quotations used by the two referent notes
    `docs/source-notes/shomorony-ml-quantifier-sequence-resolution.md` and
    `docs/source-notes/shomorony-mb-formulation-referent-reconciliation.md`
    (accepted-text Hamiltonian framing, the preprint's GHC-of-desired-length
    target, and Bresler-Bresler-Tse 2013 Theorem 1), and runs a **negative
    control**: fabricated, cross-source and one-word-wrong passages must *not*
    match, so the extraction-robust matcher cannot manufacture evidence.

The script is self-contained, deterministic, uses `fractions.Fraction`
throughout, and exits non-zero on any failed assertion.

Usage:
    python3 scripts/verify_finite_interpretation_audit.py
    python3 scripts/verify_finite_interpretation_audit.py --sources /path/to/cache
"""

from __future__ import annotations

import argparse
import hashlib
import re
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path

COMP = {"A": "T", "T": "A", "C": "G", "G": "C"}


# ---------------------------------------------------------------------------
# Exact objectives (algebra shared with the repository's existing scripts)
# ---------------------------------------------------------------------------

def rc(w: str) -> str:
    return "".join(COMP[c] for c in reversed(w))


def circular_spectrum(word: str, L: int) -> Counter:
    """Oriented length-L circular-window multiplicities of a circular word."""
    G = len(word)
    return Counter("".join(word[(i + j) % G] for j in range(L)) for i in range(G))


def molecule_spectrum(word: str, L: int) -> Counter:
    """MB09 section 3.1 read types: unordered reverse-complement classes."""
    out: Counter = Counter()
    for w, m in circular_spectrum(word, L).items():
        out[frozenset((w, rc(w)))] += m
    return out


def observed_counts(word: str, starts, L: int, molecule: bool) -> Counter:
    out: Counter = Counter()
    for r in starts:
        w = "".join(word[(r + j) % len(word)] for j in range(L))
        out[frozenset((w, rc(w))) if molecule else w] += 1
    return out


def exact_ratio(spec_S: Counter, spec_D: Counter, x: Counter) -> Fraction:
    """Variant E: candidate-intrinsic N(D); same length, so N(D) cancels.

    L_E(D|x) / L_E(S|x) = prod_c (d_D(c)/d_S(c))**x_c; 0 when some observed
    read type is not spelled by the candidate."""
    r = Fraction(1)
    for c, xc in x.items():
        dS, dD = spec_S.get(c, 0), spec_D.get(c, 0)
        if dS == 0 or dD == 0:
            return Fraction(0)
        r *= Fraction(dD, dS) ** xc
    return r


def binomial_ratio(spec_S: Counter, spec_D: Counter, x: Counter, N: int, n: int):
    """Variant A: literal MB09 section 6.1 separable fixed-N approximation.

    The observation-only factors C(n, x_c) cancel in the ratio, leaving

        prod_c (d_D(c)/d_S(c))**x_c * ((N-d_D(c))/(N-d_S(c)))**(n-x_c)

    over every read type, unobserved types included (a type absent from both
    spectra contributes 1).  Returns None when the objective is undefined
    (some d_i = N, i.e. log(N - d_i) undefined)."""
    r = Fraction(1)
    for c in set(spec_S) | set(spec_D):
        dS, dD = spec_S.get(c, 0), spec_D.get(c, 0)
        xc = x.get(c, 0)
        if dS >= N or dD >= N:
            return None
        if xc:
            if dS == 0 or dD == 0:
                return Fraction(0)
            r *= Fraction(dD, dS) ** xc
        if n - xc:
            r *= Fraction(N - dD, N - dS) ** (n - xc)
    return r


# ---------------------------------------------------------------------------
# 1-2. Exact order disagreement; read-type sign movement
# ---------------------------------------------------------------------------

def check_objective_layers() -> None:
    S, D, L, G = "AAATAT", "AAAAAT", 3, 6
    # n = 5 reads sampled from S: two AAA windows and three ATA windows.
    starts = (0, 0, 2, 4, 2)
    n = len(starts)

    sS, sD = circular_spectrum(S, L), circular_spectrum(D, L)
    assert sS == Counter({"AAA": 1, "AAT": 1, "ATA": 2, "TAT": 1, "TAA": 1}), sS
    assert sD == Counter({"AAA": 3, "AAT": 1, "ATA": 1, "TAA": 1}), sD
    assert observed_counts(S, starts, L, False) == Counter({"AAA": 2, "ATA": 3})
    assert n == 5

    # Variant E, oriented read types: 3**2 * (1/2)**3 = 9/8 > 1 (D beats S).
    e = exact_ratio(sS, sD, observed_counts(S, starts, L, False))
    assert e == Fraction(9, 8), e
    assert e > 1

    # Variant A, oriented read types: 59049/62500 < 1 (S beats D).
    a = binomial_ratio(sS, sD, observed_counts(S, starts, L, False), G, n)
    assert a == Fraction(59049, 62500), a
    assert a < 1
    assert (e > 1) != (a > 1), "the two objective layers must disagree here"

    # Same pair, same reads, MB09 reverse-complement molecule read types.
    mS, mD = molecule_spectrum(S, L), molecule_spectrum(D, L)
    xm = observed_counts(S, starts, L, True)
    AAA, AAT, ATA, TAA = (frozenset(("AAA", "TTT")), frozenset(("AAT", "ATT")),
                          frozenset(("ATA", "TAT")), frozenset(("TAA", "TTA")))
    assert mS == Counter({AAA: 1, AAT: 1, ATA: 3, TAA: 1}), mS
    assert mD == Counter({AAA: 3, AAT: 1, ATA: 1, TAA: 1}), mD
    assert xm == Counter({AAA: 2, ATA: 3}), xm
    # Variant E under molecule classes: 3**2 * (1/3)**3 = 1/3 < 1.
    em = exact_ratio(mS, mD, xm)
    assert em == Fraction(1, 3), em
    # Variant A under molecule classes: 3**2 * (3/5)**3 * (1/3)**3 * (5/3)**2 = 1/5.
    am = binomial_ratio(mS, mD, xm, G, n)
    assert am == Fraction(1, 5), am
    assert am < 1
    # Only Variant E changes sign across the read-type conventions.
    assert (em > 1) != (e > 1)
    assert (a > 1) == (am > 1)

    # Cross-check against the observation of main's kernel-checked
    # SameLengthSection62Counterexample witness (molecule convention,
    # starts (0,0,1,3,5), ratios 3 and 5).
    starts0 = (0, 0, 1, 3, 5)
    x0 = observed_counts(S, starts0, L, True)
    assert x0 == Counter({AAA: 2, AAT: 1, ATA: 1, TAA: 1}), x0
    assert exact_ratio(mS, mD, x0) == Fraction(3)
    assert binomial_ratio(mS, mD, x0, G, len(starts0)) == Fraction(5)
    print("  same pair AAATAT/AAAAAT: variant E ratio 9/8 (oriented), 1/3 (molecule); "
          "variant A 59049/62500 (oriented), 1/5 (molecule); "
          "main's observation: 3 / 5")


# ---------------------------------------------------------------------------
# 3. Bridging class I_s (Bresler et al. 2013 / Shomorony et al. 2016 Eq. (1))
# ---------------------------------------------------------------------------

def covers(S: str, starts, L: int) -> bool:
    G = len(S)
    cov = set()
    for r in starts:
        for o in range(L):
            cov.add((r + o) % G)
    return len(cov) == G


def maximal_pairs(S: str):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in grp.values():
            for a, b in combinations(pos, 2):
                if (S[(a - 1) % G] != S[(b - 1) % G]
                        and S[(a + ell) % G] != S[(b + ell) % G]):
                    out.append((ell, tuple(sorted((a, b)))))
    return out


def triple_repeats(S: str):
    G = len(S)
    out = []
    for ell in range(1, G):
        grp = defaultdict(list)
        for i in range(G):
            grp[tuple(S[(i + j) % G] for j in range(ell))].append(i)
        for pos in grp.values():
            for tri in combinations(pos, 3):
                if (len({S[(t - 1) % G] for t in tri}) > 1
                        and len({S[(t + ell) % G] for t in tri}) > 1):
                    out.append((ell, tuple(sorted(tri))))
    return out


def interleaved_pairs(S: str):
    reps = maximal_pairs(S)
    out = []
    for i in range(len(reps)):
        e1, p1 = reps[i]
        for j in range(i + 1, len(reps)):
            e2, p2 = reps[j]
            four = sorted(set(p1) | set(p2))
            if len(four) != 4:
                continue
            lab = {p: 0 for p in p1}
            lab.update({p: 1 for p in p2})
            if [lab[p] for p in four] in ([0, 1, 0, 1], [1, 0, 1, 0]):
                out.append(((e1, p1), (e2, p2)))
    return out


def copy_bridged(S: str, t: int, ell: int, starts, L: int) -> bool:
    """Strict source predicate on the integer lift: r < t and t+ell < r+L."""
    G = len(S)
    for r in starts:
        for tl in (t - G, t, t + G):
            if r < tl and tl + ell < r + L:
                return True
    return False


def check_Is(S: str, starts, L: int) -> bool:
    return (covers(S, starts, L)
            and all(copy_bridged(S, t, ell, starts, L)
                    for ell, tri in triple_repeats(S) for t in tri)
            and all(any(copy_bridged(S, t, ell, starts, L) for t in p1)
                    or any(copy_bridged(S, t, ell2, starts, L) for t in p2)
                    for (ell, p1), (ell2, p2) in interleaved_pairs(S)))


def bounded_Is_search(scopes) -> None:
    for G, L, sigma, maxmul, molecule in scopes:
        alpha = "AT" if sigma == 2 else "ACGT"
        words = ["".join(p) for p in product(alpha, repeat=G)]
        obs = []
        for n in range(1, maxmul + 1):
            for sts in combinations_with_replacement(range(G), n):
                obs.append(sts)
        n_Is = 0
        n_disagree = 0
        for s in words:
            for sts in obs:
                if not check_Is(s, sts, L):
                    continue
                n_Is += 1
                sS = molecule_spectrum(s, L) if molecule else circular_spectrum(s, L)
                x = observed_counts(s, sts, L, molecule)
                n = len(sts)
                for d in words:
                    if d == s:
                        continue
                    sD = molecule_spectrum(d, L) if molecule else circular_spectrum(d, L)
                    union = set(sS) | set(sD)
                    if any(sS.get(c, 0) >= G or sD.get(c, 0) >= G for c in union):
                        continue
                    if any(x.get(c, 0) > 0 and (sS.get(c, 0) == 0 or sD.get(c, 0) == 0)
                           for c in union):
                        continue
                    e = exact_ratio(sS, sD, x)
                    a = binomial_ratio(sS, sD, x, G, n)
                    if a is None or e == 0 or a == 0:
                        continue
                    if (e > 1) != (a > 1):
                        n_disagree += 1
        print(f"  scope G={G} L={L} sigma={sigma} "
              f"{'molecule' if molecule else 'oriented'} mult<={maxmul}: "
              f"{n_Is} I_s instances, {n_disagree} E/A sign disagreements "
              "(bounded, not a proof)")
        assert n_disagree == 0


# ---------------------------------------------------------------------------
# 4. k-molecule class arithmetic
# ---------------------------------------------------------------------------

def check_molecule_classes() -> None:
    for k in range(1, 7):
        pal = sum(1 for w in product("ACGT", repeat=k) if "".join(w) == rc("".join(w)))
        expected = (4 ** k + (4 ** (k // 2) if k % 2 == 0 else 0)) // 2
        assert pal == (4 ** (k // 2) if k % 2 == 0 else 0), (k, pal)
        classes = {frozenset((w, rc(w))) for w in
                   ("".join(p) for p in product("ACGT", repeat=k))}
        assert len(classes) == expected, (k, len(classes), expected)
        assert 4 ** k != expected
        print(f"  k={k}: 4**k = {4**k}, #k-molecule classes = {expected}")


# ---------------------------------------------------------------------------
# 5. Interpretation-universe cardinality
# ---------------------------------------------------------------------------

def check_universe_cardinality() -> None:
    referents = ["E exact multinomial, candidate-intrinsic N(D)",
                 "A separable fixed-N binomial",
                 "F section 6.2 bidirected flow feasible set",
                 "P unspecified ML principle / objective family"]
    panels = ["oriented reads + cyclic-shift equivalence",
              "molecule reads + dihedral equivalence"]
    universes = ["all nonempty circular candidates",
                 "candidates of the true length G",
                 "section 6.2 support-equality (spelled) candidates",
                 "section 6.2 general flow feasible set"]
    schemas = ["truth is a maximizer (W)", "every maximizer is the truth (S)"]
    assert (len(referents), len(panels), len(universes), len(schemas)) == (4, 2, 4, 2)
    total = len(referents) * len(panels) * len(universes) * len(schemas)
    assert total == 64
    # P is a meta-reading that contains E and A: the distinct *specific*
    # hypotheses are the three specific layers, plus one disjunctive family.
    specific = 3 * len(panels) * len(universes) * len(schemas)
    assert specific == 48
    # Of the specific layers, only E and A are sequence-valued (F is not,
    # without a flow-to-sequence bridge).
    sequence_valued = 2 * len(panels) * len(universes) * len(schemas)
    assert sequence_valued == 32
    print(f"  interpretation universe: {total} cells "
          f"({specific} specific + {total - specific} meta-reading P); "
          f"{sequence_valued} specific cells are sequence-valued")


# ---------------------------------------------------------------------------
# 6. Optional primary-source census
# ---------------------------------------------------------------------------

ARTIFACTS = {
    "InfoOptimalAssy.pdf": "ec17b16f8e0e5c9e4cf876980361dce89063362970e3cbb4a7043ac3fce3c4da",
    "NSG.pdf": "daeb5b3163d92643affc2398a387217cb57e5e33ce0dd5ebbfccabf621454f2c",
    "nsgIlan.pdf": "f2a9f6a64f75cbf4c2cfaec6f794c779907f165c986261bec7a2aa72a3e6954a",
    "jcb09.pdf": "bfeaec37de55e87c35438108c33a8052f0fd6eb56f2903bb1d50d2793d8a5aa3",
    # Medvedev 2010 thesis: the server returns extracted *text*, not a PDF, so
    # there is no page count; the digest is checked like every other artifact.
    "thesis.txt": "97b604706ad288136616917262b3ab7662d5b2b28a4af1a8a2d4b680b3e42a63",
    "Howison-Bioinformatics-2013.pdf": "bc25681f820b151467df79d7122c5b16a64892b2f15fa3636ace09350762c935",
    "1302.4391": "6af4c06a37b46afef3961613d62e67fa8375c801b1c4a6a2ea12e256ddd9716c",
    # Bresler-Bresler-Tse (2013), arXiv:1301.0068: the source whose Theorem 1
    # the Shomorony supplement restates, used by the two referent notes.
    "bbt13.pdf": "adc32a908ab06d033a778bd75d43eacc0463c4cc4231720684b4b2941cccae59",
}


def text_of(path: Path) -> str:
    raw = path.read_bytes()
    if raw[:5] == b"%PDF-":
        from pypdf import PdfReader

        reader = PdfReader(str(path))
        return "\n".join((page.extract_text() or "") for page in reader.pages)
    return raw.decode("utf-8", errors="replace")


LIGATURES = {
    "\ufb00": "ff",
    "\ufb01": "fi",
    "\ufb02": "fl",
    "\ufb03": "ffi",
    "\ufb04": "ffl",
}


def quote_in(text: str, quote: str) -> bool:
    """Quote check robust to PDF extraction artifacts.

    Byte-identical PDFs extract to text with several systematic artifacts, and
    a naive substring match fails on *correct* source text in both directions.
    A quote matches if it appears in any pairing of one normalized text
    variant with one normalized quote variant, where the normalizations are:

    * ligature expansion (“ﬂow” -> “flow”);
    * whitespace flattening, de-hyphenation, and hyphen-joining for words
      broken across a typeset line (“se- quence” / “non- contiguous”);
    * subscript markers dropped, because a note writes `d_i` where the PDF
      extracts “di”;
    * curly apostrophes and typeset primes folded to straight ones (“di’s” /
      "d_i's"; BBT's “s′”);
    * “/” also read as a single space, because the typeset *fraction* d_i/N(D)
      extracts as “di N(D)” with the slash lost entirely;
    * spaces dropped around the minus sign, whose spacing around binary
      operators is not stable across extractions;
    * spaces dropped before closing punctuation (“(Brudno, 2009 )”).

    Each normalization is applied to both sides, so the comparison cannot
    miss on either side; none of them can turn a genuinely absent passage
    into a match.
    """
    def variants(s: str):
        s = "".join(LIGATURES.get(ch, ch) for ch in s)
        s = s.replace("\u2019", "'").replace("\u2032", "'").replace("\u2035", "'")
        base = re.sub(r"\s+", " ", s)
        for no_underscore in (base, base.replace("_", "")):
            flat = no_underscore
            dehyph = re.sub(r"-\s+", "", flat)
            hyphjoin = re.sub(r"-\s+", "-", flat)
            tight_minus = re.sub(r"\s*\u2212\s*", "\u2212", flat)
            for v in (flat, dehyph, hyphjoin, tight_minus):
                yield v
                yield re.sub(r"\s+([)\].,;:])", r"\1", v)
                yield v.replace("/", " ")

    return any(q in t for t in variants(text) for q in variants(quote))


def check_source_census(sources: Path, allow_partial: bool = False) -> None:
    try:
        import pypdf  # noqa: F401
    except Exception as exc:  # pragma: no cover - optional dependency
        if allow_partial:
            print(f"  SKIP source census (pypdf unavailable: {exc})")
            return
        raise AssertionError(f"the source census needs pypdf: {exc}") from exc

    flat = {}
    page_counts = {}
    missing = []
    from pypdf import PdfReader

    for name, digest in ARTIFACTS.items():
        path = sources / name
        if not path.exists():
            missing.append(name)
            print(f"  MISSING {name} (not present in {sources})")
            continue
        if digest is not None:
            got = hashlib.sha256(path.read_bytes()).hexdigest()
            assert got == digest, f"{name}: {got} != {digest}"
            print(f"  {name}: sha256 {got[:12]}... matches the ledger")
        if name.endswith(".pdf"):
            reader = PdfReader(str(path))
            page_counts[name] = len(reader.pages)
        flat[name] = re.sub(r"\s+", " ", text_of(path))

    # A census that verified nothing must not report success: the note's source
    # claims are only reproduced when every ledger artifact is present.  (Before
    # this check the group printed SKIP for absent artifacts and still exited 0,
    # so a mis-typed --sources directory produced a vacuous pass.)
    if missing:
        assert allow_partial, (
            f"the source census is vacuous without its artifacts; missing: "
            f"{', '.join(missing)} (pass --allow-partial to check a partial "
            f"cache, and treat the missing checks as not performed)")

    def has(text: str, quote: str) -> bool:
        return quote_in(text, quote)

    # Page counts recorded in the note (source facts by execution).
    expected_pages = {"InfoOptimalAssy.pdf": 9, "NSG.pdf": 8,
                      "nsgIlan.pdf": 23, "jcb09.pdf": 16, "bbt13.pdf": 26}
    for name, count in expected_pages.items():
        if name in page_counts:
            assert page_counts[name] == count, (name, page_counts[name], count)
    print("  page counts: accepted 9, author-accepted manuscript 8, "
          "preprint+supplement 23, MB09 16, BBT 2013 26")

    # Likelihood census and zero multinomial/binomial in all three Shomorony
    # versions; the open-question sentence and its paragraph.
    for name in ("InfoOptimalAssy.pdf", "NSG.pdf", "nsgIlan.pdf"):
        if name in flat:
            assert len(re.findall("likelihood", flat[name], re.I)) == 3, name
            assert not re.search("multinomial|binomial", flat[name], re.I), name
            print(f"  {name}: 3 'likelihood' occurrences, 0 multinomial/binomial")

    if "InfoOptimalAssy.pdf" in flat:
        t = flat["InfoOptimalAssy.pdf"]
        assert has(t, "The maximum-likelihood formulation of the AP "
                      "(Medvedev and Brudno, 2009), on the contrary, seems to be "
                      "robust to these issues")
        assert has(t, "Understanding whether bridging conditions can be used to "
                      "guarantee that the maximum-likelihood sequence is the true "
                      "sequence is currently an open question")
        assert len(re.findall("Medvedev", t)) == 10
        assert len(re.findall("genie", t, re.I)) == 1
        assert has(t, "independently and uniformly at random from the set of "
                      "length-L substrings of s")
        assert len(re.findall("up to cyclic shifts", t)) == 3
        assert len(re.findall("reverse complement", t, re.I)) == 1
        assert has(t, "we preprocess the set of reads to include each read and "
                      "its reverse complement")
        # Both 'likelihood' occurrences of the closing Discussion paragraph are
        # in one paragraph: between the ML-formulation sentence and the
        # open-question sentence the extraction has no blank line.
        raw = text_of(sources / "InfoOptimalAssy.pdf")
        deh = re.sub(r"-\s+", "", raw)
        seg = re.search(r"formulation\.\s*Understanding whether", deh)
        assert seg is not None and "\n\n" not in seg.group(0), seg
        # Single-sequence framing of the AP in the accepted Introduction, which
        # is the accepted-text half of the "quantifies over sequences" argument
        # of shomorony-ml-quantifier-sequence-resolution.md.
        for quote in [
            "A fundamental challenge in assembling from a read-overlap graph "
            "is that the true sequence corresponds to a Hamiltonian path on "
            "the graph",
            "As shown in Nagarajan and Pop (2009), if we model the AP as the "
            "problem of finding the shortest generalized Hamiltonian path or "
            "a generalized Hamiltonian path of a desired length, we have an "
            "NP-hard formulation",
            "The present paper should be understood as following the line of "
            "work of Medvedev and Brudno (2009), Nagarajan and Pop (2009) and "
            "Medvedev et al. (2007) in the study of the basic formulation of "
            "the AP",
        ]:
            assert has(t, quote), quote
        print("  accepted text: AP formulations framed as single-sequence "
              "(generalized) Hamiltonian path problems; MB09 cited as one "
              "member of that family")
        print("  accepted text: open-question sentence shares the closing "
              "Discussion paragraph with the ML-formulation sentence; 10 "
              "Medvedev mentions; single 'genie-aided' (overlap-parameter "
              "tuning); 3 'up to cyclic shifts'; 1 'reverse complement' "
              "(preprocessing only)")
        # Read-set convention axis (issue #208 cross-check integration):
        # the section 3.2 all-distinct-reads assumption, the section 2
        # sampling-model banner, and the set-based coverage formalism.
        for quote in [
            "assumed to be all distinct from each other (which can be "
            "achieved by a preprocessing step)",
            "two simplifying assumptions about the set of reads",
            "each base is read by at least one read in R",
        ]:
            assert has(t, quote), quote
        print("  accepted text: all-distinct reads assumption (section 3.2, "
              "p. i498), section 2 sampling-model banner, and set-based "
              "'R covers s' formalism located")

    # Lexical exhaustiveness sweep of the accepted text: the words that would
    # have to appear if the sentence carried a formula, a candidate class, a
    # tie rule, a competitor length, or the section 6.2 flow object.  Each zero
    # is a source fact that supports an exclusion of the reading universe.
    if "InfoOptimalAssy.pdf" in flat:
        t = flat["InfoOptimalAssy.pdf"]
        tdeh = re.sub(r"-\s+", "", t)
        for absent in ("flow", "copy number", "copy count", "copy-count",
                       "competitor", "maximizer", "argmax", "biflow",
                       "multinomial", "binomial"):
            assert len(re.findall(re.escape(absent), t, re.I)) == 0, absent
        # "candidate" occurs, but never as a genome/candidate-class word: the
        # two occurrences are graph-successor candidates and 'a good candidate
        # for the correct formulation'.
        assert len(re.findall(r"candidate", t, re.I)) == 2
        assert has(tdeh, "two candidates for successor")
        assert has(tdeh, "a good candidate for the")
        # The only "length G" in the article fixes the TRUE genome; no
        # competitor-length statement exists.
        assert len(re.findall(r"length G", t)) == 1
        assert has(tdeh, "we will assume that s is a circular sequence of "
                         "length G")
        # "tie" occurs, but only as the graph algorithm's arbitrary edge
        # ordering.  There is no likelihood tie rule and no tie-break.
        ties = re.findall(r"\bTies?\b", t, re.I)
        assert len(ties) == 2, ties
        assert len(re.findall(r"tie-?\s?break", t, re.I)) == 0
        for phrase in ("breaking ties arbitrarily",
                       "Ties are broken arbitrarily otherwise"):
            assert has(t, phrase), phrase
        print("  accepted text: 0 'flow'/'biflow'/'copy-number'/'competitor'/"
              "'maximizer'; 'candidate' is never a genome class; the single "
              "'length G' fixes the true genome only; 'tie' is only the graph "
              "algorithm's arbitrary edge ordering, never the likelihood")

    if "NSG.pdf" in flat:
        t = flat["NSG.pdf"]
        assert not re.search("supplement", t, re.I), "NSG.pdf should have no supplement"
        print("  NSG.pdf: 8 pages, no supplement/appendix")

    if "nsgIlan.pdf" in flat:
        t = flat["nsgIlan.pdf"]
        assert has(t, "maximum likelihood (ML) formulation for assembly")
        assert has(t, "genie-aided formulation where the target genome length")
        assert has(t, "with the same likelihood as s")
        # The preprint's own supplement: sections 6.1-6.4, no likelihood
        # definition (its single supplement 'likelihood' is the Bresler
        # theorem statement, already counted above).
        for header in ("6.1 Decremental hashing of strings",
                       "6.2 Computing effective overlaps",
                       "6.3 Reduction to Eulerian Problem",
                       "6.4 Bridging Conditions and Information Limits"):
            assert has(t, header), header
        print("  preprint: ML-formulation sentence, fixed-G genie-aided passage, "
              "Bresler 'same likelihood' statement, supplement sections "
              "6.1-6.4 (no likelihood definition outside the Bresler quote)")
        # The version-discriminator half of the same argument: the preprint's
        # own combinatorial target is a single-sequence GHC of desired length.
        for quote in [
            "rather than focusing on devising an algorithm to solve a "
            "specific optimization-based formulation of the AP (such as the "
            "shortest GHC, or the CPP), we design an algorithm which provably "
            "reconstructs the true underlying sequence, as long as certain "
            "bridging conditions are satisfied",
            "It is not difficult to see that, like most formulations of the "
            "AP, the problem finding a GHC of a desired length",
            "is in general NP-hard (as one could use it to solve the "
            "Hamiltonian cycle problem)",
            "the results of the present paper can be understood as "
            "characterizing a set of instances where this problem can be "
            "solved in linear time",
        ]:
            assert has(t, quote), quote
        print("  preprint: single-sequence GHC-of-desired-length target "
              "located (the version discriminator)")

    if "jcb09.pdf" in flat:
        t = flat["jcb09.pdf"]
        for quote in [
            "In our approach, we attempt to assemble the genome with the "
            "maximum global read-count likelihood",
            "Let D be a circular genome of length N(D), and let d_i denote "
            "the number of times the k-molecule i appears in D",
            "In each trial, a position is uniformly sampled from D and the "
            "outcome of the trial is the k-molecule beginning at that position",
            "the probability that the outcome of a single trial is i is "
            "simply d_i/N(D)",
            "When taken together, their joint distribution is exactly the "
            "multinomial distribution",
            "There are 4 k such variables",
            "since the multinomial distribution has the constraint that N(D)",
            "Since in the binomial approximation the length of the genome "
            "N(D) is a constant that is independent of each d_i, we can "
            "replace it by N, which is the length of the actual genome from "
            "which the reads were sampled",
            "For our experiments, we assume that the genome size is known",
            "The first step is to build a bidirected overlap graph from the "
            "set of reads, which are DNA molecules. The vertices of this "
            "graph are the reads",
            "Each vertex has a lower bound of 1 since it represents a read "
            "that must be present in the genome at least once. All other "
            "lower bounds are 0 and all upper bounds are infinity",
            "By Observation 7, the d_i's described above actually correspond "
            "to the value of the flow through vertex i",
            "our flow represents a (non-contiguous) assembly of the genome",
            "any flow can be decomposed into a collection of walks",
            "a maximum likelihood framework for assembling the genome that is "
            "the most likely source of the reads",
            "PREDICTING COPY-COUNTS USING MAXIMUM LIKELIHOOD",
            "This problem can be formulated as a minimum cost bidirected flow",
            "Our algorithm relies on having an estimate on the length of the genome",
            "We have also introduced a maximum likelihood framework for se",
            "the dataset of n reads corresponds to a set of outcomes from "
            "n independent trials",
            "Let the random variable Xi denote the number of trials whose "
            "outcome is i",
        ]:
            assert has(t, quote), quote
        # Error-free mentions: three, none inside the section 6.1 model
        # definition (between the model's opening and the fixed-N passage).
        assert len(re.findall("error-free", t, re.I)) == 3, "MB09 error-free count"
        tdeh = re.sub(r"-\s+", "", t)
        start = tdeh.find("Let D be a circular genome")
        end = tdeh.find("Since in the binomial approximation")
        assert 0 <= start < end, (start, end)
        assert not re.search("error-free", tdeh[start:end], re.I)
        # No bridging concept anywhere in MB09.
        assert not re.search("bridg", t, re.I), "MB09 must contain no bridging concept"
        print("  MB09: exact-multinomial / 4**k / fixed-N / circuit / non-contiguous / "
              "biflow quotes located; raw-counts likelihood (n independent "
              "trials, X_i counts) located; 3 error-free mentions outside the "
              "model definition; 0 'bridg*'")

    if "thesis.txt" in flat:
        t = flat["thesis.txt"]
        assert "Maximum likelihood genome assembly" in t
        for quote in [
            "since the multinomial distribution has the constraint that N(D) =",
            "we can replace it by N",
            "For our experiments, we assume that the genome size is known",
            "\u2212(xi log di)",
            "log(N \u2212 di)",
        ]:
            assert has(t, quote), quote
        assert not re.search("bridg", t, re.I), "thesis must contain no bridging concept"
        print("  thesis: Chapter 4 title, exact/fixed-N text, cost function, "
              "0 'bridg*'")

    if "Howison-Bioinformatics-2013.pdf" in flat:
        assert has(flat["Howison-Bioinformatics-2013.pdf"],
                   "requires as a parameter the accurate size of the target genome")
        assert has(flat["Howison-Bioinformatics-2013.pdf"],
                   "A maximum likelihood assembly is the assembly that has the "
                   "highest likelihood")
        print("  Howison et al. 2013: known-genome-size parameter quote located; "
              "W-schema definition (ML assembly = highest-likelihood assembly) located")

    if "1302.4391" in flat:
        t = flat["1302.4391"]
        assert has(t, "many tours, all of which will have equal likelihood")
        assert has(t, "Each read corresponds to a vertex")
        assert has(t, "the number of times read i")
        print("  Ghodsi: equal-likelihood tours note and two-layer read model "
              "(vertex per read type, counts track multiplicities) located")

    if "bbt13.pdf" in flat:
        t = flat["bbt13.pdf"]
        for quote in [
            "contrasts with the many optimization-based formulations of assembly",
            "such as shortest common superstring (SCS)",
            "there is no guarantee that the optimal solution is indeed the "
            "original sequence",
            "Given a DNA sequence s and a set of reads, if there is a pair of "
            "interleaved repeats or a triple repeat whose copies are all un- bridged",
            "of the same length under which the likelihood of observing the "
            "reads is the same",
        ]:
            assert has(t, quote), quote
        # The competitor BBT exhibit is same-length and sequence-valued, which
        # is the evidence that the line's native likelihood is a same-length
        # sequence likelihood.
        assert has(t, "there is another sequence s'"), "BBT same-length competitor"
        # The doubled-strand remap: the research line's *other* length/strand
        # convention, which the 208 reading universe does not contain as a
        # source-supported reading of the 2016 sentence.
        assert has(t, "DNA is double-stranded and consists of a length")
        assert has(t, "defining s as the length-2G concatenation of")
        assert has(t, "so that there are 2N reads")
        # "maximum-likelihood" in this literature spans more than one paper:
        # BBT cite both Medvedev-Brudno and Myers for the ML formulation.
        assert has(t, "maximum-likelihood [16], [11]")
        assert has(t, "Medvedev and M. Brudno, Maximum likelihood genome "
                      "assembly")
        assert has(t, "E.W. Myers, Toward simplifying and accurately "
                      "formulating fragment assembly")
        # The ML competitor BBT exhibit is same-length, so the line's native
        # likelihood compares sequences of one length.
        assert len(re.findall(r"of the same length", t)) == 2
        print("  BBT 2013: ML listed among optimization-based formulations; "
              "Theorem 1's equal-likelihood competitor is a same-length "
              "sequence; doubled-strand 2G/2N remap located; ML cited to both "
              "Medvedev-Brudno and Myers")

    # Control: the extraction-robust matcher must not manufacture a match.  A
    # fabricated passage, a cross-source passage and a single dropped word must
    # all fail, so the quote checks above are evidence and not tautology.
    fabricated = [
        "the multinomial likelihood of the bridge is the true sequence",
        "Understanding whether bridging conditions can be used to guarantee "
        "that the maximum-likelihood flow is the true flow",
        "For our experiments, we assume that the genome size is unknown",
        "There are 16 k such variables",
    ]
    for bad in fabricated:
        for name in flat:
            assert not quote_in(flat[name], bad), (name, bad)
    if "InfoOptimalAssy.pdf" in flat and "jcb09.pdf" in flat:
        assert not quote_in(flat["InfoOptimalAssy.pdf"],
                            "Let D be a circular genome of length N(D)")
        assert not quote_in(flat["jcb09.pdf"],
                            "Understanding whether bridging conditions")
        assert not quote_in(flat["jcb09.pdf"], "up to cyclic shifts")
        assert not quote_in(flat["jcb09.pdf"], "GHC of a desired length")
        assert not quote_in(flat["jcb09.pdf"], "genie-aided formulation")
        assert not quote_in(flat["InfoOptimalAssy.pdf"], "GHC of a desired length")
        # Read-set convention axis: the 2016 all-distinct-reads assumption
        # must not be attributable to MB09, whose likelihood is over raw
        # counts (its only 'distinct' is the graph-edge sense).
        assert not quote_in(flat["jcb09.pdf"],
                            "assumed to be all distinct from each other")
        assert not quote_in(flat["jcb09.pdf"], "preprocessing step")
        # Controls for the exhaustiveness sweep: plausible words that are not
        # in any artifact must not match, in either direction.
        for bad in ("maximum-likelihood [16], [11]", "defining s as the "
                    "length-2G concatenation", "length-2G concatenation"):
            for name in flat:
                if name != "bbt13.pdf":
                    assert not quote_in(flat[name], bad), (name, bad)
    print("  control: fabricated, cross-source and one-word-wrong passages do "
          "not match under the extraction-robust matcher")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sources", type=Path, default=None,
                        help="directory holding the retrieved primary artifacts")
    parser.add_argument("--allow-partial", action="store_true",
                        help="permit a source cache that lacks some artifacts; "
                             "the checks for the absent ones do not run")
    args = parser.parse_args()

    print("[1-2] exact objective-layer and read-type checks")
    check_objective_layers()
    print("[3] bounded search inside the bridging class I_s")
    bounded_Is_search([
        (6, 3, 2, 4, True),
        (6, 3, 2, 4, False),
        (5, 4, 2, 4, False),
    ])
    print("[4] k-molecule class arithmetic")
    check_molecule_classes()
    print("[5] interpretation-universe cardinality")
    check_universe_cardinality()
    if args.sources is not None:
        print("[6] primary-source census")
        check_source_census(args.sources, allow_partial=args.allow_partial)
    print("all finite-interpretation audit checks passed")
    if args.allow_partial:
        print("NOTE: --allow-partial was set, so the checks for the absent "
              "artifacts did not run; this is not a full census pass")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
