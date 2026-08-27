# Literature search for prior proofs of `NF ⊢ ¬WPP`

**Search completed:** 26 August 2026  
**Coverage cutoff:** 26 August 2026  
**Status:** bounded search of publicly accessible literature

## Conclusion

The search documented below located no proof of the exact mathematical result
`NF ⊢ ¬WPP` independent of this project. On this evidence, the project claims
the result as novel to the best of its knowledge.

This is a documented literature-search conclusion, not a proof of an
unrestricted negative. In particular, the search cannot exclude private
communications, unpublished or unindexed manuscripts, inaccessible mailing-list
archives, or prior work stated using terminology not identified below.

## Exact claim searched

The claim is syntactic derivability of the negation of the Weak Partition
Principle from standard first-order New Foundations:

```text
NF ⊢ ¬WPP.
```

Here `NF` is extensionality together with the full stratified-comprehension
schema. In the exact Metamath source spelling used by this repository, WPP says
that for all sets `x` and `y`, if a function from `y` onto `x` and a one-to-one
function from `y` to `x` both exist, then a one-to-one function from `x` to `y`
exists. The formal source is the `df-wpp` expansion preserved in
`provenance/metamath/accepted-translator-input.mm`; the public Lean statement is
`NFNotWPP.NF_proves_not_WPP`.

The search distinguishes:

- the Weak Partition Principle (WPP) from the stronger Partition Principle
  (PP);
- NF from NFU, intuitionistic NF, and extensions of NF or NFU;
- novelty of the mathematical result from novelty of its Lean translation; and
- the project-authored Metamath extension from the upstream Metamath `nf.mm`
  database.

Under the standard definitions, `PP → WPP`; see Howard and Rubin's Forms 100
and 101 and da Silva's modern treatment cited below. Consequently,
`NF ⊢ ¬WPP` mathematically also gives `NF ⊢ ¬PP`. The compared Lean declaration
states not-WPP; this repository does not claim a separate compared PP
declaration. Thomas Forster's 2023 MathOverflow answer concerns whether PP is
consistent with NF; it does not mention WPP by name. It is therefore historical
evidence concerning a stronger neighboring question, rather than the sole
evidence for novelty of the exact WPP result.

## Priority reference point

This audit asks whether an exact proof **independent of this project** was
located by the coverage cutoff. It does not use the repository's first Git
commit as the discovery date: Holmes's 13 August 2026 working note already
credits the result's underlying work to this project, while the repository's
initial recorded commit is dated 24 August 2026. The note is therefore a
project-dependent acknowledgment, not independent prior art. Because the
project does not claim a separately archived timestamp for the initial
discovery, the conclusion is consistently limited to the absence of a located
independent proof.

## Method

The search combined four procedures:

1. exact-phrase and terminology-variant searches in general mathematical
   indexes;
2. a subject search for identifiable NF and NFU work from 2023 through the
   coverage cutoff, followed by AI-assisted record-by-record screening of the
   returned candidate set;
3. backward and forward citation chasing from the principal NF choice and WPP
   sources; and
4. inspection of specialist NF resources, current formal libraries, and public
   expert discussions.

Records were screened by title and abstract; plausible candidates were then
inspected in available full text. Searches also used keywords, bibliographies,
and source-code text. Candidate dispositions record the resulting assessment
of whether a work proves or claims the exact result, an equivalent result, or a
stronger result over classical NF. Search strings and observations below are
recorded as they appeared on 26 August 2026; mutable database results may change
later.

The audit was prepared by Codex with AI-assisted web and database searching
under the project maintainer's direction. The candidate exclusion judgments are
AI-assisted; this record does not represent that the maintainer personally
reproduced every query or read every candidate in full. This file supplies links
and candidate dispositions so that the bibliographic conclusions can be checked
independently.

## Search log

The following query families were run in
[arXiv](https://arxiv.org/search/advanced), [zbMATH](https://zbmath.org/),
[OpenAlex](https://openalex.org/),
[Crossref](https://search.crossref.org/),
[Semantic Scholar](https://www.semanticscholar.org/), and general web search,
with syntax adjusted to each service:

```text
"Weak Partition Principle"
"Weak Partition Principle" AND ("New Foundations" OR NF OR NFU)
"Partition Principle" AND ("New Foundations" OR NFU)
(WPP OR "weak partition") AND ("New Foundations" OR NFU)
(surjection OR onto) AND injection AND "New Foundations"
(choice OR cardinal OR partition) AND "New Foundations"
ACwo AND (NF OR "New Foundations")
```

For the recent-period subject screen, the principal zbMATH queries were:

```text
"New Foundations" py:2023-2026
NFU py:2023-2026
"Partition Principle" py:2023-2026
"Weak Partition Principle" py:2023-2026
```

The observations were:

| Resource | Scope and observed result on 2026-08-26 | Disposition |
| --- | --- | --- |
| arXiv | The three exact combined searches recorded in the query manifest returned 0 relevant records; the broader NF/choice search was screened. | No independent proof found. |
| zbMATH | The deduplicated union of the 2023–2026 NF and NFU result sets contained 19 records; all were screened. | No independent proof found. |
| OpenAlex | Exact title/abstract searches returned 0 NF/WPP records; the forward-citation results described below were screened. | No independent proof found. |
| Crossref | The first 100 ranked results across the combined WPP/PP and NF/NFU searches were screened; the NFU cardinal-squaring paper was the sole plausible candidate. | No classical-NF proof found. |
| Semantic Scholar | Exact combined searches returned 0 relevant NF/WPP records. | No independent proof found. |
| MathOverflow | The NF and choice discussion and related WPP/PP searches were examined. | The 2023 answer concerns PP, not WPP by name. |
| Holmes–Forster bibliography | The specialist bibliography as a whole and its 2023–2026 entries were searched for choice, partition, WPP, surjection, and injection terminology. | No competing result found. |
| Metamath `nf.mm` | The pinned source, current source text, and 23 file-touching commits since 2023 were searched for WPP, weak partition, and partition-principle results. | Upstream contains Specker-style not-AC material but no WPP theorem. |

The service-specific query spellings, result counts, citation parents, and
Metamath revision points are retained in the
[dated search manifest](literature-search/2026-08-26/SEARCH_MANIFEST.md).

Exact-phrase zero results are useful but not decisive: `WPP` is ambiguous, and
an equivalent theorem need not use the customary name. The broader subject and
citation screens were included for that reason.

## Principal literature examined

The historical baseline was not limited to the three years following the 2023
MathOverflow answer. It included:

- Ernst Specker, "The Axiom of Choice in Quine's New Foundations for
  Mathematical Logic," *PNAS* 39 (1953),
  [doi:10.1073/pnas.39.9.972](https://doi.org/10.1073/pnas.39.9.972). This proves
  the failure of full choice in NF, not the exact not-WPP result.
- Thomas Forster, "The Status of the Axiom of Choice in Set Theory with a
  Universal Set," *Journal of Symbolic Logic* 50 (1985),
  [doi:10.2307/2274324](https://doi.org/10.2307/2274324), and *Set Theory with a
  Universal Set* (2nd ed., 1995).
- M. Randall Holmes, *Elementary Set Theory with a Universal Set*, the standard
  NFU-oriented reference, together with the current NF pages and drafts linked
  from [Holmes's homepage](https://randall-holmes.github.io/).
- Paul Howard and Jean Rubin, *Consequences of the Axiom of Choice*, Forms 100
  and 101, covering WPP and PP.
- B. Banaschewski and R. Moore, "The Dual Cantor–Bernstein Theorem and the
  Partition Principle," [doi:10.1305/NDJFL/1093635502](https://doi.org/10.1305/NDJFL/1093635502).
- M. Higasikawa, "Partition Principles and Infinite Sums of Cardinal Numbers,"
  [doi:10.1305/NDJFL/1040149358](https://doi.org/10.1305/NDJFL/1040149358).
- Samuel G. da Silva, "The Axiom of Choice and the Partition Principle from
  Dialectica Categories," *Logic Journal of the IGPL* 29 (2021),
  [doi:10.1093/jigpal/jzaa023](https://doi.org/10.1093/jigpal/jzaa023), for the
  modern WPP terminology and injection/surjection formulation.
- The [Holmes–Forster bibliography of set theory with a universal
  set](https://randall-holmes.github.io/Bibliography/setbiblio.html), whose last
  stated revision was in 2025, and the current
  [Metamath New Foundations Explorer](https://github.com/metamath/set.mm/blob/develop/nf.mm).

No source in this baseline was found to contain `NF ⊢ ¬WPP` or an equivalent
classical-NF theorem.

## Recent NF and NFU literature screened

The following are the most plausible recent candidates found by the broad
2023–2026 subject search. This table records why each was not treated as prior
art for the submitted theorem.

| Work | Reason examined | Disposition |
| --- | --- | --- |
| Adlešić and Čačić, "The Cardinal Squaring Principle and an Alternative Axiomatization of NFU" (2023), [doi:10.18778/0138-0680.2023.25](https://doi.org/10.18778/0138-0680.2023.25) | Recent cardinal and choice-related work. | Concerns `NFU + Inf + AC`; it does not prove the exact classical-NF result. |
| Pireva, *Ambiguity in Typed Set Theory and the Axiom of Counting* (2023), [doi:10.26686/wgtn.24463606](https://doi.org/10.26686/wgtn.24463606) | Recent NF/NFU dissertation citing the historical choice literature. | No WPP result was found. |
| Rouvelas, "Cantorian Models of Predicative NF" (2024), [doi:10.1017/jsl.2022.75](https://doi.org/10.1017/jsl.2022.75) | Recent NF model theory. | Predicative NF models, not a WPP theorem over full NF. |
| Bowler and Forster, "Internal Automorphisms and Antimorphisms of Models of NF" (2025), [doi:10.1017/jsl.2024.47](https://doi.org/10.1017/jsl.2024.47) | Recent work involving symmetry and weak-choice phenomena. | No `NF ⊢ ¬WPP` result was found. |
| Forster and Holmes, "Synonymy Questions Concerning the Quine Systems" (2025), [doi:10.1017/jsl.2024.85](https://doi.org/10.1017/jsl.2024.85) | Major recent work about NF and related systems. | Concerns interpretation and synonymy, not WPP. |
| Ryan-Smith, "Stratified Formulas Are Not Context-Free" (2025), [doi:10.1215/00294527-2024-0040](https://doi.org/10.1215/00294527-2024-0040) | Recent work on the defining syntax of NF. | Not a choice-principle result. |
| Holmes and Wilshaw, "NF is Consistent," revised 2025, [arXiv:1503.01406](https://arxiv.org/abs/1503.01406) | The principal recent NF result and its Lean formalization. | Establishes consistency; no WPP result was found. |
| Sevilla Simón, "On the consistency of NF via Fuzzy Forcing" (2025), [arXiv:2504.14400](https://arxiv.org/abs/2504.14400) | Independent recent NF consistency work. | Establishes consistency; no WPP result was found. |
| Beeson, "Finite sets, mappings, cardinals, and arithmetic in intuitionistic New Foundations" (2026), [doi:10.60866/CAM.290](https://doi.org/10.60866/CAM.290) | Current NF paper involving mappings, injections, surjections, and cardinals. | Concerns intuitionistic NF and finite-cardinal arithmetic, not WPP over classical NF. |

Forster and Holmes's 2025
[Possible Thesis Topics in NF](https://thomasedwardforster.github.io/thesistopics.pdf)
was also examined as a current specialist research agenda. Its section on weak
choice principles treats substantial choice questions in NF as continuing
research and does not report an exact WPP refutation. This is corroborating
context, not proof by itself that the WPP result was previously unknown.

## Citation-trail checks

Forward citations were checked for three natural starting points:

- Specker's 1953 not-AC paper;
- Forster's 1985 paper on choice in universal-set theories; and
- da Silva's 2021 WPP/PP paper.

On 26 August 2026, OpenAlex returned five post-2023 records citing Specker's
paper and no post-2023 records citing either Forster's 1985 paper or da Silva's
2021 paper. All five Specker-citing records were screened; none claimed or
proved `NF ⊢ ¬WPP`. Backward references in the plausible recent candidates were
also checked against the principal sources above.

Citation indexes are incomplete and can lag new publications. These counts are
dated observations, not completeness guarantees.

## Public discussion and post-discovery corroboration

In a [2023 MathOverflow answer](https://mathoverflow.net/a/449571/109573),
Thomas Forster reported that consistency of PP with NF was not known. A later
claim in the same discussion that `NF + PP` was consistent was expressly
withdrawn in 2024. Because `PP → WPP`, the theorem in this repository shows
that `NF + PP` is inconsistent. The discussion does not independently establish
that the exact WPP theorem was open.

The same MathOverflow page was checked through its later updates. Holmes's April
2024 answer reports that the constructed NF models satisfy countable choice and
dependent choice; this supplies useful context about weaker choice in NF but
does not resolve WPP.

Holmes's [current homepage](https://randall-holmes.github.io/) and associated
[August 2026 working note](https://randall-holmes.github.io/Drafts/acwo2.pdf)
publicly credit work by Elliot Glazer's project as the source of a related NF
failure-of-choice result concerning choice from well-ordered partitions. This
acknowledgment arose after the project's discovery and is recorded as
corroboration of attribution and significance, not as evidence that the exact
WPP theorem had previously appeared, not as prior art independent of the
project, and not as a substitute for the database search.

## Limitations and correction policy

This audit is limited by:

- database coverage, indexing lag, OCR quality, and access restrictions;
- terminology changes and the possibility of an equivalent result stated only
  in cardinal-arithmetic notation;
- private correspondence, unpublished drafts, and incompletely public NF
  mailing-list archives;
- sources in languages or repositories not surfaced by the listed searches;
  and
- the distinction between establishing a formal implication and recording it
  explicitly as a named theorem.

The intended claim is therefore bounded: **as of 26 August 2026, the documented
search found no independent prior proof in the publicly accessible literature
of the exact result `NF ⊢ ¬WPP`.** Corrections and pointers to omitted prior art
are welcome and should be reported through the repository's public issue
tracker.
