# Search manifest: 26 August 2026

This is the contemporaneous query manifest supporting
[`LITERATURE_SEARCH.md`](../../LITERATURE_SEARCH.md). Searches were run by Codex
with AI-assisted screening under the project maintainer's direction. Result
counts are observations from 26 August 2026 in the America/Los_Angeles time
zone; database contents and ranking can change.

The manifest records queries and counts, not raw third-party database exports.
It does not represent that the maintainer personally reran each query or read
each candidate in full.

## arXiv

Interface: [arXiv advanced search](https://arxiv.org/search/advanced)

| Query | Observed result |
| --- | ---: |
| `all:"Weak Partition Principle" AND (all:"New Foundations" OR all:NFU)` | 0 relevant records |
| `all:"Partition Principle" AND (all:"New Foundations" OR all:NFU)` | 0 relevant records |
| `all:WPP AND (all:"New Foundations" OR all:NFU)` | 0 relevant records |
| `(ti:"New Foundations" OR abs:"New Foundations") AND all:choice` | Broader candidate set screened; no exact result found |

The broader NF search was also checked against `Quine`, `NFU`, `choice`,
`partition`, `surjection`, and `injection`. The plausible recent works are
listed with dispositions in the parent report.

## zbMATH Open

Interface: [zbMATH Open](https://zbmath.org/)

Queries:

```text
"New Foundations" py:2023-2026
NFU py:2023-2026
"Partition Principle" py:2023-2026
"Weak Partition Principle" py:2023-2026
ti:WPP py:2023-2026
```

The deduplicated union of the recent NF and NFU result sets contained 19
records. Each record was screened by title and abstract; plausible records were
inspected in available full text. The PP-only query returned general ZF choice
work and terminological false positives. Neither the exact WPP query nor the
WPP-title query produced a competing NF result.

## OpenAlex

Interfaces: [OpenAlex search](https://openalex.org/) and the
[OpenAlex Works API](https://developers.openalex.org/api-reference/works/list-works)

Exact title/abstract intersections were checked for:

```text
"Weak Partition Principle" AND "New Foundations"
"Weak Partition Principle" AND NFU
"Partition Principle" AND "New Foundations"
WPP AND ("New Foundations" OR NFU)
```

Observed exact NF/WPP result: **0 records**.

Forward-citation filters used a publication-date lower bound of 1 January 2023
and an upper bound of 26 August 2026:

| Citation parent | Stable identifier | Post-2023 records returned | Screening result |
| --- | --- | ---: | --- |
| Specker, not-AC in NF (1953) | [OpenAlex W1976151458](https://openalex.org/W1976151458), DOI `10.1073/pnas.39.9.972` | 5 | None proves or claims `NF ⊢ ¬WPP`. |
| Forster, choice in universal-set theories (1985) | DOI `10.2307/2274324` | 0 | No recent citing candidate. |
| da Silva, WPP and PP (2021) | DOI `10.1093/jigpal/jzaa023` | 0 | No recent citing candidate. |

The five Specker-citing records included NF/NFU and general-foundations work;
all were screened by title and abstract and plausible items were inspected more
closely.

## Crossref

Interface: [Crossref Metadata Search](https://search.crossref.org/)

Combined searches used:

```text
"Weak Partition Principle" "New Foundations"
"Partition Principle" "New Foundations"
"Weak Partition Principle" NFU
"New Foundations" choice
NFU choice
```

The first 100 ranked records across these combined searches were screened. The
sole plausible recent candidate was Adlešić and Čačić's 2023 NFU cardinal-
squaring paper, which works in `NFU + Inf + AC` and does not prove a result over
classical NF. The other results were general ZF choice literature or lexical
false positives.

## Semantic Scholar

Interface: [Semantic Scholar](https://www.semanticscholar.org/)

Exact and variant searches used:

```text
"Weak Partition Principle" "New Foundations"
"Partition Principle" "New Foundations"
WPP NFU
"New Foundations" choice
```

Observed exact NF/WPP result: **0 records**. Broader results duplicated the
candidate families recorded in the parent report or were unrelated uses of the
initialisms `NF` and `WPP`.

## Specialist NF resources

The [Holmes–Forster bibliography](https://randall-holmes.github.io/Bibliography/setbiblio.html),
whose page states a 2025 revision date, was searched as a whole and by its
2023–2026 entries using:

```text
weak partition
partition principle
choice
surjection
injection
```

No exact WPP result was located. The bibliography itself warns that some
private, unpublished, or not-yet-listed NF material exists; that limitation is
preserved in the parent report.

The [MathOverflow NF choice thread](https://mathoverflow.net/questions/81577/new-foundations-and-weaker-forms-of-choice)
was checked through its 2024 updates. The Forster answer concerns PP rather than
WPP. A separate claim of `NF + PP` consistency was withdrawn, and Holmes's later
answer about countable choice and dependent choice does not resolve WPP.

## Metamath

The immutable upstream reference used by the formalization is
[`nf.mm` at commit `c1814c4fbaf88d329d7d73ec1c7358647570e435`](https://github.com/metamath/set.mm/blob/c1814c4fbaf88d329d7d73ec1c7358647570e435/nf.mm).
That source, current `develop/nf.mm`, and 23 file-touching commits since 1
January 2023 were inspected for:

```text
WPP
weak partition
partition principle
surjection
injection
```

No upstream not-WPP theorem was found. The WPP endpoint formalized by this
repository is in the separately identified project-authored Metamath extension,
not upstream `nf.mm`.

## Screening standard

Records were first screened by title, abstract, and metadata. Plausible
candidates were checked in available full text for an exact WPP result, an
equivalent injection/surjection statement, or a stronger classical-NF theorem.
The record-by-record judgments were AI-assisted. Candidate dispositions and the
audit's limitations are recorded in `LITERATURE_SEARCH.md`.
