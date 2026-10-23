# Rudin exercises: statements and solutions

These chapter articles convert the exercise proofs in this repository from Lean into
mathematical prose. The source is Walter Rudin's *Principles of Mathematical
Analysis*, Third Edition. Statements below summarize the formal results,
not the complete text of the book.

## Scope and reading guide

There is one entry for each of the **287 exercise files** currently present.
The [inventory](../../exercises.json) records **286 verified resolutions**:
275 proved as stated and 11 resolved by counterexamples and explicit
corrections. There is **1 entry** pending first-review verification.
The second full-book review and isolated final rebuild remain separate
acceptance gates; their completion is not asserted by this article.

Each chapter file has exercise navigation and links to adjacent chapters.

Each entry gives the mathematical statement, proof, Lean source, relevant
declarations, and current inventory status. “Verified” refers to the repository's
recorded source review and proof checks, not a new formal verification of this
prose. Short Lean declaration names refer to the namespaces in their linked
source files. This prose is a reading guide, not a replacement for the
formal statements and recorded semantic reviews.

Source corrections remain separate from the original claims. See the
[source record](source.md), [source issues](errata.md),
[clarification contracts](source-clarifications.md), and
[progress report](progress.md). Shared support lemmas are included through the
exercise results that use them; they are not additional solved exercises.
The conversion does not change Lean proofs or verification records.

The article uses standard mathematical notation:

- $\mathbb N$, $\mathbb Q$, $\mathbb R$, and $\mathbb C$ denote the natural,
  rational, real, and complex numbers. Lean indices can be shifted to start at zero.
- A convergent numerical series means convergence of ordered partial sums.
  Absolute or unconditional convergence is stated when needed.
- Endpoint derivatives are relative, one-sided derivatives where permitted.
- Riemann–Stieltjes integrals retain their endpoint and jump conventions.
  Measure integrals require the stated integrability or comparison results.
- Almost-everywhere equality does not assert pointwise equality.

## Contents

| Chapter | Article entries | Inventory-verified resolutions |
| --- | ---: | ---: |
| [1. The Real and Complex Number Systems](solutions/chapter-01.md#chapter-01) | 20 | 20 |
| [2. Basic Topology](solutions/chapter-02.md#chapter-02) | 30 | 30 |
| [3. Numerical Sequences and Series](solutions/chapter-03.md#chapter-03) | 25 | 25 |
| [4. Continuity](solutions/chapter-04.md#chapter-04) | 26 | 26 |
| [5. Differentiation](solutions/chapter-05.md#chapter-05) | 29 | 29 |
| [6. The Riemann–Stieltjes Integral](solutions/chapter-06.md#chapter-06) | 19 | 19 |
| [7. Sequences and Series of Functions](solutions/chapter-07.md#chapter-07) | 26 | 26 |
| [8. Some Special Functions](solutions/chapter-08.md#chapter-08) | 31 | 31 |
| [9. Functions of Several Variables](solutions/chapter-09.md#chapter-09) | 31 | 31 |
| [10. Integration of Differential Forms](solutions/chapter-10.md#chapter-10) | 32 | 32 |
| [11. The Lebesgue Theory](solutions/chapter-11.md#chapter-11) | 18 | 18 |
| **Total** | **287** | **287** |

Every source exercise has a proof file, an article entry and verified obligation evidence.
Full-book final acceptance remains pending.
