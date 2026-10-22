# Source

The exercise source is Walter Rudin, *Principles of Mathematical Analysis*,
Third Edition (1976).

- Primary local file: `data/Rudin - 1976 - Principles of Mathematical Analysis (International Series in Pure & Applied Mathematics).pdf`.
- SHA-256: `c0d8530ad52ff06bb3b949b4b27245c446cde045e70b3efcad0cd51804e938e7`.
- PDF length: 351 pages.
- Alternate local scan: `data/Walter Rudin - Principles of Mathematical Analysis.pdf`.
  Its title page also identifies the Third Edition. The scans have not been
  compared page by page.
- Page references in `exercises.json` are one-based. In the exercise sections,
  PDF page = printed book page + 9.
- The primary scan has an OCR layer. Formulas and exercise numbers can be wrong
  in extracted text. Page images are the authority for disputed text.
- Source review methods are recorded per exercise. An OCR review is not a
  claim that the image was checked or that the Lean translation was reviewed.
- Local PDFs, extracted chapter text, and rendered images are not committed.
  The repository contains original summaries and formal statements.

## Inventory review

The current inventory has 287 exercise IDs and 847 obligations. The obligation
count includes lettered parts, unlettered questions, required constructions, and
explicit dispositions of problematic source claims. The initial inventory had
839 obligations. The second batch added eight explicit domain, termination,
endpoint, literal-order, diameter and degree-zero checks, justified in
`source-clarifications.md`; the number of source exercises did not change. All exercise-section page
images were checked across three inventory workers; the main agent checked PDF
page 30 separately. This review does not establish that every formal theorem
matches its source. Proof-specific semantic review is recorded separately.

Rudin Definition 6.1 (book page 120, PDF page 129) permits weakly increasing
partition nodes. Definitions 6.1–6.2 and Exercise 6.1 do not exclude a singleton
interval. The formal partition model must not silently impose strict nodes or
`a < b` on that exercise.

## Exercise sections

| Chapter | Exercises | Book pages | PDF pages |
| --- | --- | --- | --- |
| 1 | 1–20 | 21–23 | 30–32 |
| 2 | 1–30 | 43–46 | 52–55 |
| 3 | 1–25 | 78–82 | 87–91 |
| 4 | 1–26 | 98–102 | 107–111 |
| 5 | 1–29 | 114–119 | 123–128 |
| 6 | 1–19 | 138–142 | 147–151 |
| 7 | 1–26 | 165–171 | 174–180 |
| 8 | 1–31 | 196–203 | 205–212 |
| 9 | 1–31 | 239–244 | 248–253 |
| 10 | 1–32 | 288–299 | 297–308 |
| 11 | 1–18 | 332–334 | 341–343 |
