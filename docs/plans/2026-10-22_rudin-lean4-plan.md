# Lean 4 Formalization Plan for All Rudin Exercises

## Goal

Use Lean 4 and Mathlib to complete all end-of-chapter exercises in Walter Rudin's *Principles of Mathematical Analysis*, Third Edition, in `data/`. Include all subparts, counterexamples, classifications of conditions, and constructions required by the exercises.

"Complete" means that the exercise interpretation has been reviewed, the answer is complete, the Lean kernel has checked the proof, and the result can be rebuilt in a clean environment with pinned versions. If the original statement is false, deliver a formal counterexample and a clearly labelled corrected version. Do not add hidden conditions or try to prove a false proposition.

The user has authorized execution of this plan. Implement batches in exercise dependency order. Use subagents for parallel inventory, solutions, and independent review. Keep tasks open until valid completion evidence is available.

## Context

### Source Materials and Project Baseline Confirmed During Planning

- Primary source: `data/Rudin - 1976 - Principles of Mathematical Analysis (International Series in Pure & Applied Mathematics).pdf`.
  - 351 PDF pages. The title page states Third Edition, and the copyright page includes 1976.
  - SHA-256: `c0d8530ad52ff06bb3b949b4b27245c446cde045e70b3efcad0cd51804e938e7`.
  - An OCR text layer is available, but it has recognition errors in exercise numbers, superscripts, subscripts, inequality signs, and integral symbols.
- Comparison source: `data/Walter Rudin - Principles of Mathematical Analysis.pdf`.
  - Also 351 pages. Page images confirm Third Edition on the title page. No usable text layer is available.
  - The two scans have not been compared page by page. Do not assume that all pages are identical.
- `lean-toolchain` pins `leanprover/lean4:v4.35.0`.
- `lakefile.toml` has only the `Math` library and `math` executable, with no Mathlib dependency.
- `Math/Basic.lean`, `Math.lean`, and `Main.lean` are Hello World templates, with no existing exercise proofs.
- `.github/workflows/lean_action_ci.yml` uses `leanprover/lean-action@v1`, with no exercise coverage or axiom checks yet.
- `lake build` succeeded for the template during planning. This does not show that analysis infrastructure is available.
- `.gitignore` already excludes `data/` and `.lake/`. Do not commit textbook PDFs, full-book OCR text, or page images.

### Inventoried Scope

Three subagents checked the complete exercise sections and page images for Chapters 1–4, 5–8, and 9–11, respectively. The main agent also checked PDF page 30. `exercises.json` currently records 287 exercises and 849 obligations, including follow-up questions and source-issue dispositions. The initial 839 obligations gained eight explicit checks in the second batch, R03E14's zero-bound strict-estimate obstruction in the fourth batch, and the printed R06E02 comparison in the seventh batch. Evidence is in `docs/rudin/source-clarifications.md`. This is the source-inventory denominator, not the number of completed solutions. If omitted obligations are found later, update the denominator with source evidence.

| Chapter | Topic | Exercise Range | Book Pages | PDF Pages, 1-Based |
| --- | --- | --- | --- | --- |
| 1 | The Real and Complex Number Systems | 1–20 | 21–23 | 30–32 |
| 2 | Basic Topology | 1–30 | 43–46 | 52–55 |
| 3 | Numerical Sequences and Series | 1–25 | 78–82 | 87–91 |
| 4 | Continuity | 1–26 | 98–102 | 107–111 |
| 5 | Differentiation | 1–29 | 114–119 | 123–128 |
| 6 | The Riemann–Stieltjes Integral | 1–19 | 138–142 | 147–151 |
| 7 | Sequences and Series of Functions | 1–26 | 165–171 | 174–180 |
| 8 | Some Special Functions | 1–31 | 196–203 | 205–212 |
| 9 | Functions of Several Variables | 1–31 | 239–244 | 248–253 |
| 10 | Integration of Differential Forms | 1–32 | 288–299 | 297–308 |
| 11 | The Lebesgue Theory | 1–18 | 332–334 | 341–343 |

### Identified Interpretation Risks

- `R01E19`: Book page 23 requires a sphere radius `r > 0` but does not exclude `a = b`. Handle the degenerate case separately. Do not silently add `a ≠ b`.
- `R11E18`: Book page 334 states Schwarz equality as the existence of a constant `c` such that `g = c f` almost everywhere. The case `f = 0` and `g ≠ 0` needs separate treatment.
- Both exercises now have Lean counterexamples, corrected versions, and independent interpretation reviews. Each is marked `refuted_and_corrected` in the inventory. This does not mean that the original propositions were proved.
- Other source questions remain pending in `exercises.json` and `progress.md`. Completion of these two exercises does not establish that other statements are correct.

### First Execution Batch (2026-10-22)

- Verified 8/287 exercise resolutions and 23/839 obligations: 6 exercises proved as stated and 2 completed with counterexamples and corrected versions. There are 279 exercises and 816 obligations remaining.
- `./scripts/check.sh` passed: inventory/import/declaration checks, default build, axiom checks for 211 declarations, and 23 regression tests.
- Rebuilt the first batch in an isolated project source copy with fresh project build outputs, reusing only the pinned dependency cache. This is not full-book `--final` acceptance.
- `./scripts/check.sh --final` still fails correctly on incomplete obligations. The full-book completion gate is not waived. Remote CI has not run.
- Current verification status, source/dependency-environment fingerprints, and per-exercise review evidence are in `exercises.json`. The summary is in `docs/rudin/progress.md`. This plan is incomplete and must be retained.

### Second Execution Batch (2026-10-22)

- Completed the remaining 18 exercises in Chapter 1. All 20/20 exercises and 55/55 obligations in the chapter are verified. The book total is 26/287 exercises and 72/847 obligations: 24 proved as stated and 2 resolved with counterexamples and corrections. There are 261 exercises and 775 obligations remaining.
- Completed source-issue discovery: 15 exercises with 18 issues have explicit contracts. Added 8 domain/convention/obstruction obligations that were not previously tracked separately. No original obligations were removed. The related mathematical proofs remain todo/pending. Selection of a contract does not count as a completed solution.
- Added Stieltjes common refinement, sum bounds, full Darboux/tagged equivalence, continuous-integrand existence for raw monotone integrators, and an explicit right-continuous measure bridge. Also added restricted raw ordered-chain boundary infrastructure. See `mathlib-coverage.md` for all scopes and incomplete comparisons.
- `./scripts/check.sh` and checks in an isolated source copy with fresh project build outputs passed: 538 declarations, 104 delivery references, and 23 regression tests. Only the pinned dependency cache was reused.
- `./scripts/check.sh --final` still fails at `R02E01.empty_subset`, an incomplete full-book obligation. The final gate is not waived. Remote CI has not run. This plan is incomplete and remains retained.

### Third execution batch (2026-10-22)

- Completed the remaining 29 exercises in Chapter 2. The chapter now has 30/30 verified resolutions and 71/71 verified obligations. The book total is 55/287 resolutions and 142/847 obligations; 232 exercises and 705 obligations remain open.
- Of the 55 resolutions, 52 prove the source claim as stated and 3 retain a refutation and explicit correction. The third correction is the bounded-only reading of R02E29. Its extended interval convention is stated separately. R02E28 preserves Rudin's countably-infinite convention; its empty-set check is a translation check, not a source erratum.
- Every new exercise passed independent page-to-type review, single-file compilation, default project build, coverage and origin checks, and the proof-body axiom audit. The full current audit covers 991 local declarations and 185 delivery references. All 23 regression tests pass.
- Added a boundary-stable orientation quotient, fixed-degree boundaries, affine face comparisons, signed square/cube identities, and actual parameterized-square/Möbius seam multiplicities. Independent model checks prove infinite-order generators and retained seam multiplicity. General smooth simplex chains, geometric orientation/coverage, form integration and comparison with Rudin remain open; P3 is not complete.
- An isolated source copy ran `lake exe cache get` and `./scripts/check.sh` successfully with fresh project outputs, reusing only the pinned dependency cache. The cache confirmed all 9031 entries. This is batch validation, not full-book acceptance.
- `./scripts/check.sh --final` still fails correctly at `R03E01.absolute_values`. Remote CI has not run. This plan remains active and must be retained.

### Fourth execution batch (2026-10-22)

- Completed the remaining 24 exercises in Chapter 3. The chapter now has 25/25 resolutions and 89/89 obligations. The book total is 79/287 resolutions and 223/848 obligations; 208 exercises and 625 obligations remain open.
- Added one source-backed obligation for R03E14(e): the printed strict estimate fails for the allowed bound `M=0`. The constant-sequence obstruction, non-strict correction and strict `M>0` result are proved. The final Tauberian converse remains valid. All ten original obligations remain.
- Of the 79 resolutions, 75 are as stated and 4 retain a refutation/correction. R03E06 separates undefined parameters from divergence. R03E18 retains the inherited square-root starting bound and the possible first-step overshoot. Ordinary conditional series are not replaced by unconditional `Summable` assumptions.
- Independent page/type reviews cover every new obligation. Default project checks and an isolated-source rebuild pass for 1356 local declarations, 280 delivery references and 23 regression tests. The isolated copy ran `lake exe cache get`, `lake build`, and `./scripts/check.sh` with fresh project outputs and only the pinned dependency cache reused.
- The first integration audit rejected generated unsafe recursion helpers in the three Newton iterations. Explicit `Nat.rec` definitions and safe equations remove them. Final independent review and the unchanged strict project gate pass; no exception was added.
- `./scripts/check.sh --final` still fails correctly at `R04E01.symmetric_difference_converse`. Remote CI has not run. General Chapter 10 integration infrastructure and all remaining chapters stay open; this plan is retained.

### Fifth execution batch (2026-10-22)

- Completed Chapter 4: 26/26 resolutions and 74/74 obligations. The book total is 105/287 resolutions and 297/848 obligations; 182 exercises and 551 obligations remain open. Of the completed resolutions, 101 are as stated and 4 retain refutations/corrections.
- Every new exercise has independent page-to-type review, compilation and current project evidence. Includes all affine-line counterexamples, explicit Cauchy-sequence extension, rational triples for all simple discontinuities, literal Thomae values, complete-range cases, extended-diameter conventions and required compact-subsequence arguments. R04E09's convention is resolved without a source-refutation count.
- Added real Stieltjes algebra, absolute-value existence/bounds and full interval joining/restriction with raw endpoints. Added genuine path-quotient integration, actual exterior-derivative comparison and a source-Darboux boundary identity. Independent review passed both modules, with 30 and 22 additional model checks respectively. No Chapter 6 or general Chapter 10 exercise is counted complete from infrastructure alone.
- `./scripts/check.sh` and an isolated-source rebuild pass: 1692 local declarations, 367 delivery references and 23 regression tests. The isolated copy ran cache retrieval, the default build and the shared check entry point with fresh project outputs. All nine dependency checkouts match the locked revisions and have clean worktrees.
- `./scripts/check.sh --final` still fails correctly at `R05E01.constant`. Remote CI has not run. Products/complex Stieltjes integrands, improper limits, general smooth simplex integration and higher-dimensional Stokes remain open. This plan remains active.

### Sixth execution batch (2026-10-22)

- Completed Chapter 5: 29/29 resolutions and 84/84 obligations. The book total is 134/287 resolutions and 381/848 obligations; 153 exercises and 467 obligations remain open. Of the completed resolutions, 128 are as stated and 6 retain obstructions/refutations and corrections.
- Independent source/type/body reviews cover every new obligation. Closed-interval derivatives remain one-sided. Genuine derivative jets prevent default-zero higher-derivative shortcuts. Includes all seven sharp oscillatory thresholds, exact Landau suprema and vector bounds, actual fixed-point orbits and diagrams, full Newton termination corrections, and complete forward square-root ODE classification and system uniqueness.
- R05E13 retains the printed negative-base obstruction and proves the explicitly labelled absolute-power correction. R05E25 retains the affine termination counterexample, absorbing iteration and separate zero-curvature estimates. A follow-up review verifies that R05E24's two comment changes clarify scalar side reversal without changing any proof or contract.
- Added continuous composition and product existence for raw Stieltjes integrals, plus actual complex tagged sums, component equivalence, norm integrability/bounds, algebra and full interval splitting. Independent reviews include 35 and 33 model checks. General discontinuous-integrand measure comparisons, vector integrands, improper integration and integration by parts remain open.
- Current project and isolated-source checks pass: 2241 local declarations, 504 delivery references and 23 regression tests. The isolated copy retrieved the locked cache, rebuilt fresh project outputs, and ran the shared check entry point. All nine dependency revisions match the manifest and have clean worktrees. These audit counts include R06E02, which remains in_progress and is not counted complete.
- `./scripts/check.sh --final` still fails correctly at `R06E02.vanishing`. Remote CI has not run. Chapter 6 work has started; Chapters 7–11 and the remaining geometric infrastructure stay open. This plan remains active.

### Seventh and eighth execution checkpoint (2026-10-22)

- Completed Chapter6 (19/19 exercises,54/54 obligations), Chapter7 (26/26,79/79), and Chapter8 Exercises1–10 (21 obligations). The book total is188/287 resolutions and533/849 obligations;99 exercises and316 obligations remain open. There are181 as-stated resolutions and7 explicit corrections.
- All new resolutions passed independent page/type/private-body review. Chapter6 includes complex raw integration by parts, conditional improper integrals and actual partition lengths. R06E18 retains the reciprocal obstruction and uniquely forced endpoint extension; it is counted as corrected. Chapter7 includes the full safe Euler-polygon construction, actual raw Riemann identities, a constructed Ascoli subsequence and Euclidean vector existence. A failed Exercise8 finite-sum continuity proof was replaced and independently rechecked.
- Added Bochner-only uniform-integral helpers, genuine smooth simplex pullbacks/integrability, and full parameter-triangle Stokes for globally C1 forms/C2 maps. The nonhorizontal value1 and nonlinear value1/3 have literal zero-extension and actual-edge Darboux witnesses. Independent reviews and30 model checks pass. General smooth-chain orientation, arbitrary-dimensional source comparison, source-neighborhood regularity and general Stokes remain open; full P3 is not complete.
- The frozen full-project gate passed for3479 local declarations and752 references. Its isolated source copy retrieved the pinned cache, rebuilt fresh project outputs and passed the same gate with the final763 references and23 regressions. The first isolated copy omitted the unchanged template `Math/Basic.lean`; adding that required source and rerunning both commands resolved the failure. Only the final passing run is acceptance evidence.
- The isolated checkpoint contains the exact sources of the passing gate, not later unfinished Chapter8/9 files. Active proof work is now beyond that checkpoint; new files remain in_progress until their independent and shared gates pass. This is not a full-book or current-unfinished-tree final acceptance claim.
- The objective remains all287 exercises and849 obligations, the second full-book semantic review and an isolated `--final` rebuild. No commit or remote CI was run. This plan remains active.

### Ninth execution checkpoint (2026-10-22)

- Completed Chapter 8 (31/31 exercises, 79/79 obligations) and Chapter 9 (31/31, 110/110). The inventory now verifies 239/287 resolutions and 700/849 obligations: 231 as stated and 8 explicit corrections. Chapter 10–11 work remains open.
- Every new obligation has independent primary-page/type/private-body review and matching source-closure hashes. Fourier work includes raw Riemann transport, actual kernels, localization and prescribed Fejer/Tauberian arguments. Winding and disc fixed-point proofs retain the explicit approximants and quadratic ray construction. Chapter 9 includes genuine implicit graphs, exact singular-curve classifications and actual Taylor multi-index counting.
- R09E19 resolves the local-branch convention without a refutation count. R09E31 retains actual matching-jet counterexamples and independently checked local C3 corrected tests; it is counted as refuted/corrected. The E09 empty-domain omission found in review was repaired and independently rebuilt.
- The root gate passed for 5175 local declarations, 1147 references and 23 regressions. The isolated checkpoint `.lake/rudin-batch09-isolated-491aolm2` retrieved the pinned cache, rebuilt fresh project outputs and passed the shared gate for 5094 declarations, the same 1147 references and 23 regressions. All 290 recorded input hashes and nine dependency revisions/worktrees matched. It predates the later E11.07 and Chapter 10 additions; its inventory still had the pre-verification status labels. This is a completed-source checkpoint, not full-book acceptance.
- `MultivariateRiemann.lean` passed independent review and both checkpoint gates. It proves real scalar box/simplex source comparisons in arbitrary dimension, all coordinate orders, Euclidean normalization and standard-simplex volume. General oriented smooth-chain integration and Stokes remain open. New Chapter 10–11 deliveries stay unverified until their separate reviews and gates pass.
- The second full-book semantic review and isolated `--final` gate remain mandatory. No commit or remote CI was run. This plan remains active.

### Tenth execution checkpoint (2026-10-22)

- Verified Chapter 11 Exercises 2–17 and Chapter 10 Exercise 30 after independent primary-source/type/private-body reviews and the passing default project gate. Chapter 11 is complete at 18/18 resolutions and 37/37 obligations. The inventory now records 256/287 resolutions and 734/849 obligations: 248 as stated and 8 corrected. R11E11 resolves the source's almost-everywhere quotient convention; it is not an additional source refutation.
- R11E07 gives a genuine a.e. raw-mass oscillation criterion, inward jump conditions, endpoint corrections and the full identity-integrator equivalence. It does not claim an off-jump discontinuity-set equivalence for arbitrary integrators.
- The default gate passed for 6054 local declarations, 1280 then-mapped references and all 23 regression tests. Newly accepted references were already in its proof-body audit and were separately checked for theorem kind and origin by the reviewers. Coverage and generated progress passed after metadata integration. This is not an isolated full-book or final acceptance gate.
- `SmoothChains` passed independent review within its stated partial scope. The permutation-only quotient can retain two-torsion and is not the older repeated-vertex quotient. General analytic `SimplexStokes` is compiled and root-integrated; its independent review and higher-degree integral descent remain separate work.
- Independent review found that R11E15's first extension obstruction covered only nonnegative functions. The source permits signed extended-real extensions. Main added the signed `EReal` obstruction, literal four-interval classification and real-charge comparisons. A new independent reviewer checked the adopted additions and all remaining Chapter 11 obligations: five fresh modules, 144 local declarations, 42417 transitive declarations, exact origins and independent signed/boundary models passed. Their frozen hashes match the passing project gate.
- Chapter 10 affine/coordinate/exterior-algebra deliveries remain in progress pending independent review. Convex-body source integration, polar/improper comparisons, radial forms, exactness and the remaining geometric obligations are active work. All P6 gates remain open; the plan is retained. No commit or remote CI was run.

### Resumed execution checkpoint

- The inventory now verifies 279/287 resolutions and 808/849 obligations: 271 as stated and 8 refuted/corrected. Chapter 10 has 24/32 verified resolutions and 76/117 verified obligations. Its remaining eight resolutions are not counted complete.
- Accepted the independent reviews of Chapter 10 Exercises 1, 6, 12–19, 21, 24–26, 28–29 and 32 at matching source-closure and configuration hashes. The corrected Exercise 6 uses the prescribed Chapter 8 function in the actual bump construction. Convex source integration retains boundary values, and the Möbius results distinguish the geometric rim from the parameter boundary.
- The current default gate passed: 18,702 build jobs, 7,134 audited local declarations, 1,526 mapped references and 37 regression tests. It includes solution-article coverage checks. Metadata and article checks passed again after recording the 55 newly verified obligations. This is not final-book acceptance.
- The full Exercise 23 primitive and sphere construction are merged and compile. Exercises 8–10 now include source comparisons and the limit-derived polar argument. Their independent reviews remain separate acceptance gates. The completed private Exercise 22, 27 and 31 candidates still require production integration and independent review.
- The second full-book review has started with Chapters 1–4. No second-review group is yet counted complete. The isolated final rebuild, final documentation and plan removal remain open. No commit or remote CI was run by this execution.

### Complete-candidate integration checkpoint

- All 287 exercise modules are now present and root-imported. The full default gate passes: 18,710 build jobs, 7,793 actual local declarations, 1,838 mapped references and 37 regression tests. A legacy-mode Exercise 27 header initially failed root import; its header-only module conversion compiles and is being independently rechecked at the new hash. No trust exception was added.
- The inventory verifies 284/287 resolutions and 831/849 obligations: 274 as stated and 10 explicitly refuted/corrected. Only Exercises 22, 27 and 31 remain pending first-review acceptance. The proper-original-module Exercise 23 review supersedes the preliminary renamed-module build. Actual artifact checks establish its complete six-obligation result despite the provider's later overload error.
- The second review of Chapters 1–2 passes all 126 obligations, with a fresh 50-module rebuild, 34,916 transitive declarations and 44 independent controls. Its evidence verifier passes. Per-obligation decisions are retained in `docs/rudin/semantic-review.json`; all other second-review scopes remain open.
- Final mode now also checks complete second-review coverage and matching source, environment, declaration and disposition records. Thirteen new regression tests pass for this evidence gate. The full strict gate, isolated rebuild and final documentation still remain open.

### Final acceptance work in progress

- The second review found a genuine R11E03 input-scope defect: Definition 11.13 allows extended-real terms, even in sequences with finite limits. Its first acceptance is reopened; current totals are 286 resolutions and 848 obligations verified (275 as stated, 11 corrected). The repair must cover extended-real inputs and separately distinguish finite and extended limits. All final Chapter 10 sources remain frozen.
- The retained second-review registry verifies 733/849 obligations: Chapters 1–7, 9 and all of Chapter 10. Source/configuration/artifact hashes and exact mappings were checked at integration. The E01–11 packet is complete and passes its checks despite a provider overload after its final report.
- The broad Chapters 8/11 attempts explicitly withheld semantic acceptance after truncated reads. None is counted. Smaller disjoint groups now review every remaining obligation using single bounded outputs and durable per-exercise read/verdict records. Chapter 8 has groups E01–10, E11–20 and E21–31. Chapter 11 has E01–07 excluding E03, E08–13 and E14–18; E03 is repaired and reviewed separately. The overall scope remains all 849 obligations.
- A tooling review found a real inherited import-parser defect: a valid local import with a trailing comment could omit a shared file from both evidence fingerprints. The complete synthetic final-gate bypass is retained under `.lake/independent-second-gate-eM0qHz4v`. The exact independently prepared parser correction is now applied. All 315 current source headers match the pinned Lean parser; all 287 old/new exercise fingerprints and the root closure are identical. The original complete-CLI bypass now rejects at both evidence gates. All 56 production regression tests pass, including actual Lean header-oracle cases, shared-change rejection and fake-comment orphan detection. No source evidence was refreshed. The corrected checker still needs the strict final gate.
- The isolated candidate `.lake/rudin-final-isolated-20261023-phase1-t2SbDcVZ` copied every intended local file and all nine pinned package trees without shared inodes. With the original project masked, cache retrieval and the fresh 18,710-job build pass. Development checks are running. This is preparation, not final acceptance. The later E03 repair is the only changed Lean/config baseline entry; its full replacement matches the compiled author proposal at SHA-256 `e1f319bf78ebb269de58e529900e11c41f94400bd53aaa207cc82c45386e03b3`. Two independent E03 reviews and a new root development gate are running. The candidate must retain the old baseline, copy this explicitly approved proof change plus corrected checker/tests and complete metadata/docs, delete only its own root build outputs, and perform a new fresh build and strict final gate. The article checker also has a tested singular pending-entry count correction; 57 regressions pass.
- Historical Chapter 5 citation/status wording was corrected explicitly, without changing mathematical contracts. CI now selects the same `--final` entry point. Remote CI has not run; no commit, push or remote workflow was triggered.

## Architecture

### Files and Responsibilities

Keep the existing `Math` library. Do not rename the project first or create a website or database.

```text
Math/Rudin/Chapter01/Exercise01.lean
...
Math/Rudin/Chapter11/Exercise18.lean
Math/Rudin/Support/<required-shared-topic>.lean
Math/Rudin.lean                         # Import all delivery modules
Math.lean                               # Import Math.Rudin
exercises.json                          # Exercise/subpart inventory, status, declaration mapping
scripts/check_exercises.py              # Coverage, source-reference and import checks
scripts/check_axioms.lean                # Check axiom dependencies of delivery declarations
scripts/check.sh                         # Shared local and CI check entry point
docs/rudin/source.md                     # Edition, page numbers, source hash
docs/rudin/formalization.md              # Interpretation rules and shared representations
docs/rudin/errata.md                     # Source-statement issues, counterexamples and corrections
docs/rudin/progress.md                   # Inventory-generated progress and blocker summary
```

- Use one main file per exercise. Subparts of the same exercise share necessary definitions and local lemmas.
- Put infrastructure in `Support/` only if it is reused across exercises or needs independent verification.
- Use chapter-specific Lean namespaces such as `Rudin.Chapter01`. Use predictable declaration names such as `exercise01` and `exercise01_a`.
- `exercises.json` is the single source of truth for coverage and status. For each exercise, record its ID, chapter/exercise number, book/PDF pages, short original summary, sub-obligations, module, delivery declarations, dependencies, status, and verification evidence.
  - Keep original letter labels for subparts. Give unlabelled follow-up questions stable IDs, such as `R01E11.uniqueness`.
  - Do not store a full transcription of the book's exercises. Put formal mathematical statements in Lean, and differences and source locations in documentation.
  - Limit status values to `todo`, `in_progress`, `blocked`, and `verified`. A written statement or informal solution does not qualify as `verified`.
  - Record a separate disposition for refuted exercises. Do not label a corrected version as proof of the original proposition.

### Mathematical Statement Contracts

- By default, any theorem proved in the pinned Mathlib is permitted, including results from later chapters of the book. Rebuilding the full textbook and using only elementary proofs are not required.
  - If an exercise explicitly requires a construction, a specified method, or verification of a structure, deliver that construction and its properties. An existence result alone is not a substitute.
- By default, use Mathlib's `ℝ`, `ℂ`, metric spaces, filters, derivatives, measures, and `Lp`. Represent Rudin's Euclidean norm with an appropriate `EuclideanSpace`. Do not treat the default norm on an arbitrary function space as the Euclidean norm.
- Before writing each proof, check quantifiers, domains, empty sets, zero/low dimensions, zero vectors, endpoints, starting indices, finite/countable conditions, and pointwise/almost-everywhere conditions.
- Convert open-ended questions into complete obligations. Include forward statements, decisions on converses, necessary counterexamples, equality conditions, and dimension classifications.
- If an exercise requires a quotient construction, Dedekind cuts, or a special integral, check that Mathlib's implementation preserves the exercise requirements before using it. Build minimal models and comparison theorems if needed.
- If the original exercise has a problem, retain the source and differences, prove a counterexample, and prove an explicitly corrected version. Do not change the source statement and present it as unchanged.
- Prohibit `sorry`, `admit`, `sorryAx`, custom axioms, and hiding the target conclusion in a hypothesis, typeclass, or definition.
- The transitive axiom dependencies of final deliveries and shared theorems may contain only the standard `propext`, `Classical.choice`, and `Quot.sound`. Rewrite proofs that use other trust mechanisms. Do not automatically expand the allowlist.
- Successful compilation proves only that the written statement holds, not that it correctly represents the exercise. Per-exercise semantic review is a separate completion condition.

### Parallel Execution Rules

- The main agent exclusively manages integration of the toolchain, root imports, `exercises.json`, verification tools, CI, and this plan.
- Subagents modify only their assigned, non-overlapping files. Report the need for shared definitions first. Do not independently change another worker's interfaces.
- Source inventory and toolchain preparation can run in parallel. Representative exercises and source counterexamples can run in parallel once the required representations are stable.
- Exploration for Chapters 6 and 10 must first deliver restricted but genuine prototypes with explicit gaps. Do not start batch solutions for dependent exercises while required bridges are missing.
- Solvers report exact declarations, compilation results, and incomplete obligations. The main agent records verification status only after an independent subagent reviews the exercise interpretation.

## Plan

### P1 — Fix the Full Scope and Exercise Interpretations

- [x] Create `docs/rudin/source.md` and `exercises.json`. Check every exercise number and follow-up question in all 11 chapters page by page. Acceptance: each source exercise has exactly one main ID, sub-obligations trace to page numbers, and chapter totals match the overall denominator. Evidence: three source inventories were merged into 287 exercises and 839 obligations. `scripts/check_exercises.py` checks exercise numbers, sub-obligation denominators, and book/PDF page offsets. Source review does not mean that Lean semantic review is complete.
- [x] Create a short semantic contract, exercise type, and dependencies for each exercise. Record OCR questions, missing conditions, and required constructions. Acceptance: every exercise has an actionable formalization target, and high-risk exercises have concrete discovery tasks without assuming unconfirmed theorem names. Evidence: all 287 exercises have source contracts and sub-obligations. Explicit correction/convention/finite-extension contracts for 15 exercises are recorded in the inventory and `source-clarifications.md` and passed independent discovery review.
- [x] Clarify all pending source issues in the inventory. Treat definition conventions, open-ended scope, and actual errors separately. Acceptance: each issue has source/context evidence, an explicit contract to prove, and dependent obligations. Issues that need counterexamples cannot be marked resolved before Lean proofs are complete. Evidence: all 18 issues have book/PDF pages, image/context evidence, and explicit contracts to prove. Added 8 omitted obligations without removing original obligations. Issues whose mathematical counterexamples and corrections are unproved remain pending. No external acceptance or manual approval gate is added.

### P2 — Establish Reproducible Lean and Check Infrastructure

- [x] Select and pin a compatible Mathlib commit and Lean toolchain. Acceptance: commit `lean-toolchain`, dependency configuration, and `lake-manifest.json`; successfully run `lake update`, `lake exe cache get`, and `lake build`; retain version evidence. Evidence: retained Lean 4.35.0 and Mathlib v4.35.0 commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. Updates, retrieval of 9031 cache entries, and default executable/library builds all succeeded.
- [x] Create `Math/Rudin.lean`, minimal examples, and `scripts/check.sh`. Acceptance: the default build target still builds the library, `lake env lean <example-file>` succeeds, and root imports include all delivery modules. Evidence: the first 8 exercises and 3 Support modules are publicly imported from the root. Single-file and default executable/library builds succeed. The original template was also moved to Lean's module system, retaining the original executable.
- [x] Implement inventory, import, declaration, and axiom checks, and connect them to existing CI. Acceptance: valid examples pass. Temporary negative fixtures with omitted subparts, missing imports, nonexistent declarations, `sorry`, or custom axioms fail. Fixtures are not included in the delivery library. Evidence: `./scripts/check.sh` passes. The 23 regression tests include actual Lean environment negative tests, failed evidence, and evidence invalidation after source/shared-definition/dependency changes. The private proof-body audit covers 211 declarations and 31 delivery references. CI uses the same entry point. Remote CI has not run.
  - Checks must use the Lean environment/type checker, not only text searches. Axiom checks cover transitive dependencies of delivery and Support declarations.
  - Run all Python check tools through `uv run python`. Pin versions of third-party dependencies if used.
  - Incomplete exercises are permitted in the inventory during development. Final mode must fail on any item that is not `verified`.
  - `verified` evidence must explicitly record success, the semantic reviewer, local source import-closure fingerprints, and toolchain/configuration/manifest fingerprints. Nonempty failure data does not count as success. Shared-definition or environment changes must invalidate old evidence.

### P3 — Explore High-Risk Areas and Prototype Representative Exercises First

Complete this phase before starting full-book exercise groups that depend on high-risk infrastructure. Do not wait until Chapter 10 to discover that substantial new infrastructure is needed. During exploration, basic exercise groups with stable definitions and no dependency on gaps can be completed in parallel. Chapter 1 was completed in the second batch. Continue selecting exercises by dependency. Required bridges and orientation conditions for Chapters 6 and 10 are not waived.

- [x] Survey chapter support in the pinned Mathlib and classify it as directly usable, requiring a bridge, or requiring new implementation. Acceptance: every reference has an actual source path and a compilable usage example. Specifically cover Dedekind cuts, metric completion, Riemann–Stieltjes integrals, ODEs, Fourier/Gamma, differential forms/Stokes, and `Lp`. Evidence: the source mapping in `docs/rudin/mathlib-coverage.md` and `Support/ApiExamples.lean` compile and are included in root imports and the full-project axiom audit. This does not claim completed API selection for every exercise.
- [x] Build a compilable prototype of the Chapter 6 integral representation. Acceptance: explain how it covers Rudin's monotone integrators, discontinuities, and endpoint conventions. Complete an equivalence or a bridge under applicable conditions. Evidence: literal weak-partition Darboux sums, full Darboux/tagged equivalence, continuous-integrand existence for raw interval-monotone integrators, and the continuous real-integrand measure bridge for `StieltjesFunction ℝ` compile and have independent review. They cover singleton intervals, zero mass, repeated nodes, and left/right endpoint atom conventions. General raw normalization/endpoint correction and the discontinuous-integrand bridge remain incomplete. Existing counterexamples still prohibit unconditional substitution.
- [x] Build a compilable prototype of the infrastructure required for Chapter 10. Acceptance: check representations of differential forms, pullback, exterior derivative, chains, orientation, and integration against actual exercise requirements. Complete one nontrivial operation and one required integration/boundary identity. List missing theorems and dependency order. Do not assume that Mathlib has a complete Stokes theory. Evidence: actual forms, pullbacks, derivatives, signed chains and smooth simplex coefficients are compiled and independently reviewed. `SimplexIntegration` and `TriangleStokes` prove genuine nonlinear and nonhorizontal boundary identities, literal source zero-extension and all three edge-integral witnesses. The frozen full-project and isolated gates pass. The prototype criterion is complete; the separate general-chain/source-comparison tasks below remain open, with their precise gaps and dependency order in `mathlib-coverage.md`.
- [x] Complete common refinement, sum bounds, and Darboux/tagged equivalence for Chapter 6 partitions. Acceptance: Lean theorems do not assume their target conclusions. Check the representation with constant and point-supported integrands. Evidence: exact node-union refinement and sum/refinement bounds in `StieltjesRefinement.lean`, and the actual predicate iff in `StieltjesEquivalence.lean`, passed independent review and full-project checks. Regressions include constants, pointSpike, singleton intervals, zero increments, repeated nodes, and examples with unattained extrema.
- [x] Build the Chapter 6 integral bridge for nonconstant integrands, with necessary jump/endpoint conditions. Acceptance: cover at least continuous integrands with a formal comparison. Existing endpoint counterexamples remain valid, and trust conditions are not relaxed. Evidence: `StieltjesMeasureBridge.continuous_bridge` proves equality of the actual Darboux integral and the `(a,b]` measure integral for an explicit right-continuous `StieltjesFunction ℝ`, `a ≤ b`, and `ContinuousOn f (Icc a b)`. Tests for nonconstant integrands, terminal jumps, exclusion of the initial atom, singleton intervals, and zero mass pass. Independently reviewed final SHA256: `2e59487e32734474713a6d4e7f8f43e1b62d0e84010c5134d6a18271a1f6f37a`. This does not claim measure comparison for arbitrary raw integrators.
- [x] Build signed affine/parameterized chains and face maps required for Chapter 10. Acceptance: prove `∂² = 0`, face cancellation and multiplicity, and compare them with Exercises 16–19 and 32. Evidence: all of those exercises passed independent primary-source/type/body review and the 7,134-declaration root gate. Actual full parameter maps, ordinary degree-zero boundaries, affine square/cube coverage and orientation, signed face cancellation and Möbius seam multiplicity are proved. The raw augmented, affine orientation and smooth permutation-quotient models remain explicitly distinct; no equality of vertex data is used as equality of nonlinear maps.
- [x] Compare Chapter 10 form pullbacks/simplex integration with Rudin's integral. Acceptance: prove comparisons and boundary identities under the required regularity and orientation conditions; do not assume Stokes to prove itself. Evidence: independently reviewed `MultivariateRiemann`, `SimplexStokes` and `SmoothChainIntegration` prove literal closed-simplex source witnesses in every coordinate order, actual local C²/C¹ Stokes, integer-chain linearity and permutation-quotient descent in every required degree. Exercise 20 verifies the resulting integration-by-parts API, including oriented and singleton segments. Matching closures passed the root gate. This does not identify the permutation quotient with a full quotient by equality of integration functionals.
- [x] Complete all obligations for representative exercises `R01E01`, `R02E02`, `R03E24`, `R06E01`, `R09E01`, and `R11E01`. Acceptance: every exercise passes semantic review, compilation, axiom checks, and inventory comparison. Evidence: all 15 obligations across the six exercises are `verified`. Independent review confirms the actual Cauchy-sequence quotient and completion bridge, and the actual Darboux integral. The first R06E01 review found a strict-partition/zero-length-interval omission. It was corrected to weak partitions and `a ≤ b`. The second independent review, singleton/endpoint tests, and integration checks all pass.
- [x] Update this plan, shared representations, and chapter workload from the prototypes and representative exercises. Acceptance: split major gaps into actionable tasks. Unresolved correctness issues explicitly block affected exercises. Use only measured categories for schedule estimates; do not claim equal cost per exercise. Evidence: updated `formalization.md`, `mathlib-coverage.md`, and P3 dependency tasks, and completed source-contract classification. Work is classified into groups using existing lemmas, groups needing explicit constructions/comparison theorems, Darboux/measure infrastructure, and oriented parameterized-chain/integration infrastructure. Classification uses implementation evidence from Chapter 1 and both prototype types. No unmeasured full-book schedule is given.

### P4 — Verify Known Source-Exercise Issues

- [x] Complete the degenerate-case counterexample, nondegenerate version, and full classification for `R01E19`. Acceptance: Lean verifies the source issue and corrected results. `errata.md` records the original conditions, correction, and corresponding declarations. Evidence: 4 obligations passed independent review and integration checks. The counterexample excludes all possible positive-radius spheres, not only the original formula.
- [x] Complete the zero-function counterexample and full Schwarz equality conditions for `R11E18`. Acceptance: Lean verifies the counterexample and the correct version including degenerate cases. Do not hide the source issue behind additional nonzero assumptions. Evidence: 4 obligations passed independent review and integration checks. The complex L2/source-integral bridge, full zero-function branch, and finite Dirac measure counterexample are proved.

### P5 — Complete All Exercises by Chapter

Each item below covers only incomplete exercises. Do not count P3 or P4 results twice. Chapter order is the default; actual order follows exercise dependencies in the inventory. Start with batches of 3–5 exercises. Handle large construction exercises separately.

- [x] Complete Chapter 1 Exercises 1–20. Acceptance: all sub-obligations pass this section's batch gates, including complex roots, equality conditions, dimension classifications, and constructions with modified cut definitions. Evidence: 20/20 exercises and 55/55 obligations passed single-file compilation, independent source/type review, and the second-batch integrated axiom audit. There are 19 exercises proved as stated; R01E19 is completed with a counterexample and corrected version. Root imports cover all 20 exercises.
- [x] Complete Chapter 2 Exercises 1–30. Acceptance: all sub-obligations pass the batch gates. Explicitly distinguish finite, at most countable, and countably infinite. Evidence: 30/30 exercises and 71/71 obligations passed independent source/type review, compilation, project and isolated-source checks. R02E29 retains the bounded-segment obstruction and explicit extended-interval correction; R02E28 keeps the source countably-infinite convention. Actual decimal4/7 expansions, irrational perfect-set construction and the required nested-ball Baire proof are included.
- [x] Complete Chapter 3 Exercises 1–25. Acceptance: all sub-obligations pass the batch gates, including the completion construction, dense embedding, and related identification results. Evidence: 25/25 resolutions and 89/89 obligations pass independent source/type review, compilation, full project and isolated-source checks. Includes ordinary conditional series, full Tauberian outline, vector-series extensions, Newton classifications, literal Cantor digits and the actual quotient completion of the rationals. R03E14's added source obstruction is retained.
- [x] Complete Chapter 4 Exercises 1–26. Acceptance: all sub-obligations pass the batch gates. Questions about converses and removal of assumptions have decisions and required counterexamples. Evidence: all 26 resolutions and 74 obligations pass independent source/type review, full project checks and isolated-source rebuild. R04E05 also covers the arbitrary metric domain stated in the source; R04E26's optional forward helpers add no source obligations.
- [x] Complete Chapter 5 Exercises 1–29. Acceptance: all sub-obligations pass the batch gates. Endpoint derivatives, ODE uniqueness, and specified initial conditions have consistent semantics. Evidence: all 29 resolutions and 84 obligations pass independent source/type/body reviews, default project checks and isolated-source rebuilding. Actual one-sided derivative chains, every initial datum, complete ODE waiting-time classification, sharp threshold equality cases, and both explicit source corrections are retained.
- [x] Complete Chapter 6 Exercises 1–19. Acceptance: all sub-obligations pass the batch gates. Integral existence, integral values, and rectifiable-curve requirements have corresponding results. Evidence:19/19 resolutions and54/54 obligations pass independent source/type/body review, frozen full-project checks and isolated-source rebuilding. Raw complex integrals, both improper endpoints, required approximation constructions, partition lengths and R06E18's explicit endpoint correction are retained.
- [x] Complete Chapter 7 Exercises 1–26. Acceptance: all sub-obligations pass the batch gates. Types and domains for uniform convergence, equicontinuity, and ODE existence are consistent. Evidence:26/26 resolutions and79/79 obligations pass independent page/type/private-body reviews, the frozen project gate and isolated rebuilding. Includes literal series and Cantor constructions, all12 metric/vector extensions, actual polynomial approximation and the full Euler-polygon/vector ODE construction with genuine within endpoint derivatives.
- [x] Complete Chapter 8 Exercises 1–31. Acceptance: all sub-obligations pass the batch gates. Cover Fourier, Gamma, winding number, fixed points, and asymptotics, not only elementary-function exercises. Evidence: all 31 exercises and 79 obligations passed independent primary-page/type/private-body review, root checks and isolated completed-source rebuilding. Actual Riemann kernels, ordered Fourier limits, prescribed winding/fixed-point constructions and Gamma asymptotics are retained.
- [x] Complete Chapter 9 Exercises 1–31. Acceptance: all sub-obligations pass the batch gates. Representations of linear maps, Fréchet derivatives, Jacobians, and Taylor polynomials have explicit comparisons. Evidence: all 31 resolutions and 110 obligations passed independent source/type/body reviews, the root gate and isolated completed-source rebuild. Every derivative has the required existence evidence; Euclidean norms, actual local inverse graphs and Taylor counting are explicit. R09E31 is refuted/corrected, not proved as printed.
- [x] Complete Chapter 10 Exercises 1–32. Acceptance: all sub-obligations pass the batch gates, including parameter direction, boundary multiplicity, orientation, and nonorientable cases. Evidence: all 32 resolutions and 117 obligations pass independent primary-source/type/actual-private-body review and the 7,793-declaration root gate. The final 18 obligations have fresh original-name 22-module and 18-module rebuilds, exact theorem-origin checks, independent nonzero/negative controls and required-method dependency checks. Exercises 9, 10 and 22 retain explicit refutations/corrections. No scope or trust waiver was used. The second review and isolated strict gate remain separate.
- [ ] Complete Chapter 11 Exercises 1–18. Acceptance: all sub-obligations pass the batch gates. Explicitly distinguish functions from almost-everywhere equivalence classes. Cover the specified measure-construction and completeness requirements. Evidence: the initial 18/37 acceptance is superseded for R11E03 by the extended-real input omission. The remaining first-review count is 17/18 resolutions and 36/37 obligations. Repair E03, obtain new independent reviews, and rerun the project gates before closing this item. Includes the literal Riemann criterion, AE quotient metric and completeness, actual elementary charge with signed-extension obstruction, exact sine convergence set and Bessel proofs. R11E18 remains explicitly refuted/corrected. The full-book second review and isolated final rebuild remain open.

Before completing each batch, perform these steps in order:

1. Review all sub-obligations against the PDF pages. Complete necessary informal derivations before confirming Lean types.
2. Search the pinned Mathlib. Use existing results first. Add only missing lemmas or constructions.
3. Run single-file `lake env lean <file>`, full-project `lake build`, and `./scripts/check.sh`.
4. Review the actual elaborated declaration types. Check for incorrect default instances, unused assumptions, weakened conclusions, or vacuous premises. Retain per-exercise review evidence.
5. Only after these checks pass, set status to `verified`, regenerate `progress.md`, and update valid completion evidence in this plan. Handle new errata to the same standard as P4.

### P6 — Full-Book Integration Acceptance

- [ ] Perform a second semantic review of all exercises. Recheck pages, quantifiers, and subpart completeness. Acceptance: each sub-obligation has an actual declaration or explicit formal answer. All source-exercise issues have counterexample and correction evidence. Unresolved issues remain blocking.
- [ ] Rebuild all results in an isolated working copy or clean checkout. Acceptance: `lake exe cache get`, `lake build`, and `./scripts/check.sh --final` succeed using only pinned dependencies, without relying on untracked files in the original working directory or custom local packages.
- [ ] Update `README.md`, source documentation, and final progress. State rebuild commands, the exercise index, dependency versions, and errata counting rules. Acceptance: total exercise and sub-obligation counts are calculated from the inventory. Report proofs of original exercises separately from refutations/corrections.

## Completion Checklist

- [x] All source exercises and sub-obligations in all 11 chapters have been checked. Official totals have source evidence. Evidence: `exercises.json` and `source.md` record 287 exercises and 849 obligations: the initial 839, eight source-clarification checks, R03E14's zero-bound obstruction, and R06E02's explicit comparison. Changes are justified in `source-clarifications.md`. This source inventory does not mean that all interpretation issues are resolved or all Lean proofs are complete.
- [ ] All 849 obligations are `verified`, with no `todo`, `in_progress`, `blocked`, or unresolved source issues. Current evidence: R11E03 is reopened; 848/849 obligations are verified. Full second-review coverage and strict final gates also remain required.
- [x] False source statements have Lean counterexamples and clearly labelled correct alternatives. Evidence: 276 exercises are as stated and 11 are explicitly refuted/corrected, with resolved issue records and independent semantic acceptance. The final E22 origin obstruction and nonvanishing correction are included. No false original proposition is counted as proved.
- [x] All current delivery modules are included in the default build. No incomplete proofs are hidden in unimported files. Evidence: all 287 exercise modules and every present Support module are reachable from `Math`; the 18,710-job default build and all 1,838 mapped theorem-kind/origin checks pass. Independent semantic acceptance remains separate.
- [x] All current delivery and Support declarations pass axiom checks, with no placeholder proofs, custom axioms, or unauthorized trust extensions. Evidence: the current root audit checks all 7,793 local declarations and 1,838 references using actual private bodies. Only the standard three axioms are allowed; no unsafe, partial or nonstandard-axiom exception was added. The isolated final audit remains a separate gate.
- [ ] Per-exercise semantic reviews and the second full-book review are recorded. All major correctness questions are resolved.
- [ ] The full-project build and final checks pass in a clean environment. Local and CI checks use the same entry point. If remote CI results are unavailable, state this explicitly and do not claim success.
- [ ] Documentation is sufficient to rebuild results, locate exercises, and understand statement differences. No textbook PDFs, full-book OCR, or other unnecessary binary files are committed.

## Non-Goals

- Do not rebuild the full real-number, topology, calculus, or measure theory already in Mathlib, except for constructions explicitly required by exercises.
- Do not make every textbook theorem a separate delivery target. Add only results needed by the exercises.
- Do not present natural-language-only answers or theorem skeletons as completed solutions.
- Do not independently create Git commits, push branches, or trigger remote operations. Execution authorization already covers local implementation and dependency preparation.
- Do not promise a fixed total schedule without measurements from representative exercises. Do not treat the infrastructure costs of Chapters 6 and 10 as known small quantities.

## Risks

- **Unknown Mathlib compatibility and API support**: P2 pins a usable version. P3 demonstrates support with compiled examples. Do not rely on guessed APIs.
- **Chapters 6 and 10 may need substantial new infrastructure**: P3 validates representations and required results early. Unresolved bridges or missing theorems block dependent exercises. Do not use `axiom` as a temporary substitute.
- **Source statements and OCR may be incorrect**: page images determine the exercise interpretation. Both known and new issues require formal treatment.
- **Successful compilation of the wrong exercise**: retain semantic contracts and review evidence for each exercise, then perform a final full-book review. Coverage tools do not replace mathematical semantic checks.
- **Misleading scope and progress**: report both completed main exercises and completed sub-obligations. Separately list refuted/corrected source exercises. Do not use file counts, line counts, or declared theorem counts as completion rates.
- **Long-term dependency drift**: use pinned versions throughout. If an upgrade is needed, separately verify all existing proofs. Do not combine unverified major changes with new exercise work.
