# Rudin exercises in Lean 4

This project formalizes all end-of-chapter exercises in Walter Rudin's
*Principles of Mathematical Analysis*, Third Edition.

The inventory records **286 verified exercise resolutions and 848 verified
obligations**: **275 proved as stated** and **11 refuted and explicitly
corrected**. Exercise 11.3 is reopened for extended-real input coverage.
The second full-book review and isolated final checks are still in progress. Counts are generated in [the progress report](docs/rudin/progress.md).

## Read the results

- [Solution index](docs/rudin/solutions.md): mathematical statements, proofs,
  source links and declaration references for every exercise.
- [Inventory](exercises.json): stable subquestion IDs, source pages, exact
  theorem mappings, dispositions and first-review evidence.
- [Second review](docs/rudin/semantic-review.json): retained individual
  decisions, source fingerprints and environment fingerprints.
- [Source](docs/rudin/source.md), [formalization rules](docs/rudin/formalization.md),
  [errata](docs/rudin/errata.md), [source contracts](docs/rudin/source-clarifications.md),
  and [Mathlib comparisons](docs/rudin/mathlib-coverage.md).

The articles explain the formal results; they do not replace Lean statements
or semantic review. False source claims are not counted as proved originals.
Source PDFs, whole-book OCR and review page images are not committed.

## Pinned environment

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
- Transitive dependency revisions: `lake-manifest.json`.
- Required tools: Elan, Git and uv. Python checks use only the standard library.
  PDF tools and the source scans are not needed to rebuild the proofs.

## Rebuild and verify

From the repository root:

```sh
lake exe cache get
lake build
./scripts/check.sh --final
```

Keep the committed manifest. Do not run `lake update` for an ordinary rebuild.
The final command currently rejects incomplete second-review coverage.

The shared local/CI entry point checks inventory coverage and imports, builds
all delivery modules, checks actual theorem kinds and origins, audits private
proof bodies and transitive axioms, checks article coverage and links, and runs
positive and negative regression tests. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted axioms. Final mode also requires every obligation
and second-review decision to be complete and current.

```sh
# Development gate; permits explicitly unfinished inventory entries.
./scripts/check.sh

# Regenerate counts after an authorized inventory change.
uv run python scripts/check_exercises.py --update-progress

# Check the articles without rebuilding Lean.
uv run python scripts/check_solutions.py
```

Remote CI has not been run. Its workflow uses `./scripts/check.sh --final`;
local success is not a claim of remote CI success. No commit or push is part
of this implementation.

## Source layout

- `Math/Rudin/ChapterNN/ExerciseNN.lean`: one main file per exercise.
- `Math/Rudin/Support/`: required shared constructions and comparisons.
- `Math/Rudin.lean`: public imports of all exercise and Support modules.
- `docs/rudin/solutions/`: one mathematical article per chapter.

The [active implementation plan](docs/plans/2026-10-22_rudin-lean4-plan.md)
remains until every final gate passes.
