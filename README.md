# Rudin exercises in Lean 4

This project formalizes the exercises in Walter Rudin's *Principles of
Mathematical Analysis*, Third Edition. It is in progress, not a complete solution
set. The source inventory contains 287 exercises and 849 obligations. Verified
counts are generated in [the progress report](docs/rudin/progress.md).

## Read the solutions

The [Markdown solution article](docs/rudin/solutions.md) gives mathematical
statements and proofs for the exercise files in this checkout. It distinguishes
verified solutions from newer or partial formalizations and keeps source
corrections explicit. The standard check also compares article entries with the
current exercise files, inventory status, and declaration references.

```sh
# Check article coverage and links without rebuilding Lean.
uv run --no-project python scripts/check_solutions.py
```

## Toolchain

- Lean: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
- Elan, Git, and uv must be available. The Python checks use only the standard
  library. PDF tooling is not needed to build or check proofs.

## Build and check

```sh
lake update
lake exe cache get
./scripts/check.sh
```

`lake-manifest.json` locks transitive dependencies. Do not update the manifest
when only rebuilding an existing checkout; after dependencies are materialized,
use `lake exe cache get` and `./scripts/check.sh`.

The check entry point validates the inventory and imports, builds the default
Lake target, checks theorem references and transitive axiom dependencies in Lean,
and runs positive and negative regression fixtures. Development checks allow
unfinished exercises. They do not establish full-book completion.

```sh
# Rebuild the progress report after an authorized inventory change.
uv run --no-project python scripts/check_exercises.py --update-progress

# Full-book gate: fails if any obligation is unfinished.
./scripts/check.sh --final
```

## Layout

- `Math/Rudin/ChapterNN/ExerciseNN.lean`: exercise proofs.
- `Math/Rudin/Support/`: shared definitions and restricted prototypes.
- `Math/Rudin.lean`: imports every delivered exercise and support module.
- `exercises.json`: original summaries, subquestion IDs, source pages, issues,
  theorem references, status, and review evidence.
- [Source](docs/rudin/source.md), [formalization rules](docs/rudin/formalization.md),
  [source issues](docs/rudin/errata.md),
  [source contracts](docs/rudin/source-clarifications.md), and
  [Mathlib coverage](docs/rudin/mathlib-coverage.md).
- [Current implementation plan](docs/plans/2026-10-22_rudin-lean4-plan.md).

False source claims require a Lean counterexample and an explicitly corrected
result. They are not reported as proved original statements. Source PDFs and
whole-book OCR are not part of the repository.
