# Formalization rules

## Statement fidelity

Use the source page and the inventory obligation as the mathematical contract.
Check all quantifiers, domains, boundary cases, and follow-up questions before
marking an obligation verified. Compilation alone does not establish fidelity.

- Use Mathlib results from the pinned revision. Later textbook results are
  allowed unless the exercise specifies a construction or proof method.
- Use `EuclideanSpace ℝ (Fin n)` when the Euclidean norm matters.
- Distinguish convergence at every point from convergence almost everywhere.
- Distinguish functions from equivalence classes in `MeasureTheory.Lp`.
- For a Bochner integral, state integrability or prove it. A non-integrable
  function can have a library integral equal to zero by definition.
- Do not replace a Riemann–Stieltjes integral by a measure integral without
  proving the required bridge, including endpoint and jump conventions.
- Do not assume the library completion solves an exercise that explicitly
  requires the Cauchy-sequence quotient construction.
- Preserve a false source claim in the issue record. Supply a counterexample
  and an explicitly corrected theorem; do not hide extra hypotheses.
- For unresolved source wording, apply the explicit contracts in
  `source-clarifications.md` and the inventory. Contract selection does not
  complete the proof or resolve an unproved source obstruction.
- Use literal ordered-chain results only within their stated scope. Raw vertex
  lists do not impose orientation signs, and mapping vertices is not nonlinear
  postcomposition of a parameterized surface.

## Proof trust

No `sorry`, `admit`, custom axioms, unsafe proofs, or partial delivery
definitions are allowed. The transitive axiom dependencies of exercise and
support declarations are limited to `propext`, `Classical.choice`, and
`Quot.sound`.

The Lean audit checks declaration existence, theorem kind, origin module, and
transitive axiom dependencies in the imported environment. It audits all
imported `Math.Rudin` declarations, including unlisted support lemmas. The audit
file intentionally uses legacy import mode to load private proof bodies
transitively: Lean 4.35 module interfaces can represent exported theorems as
axioms, which must not be confused with custom axioms in the actual proof
bodies.

## Status and evidence

`exercises.json` is the source of truth for progress. Each obligation has a
stable ID and one of `todo`, `in_progress`, `blocked`, or `verified`.

A verified obligation must have theorem references and a nonempty evidence
record with `semantic_review.result = "passed"`, a reviewer and source-to-type
notes, and `checks` entries `single_file`, `project_build`, `axiom_audit`, and
`coverage` all equal to `"passed"`. Failed or merely nonempty evidence does not
qualify. Evidence also records hashes of the exercise and its local imported
modules, plus the toolchain, Lake configuration, and dependency manifest. A
change invalidates the stored evidence. Reopen affected obligations, review the
changed contracts, and run the checks before recording new hashes.
Unresolved source issues must remain visible; a corrected result must not be
reported as proof of the original claim. Main-exercise completion requires all
its obligations to be verified.

Automated checks detect structural omissions and undeclared evidence. They
cannot infer whether an omitted natural-language subquestion exists. Source
inventory review and independent semantic review remain required.

## Parallel execution

The main agent owns the toolchain, shared support integration, root imports,
inventory, checks, and plan. Workers receive disjoint file ownership and
explicit mathematical obligations. They report exact declaration names and
compile evidence; they do not update shared completion state.

Independent source inventory work can run with toolchain preparation.
Independent proofs can run after their definitions are stable. A separate
review checks source fidelity before the main agent records completion.
Missing shared definitions block dependent proofs. Do not dispatch all
exercises before the chapter 6 and chapter 10 prototypes establish their
representations.
