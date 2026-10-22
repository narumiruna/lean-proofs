# Source issues

A false source claim is not counted as a proved original statement. A verified
resolution requires a counterexample, an explicit correction, source-to-type
review, compilation, and the project axiom checks.

## R01E19: positive radius in the degenerate case

- Source: book page 23, PDF page 32; page image checked.
- The source requires `r > 0` without excluding `a = b`.
- `Rudin.Chapter01.exercise19_original_counterexample` proves that no center
  and positive radius work for coincident zero centers in dimension one.
  `exercise19_degenerate_no_positive_radius` proves the general impossibility;
  it does not merely observe that the book's displayed radius is zero.
- `Rudin.Chapter01.exercise19` proves the distance-locus equivalence with the
  source center and nonnegative radius formulas. `exercise19_nondegenerate`
  proves positivity for distinct centers. `exercise19_degenerate` gives the
  singleton locus and the zero-radius correction.
- Status: **verified refutation and correction**, not proof of the original
  unrestricted positive-radius claim. See `exercises.json` for review evidence
  and source/environment fingerprints.

## R11E18: equality case with a zero first function

- Source: book page 334, PDF page 343; page image checked.
- The asserted equivalence uses `g = c f` almost everywhere without a nonzero
  condition on `f`. If `f = 0` and `g` is not zero almost everywhere, equality
  holds but that scalar-multiple conclusion fails.
- `Rudin.Chapter11.exercise18_original_counterexample` uses the finite measure
  `Measure.dirac ()`, proves square integrability of `f = 0` and `g = 1`, proves
  the integral equality, and excludes every proposed scalar.
- `Rudin.Chapter11.exercise18` proves the complete correction for complex L2
  functions on arbitrary measures: equality holds if and only if `f = 0`
  almost everywhere or `g = c f` almost everywhere for some complex `c`.
  The source's conjugation convention and the norm-square integrals are
  connected to L2 by proved bridge theorems.
- Status: **verified refutation and correction**, not proof of the original
  unrestricted equivalence. The valid proportionality direction and the
  equivalence under an explicit nonzero hypothesis are also proved.

## Remaining issues

Other source questions are retained in `exercises.json` and the generated
[progress report](progress.md). They include possible false claims, notation
problems, quotient conventions, and open-ended scope. A pending issue is not
an established erratum. No unresolved issue is waived by the two corrections
above.
