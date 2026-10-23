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

## R02E28: countability translation

- Source: book page 45, PDF page 54; Definition 2.4 distinguishes countably
  infinite from finite-or-countable sets.
- The source corollary already excludes the empty set under its own convention.
  `exercise28_source` uses countability and infinitude. This is not a source
  refutation.
- `exercise28_nonempty` proves the stronger at-most-countable result with an
  explicit nonempty hypothesis. `exercise28_empty` refutes the translation
  without that hypothesis. `exercise28_decomposition` includes empty sets.
- Status: verified convention and translation check; counted as stated.

## R02E29: bounded segments do not cover the line disjointly

- Source: book page 45, PDF page 54. Definition 2.17 displays finite real
  endpoints. Later usage on book page 278 permits unbounded segments.
- `exercise29_bounded_segment_obstruction` proves that the open connected
  whole real line cannot be covered by any pairwise-disjoint family of
  finite-endpoint open segments. Countability does not repair that reading.
- `exercise29_open_interval_decomposition` constructs the countable family
  of nonempty open connected components. Each is a bounded interval, an open
  ray, or the whole line. `exercise29_source_segments` uses this explicitly
  extended convention; the empty input uses the empty family.
- Status: verified refutation of the bounded-only reading and explicit
  extended-interval correction. Counted as refuted/corrected, not as proof of
  the finite-endpoint claim. This does not refute the later extended usage.

## R03E14(e): zero bound in the strict intermediate estimate

- Source: book page 80, PDF page 89; primary page image checked.
- The outline prints `|s_n-s_i| < M*epsilon`, but permits `M=0`.
  `exercise14_e_zero_bound_obstruction` uses the constant zero sequence and
  proves strict failure for every positive final index with the prescribed
  floor index. All bound and mean-convergence assumptions hold.
- `exercise14_e_index_estimate` proves `<= M*epsilon` without a stronger
  assumption. `exercise14_e_index_estimate_strict` proves the printed strict
  inequality under the separately stated `M>0` hypothesis.
- Status: verified refutation and correction of the intermediate estimate.
  The final Tauberian converse is valid and proved by the required outline.
  All ten original obligations remain; the new obstruction is an eleventh
  obligation. The current inventory denominator is 849.

## R05E13: real powers on negative inputs

- Source: book page 115, PDF page 124; the image prints `x^a`, not `|x|^a`.
  Rudin's real-power construction does not define arbitrary real powers on
  negative inputs. `exercise13_domain_obstruction` proves that no real square
  root of `-1` exists, covering the allowed choice `a=1/2`, `x=-1`.
- The explicitly corrected `exercise13F` uses `|x|^a` off zero and value zero
  at zero. `exercise13_a` through `exercise13_g` prove all seven sharp
  thresholds for `c>0`: `a>0`, `a>1`, `a>=1+c`, `a>1+c`, `a>2+c`,
  `a>=2+2c`, and `a>2+2c`, respectively.
- Derivative assertions include genuine existence and one-sided endpoint
  derivatives. `exercise13_e_local_iff_interval` connects the local
  second-derivative condition to interval witnesses. The two equality-case
  theorems prove boundedness without continuity at the non-strict thresholds.
- Status: verified domain obstruction and explicit correction, not an OCR
  repair or proof of the printed arbitrary-real-power formula. All names are
  in `Rudin.Chapter05`.

## R05E25: finite Newton termination and zero curvature

- Source: book page 118, PDF page 127. The printed all-step strict descent
  fails after termination; its interior Taylor interval then becomes empty.
  `exercise25_termination_counterexample` verifies an admissible affine
  example and proves both failures.
- The actual infinite iteration absorbs the root. `exercise25_iteration`,
  `exercise25_strict_step`, and `exercise25_convergence` prove its invariant,
  weak descent, strict descent off the root, and convergence. The Taylor
  theorem is split into off-root and terminated cases.
- `exercise25_denominator_free` includes zero curvature. The printed form
  requires `A>0`; `exercise25_zero_A_termination` proves immediate termination
  at `A=0`. `exercise25_zero_bound_domain_obstruction` proves that zero has
  no multiplicative inverse, rather than using totalized division.
- Both derivatives are genuine within derivatives on the closed interval.
  No continuity of the second derivative is assumed. The source starts in
  `(xi,b)`; the verified construction also permits `x_1=b`.
- Status: verified refutation and correction of the affected subclaims.
  Root, tangent, derivative, and cube-root questions remain included and are
  proved. All names are in `Rudin.Chapter05`.

## R06E18: the missing endpoint of the third curve

- Source: book page141, PDF page150; Definition6.26 requires continuity on
  the closed interval. The printed expression contains `1/t` at `t=0`.
- `Rudin.Chapter06.exercise18_printed_endpoint_obstruction` proves that zero
  has no multiplicative inverse. Totalized reciprocal notation does not
  supply the missing source definition.
- The corrected curve explicitly has `gamma3(0)=1` and the printed formula
  for positive `t`. `exercise18_endpoint_extension` proves continuity;
  `exercise18_endpoint_unique` proves that this extension is unique.
- `exercise18_common_range` proves the common unit-circle range. The three
  actual partition lengths are `2*pi`, `4*pi` and infinity; the third curve
  is not rectifiable despite continuity.
- Status: verified domain obstruction and explicit endpoint correction.
  Counted as corrected, not as a defined literal source formula.

## R09E19: local solution branches

- Source: book page 241, PDF page 250. The implicit-function question is local
  to each solution, not a claim of global uniqueness across both branches.
- `Rudin.Chapter09.exercise19_solve_in_x`, `exercise19_solve_in_y`, and
  `exercise19_solve_in_z` classify both branches, with `u=0` or `u=3`.
  `exercise19_local_graphs` and `exercise19_smooth_graphs` supply the actual
  neighborhood graphs and their regularity.
- `exercise19_failure_in_u` constructs distinct solutions with the same `u`
  in every neighborhood of every solution. A zero minor alone is not used
  to infer failure.
- Status: verified local-graph convention; counted as stated, not as a source
  refutation.

## R09E31: a nonzero Hessian does not classify every extremum

- Source: book page 244, PDF page 253. The printed condition permits a
  nonzero singular semidefinite Hessian.
- `Rudin.Chapter09.exercise31_counterexample` and `exercise31_planar_formula`
  give the actual functions `x²+y⁴` and `x²-y⁴`. They have the same quadratic
  Taylor polynomial and Hessian `diag(2,0)`, but only the first has a local
  minimum. The construction extends to every dimension at least two.
- The negative-semidefinite examples have matching negative jets and different
  maximum behavior. Dimension one has a separate complete sign test;
  dimension zero cannot have a nonzero Hessian.
- `exercise31_quadratic_expansion` derives the Peano remainder from local C3
  hypotheses. `exercise31_positive_test`, `exercise31_negative_test`,
  `exercise31_indefinite_test`, and `exercise31_semidefinite_exclusions` prove
  the valid tests without assuming the expansion or the extremum.
- Status: **verified refutation and correction**, not proof of the printed
  nonzero-Hessian classification. All four obligations passed independent
  page/type/body review and the Chapter 8–9 project gate.

## R10E09: polar bounds and the angular seam

- Source: book page 290, PDF page 299; primary and comparison images checked.
- Under the usual nested binding, the printed bounds and differentials give
  $2\pi^2$ for the unit-disk constant example, rather than its source area
  $\pi$. `Exercise09.literal_order_obstruction` and
  `Exercise09.literal_disk_obstruction` prove this discrepancy.
- The correction states the radial-outer, angular-inner order explicitly.
  Its real and complex versions have literal repeated source witnesses on
  both the closed disk and the polar rectangle. Independent disk and polar
  dominated-convergence limits prove the required approximation argument.
- The stated angular interior omits the positive $x$-axis, not the positive
  $y$-axis from the hint. `Exercise09.printed_y_seam_obstruction` proves the
  mismatch; `Exercise09.image_slit` identifies the corrected image.
- Status: **verified refutation and correction** of these printed choices.
  All names have prefix `Rudin.Chapter10`.

## R10E10: improper polar binding

- Source: book page 290, PDF page 299.
- For the Gaussian, the literal printed binding gives
  $A(1-\exp(-(2\pi)^2))/2$, which tends to positive infinity.
  `Exercise10.literal_order_obstruction` and
  `Exercise10.literal_no_finite_value` prove that it has no finite value.
- The corrected angular-inner formula has ordinary and absolute improper
  source limits. The selected sufficient decay condition has a nonnegative
  bound and exponent greater than two. No necessity claim is made.
- The Gaussian value is derived through the finite source polar approximation
  and exhaustion, followed by Cartesian product integration.
- Status: **verified refutation and correction**, not proof of the printed
  binding. All names have prefix `Rudin.Chapter10`.

## R10E22(c): a radial curtain can pass through the origin

- Source: book pages 294–295, PDF pages 303–304.
- The printed positivity condition on the radial scale does not make the
  direction nonzero. The allowed smooth data `g=1`, `h=0` map the whole
  curtain to the origin, outside the domain of the radial form.
- `Exercise22.origin_obstruction` proves this domain defect. The corrected
  curtain explicitly requires nonvanishing direction. Its zero pullback is
  proved for a scale depending on both parameters, not just separable scales.
- The radial-homotopy and primitive/pole-limit invariance arguments remain
  separate proofs. Neither uses the uncorrected assertion.
- Status: **verified refutation and correction**, not proof of the printed
  domain claim. See the full declarations for `R10E22.origin_obstruction`
  and `R10E22.corrected_radial_surface` in the inventory.

## R10E23: extension scope and degree zero

- Source: book pages 295–296, PDF pages 304–305.
- The open-ended extension is explicitly fixed to whole-sphere flux and
  positive radial invariance, including literal cell/simplex source witnesses.
  Actual sphere coverage, signed face cancellation and strictly positive
  independently defined Gram area are proved.
- Positive-degree nonexactness covers every ambient dimension at least two.
  In degree zero, exactness is explicitly added as vanishing, or image
  contained in $\{0\}$. The punctured-line form is closed but not exact under
  that convention. No negative-degree primitive is attributed to the book.
- The $S^0$ extension has counting area and signed flux two, with ordinary
  boundary zero rather than augmentation.
- Status: **verified scope and convention**, counted as stated under the
  documented contract, not as a refuted source claim. The prescribed
  positive-degree primitive is also proved with its exact lower endpoint,
  exponent and sign. See `Exercise23.Primitive.prescribed_primitive`,
  `Exercise23.Sphere.wholeSphere_flux` and the full inventory mapping.

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
an established erratum. No unresolved issue is waived by the verified
resolutions above.
