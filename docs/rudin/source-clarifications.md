# Source clarification contracts

## Scope and evidence

This note records 19 source issues in 16 exercises. The initial discovery
covered 18 issues in 15 exercises; execution added R03E14's zero-bound check.
It follows P1 of `docs/plans/2026-10-22_rudin-lean4-plan.md`. The contracts below
are selected for implementation under the authorized plan. The inventory
records their obligation mappings; no proof is complete merely because its
contract has been selected.

References use the primary Third Edition PDF identified in
`docs/rudin/source.md`. PDF page numbers are one-based; book page numbers are
printed page numbers. The relevant complete extracts were read in
`.lake/rudin-source/ch02.txt` through `ch06.txt`, and `ch09.txt` through
`ch11.txt`. Primary PDF text and rendered images were inspected for every
exercise below: PDF pages 54, 87, 90, 108, 124, 127, 150, 250, 253, 299,
303–305, and 342. Definition context was inspected as specified below.
Scratch extracts and images are under `.lake/rudin-source/clarifications/`.
No alternate-scan comparison is claimed.

The classifications are:

1. **Convention/context:** source definitions or context determine the meaning.
2. **Correction:** the literal claim fails, or its expression is not defined.
   Retain the obstruction and a separately identified correction. An undefined
   expression is not a divergent series or a false numerical equality.
3. **Scope contract:** the source does not select a complete formal target.
   The proposed choice must be explicit before implementation.

Some issues have more than one classification under different readings.
The arguments below first established source contracts, not proof completion.
R02E28, R02E29, R03E06, R03E14, R03E18 and R04E09 now have independently
reviewed Lean proofs and pass project and isolated-source checks; their inventory
issues are resolved. R05E13 and R05E25 also have independently reviewed
proofs and pass project and isolated-source checks; their issues are resolved. Other entries
still require their counterexamples, corrected results, bridges, compilation,
semantic review and axiom audit. Contract selection alone is not completion.

## R02E28 — Countable does not include finite

- **Evidence:** exercise, book 45 / PDF 54, text and image. Definition 2.4,
  book 25 / PDF 34, text and image, distinguishes countably infinite from
  finite or countably infinite. Theorem 2.43, book 41 / PDF 50, text,
  excludes nonempty perfect countable subsets of Euclidean space.
- **Classification: 1.** The corollary uses Rudin's countably infinite meaning.
  Its set is therefore nonempty. There is no empty-set counterexample to that
  source reading. Replacing this meaning by Lean `Set.Countable` without a
  nonempty hypothesis would produce a different, false statement.
- **Reason:** a nonempty closed Euclidean set without isolated points is
  perfect and hence uncountable. The empty set has no isolated point.
- **Contract:** prove the decomposition for every closed subset of a separable
  metric space, including the empty subset. Translate the source corollary
  using countability plus infinitude. Also prove the stronger corollary for a
  nonempty at-most-countable closed Euclidean set. Record the failure of the
  empty version as a translation check, not as a source erratum. Do not extend
  this corollary to arbitrary separable metric spaces.
- **Affected IDs:** `R02E28.decomposition`, `R02E28.source_corollary`,
  `R02E28.empty_corollary`, `R02E28.nonempty_corollary`.
- **Verified:** `exercise28_decomposition`, `exercise28_source`,
  `exercise28_empty`, and `exercise28_nonempty`. The source reading is counted
  as stated; the empty-set result is a translation check.

## R02E29 — Segments, rays, and the whole line

- **Evidence:** exercise, book 45 / PDF 54, text and image; Definition 2.17,
  book 31 / PDF 40, text and image. The definition displays two endpoints and
  does not supply infinite endpoints. However, the proof of Theorem 10.38,
  book 278 / PDF 287, text and image, explicitly calls an open convex subset
  of the line a segment that can be unbounded.
- **Classification: 1 for the extended usage; 2 for a bounded-only reading.**
  Later source usage supports the intended open-interval interpretation. It
  does not justify silently treating two real endpoints as infinite endpoints.
- **Reason:** the line cannot be a disjoint union of bounded open segments.
  If there were more than one nonempty segment, one segment and the union of
  the rest would disconnect the line. A single bounded segment cannot cover it.
- **Contract:** construct the at-most-countable family of nonempty open
  interval components. Permit bounded intervals, either ray, and the whole
  line; use the empty family for the empty open set. Document this as the
  extended segment convention supported by book 278. Separately prove the
  bounded-segment obstruction already requested by the inventory. Do not
  remove that obligation on the basis of authorial intent.
- **Affected IDs:** `R02E29.source_segments`,
  `R02E29.bounded_segment_obstruction`,
  `R02E29.open_interval_decomposition`.
- **Verified:** `exercise29_source_segments`,
  `exercise29_bounded_segment_obstruction`, and
  `exercise29_open_interval_decomposition`. The inventory counts the
  bounded-only refutation and extended-interval correction separately from
  proofs of unmodified source claims.

## R03E06(d) — Undefined complex terms are a separate case

- **Evidence:** exercise, book 78 / PDF 87, text and image; reciprocal axiom
  1.12(M5) and division notation 1.13(a), book 5–6 / PDF 14–15, text;
  necessary term test 3.23, book 60 / PDF 69, text.
- **Classification: 1, with an explicit domain contract.** The question asks
  for investigation, not for convergence at every complex parameter. Source
  division does not define a reciprocal of zero.
- **Reason:** undefined parameters are exactly those satisfying
  `z^n = -1` for some positive integer `n`, equivalently roots of unity of
  even order. For admissible parameters, the series converges absolutely
  exactly when `|z| > 1`. For `|z| < 1` its terms tend to 1. For `|z| = 1`
  every defined term has modulus at least `1/2`, so the term test fails.
  When `|z| > 1`, the tail is bounded by `2 |z|^(-n)`.
- **Contract:** use indices `n >= 1`. First classify the domain by
  `forall n >= 1, 1 + z^n != 0`. Report failure of this condition as undefined,
  not divergent. Prove the convergence classification under that condition.
  Do not use Lean's totalized division to redefine the source series.
- **Affected IDs:** `R03E06.d.defined_parameters`,
  `R03E06.d.convergence`. Parts (a)–(c) are not affected by this issue.
- **Verified:** `exercise06_d_defined_parameters` and
  `exercise06_d_undefined_even` identify the excluded parameters.
  `exercise06_d_convergence` proves the full ordered-convergence classification
  under the domain condition. Undefined cases are not counted as divergence.

## R03E14(e) — A strict estimate with a zero bound

- **Evidence:** book 80 / PDF 89, primary page image. The outline prints
  `|s_n-s_i| < M*epsilon`, with only a finite bound `M`.
- **Classification: 2 for that intermediate estimate.** With `s_n=0` and
  `M=0`, all assumptions hold but the estimate says `0<0`, including at
  `i=n`. This does not refute the final Tauberian converse.
- **Contract:** retain the prescribed identities, floor choice, estimates
  and limsup argument. Prove `<= M*epsilon` for the original hypotheses.
  Retain the strict result under explicit `M>0` and prove the zero-bound
  obstruction at the source's floor index.
- **Affected ID:** added `R03E14.e.zero_bound_obstruction`; all ten original
  obligations remain. The book denominator is now 848, not 847.
- **Verified:** `exercise14_e_zero_bound_obstruction`,
  `exercise14_e_index_estimate`, and `exercise14_e_index_estimate_strict`.
  Independent review checked all eleven obligations and the full prescribed
  argument. The source's final converse is proved without a stronger bound.

## R03E18 — Keep the inherited starting bound

- **Evidence:** Exercises 16 and 18, book 81 / PDF 90, text and image.
  Exercise 18 replaces the recursion, not the other hypotheses of Exercise 16.
- **Classification: 1 for the inherited data; 3 for the requested description.**
  Retain `alpha > 0` and `x_1 > sqrt(alpha)`. The source does not say to
  replace the square root in the starting bound by a p-th root, and does not
  assert that the new sequence decreases from its first term.
- **Reason:** let `r > 0` satisfy `r^p = alpha`. For `p >= 2`, the update
  `N(x) = ((p-1)x + alpha*x^(1-p))/p` satisfies `N(x) >= r` for every
  positive `x`, with equality only at `r`. Also
  `N(x)-x = (alpha-x^p)/(p*x^(p-1))`. Thus a start below `r` increases once
  to above `r` and then decreases to `r`; a start at `r` is constant; a start
  above `r` decreases to `r`. The inherited bound can allow a start below
  `r`: take `alpha = 1/64`, `p = 3`, `x_1 = 3/16`.
- **Contract:** prove positivity and well-definedness. For `p = 1`, the second
  and all later terms equal `alpha`. For `p >= 2`, prove all three cases
  relative to `r`, including the possible first-step change of direction.
  Proving the description for all positive starts is acceptable only with an
  explicit specialization to the inherited hypotheses. Do not strengthen
  the starting bound to obtain monotonicity from the first term.
- **Affected IDs:** `R03E18.well_defined`, `R03E18.unit_exponent`,
  `R03E18.higher_exponents`.
- **Verified:** `exercise18_well_defined` and `exercise18_source_update`
  preserve the inherited data and integer exponent. The unit-exponent
  theorems and `exercise18_higher_exponents` give the full classification,
  including a proved inherited-bound example with an initial overshoot.

## R04E09 — Empty diameter needs an explicit extension

- **Evidence:** exercise, book 99 / PDF 108, text and image. Definition 3.9,
  book 52 / PDF 61, text, defines diameter only for nonempty sets. Uniform
  continuity is Definition 4.18, book 90 / PDF 99, text.
- **Classification: 3, a notation extension, not a substantive false theorem.**
  The exercise quantifies over all subsets, but its diameter definition does
  not cover the empty subset.
- **Reason:** setting the empty diameter to zero makes its image condition
  automatic for every positive epsilon. For nonempty sets, uniform continuity
  with output tolerance `epsilon/2` bounds the image diameter by
  `epsilon/2 < epsilon`. The reverse implication uses two-point sets.
- **Contract:** use extended nonnegative diameter, zero on the empty set and
  infinity on unbounded sets. Compare with finite positive real tolerances.
  Prove agreement with Definition 3.9 whenever its diameter is finite, then
  prove both implications with all subsets, including empty subsets. An
  alternative nonempty-only statement must be identified explicitly.
  Do not use a real-valued diameter that assigns zero to unbounded sets
  without adding boundedness hypotheses and proving the comparison.
- **Affected IDs:** `R04E09.uniform_to_diameter`,
  `R04E09.diameter_to_uniform`, `R04E09.diameter_convention`.
- **Verified:** `exercise09_diameter_empty`, `exercise09_diameter_unbounded`,
  and `exercise09_diameter_agrees` prove the selected extension and comparison.
  Both uniform-continuity implications quantify over all subsets with strict
  tolerances. This is a convention resolution, not a false-source refutation.

## R05E13 — The negative-base real power is not defined

- **Evidence:** exercise, book 115 / PDF 124, text and image. The image
  prints `x^a`, not `|x|^a`. Chapter 5 treats real-valued functions, book 103 /
  PDF 112, text. Exercise 1.6, book 22 / PDF 31, text, constructs real powers
  for a positive base; the explicit definition (43), book 181 / PDF 190,
  text, likewise requires a positive base. Endpoint derivatives are one-sided
  under Definition 5.1, book 103–104 / PDF 112–113, text.
- **Classification: 2, a domain defect requiring a correction.** No inspected
  definition makes the printed expression real-valued on the whole interval
  for arbitrary real `a`. In particular, `a = 1/2` requires square roots of
  negative numbers. A choice of complex powers would change the problem.
- **Reason:** the factor `|x|^(-c)` is defined off zero, but it does not repair
  the factor `x^a`. Replacing that factor by `|x|^a` gives a real function and
  the stated seven thresholds. Away from zero it is smooth. Its leading
  oscillatory derivative terms have sizes `|x|^(a-c-1)` and
  `|x|^(a-2c-2)`; difference quotients at zero give the other thresholds.
- **Contract:** retain and formalize the negative-base obstruction. Label
  `F(0)=0`, `F(x)=|x|^a sin(|x|^(-c))` for nonzero `x` as a correction,
  not an OCR repair established by the source. Prove all seven equivalences
  for this corrected function: continuity `a>0`; derivative at zero `a>1`;
  bounded first derivative `a>=1+c`; continuous first derivative `a>1+c`;
  second derivative at zero `a>2+c`; bounded second derivative
  `a>=2+2c`; continuous second derivative `a>2+2c`. Boundedness and
  continuity of derivatives include their existence at zero, and use
  one-sided derivatives at the endpoints. Keep the source assumption `c>0`.
  This absolute-power correction is explicitly selected for implementation;
  the negative-base obstruction remains a separate proof obligation.
- **Affected IDs:** `R05E13.a`, `R05E13.b`, `R05E13.c`, `R05E13.d`,
  `R05E13.e`, `R05E13.f`, `R05E13.g`. The domain-obstruction proof is separately mapped to
  `R05E13.domain_obstruction`.
- **Verified:** `exercise13_a` through `exercise13_g` prove all thresholds for
  the labelled correction; `exercise13_domain_obstruction` preserves the
  original domain defect. Local derivative and equality-case bridges are
  proved. This exercise is counted as corrected, not as stated.

## R05E25 — Newton termination and a zero curvature bound

- **Evidence:** exercise, book 118 / PDF 127, text and image. The image has
  `f' >= delta > 0`, `0 <= f'' <= M`, strict descent in (b), an interior
  Taylor point in (c), and division by `A = M/(2 delta)` in (d). These are
  not OCR-generated strictness or denominator errors.

### Finite termination

- **Classification: 2.** On `[-1,1]`, take `f(x)=x`, root `xi=0`,
  `delta=1`, `M=1`, and `x_1=1/2`. All source hypotheses hold. The second
  iterate is zero and remains zero. Thus (b)'s strict inequality fails from
  the second step, and (c)'s interval `(xi,x_n)` is empty after termination.
- **Contract:** define the infinite iteration, with the root an absorbing
  fixed point. Prove `xi <= x_(n+1) <= x_n`, strict descent exactly while
  `x_n > xi`, and convergence to `xi`. State the Taylor-point identity only
  when `x_n > xi`; handle `x_n = xi` separately by zero error. Preserve
  formal refutations of the unrestricted strict descent and interior-point
  claims. Do not assume strict convexity to avoid termination.
- **Affected IDs:** `R05E25.a.iteration`, `R05E25.b.descent`,
  `R05E25.b.convergence`, `R05E25.c`.

### The case M = 0

- **Classification: 2 for the undefined displayed estimate.** The same
  example permits `M=0`, so `A=0`. The printed reciprocal is then undefined,
  even though Newton's method itself works and terminates in one step.
- **Contract:** prove `0 <= e_(n+1) <= A*e_n^2`, where `e_n=x_n-xi`, and
  for `n >= 1` prove the denominator-free estimate
  `e_(n+1) <= A^(2^n-1) * e_1^(2^n)` for `M >= 0`. Recover the printed
  estimate only under `A > 0`. Prove immediate termination when `M=0`.
  Do not interpret the printed expression using totalized division.
- **Affected ID:** `R05E25.d`; its one-step estimate also uses
  `R05E25.c` with the termination case split.

The root and tangent contracts need no correction. For (e), use
`g'=f*f''/(f')^2`; bounded `f''` and `f'>=delta` give `g'(x)->0` near the
root without assuming continuity of `f''`. The correction does not remove
`R05E25.root`, `R05E25.a.tangent`, `R05E25.e.fixed_point`,
`R05E25.e.derivative`, or `R05E25.f` from the exercise's requirements.
All false-claim proofs now have explicit registry mappings.
`exercise25_termination_counterexample` refutes the two unrestricted claims;
`exercise25_denominator_free`, `exercise25_printed_bound`, and the zero-bound
results prove the selected corrections. The source prints `x_1` in `(xi,b)`;
the verified construction also admits `x_1=b` using the source one-sided
endpoint derivatives. This exercise is counted as corrected, not as stated.

## R06E18 — Continuity forces the missing endpoint

- **Evidence:** exercise, book 141 / PDF 150, text and image. The third
  exponent is `2*pi*i*t*sin(1/t)`. Definition 6.26, book 136 / PDF 145,
  text, requires a curve to be a continuous mapping on its closed interval.
- **Classification: 1 determines the unique extension; the printed formula
  still has a domain omission.** Since `|t*sin(1/t)| <= |t|`, the only
  endpoint value consistent with a curve is `gamma_3(0)=1`.
- **Reason:** continuity at zero does not imply finite length. Away from zero,
  the phase derivative is `2*pi*(sin(1/t)-cos(1/t)/t)`. Its absolute integral
  diverges near zero; the term involving `|cos(1/t)|/t` causes the divergence.
- **Contract:** define the third curve piecewise, with value 1 at zero, and
  prove continuity before its range or length claims. Keep the printed
  formula only for positive `t`. Prove the common unit-circle range, lengths
  `2*pi` and `4*pi` of the first two curves, and infinite variation of the
  extended third curve. Do not replace the phase by `sin(1/t)` alone.
- **Affected IDs:** `R06E18.common_range`, `R06E18.first_length`,
  `R06E18.second_length`, `R06E18.third_nonrectifiable`. The first two
  length claims do not depend on the endpoint repair, but remain required.

## R09E19 — Solvability is local to a solution branch

- **Evidence:** exercise, book 241 / PDF 250, text and image. The implicit
  function theorem 9.28, book 224–225 / PDF 233–234, text, provides a unique
  graph in a neighborhood of a specified solution, not a global graph.
- **Classification: 1.** The surrounding theorem supplies the local meaning
  of solvability. A global unique graph would be a different assertion.
- **Reason:** eliminating `y,z` gives
  `z=-4x-4u`, `y=-7x-7u`, and `u(u-3)=0`. The solution set is the two
  affine lines
  `(x,y,z,u)=(s,-7s-7c,-4s-4c,c)`, with `c=0` or `c=3`.
  On either line, `x`, `y`, or `z` is a valid free parameter. The coordinate
  `u` is constant, and arbitrarily close distinct solutions have the same `u`.
- **Contract:** classify the full solution set, then for every solution
  choose a neighborhood excluding the other value of `u`. Prove local unique
  smooth graphs over open intervals of each of `x,y,z`, agreeing with all
  solutions in that neighborhood. Prove that no neighborhood of a solution
  gives a unique graph over `u`, not merely that a Jacobian minor vanishes.
  Do not claim global uniqueness across both lines, or rule out a constant
  choice of a single solution while overlooking the rest of the solution set.
- **Affected IDs:** `R09E19.solve_in_z`, `R09E19.solve_in_y`,
  `R09E19.solve_in_x`, `R09E19.failure_in_u`.

## R09E31 — A nonzero Hessian need not decide an extremum

- **Evidence:** exercise, book 244 / PDF 253, text and image. The hypothesis
  says that some second derivative is nonzero, not that the Hessian is
  nonsingular. The preceding Taylor exercise is on book 243–244 /
  PDF 252–253, chapter extract and primary PDF 253 image.
- **Classification: 2.** The stated hypothesis is insufficient for complete
  classification by the quadratic Taylor polynomial.
- **Reason:** `f_+(x,y)=x^2+y^4` and `f_-(x,y)=x^2-y^4` are smooth,
  have zero gradient and Hessian `diag(2,0)` at zero, and have the same
  degree-two Taylor polynomial. The first has a strict local minimum; the
  second has neither a local minimum nor a local maximum.
- **Contract:** formally refute determination from the degree-two polynomial
  under the printed hypotheses. Prove the corrected second-derivative test:
  positive definite implies a strict local minimum; negative definite implies
  a strict local maximum; indefinite implies neither. A nonzero singular
  semidefinite Hessian is inconclusive for the full classification. For a
  positive semidefinite nonzero Hessian, a local maximum is excluded; reverse
  signs for the negative case. Preserve these partial conclusions.
  In dimension one the nonzero second derivative is decisive. In every
  dimension at least two, add positive squares in the extra coordinates to
  the example to obtain the same obstruction. Do not discard singular cases.
- **Affected IDs:** `R09E31.planar_classification`,
  `R09E31.higher_dimensions`, `R09E31.semidefinite_counterexample`,
  `R09E31.corrected_test`.

## R10E09–R10E10 — Polar variable order and the slit

- **Evidence:** both exercises, book 290 / PDF 299, text and image;
  Definitions 10.1–10.3 and Theorem 10.2, book 245–247 /
  PDF 254–256, text; change of variables 10.9, book 252–253 /
  PDF 261–262, text. The compact-domain regularity convention on book 253 /
  PDF 262 was also inspected.

### Printed integration order

- **Classification: 2 for the ordinary nested-integral reading.** The image
  places the radial upper bound first and the angular upper bound second,
  followed by `dr dtheta`. The source context does not establish a special
  binding rule that would remove the mismatch.
- **Reason:** under the usual nested reading the inner differential `dr`
  gets the angular bound. Even for the globally constant function 1 and
  `a=1`, that reading gives `2*pi^2`, not the disk area `pi`. For a general
  function defined only on the disk it can also request values outside its
  domain. Order independence for a fixed rectangle does not repair incorrect
  variable-bound assignments.
- **Contract:** write the disk formula unambiguously as
  `integral r=0..a (integral theta=0..2*pi f(T(r,theta))*r dtheta) dr`,
  or with both integration order and differentials reversed. Use `a>=0`;
  handle `a=0` separately. For the whole plane replace the radial upper
  bound by infinity. Preserve the printed notation discrepancy and a formal
  literal-reading obstruction; do not describe it as a failure of the
  corrected polar-coordinate theorem.
- **Affected IDs:** `R10E09.polar_integral`,
  `R10E10.whole_plane_polar`, `R10E10.gaussian`. Literal-reading evidence
  needs an explicit mapping at integration time.

### The hint's slit

- **Classification: 1 identifies the mismatch; 3 selects the branch contract.**
  The stated parameter interior `(0,a) x (0,2*pi)` maps to the disk interior
  minus the origin and the positive x-axis radius. The hint instead removes
  the radius to `(0,a)`, on the positive y-axis. That target is not the image
  of the stated open parameter rectangle.
- **Contract:** retain `T(r,theta)=(r*cos(theta),r*sin(theta))` and the stated
  angular interval. Apply 10.9 on the positive-x-axis slit disk, then justify
  removal of the support restriction and the omitted boundary and radius by
  approximation as requested. A positive-y-axis slit would instead require
  an angular interval such as `(pi/2,5*pi/2)`. Record whichever branch is
  used; do not assert that the original rectangle is a diffeomorphism onto
  the hint's slit domain.
- **Affected IDs:** `R10E09.interior_injectivity`,
  `R10E09.polar_integral`; also `R10E10.whole_plane_polar` if it reuses
  this change-of-variables argument. `R10E09.range` and
  `R10E09.jacobian` remain unchanged.

### Whole-plane decay scope

- **Classification: 3.** Exercise 10 expressly requests a precise version of
  sufficiently rapid decrease.
- **Contract:** one sufficient choice is continuous real or complex `f` with
  `|f(x)| <= C*(1+||x||)^(-q)` for some `C>=0` and real `q>2`.
  Define the plane improper integral by expanding disks and prove absolute
  convergence and agreement with expanding rectangles. Define the radial
  improper integral by a radial cutoff with the full angular interval.
  Prove the polar identity by passage to the limit, and check the Gaussian
  satisfies the bound before deriving its one-dimensional integral. A
  Lebesgue formulation requires an explicit comparison with these integrals.
- **Affected IDs:** `R10E10.decay_condition`,
  `R10E10.whole_plane_polar`, `R10E10.gaussian`.

## R10E22(c) — Positive radial scale does not exclude the origin

- **Evidence:** exercise, book 294–295 / PDF 303–304, text and images.
  Definitions 10.10–10.11 and integral rule (35), book 254 / PDF 263, text,
  require the surface to map into the domain of the form.
- **Classification: 2, a domain defect.** `g>0` does not ensure that
  `Phi(s,t)=g(t)h(s)` avoids zero. The form is defined only off zero.
- **Reason:** take `g=1` and all three components of `h` identically zero.
  These are smooth allowed data, but the displayed integral is undefined.
  Vanishing Jacobian minors do not make undefined form coefficients defined.
  If `h(s)!=0`, the corrected pullback vanishes because
  `Phi dot (Phi_s cross Phi_t)=0`: both `Phi` and `Phi_t` are proportional
  to `h`.
- **Contract:** retain the origin obstruction, then prove (c) under the
  separately marked condition `forall s in [0,1], h(s)!=0`. Do not extend
  the singular form to zero using totalized division. In (d), positivity of
  the radius and the unit norm of `Sigma` already establish avoidance of
  zero for the radial homotopy, including its side surfaces. Record this
  fact when using corrected (c); it is not an extra missing assumption in (d).
- **Affected IDs:** `R10E22.c`, `R10E22.origin_obstruction`,
  `R10E22.corrected_radial_surface`, and the use of (c) in `R10E22.d`.
  The separate proof required by `R10E22.f` must still avoid use of (c).

## R10E23 — Degree zero and the open extension request

- **Evidence:** exercise, book 295–296 / PDF 304–305, text and images;
  Exercises 21–22, book 292–295 / PDF 301–304, chapter extract, with
  PDF 303–304 images; Definition 10.11, book 254 / PDF 263, text;
  Definition 10.34 and Remarks 10.35, book 275–276 / PDF 284–285, text.

### Part (c), n = 1

- **Classification: 3, not a source-defined negative-degree construction.**
  The chapter defines 0-forms, but exactness requires a form one degree
  lower. It supplies no negative-degree forms. For `n=1`, `omega_1` is the
  locally constant function `x/|x|` on the punctured line, so closedness is
  meaningful but source exactness in degree zero is not specified.
- **Contract:** state the source exactness question and its negative answer
  for `n>=2`, using the nonzero integral on the outward-oriented unit sphere
  as obstruction. Explicitly retain the `n=1` domain-of-definition issue.
  If a uniform all-dimensions exactness predicate is wanted, state the added
  convention that the image in degree zero is `{0}`. Under that convention
  `omega_1` is not exact because it is not zero. Do not infer a primitive
  from local constancy, or silently omit dimension one. Part (a) must include
  `k=1`; part (b) already has `k>=2`.
- **Affected IDs:** `R10E23.a`, `R10E23.c`. The prescribed primitive in
  `R10E23.b` keeps its original scope.

### Part (d), selected extensions

- **Classification: 3.** The source asks for some further extensions and does
  not select them. No source-only inspection can determine a unique list.
- **Selected finite contract:** prove the following two extensions for every
  `n>=2`, and identify them by name in the eventual formal statements:
  - **Sphere flux:** the integral of `omega_n` on the outward-oriented unit
    sphere equals its positive `(n-1)`-dimensional area. Use the boundary
    orientation of the unit ball; a chain or chart representation must
    account for face cancellation. Do not assume the nonzero integral as
    the definition of the area.
  - **Radial invariance:** for every compact parameter cell or simplex
    `K` of dimension `n-1`, every `C2` map
    `sigma: K -> S^(n-1)`, and every positive `C2` scalar function `rho`
    on `K`, the pullbacks of `omega_n` along `rho*sigma` and `sigma`
    are equal, hence their oriented integrals agree. Use the same parameter
    orientation on both maps. Rank deficiency is allowed. Compact-domain
    `C2` means extension to an open neighborhood, as on book 253 / PDF 262.
  These generalize the sphere and radial-surface assertions in Exercise 22.
  They do not assert that all claims of Exercises 21–22 extend unchanged.
  Dimension one is handled separately above, not through a presumed
  negative-degree primitive or an undefined sphere integration API.
- **Affected IDs:** `R10E23.d.formulation`,
  `R10E23.d.generalization`; sphere flux also supplies the obstruction for
  `R10E23.c`. This list fixes the finite implementation scope; it does not
  introduce an external approval gate.

## R11E11 — Use almost-everywhere equivalence classes

- **Evidence:** exercise, book 333 / PDF 342, text and image. Remark 11.37,
  book 326 / PDF 335, text and image, explicitly identifies functions equal
  almost everywhere to obtain a metric in `L2`. The concluding discussion
  on book 332 / PDF 341, chapter extract, repeats that identification.
- **Classification: 1.** The same quotient convention supplies the intended
  `L1` metric. Pointwise separation on raw functions would be false, but is
  not required under the chapter's identification convention.
- **Reason:** on the unit interval with Lebesgue measure, zero and the
  indicator of a singleton are distinct integrable functions at distance
  zero. In general the distance vanishes exactly for almost-everywhere equal
  integrable functions.
- **Contract:** retain the raw-function degeneracy example. Define the metric
  on integrable real or complex functions modulo almost-everywhere equality,
  prove representative independence and the distance-zero equivalence, then
  prove completeness on that quotient. A Mathlib `Lp` model at exponent 1
  is suitable only with a proved identification of its distance and the
  displayed integral. Do not impose finite total measure or pointwise
  convergence as additional source requirements.
- **Affected IDs:** `R11E11.distance`, `R11E11.completeness`,
  `R11E11.raw_function_degeneracy`.

## Implementation contracts and remaining proof gates

1. Apply the explicitly selected extensions and scope choices: unbounded interval
   components in R02E29; empty/extended diameter in R04E09; the corrected
   absolute-power function in R05E13; Newton's absorbing-root convention
   and denominator-free estimate; the piecewise endpoint in R06E18; polar
   variable order, slit, and improper-integral scope; and the degree-zero
   convention and selected extensions in R10E23.
2. Preserve formal obstruction/correction work for the bounded-only segment
   reading, R05E13's domain, R05E25's termination and zero-bound expressions,
   R09E31's semidefinite Hessian, literal polar bounds, and R10E22's origin.
   The second batch adds eight explicit obligations for source-domain,
   termination, endpoint, literal-order, diameter and degree-zero checks.
   Exercise count remains 287. The second batch changed the obligation count
   from 839 to 847. The fourth batch added R03E14's strict-estimate obstruction,
   giving 848. The inventory records the exact IDs and source-page evidence.
3. Compile and review all required proofs and bridges before closing any
   affected obligation. Definition-based clarification, source images, and
   the arguments in this note do not waive any mandatory proof gate.
