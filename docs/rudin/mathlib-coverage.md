# Mathlib coverage and P3 risks

## Result and scope

The pinned Mathlib supplies many required objects, but no single API identifies Rudin's integrals, oriented chains and Stokes theory. The current Stieltjes modules prove the actual Darboux/tagged equivalence and a continuous real-integrand measure bridge with explicit right-continuity hypotheses. Oriented parameterized chains and general Stokes integration remain incomplete.

Evidence uses Lean `v4.35.0` and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All Mathlib paths below are relative to `.lake/packages/mathlib/Mathlib/`. `Math/Rudin/Support/ApiExamples.lean` contains compiled `#check` probes and usage proofs for the listed topics. This is a topic survey, not a verified classification of every exercise.

## Coverage map

| Chapters/topic | Available declarations and source | Classification and remaining work |
| --- | --- | --- |
| 1: cuts and real numbers | `Order/Completion.lean`: `DedekindCut.principal`, `principalEmbedding`, `factorEmbedding`. `Basic/Real/Basic.lean`: `Real.equivCauchy`, `Real.mk_eq`. | **Bridge/new construction.** `DedekindCut` is the Dedekind–MacNeille completion. A principal left set is `Iic q`, with a greatest element. It is not Rudin's nonempty proper rational lower cut without a greatest element. Mathlib's real numbers use a Cauchy construction. `R01E20` now has a literal modified-cut model in `Chapter01/Exercise20.lean`, including the new closed zero and inverse failure. It is not identified with `ℝ`; source cuts with no greatest element require a separate comparison when needed. |
| 2–3: metric completion | `Topology/UniformSpace/Completion.lean`: `UniformSpace.Completion`, `denseRange_coe`, `extension_coe`. `Topology/MetricSpace/Completion.lean`: `UniformSpace.Completion.coe_isometry`. | **Direct use, with a construction bridge when required.** The completion is a separation quotient of Cauchy filters. Isometry, density, extension, and completeness are available. `R03E24` supplies the actual Cauchy-sequence quotient and a proved isometric identification with this completion, including its limit-distance metric and the empty-space case. |
| 5, 7: ODE | `Analysis/ODE/ExistUnique.lean`: `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀`, `ODE_solution_unique`. | **Direct use under checked hypotheses.** Existence requires completeness and local regularity/bounds. The checked uniqueness theorem uses Lipschitz control, continuity on `Icc`, and right-sided derivatives on `Ico`. Do not change a problem's endpoint or initial-value conditions to fit it. |
| 6: Stieltjes measures | `MeasureTheory/Measure/Stieltjes.lean`: `StieltjesFunction`, `measure_Ioc`, `measure_Icc`, `measure_singleton`, `Monotone.stieltjesFunction_eq`. | **Bridge required.** A Stieltjes function is monotone and right-continuous. Its measure is not a definition of Rudin's Riemann–Stieltjes integral. See the endpoint test below. |
| 6, 10: tagged integrals | `Analysis/BoxIntegral/Basic.lean`: `BoxIntegral.HasIntegral`, `Integrable.hasIntegral`. `Analysis/BoxIntegral/Partition/Filter.lean`: `IntegrationParams.Riemann`. `Analysis/BoxIntegral/Partition/Additive.lean`: `BoxAdditiveMap.upperSubLower`. `Analysis/BoxIntegral/Integrability.lean`: `MeasureTheory.IntegrableOn.hasBoxIntegral`, `MeasureTheory.ContinuousOn.hasBoxIntegral`, `MeasureTheory.AEContinuous.hasBoxIntegral`. | **Existing bridge components.** Box integrals accept box-additive increments, not just Lebesgue volume. The continuous-function bridge works for the Riemann parameter and any locally finite measure; a compiled one-dimensional-box example verifies this. The general `IntegrableOn` bridge requires `bRiemann = false`. Neither result alone identifies arbitrary Rudin Darboux sums with these filters. |
| 8: Fourier | `Analysis/Fourier/AddCircle.lean`: `fourierCoeff`, `fourierCoeff_eq_intervalIntegral`, `hasSum_fourier_series_L2`, `tsum_sq_fourierCoeff`. `Analysis/Fourier/FourierTransform.lean`: `Real.fourier_real_eq_integral_exp_smul`. | **Direct use plus normalization checks.** Periodic coefficients use normalized Haar measure and a `1/T` interval formula. The real-line transform uses the exponential with `-2πivw`. L² convergence does not imply pointwise or uniform convergence. |
| 8: Gamma | `Analysis/SpecialFunctions/Gamma/Basic.lean`: `Real.Gamma_eq_integral`, `Real.Gamma_add_one`, `Real.Gamma_nat_eq_factorial`, `Complex.Gamma_eq_integral`. | **Direct use under domain checks.** The real integral formula requires a positive argument; the complex formula requires positive real part. The total function's values at poles are not improper-integral convergence claims. |
| 9–10: forms and pullback | `Analysis/Calculus/DifferentialForm/Basic.lean`: `extDeriv`, `extDeriv_apply`, `extDeriv_extDeriv`, `extDeriv_pullback`. `Topology/Algebra/Module/Alternating/Basic.lean`: `ContinuousAlternatingMap.compContinuousLinearMap` supplies pointwise pullback. | **Direct local calculus; integration bridge required.** An unbundled form is `E → E [⋀^Fin n]→L[ℝ] F`. The file proves `d² = 0` with smoothness assumptions and compatibility of `d` with pullback. It explicitly lists bundled smooth forms and manifold forms as future work. |
| 10: exterior product and orientation | `LinearAlgebra/Alternating/DomCoprod.lean`: `AlternatingMap.domCoprod`. `LinearAlgebra/Orientation.lean`: `Orientation`, `Orientation.map_eq_iff_det_pos`. | **Components, not a complete forms API.** The checked exterior product is algebraic and tensor-valued. Its connection to scalar-valued continuous forms, signs, and the Leibniz rule needs work. Vector-space orientation does not supply oriented smooth chains or their boundary multiplicities. |
| 10: boundary integration | `MeasureTheory/Integral/DivergenceTheorem.lean`: `integral_divergence_of_hasFDerivAt_off_countable`, `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`. | **Direct on coordinate boxes; bridge elsewhere.** These are genuine volume/face identities, not general Stokes for differential forms. `FormsPrototype.lean` connects the rectangle result to the actual exterior derivative. |
| 11: Lp | `MeasureTheory/Function/LpSpace/Basic.lean`: `MemLp.toLp`, `coeFn_toLp`, `toLp_eq_toLp_iff`, `Lp.ext`. `MeasureTheory/Function/LpSpace/Complete.lean`: `Lp.instCompleteSpace`. | **Direct use.** Lp elements are almost-everywhere classes. Completeness requires a complete target and `1 ≤ p`. Pointwise exercise statements require representatives or an explicit almost-everywhere translation. |

## Chapter 6 prototype

`Math/Rudin/Support/StieltjesPrototype.lean` defines finite weakly increasing partitions on `a ≤ b`, closed-subinterval tags, refinement, and sums with the original increments `α(xᵢ₊₁) - α(xᵢ)`. The integrator only needs to be monotone on the interval; its values at discontinuities are retained. This matches the weak inequalities in Rudin Definition 6.1. Repeated nodes are allowed, and their integrator increments are zero. `degenerate` gives a real one-cell partition of `[a,a]`; `lowerSum_self`, `upperSum_self`, and `hasDarbouxRSIntegral_self` prove the zero-interval case using nonempty partition families, not default extrema of empty sets.

It provides two separate predicates:

- `HasRSIntegral`: boundedness, monotonicity, and convergence of all tagged refinements of a suitable partition.
- `HasDarbouxRSIntegral`: boundedness, monotonicity, and equality of the supremum of lower sums and infimum of upper sums with the stated value. The lower/upper sums use infima/suprema on closed subintervals, as in Rudin §6.1–6.2.

No general equivalence of these predicates is claimed. For constants, `taggedSum_const`, `lowerSum_const`, and `upperSum_const` prove that every sum is `c * (α b - α a)`. `constant_value_unique` also rules out a vacuous tagged-sum value. `darboux_constant_bridge` proves that the actual Darboux criterion has value `∫ _ in a..b, c ∂α.measure` when `α` is a `StieltjesFunction`. Thus this restricted bridge is proved, not assumed.

### Endpoint and jump checks

For a right-continuous `α`, Mathlib gives:

- `α.measure (Ioc a b) = ENNReal.ofReal (α b - α a)`.
- `α.measure {a} = ENNReal.ofReal (α a - leftLim α a)`.
- `α.measure (Icc a b) = ENNReal.ofReal (α b - leftLim α a)`.

For `a ≤ b`, `intervalIntegral.integral_of_le` uses `(a,b]`, not `[a,b]`. Therefore replacing it by a closed-set integral can add an atom at `a`.

Right normalization is also unsafe without a bridge. `Monotone.stieltjesFunction` replaces `α x` by `rightLim α x`. The compiled theorem `normalization_changes_endpoint` uses `α(x) = 0` for `x ≤ 0` and `α(x) = 1` for `x > 0`. The Darboux integral of `1` on `[-1,0]` is `0`. The interval integral against the right-normalized Stieltjes measure is `1`.

### Partition and refinement foundation

`Support/StieltjesRefinement.lean` uses the unchanged prototype definitions.
It constructs a partition whose node set is exactly the union of two node
sets. Sorted finite vertices and a repeated final node preserve `n>0`, including
for a singleton interval. It proves reflexivity and transitivity of refinement,
`lowerSum <= taggedSum <= upperSum`, global bounds, lower/upper monotonicity
under refinement, cross-partition bounds, and boundedness of both Darboux sum
ranges. Zero-weight cells and repeated nodes are included.

`hasRSIntegral_of_hasDarbouxRSIntegral` proves the forward implication with
interval-only monotonicity and boundedness. Tagged values are unique, and
singleton tagged integrals are zero.

`Support/StieltjesEquivalence.lean` proves the converse and the exact iff for
`a ≤ b`. It approximates cell infima and suprema by finitely many tags; it
does not assume extrema are attained. The error scale uses `Δα+1`, not a
possibly zero total increment. Repeated nodes, zero mass and singleton
intervals are included. This equivalence needs no right continuity of `α`.

### Continuous integrands and measures

`Support/StieltjesMeasureBridge.lean` proves:

- For any raw `α` monotone on `[a,b]`, a real continuous integrand has an
  actual Darboux integral. This is existence, not a measure comparison.
- For `α : StieltjesFunction ℝ`, `a ≤ b`, and `ContinuousOn f (Icc a b)`,
  `continuous_bridge` identifies that Darboux integral with
  `∫ x in a..b, f x ∂α.measure`. `continuous_tagged_bridge` gives the
  matching tagged criterion.
- The proof establishes finite cell-integral additivity and lower/upper sum
  bounds, then uses uniform continuity and an explicit uniform grid to make
  the Darboux gap arbitrarily small. No desired equality is assumed.
- Singleton intervals, repeated cells and zero mass are proved separately.
  Endpoint regressions include a terminal jump and exclude an initial atom,
  consistently with `(a,b]`. No regularity of `f` outside `[a,b]` is required.

The measure bridge explicitly uses the integrator's right continuity. It
does not normalize an arbitrary raw integrator without correction. The
existing endpoint counterexample still refutes that shortcut.

### Algebra and interval splitting

`Support/StieltjesIntegralLaws.lean` proves real-integrand algebra for both
literal predicates: addition, arbitrary real scaling, negation, subtraction,
interval-wise congruence, order and bounds. Integrator addition and nonnegative
scaling preserve raw integrator values. Absolute-value integrability is proved
by a cell-gap contraction and a genuine small-gap existence criterion; the
absolute integral bound does not assume the missing integral exists.

Partition concatenation proves joining. Filtered vertices and inserted cut
points give genuine weak partitions for restriction. Cut/rejoin refinement
bounds each restricted gap by the original gap, so full splitting constructs
both restricted integrals and proves value additivity. Endpoint cuts, singleton
intervals, repeated nodes and jumps at the cut are included. Bounded integrands
with zero raw mass need no continuity assumption.

Independent review passed at SHA256
`7e0de819804fcb97aed6ce7f520657775322e6822803dd2868ce380d7cee2d24`.
The reviewer compiled 30 independent model checks, including a discontinuous
endpoint-integrand counterexample that forbids an unconditional measure bridge.
These are real foundations for Theorem 6.12(a–e) and 6.13(b), not completion of
any remaining exercise. The composition and complex results below extend
this foundation. Vector integrands, integration by parts and improper arguments
remain open.

### Continuous composition, products and complex values

`Support/StieltjesComposition.lean` proves an affine cell-oscillation gap
estimate. Compact-range uniform continuity then proves actual integrability
of `phi ∘ f` without continuity of `f`. Squares, products by polarization,
natural powers including zero, and tagged versions follow from proved laws.
This supplies Rudin 6.11 and 6.13(a), not a measure substitution.
Independent review passed 35 model checks, including square root on a range
where it is not Lipschitz. Final SHA256:
`92e56ea46a1f7927d5778178096f6531ed888c9511097d33475c6c20089732e1`.

`Support/StieltjesComplex.lean` defines actual complex tagged sums and norm
convergence over the same weak partitions. The real/imaginary component iff
is proved. It gives uniqueness, complex algebra, conjugation, product and norm
integrability, the integral norm inequality, integrator laws and full interval
splitting. The norm construction uses real squares and square-root composition;
it does not assume that the norm is integrable. Independent review passed
33 boundary checks. Final SHA256:
`f42959dd681c290793461d59de971570431c26e3c74dda32ee4a3ebdc65d6dfe`.

Both modules retain raw integrator values, repeated nodes, singleton intervals
and zero mass. Neither supplies a general discontinuous-integrand measure
bridge, improper integration, or a general vector-valued predicate.

Remaining Chapter 6 work, as required by the exercises:

1. Extend measure comparisons only where needed to compact-interval raw
   integrators, with proved normalization and endpoint corrections.
2. State and prove jump-compatibility conditions for more general or
   discontinuous integrands before using measure identification.
3. Add the needed vector-valued integrands, integration by parts, improper
   limits and remaining exercise-specific integral laws. `Chapter06/Exercise01.lean` already proves the point-supported
   result directly from Darboux sums, including endpoints and `a=b`.

Completion status is recorded only in the registry and progress report.

## Chapter 10 prototype

`Math/Rudin/Support/FormsPrototype.lean` uses Mathlib's continuous alternating maps and actual `extDeriv`, not an unrelated symbolic derivative.

- `exterior_square` computes the derivative of the 0-form `x ↦ x²` on the unit tangent as `2x`.
- `segment_stokes` proves the integral of that exterior derivative equals evaluation on the oriented boundary `[b] - [a]`, under ordinary differentiability and integrability assumptions. `square_segment` discharges these assumptions for the polynomial. `segmentIntegral_reverse` checks the orientation sign.
- `exterior_plane` identifies a plane 1-form's exterior derivative on the ordered coordinate frame with `∂Q/∂x - ∂P/∂y`.
- `rectangle_stokes` proves that the area integral of this actual exterior derivative equals four oriented edge integrals. It specializes the existing divergence theorem to the rotated coefficient field. Its hypotheses are global differentiability, ordered rectangle endpoints, and integrability of the exterior-derivative coefficient. They do not assume the boundary identity.

The rectangle theorem uses Bochner area integration. It does not identify this integral with Rudin's iterated or parameterized surface integral. The example uses the product norm only for calculus; it makes no Euclidean length or area-norm assertion.

Targeted source-text review of PDF pages 300–308 identifies the following needs. This review is not a full page-image or exercise-semantic acceptance check:

- R10E15 needs exterior-product signs.
- R10E16–19 need affine simplex chains, `∂² = 0`, and signed square/cube face cancellation.
- R10E20 needs integration by parts for forms.
- R10E21–28 need pullback integration, punctured-domain exactness, homotopy arguments, and explicit curve/surface computations.
- R10E31 needs Green identities beyond coordinate boxes.
- R10E32 needs the parameter-chain boundary with multiplicity, not just the geometric edge of a Möbius band.

The source search found algebraic/topological simplex and singular-homology infrastructure, but no complete interface connecting smooth parameterized chains, continuous differential forms, oriented boundary, and integration. Do not interpret the separate orientation or homology APIs as that interface.

### Ordered-chain foundation

`Support/OrderedChains.lean` represents formal signed sums of ordered vertex
lists by `FreeAbelianGroup (List E)`. It proves the boundary is the alternating
sum of vertex deletions, its square is zero on every formal chain, the edge and
triangle formulas, and preservation of integer multiplicity. Vertex maps
commute with that combinatorial boundary.

This is an augmented, ungraded presentation: `boundary [] = 0` while
`boundary [a]` is the nonzero empty-list generator. It does not impose the
orientation-permutation relation. Reversed raw edges therefore do not cancel
as they do after Rudin's orientation/integration comparison. Mapping vertices
is not nonlinear postcomposition of affine surfaces. Fixed-degree chains,
affine and smooth parameterization, orientation relations, and integration
comparisons are not part of this raw model. The separate oriented model below
adds some of these structures. Neither model alone completes a Chapter 10
exercise or supplies a general Stokes theorem.

The compiler-generated unsafe recursion helper reported during review was
removed by expressing the recursion through `List.rec`. The unchanged project
audit then passed; no unsafe-declaration exception was added.

### Oriented chains and parameterized squares

`Support/OrientedChains.lean` quotients raw vertex chains by adjacent swaps
and repeated-vertex relations. It proves that the boundary preserves these
relations before defining the quotient boundary. Homogeneous subgroups give
fixed vertex counts and dimensions, with typed boundaries and `∂² = 0`.
The ordinary boundary of a zero-dimensional chain is zero; the augmented
boundary is kept separate. Square and six-tetrahedron cube identities retain
signs and integer multiplicity.

Barycentric realization and zero-coordinate face inclusions give an actual
affine comparison. Cartesian parameters recover Rudin's formula (76).
Nonlinear postcomposition acts on the full parameterized maps, not merely
their vertices.

The separate `Parametric` API uses actual paths and maps from the parameter
plane. Path reversal and constant paths define a quotient; square boundaries
are sums of four restricted paths. Boundary-square-zero and postcomposition
naturality are proved. The actual Möbius parameterization has a proved seam
identity and the boundary `Γ₁ + Γ₃ + 2Γ₂`. This is not a claim about its
geometric edge or its integrals.

`Support/OrientedChainChecks.lean` retains independently developed model
checks. Exterior-algebra evaluation proves infinite order for simplex
generators in every vertex degree, so the quotient equations are not vacuous.
It also checks the six coordinate-insertion cube-face signs, a nonadjacent
repeated vertex, a nonzero segment, and `2Γ₂ ≠ Γ₂` for a nonzero band width.

Independent source/type review and the project proof-body audit passed.
The reviewed `OrientedChains.lean` SHA256 is
`6ea0aab7581897268da9356dd4bea40d705e19a30ac661a7fdd2fd2f52910a1a`.
The model still has these limits:

- Homogeneous subgroups are not proved to form an internal direct sum.
- Arbitrary permutation signs are not packaged as a general theorem.
- Paths are full real-domain maps, identified by reversal and constants, not
  by equality restricted to `[0,1]` or by integration functionals.
- No regularity is bundled. General smooth parameterized simplex chains and
  the comparison of square parameterizations with affine triangulations are
  not implemented.
- Determinants, geometric coverage, positive orientation, the remaining
  Möbius geometry, and all form-integration comparisons remain open.

### Path integration and a source-integral comparison

`Support/PathIntegration.lean` uses the actual coefficient
`ω(p(t))(deriv p t)`. Reversal and constant-path identities prove descent to the
existing signed path quotient. The alternating-map representation is connected
to continuous linear 1-forms; the exterior derivative of an actual scalar
0-form is compared with `fderiv`.

The differentiable-potential theorem identifies the integral with evaluation
on the actual endpoint boundary. With a continuous coefficient, the identity
integrator bridge proves the literal Darboux integral. A quadratic affine-path
example proves both the chain value and the Darboux result `b²-a²`, including
reversal and constant paths, without remaining regularity hypotheses.

The total integral and derivative defaults are explicit: nonintegrable
coefficients and missing derivatives can produce zero. The scalar-coefficient
bridge alone does not certify a differentiable source path. The actual
exterior-boundary comparison includes the required derivative hypotheses.

Independent review passed at SHA256
`62191f3c70fbea6d116aadf3603cb914e6ee2cd48bd664daa3b2603c4ab17c24`,
with a fresh local import closure and 22 independent checks. This is a
path-only bridge, not general simplex integration, arbitrary
reparameterization or higher-dimensional Stokes.

Remaining Chapter 10 work, in dependency order:

1. Fix continuous scalar-valued exterior product, normalization, and Leibniz lemmas.
2. Extend the fixed-degree model to the required smooth parameterized simplexes. Prove general permutation signs, square-triangulation comparison, and exercise-specific orientation and coverage results.
3. Define form integration by pullback on segments, rectangles, and simplexes. Prove change-of-variables and comparison with Rudin's integral conventions.
4. Extend the proved coordinate-rectangle identity to pullbacks and chains, then to the required exactness and homotopy results.
5. Treat general domains, outward normals, Green identities, and nonorientable examples separately. No general manifold Stokes theorem is claimed.

## Verification and open P3 criteria

The following commands succeeded with exit code `0`:

```sh
lake env lean Math/Rudin/Support/ApiExamples.lean
lake env lean Math/Rudin/Support/StieltjesPrototype.lean
lake env lean Math/Rudin/Support/FormsPrototype.lean
lake env lean Math/Rudin/Support/OrderedChains.lean
lake env lean Math/Rudin/Support/OrientedChains.lean
lake env lean Math/Rudin/Support/OrientedChainChecks.lean
lake env lean Math/Rudin/Support/PathIntegration.lean
lake env lean Math/Rudin/Support/StieltjesIntegralLaws.lean
lake env lean Math/Rudin/Support/StieltjesComposition.lean
lake env lean Math/Rudin/Support/StieltjesComplex.lean
lake env lean Math/Rudin/Support/StieltjesRefinement.lean
lake env lean Math/Rudin/Support/StieltjesEquivalence.lean
lake env lean Math/Rudin/Support/StieltjesMeasureBridge.lean
```

The prototype `#print axioms` commands for the main bridge, endpoint, computation, and boundary theorems report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholder or custom axiom was added. The project audit now also checks every imported Support declaration, including private proof bodies. Current integrated results are recorded in the plan; theorem-level prototype output alone does not replace that audit.

P3 remains open:

- The requested high-risk topics have source and compilation evidence; the complete exercise-by-exercise coverage classification remains open.
- Chapter 6 has literal weak-partition Darboux sums, full Darboux/tagged equivalence, raw monotone continuous-integrand existence, and a continuous-integrand measure bridge for right-continuous Stieltjes functions. Real algebra, absolute values, full interval splitting, continuous composition, products and actual complex tagged integrals are also proved. General raw normalization corrections, discontinuous-integrand measure bridges and vector integrands remain open; no unconditional normalization is claimed.
- Chapter 10 has nontrivial exterior-derivative computations, genuine segment/rectangle boundary identities, an orientation quotient with fixed degrees and affine faces, and actual parameterized-square/Möbius boundary multiplicities. The path-only integration/source-Darboux bridge is proved. General smooth chains, higher-dimensional integration comparisons, and the remaining geometric exercise requirements remain open.
- This investigation alone does not certify the six representative exercises. Subsequent source/type reviews, root integration, registry evidence and project-wide checks are tracked in the current plan and progress report. Full-book completion remains open.
