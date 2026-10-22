# Mathlib coverage and P3 risks

## Result and scope

The pinned Mathlib supports most required mathematical objects. It does not provide a single API that identifies Rudin's integrals, oriented chains, and Stokes theory. The two prototypes below prove restricted bridges and boundary identities. Neither completes its P3 work item.

Evidence uses Lean `v4.35.0` and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All Mathlib paths below are relative to `.lake/packages/mathlib/Mathlib/`. `Math/Rudin/Support/ApiExamples.lean` contains compiled `#check` probes and usage proofs for the listed topics. This is a topic survey, not a verified classification of every exercise.

## Coverage map

| Chapters/topic | Available declarations and source | Classification and remaining work |
| --- | --- | --- |
| 1: cuts and real numbers | `Order/Completion.lean`: `DedekindCut.principal`, `principalEmbedding`, `factorEmbedding`. `Basic/Real/Basic.lean`: `Real.equivCauchy`, `Real.mk_eq`. | **Bridge/new construction.** `DedekindCut` is the Dedekind–MacNeille completion. A principal left set is `Iic q`, with a greatest element. It is not Rudin's nonempty proper rational lower cut without a greatest element. Mathlib's real numbers use a Cauchy construction. Explicit cut exercises still require a model and a comparison with `ℝ`. |
| 2–3: metric completion | `Topology/UniformSpace/Completion.lean`: `UniformSpace.Completion`, `denseRange_coe`, `extension_coe`. `Topology/MetricSpace/Completion.lean`: `UniformSpace.Completion.coe_isometry`. | **Direct use, with a construction bridge when required.** The completion is a separation quotient of Cauchy filters. Isometry, density, extension, and completeness are available. An exercise that specifies equivalence classes of Cauchy sequences still needs that construction and its identification with this completion. |
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

Remaining Chapter 6 work, in dependency order:

1. Prove partition refinement and common-refinement results, sum bounds, and the general Darboux/tagged equivalence.
2. Relate the one-dimensional representation to `BoxIntegral` or prove a direct measure bridge for a useful nonconstant class, initially continuous integrands.
3. Handle integrators given only on a compact interval, arbitrary jump values, and endpoint corrections. State and prove the required continuity conditions on the integrand at jumps.
4. Add complex/vector-valued integrands and the remaining exercise-specific integral laws. The degenerate interval is proved. `Math/Rudin/Chapter06/Exercise01.lean` separately proves the point-supported integrand result directly from these Darboux sums, for `a ≤ b` and interval-relative continuity, including both endpoints and the singleton interval. Completion status is recorded only in the registry and progress report.

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

Remaining Chapter 10 work, in dependency order:

1. Fix continuous scalar-valued exterior product, degree indexing, normalization, and Leibniz lemmas.
2. Define the needed affine/parameterized chains and signed face maps; prove `∂² = 0` and cancellation, including multiplicity.
3. Define form integration by pullback on segments, rectangles, and simplexes. Prove change-of-variables and comparison with Rudin's integral conventions.
4. Extend the proved coordinate-rectangle identity to pullbacks and chains, then to the required exactness and homotopy results.
5. Treat general domains, outward normals, Green identities, and nonorientable examples separately. No general manifold Stokes theorem is claimed.

## Verification and open P3 criteria

The following commands succeeded with exit code `0`:

```sh
lake env lean Math/Rudin/Support/ApiExamples.lean
lake env lean Math/Rudin/Support/StieltjesPrototype.lean
lake env lean Math/Rudin/Support/FormsPrototype.lean
```

The prototype `#print axioms` commands for the main bridge, endpoint, computation, and boundary theorems report only `propext`, `Classical.choice`, and `Quot.sound`. No proof placeholder or custom axiom was added. This is theorem-level evidence, not the project's planned automatic audit of every Support declaration.

P3 remains open:

- The requested high-risk topics have source and compilation evidence; the complete exercise-by-exercise coverage classification remains open.
- Chapter 6 has a genuine constant-integrand Darboux/measure bridge, a checked endpoint obstruction, and an actual weak-partition treatment of the degenerate interval. Its general bridge and the other cases listed above remain open.
- Chapter 10 has nontrivial exterior-derivative computations and genuine segment/rectangle boundary identities. Smooth chains, integration comparisons, and the exercise-specific infrastructure remain open.
- This investigation alone does not certify the six representative exercises. Subsequent source/type reviews, root integration, registry evidence and project-wide checks are tracked in the current plan and progress report. Full-book completion remains open.
