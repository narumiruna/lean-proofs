# Mathlib and source representations

## Scope

Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` supply the underlying analysis.
The repository adds the constructions and comparisons required by the exercise
contracts. It does not replace a source integral or prescribed construction
with an unrelated library object.

`Math/Rudin/Support/ApiExamples.lean` contains compiled probes and usage proofs
for the APIs below. Every path is relative to
`.lake/packages/mathlib/Mathlib/`. Exercise acceptance is recorded in
`exercises.json`; compiled API probes alone are not semantic acceptance.

## Library map

| Topic | Pinned source and API | Use and required comparison |
| --- | --- | --- |
| Cuts and real numbers | `Order/Completion.lean`: `DedekindCut.principal`. `Basic/Real/Basic.lean`: `Real.equivCauchy`, `Real.mk_eq`. | Mathlib's order completion is not Rudin's rational lower-cut construction. Exercise 1.20 defines the literal modified cuts, their union supremum, pairwise-sum addition, closed zero and inverse obstruction. |
| Metric completion | `Topology/UniformSpace/Completion.lean` and `Topology/MetricSpace/Completion.lean`: `UniformSpace.Completion`, `coe_isometry`, `denseRange_coe`, `extension_coe`. | Exercise 3.24 constructs the actual Cauchy-sequence quotient and its limit-distance metric, then proves its isometric comparison, completeness and dense embedding. |
| ODEs | `Analysis/ODE/ExistUnique.lean`: `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, `ODE_solution_unique`. | Library results are used only with matching regularity, initial values and endpoint derivatives. Chapter 7 also constructs the required Euler polygons and their limiting solution. |
| Stieltjes measures | `MeasureTheory/Measure/Stieltjes.lean`: `StieltjesFunction`, `measure_Ioc`, `measure_Icc`, `measure_singleton`. | The source Darboux/tagged predicates retain raw integrator values. Measure comparisons state their right-continuity and endpoint hypotheses explicitly. |
| Tagged box integrals | `Analysis/BoxIntegral/Basic.lean`, `Analysis/BoxIntegral/Partition/Filter.lean`, `Analysis/BoxIntegral/Integrability.lean`: `BoxIntegral.HasIntegral`, `IntegrationParams.Riemann`, `ContinuousOn.hasBoxIntegral`. | These are comparison components, not definitions of repeated source Darboux integrals. The repository constructs the latter at every remaining parameter. |
| Fourier analysis | `Analysis/Fourier/AddCircle.lean`: `fourierCoeff_eq_intervalIntegral`, `hasSum_fourier_series_L2`, `tsum_sq_fourierCoeff`. `Analysis/Fourier/FourierTransform.lean`: `Real.fourier_real_eq_integral_exp_smul`. | Periodic Haar normalization, ordinary ordered sums, source Riemann kernels and the required pointwise/uniform limits are checked separately. L2 convergence is not substituted for them. |
| Gamma | `Analysis/SpecialFunctions/Gamma/Basic.lean`: `Real.Gamma_eq_integral`, `Complex.Gamma_eq_integral`, `Real.Gamma_nat_eq_factorial`. | Integral formulas require positive arguments or positive real parts. Values of the total Gamma function at poles are not convergence claims. Exercise 10.11 derives its beta value through finite source substitution and product limits. |
| Differential forms | `Analysis/Calculus/DifferentialForm/Basic.lean`: `extDeriv`, `extDeriv_apply`, `extDeriv_pullback`. | Forms are actual continuous alternating maps; pullbacks use genuine Fréchet derivatives. Local regularity is proved before using total derivative operations. |
| Exterior algebra and orientation | `LinearAlgebra/Alternating/DomCoprod.lean`, `LinearAlgebra/Orientation.lean`: `AlternatingMap.domCoprod`, `Orientation.map_eq_iff_det_pos`. | Exercises 10.14–15 use cotangent exterior algebra for the required sign laws. Exercise 10.20 proves the scalar-product/one-form-wedge rule needed by its form-integration API. These representations are kept distinct. |
| Coordinate divergence | `MeasureTheory/Integral/DivergenceTheorem.lean`: `integral_divergence_of_hasFDerivAt_off_countable`, `integral_divergence_prod_Icc_of_hasFDerivAt_of_le`. | The prototype uses a genuine rectangle identity. General positive simplex-image regions use the separately proved local simplex Stokes and geometric comparisons. |
| Lp | `MeasureTheory/Function/LpSpace/Basic.lean` and `Complete.lean`: `MemLp.toLp`, `Lp.ext`, `Lp.instCompleteSpace`. | Lp elements are almost-everywhere classes. Chapter 11 proves the required representative, quotient-metric, source-integral and complex-conjugation comparisons. |

## Raw Riemann–Stieltjes integrals

The following files are under `Math/Rudin/Support/`.

- `StieltjesPrototype.lean` defines weakly increasing finite partitions,
  closed-subinterval tags and the original increments
  `α(xᵢ₊₁) - α(xᵢ)`. Repeated nodes and singleton intervals are included.
  It defines separate literal tagged and lower/upper Darboux predicates.
- `StieltjesRefinement.lean` constructs common refinements from the exact
  node union. It proves sum bounds, refinement inequalities and the forward
  Darboux/tagged implication.
- `StieltjesEquivalence.lean` proves the converse and exact equivalence.
  Finite approximate extrema suffice; attained extrema and positive total
  integrator mass are not assumed.
- `StieltjesMeasureBridge.lean` proves continuous-integrand existence for
  interval-monotone raw integrators. For a right-continuous
  `StieltjesFunction`, it proves equality with the measure integral on
  `(a,b]`, including singleton intervals and terminal atoms.
- `StieltjesIntegralLaws.lean` proves real algebra, absolute-value existence,
  bounds, interval joining and restriction. `StieltjesComposition.lean`
  proves continuous composition, squares and products.
- `StieltjesComplex.lean` uses actual complex tagged sums. Its component
  equivalence, norm integrability, algebra and interval splitting are proved.
- `StieltjesIntegrationByParts.lean` proves the real and complex source
  integration-by-parts result by finite summation by parts and genuine within
  derivatives. It does not assume continuous integrators.
- `RiemannIntegrability.lean` proves the ordinary Riemann criterion and the
  value comparison with interval integration. Existence is not inferred from
  a default zero Bochner value.
- `UniformIntegralLimits.lean` and Chapter 7's coordinatewise results retain
  actual source integrals. Chapter 6's improper predicates use finite cuts
  and limits, including the required conditional cases.

Endpoint tests remain necessary. A closed measure interval can add the atom
at its initial endpoint. Right normalization can also change the value:
for `α(x)=0` when `x≤0` and `α(x)=1` when `x>0`, the raw integral of `1` on
`[-1,0]` is zero, while the right-normalized measure integral is one. The
compiled counterexample rules out an unconditional normalization shortcut.
The rational indicator separately rules out an unconditional converse from
Lebesgue integrability to proper Riemann integrability.

## Forms, chains and source integration

### Distinct chain models

- `OrderedChains.lean` uses free integer sums of vertex lists and the literal
  alternating deletion boundary. This is augmented; a singleton has the
  nonzero empty-list boundary.
- `OrientedChains.lean` proves boundary stability of adjacent-swap and
  repeated-vertex relations before taking its quotient. Fixed degrees,
  ordinary degree-zero boundary, affine realization, square/cube signs and
  full-map path/square postcomposition are proved.
- `OrientedChainChecks.lean` proves nontriviality, retained integer
  multiplicities and coordinate-face signs. These checks prevent a collapsed
  quotient from making the identities vacuous.
- `SmoothChains.lean` uses locally C2 simplex parameter maps and a signed
  permutation quotient. Its boundary and nonlinear postcomposition act on
  entire maps, not only vertices. Exercise 10.16 also proves cancellation
  directly for chains of full parameter maps.

The augmented, affine-orientation and smooth-permutation quotients are not
identified with each other. No equality of ranges or vertex data is treated
as equality of nonlinear parameter maps. Equality of flux functionals is not
asserted to imply equality in an abstract chain quotient.

### Calculus and integration

`FormsPrototype.lean` proves nontrivial exterior-derivative and genuine
segment/rectangle identities. `PathIntegration.lean` integrates the actual
coefficient `ω(p(t))(deriv p t)`, proves signed-path descent and gives the
continuous-coefficient source Darboux comparison.

`SimplexIntegration.lean` defines actual pullback coefficients on locally C2
Euclidean simplexes. `TriangleStokes.lean` proves the complete plane-form
identity, including nonhorizontal examples and all three source edge integrals.
`MultivariateRiemann.lean` constructs every repeated real Darboux stage on
closed cells and simplexes, retaining singleton boundary fibers. It proves
all-coordinate-order equality, Euclidean volume comparison and volume `1/n!`.

`SimplexStokes.lean` proves the general local simplex theorem by actual
calculus, with the required C2 map and C1 form hypotheses on neighborhoods.
`SmoothChainIntegration.lean` gives integer-chain integration, naturality and
signed-permutation quotient descent. It compares these values with the literal
source integrals. Stokes is a proved result, not an input field of a chain.

Exercise 10.1 extends the repeated source construction to compact convex
closed domains, including lower-dimensional and empty sets. It derives
regularity for every affine section and actual marginal, rather than assuming
almost-everywhere row existence. Real Darboux and complex tagged witnesses
preserve every closed-boundary value and every coordinate order.

### Exercise-specific comparisons

- Exercises 10.8–11 prove finite source changes of variables and their actual
  improper limits. Polar substitution uses independent disk and polar cutoff
  limits; Gaussian and beta derivations retain their prescribed routes.
- Exercises 10.12–19 prove the actual cube/simplex maps, Jacobians, moments,
  exterior signs, geometric coverage and complete signed face formulas.
- Exercise 10.20 proves the required Leibniz rule and form integration by
  parts, including source integral and oriented segment comparisons.
- Exercise 10.22 proves analytic square subdivision and the six-tetrahedron
  radial homotopy argument. Its exactness/pole-limit proof is separate.
- Exercise 10.23 constructs the prescribed primitive and a complete sphere
  chain. Coverage, null chart overlaps, outward orientation, boundary
  cancellation and strictly positive independent Gram area are conclusions.
  The zero-sphere case uses counting area and ordinary boundary.
- Exercises 10.24–29 construct actual potentials, compatible cells, curves,
  parameter-integral derivatives and source witnesses under local hypotheses.
- `EuclideanFlux.lean` and Exercise 10.31 compare actual geometric volume,
  cofactor normals and Gram area with local simplex Stokes on arbitrary finite
  positive simplex-image regions. Jacobians need only be positive in source
  interiors. Singular boundary normals are limits of actual interior
  parallel-face outward normals. Frontier-only cancellation and the literal
  `g=h` energy argument give harmonic uniqueness without connectedness.
- Exercise 10.32 distinguishes the parameter boundary, with its seam
  multiplicity, from the geometric Möbius rim. Rank, point identifications,
  nonorientability and the requested integral obstruction are proved.

## Limits outside the selected exercise contracts

1. No unconditional raw-integrator normalization or general discontinuous
   Stieltjes/measure identification is claimed. Each use needs its actual
   jump and endpoint hypotheses.
2. The coordinatewise Euclidean results are not a general Banach-valued raw
   Stieltjes calculus.
3. The smooth permutation quotient is not a quotient by equality of all
   integration functionals. No general manifold Stokes package or unrestricted
   reparameterization theorem is claimed.
4. The selected improper change-of-variables contracts are sufficient absolute
   convergence statements. They do not claim every conditionally convergent
   substitution or proper source integrability on arbitrary measurable sets.
5. Sphere area is geometric parametric Gram area. No additional Hausdorff
   normalization or closed numerical formula for every positive dimension is
   needed or claimed.

These limits do not replace an exercise requirement. The source contracts,
per-obligation evidence and second review determine acceptance. All delivery
and Support files are included in the default build and actual-private-body
trust audit. Use `./scripts/check.sh --final` for the complete verification
entry point; an individual prototype or file build is not the final gate.
