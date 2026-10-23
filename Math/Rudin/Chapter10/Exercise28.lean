module

public import Math.Rudin.Support.MultivariateRiemann
public import Math.Rudin.Support.FormsPrototype
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exercise 10.28. Primary PDF 306, book 297. The ordered parameters are
`(r, θ)`, on the closed rectangle `[a,b] × [0,2π]`. -/
@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise28
open Set MeasureTheory
open scoped Real
open Rudin.Support Rudin.Support.SimplexIntegration
open ContinuousAlternatingMap

/-- The actual polar parameter map, including both copies of the seam. -/
def polar (p : ℝ × ℝ) : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)

def omega : Form 1 (ℝ × ℝ) := TriangleStokes.coordinateForm (fun _ => 0) (fun p => p.1 ^ 3)

theorem polar_smooth : ContDiff ℝ 2 polar := by unfold polar; fun_prop

theorem omega_smooth : ContDiff ℝ 1 omega := by
  unfold omega TriangleStokes.coordinateForm
  fun_prop

theorem polar_derivative (p : ℝ × ℝ) :
    HasFDerivAt polar (fderivPolarCoordSymm p) p := hasFDerivAt_polarCoord_symm p

/-- The Cartesian exterior derivative is `3x² dx ∧ dy`. -/
theorem exterior (p : ℝ × ℝ) (v : Fin 2 → ℝ × ℝ) :
    extDeriv omega p v = 3 * p.1 ^ 2 * ((v 0).1 * (v 1).2 - (v 1).1 * (v 0).2) := by
  rw [extDeriv_apply (omega_smooth.differentiable (by norm_num) p)]
  have hd (w : Fin 1 → ℝ × ℝ) :
      fderiv ℝ (fun q => omega q w) p =
        (3 * p.1 ^ 2 * (w 0).2) • ContinuousLinearMap.fst ℝ ℝ ℝ := by
    have h := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 3).mul_const (w 0).2
    convert h.fderiv using 1 <;> simp [omega, TriangleStokes.coordinateForm_apply]; module
  simp [hd, Fin.removeNth]
  ring

/-- Pull back the real form, rather than assigning a boundary value. -/
theorem pullback_value (p : ℝ × ℝ) (v : Fin 1 → ℝ × ℝ) :
    pullback omega polar p v =
      p.1 ^ 3 * Real.cos p.2 ^ 3 * Real.sin p.2 * (v 0).1 +
      p.1 ^ 4 * Real.cos p.2 ^ 4 * (v 0).2 := by
  simp [pullback_apply, omega, TriangleStokes.coordinateForm_apply,
    (polar_derivative p).fderiv, fderivPolarCoordSymm, polar]
  ring

def surfaceCoefficient (p : ℝ × ℝ) : ℝ :=
  pullback (extDeriv omega) polar p FormsPrototype.planeFrame

theorem surface_coefficient (p : ℝ × ℝ) :
    surfaceCoefficient p = 3 * p.1 ^ 3 * Real.cos p.2 ^ 2 := by
  simp only [surfaceCoefficient, pullback_apply, exterior]
  simp [FormsPrototype.planeFrame, (polar_derivative p).fderiv,
    fderivPolarCoordSymm, polar]
  calc
    _ = 3 * p.1 ^ 3 * Real.cos p.2 ^ 2 *
        (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/-- The oriented surface integral uses the actual pullback coefficient. -/
def surfaceIntegral (a b : ℝ) : ℝ :=
  ∫ r in a..b, ∫ θ in (0 : ℝ)..(2*π), surfaceCoefficient (r, θ)

/-- Four actual parameter-edge integrals, with induced signs `+,+,-,-`. -/
def bottomIntegral (a b : ℝ) : ℝ :=
  ∫ r in a..b, pullback omega polar (r, 0) (fun _ => (1,0))
def outerIntegral (b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2*π), pullback omega polar (b, θ) (fun _ => (0,1))
def topIntegral (a b : ℝ) : ℝ :=
  -(∫ r in a..b, pullback omega polar (r, 2*π) (fun _ => (1,0)))
def innerIntegral (a : ℝ) : ℝ :=
  -(∫ θ in (0 : ℝ)..(2*π), pullback omega polar (a, θ) (fun _ => (0,1)))
def boundaryIntegral (a b : ℝ) : ℝ :=
  bottomIntegral a b + outerIntegral b + topIntegral a b + innerIntegral a

theorem angular_two : (∫ θ in (0 : ℝ)..(2*π), Real.cos θ ^ 2) = π := by
  simp [integral_cos_sq]

theorem angular_four : (∫ θ in (0 : ℝ)..(2*π), Real.cos θ ^ 4) = 3*π/4 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, integral_cos_pow, angular_two]
  simp
  ring

theorem surface_value (a b : ℝ) : surfaceIntegral a b = 3*π/4 * (b^4-a^4) := by
  simp only [surfaceIntegral, surface_coefficient, intervalIntegral.integral_const_mul,
    angular_two]
  simp_rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem radial_edges (a b : ℝ) : bottomIntegral a b = 0 ∧ topIntegral a b = 0 := by
  simp only [bottomIntegral, topIntegral, pullback_value]
  simp

theorem circular_edges (a b : ℝ) :
    outerIntegral b = 3*π/4*b^4 ∧ innerIntegral a = -(3*π/4*a^4) := by
  simp only [outerIntegral, innerIntegral, pullback_value, mul_zero, mul_one, zero_add,
    intervalIntegral.integral_const_mul, angular_four]
  constructor <;> ring

theorem boundary_value (a b : ℝ) : boundaryIntegral a b = 3*π/4 * (b^4-a^4) := by
  obtain ⟨hb,ht⟩ := radial_edges a b
  obtain ⟨ho,hi⟩ := circular_edges a b
  rw [boundaryIntegral, hb, ht, ho, hi]
  ring

/-- The two seam paths coincide; their induced signs are opposite. -/
theorem seam_paths (r : ℝ) : polar (r, 0) = polar (r, 2*π) := by
  simp [polar]

theorem annular_radius {a b : ℝ} (ha : 0 < a) {p : ℝ × ℝ}
    (hp : p ∈ Icc (a, 0) (b, 2*π)) :
    a^2 ≤ (polar p).1^2 + (polar p).2^2 ∧
    (polar p).1^2 + (polar p).2^2 ≤ b^2 := by
  have he : (polar p).1^2 + (polar p).2^2 = p.1^2 := by
    dsimp [polar]
    nlinarith [Real.cos_sq_add_sin_sq p.2]
  rw [he]
  exact ⟨pow_le_pow_left₀ ha.le hp.1.1 2,
    pow_le_pow_left₀ (ha.le.trans hp.1.1) hp.2.1 2⟩

theorem coefficient_continuous : Continuous surfaceCoefficient := by
  simp only [funext surface_coefficient]
  fun_prop

/-- Compactness gives actual integrability before any area integral is used. -/
theorem coefficient_integrable (a b : ℝ) :
    IntegrableOn surfaceCoefficient (Icc (a,0) (b,2*π)) :=
  coefficient_continuous.continuousOn.integrableOn_compact isCompact_Icc

/-- Fubini compares the oriented repeated integral with parameter area. -/
theorem surface_area (a b : ℝ) (hab : a ≤ b) :
    surfaceIntegral a b = ∫ p in Icc (a,0) (b,2*π), surfaceCoefficient p := by
  have ht : (0 : ℝ) ≤ 2*π := by positivity
  have hset : Icc (a,0) (b,2*π) = Icc a b ×ˢ Icc 0 (2*π) := by
    ext p; simp only [mem_Icc, Prod.le_def, mem_prod]; tauto
  rw [hset]
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod _ (by
    simpa only [← Measure.volume_eq_prod, hset] using coefficient_integrable a b)]
  simp_rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_of_le ht]
  rfl

/-- Stokes is applied to the actual pullback form on the parameter rectangle.
The independent four-edge definition is compared with that theorem. -/
theorem actual_stokes {a b : ℝ} (hab : a ≤ b) :
    surfaceIntegral a b = boundaryIntegral a b := by
  have he (p : ℝ × ℝ) : extDeriv (pullback omega polar) p =
      pullback (extDeriv omega) polar p :=
    (exterior_pullback omega polar p
      (omega_smooth.differentiable (by norm_num) _) polar_smooth.contDiffAt)
  have hi : IntegrableOn
      (fun p => extDeriv (pullback omega polar) p FormsPrototype.planeFrame)
      (Icc (a,0) (b,2*π)) := by
    simp_rw [he]
    exact coefficient_integrable a b
  rw [surface_area a b hab]
  change (∫ p in Icc (a,0) (b,2*π),
    pullback (extDeriv omega) polar p FormsPrototype.planeFrame) = _
  simp_rw [← he]
  rw [FormsPrototype.rectangle_stokes _ _ _ ⟨hab, by positivity⟩
    ((TriangleStokes.pullback_contDiff omega polar omega_smooth polar_smooth).differentiable
      (by norm_num)) hi]
  simp only [FormsPrototype.rectangleBoundary, FormsPrototype.planeP, FormsPrototype.planeQ,
    boundaryIntegral, bottomIntegral, topIntegral, outerIntegral, innerIntegral]
  ring

/-- The source one-dimensional Riemann predicate is supplied by the frozen
Darboux-to-measure comparison, not by redefining the source integral. -/
theorem continuous_source {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) :
    StieltjesPrototype.HasDarbouxRSIntegral f id a b (∫ t in a..b, f t) := by
  have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hf.continuousOn
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id] using h

/-- Both repeated source integrals exist, including every individual slice. -/
theorem surface_source {a b : ℝ} (hab : a ≤ b) :
    (∀ r ∈ Icc a b, StieltjesPrototype.HasDarbouxRSIntegral
      (fun θ => surfaceCoefficient (r,θ)) id 0 (2*π) (3*r^3*π)) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun r => ∫ θ in (0 : ℝ)..(2*π), surfaceCoefficient (r,θ)) id a b
      (3*π/4*(b^4-a^4)) := by
  constructor
  · intro r _
    have h := continuous_source (coefficient_continuous.comp
      (show Continuous (fun θ : ℝ => (r,θ)) by fun_prop))
      (a := 0) (b := 2*π) (by positivity)
    simpa only [Function.comp_def, surface_coefficient, intervalIntegral.integral_const_mul, angular_two] using h
  · rw [← surface_value]
    apply continuous_source _ hab
    simp only [surface_coefficient, intervalIntegral.integral_const_mul, angular_two]
    fun_prop

/-- The four signed boundary integrands have source Riemann witnesses too. -/
theorem boundary_source {a b : ℝ} (hab : a ≤ b) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun r => pullback omega polar (r,0) (fun _ => (1,0))) id a b 0 ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun θ => pullback omega polar (b,θ) (fun _ => (0,1))) id 0 (2*π) (3*π/4*b^4) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun r => -pullback omega polar (r,2*π) (fun _ => (1,0))) id a b 0 ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun θ => -pullback omega polar (a,θ) (fun _ => (0,1))) id 0 (2*π) (-(3*π/4*a^4)) := by
  have hp (r : ℝ) : Continuous (fun θ => pullback omega polar (r,θ) (fun _ => (0,1))) := by
    simp only [pullback_value]
    fun_prop
  have hr (θ : ℝ) : Continuous (fun r => pullback omega polar (r,θ) (fun _ => (1,0))) := by
    simp only [pullback_value]
    fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := continuous_source (hr 0) hab
    change StieltjesPrototype.HasDarbouxRSIntegral _ _ _ _ (bottomIntegral a b) at h
    rwa [(radial_edges a b).1] at h
  · rw [← (circular_edges a b).1]
    exact continuous_source (hp b) (a := 0) (b := 2*π) (by positivity)
  · have h := continuous_source (hr (2*π)).neg hab
    simp only [Pi.neg_apply, intervalIntegral.integral_neg] at h
    change StieltjesPrototype.HasDarbouxRSIntegral _ _ _ _ (topIntegral a b) at h
    rwa [(radial_edges a b).2] at h
  · rw [← (circular_edges a b).2, innerIntegral, ← intervalIntegral.integral_neg]
    exact continuous_source (hp a).neg (a := 0) (b := 2*π) (by positivity)

/-- All three inventory claims for the source's nondegenerate annulus. -/
theorem exercise28 {a b : ℝ} (_ha : 0 < a) (hab : a < b) :
    surfaceIntegral a b = 3*π/4*(b^4-a^4) ∧
    boundaryIntegral a b = 3*π/4*(b^4-a^4) ∧
    surfaceIntegral a b = boundaryIntegral a b :=
  ⟨surface_value a b, boundary_value a b, actual_stokes hab.le⟩

end Rudin.Chapter10.Exercise28
