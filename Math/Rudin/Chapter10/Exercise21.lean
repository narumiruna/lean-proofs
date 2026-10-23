module

public import Math.Rudin.Chapter08.Exercise23
public import Math.Rudin.Support.PathIntegration
public import Math.Rudin.Support.SimplexStokes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Tactic

/-! # Chapter 10, Exercise 21

The angular form is an actual alternating one-form on the Euclidean complex
plane. All curve integrals have real pullback coefficients. The C¹ winding
statement uses within derivatives at both endpoints and the exact Chapter 8
index. The C² homotopy theorem uses an open neighborhood of the parameter
interval. Its Stokes proof uses two actual smooth triangle maps. A separate
proof uses the arctangent chart and FTC, without Stokes.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise21
open Set MeasureTheory Filter Topology
open Rudin.Support

/-- Complex coordinates identify the Euclidean plane with its ordered real coordinates. -/
def puncturedPlane : Set ℂ := {z | z ≠ 0}

/-- The actual angular covector `(x dy-y dx)/(x²+y²)`. -/
def etaLinear (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (z.re ^ 2 + z.im ^ 2)⁻¹ • (z.re • Complex.imCLM - z.im • Complex.reCLM)

def eta (z : ℂ) : ℂ [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1) (etaLinear z)

@[simp] theorem etaLinear_apply (z v : ℂ) :
    etaLinear z v = (z.re * v.im - z.im * v.re) / (z.re ^ 2 + z.im ^ 2) := by
  simp [etaLinear, div_eq_mul_inv, mul_comm]

@[simp] theorem eta_apply (z : ℂ) (v : Fin 1 → ℂ) :
    eta z v = etaLinear z (v 0) := rfl

@[simp] theorem fromAlternating_eta : PathIntegration.fromAlternating eta = etaLinear := rfl

theorem eta_eq_im_div (z v : ℂ) : etaLinear z v = (v / z).im := by
  simp [Complex.div_im, Complex.normSq_apply, etaLinear_apply, pow_two]
  ring

/-- Pullback with an explicit within-derivative jet; endpoints need not have ambient derivatives. -/
def angularIntegral (γ v : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, etaLinear (γ t) (v t)

theorem angularIntegral_eq_im (γ v : ℝ → ℂ) (a b : ℝ)
    (hi : IntervalIntegrable (fun t => v t / γ t) volume a b) :
    angularIntegral γ v a b = (∫ t in a..b, v t / γ t).im := by
  simp only [angularIntegral, eta_eq_im_div]
  exact Complex.imCLM.intervalIntegral_comp_comm hi

/-- The angular integral uses the literal real source Riemann integral. -/
theorem angularIntegral_source {γ v : ℝ → ℂ} {a b : ℝ}
    (h : Rudin.Chapter08.IsC1NonzeroLoop γ v a b) :
    StieltjesPrototype.HasDarbouxRSIntegral (fun t => etaLinear (γ t) (v t)) id a b
      (angularIntegral γ v a b) := by
  have hc : ContinuousOn (fun t => etaLinear (γ t) (v t)) (Icc a b) := by
    simp only [eta_eq_im_div]
    exact Complex.continuous_im.comp_continuousOn h.continuous_logDerivative
  have hb := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id h.ordered hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id, angularIntegral] using hb

/-- Exercise (f), for all closed C¹ curves with one-sided endpoint derivatives.
The index is exactly the Chapter 8 Exercise 23 definition, not a replacement invariant. -/
theorem winding_index {γ v : ℝ → ℂ} {a b : ℝ}
    (h : Rudin.Chapter08.IsC1NonzeroLoop γ v a b) :
    ((angularIntegral γ v a b / (2 * Real.pi) : ℝ) : ℂ) =
      Rudin.Chapter08.curveIndex γ v a b := by
  obtain ⟨n, hn⟩ := Rudin.Chapter08.exercise23_integer_index h
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have he : (∫ t in a..b, v t / γ t) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    exact (div_eq_iff hp).mp hn
  rw [angularIntegral_eq_im γ v a b h.integrable_logDerivative, he, hn]
  simp [Complex.mul_im, Real.pi_ne_zero]

/-- The source coefficient and the full-map path integral agree whenever the
jet is the genuine ambient derivative. -/
theorem pathIntegral_bridge (γ v : ℝ → ℂ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (v t) t) :
    PathIntegration.pathIntegral etaLinear γ = angularIntegral γ v 0 1 := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact congrArg (etaLinear (γ t)) (hd t ht).deriv

/-- The literal circular parameterization in real coordinates. -/
def circle (r t : ℝ) : ℂ := ⟨r * Real.cos t, r * Real.sin t⟩
def circleVelocity (r t : ℝ) : ℂ := ⟨-(r * Real.sin t), r * Real.cos t⟩

theorem circle_derivative (r t : ℝ) : HasDerivAt (circle r) (circleVelocity r t) t := by
  have h := (((Real.hasDerivAt_cos t).const_mul r).ofReal_comp.add
    (((Real.hasDerivAt_sin t).const_mul r).ofReal_comp.mul_const Complex.I))
  convert h using 1
  · funext s
    apply Complex.ext <;> simp only [circle, Pi.add_apply, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
  · apply Complex.ext <;> simp only [circleVelocity, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add, mul_neg]

theorem circle_coefficient {r : ℝ} (hr : 0 < r) (t : ℝ) :
    etaLinear (circle r t) (circleVelocity r t) = 1 := by
  rw [etaLinear_apply]
  dsimp [circle, circleVelocity]
  have h := Real.sin_sq_add_cos_sq t
  have hd : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by nlinarith [sq_nonneg r]
  rw [hd]
  apply (div_eq_one_iff_eq (pow_ne_zero 2 hr.ne')).mpr
  nlinarith [sq_nonneg r]

theorem circle_integral {r : ℝ} (hr : 0 < r) :
    angularIntegral (circle r) (circleVelocity r) 0 (2 * Real.pi) = 2 * Real.pi := by
  simp [angularIntegral, circle_coefficient hr]

/-- The first local angle chart. -/
def xAngle (z : ℂ) : ℝ := Real.arctan (z.im / z.re)
/-- The second local angle chart. -/
def yAngle (z : ℂ) : ℝ := -Real.arctan (z.re / z.im)

theorem xAngle_derivative {z : ℂ} (hz : z.re ≠ 0) :
    HasFDerivAt xAngle (etaLinear z) z := by
  have hd := (Complex.imCLM.hasFDerivAt (x := z)).mul
    ((hasDerivAt_inv hz).comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  convert hd.arctan using 1
  · funext w
    simp [xAngle, div_eq_mul_inv]
  · ext v
    simp [etaLinear_apply]
    field_simp
    ring

theorem yAngle_derivative {z : ℂ} (hz : z.im ≠ 0) :
    HasFDerivAt yAngle (etaLinear z) z := by
  have hd := (Complex.reCLM.hasFDerivAt (x := z)).mul
    ((hasDerivAt_inv hz).comp_hasFDerivAt z Complex.imCLM.hasFDerivAt)
  convert hd.arctan.neg using 1
  · funext w
    simp [yAngle, div_eq_mul_inv]
  · ext v
    simp [etaLinear_apply]
    field_simp
    ring

theorem xAngle_exterior {z : ℂ} (hz : z.re ≠ 0) :
    extDeriv (PathIntegration.zeroForm xAngle) z = eta z := by
  change extDeriv (fun w => ContinuousAlternatingMap.constOfIsEmpty ℝ ℂ (Fin 0) (xAngle w)) z = _
  rw [extDeriv_constOfIsEmpty, (xAngle_derivative hz).fderiv]
  rfl

theorem yAngle_exterior {z : ℂ} (hz : z.im ≠ 0) :
    extDeriv (PathIntegration.zeroForm yAngle) z = eta z := by
  change extDeriv (fun w => ContinuousAlternatingMap.constOfIsEmpty ℝ ℂ (Fin 0) (yAngle w)) z = _
  rw [extDeriv_constOfIsEmpty, (yAngle_derivative hz).fderiv]
  rfl

theorem xAngle_smooth {z : ℂ} (hz : z.re ≠ 0) : ContDiffAt ℝ 2 xAngle z := by
  exact (Complex.imCLM.contDiff.contDiffAt.div Complex.reCLM.contDiff.contDiffAt hz).arctan

theorem yAngle_smooth {z : ℂ} (hz : z.im ≠ 0) : ContDiffAt ℝ 2 yAngle z := by
  exact (Complex.reCLM.contDiff.contDiffAt.div Complex.imCLM.contDiff.contDiffAt hz).arctan.neg

/-- Closedness of the actual exterior derivative, using the local C² potentials. -/
theorem eta_closed {z : ℂ} (hz : z ≠ 0) : extDeriv eta z = 0 := by
  have hchart (f : ℂ → ℝ) (hf : ContDiffAt ℝ 2 f z)
      (he : eta =ᶠ[𝓝 z] extDeriv (PathIntegration.zeroForm f)) :
      extDeriv eta z = 0 := by
    rw [he.extDeriv_eq]
    apply extDeriv_extDeriv_apply (r := 2) _ (by simp)
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ ℂ ℝ (Fin 0)).contDiff.contDiffAt.comp z hf
  by_cases hx : z.re = 0
  · have hy : z.im ≠ 0 := by
      intro hy
      exact hz (Complex.ext hx hy)
    apply hchart yAngle (yAngle_smooth hy)
    filter_upwards [(isOpen_ne.preimage Complex.continuous_im).mem_nhds hy] with w hw
    exact (yAngle_exterior hw).symm
  · apply hchart xAngle (xAngle_smooth hx)
    filter_upwards [(isOpen_ne.preimage Complex.continuous_re).mem_nhds hx] with w hw
    exact (xAngle_exterior hw).symm

theorem circle_nonzero {r : ℝ} (hr : 0 < r) (t : ℝ) : circle r t ≠ 0 := by
  intro h
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  simp only [circle, Complex.zero_re, Complex.zero_im, mul_eq_zero, hr.ne', false_or] at hx hy
  have hh := Real.sin_sq_add_cos_sq t
  simp [hx, hy] at hh

/-- No single differentiable potential on the punctured plane has this differential. -/
theorem not_globally_exact :
    ¬ ∃ f : ℂ → ℝ, ∀ z ≠ 0, HasFDerivAt f (etaLinear z) z := by
  rintro ⟨f, hf⟩
  have hd (t : ℝ) : HasDerivAt (fun s => f (circle 1 s)) 1 t := by
    simpa only [Function.comp_def, circle_coefficient (r := 1) (by norm_num)] using
      (hf _ (circle_nonzero (r := 1) (by norm_num) t)).comp_hasDerivAt t
        (circle_derivative 1 t)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2 * Real.pi) (fun t _ => hd t) (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 (2 * Real.pi))
  have hc : circle 1 (2 * Real.pi) = circle 1 0 := by
    apply Complex.ext <;> simp [circle]
  rw [hc, sub_self] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hi
  exact (mul_ne_zero (by norm_num) Real.pi_ne_zero) hi

/-- Both local charts coexist with the failure of a global angle potential. -/
theorem local_angles_not_global :
    (∀ z : ℂ, z.re ≠ 0 → extDeriv (PathIntegration.zeroForm xAngle) z = eta z) ∧
    (∀ z : ℂ, z.im ≠ 0 → extDeriv (PathIntegration.zeroForm yAngle) z = eta z) ∧
    ¬ (∃ f : ℂ → ℝ, ∀ z ≠ 0, HasFDerivAt f (etaLinear z) z) :=
  ⟨fun _ => xAngle_exterior, fun _ => yAngle_exterior, not_globally_exact⟩

theorem circle_smooth (r : ℝ) : ContDiff ℝ 2 (circle r) := by
  exact Complex.equivRealProdCLM.symm.contDiff.comp
    ((contDiff_const.mul Real.contDiff_cos).prodMk (contDiff_const.mul Real.contDiff_sin))

theorem eta_smooth : ContDiffOn ℝ 1 eta puncturedPlane := by
  intro z hz
  have hn : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    intro he
    have hx : z.re = 0 := by nlinarith [sq_nonneg z.im]
    have hy : z.im = 0 := by nlinarith [sq_nonneg z.re]
    exact hz (Complex.ext hx hy)
  have hl : ContDiffAt ℝ 1 etaLinear z := by
    exact ((Complex.reCLM.contDiff.contDiffAt.pow 2).add
      (Complex.imCLM.contDiff.contDiffAt.pow 2)).inv hn |>.smul
        ((Complex.reCLM.contDiff.contDiffAt.smul contDiffAt_const).sub
          (Complex.imCLM.contDiff.contDiffAt.smul contDiffAt_const))
  exact ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℂ)
    (F := ℝ) (0 : Fin 1)).contDiff.contDiffAt.comp z hl).contDiffWithinAt

/-- Positive linear rescaling preserves the actual one-form integral. -/
theorem integral_rescale {γ v : ℝ → ℂ} {c : ℝ} (hc : 0 < c)
    (hd : ∀ t ∈ Icc 0 c, HasDerivAt γ (v t) t) :
    PathIntegration.pathIntegral etaLinear (fun t => γ (c*t)) = angularIntegral γ v 0 c := by
  have he : PathIntegration.pathIntegral etaLinear (fun t => γ (c*t)) =
      ∫ t in (0 : ℝ)..1, c * etaLinear (γ (c*t)) (v (c*t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hct : c*t ∈ Icc 0 c := ⟨mul_nonneg hc.le ht.1, by nlinarith [ht.2]⟩
    have hh := (hd _ hct).scomp t ((hasDerivAt_id t).const_mul c)
    simp only [Function.comp_def, mul_one] at hh
    change etaLinear (γ (c*t)) (deriv (fun t => γ (c*t)) t) = _
    rw [hh.deriv, map_smul]
    rfl
  rw [he, intervalIntegral.integral_const_mul]
  simpa [angularIntegral, smul_eq_mul] using
    intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t => etaLinear (γ t) (v t)) c

section Stokes
open SimplexIntegration SmoothChains OrientedChains.Parametric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed form has zero integral on the full-map boundary of any C² triangle.
This is a consequence of analytic simplex Stokes, not an input identity. -/
theorem closed_triangle_boundary (ω : Form 1 E) (S : SmoothChains.Simplex 2 E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (him : S.val '' standardSimplex 2 ⊆ U) (hz : ∀ x ∈ U, extDeriv ω x = 0) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating ω)
      (SmoothChains.toPaths (SmoothChains.boundary 1 (SmoothChains.simplex S))) = 0 := by
  have hext : SmoothChains.integral (extDeriv ω) (SmoothChains.simplex S) = 0 := by
    rw [SmoothChains.integral_simplex, simplexIntegral]
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro u hu
    change extDeriv ω (S.val u) (fun i => fderiv ℝ S.val u (EuclideanSpace.single i 1)) = 0
    rw [hz _ (him (mem_image_of_mem _ hu))]
    rfl
  have hs := SimplexStokes.smoothChains_stokes ω S hU hω him
  rw [hext] at hs
  rw [hs]
  simp only [SmoothChains.boundary_simplex, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [SmoothChains.toPaths_simplex, PathIntegration.chainIntegral_path]
  apply (SmoothChains.integral_eq_pathIntegral ω (S.face i) _).symm
  apply hω.continuousOn.mono
  rintro y ⟨u,hu,rfl⟩
  exact him ⟨relabel i.succAbove u, relabel_mem _ hu, rfl⟩

theorem mapped_triangle_boundary (T : SmoothChains.Simplex 2 (ℝ × ℝ))
    (S : (ℝ × ℝ) → E) (V : Set (ℝ × ℝ)) (hV : IsOpen V)
    (hS : ContDiffOn ℝ 2 S V) (hT : ∀ u ∈ standardSimplex 2, T.val u ∈ V) :
    toPaths (boundary 1 (simplex (T.mapOn S V hV hS hT))) =
      pathMap S (toPaths (boundary 1 (simplex T))) := by
  simp only [boundary_simplex, map_sum, map_zsmul, toPaths_simplex, pathMap_path]
  rfl

/-- Stokes on a square whose map is C² only near its closed source.
The two simplex maps and all four boundary restrictions remain literal maps. -/
theorem closed_square_boundary (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hsub : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ V) (hS : ContDiffOn ℝ 2 S V)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (him : MapsTo S (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) U)
    (hz : ∀ x ∈ U, extDeriv ω x = 0) :
    PathIntegration.chainIntegral (PathIntegration.fromAlternating ω)
      (surfaceBoundary (surface S)) = 0 := by
  let A := affine ![((0,0) : ℝ × ℝ),(1,0),(1,1)]
  let B := affine ![((0,0) : ℝ × ℝ),(0,1),(1,1)]
  have hA : ∀ u ∈ standardSimplex 2, A.val u ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← square_coverage]
    exact Or.inl (mem_image_of_mem _ hu)
  have hB : ∀ u ∈ standardSimplex 2, B.val u ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← square_coverage]
    exact Or.inr (mem_image_of_mem _ hu)
  let AS := A.mapOn S V hV hS (fun u hu => hsub (hA u hu))
  let BS := B.mapOn S V hV hS (fun u hu => hsub (hB u hu))
  have hAS : AS.val '' standardSimplex 2 ⊆ U := by
    rintro _ ⟨u,hu,rfl⟩
    exact him (hA u hu)
  have hBS : BS.val '' standardSimplex 2 ⊆ U := by
    rintro _ ⟨u,hu,rfl⟩
    exact him (hB u hu)
  have ha := closed_triangle_boundary ω AS hU hω hAS hz
  have hb := closed_triangle_boundary ω BS hU hω hBS hz
  have he : toPaths (boundary 1 (simplex AS - simplex BS)) =
      surfaceBoundary (surface S) := by
    simp only [map_sub]
    rw [mapped_triangle_boundary, mapped_triangle_boundary, ← map_sub, ← map_sub, ← map_sub]
    have hbase : toPaths (boundary 1 (simplex A - simplex B)) =
        surfaceBoundary (surface (fun p : ℝ × ℝ => p)) := by
      have hbase := triangulate_boundary (id : (ℝ × ℝ) → (ℝ × ℝ)) contDiff_id
      rw [triangulate, SmoothChains.map_id] at hbase
      exact hbase
    rw [hbase]
    exact (surfaceBoundary_map S (surface (fun p : ℝ × ℝ => p))).symm
  rw [← he, map_sub, map_sub, map_sub, ha, hb, sub_self]

end Stokes

/-- The straight-line homotopy specified in part (b), with the rectangle
rescaled positively to the unit square. -/
def straightHomotopy (γ : ℝ → ℂ) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  (1-p.2) • γ (2*Real.pi*p.1) + p.2 • circle r (2*Real.pi*p.1)

/-- Part (b). C² is required only on an open neighborhood of the closed curve
interval. The segment-avoidance hypothesis is literally about line segments. -/
theorem straight_homotopy_stokes {γ : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set ℝ} (hV : IsOpen V) (hsub : Icc 0 (2*Real.pi) ⊆ V)
    (hγ : ContDiffOn ℝ 2 γ V) (hclosed : γ 0 = γ (2*Real.pi))
    (havoid : ∀ t ∈ Icc 0 (2*Real.pi),
      (0 : ℂ) ∉ _root_.segment ℝ (circle r t) (γ t)) :
    angularIntegral γ (deriv γ) 0 (2*Real.pi) = 2*Real.pi := by
  let W : Set (ℝ × ℝ) := (fun p => 2*Real.pi*p.1) ⁻¹' V
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have ht (p : ℝ × ℝ) (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
      2*Real.pi*p.1 ∈ Icc 0 (2*Real.pi) :=
    ⟨mul_nonneg (by positivity) hp.1.1, mul_le_of_le_one_right (by positivity) hp.1.2⟩
  have hSW : Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 ⊆ W := fun p hp => hsub (ht p hp)
  have hH : ContDiffOn ℝ 2 (straightHomotopy γ r) W := by
    have harg : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => 2*Real.pi*p.1) W := by fun_prop
    have hcomp := hγ.comp harg (fun _ hp => hp)
    exact ((show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => 1-p.2) W by fun_prop).smul hcomp).add
      ((show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => p.2) W by fun_prop).smul
        ((circle_smooth r).contDiffOn.comp harg (fun _ _ => mem_univ _)))
  have him : MapsTo (straightHomotopy γ r)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) puncturedPlane := by
    intro p hp he
    apply havoid _ (ht p hp)
    refine ⟨p.2, 1-p.2, hp.2.1, sub_nonneg.mpr hp.2.2, by ring, ?_⟩
    simpa [straightHomotopy, add_comm] using he
  have hs := closed_square_boundary eta (straightHomotopy γ r) hW hSW hH
    isOpen_ne eta_smooth him (fun _ hz => eta_closed hz)
  have hedge : (fun t => straightHomotopy γ r (1,t)) =
      (fun t => straightHomotopy γ r (0,t)) := by
    funext t
    simp only [straightHomotopy, mul_one, mul_zero, ← hclosed]
    have hc : circle r (2*Real.pi) = circle r 0 := by
      apply Complex.ext <;> simp [circle]
    rw [hc]
  rw [OrientedChains.Parametric.surfaceBoundary_surface, hedge] at hs
  simp only [map_sub, map_add, PathIntegration.chainIntegral_path, fromAlternating_eta] at hs
  have hbot : (fun t => straightHomotopy γ r (t,0)) = fun t => γ (2*Real.pi*t) := by
    funext t; simp [straightHomotopy]
  have htop : (fun t => straightHomotopy γ r (t,1)) = fun t => circle r (2*Real.pi*t) := by
    funext t; simp [straightHomotopy]
  rw [hbot, htop, integral_rescale (by positivity)
    (fun t _ => circle_derivative r t), circle_integral hr] at hs
  have hd : ∀ t ∈ Icc 0 (2*Real.pi), HasDerivAt γ (deriv γ t) t := by
    intro t ht
    exact ((hγ.differentiableOn (by norm_num) t (hsub ht)).differentiableAt
      (hV.mem_nhds (hsub ht))).hasDerivAt
  rw [integral_rescale (by positivity) hd] at hs
  linarith

def ellipse (a b t : ℝ) : ℂ := ⟨a*Real.cos t, b*Real.sin t⟩

theorem ellipse_derivative (a b t : ℝ) :
    HasDerivAt (ellipse a b) (⟨-a*Real.sin t,b*Real.cos t⟩ : ℂ) t := by
  have h := Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
    (((Real.hasDerivAt_cos t).const_mul a).prodMk ((Real.hasDerivAt_sin t).const_mul b))
  convert h using 1
  · rfl
  · change (⟨-a*Real.sin t,b*Real.cos t⟩ : ℂ) = ⟨a * -Real.sin t,b*Real.cos t⟩
    congr 1
    ring

theorem ellipse_smooth (a b : ℝ) : ContDiff ℝ 2 (ellipse a b) :=
  Complex.equivRealProdCLM.symm.contDiff.comp
    ((contDiff_const.mul Real.contDiff_cos).prodMk (contDiff_const.mul Real.contDiff_sin))

theorem ellipse_coefficient (a b t : ℝ) :
    etaLinear (ellipse a b t) (deriv (ellipse a b) t) =
      a*b/(a^2*Real.cos t^2+b^2*Real.sin t^2) := by
  rw [(ellipse_derivative a b t).deriv,etaLinear_apply]
  dsimp [ellipse]
  congr 1
  · nlinarith [congrArg (fun x : ℝ => a*b*x) (Real.sin_sq_add_cos_sq t)]
  · ring

/-- Part (c), obtained by applying the prescribed straight-line Stokes homotopy. -/
theorem ellipse_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..2*Real.pi, a*b/(a^2*Real.cos t^2+b^2*Real.sin t^2)) =
      2*Real.pi := by
  have hav : ∀ t ∈ Icc 0 (2*Real.pi),
      (0 : ℂ) ∉ _root_.segment ℝ (circle 1 t) (ellipse a b t) := by
    rintro t _ ⟨u,v,hu,hv,huv,he⟩
    have hx := congrArg Complex.re he
    have hy := congrArg Complex.im he
    simp only [Complex.add_re,Complex.add_im,Complex.real_smul,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      add_zero,sub_zero,circle,ellipse,Complex.zero_re,Complex.zero_im,one_mul] at hx hy
    have hpa : 0 < u+v*a := by
      by_cases hz : v = 0
      · simp [hz] at huv ⊢; linarith
      · positivity
    have hpb : 0 < u+v*b := by
      by_cases hz : v = 0
      · simp [hz] at huv ⊢; linarith
      · positivity
    have hcos : Real.cos t = 0 := (mul_eq_zero.mp
      (show (u+v*a)*Real.cos t = 0 by nlinarith)).resolve_left hpa.ne'
    have hsin : Real.sin t = 0 := (mul_eq_zero.mp
      (show (u+v*b)*Real.sin t = 0 by nlinarith)).resolve_left hpb.ne'
    have hh := Real.sin_sq_add_cos_sq t
    simp [hcos,hsin] at hh
  have hcl : ellipse a b 0 = ellipse a b (2*Real.pi) := by
    apply Complex.ext <;> simp [ellipse]
  have h := straight_homotopy_stokes (r := 1) (by norm_num) isOpen_univ (subset_univ _)
    (ellipse_smooth a b).contDiffOn hcl hav
  simpa only [angularIntegral,ellipse_coefficient] using h

/-- A single angle primitive off the negative real axis, constructed from the
first arctangent chart by the half-angle map. -/
def cutAngle (z : ℂ) : ℝ :=
  2*xAngle ⟨Real.sqrt (z.re^2+z.im^2)+z.re,z.im⟩

theorem half_angle_positive {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < Real.sqrt (z.re^2+z.im^2)+z.re := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))
  have hn := Real.sqrt_nonneg (z.re^2+z.im^2)
  rcases hz with hx | hy
  · linarith
  · have hy2 : 0 < z.im^2 := sq_pos_of_ne_zero hy
    nlinarith

/-- This derivative is obtained from `xAngle_derivative`, the primitive in (d). -/
theorem cutAngle_curve_derivative {q : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hq : HasDerivAt q v t) (hz : q t ∈ Complex.slitPlane) :
    HasDerivAt (fun s => cutAngle (q s)) (etaLinear (q t) v) t := by
  let x := (q t).re
  let y := (q t).im
  let R := Real.sqrt (x^2+y^2)
  have hR2 : R^2 = x^2+y^2 := Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hA : 0 < R+x := half_angle_positive hz
  have hR : 0 < R := by
    have hnon := Complex.slitPlane_ne_zero hz
    have hxy : 0 < x^2+y^2 := by
      by_contra hh
      have hx : x = 0 := by nlinarith [sq_nonneg x,sq_nonneg y]
      have hy : y = 0 := by nlinarith [sq_nonneg x,sq_nonneg y]
      exact hnon (Complex.ext hx hy)
    exact Real.sqrt_pos.mpr hxy
  have hx := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hq
  have hy := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hq
  have hn := ((hx.pow 2).add (hy.pow 2)).sqrt (show (q t).re^2+(q t).im^2 ≠ 0 by
    change x^2+y^2 ≠ 0
    rw [← hR2]
    exact pow_ne_zero 2 hR.ne')
  have hm := Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t ((hn.add hx).prodMk hy)
  have hd := ((xAngle_derivative (z := ⟨R+x,y⟩) hA.ne').comp_hasDerivAt t hm).const_mul 2
  convert hd using 1
  · rfl
  · simp only [etaLinear_apply]
    change (x*v.im-y*v.re)/(x^2+y^2) =
      2*(((R+x)*v.im-y*((2*x^(2-1)*v.re+2*y^(2-1)*v.im)/(2*R)+v.re))/((R+x)^2+y^2))
    have hB : (R+x)^2+y^2 = 2*R*(R+x) := by nlinarith [hR2]
    rw [hB,← hR2]
    field_simp [hR.ne',hA.ne']
    norm_num
    nlinarith [congrArg (fun a : ℝ => a*v.im) hR2]

theorem quotient_slitPlane {a b : ℂ} (ha : a ≠ 0)
    (hav : (0 : ℂ) ∉ _root_.segment ℝ a b) : b/a ∈ Complex.slitPlane := by
  by_contra h
  have hx : (b/a).re ≤ 0 := by
    by_contra hn
    exact h (Or.inl (lt_of_not_ge hn))
  have hy : (b/a).im = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  let x := (b/a).re
  have hd : 0 < 1-x := by dsimp [x]; linarith
  have he : b = (x : ℂ)*a := by
    have hq : b/a = (x : ℂ) := Complex.ext rfl hy
    exact (div_eq_iff ha).mp hq
  apply hav
  refine ⟨-x/(1-x),1/(1-x),div_nonneg (neg_nonneg.mpr hx) hd.le,
    by positivity,?_,?_⟩
  · field_simp
    ring
  · rw [he]
    simp only [Complex.real_smul,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_sub,
      Complex.ofReal_one]
    have hdn : (1-(x : ℂ)) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
    ring

theorem eta_quotient (a b u v : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    etaLinear (a/b) ((u*b-a*v)/b^2) = etaLinear a u-etaLinear b v := by
  simp only [eta_eq_im_div,← Complex.sub_im]
  congr 1
  field_simp

/-- Part (e). The half-angle primitive is built from (d). FTC on this single
primitive of the quotient curve proves the result without using Stokes. -/
theorem straight_homotopy_local_primitives {γ : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set ℝ} (hV : IsOpen V) (hsub : Icc 0 (2*Real.pi) ⊆ V)
    (hγ : ContDiffOn ℝ 2 γ V) (hclosed : γ 0 = γ (2*Real.pi))
    (havoid : ∀ t ∈ Icc 0 (2*Real.pi),
      (0 : ℂ) ∉ _root_.segment ℝ (circle r t) (γ t)) :
    angularIntegral γ (deriv γ) 0 (2*Real.pi) = 2*Real.pi := by
  have hdγ (t : ℝ) (ht : t ∈ Icc 0 (2*Real.pi)) : HasDerivAt γ (deriv γ t) t :=
    ((hγ.differentiableOn (by norm_num) t (hsub ht)).differentiableAt
      (hV.mem_nhds (hsub ht))).hasDerivAt
  have hγn (t : ℝ) (ht : t ∈ Icc 0 (2*Real.pi)) : γ t ≠ 0 := by
    intro he
    apply havoid t ht
    rw [← he]
    exact ⟨0,1,le_rfl,zero_le_one,by norm_num,by simp⟩
  have hprim (t : ℝ) (ht : t ∈ Icc 0 (2*Real.pi)) :
      HasDerivAt (fun s => cutAngle (γ s/circle r s)) (etaLinear (γ t) (deriv γ t)-1) t := by
    have hq := (hdγ t ht).fun_div (circle_derivative r t) (circle_nonzero hr t)
    have hc := cutAngle_curve_derivative hq (quotient_slitPlane (circle_nonzero hr t) (havoid t ht))
    rw [eta_quotient _ _ _ _ (hγn t ht) (circle_nonzero hr t),circle_coefficient hr] at hc
    exact hc
  have hcont : ContinuousOn (fun t => etaLinear (γ t) (deriv γ t)) (Icc 0 (2*Real.pi)) := by
    simp only [eta_eq_im_div]
    apply Complex.continuous_im.comp_continuousOn
    apply ContinuousOn.div _ _ hγn
    · exact (hγ.continuousOn_deriv_of_isOpen hV (by norm_num)).mono hsub
    · exact hγ.continuousOn.mono hsub
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := 2*Real.pi)
    (fun t ht => hprim t (by simpa [uIcc_of_le (by positivity : 0 ≤ 2*Real.pi)] using ht))
    ((hcont.sub continuousOn_const).intervalIntegrable_of_Icc (by positivity))
  have hc : circle r (2*Real.pi) = circle r 0 := by
    apply Complex.ext <;> simp [circle]
  rw [hc,← hclosed,sub_self,intervalIntegral.integral_sub
    (hcont.intervalIntegrable_of_Icc (by positivity)) intervalIntegrable_const,
    intervalIntegral.integral_const] at hi
  simp only [sub_zero,smul_eq_mul,mul_one] at hi
  exact sub_eq_zero.mp hi

/-- The circle computation also gives the literal source Riemann integral. -/
theorem circle_source_integral {r : ℝ} (hr : 0 < r) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => etaLinear (circle r t) (circleVelocity r t)) id 0 (2*Real.pi) (2*Real.pi) := by
  have hc : ContinuousOn (fun t => etaLinear (circle r t) (circleVelocity r t))
      (Icc 0 (2*Real.pi)) := by
    simp only [circle_coefficient hr]
    exact continuousOn_const
  have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by positivity : 0 ≤ 2*Real.pi) hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id,
    show (∫ t in (0 : ℝ)..2*Real.pi, etaLinear (circle r t) (circleVelocity r t)) =
      2*Real.pi from circle_integral hr] using h

/-- The homotopy result includes source integral existence, not only a total
Bochner value. -/
theorem straight_homotopy_source {γ : ℝ → ℂ} {r : ℝ} (hr : 0 < r)
    {V : Set ℝ} (hV : IsOpen V) (hsub : Icc 0 (2*Real.pi) ⊆ V)
    (hγ : ContDiffOn ℝ 2 γ V) (hclosed : γ 0 = γ (2*Real.pi))
    (havoid : ∀ t ∈ Icc 0 (2*Real.pi),
      (0 : ℂ) ∉ _root_.segment ℝ (circle r t) (γ t)) :
    StieltjesPrototype.HasDarbouxRSIntegral (fun t => etaLinear (γ t) (deriv γ t))
      id 0 (2*Real.pi) (2*Real.pi) := by
  have hl : Rudin.Chapter08.IsC1NonzeroLoop γ (deriv γ) 0 (2*Real.pi) := by
    refine ⟨by positivity,hclosed,?_,
      (hγ.continuousOn_deriv_of_isOpen hV (by norm_num)).mono hsub,?_⟩
    · intro t ht
      exact ((hγ.differentiableOn (by norm_num) t (hsub ht)).differentiableAt
        (hV.mem_nhds (hsub ht))).hasDerivAt.hasDerivWithinAt
    · intro t ht he
      apply havoid t ht
      exact ⟨0,1,le_rfl,zero_le_one,by norm_num,by simp [he]⟩
  have h := angularIntegral_source hl
  rw [straight_homotopy_stokes hr hV hsub hγ hclosed havoid] at h
  exact h

theorem ellipse_source_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun t => a*b/(a^2*Real.cos t^2+b^2*Real.sin t^2)) id 0 (2*Real.pi) (2*Real.pi) := by
  have hn (t : ℝ) : a^2*Real.cos t^2+b^2*Real.sin t^2 ≠ 0 := by
    intro he
    have hx : a*Real.cos t = 0 := by nlinarith [sq_nonneg (a*Real.cos t),sq_nonneg (b*Real.sin t)]
    have hy : b*Real.sin t = 0 := by nlinarith [sq_nonneg (a*Real.cos t),sq_nonneg (b*Real.sin t)]
    have hcos := (mul_eq_zero.mp hx).resolve_left ha.ne'
    have hsin := (mul_eq_zero.mp hy).resolve_left hb.ne'
    have hh := Real.sin_sq_add_cos_sq t
    simp [hcos,hsin] at hh
  have hc : ContinuousOn (fun t => a*b/(a^2*Real.cos t^2+b^2*Real.sin t^2))
      (Icc 0 (2*Real.pi)) := by
    exact continuousOn_const.div (by fun_prop) (fun t _ => hn t)
  have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id
    (by positivity : 0 ≤ 2*Real.pi) hc
  simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
    ← Real.volume_eq_stieltjes_id,ellipse_integral ha hb] using h

end Rudin.Chapter10.Exercise21
