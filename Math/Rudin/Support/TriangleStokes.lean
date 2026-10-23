module

public import Math.Rudin.Support.SimplexIntegration
public import Math.Rudin.Support.FormsPrototype

/-! # Stokes on a parameter triangle
The full real plane 1-form P dx + Q dy has the actual oriented triangle
boundary identity. This extends the horizontal prototype, using FTC and the
proved two-dimensional order-exchange theorem. General dimension and
orientation-quotient descent are not claimed here.
-/

@[expose] public section

noncomputable section

namespace Rudin.Support.TriangleStokes

open Set MeasureTheory
open OrientedChains.Parametric PathIntegration SimplexIntegration

/-- Both coordinate components in the actual alternating-map representation. -/
def coordinateForm (P Q : (ℝ × ℝ) → ℝ) : Form 1 (ℝ × ℝ) :=
  fun p => P p • ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    Q p • ContinuousAlternatingMap.ofSubsingleton ℝ (ℝ × ℝ) ℝ (0 : Fin 1)
      (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp] theorem coordinateForm_apply (P Q : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ)
    (v : Fin 1 → ℝ × ℝ) :
    coordinateForm P Q p v = P p * (v 0).1 + Q p * (v 0).2 := rfl

theorem exterior_coordinateForm (P Q : (ℝ × ℝ) → ℝ)
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q) (p : ℝ × ℝ) :
    extDeriv (coordinateForm P Q) p ![(1, 0), (0, 1)] =
      fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1) := by
  have hw : DifferentiableAt ℝ (coordinateForm P Q) p := by
    exact ((hP p).smul_const _).add ((hQ p).smul_const _)
  rw [extDeriv_apply hw]
  simp [Fin.sum_univ_two, coordinateForm_apply, Fin.removeNth, sub_eq_add_neg]

theorem triangleCoefficient_coordinateForm (P Q : (ℝ × ℝ) → ℝ)
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q) (p : ℝ × ℝ) :
    triangleCoefficient (extDeriv (coordinateForm P Q)) id p =
      fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1) := by
  simpa [triangleCoefficient, pullback_apply] using exterior_coordinateForm P Q hP hQ p

/-- The opposite integration order gives the vertical component by FTC. -/
theorem vertical_integral (Q : (ℝ × ℝ) → ℝ) (hQ : ContDiff ℝ 1 Q) :
    triangleIntegral (fun p => fderiv ℝ Q p (1, 0)) =
      (∫ t in (0 : ℝ)..1, Q (1 - t, t)) - ∫ t in (0 : ℝ)..1, Q (0, t) := by
  have hc : Continuous (fun p => fderiv ℝ Q p (1, 0)) :=
    (hQ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  rw [triangleIntegral_swap _ hc, triangleIntegral]
  have hs (y : ℝ) : (∫ x in (0 : ℝ)..(1 - y), fderiv ℝ Q (x, y) (1, 0)) =
      Q (1 - y, y) - Q (0, y) := by
    have hd (x : ℝ) : HasDerivAt (fun x => Q (x, y)) (fderiv ℝ Q (x, y) (1, 0)) x :=
      (hQ.differentiable (by norm_num) (x, y)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  simp only [Function.comp_apply, Prod.swap_prod_mk]
  simp_rw [hs]
  rw [intervalIntegral.integral_sub]
  · exact (hQ.continuous.comp ((continuous_const.sub continuous_id).prodMk continuous_id)).intervalIntegrable _ _
  · exact (hQ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- All three edges are actual parameter restrictions, with their tangents. -/
theorem coordinate_boundary (P Q : (ℝ × ℝ) → ℝ) (hP : Continuous P) (hQ : Continuous Q) :
    chainIntegral (fromAlternating (coordinateForm P Q)) (triangleBoundary id) =
      ((∫ t in (0 : ℝ)..1, Q (1 - t, t)) - ∫ t in (0 : ℝ)..1, Q (0, t)) +
      ((∫ t in (0 : ℝ)..1, P (t, 0)) - ∫ t in (0 : ℝ)..1, P (t, 1 - t)) := by
  have hb (t : ℝ) : HasDerivAt (fun t : ℝ => (t, (0 : ℝ))) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t 0)
  have hv (t : ℝ) : HasDerivAt (fun t : ℝ => ((0 : ℝ), t)) (0, 1) t :=
    (hasDerivAt_const t 0).prodMk (hasDerivAt_id t)
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (1 - t, t)) (-1, 1) t :=
    ((hasDerivAt_id t).const_sub 1).prodMk (hasDerivAt_id t)
  simp only [triangleBoundary, map_add, map_sub, chainIntegral_path, pathIntegral,
    coefficient, Function.id_def, fromAlternating_apply, coordinateForm_apply,
    (hb _).deriv, (hv _).deriv, (hd _).deriv, mul_zero, mul_one, mul_neg_one,
    add_zero, zero_add]
  have hp : IntervalIntegrable (fun t : ℝ => -P (1 - t, t)) volume 0 1 :=
    (show Continuous (fun t : ℝ => -P (1 - t, t)) by fun_prop).intervalIntegrable _ _
  have hq : IntervalIntegrable (fun t : ℝ => Q (1 - t, t)) volume 0 1 :=
    (show Continuous (fun t : ℝ => Q (1 - t, t)) by fun_prop).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hp hq, intervalIntegral.integral_neg]
  have hi := intervalIntegral.integral_comp_sub_left
    (fun s => P (s, 1 - s)) (a := (0 : ℝ)) (b := 1) 1
  norm_num at hi
  rw [hi]
  ring

/-- The actual exterior derivative integrates to the actual oriented boundary.
The hypotheses imply every integral's existence, including the exterior one. -/
theorem coordinate_stokes (P Q : (ℝ × ℝ) → ℝ)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    formIntegral (extDeriv (coordinateForm P Q)) id =
      chainIntegral (fromAlternating (coordinateForm P Q)) (triangleBoundary id) := by
  have hcP : Continuous (fun p => fderiv ℝ P p (0, 1)) :=
    (hP.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcQ : Continuous (fun p => fderiv ℝ Q p (1, 0)) :=
    (hQ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsplit : triangleIntegral (fun p => fderiv ℝ Q p (1, 0) - fderiv ℝ P p (0, 1)) =
      triangleIntegral (fun p => fderiv ℝ Q p (1, 0)) +
      triangleIntegral (fun p => -fderiv ℝ P p (0, 1)) := by
    have hi (x : ℝ) := intervalIntegral.integral_sub
      ((triangle_integrable _ hcQ).1 x) ((triangle_integrable _ hcP).1 x)
    unfold triangleIntegral
    simp_rw [hi, intervalIntegral.integral_neg]
    rw [intervalIntegral.integral_sub (triangle_integrable _ hcQ).2
      (triangle_integrable _ hcP).2]
    ring
  have hh : triangleIntegral (fun p => -fderiv ℝ P p (0, 1)) =
      chainIntegral (horizontal P) (triangleBoundary id) := by
    have h := horizontal_stokes P hP
    have he := funext (triangleCoefficient_horizontal P (hP.differentiable (by norm_num)))
    rw [formIntegral, he] at h
    exact h
  rw [formIntegral]
  have he := funext (triangleCoefficient_coordinateForm P Q
    (hP.differentiable (by norm_num)) (hQ.differentiable (by norm_num)))
  rw [he, hsplit, vertical_integral Q hQ, hh, horizontal_boundary,
    coordinate_boundary P Q hP.continuous hQ.continuous]

/-- Every plane 1-form is exactly its two coordinate components. -/
theorem coordinateForm_eq (ω : Form 1 (ℝ × ℝ)) :
    coordinateForm (FormsPrototype.planeP ω) (FormsPrototype.planeQ ω) = ω := by
  funext p
  ext v
  rw [coordinateForm_apply]
  have hv : v = fun _ => v 0 := by
    funext i
    fin_cases i
    rfl
  rw [hv]
  change FormsPrototype.planeP ω p * (v 0).1 + FormsPrototype.planeQ ω p * (v 0).2 =
    fromAlternating ω p (v 0)
  have he : v 0 = (v 0).1 • ((1 : ℝ), (0 : ℝ)) + (v 0).2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_rhs => rw [he]
  rw [map_add, map_smul, map_smul]
  simp only [fromAlternating_apply, FormsPrototype.planeP, FormsPrototype.planeQ, smul_eq_mul]
  ring

/-- Stokes for any C¹ real 1-form on the coordinate plane. -/
theorem stokes (ω : Form 1 (ℝ × ℝ)) (hω : ContDiff ℝ 1 ω) :
    formIntegral (extDeriv ω) id =
      chainIntegral (fromAlternating ω) (triangleBoundary id) := by
  have hp : ContDiff ℝ 1 (FormsPrototype.planeP ω) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ
      (fun _ : Fin 1 => (1, 0))).contDiff.comp hω
  have hq : ContDiff ℝ 1 (FormsPrototype.planeQ ω) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ
      (fun _ : Fin 1 => (0, 1))).contDiff.comp hω
  simpa only [coordinateForm_eq] using
    coordinate_stokes (FormsPrototype.planeP ω) (FormsPrototype.planeQ ω) hp hq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Regularity of the actual pullback is derived from the form and map. -/
theorem pullback_contDiff (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hω : ContDiff ℝ 1 ω) (hS : ContDiff ℝ 2 S) :
    ContDiff ℝ 1 (pullback ω S) := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E)
    (F := ℝ) (0 : Fin 1)
  let e' := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ℝ × ℝ)
    (F := ℝ) (0 : Fin 1)
  have hw : ContDiff ℝ 1 (fun p => e.symm (ω (S p))) :=
    e.symm.toContinuousLinearEquiv.contDiff.comp (hω.comp (hS.of_le (by norm_num)))
  have hd : ContDiff ℝ 1 (fderiv ℝ S) := hS.fderiv_right (by norm_num)
  have hc := hw.clm_comp hd
  have hh := e'.toContinuousLinearEquiv.contDiff.comp hc
  convert hh using 1
  funext p
  ext v
  change ω (S p) (fun i => fderiv ℝ S p (v i)) =
    ω (S p) (fun _ => fderiv ℝ S p (v 0))
  congr 1
  funext i
  fin_cases i
  rfl

/-- A C² parameter triangle may be nonlinear, noninjective or degenerate.
The C¹ form and C² map imply every regularity condition. -/
theorem pullback_stokes (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hω : ContDiff ℝ 1 ω) (hS : ContDiff ℝ 2 S) :
    formIntegral (extDeriv ω) S =
      chainIntegral (fromAlternating ω) (triangleBoundary S) := by
  have hc : triangleCoefficient (extDeriv ω) S =
      triangleCoefficient (extDeriv (pullback ω S)) id := by
    funext p
    have h := exterior_pullback ω S p (hω.differentiable (by norm_num) _) hS.contDiffAt
    simp only [triangleCoefficient]
    rw [← h]
    simp [pullback_apply]
  rw [formIntegral, hc, ← formIntegral,
    stokes (pullback ω S) (pullback_contDiff ω S hω hS),
    ← triangleBoundary_integral_pullback ω S (hS.differentiable (by norm_num))]

/-- The exterior pullback coefficient is continuous, so no total-integral
default is used in the boundary theorem. -/
theorem coefficient_continuous (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hω : ContDiff ℝ 1 ω) (hS : ContDiff ℝ 2 S) :
    Continuous (triangleCoefficient (extDeriv ω) S) := by
  let η := pullback ω S
  have hη : ContDiff ℝ 1 η := pullback_contDiff ω S hω hS
  have hp : ContDiff ℝ 1 (FormsPrototype.planeP η) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ
      (fun _ : Fin 1 => (1, 0))).contDiff.comp hη
  have hq : ContDiff ℝ 1 (FormsPrototype.planeQ η) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ
      (fun _ : Fin 1 => (0, 1))).contDiff.comp hη
  have he : triangleCoefficient (extDeriv ω) S = fun p =>
      fderiv ℝ (FormsPrototype.planeQ η) p (1, 0) -
      fderiv ℝ (FormsPrototype.planeP η) p (0, 1) := by
    funext p
    have h := exterior_pullback ω S p (hω.differentiable (by norm_num) _) hS.contDiffAt
    unfold triangleCoefficient
    rw [← h]
    exact FormsPrototype.exterior_plane (hη.differentiable (by norm_num) p)
  rw [he]
  exact ((hq.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
    ((hp.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- Literal closed-triangle zero-extension Riemann witnesses, with the actual
parameter-boundary integral as the outer value. -/
theorem pullback_stokes_source (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hω : ContDiff ℝ 1 ω) (hS : ContDiff ℝ 2 S) :
    (∀ x ∈ Icc (0 : ℝ) 1, StieltjesPrototype.HasDarbouxRSIntegral
      (fun y => triangleZeroExtension (triangleCoefficient (extDeriv ω) S) (x, y))
      id 0 1 (∫ y in 0..(1 - x), triangleCoefficient (extDeriv ω) S (x, y))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (fun x => ∫ y in 0..1,
        triangleZeroExtension (triangleCoefficient (extDeriv ω) S) (x, y)) id 0 1
      (chainIntegral (fromAlternating ω) (triangleBoundary S)) := by
  obtain ⟨hi, ho⟩ := triangle_source_riemann _
    (coefficient_continuous ω S hω hS)
  refine ⟨hi, ?_⟩
  rw [← pullback_stokes ω S hω hS]
  exact ho

/-- A continuous 1-form on a genuine C¹ path has the source Riemann integral. -/
theorem smooth_path_source (ω : Form 1 E) (p : ℝ → E)
    (hω : Continuous ω) (hp : ContDiff ℝ 1 p) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating ω) p) id 0 1
      (pathIntegral (fromAlternating ω) p) := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E)
    (F := ℝ) (0 : Fin 1)
  have hw : Continuous (fromAlternating ω) :=
    e.symm.toContinuousLinearEquiv.continuous.comp hω
  apply darboux_path_bridge
  exact ((hw.comp hp.continuous).clm_apply hp.continuous_deriv_one).continuousOn

/-- Every actual parameter edge, including the nonlinear diagonal, has its
source integral before the signed boundary combination is formed. -/
theorem boundary_source (ω : Form 1 E) (S : (ℝ × ℝ) → E)
    (hω : Continuous ω) (hS : ContDiff ℝ 1 S) :
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating ω) (fun t => S (1 - t, t))) id 0 1
      (pathIntegral (fromAlternating ω) (fun t => S (1 - t, t))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating ω) (fun t => S (0, t))) id 0 1
      (pathIntegral (fromAlternating ω) (fun t => S (0, t))) ∧
    StieltjesPrototype.HasDarbouxRSIntegral
      (coefficient (fromAlternating ω) (fun t => S (t, 0))) id 0 1
      (pathIntegral (fromAlternating ω) (fun t => S (t, 0))) := by
  exact ⟨smooth_path_source ω _ hω (hS.comp (by fun_prop)),
    smooth_path_source ω _ hω (hS.comp (by fun_prop)),
    smooth_path_source ω _ hω (hS.comp (by fun_prop))⟩

/-- A nonhorizontal regression: ω=-y dx+x dy integrates to 1 on the triangle. -/
theorem both_components_example :
    formIntegral (extDeriv (coordinateForm (fun p => -p.2) (fun p => p.1))) id = 1 ∧
    chainIntegral (fromAlternating (coordinateForm (fun p => -p.2) (fun p => p.1)))
      (triangleBoundary id) = 1 := by
  have hp : ContDiff ℝ 1 (fun p : ℝ × ℝ => -p.2) := by fun_prop
  have hq : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1) := by fun_prop
  have hb : chainIntegral
      (fromAlternating (coordinateForm (fun p => -p.2) (fun p => p.1)))
      (triangleBoundary id) = 1 := by
    rw [coordinate_boundary _ _ hp.continuous hq.continuous]
    norm_num [intervalIntegral.integral_sub, intervalIntegral.integral_neg,
      intervalIntegral.integral_const, integral_id]
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
      (g := fun t : ℝ => t) (μ := volume) intervalIntegrable_const
      (continuous_id.intervalIntegrable 0 1)]
    norm_num
  exact ⟨by rw [coordinate_stokes _ _ hp hq, hb], hb⟩

end Rudin.Support.TriangleStokes
