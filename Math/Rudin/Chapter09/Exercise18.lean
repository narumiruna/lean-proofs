module

public import Math.Rudin.Chapter09.Exercise17
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # The square map on the Euclidean complex plane -/

@[expose] public section

open Set Filter
open scoped Topology Matrix

namespace Rudin.Chapter09

noncomputable def exercise18F (z : ℂ) : ℂ := z ^ 2

/-- Literal real coordinate functions of the source map. -/
theorem exercise18_coordinates (z : ℂ) :
    (exercise18F z).re = z.re ^ 2 - z.im ^ 2 ∧
    (exercise18F z).im = 2 * z.re * z.im := by
  simp [exercise18F, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem exercise18_xy (x y : ℝ) :
    exercise18F ((x : ℂ) + y * Complex.I) =
      ((x ^ 2 - y ^ 2 : ℝ) : ℂ) + (2 * x * y : ℝ) * Complex.I := by
  apply Complex.ext
  · rw [(exercise18_coordinates _).1]
    simp only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero,
      Complex.ofReal_re, Complex.add_im, Complex.mul_I_im, zero_add]
  · rw [(exercise18_coordinates _).2]
    simp only [Complex.add_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero,
      Complex.ofReal_re, Complex.add_im, Complex.mul_I_im, zero_add]

/-- An explicit inverse branch near the source's negative-real image point. -/
noncomputable def exercise18G (w : ℂ) : ℂ :=
  Complex.exp (Complex.log (-w) / 2) * Complex.I

theorem exercise18_right_inverse {w : ℂ} (hw : w ≠ 0) :
    exercise18F (exercise18G w) = w := by
  rw [exercise18F, exercise18G, mul_pow, Complex.I_sq]
  rw [pow_two, ← Complex.exp_add]
  rw [show Complex.log (-w) / 2 + Complex.log (-w) / 2 = Complex.log (-w) by ring,
    Complex.exp_log (neg_ne_zero.mpr hw)]
  ring

theorem exercise18_range : range exercise18F = univ := by
  apply eq_univ_of_forall
  intro w
  by_cases hw : w = 0
  · subst w; exact ⟨0, by simp [exercise18F]⟩
  · exact ⟨exercise18G w, exercise18_right_inverse hw⟩

noncomputable def exercise18D (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) (2 * z)

theorem exercise18_hasFDerivAt (z : ℂ) : HasFDerivAt exercise18F (exercise18D z) z := by
  have he : exercise18D z =
      (ContinuousLinearMap.toSpanSingleton ℂ (2 * z)).restrictScalars ℝ := by
    ext w
    simp [exercise18D, mul_comm]
  rw [he]
  convert! (hasDerivAt_pow 2 z).hasFDerivAt.restrictScalars ℝ using 1
  simp

noncomputable def exercise18Jacobian (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * z.re, -(2 * z.im); 2 * z.im, 2 * z.re]

theorem exercise18_matrix_action (z w : ℂ) :
    exercise18Jacobian z *ᵥ ![w.re, w.im] =
      ![(exercise18D z w).re, (exercise18D z w).im] := by
  ext i
  fin_cases i <;> simp [exercise18Jacobian, exercise18D, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem exercise18_jacobian (z : ℂ) : (exercise18Jacobian z).det = 4 * ‖z‖ ^ 2 := by
  rw [exercise18Jacobian, Matrix.det_fin_two, exercise17_euclidean_norm]
  simp
  ring

theorem exercise18_jacobian_zero_iff (z : ℂ) : (exercise18Jacobian z).det = 0 ↔ z = 0 := by
  rw [exercise18_jacobian]
  simp

theorem exercise18_not_injective : ¬Function.Injective exercise18F := by
  intro h
  have he : exercise18F 1 = exercise18F (-1) := by norm_num [exercise18F]
  have hi := h he
  norm_num at hi

theorem exercise18_not_injOn_nhds_zero {s : Set ℂ} (hs : s ∈ 𝓝 (0 : ℂ)) :
    ¬InjOn exercise18F s := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  intro hi
  have hp : (r / 2 : ℂ) ∈ s := hrs (by
    simp [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    linarith)
  have hn : -(r / 2 : ℂ) ∈ s := hrs (by
    simp [Metric.mem_ball, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    linarith)
  have he := hi hp hn (by simp [exercise18F])
  have hre := congrArg Complex.re he
  simp at hre
  linarith

theorem exercise18_locally_injective_iff (z : ℂ) :
    (∃ s ∈ 𝓝 z, InjOn exercise18F s) ↔ z ≠ 0 := by
  constructor
  · rintro ⟨s, hs, hi⟩ rfl
    exact exercise18_not_injOn_nhds_zero hs hi
  · intro hz
    have hd : HasStrictDerivAt exercise18F (2 * z) z := by
      convert! hasStrictDerivAt_pow 2 z using 1
      simp
    have hd0 : 2 * z ≠ 0 := mul_ne_zero (by norm_num) hz
    have hl := hd.eventually_left_inverse hd0
    refine ⟨{w | hd.localInverse exercise18F (2 * z) z hd0 (exercise18F w) = w}, hl, ?_⟩
    intro u hu v hv huv
    rw [← hu, ← hv, huv]

noncomputable def exercise18A : ℂ := (Real.pi / 3 : ℝ) * Complex.I
noncomputable def exercise18B : ℂ := exercise18F exercise18A

theorem exercise18_b_value : exercise18B = -((Real.pi / 3 : ℝ) ^ 2 : ℂ) := by
  simp [exercise18B, exercise18F, exercise18A, mul_pow, Complex.I_sq]

theorem exercise18_branch_continuous {w : ℂ} (hw : -w ∈ Complex.slitPlane) :
    ContinuousAt exercise18G w := by
  exact ((((Complex.hasDerivAt_log hw).continuousAt).comp continuous_neg.continuousAt).div_const 2).cexp.mul_const _

theorem exercise18_branch_upper {w : ℂ} (hw : -w ∈ Complex.slitPlane) :
    0 < (exercise18G w).im := by
  have hlo := Complex.neg_pi_lt_arg (-w)
  have hhi : (-w).arg < Real.pi :=
    (Complex.arg_lt_pi_iff.mpr (hw.imp_left le_of_lt))
  have hc : 0 < Real.cos ((-w).arg / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  simpa [exercise18G, Complex.mul_I_im, Complex.exp_re, Complex.div_re,
    Complex.div_im, Complex.normSq_ofNat, Complex.log_im] using
    mul_pos (Real.exp_pos ((Complex.log (-w)).re / 2)) hc

theorem exercise18_square_injOn_upper : InjOn exercise18F {z : ℂ | 0 < z.im} := by
  intro z hz w hw he
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · exact he
  · have hh := congrArg Complex.im he
    simp at hh
    change 0 < z.im at hz
    change 0 < w.im at hw
    linarith

theorem exercise18_upper_maps {z : ℂ} (hz : 0 < z.im) :
    -(exercise18F z) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hr : z.re = 0
  · left
    simp [exercise18F, pow_two, Complex.mul_re, hr]
    positivity
  · right
    change -(exercise18F z).im ≠ 0
    rw [exercise18_coordinates z |>.2]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hr) hz.ne')

theorem exercise18_left_inverse {z : ℂ} (hz : 0 < z.im) :
    exercise18G (exercise18F z) = z := by
  apply exercise18_square_injOn_upper (exercise18_branch_upper (exercise18_upper_maps hz)) hz
  apply exercise18_right_inverse
  simp only [exercise18F, ne_eq, pow_eq_zero_iff (by norm_num : 2 ≠ 0)]
  intro he
  simp [he] at hz

theorem exercise18_inverse_value : exercise18G exercise18B = exercise18A := by
  apply exercise18_left_inverse
  simp [exercise18A]
  exact Real.pi_pos

theorem exercise18_a_upper : 0 < exercise18A.im := by
  simp [exercise18A]
  exact Real.pi_pos

theorem exercise18_inverse_branch :
    ∃ (u v : Set ℂ), IsOpen u ∧ IsOpen v ∧ exercise18A ∈ u ∧ exercise18B ∈ v ∧
      MapsTo exercise18F u v ∧ MapsTo exercise18G v u ∧
      (∀ z ∈ u, exercise18G (exercise18F z) = z) ∧
      (∀ z ∈ v, exercise18F (exercise18G z) = z) ∧ ContinuousOn exercise18G v := by
  refine ⟨{z | 0 < z.im}, {w | -w ∈ Complex.slitPlane},
    isOpen_lt continuous_const Complex.continuous_im,
    Complex.isOpen_slitPlane.preimage continuous_neg, exercise18_a_upper,
    exercise18_upper_maps exercise18_a_upper,
    fun _ hz ↦ exercise18_upper_maps hz, fun _ hw ↦ exercise18_branch_upper hw,
    fun _ hz ↦ exercise18_left_inverse hz,
    fun w hw ↦ exercise18_right_inverse (neg_ne_zero.mp (Complex.slitPlane_ne_zero hw)),
    fun _ hw ↦ (exercise18_branch_continuous hw).continuousWithinAt⟩

noncomputable def exercise18ForwardMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -(2 * Real.pi / 3); 2 * Real.pi / 3, 0]
noncomputable def exercise18InverseMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 3 / (2 * Real.pi); -(3 / (2 * Real.pi)), 0]

theorem exercise18_forward_matrix : exercise18Jacobian exercise18A =
    exercise18ForwardMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exercise18Jacobian, exercise18A, exercise18ForwardMatrix]
  <;> ring

theorem exercise18_derivative_inverse : (2 * exercise18A)⁻¹ =
    -(3 / (2 * Real.pi) : ℝ) * Complex.I := by
  apply inv_eq_of_mul_eq_one_right
  apply Complex.ext <;>
    simp only [exercise18A, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  · norm_num
    field_simp
  · norm_num

noncomputable def exercise18InverseD : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ) (2 * exercise18A)⁻¹

theorem exercise18_inverse_hasFDerivAt :
    HasFDerivAt exercise18G exercise18InverseD exercise18B := by
  have hd : HasStrictDerivAt exercise18F (2 * exercise18A) exercise18A := by
    convert! hasStrictDerivAt_pow 2 exercise18A using 1
    simp
  have hn : 2 * exercise18A ≠ 0 := mul_ne_zero (by norm_num) (by
    intro h
    have hp := exercise18_a_upper
    simp [h] at hp)
  have hl : ∀ᶠ z in 𝓝 exercise18A, exercise18G (exercise18F z) = z := by
    filter_upwards [Complex.continuous_im.continuousAt.eventually
      (Ioi_mem_nhds exercise18_a_upper)] with z hz
    exact exercise18_left_inverse hz
  have hi := (hd.to_local_left_inverse hn hl).hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have he : exercise18InverseD =
      (ContinuousLinearMap.toSpanSingleton ℂ (2 * exercise18A)⁻¹).restrictScalars ℝ := by
    ext w
    simp [exercise18InverseD, mul_comm]
  rw [he]
  exact hi

theorem exercise18_inverse_matrix_action (w : ℂ) :
    exercise18InverseMatrix *ᵥ ![w.re, w.im] =
      ![(exercise18InverseD w).re, (exercise18InverseD w).im] := by
  change _ = ![((2 * exercise18A)⁻¹ * w).re, ((2 * exercise18A)⁻¹ * w).im]
  rw [exercise18_derivative_inverse]
  ext i
  fin_cases i <;> simp only [exercise18InverseMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  <;> norm_num

theorem exercise18_inverse_identity :
    exercise18InverseMatrix * exercise18ForwardMatrix = 1 ∧
      exercise18ForwardMatrix * exercise18InverseMatrix = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [exercise18ForwardMatrix, exercise18InverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Real.pi_ne_zero]

theorem exercise18_inverse_eq_matrix_inv :
    exercise18InverseMatrix = exercise18ForwardMatrix⁻¹ :=
  Matrix.inv_eq_left_inv exercise18_inverse_identity.1 |>.symm

/-- Non-axis horizontal lines map onto parabolas, with unrestricted imaginary coordinate. -/
theorem exercise18_horizontal_image {c : ℝ} (hc : c ≠ 0) :
    range (fun x : ℝ ↦ exercise18F ((x : ℂ) + c * Complex.I)) =
      {w : ℂ | w.re = (w.im / (2 * c)) ^ 2 - c ^ 2} := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    change (exercise18F ((x : ℂ) + c * Complex.I)).re =
      ((exercise18F ((x : ℂ) + c * Complex.I)).im / (2 * c)) ^ 2 - c ^ 2
    rw [exercise18_xy]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
    field_simp
  · intro hw
    change w.re = (w.im / (2 * c)) ^ 2 - c ^ 2 at hw
    refine ⟨w.im / (2 * c), ?_⟩
    dsimp only
    rw [exercise18_xy]
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero] using hw.symm
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
      field_simp

/-- Non-axis vertical lines map onto oppositely directed parabolas. -/
theorem exercise18_vertical_image {c : ℝ} (hc : c ≠ 0) :
    range (fun y : ℝ ↦ exercise18F ((c : ℂ) + y * Complex.I)) =
      {w : ℂ | w.re = c ^ 2 - (w.im / (2 * c)) ^ 2} := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    change (exercise18F ((c : ℂ) + y * Complex.I)).re =
      c ^ 2 - ((exercise18F ((c : ℂ) + y * Complex.I)).im / (2 * c)) ^ 2
    rw [exercise18_xy]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
    field_simp
  · intro hw
    change w.re = c ^ 2 - (w.im / (2 * c)) ^ 2 at hw
    refine ⟨w.im / (2 * c), ?_⟩
    dsimp only
    rw [exercise18_xy]
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
        Complex.ofReal_im, neg_zero, add_zero] using hw.symm
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
      field_simp

/-- The horizontal axis maps onto the nonnegative real half-axis. -/
theorem exercise18_real_axis_image : range (fun x : ℝ ↦ exercise18F (x : ℂ)) =
    {w : ℂ | w.im = 0 ∧ 0 ≤ w.re} := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨by rw [(exercise18_coordinates _).2]; simp,
      by rw [(exercise18_coordinates _).1]; simpa using sq_nonneg x⟩
  · rintro ⟨hi, hr⟩
    refine ⟨Real.sqrt w.re, ?_⟩
    apply Complex.ext
    · rw [(exercise18_coordinates _).1]; simp [Real.sq_sqrt hr]
    · rw [(exercise18_coordinates _).2]; simp [hi]

/-- The vertical axis maps onto the nonpositive real half-axis. -/
theorem exercise18_imaginary_axis_image : range (fun y : ℝ ↦ exercise18F (y * Complex.I)) =
    {w : ℂ | w.im = 0 ∧ w.re ≤ 0} := by
  ext w
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨by rw [(exercise18_coordinates _).2]; simp,
      by rw [(exercise18_coordinates _).1]; simpa using sq_nonneg y⟩
  · rintro ⟨hi, hr⟩
    refine ⟨Real.sqrt (-w.re), ?_⟩
    apply Complex.ext
    · rw [(exercise18_coordinates _).1]
      simp [Real.sq_sqrt (by linarith : 0 ≤ -w.re)]
    · rw [(exercise18_coordinates _).2]; simp [hi]

end Rudin.Chapter09
