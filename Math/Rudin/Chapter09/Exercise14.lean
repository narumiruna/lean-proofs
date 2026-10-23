module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-! # R09E14: a homogeneous function without a total derivative
Source: book page 240, PDF page 249.
The rational formula is also zero at the origin under totalized division;
`exercise14_value_zero` checks the prescribed value explicitly.
-/
@[expose] public section
namespace Rudin.Chapter09
open Filter Topology

noncomputable def exercise14Function (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 ^ 3 / (p 0 ^ 2 + p 1 ^ 2)

@[simp] theorem exercise14_value_zero : exercise14Function 0 = 0 := by
  simp [exercise14Function]

theorem exercise14_denominator {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by
  intro h
  have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0)]
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0)]
  apply hp
  ext i
  fin_cases i <;> simp_all

theorem exercise14_homogeneous (s : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    exercise14Function (s • p) = s * exercise14Function p := by
  simp only [exercise14Function, PiLp.smul_apply, smul_eq_mul]
  by_cases hs : s = 0
  · simp [hs]
  by_cases hp : p 0 ^ 2 + p 1 ^ 2 = 0
  · have h : (s * p 0) ^ 2 + (s * p 1) ^ 2 = 0 := by
      calc
        _ = s ^ 2 * (p 0 ^ 2 + p 1 ^ 2) := by ring
        _ = 0 := by rw [hp, mul_zero]
    simp [hp, h]
  · have h : (s * p 0) ^ 2 + (s * p 1) ^ 2 ≠ 0 := by
      have he : (s * p 0) ^ 2 + (s * p 1) ^ 2 = s ^ 2 * (p 0 ^ 2 + p 1 ^ 2) := by ring
      rw [he]; exact mul_ne_zero (pow_ne_zero _ hs) hp
    field_simp

theorem exercise14_bound (p : EuclideanSpace ℝ (Fin 2)) :
    |exercise14Function p| ≤ |p 0| := by
  by_cases hp : p = 0
  · simp [hp]
  have hd : 0 < p 0 ^ 2 + p 1 ^ 2 :=
    lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm (exercise14_denominator hp))
  rw [exercise14Function, abs_div, abs_of_pos hd, div_le_iff₀ hd, abs_pow]
  have hx : |p 0| ^ 2 = p 0 ^ 2 := sq_abs _
  calc
    |p 0| ^ 3 = |p 0| * p 0 ^ 2 := by rw [← hx]; ring
    _ ≤ |p 0| * (p 0 ^ 2 + p 1 ^ 2) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (abs_nonneg _)

theorem exercise14_continuous : Continuous exercise14Function := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    change Tendsto exercise14Function (𝓝 0) (𝓝 (exercise14Function 0))
    rw [exercise14_value_zero]
    apply squeeze_zero_norm (fun q => exercise14_bound q)
    convert ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).norm.continuousAt :
      ContinuousAt (fun q : EuclideanSpace ℝ (Fin 2) => ‖q 0‖) 0).tendsto using 1
    simp
  · exact ((PiLp.continuous_apply 2 _ 0).pow 3).continuousAt.div
      (((PiLp.continuous_apply 2 _ 0).pow 2).add
        ((PiLp.continuous_apply 2 _ 1).pow 2)).continuousAt (exercise14_denominator hp)

/-- At every zero of any differentiable curve, including stationary zeros. -/
theorem exercise14_curve_at_zero {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ} (hγ : HasDerivAt γ v a) (hz : γ a = 0) :
    HasDerivAt (fun t => exercise14Function (γ t)) (exercise14Function v) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := exercise14_continuous.continuousAt.tendsto.comp hγ.tendsto_slope
  convert h using 1
  ext t
  simp [slope_def_module, hz, exercise14_homogeneous]

/-- All directions, not only unit directions, have genuine directional derivatives. -/
theorem exercise14_directional (u : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => exercise14Function (t • u)) (exercise14Function u) 0 := by
  simpa using exercise14_curve_at_zero ((hasDerivAt_id (0 : ℝ)).smul_const u) (by simp)

noncomputable def exercise14A (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 ^ 2 * (p 0 ^ 2 + 3 * p 1 ^ 2) / (p 0 ^ 2 + p 1 ^ 2) ^ 2

noncomputable def exercise14B (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  -(2 * p 0 ^ 3 * p 1) / (p 0 ^ 2 + p 1 ^ 2) ^ 2

theorem exercise14_curve_off_zero {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    {v : EuclideanSpace ℝ (Fin 2)} {a : ℝ} (hγ : HasDerivAt γ v a) (hz : γ a ≠ 0) :
    HasDerivAt (fun t => exercise14Function (γ t))
      (exercise14A (γ a) * v 0 + exercise14B (γ a) * v 1) a := by
  have h0 := (PiLp.hasFDerivAt_apply 2 (γ a) 0).comp_hasDerivAt a hγ
  have h1 := (PiLp.hasFDerivAt_apply 2 (γ a) 1).comp_hasDerivAt a hγ
  convert (h0.pow 3).div ((h0.pow 2).add (h1.pow 2)) (exercise14_denominator hz) using 1 <;>
    simp [exercise14Function, exercise14A, exercise14B, PiLp.proj_apply, Function.comp_def] <;>
    first | (solve | ring) | (funext t; rfl)

/-- The source assumptions at parameter zero are unnecessary. This covers every
later visit to zero, with either zero or nonzero velocity. -/
theorem exercise14_curve_differentiable {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : Differentiable ℝ γ) : Differentiable ℝ (fun t => exercise14Function (γ t)) := by
  intro a
  by_cases hz : γ a = 0
  · exact (exercise14_curve_at_zero (hγ a).hasDerivAt hz).differentiableAt
  · exact (exercise14_curve_off_zero (hγ a).hasDerivAt hz).differentiableAt

theorem exercise14_unit_directional (u : EuclideanSpace ℝ (Fin 2)) (hu : ‖u‖ = 1) :
    HasDerivAt (fun t : ℝ => exercise14Function (t • u)) (exercise14Function u) 0 ∧
    |exercise14Function u| ≤ 1 := by
  refine ⟨exercise14_directional u, (exercise14_bound u).trans ?_⟩
  simpa [hu] using PiLp.norm_apply_le u 0

theorem exercise14_A_bound (p : EuclideanSpace ℝ (Fin 2)) : |exercise14A p| ≤ 3 := by
  by_cases hp : p = 0
  · simp [exercise14A, hp]
  have hd : 0 < (p 0 ^ 2 + p 1 ^ 2) ^ 2 := sq_pos_of_ne_zero (exercise14_denominator hp)
  rw [exercise14A, abs_div, abs_of_pos hd,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (by positivity)), div_le_iff₀ hd]
  nlinarith [sq_nonneg (p 0 ^ 2), sq_nonneg (p 1 ^ 2), mul_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]

theorem exercise14_B_bound (p : EuclideanSpace ℝ (Fin 2)) : |exercise14B p| ≤ 2 := by
  by_cases hp : p = 0
  · simp [exercise14B, hp]
  have hd : 0 < (p 0 ^ 2 + p 1 ^ 2) ^ 2 := sq_pos_of_ne_zero (exercise14_denominator hp)
  have hxy : |p 0| * |p 1| ≤ p 0 ^ 2 + p 1 ^ 2 := by
    nlinarith [sq_nonneg (|p 0| - |p 1|), sq_abs (p 0), sq_abs (p 1), sq_nonneg (p 0), sq_nonneg (p 1)]
  have h := mul_le_mul_of_nonneg_left hxy (sq_nonneg (p 0))
  rw [exercise14B, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  simp only [abs_neg, abs_mul, abs_pow]
  norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have he : |p 0| ^ 3 * |p 1| = p 0 ^ 2 * (|p 0| * |p 1|) := by
    rw [← sq_abs (p 0)]; ring
  nlinarith [sq_nonneg (p 1 ^ 2), mul_nonneg (sq_nonneg (p 0)) (sq_nonneg (p 1))]

def exercise14Basis (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (Pi.single i 1)

/-- Coordinate partials exist at every point, with uniform bounds 3 and 2. -/
theorem exercise14_partials (p : EuclideanSpace ℝ (Fin 2)) :
    ∃ d₀ d₁ : ℝ,
      HasDerivAt (fun t : ℝ => exercise14Function (p + t • exercise14Basis 0)) d₀ 0 ∧
      HasDerivAt (fun t : ℝ => exercise14Function (p + t • exercise14Basis 1)) d₁ 0 ∧
      |d₀| ≤ 3 ∧ |d₁| ≤ 2 := by
  have hc (i : Fin 2) : HasDerivAt (fun t : ℝ => p + t • exercise14Basis i)
      (exercise14Basis i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (exercise14Basis i)).const_add p
  by_cases hp : p = 0
  · subst p
    refine ⟨1, 0, ?_, ?_, by norm_num, by norm_num⟩
    · simpa [exercise14Function, exercise14Basis] using
        exercise14_curve_at_zero (hc 0) (by simp)
    · simpa [exercise14Function, exercise14Basis] using
        exercise14_curve_at_zero (hc 1) (by simp)
  · refine ⟨exercise14A p, exercise14B p, ?_, ?_, exercise14_A_bound p, exercise14_B_bound p⟩
    · simpa [exercise14Basis] using exercise14_curve_off_zero (hc 0) (by simpa using hp)
    · simpa [exercise14Basis] using exercise14_curve_off_zero (hc 1) (by simpa using hp)

theorem exercise14_not_differentiable : ¬ DifferentiableAt ℝ exercise14Function 0 := by
  intro h
  let L := fderiv ℝ exercise14Function 0
  have he (u : EuclideanSpace ℝ (Fin 2)) : L u = exercise14Function u := by
    have hc : HasDerivAt (fun t : ℝ => t • u) u 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
    have hf : HasFDerivAt exercise14Function L ((fun t : ℝ => t • u) 0) := by
      simpa [L] using h.hasFDerivAt
    have hh := hf.comp_hasDerivAt 0 hc
    simpa [L] using hh.unique (exercise14_directional u)
  have hadd := L.map_add (exercise14Basis 0) (exercise14Basis 1)
  rw [he, he, he] at hadd
  norm_num [exercise14Function, exercise14Basis, PiLp.add_apply] at hadd

theorem exercise14_coefficients_scale (p : EuclideanSpace ℝ (Fin 2))
    {s : ℝ} (hs : s ≠ 0) :
    exercise14A (s • p) = exercise14A p ∧ exercise14B (s • p) = exercise14B p := by
  by_cases hp : p = 0
  · simp [hp, exercise14A, exercise14B]
  have hd := exercise14_denominator hp
  have hds : (s * p 0) ^ 2 + (s * p 1) ^ 2 ≠ 0 := by
    have he : (s * p 0) ^ 2 + (s * p 1) ^ 2 = s ^ 2 * (p 0 ^ 2 + p 1 ^ 2) := by ring
    rw [he]; exact mul_ne_zero (pow_ne_zero _ hs) hd
  constructor <;> simp only [exercise14A, exercise14B, PiLp.smul_apply, smul_eq_mul] <;>
    field_simp

theorem exercise14_euler (p : EuclideanSpace ℝ (Fin 2)) :
    exercise14A p * p 0 + exercise14B p * p 1 = exercise14Function p := by
  by_cases hp : p = 0
  · simp [hp, exercise14A, exercise14B]
  have hd := exercise14_denominator hp
  dsimp [exercise14A, exercise14B, exercise14Function]
  field_simp
  ring

theorem exercise14_coefficients_continuous {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    ContinuousAt exercise14A p ∧ ContinuousAt exercise14B p := by
  have h0 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt (x := p)
  have h1 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt (x := p)
  have hd := pow_ne_zero 2 (exercise14_denominator hp)
  exact ⟨((h0.pow 2).mul ((h0.pow 2).add ((h1.pow 2).const_mul 3))).div
      (((h0.pow 2).add (h1.pow 2)).pow 2) hd,
    ((((h0.pow 3).const_mul 2).mul h1).neg).div
      (((h0.pow 2).add (h1.pow 2)).pow 2) hd⟩

theorem exercise14_curve_deriv_bound {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : Differentiable ℝ γ) (t : ℝ) :
    |deriv (fun t => exercise14Function (γ t)) t| ≤
      3 * |deriv γ t 0| + 2 * |deriv γ t 1| := by
  by_cases hz : γ t = 0
  · rw [(exercise14_curve_at_zero (hγ t).hasDerivAt hz).deriv]
    exact (exercise14_bound _).trans (by nlinarith [abs_nonneg (deriv γ t 0), abs_nonneg (deriv γ t 1)])
  · rw [(exercise14_curve_off_zero (hγ t).hasDerivAt hz).deriv]
    calc
      _ ≤ |exercise14A (γ t) * deriv γ t 0| + |exercise14B (γ t) * deriv γ t 1| := abs_add_le _ _
      _ ≤ _ := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (exercise14_A_bound _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (exercise14_B_bound _) (abs_nonneg _))

/-- Continuous velocity gives a continuous derivative of the composition,
including repeated and stationary visits to the origin. -/
theorem exercise14_curve_C1 {γ : ℝ → EuclideanSpace ℝ (Fin 2)}
    (hγ : ContDiff ℝ 1 γ) : ContDiff ℝ 1 (fun t => exercise14Function (γ t)) := by
  classical
  have hd := hγ.differentiable (by norm_num)
  have hv := hγ.continuous_deriv (by norm_num)
  rw [contDiff_one_iff_deriv]
  refine ⟨exercise14_curve_differentiable hd, continuous_iff_continuousAt.mpr ?_⟩
  intro a
  have hv0 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp hv
  have hv1 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp hv
  by_cases hz : γ a = 0
  · by_cases hva : deriv γ a = 0
    · have he : deriv (fun t => exercise14Function (γ t)) a = 0 := by
        rw [(exercise14_curve_at_zero (hd a).hasDerivAt hz).deriv, hva, exercise14_value_zero]
      change Tendsto _ (𝓝 a) (𝓝 _)
      rw [he]
      apply squeeze_zero_norm (exercise14_curve_deriv_bound hd)
      convert ((hv0.abs.const_mul 3).add (hv1.abs.const_mul 2)).continuousAt.tendsto using 1 <;>
        simp [hva]
      rfl
    · let w : ℝ → EuclideanSpace ℝ (Fin 2) := Function.update (slope γ a) a (deriv γ a)
      have hwval : w a = deriv γ a := by simp [w]
      have hw : ContinuousAt w a := by
        exact continuousAt_update_same.mpr (hd a).hasDerivAt.tendsto_slope
      have hwne : ∀ᶠ t in 𝓝 a, w t ≠ 0 := hw.eventually_ne (by simpa [hwval] using hva)
      have hc := exercise14_coefficients_continuous (p := w a) (by simpa [hwval] using hva)
      have hmodel : ContinuousAt (fun t => exercise14A (w t) * deriv γ t 0 +
          exercise14B (w t) * deriv γ t 1) a :=
        ((hc.1.comp hw).mul hv0.continuousAt).add ((hc.2.comp hw).mul hv1.continuousAt)
      apply hmodel.congr_of_eventuallyEq
      filter_upwards [hwne] with t ht
      by_cases hta : t = a
      · subst t
        rw [(exercise14_curve_at_zero (hd a).hasDerivAt hz).deriv, hwval, exercise14_euler]
      · have hs : t - a ≠ 0 := sub_ne_zero.mpr hta
        have hwform : w t = (t - a)⁻¹ • γ t := by
          simp [w, Function.update_of_ne hta, slope_def_module, hz]
        have hγform : γ t = (t - a) • w t := by
          rw [hwform, smul_smul, mul_inv_cancel₀ hs, one_smul]
        have hγne : γ t ≠ 0 := by rw [hγform]; exact smul_ne_zero hs ht
        rw [(exercise14_curve_off_zero (hd t).hasDerivAt hγne).deriv, hγform]
        rw [(exercise14_coefficients_scale (w t) hs).1, (exercise14_coefficients_scale (w t) hs).2]
  · have hc := exercise14_coefficients_continuous hz
    have hmodel : ContinuousAt (fun t => exercise14A (γ t) * deriv γ t 0 +
        exercise14B (γ t) * deriv γ t 1) a :=
      ((hc.1.comp (hd a).continuousAt).mul hv0.continuousAt).add
        ((hc.2.comp (hd a).continuousAt).mul hv1.continuousAt)
    apply hmodel.congr_of_eventuallyEq
    filter_upwards [(hd a).continuousAt.eventually_ne hz] with t ht
    exact (exercise14_curve_off_zero (hd t).hasDerivAt ht).deriv

end Rudin.Chapter09
