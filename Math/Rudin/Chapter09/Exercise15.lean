module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Tactic

/-! # R09E15: strict minima on lines do not give a planar minimum
Source: book pages 240–241, PDF pages 249–250. The literal rational term is
retained. Its totalized value at zero agrees with the assigned value zero.
-/
@[expose] public section
namespace Rudin.Chapter09
open Filter Topology

def exercise15Point (x y : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, y]

noncomputable def exercise15Function (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 ^ 2 + p 1 ^ 2 - 2 * p 0 ^ 2 * p 1 -
    4 * p 0 ^ 6 * p 1 ^ 2 / (p 0 ^ 4 + p 1 ^ 2) ^ 2

@[simp] theorem exercise15_zero : exercise15Function 0 = 0 := by simp [exercise15Function]

theorem exercise15_inequality (x y : ℝ) : 4 * x ^ 4 * y ^ 2 ≤ (x ^ 4 + y ^ 2) ^ 2 := by
  nlinarith [sq_nonneg (x ^ 4 - y ^ 2)]

theorem exercise15_denominator {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    p 0 ^ 4 + p 1 ^ 2 ≠ 0 := by
  intro h
  have h0 : p 0 = 0 := by
    have hz : p 0 ^ 4 = 0 := by nlinarith [sq_nonneg (p 0 ^ 2), sq_nonneg (p 1)]
    exact (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hz
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0 ^ 2), sq_nonneg (p 1)]
  apply hp
  ext i
  fin_cases i <;> simp_all

/-- The singular rational term is nonnegative and is bounded by x². -/
theorem exercise15_rational_bound (p : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ 4 * p 0 ^ 6 * p 1 ^ 2 / (p 0 ^ 4 + p 1 ^ 2) ^ 2 ∧
    4 * p 0 ^ 6 * p 1 ^ 2 / (p 0 ^ 4 + p 1 ^ 2) ^ 2 ≤ p 0 ^ 2 := by
  refine ⟨by positivity, ?_⟩
  by_cases hp : p = 0
  · simp [hp]
  rw [div_le_iff₀ (sq_pos_of_ne_zero (exercise15_denominator hp))]
  have h := mul_le_mul_of_nonneg_left (exercise15_inequality (p 0) (p 1)) (sq_nonneg (p 0))
  nlinarith

theorem exercise15_continuous : Continuous exercise15Function := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have h0 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt (x := p)
  have h1 := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt (x := p)
  have hpoly := ((h0.pow 2).add (h1.pow 2)).sub (((h0.pow 2).const_mul 2).mul h1)
  apply hpoly.sub
  by_cases hp : p = 0
  · subst p
    have hb := squeeze_zero (fun q => (exercise15_rational_bound q).1)
      (fun q => (exercise15_rational_bound q).2)
      (show Tendsto (fun q : EuclideanSpace ℝ (Fin 2) => q 0 ^ 2) (𝓝 0) (𝓝 0) from by
        convert (h0.pow 2).tendsto using 1
        simp)
    change Tendsto _ _ _
    convert hb using 1
    simp
  · exact ((((h0.pow 6).const_mul 4).mul (h1.pow 2)).div
      (((h0.pow 4).add (h1.pow 2)).pow 2) (pow_ne_zero _ (exercise15_denominator hp)))

theorem exercise15_curved_values (x : ℝ) :
    exercise15Function (exercise15Point x (x ^ 2)) = -x ^ 4 := by
  dsimp [exercise15Function, exercise15Point]
  by_cases hx : x = 0
  · simp [hx]
  field_simp
  ring

/-- Each unit line has a smooth factor with value one at zero. -/
theorem exercise15_line_factor (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    ∃ k : ℝ → ℝ, ContDiff ℝ 2 k ∧ k 0 = 1 ∧
      ∀ t, exercise15Function (exercise15Point (t * a) (t * b)) = t ^ 2 * k t := by
  by_cases hb : b = 0
  · refine ⟨fun _ => 1, contDiff_const, rfl, ?_⟩
    intro t
    have ha : a ^ 2 = 1 := by simpa [hb] using hu
    simp [exercise15Function, exercise15Point, hb, mul_pow, ha]
  · let k : ℝ → ℝ := fun t => 1 - 2 * a ^ 2 * b * t -
        4 * a ^ 6 * b ^ 2 * t ^ 2 / (a ^ 4 * t ^ 2 + b ^ 2) ^ 2
    have hd (t : ℝ) : a ^ 4 * t ^ 2 + b ^ 2 ≠ 0 := by
      have : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      positivity
    have hk : ContDiff ℝ 2 k := by
      dsimp [k]
      apply ContDiff.sub
      · fun_prop
      · apply ContDiff.div
        · fun_prop
        · fun_prop
        · intro t; exact pow_ne_zero _ (hd t)
    refine ⟨k, hk, by simp [k], ?_⟩
    intro t
    by_cases ht : t = 0
    · simp [ht, exercise15Function, exercise15Point]
    have hdt : (t * a) ^ 4 + (t * b) ^ 2 ≠ 0 := by
      have : 0 < (t * b) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero ht hb)
      positivity
    dsimp [exercise15Function, exercise15Point, k]
    have h := hd t
    field_simp
    nlinarith [hu]

/-- A genuine derivative jet, with first derivatives at every parameter. -/
theorem exercise15_factor_jet {k : ℝ → ℝ} (hk : ContDiff ℝ 2 k) (hk0 : k 0 = 1) :
    (∀ t, HasDerivAt (fun s => s ^ 2 * k s)
      (2 * t * k t + t ^ 2 * deriv k t) t) ∧
    HasDerivAt (fun t => 2 * t * k t + t ^ 2 * deriv k t) 2 0 := by
  have hd := hk.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv k) := by
    exact hk.differentiable_deriv_two
  constructor
  · intro t
    have hs : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;> (first | rfl | simp)
    exact hs.fun_mul (hd t).hasDerivAt
  · have hs : HasDerivAt (fun s : ℝ => s ^ 2) 0 0 := by
      convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> (first | rfl | simp)
    have hl : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
      convert (hasDerivAt_id (0 : ℝ)).const_mul 2 using 1 <;> simp
    exact ((hl.fun_mul (hd 0).hasDerivAt).fun_add
      (hs.fun_mul (hdd 0).hasDerivAt)).congr_deriv (by simp [hk0])

/-- All real unit directions; hence the full inclusive angle interval is covered. -/
theorem exercise15_line_derivatives (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    let g : ℝ → ℝ := fun t => exercise15Function (exercise15Point (t * a) (t * b))
    g 0 = 0 ∧ (∀ t, DifferentiableAt ℝ g t) ∧ HasDerivAt g 0 0 ∧
      HasDerivAt (deriv g) 2 0 := by
  obtain ⟨k, hk, hk0, he⟩ := exercise15_line_factor a b hu
  have hfun : (fun t => exercise15Function (exercise15Point (t * a) (t * b))) =
      fun t => t ^ 2 * k t := funext he
  dsimp only
  rw [hfun]
  obtain ⟨hj, hj2⟩ := exercise15_factor_jet hk hk0
  refine ⟨by simp [exercise15Function, exercise15Point], fun t => (hj t).differentiableAt, ?_, ?_⟩
  · simpa using hj 0
  · have he' : deriv (fun t => t ^ 2 * k t) = fun t => 2 * t * k t + t ^ 2 * deriv k t :=
      funext (fun t => (hj t).deriv)
    rw [he']; exact hj2

theorem exercise15_angles (θ : ℝ) :
    let g : ℝ → ℝ := fun t => exercise15Function
      (exercise15Point (t * Real.cos θ) (t * Real.sin θ))
    g 0 = 0 ∧ (∀ t, DifferentiableAt ℝ g t) ∧ HasDerivAt g 0 0 ∧
      HasDerivAt (deriv g) 2 0 :=
  exercise15_line_derivatives _ _ (Real.cos_sq_add_sin_sq θ)

/-- Strict local minimality is expressed on the punctured neighborhood. -/
theorem exercise15_line_strict_minimum (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), exercise15Function 0 <
      exercise15Function (exercise15Point (t * a) (t * b)) := by
  obtain ⟨k, hk, hk0, he⟩ := exercise15_line_factor a b hu
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < k t :=
    hk.continuous.continuousAt.eventually (lt_mem_nhds (by rw [hk0]; norm_num))
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
  rw [exercise15_zero, he]
  exact mul_pos (sq_pos_of_ne_zero hne) ht

theorem exercise15_angle_strict_minimum (θ : ℝ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), exercise15Function 0 < exercise15Function
      (exercise15Point (t * Real.cos θ) (t * Real.sin θ)) :=
  exercise15_line_strict_minimum _ _ (Real.cos_sq_add_sin_sq θ)

/-- Every neighborhood contains a point on the parabola with smaller value. -/
theorem exercise15_no_minimum : ¬ IsLocalMin exercise15Function 0 := by
  intro h
  have hc : Continuous (fun t : ℝ => exercise15Point t (t ^ 2)) := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hc0 : Tendsto (fun t : ℝ => exercise15Point t (t ^ 2)) (𝓝 0) (𝓝 0) := by
    convert hc.continuousAt.tendsto (x := 0) using 1
    congr 1
    ext i
    fin_cases i <;> simp [exercise15Point]
  have hh : ∀ᶠ t : ℝ in 𝓝 0, (0 : ℝ) ≤ -t ^ 4 := by
    have hh := hc0.eventually h
    simpa only [exercise15_zero, exercise15_curved_values] using hh
  have hboth : ∀ᶠ t : ℝ in 𝓝[≠] 0, (0 : ℝ) ≤ -t ^ 4 ∧ t ≠ 0 :=
    (hh.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨t, ht, htne⟩ := hboth.exists
  have hp := sq_pos_of_ne_zero (pow_ne_zero 2 htne)
  nlinarith

end Rudin.Chapter09
