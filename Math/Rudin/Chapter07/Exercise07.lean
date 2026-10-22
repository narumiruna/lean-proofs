module

public import Mathlib

/-! # Chapter 7, Exercise 7
The positive source index is `n + 1`. The limit on the whole real line is zero.
Source: book page 166, PDF page 175.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter07

noncomputable section

def exercise07Fn (n : ℕ) (x : ℝ) : ℝ := x / (1 + (n + 1 : ℝ) * x ^ 2)

def exercise07Derivative (n : ℕ) (x : ℝ) : ℝ :=
  (1 - (n + 1 : ℝ) * x ^ 2) / (1 + (n + 1 : ℝ) * x ^ 2) ^ 2

theorem exercise07_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (exercise07Fn n) (exercise07Derivative n x) x := by
  have hd : 1 + (n + 1 : ℝ) * x ^ 2 ≠ 0 := by positivity
  change HasDerivAt (fun y : ℝ => y / (1 + (n + 1 : ℝ) * y ^ 2)) _ x
  convert (hasDerivAt_id x).div
    (((hasDerivAt_id x).pow 2).const_mul (n + 1 : ℝ) |>.const_add 1) hd using 1
  · rfl
  · dsimp [exercise07Derivative]
    ring

theorem exercise07_norm_bound (n : ℕ) (x : ℝ) :
    ‖exercise07Fn n x‖ ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hs := Real.sqrt_pos.mpr hn
  have he := Real.sq_sqrt hn.le
  rw [exercise07Fn, norm_div, Real.norm_eq_abs,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (n + 1 : ℝ) * x ^ 2)]
  apply (div_le_div_iff₀ (by positivity) hs).mpr
  nlinarith [sq_nonneg (Real.sqrt (n + 1 : ℝ) * |x| - 1), sq_abs x]

/-- Uniform convergence on all of `ℝ`, not just on bounded intervals. -/
theorem exercise07_uniform_limit :
    TendstoUniformly exercise07Fn (fun _ => 0) atTop := by
  have ht : Tendsto (fun n : ℕ => 1 / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ) |>.atTop_add tendsto_const_nhds))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x
  simpa only [dist_zero_left] using (exercise07_norm_bound n x).trans_lt hn

theorem exercise07_derivative_bound (n : ℕ) (x : ℝ) :
    ‖exercise07Derivative n x‖ ≤ 1 / (1 + (n + 1 : ℝ) * x ^ 2) := by
  have ht : 0 ≤ (n + 1 : ℝ) * x ^ 2 := by positivity
  have hd : 0 < 1 + (n + 1 : ℝ) * x ^ 2 := by positivity
  rw [exercise07Derivative, norm_div, Real.norm_eq_abs,
    Real.norm_of_nonneg (sq_nonneg _)]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd).mpr
  have ha : |1 - (n + 1 : ℝ) * x ^ 2| ≤ 1 + (n + 1 : ℝ) * x ^ 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [mul_le_mul_of_nonneg_right ha hd.le]

/-- The derivatives are genuine derivatives, and their limit agrees off zero. -/
theorem exercise07_derivative_nonzero {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x ∧
    Tendsto (fun n => deriv (exercise07Fn n) x) atTop (𝓝 0) := by
  refine ⟨hasDerivAt_const x 0, ?_⟩
  have ht : Tendsto (fun n : ℕ => 1 / (1 + (n + 1 : ℝ) * x ^ 2)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_left _ 1
      (((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds).atTop_mul_const
        (sq_pos_of_ne_zero hx))
  apply squeeze_zero_norm (fun n => ?_) ht
  rw [(exercise07_hasDerivAt n x).deriv]
  exact exercise07_derivative_bound n x

/-- At zero every derivative is one, whereas the derivative of the limit is zero. -/
theorem exercise07_derivative_zero :
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 ∧
    (∀ n, HasDerivAt (exercise07Fn n) 1 0) ∧
    Tendsto (fun n => deriv (exercise07Fn n) 0) atTop (𝓝 1) ∧
    deriv (fun _ : ℝ => (0 : ℝ)) 0 ≠ (1 : ℝ) := by
  refine ⟨hasDerivAt_const 0 0, ?_, ?_, by simp⟩
  · intro n
    simpa [exercise07Derivative] using exercise07_hasDerivAt n 0
  · convert (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)) using 1
    ext n
    simpa [exercise07Derivative] using (exercise07_hasDerivAt n 0).deriv

end

end Rudin.Chapter07
