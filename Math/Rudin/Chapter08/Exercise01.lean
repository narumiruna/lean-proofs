module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-! # Chapter 8, Exercise 1
Source: book page 196, PDF page 205. Every successive derivative exists.
-/

@[expose] public section

open scoped ContDiff

namespace Rudin.Chapter08

noncomputable def exercise01_function (x : ℝ) : ℝ := expNegInvGlue (x ^ 2)

theorem exercise01_formula (x : ℝ) :
    exercise01_function x = if x = 0 then 0 else Real.exp (-1 / x ^ 2) := by
  by_cases hx : x = 0
  · simp [exercise01_function, hx]
  · simp [exercise01_function, expNegInvGlue, hx, not_le.mpr (sq_pos_of_ne_zero hx), div_eq_mul_inv]

private theorem glue_polynomial_flat (n : ℕ) (p : Polynomial ℝ) :
    iteratedDeriv n (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) 0 = 0 := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) =
        fun x ↦ (Polynomial.X ^ 2 * (p - Polynomial.derivative p)).eval x⁻¹ *
          expNegInvGlue x := by
      funext x
      exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p x).deriv
    rw [hd]
    exact ih _

private theorem glue_flat (n : ℕ) : iteratedDeriv n expNegInvGlue 0 = 0 := by
  simpa using glue_polynomial_flat n 1

theorem exercise01_smooth (n : ℕ) : ContDiff ℝ n exercise01_function :=
  expNegInvGlue.contDiff.comp (contDiff_id.pow 2)

theorem exercise01_flatness (n : ℕ) : iteratedDeriv n exercise01_function 0 = 0 := by
  change iteratedDeriv n (expNegInvGlue ∘ fun x : ℝ ↦ x ^ 2) 0 = 0
  have h := iteratedDeriv_comp_eq_sum_orderedFinpartition (x := (0 : ℝ)) (i := n)
    (expNegInvGlue.contDiff (n := n)).contDiffAt
    ((contDiff_id.pow 2 : ContDiff ℝ n (fun x : ℝ ↦ x ^ 2)).contDiffAt)
    le_rfl
  simpa [Function.comp_def, glue_flat] using h

theorem exercise01_all_derivatives (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n exercise01_function)
      (iteratedDeriv (n + 1) exercise01_function x) x := by
  rw [iteratedDeriv_succ]
  exact ((exercise01_smooth (n + 1)).differentiable_iteratedDeriv' n x).hasDerivAt

theorem exercise01_derivatives_at_zero (n : ℕ) :
    HasDerivAt (iteratedDeriv n exercise01_function) 0 0 := by
  simpa [exercise01_flatness] using exercise01_all_derivatives n 0

end Rudin.Chapter08
