module

public import Mathlib.Analysis.Complex.Basic

/-!
# R01E13: reverse triangle inequality

Source: Rudin, Exercise 1.13, book page 23 (PDF page 32).
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The absolute difference of the moduli is bounded by the modulus of the difference. -/
theorem exercise13 (x y : ℂ) : |‖x‖ - ‖y‖| ≤ ‖x - y‖ :=
  abs_norm_sub_norm_le x y

end Rudin.Chapter01
