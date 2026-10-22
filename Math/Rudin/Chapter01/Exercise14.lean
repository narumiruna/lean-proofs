module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic

/-!
# R01E14: a sum of squared moduli

Source: Rudin, Exercise 1.14, book page 23 (PDF page 32).
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The requested numerical value is `4` for every unit complex number. -/
theorem exercise14 (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 + z‖ ^ 2 + ‖1 - z‖ ^ 2 = 4 := by
  rw [parallelogram_law_with_norm ℂ (1 : ℂ) z, hz]
  norm_num

end Rudin.Chapter01
