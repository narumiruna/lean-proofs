module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Chapter 8, Exercise 7
Source: book page 197, PDF page 206. Both inequalities are strict.
-/

@[expose] public section

namespace Rudin.Chapter08

theorem exercise07_sine_ratio {x : ℝ} (hx : 0 < x) (hπ : x < Real.pi / 2) :
    2 / Real.pi < Real.sin x / x ∧ Real.sin x / x < 1 := by
  constructor
  · exact (lt_div_iff₀ hx).mpr (Real.mul_lt_sin hx hπ)
  · exact (div_lt_iff₀ hx).mpr (by simpa using Real.sin_lt hx)

end Rudin.Chapter08
