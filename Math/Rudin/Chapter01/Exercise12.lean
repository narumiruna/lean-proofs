module

public import Mathlib.Analysis.Complex.Basic

/-!
# R01E12: finite triangle inequality

Source: Rudin, Exercise 1.12, book page 23 (PDF page 32).
`Fin n` reindexes the source's `1, …, n`; the result also covers the empty sum.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The triangle inequality for any finite list of complex numbers. -/
theorem exercise12 {n : ℕ} (z : Fin n → ℂ) :
    ‖∑ j, z j‖ ≤ ∑ j, ‖z j‖ :=
  norm_sum_le _ _

end Rudin.Chapter01
