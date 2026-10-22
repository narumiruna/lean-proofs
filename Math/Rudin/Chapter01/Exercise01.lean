module

public import Mathlib.NumberTheory.Real.Irrational

/-!
# R01E01: rational and irrational arithmetic

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 1.1, book page 21 (PDF page 30).

The rational number is represented by `r : ℚ` and its canonical cast to `ℝ`.
Both requested conclusions use the same nonzero rational and irrational real.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Adding or multiplying by a nonzero rational preserves irrationality. -/
theorem exercise01 (r : ℚ) (hr : r ≠ 0) (x : ℝ) (hx : Irrational x) :
    Irrational ((r : ℝ) + x) ∧ Irrational ((r : ℝ) * x) :=
  ⟨hx.ratCast_add r, hx.ratCast_mul hr⟩

end Rudin.Chapter01
