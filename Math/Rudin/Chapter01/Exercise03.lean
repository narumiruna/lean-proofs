module

public import Mathlib.Algebra.Field.Basic

/-!
# R01E03: multiplicative consequences of the field axioms

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 1.3, book page 22 (PDF page 31), and Proposition 1.15,
book page 7 (PDF page 16).
-/

@[expose] public section

namespace Rudin.Chapter01

variable {F : Type*} [Field F]

/-- Proposition 1.15(a): cancel a nonzero left factor. -/
theorem exercise03_a (x y z : F) (hx : x ≠ 0) (h : x * y = x * z) : y = z :=
  mul_left_cancel₀ hx h

/-- Proposition 1.15(b): uniqueness of the multiplicative identity. -/
theorem exercise03_b (x y : F) (hx : x ≠ 0) (h : x * y = x) : y = 1 :=
  exercise03_a x y 1 hx (h.trans (mul_one x).symm)

/-- Proposition 1.15(c): uniqueness of the reciprocal. -/
theorem exercise03_c (x y : F) (hx : x ≠ 0) (h : x * y = 1) : y = 1 / x := by
  apply exercise03_a x y (1 / x) hx
  simpa [hx] using h

/-- Proposition 1.15(d): the reciprocal of the reciprocal. -/
theorem exercise03_d (x : F) (hx : x ≠ 0) : 1 / (1 / x) = x := by
  symm
  apply exercise03_c (1 / x) x (one_div_ne_zero hx)
  simp [hx]

end Rudin.Chapter01
