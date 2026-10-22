module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-! # R01E08
Rudin, book page 22 (PDF page 31): no order is compatible with the usual complex field.
The field operations remain fixed; the linear order is universally quantified.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Every linear order on the usual complex field fails the ordered-ring axioms. -/
theorem exercise08 (order : LinearOrder ℂ) :
    letI := order
    ¬ IsStrictOrderedRing ℂ := by
  let := order
  intro h
  let := h
  have hs : (0 : ℂ) ≤ Complex.I ^ 2 := sq_nonneg _
  rw [Complex.I_sq] at hs
  exact (not_le_of_gt (neg_one_lt_zero (R := ℂ))) hs

end Rudin.Chapter01
