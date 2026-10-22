module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter05

/-- Restricting a closed-interval derivative to the right at a point before its end.
No ambient derivative is required at either endpoint. -/
theorem exercise26_right_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {v : E} {a b x : ℝ}
    (h : HasDerivWithinAt f v (Icc a b) x) (hx : x ∈ Ico a b) :
    HasDerivWithinAt f v (Ici x) x := by
  apply h.mono_of_mem_nhdsWithin
  exact Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)

/-- The norm version also supplies the vector estimate used in Exercise 28.
The real constant can have any sign. -/
theorem exercise26_norm_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f v : ℝ → E} {a b A : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (v x) (Icc a b) x)
    (ha : f a = 0) (hbound : ∀ x ∈ Icc a b, ‖v x‖ ≤ A * ‖f x‖) :
    ∀ x ∈ Icc a b, f x = 0 := by
  apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (fun x hx => (hd x hx).continuousWithinAt)
    (fun x hx => exercise26_right_derivative (hd x (Ico_subset_Icc_self hx)) hx) ha
  exact fun x hx => hbound x (Ico_subset_Icc_self hx)

/-- R05E26: all derivatives, including endpoint derivatives, are relative to `[a,b]`. -/
theorem exercise26_zero_solution {f v : ℝ → ℝ} {a b A : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (v x) (Icc a b) x)
    (ha : f a = 0) (hbound : ∀ x ∈ Icc a b, |v x| ≤ A * |f x|) :
    ∀ x ∈ Icc a b, f x = 0 := by
  exact exercise26_norm_zero hd ha (by simpa only [Real.norm_eq_abs] using hbound)

end Rudin.Chapter05
