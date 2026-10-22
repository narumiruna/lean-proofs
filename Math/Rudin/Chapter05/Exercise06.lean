module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter05

/-- Exercise 6: the secant slope from the endpoint is nondecreasing.
Continuity, but no derivative, is required at zero. -/
theorem exercise06_quotient_monotonicity (f : ℝ → ℝ)
    (hc : ContinuousOn f (Ici 0))
    (hd : ∀ x > 0, DifferentiableAt ℝ f x)
    (hzero : f 0 = 0) (hm : MonotoneOn (deriv f) (Ioi 0)) :
    MonotoneOn (fun x => f x / x) (Ioi 0) := by
  have hconv : ConvexOn ℝ (Ici 0) f := by
    apply MonotoneOn.convexOn_of_deriv (convex_Ici (0 : ℝ)) hc
    · rw [interior_Ici]
      exact fun x hx => (hd x hx).differentiableWithinAt
    · simpa only [interior_Ici] using hm
  intro x hx y hy hxy
  have hs := hconv.monotoneOn_slope_gt (show (0 : ℝ) ∈ Ici 0 by simp)
    ⟨hx.le, hx⟩ ⟨hy.le, hy⟩ hxy
  simpa [slope_def_field, hzero] using hs

end Rudin.Chapter05
