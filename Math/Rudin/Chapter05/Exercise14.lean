module

public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

namespace Rudin.Chapter05

open Set

/-- Rudin 5.14: no continuity of the derivative is assumed. -/
theorem exercise14_first_derivative_criterion {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b)) :
    ConvexOn ℝ (Ioo a b) f ↔ MonotoneOn (deriv f) (Ioo a b) := by
  have hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x :=
    fun x hx => (hf x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  constructor
  · exact fun h => h.monotoneOn_deriv hd
  · intro h
    apply MonotoneOn.convexOn_of_deriv (convex_Ioo a b) hf.continuousOn
    · simpa using hf
    · simpa using h

/-- Rudin 5.14: existence of both derivatives, not `ContDiff 2`. -/
theorem exercise14_second_derivative_criterion {f : ℝ → ℝ} {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Ioo a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Ioo a b)) :
    ConvexOn ℝ (Ioo a b) f ↔ ∀ x ∈ Ioo a b, 0 ≤ deriv (deriv f) x := by
  rw [exercise14_first_derivative_criterion hf]
  constructor
  · intro h x hx
    rw [← derivWithin_of_isOpen isOpen_Ioo hx]
    exact h.derivWithin_nonneg
  · intro h
    apply monotoneOn_of_deriv_nonneg (convex_Ioo a b) hf'.continuousOn
    · simpa using hf'
    · simpa using h

end Rudin.Chapter05
