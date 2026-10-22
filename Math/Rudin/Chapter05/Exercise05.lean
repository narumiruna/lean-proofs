module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter05

/-- The increment is the derivative at a point strictly between its endpoints. -/
theorem exercise05_mean_value (f : ℝ → ℝ)
    (hd : ∀ x > 0, DifferentiableAt ℝ f x) {x : ℝ} (hx : 0 < x) :
    ∃ c ∈ Ioo x (x + 1), f (x + 1) - f x = deriv f c := by
  obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope f (by linarith : x < x + 1)
    (show ContinuousOn f (Icc x (x + 1)) from fun t ht =>
      (hd t (lt_of_lt_of_le hx ht.1)).continuousAt.continuousWithinAt)
    (show DifferentiableOn ℝ f (Ioo x (x + 1)) from fun t ht =>
      (hd t (hx.trans ht.1)).differentiableWithinAt)
  exact ⟨c, hc, by simpa using heq.symm⟩

/-- Exercise 5: a derivative tending to zero forces the unit increment to
 tend to zero. No limit for `f` itself is assumed. -/
theorem exercise05_increment_limit (f : ℝ → ℝ)
    (hd : ∀ x > 0, DifferentiableAt ℝ f x)
    (hlim : Tendsto (deriv f) atTop (𝓝 0)) :
    Tendsto (fun x => f (x + 1) - f x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hlim ⊢
  intro ε hε
  obtain ⟨R, hR⟩ := hlim ε hε
  refine ⟨max R 1, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_right R 1).trans hx)
  obtain ⟨c, hc, heq⟩ := exercise05_mean_value f hd hxpos
  rw [heq]
  exact hR c ((le_max_left R 1).trans (hx.trans hc.1.le))

end Rudin.Chapter05
