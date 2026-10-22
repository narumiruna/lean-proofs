module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- The quotient of two functions of a real parameter. The denominator is
nonzero on a punctured neighborhood, not merely nonzero after totalized division. -/
theorem exercise07_quotient {𝕜 : Type*} [RCLike 𝕜]
    {f g : ℝ → 𝕜} {x : ℝ} {A B : 𝕜}
    (hf : HasDerivAt f A x) (hg : HasDerivAt g B x)
    (hfx : f x = 0) (hgx : g x = 0) (hB : B ≠ 0) :
    (∀ᶠ t in 𝓝[≠] x, g t ≠ 0) ∧
      Tendsto (fun t => f t / g t) (𝓝[≠] x) (𝓝 (A / B)) := by
  have hf' := hf.tendsto_slope
  have hg' := hg.tendsto_slope
  have hn : ∀ᶠ t in 𝓝[≠] x, slope g x t ≠ 0 :=
    hg'.eventually (eventually_ne_nhds hB)
  constructor
  · filter_upwards [hn] with t ht hzero
    exact ht (by simp [slope, hgx, hzero])
  · apply (hf'.div hg' hB).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htx : t - x ≠ 0 := sub_ne_zero.mpr ht
    change slope f x t / slope g x t = f t / g t
    simp only [slope_def_module, hfx, hgx, sub_zero, Algebra.smul_def]
    have hc : algebraMap ℝ 𝕜 (t - x)⁻¹ ≠ 0 :=
      (map_ne_zero (algebraMap ℝ 𝕜)).mpr (inv_ne_zero htx)
    exact mul_div_mul_left (f t) (g t) hc

/-- Exercise 7 for real-valued functions. -/
theorem exercise07_real_quotient_limit {f g : ℝ → ℝ} {x A B : ℝ}
    (hf : HasDerivAt f A x) (hg : HasDerivAt g B x)
    (hfx : f x = 0) (hgx : g x = 0) (hB : B ≠ 0) :
    (∀ᶠ t in 𝓝[≠] x, g t ≠ 0) ∧
      Tendsto (fun t => f t / g t) (𝓝[≠] x) (𝓝 (A / B)) :=
  exercise07_quotient hf hg hfx hgx hB

/-- Exercise 7 for complex-valued functions of a real variable. -/
theorem exercise07_complex_quotient_limit {f g : ℝ → ℂ} {x : ℝ} {A B : ℂ}
    (hf : HasDerivAt f A x) (hg : HasDerivAt g B x)
    (hfx : f x = 0) (hgx : g x = 0) (hB : B ≠ 0) :
    (∀ᶠ t in 𝓝[≠] x, g t ≠ 0) ∧
      Tendsto (fun t => f t / g t) (𝓝[≠] x) (𝓝 (A / B)) :=
  exercise07_quotient hf hg hfx hgx hB

end Rudin.Chapter05
