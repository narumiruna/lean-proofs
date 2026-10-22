module

public import Mathlib

/-!
# R07E03: products of uniform limits need not converge uniformly

Source: Rudin, Third Edition, book page 165 (PDF 174).
Use E = R, F_n(x) = x, and G_n(x) = 1/(n+1). The product tends to zero
at every point, but has no uniform limit on R.
-/

@[expose] public section

namespace Rudin.Chapter07

open Set Filter
open scoped Topology

noncomputable def exercise03F (_n : ℕ) (x : ℝ) : ℝ := x

noncomputable def exercise03G (n : ℕ) (_x : ℝ) : ℝ := 1 / ((n : ℝ) + 1)

theorem exercise03_first_uniform :
    TendstoUniformlyOn exercise03F (fun x => x) atTop univ := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa [exercise03F] using hε)

theorem exercise03_second_uniform :
    TendstoUniformlyOn exercise03G (fun _ => 0) atTop univ := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := Metric.tendsto_nhds.mp hz ε hε
  filter_upwards [h] with n hn
  intro x _
  simpa only [exercise03G, Real.dist_eq, zero_sub, sub_zero, abs_neg] using hn

theorem exercise03_pointwise (x : ℝ) :
    Tendsto (fun n => exercise03F n x * exercise03G n x) atTop (𝓝 0) := by
  simpa only [exercise03F, exercise03G, mul_zero] using
    (tendsto_const_nhds (x := x)).mul tendsto_one_div_add_atTop_nhds_zero_nat

theorem exercise03_not_uniform :
    ¬ TendstoUniformlyOn (fun n x => exercise03F n x * exercise03G n x)
      (fun _ => 0) atTop univ := by
  intro hu
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hu (1 / 2) (by norm_num))
  have h := hN N le_rfl ((N : ℝ) + 1) (mem_univ _)
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  norm_num [exercise03F, exercise03G, Real.dist_eq, one_div, hn] at h

/-- The same explicit product has no other possible uniform limit either. -/
theorem exercise03_no_uniform_limit :
    ¬ ∃ h : ℝ → ℝ, TendstoUniformlyOn
      (fun n x => exercise03F n x * exercise03G n x) h atTop univ := by
  rintro ⟨h, hh⟩
  have he : h = fun _ => 0 := by
    funext x
    exact tendsto_nhds_unique (hh.tendsto_at (mem_univ x)) (exercise03_pointwise x)
  rw [he] at hh
  exact exercise03_not_uniform hh

/-- Both factors converge uniformly; their product converges pointwise but
has no uniform limit. All functions and the common domain are explicit. -/
theorem exercise03_unbounded_product_example :
    TendstoUniformlyOn exercise03F (fun x => x) atTop univ ∧
    TendstoUniformlyOn exercise03G (fun _ => 0) atTop univ ∧
    (∀ x, Tendsto (fun n => exercise03F n x * exercise03G n x) atTop (𝓝 0)) ∧
    ¬ ∃ h : ℝ → ℝ, TendstoUniformlyOn
      (fun n x => exercise03F n x * exercise03G n x) h atTop univ :=
  ⟨exercise03_first_uniform, exercise03_second_uniform, exercise03_pointwise,
    exercise03_no_uniform_limit⟩

end Rudin.Chapter07
