module

public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# R06E02: a nonnegative continuous function with zero Riemann integral

Source: Rudin, Third Edition, book page 138 (PDF page 147).
The input is the literal Darboux integral with identity integrator. The proved
continuous Stieltjes bridge applies to this integrator, whose measure is volume.
Continuity and nonnegativity are required only on the closed interval.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesRefinement
  Rudin.Support.StieltjesMeasureBridge

/-- R06E02, including both endpoints. The strict interval hypothesis is essential. -/
theorem exercise02 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hi : HasDarbouxRSIntegral f id a b 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  have hb := continuous_bridge StieltjesFunction.id hab.le hf
  have hv := hasRSIntegral_unique (hasRSIntegral_of_hasDarbouxRSIntegral hab.le hi)
    (hasRSIntegral_of_hasDarbouxRSIntegral hab.le hb)
  have hz : (∫ x in a..b, f x) = 0 := by
    rw [Real.volume_eq_stieltjes_id]
    exact hv.symm
  intro x hx
  apply le_antisymm _ (hn x hx)
  by_contra h
  have hp := intervalIntegral.integral_pos hab hf
    (fun y hy => hn y (Ioc_subset_Icc_self hy)) ⟨x, hx, lt_of_not_ge h⟩
  rw [hz] at hp
  exact (lt_irrefl _ hp)

/-- A singleton interval cannot be included in the vanishing conclusion. -/
theorem exercise02_singleton_obstruction (a : ℝ) :
    ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a a) ∧
    (∀ x ∈ Icc a a, 0 ≤ (1 : ℝ)) ∧
    HasDarbouxRSIntegral (fun _ => 1) id a a 0 ∧
    ¬ (∀ x ∈ Icc a a, (1 : ℝ) = 0) := by
  refine ⟨continuousOn_const, by simp, hasDarbouxRSIntegral_self _ _ _, ?_⟩
  intro h
  have := h a ⟨le_rfl, le_rfl⟩
  norm_num at this

end Rudin.Chapter06
