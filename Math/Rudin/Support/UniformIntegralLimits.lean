module

public import Mathlib

/-! # Uniform limits and interval primitives
These are Bochner interval-integral results. Integrability is an explicit
hypothesis or follows from continuity. They do not replace the separate
Riemann or Stieltjes existence obligations in the exercises.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology

namespace Rudin.Support.UniformIntegralLimits

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform error on a closed interval bounds every primitive error. -/
theorem primitive_error_bound {a b x δ : ℝ} {f g : ℝ → E}
    (hx : x ∈ Icc a b) (hδ : 0 ≤ δ)
    (hf : IntervalIntegrable f volume a x) (hg : IntervalIntegrable g volume a x)
    (hbound : ∀ t ∈ Icc a b, ‖f t - g t‖ ≤ δ) :
    ‖(∫ t in a..x, f t) - ∫ t in a..x, g t‖ ≤ δ * (b - a) := by
  rw [← intervalIntegral.integral_sub hf hg]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := x) (f := fun t => f t - g t) (C := δ) (by
      intro t ht
      rw [uIoc_of_le hx.1] at ht
      exact hbound t ⟨ht.1.le, ht.2.trans hx.2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith [hx.2]) hδ)

/-- Uniform convergence of integrands gives uniform convergence of all primitives. -/
theorem uniform_primitives {a b : ℝ} {F : ℕ → ℝ → E} {g : ℝ → E}
    (hF : ∀ n x, x ∈ Icc a b → IntervalIntegrable (F n) volume a x)
    (hg : ∀ x, x ∈ Icc a b → IntervalIntegrable g volume a x)
    (hu : TendstoUniformlyOn F g atTop (Icc a b)) :
    TendstoUniformlyOn (fun n x => ∫ t in a..x, F n t)
      (fun x => ∫ t in a..x, g t) atTop (Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  let δ := ε / (|b - a| + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hu δ hδ] with n hn x hx
  have hb := primitive_error_bound hx hδ.le (hF n x hx) (hg x hx) (by
    intro t ht
    have h := (hn t ht).le
    simpa only [dist_eq_norm, norm_sub_rev] using h)
  rw [dist_comm, dist_eq_norm]
  refine hb.trans_lt ?_
  have hd : 0 < |b - a| + 1 := by positivity
  have he : δ * (b - a) = ε * (b - a) / (|b - a| + 1) := by dsimp [δ]; ring
  rw [he]
  apply (div_lt_iff₀ hd).mpr
  nlinarith [le_abs_self (b - a)]

/-- Continuous integrands supply all integrability hypotheses in the previous result. -/
theorem uniform_primitives_of_continuousOn {a b : ℝ} {F : ℕ → ℝ → E} {g : ℝ → E}
    (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hu : TendstoUniformlyOn F g atTop (Icc a b)) :
    TendstoUniformlyOn (fun n x => ∫ t in a..x, F n t)
      (fun x => ∫ t in a..x, g t) atTop (Icc a b) := by
  apply uniform_primitives (fun n x hx => ?_) (fun x hx => ?_) hu
  · exact ((hF n).mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  · exact (hg.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1

variable [CompleteSpace E]

/-- The continuous primitive has the source one-sided derivatives at both endpoints. -/
theorem primitive_hasDerivWithinAt {a b x : ℝ} {g : ℝ → E}
    (hg : ContinuousOn g (Icc a b)) (hx : x ∈ Icc a b) :
    HasDerivWithinAt (fun u => ∫ t in a..u, g t) (g x) (Icc a b) x := by
  let : Fact (x ∈ Icc a b) := ⟨hx⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hg.mono (Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1)
    (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hg x hx)

end Rudin.Support.UniformIntegralLimits
