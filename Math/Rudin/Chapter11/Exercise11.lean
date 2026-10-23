module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

/-! # Exercise 11.11
The metric space is Lp at exponent 1: integrable functions modulo equality
almost everywhere. Raw functions have only a pseudometric. No finiteness
condition is imposed on the measure. The results apply to real and complex
functions, and more generally to complete real normed spaces.
Source: book page 333, PDF page 342; quotient convention, book pages 326, 332.
-/
@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter Set
open scoped Topology

section Metric
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α}

/-- The displayed distance is exactly the existing quotient metric. -/
theorem exercise11_distance (f g : Lp E 1 μ) :
    dist f g = ∫ x, ‖f x - g x‖ ∂μ := by
  simpa only [dist_eq_norm] using L1.dist_eq_integral_dist f g

theorem exercise11_norm_difference (f g : Lp E 1 μ) :
    ‖f - g‖ = ∫ x, ‖f x - g x‖ ∂μ := by
  rw [← dist_eq_norm]
  exact exercise11_distance f g

theorem exercise11_distance_integrable (f g : Lp E 1 μ) :
    Integrable (fun x => ‖f x - g x‖) μ :=
  ((L1.integrable_coeFn f).sub (L1.integrable_coeFn g)).norm

theorem exercise11_metric_axioms (f g h : Lp E 1 μ) :
    0 ≤ (∫ x, ‖f x - g x‖ ∂μ) ∧
    ((∫ x, ‖f x - g x‖ ∂μ) = 0 ↔ f = g) ∧
    (∫ x, ‖f x - g x‖ ∂μ) = (∫ x, ‖g x - f x‖ ∂μ) ∧
    (∫ x, ‖f x - h x‖ ∂μ) ≤
      (∫ x, ‖f x - g x‖ ∂μ) + (∫ x, ‖g x - h x‖ ∂μ) := by
  simp only [← exercise11_distance]
  exact ⟨dist_nonneg, dist_eq_zero, dist_comm f g, dist_triangle f g h⟩

theorem exercise11_representative_independence {f f' g g' : α → E}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    (∫ x, ‖f x - g x‖ ∂μ) = ∫ x, ‖f' x - g' x‖ ∂μ :=
  integral_congr_ae (hf.sub hg |>.fun_comp norm)

/-- Every integrable raw function has its class, with the same distance. -/
theorem exercise11_toL1_distance {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, ‖f x - g x‖ ∂μ := by
  rw [exercise11_distance]
  exact exercise11_representative_independence hf.coeFn_toL1 hg.coeFn_toL1

theorem exercise11_zero_iff_ae {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    (∫ x, ‖f x - g x‖ ∂μ) = 0 ↔ f =ᵐ[μ] g := by
  rw [← exercise11_toL1_distance hf hg, dist_eq_zero]
  exact Integrable.toL1_eq_toL1_iff f g hf hg

theorem exercise11_complete [CompleteSpace E] : CompleteSpace (Lp E 1 μ) := inferInstance

theorem exercise11_cauchy_converges [CompleteSpace E] (u : ℕ → Lp E 1 μ) (hu : CauchySeq u) :
    ∃ f : Lp E 1 μ, Tendsto (fun n => ∫ x, ‖u n x - f x‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hu
  exact ⟨f, by simpa only [← exercise11_distance] using
    (tendsto_iff_dist_tendsto_zero.mp hf)⟩
end Metric

/-- A singleton indicator and zero are distinct raw integrable functions on [0,1]. -/
theorem exercise11_raw_function_degeneracy :
    ∃ f g : ℝ → ℝ,
      IntegrableOn f (Icc 0 1) ∧ IntegrableOn g (Icc 0 1) ∧
      f 0 ≠ g 0 ∧ f =ᵐ[volume.restrict (Icc 0 1)] g ∧
      (∫ x in Icc (0 : ℝ) 1, ‖f x - g x‖) = 0 := by
  let f : ℝ → ℝ := ({0} : Set ℝ).indicator (fun _ => 1)
  have heq : f =ᵐ[volume.restrict (Icc 0 1)] (fun _ => 0) := by
    apply ae_restrict_of_ae
    filter_upwards [show ∀ᵐ x : ℝ, x ≠ 0 from by simp [ae_iff]] with x hx
    simp [f, hx]
  have hz : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) := integrable_zero _ _ _
  have hi : IntegrableOn f (Icc 0 1) := hz.congr heq.symm
  refine ⟨f, fun _ => 0, hi, hz, ?_, heq, ?_⟩
  · simp [f]
  · exact (exercise11_zero_iff_ae hi hz).mpr heq

end Rudin.Chapter11
