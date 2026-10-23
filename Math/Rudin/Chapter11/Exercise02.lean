module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Analysis.Complex.Basic

/-!
# Exercise 11.2
An integrable function whose integral on every measurable subset is zero
vanishes almost everywhere. The measure is arbitrary, not necessarily finite
or sigma-finite. The normed-space statement includes real and complex scalars.
Source: book page 332, PDF page 341.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory
variable {α V : Type*} [MeasurableSpace α]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem exercise02 (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (f : α → V) (hf : IntegrableOn f E μ)
    (hzero : ∀ A, MeasurableSet A → A ⊆ E → ∫ x in A, f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ E → f x = 0 := by
  apply (ae_restrict_iff' hE).mp
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro A hA _
  rw [Measure.restrict_restrict hA]
  exact hzero (A ∩ E) (hA.inter hE) Set.inter_subset_right

end Rudin.Chapter11
