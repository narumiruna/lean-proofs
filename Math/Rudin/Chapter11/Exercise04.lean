module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Exercise 11.4
A bounded measurable multiplier preserves integrability on a measurable set.
The scalar type can be real or complex. Measurability is needed only with
respect to the restricted measure. Source: book page 332, PDF page 341.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory
variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]


theorem exercise04 (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (f g : α → 𝕜) (hf : IntegrableOn f E μ)
    (hg : AEStronglyMeasurable g (μ.restrict E))
    (hbound : ∃ C : ℝ, ∀ x ∈ E, ‖g x‖ ≤ C) :
    AEStronglyMeasurable (fun x => f x * g x) (μ.restrict E) ∧
      IntegrableOn (fun x => f x * g x) E μ := by
  obtain ⟨C, hC⟩ := hbound
  have h := hf.mul_bdd hg ((ae_restrict_iff' hE).mpr (.of_forall hC))
  exact ⟨h.aestronglyMeasurable, h⟩

/-- Measurability on the source domain for real functions. -/
theorem exercise04_measurable_real (E : Set α) (f g : α → ℝ)
    (hf : Measurable (fun x : E => f x)) (hg : Measurable (fun x : E => g x)) :
    Measurable (fun x : E => f x * g x) :=
  continuous_mul.measurable.comp (hf.prodMk hg)

/-- Measurability on the source domain for complex functions. -/
theorem exercise04_measurable_complex (E : Set α) (f g : α → ℂ)
    (hf : Measurable (fun x : E => f x)) (hg : Measurable (fun x : E => g x)) :
    Measurable (fun x : E => f x * g x) :=
  continuous_mul.measurable.comp (hf.prodMk hg)

end Rudin.Chapter11
