module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# R11E01: a nonnegative function with zero integral vanishes almost everywhere

Source: Rudin, *Principles of Mathematical Analysis*, Third Edition,
Exercise 11.1, book page 332 (PDF page 341).

Original convention: Definition 11.21 (book page 314) defines the integral of
a measurable nonnegative function as a supremum of simple-function integrals;
its value may be positive infinity. Thus measurability is implicit in the
exercise's integral notation. We state it explicitly, only on the measurable
set `E`. Mathlib's `AEMeasurable` is sufficient and also permits changes on null
sets. Almost everywhere on `E` is written as `∀ᵐ x ∂μ, x ∈ E → ...`.

`exercise01` uses the nonnegative Lebesgue integral (`lintegral`) of
`ENNReal.ofReal ∘ f`. Nonnegativity on `E` ensures that this conversion loses no
values on the domain of integration. `exercise01_ennreal` also covers extended
nonnegative values, including positive infinity. Neither theorem assumes finite
measure or integrability in advance.

`exercise01_integrable` gives the real Bochner-integral version. Its explicit
`IntegrableOn` hypothesis is necessary for this notation: Mathlib defines the
Bochner integral to be zero for non-integrable functions. This default value
must not be used as the zero-integral hypothesis in the original exercise.
-/

@[expose] public section

namespace Rudin.Chapter11

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- Nonnegative extended-valued version of the source statement. -/
theorem exercise01_ennreal (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (f : α → ℝ≥0∞) (hf : AEMeasurable f (μ.restrict E))
    (hzero : ∫⁻ x in E, f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ E → f x = 0 :=
  (setLIntegral_eq_zero_iff' hE hf).mp hzero

/-- A real function, nonnegative on `E`, with zero nonnegative integral is zero a.e. on `E`. -/
theorem exercise01 (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (f : α → ℝ) (hf : AEMeasurable f (μ.restrict E))
    (hnonneg : ∀ x ∈ E, 0 ≤ f x)
    (hzero : ∫⁻ x in E, ENNReal.ofReal (f x) ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ E → f x = 0 := by
  have h := exercise01_ennreal μ E hE (fun x => ENNReal.ofReal (f x))
    hf.ennreal_ofReal hzero
  filter_upwards [h] with x hx
  intro hxE
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp (hx hxE)) (hnonneg x hxE)

/-- Bochner-integral version, with integrability explicit to exclude its default zero value. -/
theorem exercise01_integrable (μ : Measure α) (E : Set α) (hE : MeasurableSet E)
    (f : α → ℝ) (hf : IntegrableOn f E μ)
    (hnonneg : ∀ x ∈ E, 0 ≤ f x) (hzero : ∫ x in E, f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ E → f x = 0 := by
  have hnonneg_ae : 0 ≤ᵐ[μ.restrict E] f :=
    (ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hnonneg)
  exact (ae_restrict_iff' hE).mp
    ((setIntegral_eq_zero_iff_of_nonneg_ae hnonneg_ae hf).mp hzero)

end Rudin.Chapter11
