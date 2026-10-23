module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Exercise 11.3
The convergence set is measurable. Limits here are finite real or complex
numbers, not extended real values. Source: book page 332, PDF page 341.
-/

@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter
open scoped Topology
variable {α : Type*} [MeasurableSpace α]

theorem exercise03_real (f : ℕ → α → ℝ) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : ℝ, Tendsto (fun n => f n x) atTop (𝓝 y)} :=
  measurableSet_exists_tendsto hf

/-- Finite complex convergence is equivalent to finite convergence of both components. -/
theorem exercise03_complex_iff (u : ℕ → ℂ) :
    (∃ z : ℂ, Tendsto u atTop (𝓝 z)) ↔
      (∃ a : ℝ, Tendsto (fun n => (u n).re) atTop (𝓝 a)) ∧
      (∃ b : ℝ, Tendsto (fun n => (u n).im) atTop (𝓝 b)) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨⟨z.re, Complex.continuous_re.continuousAt.tendsto.comp hz⟩,
      ⟨z.im, Complex.continuous_im.continuousAt.tendsto.comp hz⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_⟩
    have h := ha.ofReal.add (hb.ofReal.mul_const Complex.I)
    simpa only [Complex.re_add_im] using h

theorem exercise03_complex (f : ℕ → α → ℂ) (hf : ∀ n, Measurable (f n)) :
    MeasurableSet {x | ∃ y : ℂ, Tendsto (fun n => f n x) atTop (𝓝 y)} := by
  have hs : {x | ∃ y : ℂ, Tendsto (fun n => f n x) atTop (𝓝 y)} =
      {x | ∃ a : ℝ, Tendsto (fun n => (f n x).re) atTop (𝓝 a)} ∩
      {x | ∃ b : ℝ, Tendsto (fun n => (f n x).im) atTop (𝓝 b)} := by
    ext x
    exact exercise03_complex_iff (fun n => f n x)
  rw [hs]
  exact (exercise03_real _ (fun n => Complex.continuous_re.measurable.comp (hf n))).inter
    (exercise03_real _ (fun n => Complex.continuous_im.measurable.comp (hf n)))

end Rudin.Chapter11
