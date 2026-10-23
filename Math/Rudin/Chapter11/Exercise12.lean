module

public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComplex
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exercise 11.12
Separate continuity and the bound ≤ 1 imply continuity of the integral on
the closed unit interval. Section continuity supplies measurability and
integrability; dominated convergence supplies parameter continuity. Joint
continuity or joint measurability is not assumed. The real and complex
section integrals also satisfy the literal Riemann definitions.
Source: book page 333, PDF page 342.
-/
@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Filter Set
open scoped Topology
open Rudin.Support StieltjesPrototype StieltjesRefinement StieltjesEquivalence
  StieltjesIntegralLaws RiemannIntegrability StieltjesComplex

theorem exercise12_section_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℝ → E}
    (hy : ∀ x ∈ Icc (0 : ℝ) 1, ContinuousOn (f x) (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (f x) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa using hy x hx

theorem exercise12_continuity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → ℝ → E}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f x y‖ ≤ 1)
    (hy : ∀ x ∈ Icc (0 : ℝ) 1, ContinuousOn (f x) (Icc 0 1))
    (hx : ∀ y ∈ Icc (0 : ℝ) 1, ContinuousOn (fun x => f x y) (Icc 0 1)) :
    ContinuousOn (fun x => ∫ y in (0 : ℝ)..1, f x y) (Icc 0 1) := by
  intro x hx0
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
    (bound := fun _ => 1)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using (exercise12_section_integrable hy hz).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards with y hy0
    have hy1 : y ∈ Ioc (0 : ℝ) 1 := by simpa using hy0
    exact hb z hz y ⟨hy1.1.le, hy1.2⟩
  · exact intervalIntegrable_const
  · filter_upwards with y hy0
    have hy1 : y ∈ Ioc (0 : ℝ) 1 := by simpa using hy0
    exact hx y ⟨hy1.1.le, hy1.2⟩ x hx0

theorem exercise12_real_riemann {f : ℝ → ℝ → ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |f x y| ≤ 1)
    (hy : ∀ x ∈ Icc (0 : ℝ) 1, ContinuousOn (f x) (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDarbouxRSIntegral (f x) id 0 1 (∫ y in (0 : ℝ)..1, f x y) :=
  hasDarbouxRSIntegral_of_ae_continuousWithinAt (by norm_num) (hb x hx)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy0
        exact hy x hx y hy0)

/-- Complex continuous sections have the actual complex tagged Riemann integral,
not just a totalized Bochner value. -/
theorem exercise12_complex_riemann {f : ℝ → ℝ → ℂ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f x y‖ ≤ 1)
    (hy : ∀ x ∈ Icc (0 : ℝ) 1, ContinuousOn (f x) (Icc 0 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasComplexRSIntegral (f x) id 0 1 (∫ y in (0 : ℝ)..1, f x y) := by
  have hr := exercise12_real_riemann
    (fun z hz y hy0 => (Complex.abs_re_le_norm _).trans (hb z hz y hy0))
    (fun z hz => Complex.continuous_re.comp_continuousOn (hy z hz)) hx
  have hi := exercise12_real_riemann
    (fun z hz y hy0 => (Complex.abs_im_le_norm _).trans (hb z hz y hy0))
    (fun z hz => Complex.continuous_im.comp_continuousOn (hy z hz)) hx
  have hf := (exercise12_section_integrable hy hx).left
  apply hasComplexRSIntegral_iff.mpr
  constructor
  · convert hasRSIntegral_of_hasDarbouxRSIntegral zero_le_one hr using 1
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (integral_re hf).symm
  · convert hasRSIntegral_of_hasDarbouxRSIntegral zero_le_one hi using 1
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact (integral_im hf).symm

end Rudin.Chapter11
