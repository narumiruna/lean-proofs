module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Tactic

/-!
# R11E18: the missing zero case in Schwarz equality

Source: Rudin, Exercise 11.18, book page 334 (PDF page 343).
The printed claim is that equality holds if and only if `g = c f` almost
everywhere. It has no nonzero hypothesis on `f`, so its forward implication
is false. `exercise18_original_counterexample` uses the finite measure
`Measure.dirac ()`, with `f = 0` and `g = 1`. It proves square integrability,
the displayed integral equality, and failure of every proposed scalar.

`exercise18` is the complete correction for complex square-integrable
functions on an arbitrary measure space: equality holds if and only if
`f = 0` almost everywhere or `g = c f` almost everywhere for some complex `c`.
It includes the both-zero and `g = 0` cases. `MemLp` includes almost-everywhere
strong measurability and finite L2 seminorm. No finite-measure assumption is
used in the correction. The integral uses `f * conj g`, as in the source;
Mathlib's inner product has the opposite conjugation convention, so the
bridge uses `inner g f`. All source hypotheses and both directions are covered.
-/

@[expose] public section

namespace Rudin.Chapter11

open MeasureTheory
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Complete Schwarz equality criterion in complex L2, including the zero case. -/
theorem exercise18_L2 (f g : Lp ℂ 2 μ) :
    ‖inner ℂ g f‖ ^ 2 = ‖f‖ ^ 2 * ‖g‖ ^ 2 ↔
      f = 0 ∨ ∃ c : ℂ, g = c • f := by
  rw [norm_inner_symm g f, ← mul_pow,
    sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (norm_inner_eq_norm_tfae ℂ f g).out 1 3

/-- Bridge from the source's conjugation convention to the L2 inner product. -/
theorem exercise18_inner_integral {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℂ (hg.toLp g) (hf.toLp f) = ∫ x, f x * conj (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [hfx, hgx, RCLike.inner_apply]

/-- Bridge from the L2 norm to the source's real integral of the squared norm. -/
theorem exercise18_norm_sq_integral {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hf.toLp f))]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, inner_self_eq_norm_sq]

/-- Corrected source statement, with no nonzero or finite-measure restriction. -/
theorem exercise18 {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x * conj (g x) ∂μ‖ ^ 2 =
        (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) ↔
      (f =ᵐ[μ] 0) ∨ ∃ c : ℂ, ∀ᵐ x ∂μ, g x = c * f x := by
  rw [← exercise18_inner_integral hf hg, ← exercise18_norm_sq_integral hf,
    ← exercise18_norm_sq_integral hg, exercise18_L2]
  have hz : hf.toLp f = 0 ↔ f =ᵐ[μ] 0 := by
    simpa only [MemLp.toLp_zero] using
      (hf.toLp_eq_toLp_iff (MemLp.zero : MemLp (0 : α → ℂ) 2 μ))
  have hs (c : ℂ) : hg.toLp g = c • hf.toLp f ↔
      ∀ᵐ x ∂μ, g x = c * f x := by
    rw [← MemLp.toLp_const_smul c hf, MemLp.toLp_eq_toLp_iff]
    rfl
  exact or_congr hz (exists_congr hs)

/-- The proportionality direction of the printed claim is valid, even for `f = 0`. -/
theorem exercise18_proportional_implies_equality {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (h : ∃ c : ℂ, ∀ᵐ x ∂μ, g x = c * f x) :
    ‖∫ x, f x * conj (g x) ∂μ‖ ^ 2 =
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) :=
  (exercise18 hf hg).mpr (Or.inr h)

/-- With the missing nonzero assumption stated, the printed equivalence is valid. -/
theorem exercise18_of_not_ae_zero {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hf0 : ¬ f =ᵐ[μ] 0) :
    ‖∫ x, f x * conj (g x) ∂μ‖ ^ 2 =
        (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖g x‖ ^ 2 ∂μ) ↔
      ∃ c : ℂ, ∀ᵐ x ∂μ, g x = c * f x := by
  rw [exercise18 hf hg, or_iff_right hf0]

/-- Explicit finite-measure counterexample to the original unrestricted claim. -/
theorem exercise18_original_counterexample :
    IsFiniteMeasure (Measure.dirac ()) ∧
    MemLp (fun _ : Unit => (0 : ℂ)) 2 (Measure.dirac ()) ∧
    MemLp (fun _ : Unit => (1 : ℂ)) 2 (Measure.dirac ()) ∧
    ‖∫ _x : Unit, (0 : ℂ) * conj (1 : ℂ) ∂Measure.dirac ()‖ ^ 2 =
      (∫ _x : Unit, ‖(0 : ℂ)‖ ^ 2 ∂Measure.dirac ()) *
        (∫ _x : Unit, ‖(1 : ℂ)‖ ^ 2 ∂Measure.dirac ()) ∧
    ¬ ∃ c : ℂ, ∀ᵐ _x : Unit ∂Measure.dirac (), (1 : ℂ) = c * (0 : ℂ) := by
  refine ⟨inferInstance, memLp_const 0, memLp_const 1, ?_, ?_⟩
  · simp
  · simp

end Rudin.Chapter11

#print axioms Rudin.Chapter11.exercise18_L2
#print axioms Rudin.Chapter11.exercise18_inner_integral
#print axioms Rudin.Chapter11.exercise18_norm_sq_integral
#print axioms Rudin.Chapter11.exercise18
#print axioms Rudin.Chapter11.exercise18_proportional_implies_equality
#print axioms Rudin.Chapter11.exercise18_of_not_ae_zero
#print axioms Rudin.Chapter11.exercise18_original_counterexample
