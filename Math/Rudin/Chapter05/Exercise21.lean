module

public import Mathlib

@[expose] public section

noncomputable section
open scoped ContDiff
namespace Rudin.Chapter05

/-- Every closed subset of the line is the exact zero set of a smooth function.
The partition-of-unity theorem includes both the empty set and the whole line. -/
theorem exercise21_smooth_zero_set {E : Set ℝ} (hE : IsClosed E) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ f ⁻¹' {0} = E ∧
      ∀ k : ℕ, Differentiable ℝ (iteratedDeriv k f) := by
  obtain ⟨f, hf, _, hzero, _⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hE
      (isClosed_empty : IsClosed (∅ : Set ℝ)) (Set.disjoint_empty E)
  refine ⟨f, hf, ?_, fun k => hf.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k)⟩
  ext x
  exact (hzero x).symm

/-- Genuine derivatives exist at every lower order, not merely totalized `deriv` values. -/
theorem exercise21_finite_order_zero_set {E : Set ℝ} (hE : IsClosed E)
    (n : ℕ) :
    ∃ f : ℝ → ℝ, f ⁻¹' {0} = E ∧
      ∀ k : ℕ, k < n → Differentiable ℝ (iteratedDeriv k f) := by
  obtain ⟨f, _, hz, hd⟩ := exercise21_smooth_zero_set hE
  exact ⟨f, hz, fun k _ => hd k⟩

theorem exercise21_differentiable_zero_set {E : Set ℝ} (hE : IsClosed E) :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ f ⁻¹' {0} = E := by
  obtain ⟨f, _, hz, hd⟩ := exercise21_smooth_zero_set hE
  exact ⟨f, by simpa using hd 0, hz⟩

end Rudin.Chapter05
