module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-! # R09E11: gradient product and reciprocal rules
Source: book page 239, PDF page 248. Each formula includes genuine derivative existence.
-/

@[expose] public section
namespace Rudin.Chapter09
open scoped Gradient

theorem exercise11_product {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    HasGradientAt (fun y => f y * g y) (f x • gradient g x + g x • gradient f x) x ∧
    gradient (fun y => f y * g y) x = f x • gradient g x + g x • gradient f x := by
  have h : HasGradientAt (fun y => f y * g y)
      (f x • gradient g x + g x • gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hf.hasGradientAt.hasFDerivAt.mul hg.hasGradientAt.hasFDerivAt using 1
    simp
  exact ⟨h, h.gradient⟩

theorem exercise11_reciprocal {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    HasGradientAt (fun y => 1 / f y) (-(f x ^ 2)⁻¹ • gradient f x) x ∧
    gradient (fun y => 1 / f y) x = -(f x ^ 2)⁻¹ • gradient f x := by
  have h : HasGradientAt (fun y => 1 / f y) (-(f x ^ 2)⁻¹ • gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hasDerivAt_inv hx).comp_hasFDerivAt x hf.hasGradientAt.hasFDerivAt using 1 <;> simp [one_div, Function.comp_def]
  exact ⟨h, h.gradient⟩
end Rudin.Chapter09
