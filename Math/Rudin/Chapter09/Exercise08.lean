module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# R09E08: stationarity at a local maximum

Source: Rudin, Third Edition, Exercise 9.8, book page 239 (PDF page 248).
The conclusion includes actual Fréchet derivative existence, not only the value
of the total function `fderiv`. A local maximum is relative to the open domain.
-/

@[expose] public section
namespace Rudin.Chapter09

/-- A differentiable real function has zero Fréchet derivative at an interior
local maximum. -/
theorem exercise08 {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hE : IsOpen E) (hx : x ∈ E) (hf : DifferentiableOn ℝ f E)
    (hmax : IsLocalMaxOn f E x) :
    HasFDerivAt f (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x ∧ fderiv ℝ f x = 0 := by
  have hd := (hf x hx).differentiableAt (hE.mem_nhds hx)
  have hz := (hmax.isLocalMax (hE.mem_nhds hx)).hasFDerivAt_eq_zero hd.hasFDerivAt
  exact ⟨hz ▸ hd.hasFDerivAt, hz⟩

end Rudin.Chapter09
