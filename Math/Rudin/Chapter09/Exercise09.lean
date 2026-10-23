module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# R09E09: zero derivative on a connected open set

Source: Rudin, Third Edition, Exercise 9.9, book page 239 (PDF page 248).
Both dimensions are arbitrary. Differentiability is an explicit hypothesis;
the zero value of the total function `fderiv` alone is not sufficient.
-/

@[expose] public section
namespace Rudin.Chapter09

/-- A differentiable Euclidean-space-valued map with zero derivative is
constant on a connected open domain, including the empty domain. -/
theorem exercise09 {n m : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hE : IsOpen E) (hc : IsPreconnected E) (hf : DifferentiableOn ℝ f E)
    (hzero : ∀ x ∈ E, fderiv ℝ f x = 0) :
    ∃ c, ∀ x ∈ E, f x = c :=
  hE.exists_is_const_of_fderiv_eq_zero hc hf hzero

end Rudin.Chapter09
