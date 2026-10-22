module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R01E17: the parallelogram identity

Source: Rudin, book page 23 (PDF page 32).
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The Euclidean parallelogram identity. -/
theorem exercise17 {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  simpa [mul_add] using parallelogram_law_with_norm ℝ x y

/-- For the four vertices `a,b,c,d` in order, `a+c=b+d` says that the
opposite sides are parallel and equal as vectors. The sum of the squared
lengths of the diagonals equals that of all four sides. No nondegeneracy
assumption is needed. -/
theorem exercise17_geometry {k : ℕ} (a b c d : EuclideanSpace ℝ (Fin k))
    (h : a + c = b + d) :
    dist a c ^ 2 + dist b d ^ 2 =
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  have hc : c = b + d - a := by
    calc c = (a + c) - a := by abel
         _ = b + d - a := by rw [h]
  subst c
  have h₁ : (b - a) + (d - a) = -(a - (b + d - a)) := by module
  have h₂ : (b - a) - (d - a) = b - d := by module
  have h₃ : b - (b + d - a) = -(d - a) := by module
  have h₄ : b + d - a - d = -(a - b) := by module
  have hp := exercise17 (b - a) (d - a)
  rw [h₁, h₂, norm_neg] at hp
  simp only [dist_eq_norm, h₃, h₄, norm_neg]
  rw [norm_sub_rev b a] at hp
  nlinarith

end Rudin.Chapter01
