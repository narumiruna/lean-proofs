module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Exercise 11.9
The hypothesis is Lebesgue integrability, not Riemann integrability.
Continuity is relative to the whole closed interval, including both endpoints.
Source: book page 333, PDF page 342; equation (96), book page 324.
-/
@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Set

theorem exercise09_continuity {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → E} (hf : IntegrableOn f (Icc a b)) :
    ContinuousOn (fun x => ∫ t in a..x, f t) (Icc a b) := by
  simpa only [uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn f (uIcc a b) from by simpa [uIcc_of_le hab] using hf)

end Rudin.Chapter11
