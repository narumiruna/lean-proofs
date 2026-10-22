module

public import Math.Rudin.Support.StieltjesIntegrationByParts

/-!
# R06E17: integration by parts with a discontinuous monotone factor

Source: Rudin, Third Edition, book page 141 (PDF 150).
All derivatives are within the closed interval, including one-sided endpoints.
Both literal integrals are constructed; neither is an assumption.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype

/-- The source formula, including actual existence and raw endpoint values. -/
theorem exercise17_stieltjes_parts {a b : ℝ} {α g G : ℝ → ℝ} (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (g x) (Icc a b) x) :
    ∃ A B : ℝ, HasDarbouxRSIntegral (fun x => α x * g x) id a b A ∧
      HasDarbouxRSIntegral G α a b B ∧ A = G b * α b - G a * α a - B :=
  Rudin.Support.StieltjesIntegrationByParts.stieltjes_parts hab hα hg hG

/-- The full complex-valued statement, by real and imaginary components. -/
theorem exercise17_stieltjes_parts_complex {a b : ℝ} {α : ℝ → ℝ} {g G : ℝ → ℂ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hG : ∀ x ∈ Icc a b, HasDerivWithinAt G (g x) (Icc a b) x) :
    ∃ A B : ℂ,
      Rudin.Support.StieltjesComplex.HasComplexRSIntegral (fun x => α x • g x) id a b A ∧
      Rudin.Support.StieltjesComplex.HasComplexRSIntegral G α a b B ∧
        A = α b • G b - α a • G a - B :=
  Rudin.Support.StieltjesIntegrationByParts.stieltjes_parts_complex hab hα hg hG

end Rudin.Chapter06
