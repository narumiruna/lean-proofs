module

public import Math.Rudin.Support.RiemannIntegrability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Exercise 11.8
The input is a literal Darboux Riemann integral. The existing small-gap
criterion constructs its restricted integrals, and the raw Riemann bridge
identifies every value with its Lebesgue interval integral. The conclusion
is genuine derivative existence almost everywhere; endpoints form a null set.
Source: book page 333, PDF page 342.
-/
@[expose] public section
namespace Rudin.Chapter11
open MeasureTheory Set
open Rudin.Support StieltjesPrototype StieltjesEquivalence StieltjesIntegralLaws
  RiemannIntegrability

/-- The indefinite integral used below is the actual source Riemann integral
at every point, including both endpoints. -/
theorem exercise08_riemann_primitive {f : ℝ → ℝ} {a b v : ℝ}
    (_hab : a ≤ b) (hf : HasDarbouxRSIntegral f id a b v) :
    ∀ x ∈ Icc a b, HasDarbouxRSIntegral f id a x (∫ t in a..x, f t) := by
  intro x hx
  obtain ⟨l, r, hl, _, _⟩ := hasDarbouxRSIntegral_split hx.1 hx.2 hf
  rw [(intervalIntegrable_and_integral_eq hx.1 hl).2]
  exact hl

/-- No Lebesgue integrability hypothesis is added to Riemann integrability. -/
theorem exercise08_almost_everywhere_derivative {f : ℝ → ℝ} {a b v : ℝ}
    (hab : a ≤ b) (hf : HasDarbouxRSIntegral f id a b v) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x := by
  have hi := (intervalIntegrable_and_integral_eq hab hf).1
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxab
  exact hx (by simpa [uIcc_of_le hab] using hxab) a left_mem_uIcc

/-- The equivalent raw tagged-refinement criterion gives the same result. -/
theorem exercise08_tagged_almost_everywhere_derivative {f : ℝ → ℝ} {a b v : ℝ}
    (hab : a ≤ b) (hf : HasRSIntegral f id a b v) :
    ∀ᵐ x ∂volume.restrict (Icc a b),
      HasDerivAt (fun x => ∫ t in a..x, f t) (f x) x :=
  exercise08_almost_everywhere_derivative hab
    (hasDarbouxRSIntegral_of_hasRSIntegral hab hf)

end Rudin.Chapter11
