module

public import Mathlib

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter05

/-- Continuity and the punctured derivative limit force the missing derivative. -/
theorem exercise09_derivative_at_zero {f : ℝ → ℝ}
    (hc : Continuous f) (hd : ∀ x ≠ 0, DifferentiableAt ℝ f x)
    (hl : Tendsto (deriv f) (𝓝[≠] 0) (𝓝 3)) : HasDerivAt f 3 0 := by
  have hr : HasDerivWithinAt f 3 (Ici 0) 0 :=
    hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun x hx => (hd x (ne_of_gt hx)).differentiableWithinAt)
      (hc.continuousAt.continuousWithinAt) self_mem_nhdsWithin
      (hl.mono_left (nhdsGT_le_nhdsNE 0))
  have hl' : HasDerivWithinAt f 3 (Iic 0) 0 :=
    hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun x hx => (hd x (ne_of_lt hx)).differentiableWithinAt)
      (hc.continuousAt.continuousWithinAt) self_mem_nhdsWithin
      (hl.mono_left (nhdsLT_le_nhdsNE 0))
  simpa using hl'.union hr

end Rudin.Chapter05
