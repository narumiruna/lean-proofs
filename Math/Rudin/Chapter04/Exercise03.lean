module

public import Mathlib

@[expose] public section

namespace Rudin.Chapter04

/-- The zero set of a continuous real function is closed. -/
theorem exercise03_zero_set_closed {X : Type*} [MetricSpace X]
    {f : X → ℝ} (hf : Continuous f) : IsClosed {p : X | f p = 0} :=
  isClosed_eq hf continuous_const

end Rudin.Chapter04
