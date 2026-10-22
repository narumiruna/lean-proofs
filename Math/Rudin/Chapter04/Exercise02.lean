module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter04

/-- Continuous maps send the closure into the closure of the image. -/
theorem exercise02_closure_image_inclusion {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) (E : Set X) :
    f '' closure E ⊆ closure (f '' E) :=
  image_closure_subset_closure_image hf

/-- The exponential on the whole real line gives a strict inclusion. -/
theorem exercise02_strict_inclusion :
    Continuous Real.exp ∧
      Real.exp '' closure (univ : Set ℝ) ⊂ closure (Real.exp '' (univ : Set ℝ)) := by
  refine ⟨Real.continuous_exp, ?_⟩
  simp only [closure_univ, image_univ, Real.range_exp, closure_Ioi]
  exact Ioi_ssubset_Ici_self

end Rudin.Chapter04
