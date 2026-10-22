module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace Rudin.Chapter04
open Set

/-- A continuous self-map of the closed unit interval has a fixed point, including endpoints. -/
theorem exercise14_fixed_point (f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  let F : ℝ → ℝ := fun x => (f ⟨max 0 (min 1 x), by constructor <;> simp⟩ : ℝ)
  have hF : Continuous F := by
    exact continuous_subtype_val.comp (hf.comp
      ((continuous_const.max (continuous_const.min continuous_id)).subtype_mk _))
  obtain ⟨c, hc, heq⟩ := exists_mem_Icc_isFixedPt_of_mapsTo hF.continuousOn
    (by norm_num : (0 : ℝ) ≤ 1) (fun x _ => (f ⟨max 0 (min 1 x), by constructor <;> simp⟩).property)
  refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  simpa [Function.IsFixedPt, F, min_eq_right hc.2, max_eq_right hc.1] using heq

end Rudin.Chapter04
