module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section

open Set

namespace Rudin.Chapter04

/-- A bounded subset of the real line is totally bounded, and uniform maps preserve this. -/
theorem exercise08_bounded_image (E : Set ℝ) (hE : Bornology.IsBounded E)
    (f : E → ℝ) (hf : UniformContinuous f) : Bornology.IsBounded (Set.range f) := by
  have ht : TotallyBounded E := hE.isCompact_closure.totallyBounded.subset subset_closure
  have hs : TotallyBounded (Set.univ : Set E) :=
    (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing).mp (by simpa using ht)
  simpa using (hs.image hf).isBounded

/-- The equivalent formulation for a real function restricted to E. -/
theorem exercise08_bounded_image_on (E : Set ℝ) (hE : Bornology.IsBounded E)
    (f : ℝ → ℝ) (hf : UniformContinuousOn f E) : Bornology.IsBounded (f '' E) := by
  simpa only [Set.range_domRestrict] using
    exercise08_bounded_image E hE (E.domRestrict f) (uniformContinuousOn_iff_restrict.mp hf)

/-- The identity on the whole real line gives the requested counterexample. -/
theorem exercise08_unbounded_domain :
    ¬ Bornology.IsBounded (Set.univ : Set ℝ) ∧
      UniformContinuousOn (fun x : ℝ => x) Set.univ ∧
      ¬ Bornology.IsBounded ((fun x : ℝ => x) '' Set.univ) := by
  have hu : ¬ Bornology.IsBounded (Set.univ : Set ℝ) := by
    intro hb
    obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hb
    have h := hC (Set.mem_univ (|C| + 1)) (Set.mem_univ 0)
    simp only [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < |C| + 1)] at h
    linarith [le_abs_self C]
  exact ⟨hu, uniformContinuous_id.uniformContinuousOn, by simpa using hu⟩

end Rudin.Chapter04
