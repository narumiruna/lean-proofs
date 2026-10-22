module

public import Mathlib.Topology.Order.Rolle
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
namespace Rudin.Chapter04
open Set Filter Topology

/-- An open real map has no local maximum. -/
theorem exercise15_no_local_max {f : ℝ → ℝ} (ho : IsOpenMap f) (x : ℝ) :
    ¬ IsLocalMax f x := by
  intro h
  have hbound : Iic (f x) ∈ 𝓝 (f x) := ho.nhds_le x h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hbound
  have hm := hsub (show f x + ε / 2 ∈ Metric.ball (f x) ε by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < f x + ε / 2 - f x)]
    linarith)
  have : f x + ε / 2 ≤ f x := hm
  linarith

/-- An open real map has no local minimum. -/
theorem exercise15_no_local_min {f : ℝ → ℝ} (ho : IsOpenMap f) (x : ℝ) :
    ¬ IsLocalMin f x := by
  intro h
  have hbound : Ici (f x) ∈ 𝓝 (f x) := ho.nhds_le x h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hbound
  have hm := hsub (show f x - ε / 2 ∈ Metric.ball (f x) ε by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith : f x - ε / 2 - f x < 0)]
    linarith)
  have : f x ≤ f x - ε / 2 := hm
  linarith

/-- Injectivity is a consequence, not a hypothesis: equal endpoint values give a local extremum. -/
theorem exercise15_injective {f : ℝ → ℝ} (hc : Continuous f) (ho : IsOpenMap f) :
    Function.Injective f := by
  intro a b hab
  by_contra hne
  obtain ⟨c, _, hmin | hmax⟩ := exists_isLocalExtr_uIoo hne hc.continuousOn hab
  · exact exercise15_no_local_min ho c hmin
  · exact exercise15_no_local_max ho c hmax

/-- Every continuous open map of the real line is monotone in one of the two directions. -/
theorem exercise15_open_continuous_monotone {f : ℝ → ℝ}
    (hc : Continuous f) (ho : IsOpenMap f) : Monotone f ∨ Antitone f := by
  exact (hc.strictMono_of_inj (exercise15_injective hc ho)).imp
    (fun h => h.monotone) (fun h => h.antitone)

end Rudin.Chapter04
