module

public import Mathlib

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter04

/-- A single nonzero value at the origin. -/
noncomputable def exercise01_spike (x : ℝ) : ℝ := by
  classical
  exact if x = 0 then 1 else 0

/-- Symmetric differences tend to zero at every real point. -/
theorem exercise01_symmetric_limit (x : ℝ) :
    Tendsto (fun h => exercise01_spike (x + h) - exercise01_spike (x - h))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
  classical
  by_cases hx : x = 0
  · subst x
    have heq : (fun h : ℝ => exercise01_spike (0 + h) - exercise01_spike (0 - h)) =
        (fun _ => 0) := by
      funext h
      simp [exercise01_spike]
    rw [heq]
    exact tendsto_const_nhds
  · have ha : ∀ᶠ h : ℝ in 𝓝 0, x + h ≠ 0 :=
      (continuousAt_const.add continuousAt_id).eventually
        (isOpen_compl_singleton.mem_nhds (by simpa using hx))
    have hb : ∀ᶠ h : ℝ in 𝓝 0, x - h ≠ 0 :=
      (continuousAt_const.sub continuousAt_id).eventually
        (isOpen_compl_singleton.mem_nhds (by simpa using hx))
    apply tendsto_const_nhds.congr'
    filter_upwards [ha, hb] with h ha hb
    simp [exercise01_spike, ha, hb]

/-- The spike is not continuous at zero. -/
theorem exercise01_not_continuous : ¬ Continuous exercise01_spike := by
  intro hc
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := 0))
    (1 / 2) (by norm_num)
  have hh : δ / 2 ≠ 0 := ne_of_gt (by positivity)
  have hi := hd (x := δ / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  norm_num [exercise01_spike, hh, Real.dist_eq] at hi

/-- The proposed converse is false. The stronger, unpunctured limit also holds. -/
theorem exercise01_symmetric_difference_converse :
    ∃ f : ℝ → ℝ, (∀ x : ℝ,
      Tendsto (fun h => f (x + h) - f (x - h)) (𝓝[≠] (0 : ℝ)) (𝓝 0)) ∧
      ¬ Continuous f := by
  exact ⟨exercise01_spike, fun x =>
    (exercise01_symmetric_limit x).mono_left nhdsWithin_le_nhds,
    exercise01_not_continuous⟩

end Rudin.Chapter04
