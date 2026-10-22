module

public import Mathlib

/-! # Chapter 7, Exercise 9
Source: book page 166, PDF page 175.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace Rudin.Chapter07

/-- The moving-point conclusion on an arbitrary metric-space subset. -/
theorem exercise09_moving_points {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {E : Set X} {F : ℕ → X → Y} {f : X → Y}
    (hc : ∀ n, ContinuousOn (F n) E) (hu : TendstoUniformlyOn F f atTop E)
    {x : X} (hx : x ∈ E) {u : ℕ → X} (hmem : ∀ n, u n ∈ E)
    (hu' : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => F n (u n)) atTop (𝓝 (f x)) := by
  have hf := hu.continuousOn (Frequently.of_forall hc)
  exact hu.tendsto_comp (hf x hx)
    (tendsto_nhdsWithin_iff.mpr ⟨hu', Eventually.of_forall hmem⟩)

noncomputable def exercise09Counterexample (n : ℕ) (x : ℝ) : ℝ := x / (n + 1 : ℝ)

theorem exercise09_counterexample_continuous (n : ℕ) :
    Continuous (exercise09Counterexample n) := by
  unfold exercise09Counterexample
  fun_prop

/-- Every convergent moving sequence satisfies the requested limit. -/
theorem exercise09_counterexample_moving {x : ℝ} {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => exercise09Counterexample n (u n)) atTop (𝓝 0) := by
  exact hu.div_atTop ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)

/-- The domain is the noncompact real line. The continuous counterexample has
all moving-point limits but does not converge uniformly. -/
theorem exercise09_converse :
    (∀ n, Continuous (exercise09Counterexample n)) ∧
    (∀ (x : ℝ) (u : ℕ → ℝ), Tendsto u atTop (𝓝 x) →
      Tendsto (fun n => exercise09Counterexample n (u n)) atTop (𝓝 0)) ∧
    ¬ TendstoUniformly exercise09Counterexample (fun _ => 0) atTop := by
  refine ⟨exercise09_counterexample_continuous,
    fun _ _ h => exercise09_counterexample_moving h, ?_⟩
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformly_iff.mp h) (1 / 2) (by norm_num))
  have hn := hN N le_rfl (N + 1 : ℝ)
  have hne : (N + 1 : ℝ) ≠ 0 := by positivity
  norm_num [exercise09Counterexample, div_self hne, Real.dist_eq] at hn

end Rudin.Chapter07
