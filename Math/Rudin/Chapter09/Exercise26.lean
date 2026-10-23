module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Tactic

/-! # A continuous mixed partial does not force the first partial

`D12` means `D1 (D2 f)`. The generic construction works for every nowhere
differentiable real function. A rational-indicator example makes the hypotheses
nonvacuous; the exercise does not require the original function to be continuous.
-/

@[expose] public section

open Set
namespace Rudin.Chapter09

noncomputable def exercise26Lift (g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := g p.1

/-- The inner derivative genuinely exists, independently of regularity in `x`. -/
theorem exercise26_second_partial (g : ℝ → ℝ) (x y : ℝ) :
    HasDerivAt (fun t ↦ exercise26Lift g (x,t)) 0 y :=
  hasDerivAt_const y (g x)

/-- The mixed derivative is a derivative of the proved inner derivative. -/
theorem exercise26_mixed_partial (g : ℝ → ℝ) (x y : ℝ) :
    HasDerivAt (fun s ↦ deriv (fun t ↦ exercise26Lift g (s,t)) y) 0 x := by
  simpa only [fun s ↦ (exercise26_second_partial g s y).deriv] using
    hasDerivAt_const x (0 : ℝ)

theorem exercise26_mixed_continuous (g : ℝ → ℝ) :
    Continuous (fun p : ℝ × ℝ ↦
      deriv (fun s ↦ deriv (fun t ↦ exercise26Lift g (s,t)) p.2) p.1) := by
  simpa only [fun x y ↦ (exercise26_mixed_partial g x y).deriv] using
    (continuous_const : Continuous (fun _ : ℝ × ℝ ↦ (0 : ℝ)))

theorem exercise26_first_nowhere {g : ℝ → ℝ}
    (hg : ∀ x, ¬ DifferentiableAt ℝ g x) (x y : ℝ) :
    ¬ DifferentiableAt ℝ (fun s ↦ exercise26Lift g (s,y)) x := hg x

open Classical in
noncomputable def exercise26Nowhere (x : ℝ) : ℝ := if Irrational x then 0 else 1

/-- Density on both sides gives a concrete nowhere differentiable function. -/
theorem exercise26_nowhere_not_continuous (x : ℝ) :
    ¬ ContinuousAt exercise26Nowhere x := by
  classical
  intro hc
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  by_cases hx : Irrational x
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - δ < x + δ by linarith)
    have hd : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hb := hbound hd
    norm_num [exercise26Nowhere, hx] at hb
  · obtain ⟨r, hr, hr1, hr2⟩ := exists_irrational_btwn (show x - δ < x + δ by linarith)
    have hd : dist r x < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hb := hbound hd
    norm_num [exercise26Nowhere, hx, hr] at hb

theorem exercise26_nowhere_not_differentiable (x : ℝ) :
    ¬ DifferentiableAt ℝ exercise26Nowhere x :=
  fun h ↦ exercise26_nowhere_not_continuous x h.continuousAt

/-- One actual function has a continuous mixed partial and no first partial anywhere. -/
theorem exercise26_example :
    (∀ x y, HasDerivAt (fun t ↦ exercise26Lift exercise26Nowhere (x,t)) 0 y) ∧
    (∀ x y, HasDerivAt
      (fun s ↦ deriv (fun t ↦ exercise26Lift exercise26Nowhere (s,t)) y) 0 x) ∧
    Continuous (fun p : ℝ × ℝ ↦
      deriv (fun s ↦ deriv (fun t ↦ exercise26Lift exercise26Nowhere (s,t)) p.2) p.1) ∧
    ∀ x y, ¬ DifferentiableAt ℝ
      (fun s ↦ exercise26Lift exercise26Nowhere (s,y)) x :=
  ⟨exercise26_second_partial _, exercise26_mixed_partial _, exercise26_mixed_continuous _,
    exercise26_first_nowhere exercise26_nowhere_not_differentiable⟩

end Rudin.Chapter09
