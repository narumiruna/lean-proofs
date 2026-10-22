module

public import Mathlib

/-! # Exercise 2.11 (PDF page 53)
Only the second and fifth proposed distances are metrics. The other three
have explicit axiom failures.
-/

@[expose] public section
namespace Rudin.Chapter02

def distanceOne (x y : ℝ) : ℝ := (x - y) ^ 2
noncomputable def distanceTwo (x y : ℝ) : ℝ := Real.sqrt |x - y|
def distanceThree (x y : ℝ) : ℝ := |x ^ 2 - y ^ 2|
def distanceFour (x y : ℝ) : ℝ := |x - 2 * y|
noncomputable def distanceFive (x y : ℝ) : ℝ := |x - y| / (1 + |x - y|)

/-- All metric axioms, with nonnegativity stated explicitly. -/
def IsMetricDistance {X : Type*} (d : X → X → ℝ) : Prop :=
  (∀ x y, 0 ≤ d x y) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧
  (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

/-- Squared distance fails the triangle inequality at 0, 1, 2. -/
theorem distanceOne_triangle_failure :
    distanceOne 0 2 > distanceOne 0 1 + distanceOne 1 2 := by
  norm_num [distanceOne]

theorem distanceOne_not_metric : ¬ IsMetricDistance distanceOne := by
  intro h
  exact (not_le_of_gt distanceOne_triangle_failure) (h.2.2.2 0 1 2)

theorem distanceTwo_metric : IsMetricDistance distanceTwo := by
  refine ⟨fun x y => Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · intro x y
    simp [distanceTwo, Real.sqrt_eq_zero (abs_nonneg _), sub_eq_zero]
  · intro x y
    simp only [distanceTwo, abs_sub_comm]
  · intro x y z
    have htri := abs_sub_le x y z
    have ha := Real.sq_sqrt (abs_nonneg (x - y))
    have hb := Real.sq_sqrt (abs_nonneg (y - z))
    have hc := Real.sq_sqrt (abs_nonneg (x - z))
    have hprod := mul_nonneg (Real.sqrt_nonneg |x - y|) (Real.sqrt_nonneg |y - z|)
    have hsum : 0 ≤ Real.sqrt |x - y| + Real.sqrt |y - z| := by positivity
    change Real.sqrt |x - z| ≤ Real.sqrt |x - y| + Real.sqrt |y - z|
    nlinarith [Real.sqrt_nonneg |x - z|]

/-- Distinct points 1 and -1 have zero third distance. -/
theorem distanceThree_separation_failure :
    (1 : ℝ) ≠ -1 ∧ distanceThree 1 (-1) = 0 := by
  norm_num [distanceThree]

theorem distanceThree_not_metric : ¬ IsMetricDistance distanceThree := by
  intro h
  exact distanceThree_separation_failure.1
    ((h.2.1 1 (-1)).mp distanceThree_separation_failure.2)

/-- The fourth distance is nonzero on the diagonal at 1. -/
theorem distanceFour_diagonal_failure : distanceFour 1 1 ≠ 0 := by
  norm_num [distanceFour]

/-- The fourth distance is also asymmetric. -/
theorem distanceFour_symmetry_failure : distanceFour 0 1 ≠ distanceFour 1 0 := by
  norm_num [distanceFour]

theorem distanceFour_not_metric : ¬ IsMetricDistance distanceFour := by
  intro h
  exact distanceFour_diagonal_failure ((h.2.1 1 1).mpr rfl)

/-- The bounded transformation of a nonnegative triangle inequality. -/
theorem bounded_transform_triangle {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : c ≤ a + b) :
    c / (1 + c) ≤ a / (1 + a) + b / (1 + b) := by
  have h1 : 0 < 1 + c := by positivity
  have h2 : 0 < 1 + a + b := by positivity
  calc
    c / (1 + c) ≤ (a + b) / (1 + a + b) := by
      apply (div_le_div_iff₀ h1 h2).mpr
      nlinarith
    _ = a / (1 + a + b) + b / (1 + a + b) := add_div _ _ _
    _ ≤ a / (1 + a) + b / (1 + b) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left ha (by positivity) (by linarith)
      · exact div_le_div_of_nonneg_left hb (by positivity) (by linarith)

theorem distanceFive_metric : IsMetricDistance distanceFive := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    exact div_nonneg (abs_nonneg _) (by positivity)
  · intro x y
    have h : (1 + |x - y|) ≠ 0 := ne_of_gt (by positivity)
    simp [distanceFive, div_eq_zero_iff, h, sub_eq_zero]
  · intro x y
    simp only [distanceFive, abs_sub_comm]
  · intro x y z
    exact bounded_transform_triangle (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
      (abs_sub_le x y z)

/-- Complete classification of the five formulas. -/
theorem exercise11 :
    ¬ IsMetricDistance distanceOne ∧ IsMetricDistance distanceTwo ∧
    ¬ IsMetricDistance distanceThree ∧ ¬ IsMetricDistance distanceFour ∧
    IsMetricDistance distanceFive :=
  ⟨distanceOne_not_metric, distanceTwo_metric, distanceThree_not_metric,
    distanceFour_not_metric, distanceFive_metric⟩
end Rudin.Chapter02
