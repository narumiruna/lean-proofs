module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter07

/-- Positive integer dilations on the source interval. -/
def exercise15Dilates (f : ℝ → ℝ) (n : ℕ) (t : Icc (0 : ℝ) 1) : ℝ :=
  f ((n + 1 : ℝ) * t)

/-- Equicontinuity forces constancy precisely on the nonnegative half-line.
No condition on negative arguments is needed for this equivalence. -/
theorem exercise15_classification (f : ℝ → ℝ) :
    Equicontinuous (exercise15Dilates f) ↔ ∀ x, 0 ≤ x → f x = f 0 := by
  constructor
  · intro he x hx
    apply eq_of_forall_dist_le
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.equicontinuousAt_iff.mp
      (he ⟨0, by constructor <;> norm_num⟩) ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (x / δ))
    have hn0 : (0 : ℝ) < n + 1 := by positivity
    have hnx : x < n + 1 := lt_trans (lt_of_le_of_lt (le_max_left _ _) hn) (by linarith)
    have hnδ : x / δ < n + 1 := lt_trans (lt_of_le_of_lt (le_max_right _ _) hn) (by linarith)
    have ht : x / (n + 1 : ℝ) ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx hn0.le, (div_le_one hn0).mpr hnx.le⟩
    have htd : dist (⟨x / (n + 1 : ℝ), ht⟩ : Icc (0 : ℝ) 1)
        ⟨0, by constructor <;> norm_num⟩ < δ := by
      change |x / (n + 1 : ℝ) - 0| < δ
      rw [sub_zero, abs_of_nonneg ht.1, div_lt_iff₀ hn0]
      have := (div_lt_iff₀ hδ).mp hnδ
      nlinarith
    have h := hd ⟨x / (n + 1 : ℝ), ht⟩ htd n
    simp only [exercise15Dilates, mul_zero, mul_div_cancel₀ _ (ne_of_gt hn0)] at h
    exact (dist_comm (f x) (f 0) ▸ h).le
  · intro h
    have heq : exercise15Dilates f = fun (_ : ℕ) (_ : Icc (0 : ℝ) 1) => f 0 := by
      funext n t
      exact h _ (mul_nonneg (by positivity) t.property.1)
    rw [heq]
    exact equicontinuous_iff_continuous.mpr continuous_const

/-- Continuous functions are classified by the same half-line restriction. -/
theorem exercise15_continuous_classification (f : ℝ → ℝ) :
    (Continuous f ∧ Equicontinuous (exercise15Dilates f)) ↔
      Continuous f ∧ ∀ x, 0 ≤ x → f x = f 0 := by
  rw [exercise15_classification]

/-- The negative half-line need not be constant, even under the source continuity hypothesis. -/
theorem exercise15_nonconstant_example :
    Continuous (fun x : ℝ => min x 0) ∧
    Equicontinuous (exercise15Dilates (fun x : ℝ => min x 0)) ∧
    (min (-1 : ℝ) 0 ≠ min (0 : ℝ) 0) := by
  refine ⟨continuous_id.min continuous_const, (exercise15_classification _).mpr ?_, by norm_num⟩
  intro x hx
  simp [min_eq_right hx]

end Rudin.Chapter07
