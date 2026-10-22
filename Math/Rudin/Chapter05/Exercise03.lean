module

public import Mathlib

@[expose] public section

open Set

namespace Rudin.Chapter05

/-- The admissible positive parameters depend only on the derivative bound.
For `M = 0` there is no upper bound. For `M > 0` this is `0 < ε < 1 / M`. -/
def exercise03_admissible (M ε : ℝ) : Prop := 0 < ε ∧ ε * M < 1

theorem exercise03_admissible_zero (ε : ℝ) :
    exercise03_admissible 0 ε ↔ 0 < ε := by
  simp [exercise03_admissible]

theorem exercise03_admissible_pos {M ε : ℝ} (hM : 0 < M) :
    exercise03_admissible M ε ↔ 0 < ε ∧ ε < 1 / M := by
  rw [exercise03_admissible, lt_div_iff₀ hM]

/-- Every nonnegative bound admits a positive parameter. -/
theorem exercise03_admissible_nonempty {M : ℝ} (hM : 0 ≤ M) :
    ∃ ε, exercise03_admissible M ε := by
  refine ⟨1 / (M + 1), one_div_pos.mpr (by linarith), ?_⟩
  rw [one_div_mul_eq_div, div_lt_one (by linarith)]
  linarith

/-- Exercise 3: the indicated perturbation is in fact strictly increasing. -/
theorem exercise03_strictMono (g : ℝ → ℝ) (M ε : ℝ)
    (hg : Differentiable ℝ g) (hbound : ∀ x, |deriv g x| ≤ M)
    (hε : exercise03_admissible M ε) : StrictMono (fun x => x + ε * g x) := by
  apply strictMono_of_deriv_pos
  intro x
  have hd : HasDerivAt (fun t => t + ε * g t) (1 + ε * deriv g x) x :=
    (hasDerivAt_id x).add ((hg x).hasDerivAt.const_mul ε)
  rw [hd.deriv]
  have hb := (abs_le.mp (hbound x)).1
  have hm := mul_le_mul_of_nonneg_left hb hε.1.le
  dsimp [exercise03_admissible] at hε
  nlinarith [hε.2]

/-- Exercise 3: injectivity for all admissible positive parameters. -/
theorem exercise03_injectivity (g : ℝ → ℝ) (M ε : ℝ)
    (hg : Differentiable ℝ g) (hbound : ∀ x, |deriv g x| ≤ M)
    (hε : exercise03_admissible M ε) : Function.Injective (fun x => x + ε * g x) :=
  (exercise03_strictMono g M ε hg hbound hε).injective

/-- The upper bound is sharp as a guarantee using only `M`: a linear example
fails to be injective at and beyond the bound. -/
theorem exercise03_sharp {M ε : ℝ} (hε : 0 < ε) (hM : 1 ≤ ε * M) :
    ∃ g : ℝ → ℝ, Differentiable ℝ g ∧ (∀ x, |deriv g x| ≤ M) ∧
      ¬ Function.Injective (fun x => x + ε * g x) := by
  refine ⟨fun x => -(x / ε), by fun_prop, ?_, ?_⟩
  · intro x
    have hd : HasDerivAt (fun x : ℝ => -(x / ε)) (-(1 / ε)) x :=
      ((hasDerivAt_id x).div_const ε).neg
    rw [hd.deriv, abs_neg, abs_of_pos (one_div_pos.mpr hε)]
    exact (div_le_iff₀ hε).mpr (by nlinarith)
  · intro hi
    have heq : (0 : ℝ) + ε * -(0 / ε) = 1 + ε * -(1 / ε) := by
      field_simp [ne_of_gt hε]
      ring
    have hh := hi (a₁ := 0) (a₂ := 1) heq
    norm_num at hh

end Rudin.Chapter05
