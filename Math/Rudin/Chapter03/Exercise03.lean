module

public import Mathlib

/-! # Exercise 3.3: the nested radical sequence.

Index zero represents Rudin's index one. The update is `sqrt (2 + sqrt s)`,
not `sqrt (2 + s)`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Rudin.Chapter03

noncomputable def exercise03_sequence : ℕ → ℝ
  | 0 => Real.sqrt 2
  | n + 1 => Real.sqrt (2 + Real.sqrt (exercise03_sequence n))

@[simp] theorem exercise03_initial : exercise03_sequence 0 = Real.sqrt 2 := rfl

@[simp] theorem exercise03_recurrence (n : ℕ) :
    exercise03_sequence (n + 1) = Real.sqrt (2 + Real.sqrt (exercise03_sequence n)) := rfl

/-- Every term is nonnegative and strictly less than two. -/
theorem exercise03_strict_bound (n : ℕ) :
    0 ≤ exercise03_sequence n ∧ exercise03_sequence n < 2 := by
  induction n with
  | zero =>
    constructor
    · exact Real.sqrt_nonneg _
    · exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  | succ n ih =>
    rw [exercise03_recurrence]
    constructor
    · exact Real.sqrt_nonneg _
    · apply (Real.sqrt_lt' (by norm_num)).2
      have h : Real.sqrt (exercise03_sequence n) < 2 :=
        (Real.sqrt_lt' (by norm_num)).2 (by linarith [ih.2])
      linarith

/-- The nested radicals increase. -/
theorem exercise03_monotone : Monotone exercise03_sequence := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    simp only [exercise03_initial, exercise03_recurrence]
    exact Real.sqrt_le_sqrt (by linarith [Real.sqrt_nonneg (Real.sqrt 2)])
  | succ n ih =>
    change Real.sqrt (2 + Real.sqrt (exercise03_sequence n)) ≤
      Real.sqrt (2 + Real.sqrt (exercise03_sequence (n + 1)))
    exact Real.sqrt_le_sqrt (by linarith [Real.sqrt_le_sqrt ih])

/-- The source sequence converges in the ordinary sense. -/
theorem exercise03_convergence :
    ∃ a : ℝ, Tendsto exercise03_sequence atTop (𝓝 a) := by
  exact ⟨_, tendsto_atTop_ciSup exercise03_monotone
    ⟨2, by rintro _ ⟨n, rfl⟩; exact (exercise03_strict_bound n).2.le⟩⟩

end Rudin.Chapter03
