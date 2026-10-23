module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Chapter 8, Exercise 9
Source: book page 197, PDF page 206. The decimal scale is between 10^43 and 10^44.
-/

@[expose] public section

open Filter Topology

namespace Rudin.Chapter08

noncomputable def exercise09_sum (N : ℕ) : ℝ := ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 1)

theorem exercise09_sum_eq_harmonic (N : ℕ) : exercise09_sum N = (harmonic N : ℝ) := by
  simp [exercise09_sum, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast]

theorem exercise09_a :
    Tendsto (fun N : ℕ ↦ exercise09_sum N - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  simpa only [exercise09_sum_eq_harmonic] using Real.tendsto_harmonic_sub_log

theorem exercise09_b :
    exercise09_sum (10 ^ 43) < 100 ∧ 100 < exercise09_sum (10 ^ 44) := by
  have hloglo : (2.3025850926 : ℝ) < Real.log 10 := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hloghi : Real.log 10 < (2.3025850934 : ℝ) := by
    rw [Real.log_ten_eq]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  constructor
  · have h := Real.strictAnti_eulerMascheroniSeq'.antitone (show 6 ≤ 10 ^ 43 by norm_num)
    have h6 := Real.eulerMascheroniSeq'_six_lt_two_thirds
    have hb : (harmonic (10 ^ 43) : ℝ) - 43 * Real.log 10 < 2 / 3 := by
      have hn : (10 : ℕ) ^ 43 ≠ 0 := by positivity
      simp only [Real.eulerMascheroniSeq', ite_eq_right hn] at h
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
      exact lt_of_le_of_lt h h6
    rw [exercise09_sum_eq_harmonic]
    norm_num only [Nat.reducePow] at hb ⊢
    linarith only [hb, hloghi]
  · have h := log_add_one_le_harmonic (10 ^ 44)
    have hl : Real.log ((10 : ℝ) ^ 44) ≤ Real.log (((10 : ℕ) ^ 44 + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [Real.log_pow] at hl
    rw [exercise09_sum_eq_harmonic]
    push_cast at h
    norm_num only [Nat.cast_ofNat] at h hl
    norm_num only [Nat.reducePow] at h hl ⊢
    linarith only [h, hl, hloglo]

/-- Among integral decimal exponents, 44 is the first that suffices. -/
theorem exercise09_decimal_threshold (m : ℕ) :
    100 < exercise09_sum (10 ^ m) ↔ 44 ≤ m := by
  have hs : Monotone exercise09_sum := by
    intro a b hab
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    intro i _ _
    positivity
  constructor
  · intro h
    by_contra hm
    have hm' : m ≤ 43 := by omega
    have hp : (10 : ℕ) ^ m ≤ 10 ^ 43 := by gcongr
    exact (not_lt_of_ge (hs hp)) (exercise09_b.1.trans h)
  · intro hm
    have hp : (10 : ℕ) ^ 44 ≤ 10 ^ m := by gcongr
    exact exercise09_b.2.trans_le (hs hp)

end Rudin.Chapter08
