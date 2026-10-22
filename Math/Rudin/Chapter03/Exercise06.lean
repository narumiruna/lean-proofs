module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

noncomputable section

open Filter Finset Set
open scoped Topology

namespace Rudin.Chapter03

/-- Part (a): partial sums tend to positive infinity. Indices are `n+1`. -/
theorem exercise06_a : Tendsto
    (fun N => ∑ n ∈ range N, (Real.sqrt (n + 2 : ℝ) - Real.sqrt (n + 1 : ℝ)))
    atTop atTop := by
  have heq : ∀ N, (∑ n ∈ range N,
      (Real.sqrt (n + 2 : ℝ) - Real.sqrt (n + 1 : ℝ))) = Real.sqrt (N + 1 : ℝ) - 1 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih]
      simp only [Nat.cast_succ, add_assoc, one_add_one_eq_two]
      ring
  simp_rw [heq]
  exact tendsto_atTop_add_const_right atTop (-1 : ℝ)
    (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right atTop (1 : ℝ)
      tendsto_natCast_atTop_atTop))

/-- Part (b) converges, in fact absolutely. -/
theorem exercise06_b : Summable (fun n : ℕ =>
    (Real.sqrt (n + 2 : ℝ) - Real.sqrt (n + 1 : ℝ)) / (n + 1 : ℝ)) := by
  have hp : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
    simpa using (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2))
  apply Summable.of_nonneg_of_le (fun n => by
    exact div_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))) (by positivity)) _ hp
  intro n
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hs : (0 : ℝ) < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 hn
  have hid : (n + 1 : ℝ) ^ (3 / 2 : ℝ) = (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn]
    rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hid, div_le_div_iff₀ hn (mul_pos hn hs)]
  have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ n + 1 by positivity)
  have hsq2 := Real.sq_sqrt (show (0 : ℝ) ≤ n + 2 by positivity)
  have hm := Real.sqrt_le_sqrt (show (n + 1 : ℝ) ≤ n + 2 by linarith)
  have hc : (Real.sqrt (n + 2 : ℝ) - Real.sqrt (n + 1 : ℝ)) *
      Real.sqrt (n + 1 : ℝ) ≤ 1 := by
    nlinarith [sq_nonneg (Real.sqrt (n + 2 : ℝ) - Real.sqrt (n + 1 : ℝ))]
  nlinarith only [mul_le_mul_of_nonneg_right hc hn.le]

/-- A finite extension used to prove part (c) by geometric comparison. -/
theorem exercise06_c_zero_extension :
    Summable (fun n : ℕ => ((n : ℝ) ^ (1 / (n : ℝ)) - 1) ^ n) := by
  have ht : Tendsto (fun n : ℕ => |(n : ℝ) ^ (1 / (n : ℝ)) - 1|)
      atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_div.comp tendsto_natCast_atTop_atTop).sub_const 1).abs
  apply Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hn n

/-- Part (c), indexed only by the positive integers required by the source. -/
theorem exercise06_c : Summable (fun n : ℕ =>
    ((n + 1 : ℝ) ^ (1 / (n + 1 : ℝ)) - 1) ^ (n + 1)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 exercise06_c_zero_extension

/-- The source's division is defined only on this domain. -/
def exercise06_defined (z : ℂ) : Prop := ∀ n : ℕ, 1 ≤ n → 1 + z ^ n ≠ 0

/-- Exact classification of the undefined parameters by positive powers. -/
theorem exercise06_d_defined_parameters (z : ℂ) :
    exercise06_defined z ↔ ¬ ∃ n : ℕ, 1 ≤ n ∧ z ^ n = -1 := by
  simp only [exercise06_defined, not_exists, not_and]
  congr! 2
  constructor <;> intro h heq <;> apply h <;> linear_combination heq

/-- The undefined parameters are precisely roots of unity with a positive
half-period at which the value is not one (equivalently, even-order roots). -/
theorem exercise06_d_undefined_even (z : ℂ) :
    ¬ exercise06_defined z ↔ ∃ n : ℕ, 1 ≤ n ∧ z ^ (2 * n) = 1 ∧ z ^ n ≠ 1 := by
  rw [exercise06_d_defined_parameters, not_not]
  constructor
  · rintro ⟨n, hn, hz⟩
    refine ⟨n, hn, ?_, ?_⟩
    · rw [mul_comm 2 n, pow_mul, hz]
      norm_num
    · rw [hz]
      norm_num
  · rintro ⟨n, hn, hz, hne⟩
    refine ⟨n, hn, ?_⟩
    have hs : (z ^ n - 1) * (z ^ n + 1) = 0 := by
      rw [mul_comm 2 n, pow_mul] at hz
      linear_combination hz
    rcases mul_eq_zero.mp hs with h | h
    · exact (hne (sub_eq_zero.mp h)).elim
    · linear_combination h

/-- The necessary term test for ordered complex partial sums. -/
theorem exercise06_term_test (f : ℕ → ℂ) (s : ℂ)
    (hs : Tendsto (fun N => ∑ n ∈ range N, f n) atTop (𝓝 s)) :
    Tendsto f atTop (𝓝 0) := by
  have ht := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
  simpa only [Function.comp_def, sum_range_succ, add_sub_cancel_left, sub_self] using ht

/-- Part (d), outside the closed unit disk: absolute convergence. -/
theorem exercise06_d_absolute (z : ℂ) (hz : 1 < ‖z‖) :
    Summable (fun n : ℕ => 1 / (1 + z ^ (n + 1))) := by
  have hz0 : 0 < ‖z‖ := by linarith
  have hg : Summable (fun n : ℕ => 2 * (‖z‖⁻¹) ^ (n + 1)) :=
    ((summable_nat_add_iff 1).2
      (summable_geometric_of_lt_one (inv_nonneg.mpr hz0.le)
        ((inv_lt_one₀ hz0).2 hz))).mul_left 2
  apply Summable.of_norm_bounded_eventually_nat hg
  have ht : Tendsto (fun n : ℕ => ‖z‖ ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hz).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_ge_atTop 2] with n hn
  have htri : ‖z‖ ^ (n + 1) ≤ ‖1 + z ^ (n + 1)‖ + 1 := by
    calc
      _ = ‖(1 + z ^ (n + 1)) - 1‖ := by rw [add_sub_cancel_left, norm_pow]
      _ ≤ ‖1 + z ^ (n + 1)‖ + 1 := by simpa using norm_sub_le (1 + z ^ (n + 1)) (1 : ℂ)
  have hd : 0 < ‖1 + z ^ (n + 1)‖ := by linarith
  rw [norm_div, norm_one, inv_pow, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd (pow_pos hz0 _)).2
  nlinarith

/-- A parameter outside the unit disk has no undefined terms. -/
theorem exercise06_d_defined_of_one_lt (z : ℂ) (hz : 1 < ‖z‖) :
    exercise06_defined z := by
  intro n hn heq
  have hp : 1 < ‖z‖ ^ n := one_lt_pow₀ hz (by omega)
  have heq' : z ^ n = -1 := by linear_combination heq
  rw [← norm_pow, heq'] at hp
  norm_num at hp

/-- Part (d): on the source domain, ordinary convergence holds exactly
outside the unit disk. Undefined parameters are not classified as divergent. -/
theorem exercise06_d_convergence (z : ℂ) (hdef : exercise06_defined z) :
    (∃ s : ℂ, Tendsto (fun N => ∑ n ∈ range N, 1 / (1 + z ^ (n + 1)))
      atTop (𝓝 s)) ↔ 1 < ‖z‖ := by
  constructor
  · rintro ⟨s, hs⟩
    by_contra! hz
    have ht := (exercise06_term_test _ s hs).norm
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (ht.eventually_lt_const (by norm_num : ‖(0 : ℂ)‖ < (1 / 2 : ℝ)))
    have hden : ‖1 + z ^ (N + 1)‖ ≤ 2 := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖z ^ (N + 1)‖ := norm_add_le _ _
        _ ≤ 2 := by
          rw [norm_one, norm_pow]
          linarith [pow_le_one₀ (norm_nonneg z) hz (n := N + 1)]
    have hpos : 0 < ‖1 + z ^ (N + 1)‖ :=
      norm_pos_iff.mpr (hdef (N + 1) (by omega))
    have hlarge : (1 / 2 : ℝ) ≤ ‖1 / (1 + z ^ (N + 1))‖ := by
      rw [norm_div, norm_one]
      exact (le_div_iff₀ hpos).2 (by linarith)
    exact (not_lt_of_ge hlarge) (hN N le_rfl)
  · intro hz
    exact ⟨_, (exercise06_d_absolute z hz).hasSum.tendsto_sum_nat⟩

end Rudin.Chapter03
