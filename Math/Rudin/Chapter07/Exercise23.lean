module

public import Mathlib

/-! # Chapter 7, Exercise 23
The literal polynomial recursion, its geometric error estimate, and uniform
convergence on the closed interval. Source: book page 169, PDF page 178.
-/

@[expose] public section

open Set Filter Polynomial
open scoped Topology BigOperators

namespace Rudin.Chapter07

noncomputable section

/-- Explicit primitive recursion avoids generated unsafe recursion helpers. -/
def exercise23Polynomial : ℕ → ℝ[X] :=
  Nat.rec 0 (fun _ p => p + C (1 / 2) * (X ^ 2 - p ^ 2))

@[simp] theorem exercise23_zero : exercise23Polynomial 0 = 0 := rfl

theorem exercise23_succ (n : ℕ) :
    exercise23Polynomial (n + 1) = exercise23Polynomial n +
      C (1 / 2) * (X ^ 2 - exercise23Polynomial n ^ 2) := rfl

def exercise23Value (n : ℕ) (x : ℝ) : ℝ := (exercise23Polynomial n).eval x

@[simp] theorem exercise23Value_zero (x : ℝ) : exercise23Value 0 x = 0 := by
  simp [exercise23Value]

theorem exercise23Value_succ (n : ℕ) (x : ℝ) :
    exercise23Value (n + 1) x = exercise23Value n x +
      (x ^ 2 - exercise23Value n x ^ 2) / 2 := by
  simp [exercise23Value, exercise23_succ]
  ring

theorem exercise23_error_identity (n : ℕ) (x : ℝ) :
    |x| - exercise23Value (n + 1) x =
      (|x| - exercise23Value n x) * (1 - (|x| + exercise23Value n x) / 2) := by
  rw [exercise23Value_succ]
  nlinarith [sq_abs x]

theorem exercise23_bounds (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ exercise23Value n x ∧ exercise23Value n x ≤ |x| := by
  induction n with
  | zero => simp [abs_nonneg]
  | succ n ih =>
    have hs : exercise23Value n x ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
    constructor
    · rw [exercise23Value_succ]
      linarith [ih.1]
    · have hfac : 0 ≤ 1 - (|x| + exercise23Value n x) / 2 := by linarith
      have hprod := mul_nonneg (sub_nonneg.mpr ih.2) hfac
      rw [← exercise23_error_identity] at hprod
      linarith

theorem exercise23_monotone_bounds (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ exercise23Value n x ∧
    exercise23Value n x ≤ exercise23Value (n + 1) x ∧
    exercise23Value (n + 1) x ≤ |x| := by
  have h := exercise23_bounds n hx
  refine ⟨h.1, ?_, (exercise23_bounds (n + 1) hx).2⟩
  rw [exercise23Value_succ]
  nlinarith [sq_abs x]

theorem exercise23_geometric_error (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |x| - exercise23Value n x ≤ |x| * (1 - |x| / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := exercise23_bounds n hx
    have hr : 0 ≤ 1 - |x| / 2 := by linarith
    rw [exercise23_error_identity, pow_succ]
    calc
      _ ≤ (|x| - exercise23Value n x) * (1 - |x| / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr h.2)
      _ ≤ (|x| * (1 - |x| / 2) ^ n) * (1 - |x| / 2) :=
        mul_le_mul_of_nonneg_right ih hr
      _ = _ := by ring

/-- A finite geometric sum proves the strict bound also at `x = 0`. -/
theorem exercise23_strict_error (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |x| * (1 - |x| / 2) ^ n < 2 / (n + 1 : ℝ) := by
  let r : ℝ := 1 - |x| / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r ≤ 1 := by dsimp [r]; linarith [abs_nonneg x]
  have hsum : (n + 1 : ℝ) * r ^ n ≤ ∑ i ∈ Finset.range (n + 1), r ^ i := by
    calc
      _ = ∑ _i ∈ Finset.range (n + 1), r ^ n := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        pow_le_pow_of_le_one hr.le hr1 (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  have hmul := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hr1)
  have he := geom_sum_mul_neg r (n + 1)
  have hp : 0 < r ^ (n + 1) := pow_pos hr _
  have ht : (n + 1 : ℝ) * r ^ n * (1 - r) < 1 := by linarith
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  dsimp [r] at ht ⊢
  nlinarith

theorem exercise23_error_bound (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |x| - exercise23Value n x ≤ |x| * (1 - |x| / 2) ^ n ∧
      |x| * (1 - |x| / 2) ^ n < 2 / (n + 1 : ℝ) :=
  ⟨exercise23_geometric_error n hx, exercise23_strict_error n hx⟩

theorem exercise23_uniform_absolute_value :
    TendstoUniformlyOn exercise23Value abs atTop (Icc (-1 : ℝ) 1) := by
  have ht : Tendsto (fun n : ℕ => 2 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
  have hax : |x| ≤ 1 := abs_le.mpr hx
  have hb := exercise23_bounds n hax
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hb.2)]
  exact (exercise23_geometric_error n hax).trans_lt
    ((exercise23_strict_error n hax).trans hn)

end

end Rudin.Chapter07
