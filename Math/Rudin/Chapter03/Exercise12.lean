module

public import Mathlib

/-! # R03E12: positive convergent series
All source terms have indices at least one. `exercise12_tail a n` is the
source's `r_n`, not a shifted tail. Convergence in the hypotheses means
convergence of ordered partial sums. Summability is obtained only after
using positivity.
-/

@[expose] public section

namespace Rudin.Chapter03
open Filter Topology Finset

noncomputable def exercise12_tail (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, a (k + n)

/-- Positivity makes ordered convergence equivalent to real summability. -/
theorem exercise12_summable (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hc : ∃ s, Tendsto (fun N => ∑ k ∈ range N, a (k + 1)) atTop (nhds s)) :
    Summable a := by
  obtain ⟨s, hs⟩ := hc
  exact (summable_nat_add_iff 1).mp
    ⟨s, (hasSum_iff_tendsto_nat_of_nonneg (fun n => (hp _ (by omega)).le) s).mpr hs⟩

theorem exercise12_tail_pos {a : ℕ → ℝ} (hp : ∀ n ≥ 1, 0 < a n)
    (ha : Summable a) {n : ℕ} (hn : 1 ≤ n) : 0 < exercise12_tail a n := by
  exact ((summable_nat_add_iff n).mpr ha).tsum_pos
    (fun k => (hp _ (by omega)).le) 0 (by simpa using hp n hn)

theorem exercise12_tail_step {a : ℕ → ℝ} (ha : Summable a) (n : ℕ) :
    exercise12_tail a n = a n + exercise12_tail a (n + 1) := by
  simpa [exercise12_tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ((summable_nat_add_iff n).mpr ha).tsum_eq_zero_add

theorem exercise12_tail_antitone {a : ℕ → ℝ} (hp : ∀ n ≥ 1, 0 < a n)
    (ha : Summable a) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    exercise12_tail a n ≤ exercise12_tail a m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := exercise12_tail_step ha (m + k)
    have h := hp (m + k) (by omega)
    have he : m + (k + 1) = m + k + 1 := by omega
    rw [he]
    have hi := ih (by omega)
    linarith

theorem exercise12_tail_sum {a : ℕ → ℝ} (ha : Summable a) (m k : ℕ) :
    ∑ j ∈ range k, a (m + j) = exercise12_tail a m - exercise12_tail a (m + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    have h := exercise12_tail_step ha (m + k)
    have he : m + (k + 1) = m + k + 1 := by omega
    rw [he]
    linarith

/-- R03E12(a): the source's strict inequality, including both endpoints. -/
theorem exercise12_a_inequality (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hc : ∃ s, Tendsto (fun N => ∑ k ∈ range N, a (k + 1)) atTop (nhds s))
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) :
    1 - exercise12_tail a n / exercise12_tail a m <
      ∑ j ∈ range (n + 1 - m), a (m + j) / exercise12_tail a (m + j) := by
  have ha := exercise12_summable a hp hc
  have hr := exercise12_tail_pos hp ha hm
  have hsum : (∑ j ∈ range (n + 1 - m), a (m + j)) / exercise12_tail a m ≤
      ∑ j ∈ range (n + 1 - m), a (m + j) / exercise12_tail a (m + j) := by
    rw [sum_div]
    apply sum_le_sum
    intro j hj
    exact div_le_div_of_nonneg_left (hp _ (by omega)).le
      (exercise12_tail_pos hp ha (by omega))
      (exercise12_tail_antitone hp ha hm (by omega))
  rw [exercise12_tail_sum ha, show m + (n + 1 - m) = n + 1 by omega] at hsum
  have hs := exercise12_tail_step ha n
  have hn := hp n (by omega)
  have hlt : 1 - exercise12_tail a n / exercise12_tail a m <
      (exercise12_tail a m - exercise12_tail a (n + 1)) / exercise12_tail a m := by
    apply (lt_div_iff₀ hr).mpr
    field_simp
    nlinarith
  exact hlt.trans_le hsum

/-- R03E12(a): divergence means failure of ordered convergence. -/
theorem exercise12_a_divergence (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hc : ∃ s, Tendsto (fun N => ∑ k ∈ range N, a (k + 1)) atTop (nhds s)) :
    ¬ ∃ s, Tendsto
      (fun N => ∑ k ∈ range N, a (k + 1) / exercise12_tail a (k + 1)) atTop (nhds s) := by
  have ha := exercise12_summable a hp hc
  let q := fun n => a (n + 1) / exercise12_tail a (n + 1)
  have hq : ∀ n, 0 ≤ q n := fun n =>
    (div_pos (hp _ (by omega)) (exercise12_tail_pos hp ha (by omega))).le
  rintro ⟨s, hs⟩
  have hqs : Summable q := ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hq s).mpr hs⟩
  have bound : ∀ m : ℕ, 1 ≤ ∑' j, q (j + m) := by
    intro m
    have hb : ∀ᶠ n in atTop, 1 - exercise12_tail a n / exercise12_tail a (m + 1) ≤
        ∑' j, q (j + m) := by
      filter_upwards [eventually_gt_atTop (m + 1)] with n hn
      refine (exercise12_a_inequality a hp hc (by omega) hn).le.trans ?_
      have h := ((summable_nat_add_iff m).mpr hqs).sum_le_tsum
        (range (n + 1 - (m + 1))) (fun _ _ => hq _)
      simpa [q, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have ht : Tendsto (fun n => 1 - exercise12_tail a n / exercise12_tail a (m + 1))
        atTop (nhds 1) := by
      simpa [exercise12_tail] using
        (tendsto_const_nhds.sub ((tendsto_sum_nat_add a).div_const (exercise12_tail a (m + 1))))
    exact le_of_tendsto ht hb
  have hz := tendsto_sum_nat_add q
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto hz (Eventually.of_forall bound)
  norm_num at this

/-- R03E12(b): strictness follows from positivity of the next tail. -/
theorem exercise12_b_inequality (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hc : ∃ s, Tendsto (fun N => ∑ k ∈ range N, a (k + 1)) atTop (nhds s))
    {n : ℕ} (hn : 1 ≤ n) :
    a n / Real.sqrt (exercise12_tail a n) <
      2 * (Real.sqrt (exercise12_tail a n) - Real.sqrt (exercise12_tail a (n + 1))) := by
  have ha := exercise12_summable a hp hc
  have hr := exercise12_tail_pos hp ha hn
  have ht := exercise12_tail_pos hp ha (show 1 ≤ n + 1 by omega)
  have hs := exercise12_tail_step ha n
  have hn' := hp n hn
  have hx := Real.sqrt_pos.mpr hr
  have hy := Real.sqrt_pos.mpr ht
  have hxy : Real.sqrt (exercise12_tail a (n + 1)) < Real.sqrt (exercise12_tail a n) :=
    Real.sqrt_lt_sqrt ht.le (by linarith)
  have hx2 := Real.sq_sqrt hr.le
  have hy2 := Real.sq_sqrt ht.le
  apply (div_lt_iff₀ hx).mpr
  nlinarith [sq_pos_of_pos (sub_pos.mpr hxy)]

/-- R03E12(b): both summability and ordered convergence of the transformed
positive series. -/
theorem exercise12_b_convergence (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hc : ∃ s, Tendsto (fun N => ∑ k ∈ range N, a (k + 1)) atTop (nhds s)) :
    Summable (fun k => a (k + 1) / Real.sqrt (exercise12_tail a (k + 1))) ∧
    ∃ s, Tendsto (fun N => ∑ k ∈ range N,
      a (k + 1) / Real.sqrt (exercise12_tail a (k + 1))) atTop (nhds s) := by
  have ha := exercise12_summable a hp hc
  have hp' : ∀ k, 0 ≤ a (k + 1) / Real.sqrt (exercise12_tail a (k + 1)) := by
    intro k
    exact div_nonneg (hp _ (by omega)).le (Real.sqrt_nonneg _)
  have hb : ∀ N, (∑ k ∈ range N, a (k + 1) / Real.sqrt (exercise12_tail a (k + 1))) +
      2 * Real.sqrt (exercise12_tail a (N + 1)) ≤ 2 * Real.sqrt (exercise12_tail a 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have h := exercise12_b_inequality a hp hc (show 1 ≤ N + 1 by omega)
      linarith
  have hsum := summable_of_sum_range_le hp' (fun N =>
    (le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).trans (hb N))
  exact ⟨hsum, ⟨_, hsum.hasSum.tendsto_sum_nat⟩⟩

end Rudin.Chapter03
