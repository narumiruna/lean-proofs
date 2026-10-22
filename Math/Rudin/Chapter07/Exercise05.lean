module

public import Mathlib

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Rudin.Chapter07

noncomputable section

/-- The literal source function with index `n + 1`; both endpoints are included. -/
def exercise05Term (n : ℕ) (x : ℝ) : ℝ :=
  if x ∈ Icc (1 / (n + 2 : ℝ)) (1 / (n + 1 : ℝ)) then
    Real.sin (Real.pi / x) ^ 2 else 0

def exercise05PartialSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, exercise05Term n x

noncomputable def exercise05Sum (x : ℝ) : ℝ := ∑' n, exercise05Term n x

theorem exercise05_source_term (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    exercise05Term (n - 1) x =
      if 1 / (n + 1 : ℝ) ≤ x ∧ x ≤ 1 / (n : ℝ) then
        Real.sin (Real.pi / x) ^ 2 else 0 := by
  have h : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  have h' : ((n - 1 : ℕ) : ℝ) + 2 = n + 1 := by linarith
  simp [exercise05Term, h, h']

theorem exercise05_nonneg (n : ℕ) (x : ℝ) : 0 ≤ exercise05Term n x := by
  unfold exercise05Term
  split_ifs <;> positivity

theorem exercise05_sin_reciprocal (m : ℕ) :
    Real.sin (Real.pi / (1 / (m : ℝ))) ^ 2 = 0 := by
  simp [div_eq_mul_inv, mul_comm, Real.sin_nat_mul_pi]

theorem exercise05_endpoints (n : ℕ) :
    exercise05Term n (1 / (n + 2 : ℝ)) = 0 ∧
      exercise05Term n (1 / (n + 1 : ℝ)) = 0 := by
  have h1 : Real.sin (Real.pi / (1 / (n + 1 : ℝ))) ^ 2 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using exercise05_sin_reciprocal (n + 1)
  have h2 : Real.sin (Real.pi / (1 / (n + 2 : ℝ))) ^ 2 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using exercise05_sin_reciprocal (n + 2)
  simp [exercise05Term, h1, h2]

theorem exercise05_zero (n : ℕ) : exercise05Term n 0 = 0 := by
  simp [exercise05Term]

/-- At each real point only finitely many source functions can be nonzero. -/
theorem exercise05_eventually_zero (x : ℝ) :
    ∀ᶠ n in atTop, exercise05Term n x = 0 := by
  by_cases hx : 0 < x
  · have he : ∀ᶠ n : ℕ in atTop, 1 / (n + 1 : ℝ) < x :=
      (tendsto_order.mp tendsto_one_div_add_atTop_nhds_zero_nat).2 x hx
    filter_upwards [he] with n hn
    apply if_neg
    intro hm
    exact (not_le_of_gt hn) hm.2
  · apply Filter.Eventually.of_forall
    intro n
    apply if_neg
    intro hm
    have hp : 0 < 1 / (n + 2 : ℝ) := by positivity
    exact hx (lt_of_lt_of_le hp hm.1)

/-- Pointwise convergence on all of `ℝ`, including zero and support endpoints. -/
theorem exercise05_pointwise_limit (x : ℝ) :
    Tendsto (fun n => exercise05Term n x) atTop (𝓝 0) := by
  exact tendsto_const_nhds.congr' (exercise05_eventually_zero x).symm

theorem exercise05_limit_continuity : Continuous (fun _ : ℝ => (0 : ℝ)) :=
  continuous_const

/-- A point strictly inside the `n + 1` support where the function has value one. -/
def exercise05Peak (n : ℕ) : ℝ := 1 / (n + 1 + (1 / 2 : ℝ))

theorem exercise05_peak_mem (n : ℕ) :
    exercise05Peak n ∈ Icc (1 / (n + 2 : ℝ)) (1 / (n + 1 : ℝ)) := by
  constructor
  · apply one_div_le_one_div_of_le (by positivity : 0 < (n + 1 + (1 / 2 : ℝ)))
    linarith
  · apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1)
    linarith

theorem exercise05_peak_value (n : ℕ) : exercise05Term n (exercise05Peak n) = 1 := by
  have hphase : Real.pi / exercise05Peak n =
      Real.pi / 2 + ((n + 1 : ℕ) : ℝ) * Real.pi := by
    unfold exercise05Peak
    simp only [div_div, div_one, Nat.cast_add, Nat.cast_one]
    ring
  rw [exercise05Term, if_pos (exercise05_peak_mem n), hphase,
    Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]
  simp [← pow_mul, Nat.mul_comm _ 2, pow_mul]

/-- The sequence does not converge uniformly to its continuous pointwise limit. -/
theorem exercise05_sequence_not_uniform :
    ¬ TendstoUniformlyOn exercise05Term (fun _ => 0) atTop (univ : Set ℝ) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp h (1 / 2) (by norm_num))
  have hp := hN N le_rfl (exercise05Peak N) (mem_univ _)
  rw [exercise05_peak_value] at hp
  norm_num at hp

/-- There is no other possible uniform limit either. -/
theorem exercise05_sequence_no_uniform_limit :
    ¬ ∃ g : ℝ → ℝ, TendstoUniformlyOn exercise05Term g atTop univ := by
  rintro ⟨g, hg⟩
  have heq : g = fun _ => 0 := funext fun x =>
    tendsto_nhds_unique (hg.tendsto_at (mem_univ x)) (exercise05_pointwise_limit x)
  exact exercise05_sequence_not_uniform (heq ▸ hg)

/-- Finite pointwise support justifies the use of `Summable`. -/
theorem exercise05_summable (x : ℝ) : Summable (fun n => exercise05Term n x) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (exercise05_eventually_zero x)
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  exact hN n (by simpa only [Finset.mem_range, not_lt] using hn)

/-- The same positive functional series converges absolutely at every real point.
The conclusion is about ordinary absolute partial sums, not only a total `tsum`. -/
theorem exercise05_series_absolute (x : ℝ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, |exercise05Term n x|)
      atTop (𝓝 (exercise05Sum x)) := by
  simp_rw [abs_of_nonneg (exercise05_nonneg _ _)]
  exact (exercise05_summable x).tendsto_sum_tsum_nat

theorem exercise05_series_pointwise (x : ℝ) :
    Tendsto (fun N => exercise05PartialSum N x) atTop (𝓝 (exercise05Sum x)) :=
  (exercise05_summable x).tendsto_sum_tsum_nat

/-- Uniform convergence of these ordinary partial sums would force the terms uniformly to zero. -/
theorem exercise05_series_no_uniform_limit (g : ℝ → ℝ) :
    ¬ TendstoUniformlyOn exercise05PartialSum g atTop (univ : Set ℝ) := by
  intro h
  obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp h.uniformCauchySeqOn)
    (1 / 2) (by norm_num)
  have hc := hN (N + 1) (by omega) N le_rfl (exercise05Peak N) (mem_univ _)
  have hid : exercise05PartialSum (N + 1) (exercise05Peak N) -
      exercise05PartialSum N (exercise05Peak N) = 1 := by
    simp [exercise05PartialSum, Finset.sum_range_succ, exercise05_peak_value]
  rw [Real.dist_eq, hid] at hc
  norm_num at hc

theorem exercise05_series_not_uniform :
    ¬ TendstoUniformlyOn exercise05PartialSum exercise05Sum atTop (univ : Set ℝ) :=
  exercise05_series_no_uniform_limit exercise05Sum

end

end Rudin.Chapter07
