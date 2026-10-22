module

public import Mathlib

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Rudin.Chapter07

noncomputable section

/-- The source term with positive index `n + 1`. -/
def exercise04Term (n : ℕ) (x : ℝ) : ℝ :=
  1 / (1 + (n + 1 : ℝ) ^ 2 * x ^ 2)

/-- The first `N` source terms, in their natural order. -/
def exercise04PartialSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, exercise04Term n x

/-- This total expression is used as a sum only at nonzero arguments. -/
noncomputable def exercise04Sum (x : ℝ) : ℝ := ∑' n, exercise04Term n x

theorem exercise04_source_term (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    exercise04Term (n - 1) x = 1 / (1 + (n : ℝ) ^ 2 * x ^ 2) := by
  have h : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simp [exercise04Term, h]

theorem exercise04_term_nonneg (n : ℕ) (x : ℝ) : 0 ≤ exercise04Term n x := by
  unfold exercise04Term
  positivity

theorem exercise04_term_bound {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) (n : ℕ) :
    exercise04Term n x ≤ (1 / δ ^ 2) * (1 / (n + 1 : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hx2 : δ ^ 2 ≤ x ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hx 2
  have hd : 0 < (n + 1 : ℝ) ^ 2 * δ ^ 2 := by positivity
  calc
    exercise04Term n x ≤ 1 / ((n + 1 : ℝ) ^ 2 * δ ^ 2) := by
      apply one_div_le_one_div_of_le hd
      nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg (n + 1 : ℝ))]
    _ = (1 / δ ^ 2) * (1 / (n + 1 : ℝ) ^ 2) := by
      simp only [one_div, mul_inv_rev]

theorem exercise04_majorant (δ : ℝ) :
    Summable (fun n : ℕ => (1 / δ ^ 2) * (1 / (n + 1 : ℝ) ^ 2)) := by
  apply Summable.mul_left
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

/-- The use of unconditional summability here is justified by a positive majorant. -/
theorem exercise04_summable {x : ℝ} (hx : x ≠ 0) :
    Summable (fun n => exercise04Term n x) := by
  exact Summable.of_nonneg_of_le (fun n => exercise04_term_nonneg n x)
    (fun n => exercise04_term_bound (abs_pos.mpr hx) le_rfl n)
    (exercise04_majorant |x|)

theorem exercise04_summable_iff (x : ℝ) :
    Summable (fun n => exercise04Term n x) ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    simp [exercise04Term, summable_const_iff] at h
  · exact exercise04_summable

/-- Absolute convergence means convergence of the ordinary absolute partial sums. -/
theorem exercise04_absolute_domain (x : ℝ) :
    (∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, |exercise04Term n x|)
      atTop (𝓝 s)) ↔ x ≠ 0 := by
  simp_rw [abs_of_nonneg (exercise04_term_nonneg _ _)]
  constructor
  · rintro ⟨s, hs⟩
    exact (exercise04_summable_iff x).mp
      ((hasSum_iff_tendsto_nat_of_nonneg (fun n => exercise04_term_nonneg n x) s).mpr
        hs).summable
  · intro hx
    exact ⟨exercise04Sum x, (exercise04_summable hx).tendsto_sum_tsum_nat⟩

/-- The displayed sum is the limit of the actual ordered partial sums. -/
theorem exercise04_pointwise {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun N => exercise04PartialSum N x) atTop (𝓝 (exercise04Sum x)) :=
  (exercise04_summable hx).tendsto_sum_tsum_nat

theorem exercise04_zero_partialSum (N : ℕ) : exercise04PartialSum N 0 = N := by
  simp [exercise04PartialSum, exercise04Term]

/-- There is no ordinary finite sum at zero. -/
theorem exercise04_zero_diverges :
    ¬ ∃ s : ℝ, Tendsto (fun N => exercise04PartialSum N 0) atTop (𝓝 s) := by
  rintro ⟨s, hs⟩
  have h := ((hasSum_iff_tendsto_nat_of_nonneg
    (fun n => exercise04_term_nonneg n 0) s).mpr hs).summable
  simp [exercise04Term, summable_const_iff] at h

theorem exercise04_uniform_of_away {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ x ∈ E, δ ≤ |x|) :
    TendstoUniformlyOn exercise04PartialSum exercise04Sum atTop E := by
  apply tendstoUniformlyOn_tsum_nat (exercise04_majorant δ)
  intro n x hx
  rw [Real.norm_of_nonneg (exercise04_term_nonneg n x)]
  exact exercise04_term_bound hδ (hE x hx) n

theorem exercise04_half_le_term (n : ℕ) {x : ℝ}
    (hx : (n + 1 : ℝ) * |x| ≤ 1) : 1 / 2 ≤ exercise04Term n x := by
  have ha : 0 ≤ (n + 1 : ℝ) * |x| := by positivity
  have hs : ((n + 1 : ℝ) * |x|) ^ 2 ≤ 1 := by nlinarith
  have hd : 0 < 1 + (n + 1 : ℝ) ^ 2 * x ^ 2 := by positivity
  rw [exercise04Term, le_div_iff₀ hd]
  simp only [mul_pow, sq_abs] at hs
  nlinarith

/-- Necessity holds for a uniform limit of ordinary partial sums, regardless of its name. -/
theorem exercise04_uniform_away {E : Set ℝ} {g : ℝ → ℝ}
    (h : TendstoUniformlyOn exercise04PartialSum g atTop E) :
    ∃ δ > 0, ∀ x ∈ E, δ ≤ |x| := by
  obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp h.uniformCauchySeqOn)
    (1 / 2) (by norm_num)
  refine ⟨1 / (N + 1 : ℝ), by positivity, ?_⟩
  intro x hx
  by_contra hsmall
  have hs : (N + 1 : ℝ) * |x| ≤ 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < N + 1)).mp (lt_of_not_ge hsmall)
    nlinarith
  have hb := exercise04_half_le_term N hs
  have hc := hN (N + 1) (by omega) N le_rfl x hx
  have hid : exercise04PartialSum (N + 1) x - exercise04PartialSum N x =
      exercise04Term N x := by simp [exercise04PartialSum, Finset.sum_range_succ]
  rw [Real.dist_eq, hid, abs_of_nonneg (exercise04_term_nonneg N x)] at hc
  linarith

/-- Complete classification for all sets, hence for every kind of interval.
The empty set is included; any set containing zero is excluded. -/
theorem exercise04_uniform_iff (E : Set ℝ) :
    TendstoUniformlyOn exercise04PartialSum exercise04Sum atTop E ↔
      ∃ δ > 0, ∀ x ∈ E, δ ≤ |x| :=
  ⟨exercise04_uniform_away, fun ⟨_, hδ, hE⟩ => exercise04_uniform_of_away hδ hE⟩

/-- This also classifies existence of any uniform ordinary partial-sum limit. -/
theorem exercise04_uniform_intervals (I : Set ℝ) (_hI : OrdConnected I) :
    (∃ g : ℝ → ℝ, TendstoUniformlyOn exercise04PartialSum g atTop I) ↔
      ∃ δ > 0, ∀ x ∈ I, δ ≤ |x| := by
  exact ⟨fun ⟨_, h⟩ => exercise04_uniform_away h,
    fun h => ⟨exercise04Sum, (exercise04_uniform_iff I).mpr h⟩⟩

/-- Intervals approaching zero from either side fail, even if zero is omitted. -/
theorem exercise04_not_uniform_of_approaches_zero {E : Set ℝ}
    (hE : ∀ δ > 0, ∃ x ∈ E, |x| < δ) (g : ℝ → ℝ) :
    ¬ TendstoUniformlyOn exercise04PartialSum g atTop E := by
  intro h
  obtain ⟨δ, hδ, hb⟩ := exercise04_uniform_away h
  obtain ⟨x, hx, hlt⟩ := hE δ hδ
  exact (not_lt_of_ge (hb x hx)) hlt

theorem exercise04_uniform_empty :
    TendstoUniformlyOn exercise04PartialSum exercise04Sum atTop ∅ := by
  exact (exercise04_uniform_iff ∅).mpr ⟨1, by norm_num, by simp⟩

theorem exercise04_uniform_singleton_iff (x : ℝ) :
    TendstoUniformlyOn exercise04PartialSum exercise04Sum atTop {x} ↔ x ≠ 0 := by
  rw [exercise04_uniform_iff]
  constructor
  · rintro ⟨δ, hδ, h⟩ hx
    have := h x (by simp)
    simp [hx] at this
    linarith
  · intro hx
    exact ⟨|x|, abs_pos.mpr hx, by simp⟩

theorem exercise04_term_continuous (n : ℕ) : Continuous (exercise04Term n) := by
  unfold exercise04Term
  apply continuous_const.div
    (continuous_const.add (continuous_const.mul (continuous_id.pow 2)))
  intro x
  change 1 + (n + 1 : ℝ) ^ 2 * x ^ 2 ≠ 0
  exact ne_of_gt (by positivity)

theorem exercise04_continuousAt {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt exercise04Sum x := by
  let E : Set ℝ := {y | |x| / 2 < |y|}
  have hpos : 0 < |x| := abs_pos.mpr hx
  have hu := exercise04_uniform_of_away (E := E) (by positivity : 0 < |x| / 2)
    (fun y hy => le_of_lt hy)
  have hc : ContinuousOn exercise04Sum E := hu.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun N =>
      (continuous_finsetSum _ (fun n _ => exercise04_term_continuous n)).continuousOn)))
  exact hc.continuousAt
    ((isOpen_lt continuous_const continuous_abs).mem_nhds (by dsimp [E]; linarith))

/-- Continuity at every point of the full convergence domain. -/
theorem exercise04_continuity : ContinuousOn exercise04Sum {x : ℝ | x ≠ 0} :=
  fun _ hx => (exercise04_continuousAt hx).continuousWithinAt

/-- The first `N` terms already have size at least `N/2` at this nonzero point. -/
theorem exercise04_large_value (N : ℕ) :
    (N : ℝ) / 2 ≤ exercise04Sum (1 / (N + 1 : ℝ)) := by
  have hx : (1 / (N + 1 : ℝ)) ≠ 0 := by positivity
  calc
    (N : ℝ) / 2 = ∑ n ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
    _ ≤ exercise04PartialSum N (1 / (N + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      apply exercise04_half_le_term
      rw [abs_of_pos (by positivity : 0 < 1 / (N + 1 : ℝ))]
      have hnN : (n + 1 : ℝ) ≤ N + 1 := by
        exact_mod_cast Nat.add_le_add_right (Finset.mem_range.mp hn).le 1
      rw [mul_one_div, div_le_one₀ (by positivity : (0 : ℝ) < N + 1)]
      exact hnN
    _ ≤ exercise04Sum (1 / (N + 1 : ℝ)) :=
      Summable.sum_le_tsum _ (fun n _ => exercise04_term_nonneg n _) (exercise04_summable hx)

/-- The actual sum is unbounded above on its full domain, not just near an undefined value. -/
theorem exercise04_unbounded : ∀ M : ℝ, ∃ x : ℝ, x ≠ 0 ∧ M < exercise04Sum x := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M)
  refine ⟨1 / (N + 1 : ℝ), by positivity, ?_⟩
  have := exercise04_large_value N
  linarith

end

end Rudin.Chapter07
