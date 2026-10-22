module

public import Mathlib

@[expose] public section

open Filter Set
open scoped BigOperators Topology

namespace Rudin.Chapter07

noncomputable section

/-- The source term with positive index `n + 1`. -/
def exercise06Term (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * ((x ^ 2 + (n + 1 : ℝ)) / (n + 1 : ℝ) ^ 2)

def exercise06PartialSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, exercise06Term n x

/-- The absolutely summable quadratic coefficient. -/
def exercise06Quadratic (n : ℕ) : ℝ := (-1 : ℝ) ^ (n + 1) / (n + 1 : ℝ) ^ 2

/-- The conditionally convergent, ordered alternating harmonic coefficient. -/
def exercise06Harmonic (n : ℕ) : ℝ := (-1 : ℝ) ^ (n + 1) / (n + 1 : ℝ)

theorem exercise06_source_term (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    exercise06Term (n - 1) x = (-1 : ℝ) ^ n * ((x ^ 2 + n) / (n : ℝ) ^ 2) := by
  have h : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast Nat.sub_add_cancel hn
  simp only [exercise06Term, Nat.sub_add_cancel hn, h]

theorem exercise06_split (n : ℕ) (x : ℝ) :
    exercise06Term n x = x ^ 2 * exercise06Quadratic n + exercise06Harmonic n := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold exercise06Term exercise06Quadratic exercise06Harmonic
  field_simp

theorem exercise06_p_series : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

theorem exercise06_quadratic_norm (n : ℕ) :
    ‖exercise06Quadratic n‖ = 1 / (n + 1 : ℝ) ^ 2 := by
  simp [exercise06Quadratic, norm_div, norm_pow, Real.norm_of_nonneg (by positivity :
    (0 : ℝ) ≤ n + 1)]

theorem exercise06_quadratic_summable : Summable exercise06Quadratic := by
  apply exercise06_p_series.of_norm_bounded
  intro n
  exact (exercise06_quadratic_norm n).le

/-- Only ordinary natural partial-sum convergence is asserted for this coefficient.
In particular the alternating harmonic series is never assumed `Summable`. -/
theorem exercise06_harmonic_converges :
    ∃ b : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, exercise06Harmonic n)
      atTop (𝓝 b) := by
  have ha : Antitone (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1)
    exact_mod_cast Nat.add_le_add_right hmn 1
  obtain ⟨b, hb⟩ := ha.tendsto_alternating_series_of_tendsto_zero
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨-b, ?_⟩
  convert hb.neg using 1
  ext N
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [exercise06Harmonic, pow_succ]
  ring

/-- The quadratic subseries has a summable uniform majorant on any bounded set. -/
theorem exercise06_quadratic_uniform {E : Set ℝ} {R : ℝ} (_hR : 0 ≤ R)
    (hE : ∀ x ∈ E, |x| ≤ R) :
    TendstoUniformlyOn
      (fun N x => ∑ n ∈ Finset.range N, x ^ 2 * exercise06Quadratic n)
      (fun x => x ^ 2 * ∑' n, exercise06Quadratic n) atTop E := by
  have hu := tendstoUniformlyOn_tsum_nat (exercise06_p_series.mul_left (R ^ 2))
    (f := fun n x => x ^ 2 * exercise06Quadratic n) (s := E) (by
      intro n x hx
      rw [norm_mul, norm_pow, Real.norm_eq_abs, exercise06_quadratic_norm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (abs_nonneg x) (hE x hx) 2)
  simpa only [tsum_mul_left] using hu

/-- A single function is the uniform limit of the ordinary partial sums on every bounded set. -/
theorem exercise06_uniform_on_bounded_sets :
    ∃ b : ℝ, ∀ E : Set ℝ, Bornology.IsBounded E →
      TendstoUniformlyOn exercise06PartialSum
        (fun x => x ^ 2 * (∑' n, exercise06Quadratic n) + b) atTop E := by
  obtain ⟨b, hb⟩ := exercise06_harmonic_converges
  refine ⟨b, fun E hE => ?_⟩
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hE
  have hbound : ∀ x ∈ E, |x| ≤ max r 0 := by
    intro x hx
    have hxr := hr hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxr
    exact hxr.trans (le_max_left _ _)
  have hu := (exercise06_quadratic_uniform (le_max_right r 0) hbound).add
    (hb.tendstoUniformlyOn_const E)
  convert hu using 1
  ext N x
  simp only [Pi.add_apply, exercise06PartialSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  exact exercise06_split n x

/-- Every bounded interval is included, without nonempty or nondegenerate assumptions. -/
theorem exercise06_local_uniform (I : Set ℝ) (hI : Bornology.IsBounded I)
    (_hinterval : OrdConnected I) :
    ∃ f : ℝ → ℝ, TendstoUniformlyOn exercise06PartialSum f atTop I := by
  obtain ⟨b, hb⟩ := exercise06_uniform_on_bounded_sets
  exact ⟨fun x => x ^ 2 * (∑' n, exercise06Quadratic n) + b, hb I hI⟩

/-- In particular the original numerical series converges in its natural order at each real x. -/
theorem exercise06_pointwise (x : ℝ) :
    ∃ s : ℝ, Tendsto (fun N => exercise06PartialSum N x) atTop (𝓝 s) := by
  obtain ⟨b, hb⟩ := exercise06_uniform_on_bounded_sets
  exact ⟨x ^ 2 * (∑' n, exercise06Quadratic n) + b,
    (hb {x} Bornology.isBounded_singleton).tendsto_at (mem_singleton x)⟩

theorem exercise06_abs_term (n : ℕ) (x : ℝ) :
    |exercise06Term n x| = (x ^ 2 + (n + 1 : ℝ)) / (n + 1 : ℝ) ^ 2 := by
  rw [exercise06Term, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (by positivity)]

theorem exercise06_harmonic_le_abs (n : ℕ) (x : ℝ) :
    1 / (n + 1 : ℝ) ≤ |exercise06Term n x| := by
  rw [exercise06_abs_term]
  have hn : (0 : ℝ) < n + 1 := by positivity
  apply (div_le_div_iff₀ hn (sq_pos_of_pos hn)).mpr
  nlinarith [mul_nonneg (sq_nonneg x) hn.le]

/-- The comparison is with a nonnegative harmonic series, so `Summable` is applicable. -/
theorem exercise06_not_summable_abs (x : ℝ) :
    ¬ Summable (fun n => |exercise06Term n x|) := by
  intro h
  have hh : Summable (fun n : ℕ => 1 / (n + 1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => exercise06_harmonic_le_abs n x) h
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).mp (by
    simpa only [Nat.cast_add, Nat.cast_one] using hh)

/-- At no real parameter do the ordinary absolute partial sums have a finite limit. -/
theorem exercise06_nowhere_absolute (x : ℝ) :
    ¬ ∃ s : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, |exercise06Term n x|)
      atTop (𝓝 s) := by
  rintro ⟨s, hs⟩
  exact exercise06_not_summable_abs x
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n => abs_nonneg (exercise06Term n x)) s).mpr
      hs).summable

end

end Rudin.Chapter07
