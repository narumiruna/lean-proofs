module

public import Mathlib

/-!
# R03E15: series in finite-dimensional Euclidean space

Source: Rudin, Third Edition, book page 81 (PDF page 90).
Convergence means convergence of ordered natural partial sums. It is not
Mathlib's unconditional `Summable` predicate. Series are indexed from zero;
the root test retains the source's positive indices and exponents. A finite
initial term does not affect convergence.
-/

@[expose] public section

namespace Rudin.Chapter03

open Set Filter Topology

/-- The ordered partial sums, before term `n`. -/
def exercise15_partialSum {E : Type*} [AddCommMonoid E] (a : ℕ → E) (n : ℕ) : E :=
  ∑ i ∈ Finset.range n, a i

/-- Ordinary series convergence, including conditionally convergent series. -/
def exercise15_converges {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (a : ℕ → E) : Prop :=
  ∃ A : E, Tendsto (exercise15_partialSum a) atTop (𝓝 A)

theorem exercise15_terms_tend_zero {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (h : exercise15_converges a) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := h
  have hs := (hA.comp (tendsto_add_atTop_nat 1)).sub hA
  simpa [exercise15_partialSum, Finset.sum_range_succ] using hs

/-- Unconditional summability is used only as a sufficient conclusion. -/
theorem exercise15_converges_of_summable {E : Type*} [AddCommMonoid E]
    [TopologicalSpace E] {a : ℕ → E} (h : Summable a) :
    exercise15_converges a :=
  ⟨∑' n, a n, h.hasSum.tendsto_sum_nat⟩

theorem exercise15_absolute_implies_convergent {k : ℕ}
    {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (h : exercise15_converges (fun n => ‖a n‖)) : exercise15_converges a := by
  obtain ⟨A, hA⟩ := h
  have ha : Summable (fun n => ‖a n‖) :=
    ⟨A, (hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (a n)) A).mpr hA⟩
  exact exercise15_converges_of_summable (ha.of_norm)

theorem exercise15_comparison {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    {c : ℕ → ℝ} (hc : exercise15_converges c)
    (hbound : ∀ᶠ n in atTop, ‖a n‖ ≤ c n) : exercise15_converges a := by
  obtain ⟨C, hC⟩ := hc
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have hreal : CauchySeq (fun m => ∑ i ∈ Finset.range m, c (N + i)) := by
    have hs := (hC.comp (tendsto_add_atTop_nat N)).sub_const (exercise15_partialSum c N)
    simpa only [Function.comp_apply, exercise15_partialSum, Nat.add_comm _ N,
      Finset.sum_range_add, add_sub_cancel_left] using hs.cauchySeq
  have hv : CauchySeq (fun m => ∑ i ∈ Finset.range m, a (N + i)) :=
    cauchySeq_range_of_norm_bounded hreal (fun i => hN _ (Nat.le_add_right N i))
  have hs : CauchySeq (fun m => exercise15_partialSum a (m + N)) := by
    have hv' : CauchySeq (fun m => exercise15_partialSum a N +
        ∑ i ∈ Finset.range m, a (N + i)) := hv.const_add
    simpa only [exercise15_partialSum, Nat.add_comm _ N, Finset.sum_range_add] using hv'
  exact cauchySeq_tendsto_of_complete ((cauchySeq_shift N).mp hs)

theorem exercise15_addition {k : ℕ} {a b : ℕ → EuclideanSpace ℝ (Fin k)}
    {A B : EuclideanSpace ℝ (Fin k)}
    (ha : Tendsto (exercise15_partialSum a) atTop (𝓝 A))
    (hb : Tendsto (exercise15_partialSum b) atTop (𝓝 B)) :
    Tendsto (exercise15_partialSum (fun n => a n + b n)) atTop (𝓝 (A + B)) := by
  change Tendsto (fun N => ∑ n ∈ Finset.range N, (a n + b n)) atTop (𝓝 (A + B))
  simp only [Finset.sum_add_distrib]
  exact ha.add hb

theorem exercise15_scalar_multiplication {k : ℕ}
    {a : ℕ → EuclideanSpace ℝ (Fin k)} {A : EuclideanSpace ℝ (Fin k)}
    (ha : Tendsto (exercise15_partialSum a) atTop (𝓝 A)) (c : ℝ) :
    Tendsto (exercise15_partialSum (fun n => c • a n)) atTop (𝓝 (c • A)) := by
  change Tendsto (fun N => ∑ n ∈ Finset.range N, c • a n) atTop (𝓝 (c • A))
  simp only [← Finset.smul_sum]
  exact ha.const_smul c

theorem exercise15_dirichlet {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    {b : ℕ → ℝ} (hb : Antitone b) (hz : Tendsto b atTop (𝓝 0))
    (hbounded : ∃ M : ℝ, ∀ n, ‖exercise15_partialSum a n‖ ≤ M) :
    exercise15_converges (fun n => b n • a n) := by
  obtain ⟨M, hM⟩ := hbounded
  exact cauchySeq_tendsto_of_complete
    (hb.cauchySeq_series_mul_of_tendsto_zero_of_bounded hz hM)

theorem exercise15_rearrangements {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin k)} (habs : exercise15_converges (fun n => ‖a n‖))
    (ha : Tendsto (exercise15_partialSum a) atTop (𝓝 A)) (e : ℕ ≃ ℕ) :
    Tendsto (exercise15_partialSum (fun n => a (e n))) atTop (𝓝 A) := by
  obtain ⟨B, hB⟩ := habs
  have hn : Summable (fun n => ‖a n‖) :=
    ⟨B, (hasSum_iff_tendsto_nat_of_nonneg (fun n => norm_nonneg (a n)) B).mpr hB⟩
  have hs : HasSum a A := (hasSum_iff_tendsto_nat_of_summable_norm hn).mpr ha
  exact (e.hasSum_iff.mpr hs).tendsto_sum_nat

/-- The source's inclusive-tail Cauchy criterion, with its non-strict bound. -/
theorem exercise15_cauchy_criterion {k : ℕ} (a : ℕ → EuclideanSpace ℝ (Fin k)) :
    exercise15_converges a ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n,
      ‖∑ i ∈ Finset.Icc n m, a i‖ ≤ ε := by
  constructor
  · rintro ⟨A, hA⟩ ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hA.cauchySeq (ε / 2) (by linarith)
    refine ⟨N, fun n hn m hmn => ?_⟩
    have hd := hN (m + 1) (by omega) n hn
    rw [dist_eq_norm] at hd
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sub a (by omega)]
    exact hd.le.trans (by linarith)
  · intro h
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    by_cases he : n = N
    · simp [he, hε]
    have hb := hN N le_rfl (n - 1) (by omega)
    rw [← Finset.Ico_add_one_right_eq_Icc,
      show n - 1 + 1 = n by omega, Finset.sum_Ico_eq_sub a hn] at hb
    rw [dist_eq_norm]
    exact hb.trans_lt (by linarith)

/-- The extended nonnegative upper root limit; finite initial terms are ignored. -/
noncomputable def exercise15_rootLimsup {k : ℕ} (a : ℕ → EuclideanSpace ℝ (Fin k)) : ENNReal :=
  limsup (fun n => ENNReal.ofReal (‖a (n + 1)‖ ^ (((n + 1 : ℕ) : ℝ)⁻¹))) atTop

theorem exercise15_root_convergence {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (h : exercise15_rootLimsup a < 1) : exercise15_converges a := by
  obtain ⟨q, hqL, hq1⟩ := exists_between h
  have hqtop : q ≠ ⊤ := ne_top_of_lt (hq1.trans ENNReal.one_lt_top)
  have hq0 : q ≠ 0 := ne_of_gt ((bot_le : (0 : ENNReal) ≤ exercise15_rootLimsup a).trans_lt hqL)
  let r := q.toReal
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqtop
  have hr1 : r < 1 := by
    simpa [r] using (ENNReal.toReal_lt_toReal hqtop (by simp)).mpr hq1
  have hq : ENNReal.ofReal r = q := ENNReal.ofReal_toReal hqtop
  have he : ∀ᶠ n in atTop, ‖a (n + 1)‖ ^ (((n + 1 : ℕ) : ℝ)⁻¹) < r := by
    have hh := eventually_lt_of_limsup_lt hqL
    filter_upwards [hh] with n hn
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mp (hq ▸ hn)
  have hb : ∀ᶠ n in atTop, ‖a (n + 1)‖ ≤ r ^ (n + 1) := by
    filter_upwards [he] with n hn
    calc
      ‖a (n + 1)‖ = (‖a (n + 1)‖ ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ^ (n + 1) :=
        (Real.rpow_inv_natCast_pow (norm_nonneg _) (by omega)).symm
      _ ≤ r ^ (n + 1) := pow_le_pow_left₀ (Real.rpow_nonneg (norm_nonneg _) _) hn.le _
  have hg : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0.le hr1)
  have ha : Summable (fun n => a (n + 1)) :=
    Summable.of_norm_bounded_eventually hg (by simpa only [Nat.cofinite_eq_atTop] using hb)
  exact exercise15_converges_of_summable ((summable_nat_add_iff 1).mp ha)

theorem exercise15_root_divergence {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (h : 1 < exercise15_rootLimsup a) : ¬ exercise15_converges a := by
  intro hs
  have hz : Tendsto (fun n => ‖a (n + 1)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero] using
      (exercise15_terms_tend_zero hs).norm.comp (tendsto_add_atTop_nat 1)
  have he : ∀ᶠ n in atTop,
      ENNReal.ofReal (‖a (n + 1)‖ ^ (((n + 1 : ℕ) : ℝ)⁻¹)) ≤ 1 := by
    filter_upwards [hz (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one (norm_nonneg _) hn.le (by positivity))
  exact h.not_ge (limsup_le_of_le (h := he))

noncomputable def exercise15_ratioLimsup {k : ℕ} (a : ℕ → EuclideanSpace ℝ (Fin k)) : ENNReal :=
  limsup (fun n => ENNReal.ofReal (‖a (n + 1)‖ / ‖a n‖)) atTop

theorem exercise15_ratio_convergence {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (hnonzero : ∀ᶠ n in atTop, a n ≠ 0) (h : exercise15_ratioLimsup a < 1) :
    exercise15_converges a := by
  obtain ⟨q, hqL, hq1⟩ := exists_between h
  have hqtop : q ≠ ⊤ := ne_top_of_lt (hq1.trans ENNReal.one_lt_top)
  have hq0 : q ≠ 0 := ne_of_gt ((bot_le : (0 : ENNReal) ≤ exercise15_ratioLimsup a).trans_lt hqL)
  let r := q.toReal
  have hr0 : 0 < r := ENNReal.toReal_pos hq0 hqtop
  have hr1 : r < 1 := by
    simpa [r] using (ENNReal.toReal_lt_toReal hqtop (by simp)).mpr hq1
  have hq : ENNReal.ofReal r = q := ENNReal.ofReal_toReal hqtop
  have he : ∀ᶠ n in atTop, ‖a (n + 1)‖ ≤ r * ‖a n‖ := by
    filter_upwards [eventually_lt_of_limsup_lt hqL, hnonzero] with n hn hz
    have hh := (ENNReal.ofReal_lt_ofReal_iff hr0).mp (hq ▸ hn)
    exact ((div_lt_iff₀ (norm_pos_iff.mpr hz)).mp hh).le
  exact exercise15_converges_of_summable (summable_of_ratio_norm_eventually_le hr1 he)

theorem exercise15_ratio_divergence {k : ℕ} {a : ℕ → EuclideanSpace ℝ (Fin k)}
    (hnonzero : ∀ᶠ n in atTop, a n ≠ 0)
    (h : ∀ᶠ n in atTop, 1 ≤ ‖a (n + 1)‖ / ‖a n‖) :
    ¬ exercise15_converges a := by
  intro hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hnonzero.and h)
  have hstep (n : ℕ) (hn : N ≤ n) : ‖a n‖ ≤ ‖a (n + 1)‖ := by
    simpa using (le_div_iff₀ (norm_pos_iff.mpr (hN n hn).1)).mp (hN n hn).2
  have hlower (m : ℕ) : ‖a N‖ ≤ ‖a (N + m)‖ := by
    induction m with
    | zero => simp
    | succ m ih => exact ih.trans (hstep _ (Nat.le_add_right N m))
  have hz : Tendsto (fun n => ‖a n‖) atTop (𝓝 0) := by
    simpa using (exercise15_terms_tend_zero hs).norm
  obtain ⟨m, hm⟩ := eventually_atTop.mp
    (hz (gt_mem_nhds (norm_pos_iff.mpr (hN N le_rfl).1)))
  exact (not_lt_of_ge (hlower m)) (hm (N + m) (Nat.le_add_left m N))

/-- Every vector series converges in the zero-dimensional space. -/
theorem exercise15_dimension_zero (a : ℕ → EuclideanSpace ℝ (Fin 0)) :
    exercise15_converges a ∧ exercise15_rootLimsup a = 0 := by
  have ha : a = fun _ => 0 := Subsingleton.elim _ _
  subst a
  constructor
  · exact exercise15_converges_of_summable summable_zero
  · unfold exercise15_rootLimsup
    have hf : (fun n : ℕ => ENNReal.ofReal ((0 : ℝ) ^ (((n + 1 : ℕ) : ℝ)⁻¹))) =
        fun _ => 0 := by
      funext n
      rw [Real.zero_rpow (by positivity), ENNReal.ofReal_zero]
    simp only [norm_zero]
    rw [hf, limsup_const]

/-- In each positive dimension, upper root limit one does not decide convergence. -/
theorem exercise15_root_boundary (k : ℕ) (hk : 0 < k) :
    ∃ a b : ℕ → EuclideanSpace ℝ (Fin k),
      exercise15_converges a ∧ ¬ exercise15_converges b ∧
      exercise15_rootLimsup a = 1 ∧ exercise15_rootLimsup b = 1 := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨v, hv⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin k)) (show (0 : ℝ) ≤ 1 by norm_num)
  let a : ℕ → EuclideanSpace ℝ (Fin k) := fun n => (n : ℝ) ^ (-2 : ℝ) • v
  let b : ℕ → EuclideanSpace ℝ (Fin k) := fun _ => v
  have ha : exercise15_converges a := exercise15_converges_of_summable
    ((Real.summable_nat_rpow.mpr (show (-2 : ℝ) < -1 by norm_num)).smul_const v)
  have hb : ¬ exercise15_converges b := by
    intro hs
    have hh : Tendsto b atTop (𝓝 v) := tendsto_const_nhds
    have he : v = 0 := tendsto_nhds_unique hh (exercise15_terms_tend_zero hs)
    simp [he] at hv
  have hroot : Tendsto
      (fun n : ℕ => ‖a (n + 1)‖ ^ (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 1) := by
    have hp := (tendsto_rpow_div_mul_add (-2) 1 0 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    convert hp using 1
    ext n
    simp only [a, norm_smul, Real.norm_eq_abs, hv, mul_one, one_mul, add_zero, Function.comp_def]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) _),
      ← Real.rpow_mul (Nat.cast_nonneg (n + 1))]
    congr 1
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · exact (ENNReal.tendsto_ofReal hroot).limsup_eq.trans (by simp)
  · simp [exercise15_rootLimsup, b, hv]

end Rudin.Chapter03
