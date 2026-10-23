module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Basic

/-! # Chapter 11, Exercise 13

The points are the almost-everywhere classes of the literal functions
`x ↦ sin ((n+1)*x)` for Lebesgue measure restricted to `[-π,π]`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace Rudin.Chapter11

namespace SineL2

abbrev μ : Measure ℝ := volume.restrict (Icc (-Real.pi) Real.pi)
abbrev Space := Lp ℝ 2 μ

theorem memLp_sin (n : ℕ) : MemLp (fun x : ℝ ↦ Real.sin ((n : ℝ) * x)) 2 μ := by
  apply MemLp.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall fun x ↦ Real.abs_sin_le_one _

/-- The `L²` class of the positive integer frequency `n+1`. -/
def sine (n : ℕ) : Space := (memLp_sin (n + 1)).toLp _

theorem sine_ae (n : ℕ) : sine n =ᵐ[μ] (fun x : ℝ ↦ Real.sin (((n+1 : ℕ) : ℝ) * x)) :=
  (memLp_sin (n + 1)).coeFn_toLp

theorem integral_cos_int (n : ℤ) (hn : n ≠ 0) :
    (∫ x in -Real.pi..Real.pi, Real.cos ((n : ℝ) * x)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [intervalIntegral.integral_comp_mul_left _ hn', integral_cos]
  simp [Real.sin_int_mul_pi, mul_neg]

theorem integral_sine_mul (n m : ℕ) :
    (∫ x in -Real.pi..Real.pi,
      Real.sin (((n+1 : ℕ) : ℝ) * x) * Real.sin (((m+1 : ℕ) : ℝ) * x)) =
      if n = m then Real.pi else 0 := by
  have hi (k : ℤ) : IntervalIntegrable (fun x : ℝ ↦ Real.cos ((k : ℝ) * x))
      volume (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have he (x : ℝ) :
      Real.sin (((n+1 : ℕ) : ℝ) * x) * Real.sin (((m+1 : ℕ) : ℝ) * x) =
      (Real.cos (((n : ℤ) - m : ℤ) * x) -
        Real.cos (((n : ℤ) + m + 2 : ℤ) * x)) / 2 := by
    push_cast
    rw [show ((n : ℝ) - m) * x = ((n : ℝ) + 1) * x - ((m : ℝ) + 1) * x by ring,
      show ((n : ℝ) + m + 2) * x = ((n : ℝ) + 1) * x + ((m : ℝ) + 1) * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _) (hi _),
    integral_cos_int ((n : ℤ) + m + 2) (by omega)]
  by_cases h : n = m
  · subst m
    simp
  · rw [integral_cos_int _ (by omega)]
    simp [h]

theorem inner_sine (n m : ℕ) :
    inner ℝ (sine n) (sine m) = if n = m then Real.pi else 0 := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial] at *
  calc
    _ = ∫ x, Real.sin (((n+1 : ℕ) : ℝ) * x) *
        Real.sin (((m+1 : ℕ) : ℝ) * x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [sine_ae n, sine_ae m] with x hn hm
      simp only [hn, hm, mul_comm]
    _ = _ := ?_
  change (∫ x in Icc (-Real.pi) Real.pi, _) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact integral_sine_mul n m

theorem norm_sine_sq (n : ℕ) : ‖sine n‖ ^ 2 = Real.pi := by
  simpa [real_inner_self_eq_norm_sq] using inner_sine n n

theorem norm_sine (n : ℕ) : ‖sine n‖ = Real.sqrt Real.pi := by
  rw [← norm_sine_sq n, Real.sqrt_sq (norm_nonneg _)]

/-- The actual distance between two distinct sine classes. -/
theorem dist_sine {n m : ℕ} (h : n ≠ m) :
    dist (sine n) (sine m) = Real.sqrt (2 * Real.pi) := by
  rw [dist_eq_norm]
  have he : ‖sine n - sine m‖ ^ 2 = 2 * Real.pi := by
    rw [norm_sub_sq_real, norm_sine_sq, norm_sine_sq, inner_sine, ite_eq_right h]
    ring
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

theorem closedEmbedding_sine : IsClosedEmbedding sine := by
  apply Metric.isClosedEmbedding_of_pairwise_le_dist (Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi))
  intro n m h
  exact (dist_sine h).ge

/-- Normalized sine classes, used for the Bessel inequality in Exercise 17. -/
def normalized (n : ℕ) : Space := (Real.sqrt Real.pi)⁻¹ • sine n

theorem orthonormal_normalized : Orthonormal ℝ normalized := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalized, inner_smul_left, inner_smul_right, conj_trivial, inner_sine]
  by_cases h : n = m
  · simp only [h, ite_true]
    have hπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    have hs := Real.sq_sqrt Real.pi_pos.le
    field_simp
    nlinarith
  · simp [h]

/-- Bessel's inequality forces each fixed vector's sine coefficients to zero. -/
theorem tendsto_inner_sine (f : Space) :
    Tendsto (fun n ↦ inner ℝ (sine n) f) atTop (𝓝 0) := by
  have h := (orthonormal_normalized.inner_products_summable f).tendsto_atTop_zero
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hnorm
  have hi : Tendsto (fun n ↦ inner ℝ (normalized n) f) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hm := hi.const_mul (Real.sqrt Real.pi)
  simpa [normalized, inner_smul_left, mul_assoc, Real.sqrt_ne_zero'.mpr Real.pi_pos] using hm

/-- The actual Lebesgue indicator belongs to `L²`; no Riemann hypothesis is needed. -/
theorem memLp_indicator {E : Set ℝ} (hE : NullMeasurableSet E volume) :
    MemLp (E.indicator (fun _ : ℝ ↦ (1 : ℝ))) 2 μ :=
  (memLp_const 1).indicator (hE.mono Measure.restrict_le_self)

def indicator {E : Set ℝ} (hE : NullMeasurableSet E volume) : Space :=
  (memLp_indicator hE).toLp _

theorem inner_sine_indicator {E : Set ℝ} (hE : NullMeasurableSet E volume)
    (hsub : E ⊆ Icc (-Real.pi) Real.pi) (n : ℕ) :
    inner ℝ (sine n) (indicator hE) =
      ∫ x in E, Real.sin (((n+1 : ℕ) : ℝ) * x) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, E.indicator (fun x : ℝ ↦ Real.sin (((n+1 : ℕ) : ℝ) * x)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [sine_ae n, (memLp_indicator hE).coeFn_toLp] with x hn hI
      change inner ℝ (sine n x) ((memLp_indicator hE).toLp _ x) = _
      rw [hn, hI]
      by_cases hx : x ∈ E <;> simp [hx, RCLike.inner_apply]
    _ = _ := by
      rw [integral_indicator₀ (hE.mono Measure.restrict_le_self)]
      rw [Measure.restrict_restrict_of_subset hsub]

theorem tendsto_setIntegral_sine {E : Set ℝ} (hE : NullMeasurableSet E volume)
    (hsub : E ⊆ Icc (-Real.pi) Real.pi) :
    Tendsto (fun n : ℕ ↦ ∫ x in E, Real.sin (((n+1 : ℕ) : ℝ) * x)) atTop (𝓝 0) := by
  simpa only [inner_sine_indicator hE hsub] using tendsto_inner_sine (indicator hE)

end SineL2

/-- Closedness of the set of positive-frequency sine classes. -/
theorem exercise13_closedness : IsClosed (range SineL2.sine) :=
  SineL2.closedEmbedding_sine.isClosed_range

/-- Every class has norm `sqrt π`. -/
theorem exercise13_boundedness : Bornology.IsBounded (range SineL2.sine) := by
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨Real.sqrt Real.pi, by rintro _ ⟨n, rfl⟩; exact (SineL2.norm_sine n).le⟩

/-- Positive separation prevents compactness. -/
theorem exercise13_noncompactness : ¬ IsCompact (range SineL2.sine) := by
  intro h
  have hc : IsCompact (univ : Set ℕ) :=
    SineL2.closedEmbedding_sine.isEmbedding.isCompact_iff.mpr (by simpa using h)
  exact Set.infinite_univ (hc.finite_of_discrete)

end Rudin.Chapter11
