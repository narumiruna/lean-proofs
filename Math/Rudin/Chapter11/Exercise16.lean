module

public import Math.Rudin.Chapter11.Exercise13
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Chapter 11, Exercise 16

The convergence set is the exact pointwise convergence set. On that set the
squared difference between terms `k` and `2*k+1` tends to zero. Dominated
convergence and cosine orthogonality force its measure to be zero.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Rudin.Chapter11

namespace CosineL2

open SineL2 (μ Space)

theorem memLp_cos (n : ℕ) : MemLp (fun x : ℝ ↦ Real.cos ((n : ℝ) * x)) 2 μ := by
  apply MemLp.of_bound (by fun_prop) 1
  exact Filter.Eventually.of_forall fun x ↦ Real.abs_cos_le_one _

def cosine (n : ℕ) : Space := (memLp_cos (n + 1)).toLp _

theorem cosine_ae (n : ℕ) : cosine n =ᵐ[μ] (fun x : ℝ ↦ Real.cos (((n+1 : ℕ) : ℝ) * x)) :=
  (memLp_cos (n + 1)).coeFn_toLp

theorem integral_cosine_mul (n m : ℕ) :
    (∫ x in -Real.pi..Real.pi,
      Real.cos (((n+1 : ℕ) : ℝ) * x) * Real.cos (((m+1 : ℕ) : ℝ) * x)) =
      if n = m then Real.pi else 0 := by
  have hi (k : ℤ) : IntervalIntegrable (fun x : ℝ ↦ Real.cos ((k : ℝ) * x))
      volume (-Real.pi) Real.pi := (by fun_prop : Continuous _).intervalIntegrable _ _
  have he (x : ℝ) :
      Real.cos (((n+1 : ℕ) : ℝ) * x) * Real.cos (((m+1 : ℕ) : ℝ) * x) =
      (Real.cos (((n : ℤ) - m : ℤ) * x) +
        Real.cos (((n : ℤ) + m + 2 : ℤ) * x)) / 2 := by
    push_cast
    rw [show ((n : ℝ) - m) * x = ((n : ℝ) + 1) * x - ((m : ℝ) + 1) * x by ring,
      show ((n : ℝ) + m + 2) * x = ((n : ℝ) + 1) * x + ((m : ℝ) + 1) * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi _) (hi _),
    SineL2.integral_cos_int ((n : ℤ) + m + 2) (by omega)]
  by_cases h : n = m
  · subst m
    simp
  · rw [SineL2.integral_cos_int _ (by omega)]
    simp [h]

theorem inner_cosine (n m : ℕ) :
    inner ℝ (cosine n) (cosine m) = if n = m then Real.pi else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, Real.cos (((n+1 : ℕ) : ℝ) * x) *
        Real.cos (((m+1 : ℕ) : ℝ) * x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [cosine_ae n, cosine_ae m] with x hn hm
      simp only [hn, hm, RCLike.inner_apply, conj_trivial, mul_comm]
    _ = _ := ?_
  change (∫ x in Icc (-Real.pi) Real.pi, _) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact integral_cosine_mul n m

def normalized (n : ℕ) : Space := (Real.sqrt Real.pi)⁻¹ • cosine n

theorem orthonormal_normalized : Orthonormal ℝ normalized := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalized, inner_smul_left, inner_smul_right, conj_trivial, inner_cosine]
  by_cases h : n = m
  · simp only [h, ite_true]
    have hπ : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
    have hs := Real.sq_sqrt Real.pi_pos.le
    field_simp
    nlinarith
  · simp [h]

theorem tendsto_inner_cosine (f : Space) :
    Tendsto (fun n ↦ inner ℝ (cosine n) f) atTop (𝓝 0) := by
  have h := (orthonormal_normalized.inner_products_summable f).tendsto_atTop_zero
  have hnorm := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hnorm
  have hi : Tendsto (fun n ↦ inner ℝ (normalized n) f) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa [normalized, inner_smul_left, mul_assoc, Real.sqrt_ne_zero'.mpr Real.pi_pos]
    using hi.const_mul (Real.sqrt Real.pi)

theorem inner_cosine_indicator {E : Set ℝ} (hE : NullMeasurableSet E volume)
    (hsub : E ⊆ Icc (-Real.pi) Real.pi) (n : ℕ) :
    inner ℝ (cosine n) (SineL2.indicator hE) =
      ∫ x in E, Real.cos (((n+1 : ℕ) : ℝ) * x) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, E.indicator (fun x : ℝ ↦ Real.cos (((n+1 : ℕ) : ℝ) * x)) x ∂μ := by
      apply integral_congr_ae
      filter_upwards [cosine_ae n, (SineL2.memLp_indicator hE).coeFn_toLp] with x hn hI
      change inner ℝ (cosine n x) ((SineL2.memLp_indicator hE).toLp _ x) = _
      rw [hn, hI]
      by_cases hx : x ∈ E <;> simp [hx, RCLike.inner_apply]
    _ = _ := by
      rw [integral_indicator₀ (hE.mono Measure.restrict_le_self)]
      exact congrArg (fun ν ↦ ∫ x, Real.cos (((n+1 : ℕ) : ℝ) * x) ∂ν)
        (Measure.restrict_restrict_of_subset hsub)

theorem tendsto_setIntegral_cosine {E : Set ℝ} (hE : NullMeasurableSet E volume)
    (hsub : E ⊆ Icc (-Real.pi) Real.pi) :
    Tendsto (fun n : ℕ ↦ ∫ x in E, Real.cos ((n : ℝ) * x)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [inner_cosine_indicator hE hsub] using tendsto_inner_cosine (SineL2.indicator hE)

end CosineL2

/-- Exact convergence set, with no exceptional points removed. -/
def sineConvergenceSet (n : ℕ → ℕ) : Set ℝ :=
  {x | x ∈ Ioo (-Real.pi) Real.pi ∧
    ∃ y : ℝ, Tendsto (fun k ↦ Real.sin ((n k : ℝ) * x)) atTop (𝓝 y)}

theorem exercise16_measurability (n : ℕ → ℕ) : MeasurableSet (sineConvergenceSet n) := by
  exact measurableSet_Ioo.inter (measurableSet_exists_tendsto (fun k ↦ by fun_prop))

private theorem sine_difference_sq (a b : ℝ) :
    (Real.sin a - Real.sin b) ^ 2 =
      1 - Real.cos (2*a) / 2 - Real.cos (2*b) / 2 - Real.cos (a-b) + Real.cos (a+b) := by
  rw [Real.cos_two_mul, Real.cos_two_mul, Real.cos_sub, Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

/-- Every strictly increasing positive integer subsequence has a null convergence set. -/
theorem exercise16_null_convergence_set {n : ℕ → ℕ}
    (hn : StrictMono n) (_hpos : ∀ k, 0 < n k) : volume (sineConvergenceSet n) = 0 := by
  let E := sineConvergenceSet n
  have hE : MeasurableSet E := exercise16_measurability n
  have hsub : E ⊆ Icc (-Real.pi) Real.pi := fun x hx ↦ Ioo_subset_Icc_self hx.1
  have hfin : volume E ≠ ∞ := ne_of_lt ((measure_mono hsub).trans_lt measure_Icc_lt_top)
  let g (k : ℕ) (x : ℝ) :=
    (Real.sin ((n (2*k+1) : ℝ) * x) - Real.sin ((n k : ℝ) * x)) ^ 2
  have hindex : Tendsto (fun k : ℕ ↦ 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by dsimp; omega) tendsto_id
  have hzero : Tendsto (fun k ↦ ∫ x in E, g k x) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict E)
      (F := g) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (4 : ℝ))
      (fun k ↦ by dsimp [g]; fun_prop) (integrableOn_const hfin) ?_ ?_
    · simpa using h
    · intro k
      exact Eventually.of_forall fun x ↦ by
        dsimp [g]
        rw [abs_of_nonneg (sq_nonneg _)]
        have ha := Real.sin_le_one ((n (2*k+1) : ℝ) * x)
        have hb := Real.neg_one_le_sin ((n (2*k+1) : ℝ) * x)
        have hc := Real.sin_le_one ((n k : ℝ) * x)
        have hd := Real.neg_one_le_sin ((n k : ℝ) * x)
        nlinarith [sq_nonneg (Real.sin ((n (2*k+1) : ℝ) * x) + Real.sin ((n k : ℝ) * x))]
    · filter_upwards [ae_restrict_mem hE] with x hx
      obtain ⟨y, hy⟩ := hx.2
      simpa [g] using ((hy.comp hindex).sub hy).pow 2
  have hcos := CosineL2.tendsto_setIntegral_cosine hE.nullMeasurableSet hsub
  have hA : Tendsto (fun k ↦ 2 * n (2*k+1)) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by
      have hk : 2*k+1 ≤ n (2*k+1) := hn.id_le (2*k+1)
      change k ≤ 2 * n (2*k+1)
      omega) tendsto_id
  have hB : Tendsto (fun k ↦ 2 * n k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by
      have hk : k ≤ n k := hn.id_le k
      change k ≤ 2 * n k
      omega) tendsto_id
  have hC : Tendsto (fun k ↦ n (2*k+1) - n k) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro k
    dsimp
    have h := hn.add_le_nat (k+1) k
    have he : k+1+k = 2*k+1 := by omega
    rw [he] at h
    omega
  have hD : Tendsto (fun k ↦ n (2*k+1) + n k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by
      have hk : k ≤ n k := hn.id_le k
      change k ≤ n (2*k+1) + n k
      omega) tendsto_id
  have hlim := (((tendsto_const_nhds (x := volume.real E)).sub
    ((hcos.comp hA).div_const 2)).sub ((hcos.comp hB).div_const 2)).sub
      (hcos.comp hC) |>.add (hcos.comp hD)
  have hformula (k : ℕ) : (∫ x in E, g k x) =
      volume.real E - (∫ x in E, Real.cos (((2*n (2*k+1) : ℕ) : ℝ) * x)) / 2 -
      (∫ x in E, Real.cos (((2*n k : ℕ) : ℝ) * x)) / 2 -
      (∫ x in E, Real.cos (((n (2*k+1) - n k : ℕ) : ℝ) * x)) +
      (∫ x in E, Real.cos (((n (2*k+1) + n k : ℕ) : ℝ) * x)) := by
    have hi (c : ℝ) : IntegrableOn (fun x : ℝ ↦ Real.cos (c*x)) E :=
      ((by fun_prop : Continuous (fun x : ℝ ↦ Real.cos (c*x))).integrableOn_Icc).mono_set hsub
    have he (x : ℝ) : g k x =
        1 - Real.cos (((2*n (2*k+1) : ℕ) : ℝ)*x) / 2 -
        Real.cos (((2*n k : ℕ) : ℝ)*x) / 2 -
        Real.cos (((n (2*k+1) - n k : ℕ) : ℝ)*x) +
        Real.cos (((n (2*k+1) + n k : ℕ) : ℝ)*x) := by
      dsimp only [g]
      rw [sine_difference_sq]
      have hle : n k ≤ n (2*k+1) := hn.monotone (by omega)
      push_cast [Nat.cast_sub hle]
      ring_nf
    simp_rw [he]
    have h1 : IntegrableOn (fun x : ℝ ↦ 1 - Real.cos (((2*n (2*k+1) : ℕ) : ℝ)*x) / 2) E :=
      (integrableOn_const (C := (1 : ℝ)) hfin).sub ((hi _).div_const 2)
    have h2 : IntegrableOn (fun x : ℝ ↦
        1 - Real.cos (((2*n (2*k+1) : ℕ) : ℝ)*x) / 2 -
        Real.cos (((2*n k : ℕ) : ℝ)*x) / 2) E := h1.sub ((hi _).div_const 2)
    have h3 : IntegrableOn (fun x : ℝ ↦
        1 - Real.cos (((2*n (2*k+1) : ℕ) : ℝ)*x) / 2 -
        Real.cos (((2*n k : ℕ) : ℝ)*x) / 2 -
        Real.cos (((n (2*k+1) - n k : ℕ) : ℝ)*x)) E := h2.sub (hi _)
    rw [integral_add h3 (hi (((n (2*k+1) + n k : ℕ) : ℝ))), integral_sub h2 (hi _),
      integral_sub h1 ((hi _).div_const 2),
      integral_sub (integrableOn_const hfin) ((hi _).div_const 2),
      integral_div, integral_div, setIntegral_const]
    simp
  have hm : Tendsto (fun k ↦ ∫ x in E, g k x) atTop (𝓝 (volume.real E)) := by
    simpa only [hformula, Function.comp_def, zero_div, sub_zero, add_zero] using hlim
  have hz : volume.real E = 0 := tendsto_nhds_unique hm hzero
  exact (ENNReal.toReal_eq_zero_iff _).1 hz |>.resolve_right hfin

end Rudin.Chapter11
