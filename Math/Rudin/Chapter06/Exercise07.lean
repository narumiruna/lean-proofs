module

public import Math.Rudin.Support.RiemannIntegrability
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Chapter 6, Exercise 7

Improper integrals are finite limits of actual proper Riemann integrals.
Each predicate includes a closed-cell Darboux witness at every truncation.
There is no default value for a divergent improper integral.

The conditional example is `cos (1 / x - 1) / x` on `(0,1]`.
The substitution `t = 1 / x - 1` reduces it to an oscillatory tail.
Source: book page 138, PDF page 147.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesIntegralLaws
  Rudin.Support.RiemannIntegrability
open scoped Topology

/-- A finite limit at a left endpoint, with proper Riemann integrals at all cuts. -/
def HasImproperRiemannIntegralLeft (f : ℝ → ℝ) (a b v : ℝ) : Prop :=
  a < b ∧
  (∀ c, a < c → c ≤ b →
    HasDarbouxRSIntegral f id c b (∫ x in c..b, f x)) ∧
  Tendsto (fun c ↦ ∫ x in c..b, f x) (𝓝[>] a) (𝓝 v)

/-- A finite limit at infinity, with proper Riemann integrals at all cuts,
including the singleton cut. -/
def HasImproperRiemannIntegralTop (f : ℝ → ℝ) (a v : ℝ) : Prop :=
  (∀ b, a ≤ b → HasDarbouxRSIntegral f id a b (∫ x in a..b, f x)) ∧
  Tendsto (fun b ↦ ∫ x in a..b, f x) atTop (𝓝 v)

/-- Existence, not a totalized numerical value. -/
def ImproperRiemannIntegrableLeft (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ v, HasImproperRiemannIntegralLeft f a b v

/-- Existence, not a totalized numerical value. -/
def ImproperRiemannIntegrableTop (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ v, HasImproperRiemannIntegralTop f a v

/-- The ordinary continuous bridge uses the identity integrator and volume. -/
theorem properRiemann_of_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  rw [Real.volume_eq_stieltjes_id]
  exact Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hf

/-- Restriction preserves actual proper integrability, without continuity. -/
theorem properRiemann_restrict_right {f : ℝ → ℝ} {a b c v : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : HasDarbouxRSIntegral f id a b v) :
    HasDarbouxRSIntegral f id c b (∫ x in c..b, f x) := by
  obtain ⟨l, r, _, hr, _⟩ := hasDarbouxRSIntegral_split hac hcb hf
  rw [(intervalIntegrable_and_integral_eq hcb hr).2]
  exact hr

/-- **7(a)**: every proper Riemann integral agrees with the finite-endpoint limit.
The integrand need not be continuous or initially assumed measurable. -/
theorem exercise07_a {f : ℝ → ℝ} {a b v : ℝ} (hab : a < b)
    (hf : HasDarbouxRSIntegral f id a b v) :
    HasImproperRiemannIntegralLeft f a b v := by
  have hi := (intervalIntegrable_and_integral_eq hab.le hf).1
  refine ⟨hab, fun c hc hcb ↦ properRiemann_restrict_right hc.le hcb hf, ?_⟩
  have hi' : IntegrableOn f (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi'
  rw [uIcc_of_le hab.le] at hcont
  rw [← (intervalIntegrable_and_integral_eq hab.le hf).2]
  exact ((hcont a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGT hab)).tendsto

/-- Absolute integrability on a ray gives an improper limit only when the
proper Riemann witnesses are also supplied. -/
theorem improperRiemannTop_of_integrableOn {f : ℝ → ℝ} {a : ℝ}
    (hp : ∀ b, a ≤ b → HasDarbouxRSIntegral f id a b (∫ x in a..b, f x))
    (hi : IntegrableOn f (Ioi a)) :
    HasImproperRiemannIntegralTop f a (∫ x in Ioi a, f x) :=
  ⟨hp, intervalIntegral_tendsto_integral_Ioi a hi tendsto_id⟩

/-- For nonnegative functions, a finite improper limit implies Lebesgue
integrability. This is a proved bridge, not the definition of an improper integral. -/
theorem integrableOn_of_improperRiemannTop_nonneg {f : ℝ → ℝ} {a v : ℝ}
    (hf : HasImproperRiemannIntegralTop f a v) (hn : ∀ x ∈ Ici a, 0 ≤ f x) :
    IntegrableOn f (Ioi a) := by
  let b : ℝ → ℝ := fun t ↦ max a t
  have hb : Tendsto b atTop atTop := tendsto_atTop_mono (fun _ ↦ le_max_right _ _) tendsto_id
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto v a
    (fun t ↦ (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_max_left a t)).mp
      (intervalIntegrable_and_integral_eq (le_max_left a t) (hf.1 _ (le_max_left a t))).1) hb
  have h := hf.2.comp hb
  convert h using 1
  ext t
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (le_max_left a t)] at hx
  exact Real.norm_of_nonneg (hn x hx.1)

/-- Kernels used to construct the finite-endpoint example. -/
noncomputable def oscillatoryKernel (k x : ℝ) : ℝ := Real.cos (k * x) / (1 + x)

noncomputable def sineSquareKernel (k x : ℝ) : ℝ := Real.sin (k * x) / (1 + x) ^ 2

noncomputable def oscillatoryBoundary (k x : ℝ) : ℝ :=
  Real.sin (k * x) / (k * (1 + x))

theorem continuousOn_oscillatoryKernel (k : ℝ) :
    ContinuousOn (oscillatoryKernel k) (Ici 0) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  linarith [mem_Ici.mp hx]

theorem continuousOn_sineSquareKernel (k : ℝ) :
    ContinuousOn (sineSquareKernel k) (Ici 0) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  exact pow_ne_zero _ (by have := hx; simp only [mem_Ici] at this; linarith)

theorem integrableOn_inverseSquare :
    IntegrableOn (fun x : ℝ ↦ 1 / (1 + x) ^ 2) (Ioi 0) := by
  convert (integrableOn_add_rpow_Ioi_of_lt (a := -2) (m := 1) (c := 0)
    (by norm_num) (by norm_num)) using 1
  ext x
  simp [add_comm, one_div]

theorem integrableOn_sineSquareKernel (k : ℝ) :
    IntegrableOn (sineSquareKernel k) (Ioi 0) := by
  apply integrableOn_inverseSquare.mono'
    (((continuousOn_sineSquareKernel k).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, sineSquareKernel, abs_div,
    abs_of_nonneg (sq_nonneg (1 + x))]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (sq_nonneg _)

theorem oscillatoryBoundary_tendsto {k : ℝ} (hk : k ≠ 0) :
    Tendsto (oscillatoryBoundary k) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ ↦ (1 / |k|) / (1 + x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ (1 / |k|) / (1 + x)) ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [oscillatoryBoundary, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by linarith : 0 < 1 + x), div_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

/-- A proper integration-by-parts identity, valid at every nonnegative cut. -/
theorem oscillatoryKernel_proper_identity {k b : ℝ} (hk : k ≠ 0) (hb : 0 ≤ b) :
    (∫ x in 0..b, oscillatoryKernel k x) =
      oscillatoryBoundary k b + (1 / k) * ∫ x in 0..b, sineSquareKernel k x := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivAt (oscillatoryBoundary k)
        (oscillatoryKernel k x - (1 / k) * sineSquareKernel k x) x := by
    have hx' : 1 + x ≠ 0 := by linarith [hx.1]
    convert (((Real.hasDerivAt_sin (k * x)).comp x ((hasDerivAt_id x).const_mul k)).div
      (((hasDerivAt_id x).const_add 1).const_mul k) (mul_ne_zero hk hx')) using 1
    · rfl
    · dsimp [oscillatoryKernel, sineSquareKernel]
      field_simp
  have hi : IntervalIntegrable (oscillatoryKernel k) volume 0 b :=
    ((continuousOn_oscillatoryKernel k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hb
  have hj : IntervalIntegrable (sineSquareKernel k) volume 0 b :=
    ((continuousOn_sineSquareKernel k).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hb
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ hd x ((uIcc_of_le hb) ▸ hx)) (hi.sub (hj.const_mul (1 / k)))
  rw [intervalIntegral.integral_sub hi (hj.const_mul (1 / k)),
    intervalIntegral.integral_const_mul] at heq
  simp only [oscillatoryBoundary, mul_zero, Real.sin_zero, zero_div, sub_zero] at heq
  dsimp only [oscillatoryBoundary]
  linarith

/-- The oscillatory integral is defined by its finite truncations, not by a
Bochner integral of the oscillatory kernel on the whole ray. -/
theorem oscillatoryKernel_improper {k : ℝ} (hk : k ≠ 0) :
    HasImproperRiemannIntegralTop (oscillatoryKernel k) 0
      ((1 / k) * ∫ x in Ioi 0, sineSquareKernel k x) := by
  refine ⟨fun b hb ↦ properRiemann_of_continuousOn hb
    ((continuousOn_oscillatoryKernel k).mono Icc_subset_Ici_self), ?_⟩
  have h := (oscillatoryBoundary_tendsto hk).add
    ((intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_sineSquareKernel k)
      tendsto_id).const_mul (1 / k))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
  exact (oscillatoryKernel_proper_identity hk hb).symm

/-- The absolute cosine kernel has no finite improper limit. The proof uses
`cos (2x) = 2 cos² x - 1` and the divergent logarithmic integral. -/
theorem oscillatoryKernel_one_not_absolute :
    ¬ ImproperRiemannIntegrableTop (fun x ↦ |oscillatoryKernel 1 x|) 0 := by
  rintro ⟨v, hv⟩
  have hi := integrableOn_of_improperRiemannTop_nonneg hv (fun x _ ↦ abs_nonneg _)
  have hsq : IntegrableOn (fun x ↦ Real.cos x ^ 2 / (1 + x)) (Ioi 0) := by
    apply hi.mono'
      (((Real.continuous_cos.pow 2).continuousOn.div (by fun_prop)
        (by intro x hx; linarith [mem_Ioi.mp hx])).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : 0 < 1 + x := by linarith [mem_Ioi.mp hx]
    change |Real.cos x ^ 2 / (1 + x)| ≤ |oscillatoryKernel 1 x|
    simp only [oscillatoryKernel, one_mul, abs_div,
      abs_of_nonneg (sq_nonneg (Real.cos x)), abs_of_pos hx']
    apply div_le_div_of_nonneg_right _ hx'.le
    nlinarith [Real.abs_cos_le_one x, sq_abs (Real.cos x), abs_nonneg (Real.cos x)]
  have hlim := (intervalIntegral_tendsto_integral_Ioi 0 hsq tendsto_id).const_mul 2 |>.sub
    (oscillatoryKernel_improper (k := 2) (by norm_num)).2
  have heq : ∀ᶠ b : ℝ in atTop,
      2 * (∫ x in 0..b, Real.cos x ^ 2 / (1 + x)) -
        (∫ x in 0..b, oscillatoryKernel 2 x) = Real.log (1 + b) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hc : ContinuousOn (fun x ↦ Real.cos x ^ 2 / (1 + x)) (Icc 0 b) :=
      (Real.continuous_cos.pow 2).continuousOn.div (by fun_prop)
        (by intro x hx; linarith [hx.1])
    have hc' : IntervalIntegrable (fun x ↦ Real.cos x ^ 2 / (1 + x)) volume 0 b :=
      hc.intervalIntegrable_of_Icc hb
    have hk : IntervalIntegrable (oscillatoryKernel 2) volume 0 b :=
      ((continuousOn_oscillatoryKernel 2).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hb
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hc'.const_mul 2) hk]
    calc
      _ = ∫ x in 0..b, 1 / (1 + x) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [oscillatoryKernel, Real.cos_two_mul]
        ring
      _ = Real.log (1 + b) := by
        rw [intervalIntegral.integral_comp_add_left (f := fun x : ℝ ↦ 1 / x) 1]
        simpa using integral_one_div_of_pos (by norm_num : (0 : ℝ) < 1)
          (by linarith : 0 < 1 + b)
  have hfinite := hlim.congr' heq
  exact not_tendsto_nhds_of_tendsto_atTop
    (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)) _ hfinite

/-- The explicit function on `(0,1]`; its value elsewhere is irrelevant. -/
noncomputable def conditionalEndpointExample (x : ℝ) : ℝ :=
  Real.cos (x⁻¹ - 1) / x

/-- The inverse substitution preserves every proper truncation. -/
theorem inverse_substitution {g : ℝ → ℝ} (hg : ContinuousOn g (Ici 0))
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ x in c..1, g (x⁻¹ - 1) / x ^ 2) = ∫ t in 0..c⁻¹ - 1, g t := by
  have hne (x : ℝ) (hx : x ∈ uIcc c 1) : x ≠ 0 := by
    rw [uIcc_of_le hc1] at hx
    linarith [hx.1]
  have h := intervalIntegral.integral_comp_mul_deriv'
    (f := fun x : ℝ ↦ x⁻¹ - 1) (f' := fun x ↦ -(x ^ 2)⁻¹)
    (fun x hx ↦ by
      simpa only [id_eq, Pi.inv_apply, neg_div, one_div] using
        ((hasDerivAt_id x).inv (hne x hx)).sub_const 1)
    (((continuousOn_id.pow 2).inv₀ (fun x hx ↦ pow_ne_zero 2 (hne x hx))).neg)
    (hg.mono (by
      rintro y ⟨x, hx, rfl⟩
      rw [uIcc_of_le hc1] at hx
      exact sub_nonneg.mpr ((one_le_inv₀ (hc.trans_le hx.1)).mpr hx.2)))
  simp only [Function.comp_apply, inv_one, sub_self] at h
  calc
    _ = -(∫ x in c..1, g (x⁻¹ - 1) * -(x ^ 2)⁻¹) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      simp [div_eq_mul_inv]
    _ = _ := by rw [h, intervalIntegral.integral_symm]; simp

/-- All proper truncations of the example and its absolute value are Riemann integrable. -/
theorem conditionalEndpointExample_proper {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    HasDarbouxRSIntegral conditionalEndpointExample id c 1
      (∫ x in c..1, conditionalEndpointExample x) ∧
    HasDarbouxRSIntegral (fun x ↦ |conditionalEndpointExample x|) id c 1
      (∫ x in c..1, |conditionalEndpointExample x|) := by
  have hn (x : ℝ) (hx : x ∈ Icc c 1) : x ≠ 0 := by linarith [hx.1]
  have hcont : ContinuousOn conditionalEndpointExample (Icc c 1) := by
    unfold conditionalEndpointExample
    fun_prop (disch := exact hn _ ‹_›)
  exact ⟨properRiemann_of_continuousOn hc1 hcont,
    properRiemann_of_continuousOn hc1 hcont.abs⟩

private theorem endpoint_substitution {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ x in c..1, conditionalEndpointExample x) =
      ∫ t in 0..c⁻¹ - 1, oscillatoryKernel 1 t := by
  rw [← inverse_substitution (continuousOn_oscillatoryKernel 1) hc hc1]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hc1] at hx
  have hn : x ≠ 0 := by linarith [hx.1]
  dsimp [conditionalEndpointExample, oscillatoryKernel]
  field_simp
  ring

private theorem endpoint_abs_substitution {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    (∫ x in c..1, |conditionalEndpointExample x|) =
      ∫ t in 0..c⁻¹ - 1, |oscillatoryKernel 1 t| := by
  rw [← inverse_substitution (continuousOn_oscillatoryKernel 1).abs hc hc1]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hc1] at hx
  have hn : x ≠ 0 := by linarith [hx.1]
  have heq : conditionalEndpointExample x = oscillatoryKernel 1 (x⁻¹ - 1) / x ^ 2 := by
    dsimp [conditionalEndpointExample, oscillatoryKernel]
    field_simp
    ring
  change |conditionalEndpointExample x| = |oscillatoryKernel 1 (x⁻¹ - 1)| / x ^ 2
  rw [heq, abs_div, abs_of_nonneg (sq_nonneg x)]

/-- **7(b)**: local proper Riemann integrability and conditional convergence. -/
theorem exercise07_b :
    ImproperRiemannIntegrableLeft conditionalEndpointExample 0 1 ∧
    ¬ ImproperRiemannIntegrableLeft (fun x ↦ |conditionalEndpointExample x|) 0 1 := by
  constructor
  · refine ⟨∫ x in Ioi 0, sineSquareKernel 1 x, by norm_num,
      fun c hc hc1 ↦ (conditionalEndpointExample_proper hc hc1).1, ?_⟩
    have ht : Tendsto (fun c : ℝ ↦ c⁻¹ - 1) (𝓝[>] 0) atTop :=
      tendsto_atTop_add_const_right _ (-1) tendsto_inv_nhdsGT_zero
    have h := (oscillatoryKernel_improper (k := 1) one_ne_zero).2.comp ht
    simp only [one_div_one, one_mul] at h
    apply h.congr'
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with c hc
    exact (endpoint_substitution hc.1 hc.2).symm
  · rintro ⟨v, hv⟩
    apply oscillatoryKernel_one_not_absolute
    refine ⟨v, fun b hb ↦ properRiemann_of_continuousOn hb
      (((continuousOn_oscillatoryKernel 1).abs).mono Icc_subset_Ici_self), ?_⟩
    have ht : Tendsto (fun b : ℝ ↦ (1 + b)⁻¹) atTop (𝓝[>] 0) :=
      tendsto_inv_atTop_nhdsGT_zero.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h := hv.2.2.comp ht
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    have hp : 0 < (1 + b)⁻¹ := inv_pos.mpr (by linarith)
    have hle : (1 + b)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
    simpa only [Function.comp_apply, inv_inv, add_sub_cancel_left] using
      endpoint_abs_substitution hp hle

end Rudin.Chapter06
