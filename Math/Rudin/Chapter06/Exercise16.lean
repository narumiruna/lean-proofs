module

public import Math.Rudin.Support.RiemannIntegrability
public import Math.Rudin.Support.StieltjesComposition
public import Mathlib

/-!
# R06E16: two improper Riemann integral formulas for zeta

Source: Rudin, Third Edition, Exercise 6.16, book page 141 (PDF page 150).
The zeta series is the ordered series starting at 1. Every finite truncation
has an actual ordinary Darboux integral. Improper integrals are limits of
these proper integrals, not totalized integrals of nonintegrable functions.
Abel summation gives the finite identity in the source hint. The fractional
part remainder converges for every positive real exponent; the zeta formulas
are asserted only for exponents greater than 1.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open scoped Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesMeasureBridge
  Rudin.Support.StieltjesComposition Rudin.Support.StieltjesIntegralLaws
  Rudin.Support.RiemannIntegrability

/-- The ordinary improper Riemann integral from 1 to infinity. -/
def HasImproperRiemannIntegralFromOne (f : ℝ → ℝ) (v : ℝ) : Prop :=
  (∀ b : ℝ, 1 ≤ b → HasDarbouxRSIntegral f id 1 b (∫ x in 1..b, f x)) ∧
    Tendsto (fun b : ℝ ↦ ∫ x in 1..b, f x) atTop (𝓝 v)

/-- Ordered partial sums of the series printed in the exercise. -/
noncomputable def zetaPartialSum (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / ((n + 1 : ℕ) : ℝ) ^ s

/-- The real zeta value; ordered convergence is proved below for `s > 1`. -/
noncomputable def realZeta (s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s

noncomputable def zetaFloorIntegrand (s x : ℝ) : ℝ := (⌊x⌋ : ℝ) / x ^ (s + 1)

noncomputable def zetaRemainderIntegrand (s x : ℝ) : ℝ :=
  (x - (⌊x⌋ : ℝ)) / x ^ (s + 1)

private theorem exercise16_continuous_ri {b : ℝ} {f : ℝ → ℝ}
    (hb : 1 ≤ b) (hf : ContinuousOn f (Icc 1 b)) :
    HasDarbouxRSIntegral f id 1 b (∫ x in 1..b, f x) := by
  have hid : (StieltjesFunction.id : ℝ → ℝ) = id := by
    funext x
    exact StieltjesFunction.id_apply x
  simpa only [hid, ← Real.volume_eq_stieltjes_id] using
    continuous_bridge StieltjesFunction.id hb hf

private theorem exercise16_power_continuous (s : ℝ) {b : ℝ} :
    ContinuousOn (fun x : ℝ ↦ 1 / x ^ (s + 1)) (Icc 1 b) := by
  apply continuousOn_const.div
    (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (show x ≠ 0 from by linarith [hx.1])))
  intro x hx
  exact (Real.rpow_pos_of_pos (show 0 < x from by linarith [hx.1]) _).ne'

/-- Both integrands have proper ordinary Riemann integrals at every real cutoff.
This statement needs no restriction on the exponent. -/
theorem exercise16_proper_integrals (s : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    HasDarbouxRSIntegral (zetaFloorIntegrand s) id 1 b
        (∫ x in 1..b, zetaFloorIntegrand s x) ∧
      HasDarbouxRSIntegral (zetaRemainderIntegrand s) id 1 b
        (∫ x in 1..b, zetaRemainderIntegrand s x) := by
  have hfloor : MonotoneOn (fun x : ℝ ↦ (⌊x⌋ : ℝ)) (Icc 1 b) := by
    intro x _ y _ hxy
    exact Int.cast_le.mpr (Int.floor_mono hxy)
  obtain ⟨v, hv⟩ := exists_product hb
    (hasDarbouxRSIntegral_of_monotoneOn hb hfloor)
    (exercise16_continuous_ri hb (exercise16_power_continuous s))
  have hv' : HasDarbouxRSIntegral (zetaFloorIntegrand s) id 1 b v := by
    apply hasDarbouxRSIntegral_congr hb hv
    intro x _
    simp only [zetaFloorIntegrand, div_eq_mul_inv, one_mul]
  have hF : HasDarbouxRSIntegral (zetaFloorIntegrand s) id 1 b
      (∫ x in 1..b, zetaFloorIntegrand s x) := by
    rw [(intervalIntegrable_and_integral_eq hb hv').2]
    exact hv'
  have hx : ContinuousOn (fun x : ℝ ↦ x / x ^ (s + 1)) (Icc 1 b) := by
    apply continuousOn_id.div
      (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (show x ≠ 0 from by linarith [hx.1])))
    intro x hx
    exact (Real.rpow_pos_of_pos (show 0 < x from by linarith [hx.1]) _).ne'
  have hR := hasDarbouxRSIntegral_sub hb (exercise16_continuous_ri hb hx) hF
  have hR' : HasDarbouxRSIntegral (zetaRemainderIntegrand s) id 1 b
      ((∫ x in 1..b, x / x ^ (s + 1)) - ∫ x in 1..b, zetaFloorIntegrand s x) := by
    apply hasDarbouxRSIntegral_congr hb hR
    intro x _
    simp only [zetaRemainderIntegrand, zetaFloorIntegrand, sub_div]
  exact ⟨hF, by rw [(intervalIntegrable_and_integral_eq hb hR').2]; exact hR'⟩

/-- The nonnegative defining series converges in its printed order for `s > 1`. -/
theorem exercise16_ordered_series {s : ℝ} (hs : 1 < s) :
    (∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ s) ∧
      Tendsto (zetaPartialSum s) atTop (𝓝 (realZeta s)) := by
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ s) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
  exact ⟨fun n ↦ by positivity, hsum.hasSum.tendsto_sum_nat⟩

private theorem exercise16_power_identity {x : ℝ} (hx : 0 < x) (s : ℝ) :
    x / x ^ (s + 1) = x ^ (-s) := by
  calc
    _ = x ^ (1 : ℝ) / x ^ (s + 1) := by rw [Real.rpow_one]
    _ = x ^ (1 - (s + 1)) := (Real.rpow_sub hx _ _).symm
    _ = x ^ (-s) := by congr 1; ring

private theorem exercise16_floor_integrable {s : ℝ} (hs : 1 < s) :
    IntegrableOn (zetaFloorIntegrand s) (Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ ↦ x ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  apply hg.mono'
  · have hm : Measurable (zetaFloorIntegrand s) := by
      unfold zetaFloorIntegrand
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hfloor0 : (0 : ℝ) ≤ (⌊x⌋ : ℝ) := Int.cast_nonneg (Int.floor_nonneg.mpr hx0.le)
    rw [Real.norm_of_nonneg (show 0 ≤ zetaFloorIntegrand s x from
      div_nonneg hfloor0 (Real.rpow_pos_of_pos hx0 _).le)]
    change (⌊x⌋ : ℝ) / x ^ (s + 1) ≤ x ^ (-s)
    rw [← exercise16_power_identity hx0 s]
    exact div_le_div_of_nonneg_right (Int.floor_le x) (Real.rpow_pos_of_pos hx0 _).le

private theorem exercise16_remainder_integrable {s : ℝ} (hs : 0 < s) :
    IntegrableOn (zetaRemainderIntegrand s) (Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ ↦ x ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  apply hg.mono'
  · have hm : Measurable (zetaRemainderIntegrand s) := by
      unfold zetaRemainderIntegrand
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hfract0 : 0 ≤ x - (⌊x⌋ : ℝ) := Int.fract_nonneg x
    have hfract1 : x - (⌊x⌋ : ℝ) ≤ 1 := (Int.fract_lt_one x).le
    rw [Real.norm_of_nonneg (show 0 ≤ zetaRemainderIntegrand s x from
      div_nonneg hfract0 (Real.rpow_pos_of_pos hx0 _).le)]
    change (x - (⌊x⌋ : ℝ)) / x ^ (s + 1) ≤ x ^ (-(s + 1))
    rw [Real.rpow_neg hx0.le, ← one_div]
    exact div_le_div_of_nonneg_right hfract1 (Real.rpow_pos_of_pos hx0 _).le

private theorem exercise16_coeff_sum (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, (if k = 0 then 0 else 1 : ℝ)) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp

private theorem exercise16_abel_sum (s : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N, (k : ℝ) ^ (-s) * (if k = 0 then 0 else 1)) =
      zetaPartialSum s N := by
  induction N with
  | zero => simp [zetaPartialSum]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [zetaPartialSum, Finset.sum_range_succ, Nat.succ_ne_zero, ite_false, mul_one]
    rw [Real.rpow_neg (Nat.cast_nonneg _) s, one_div]

/-- The exact finite error in the source hint. -/
theorem exercise16_finite_identity (s : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    zetaPartialSum s N = (N : ℝ) ^ (1 - s) +
      s * ∫ x in 1..(N : ℝ), zetaFloorIntegrand s x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hderiv (x : ℝ) (hx : x ∈ Icc 1 (N : ℝ)) :
      HasDerivAt (fun t : ℝ ↦ t ^ (-s)) ((-s) * x ^ (-s - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))
  have hcont : ContinuousOn (fun x : ℝ ↦ (-s) * x ^ (-s - 1)) (Icc 1 (N : ℝ)) :=
    (continuousOn_id.rpow_const (fun x hx ↦ Or.inl (by simp only [id_eq]; linarith [hx.1]))).const_mul _
  have hint : IntegrableOn (deriv (fun x : ℝ ↦ x ^ (-s))) (Icc 1 (N : ℝ)) := by
    apply hcont.integrableOn_Icc.congr_fun
    · intro x hx
      exact (hderiv x hx).deriv.symm
    · exact measurableSet_Icc
  have hab := sum_mul_eq_sub_integral_mul₀' (fun k : ℕ ↦ if k = 0 then (0 : ℝ) else 1)
    (by simp) N (fun x hx ↦ (hderiv x hx).differentiableAt) hint
  rw [exercise16_abel_sum, exercise16_coeff_sum] at hab
  have hi : (∫ t in Ioc 1 (N : ℝ), deriv (fun x : ℝ ↦ x ^ (-s)) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k = 0 then 0 else 1 : ℝ)) =
        (-s) * ∫ x in 1..(N : ℝ), zetaFloorIntegrand s x := by
    rw [← intervalIntegral.integral_of_le (by exact_mod_cast hN),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by exact_mod_cast hN)] at hx
    change deriv (fun x : ℝ ↦ x ^ (-s)) x * _ = (-s) * zetaFloorIntegrand s x
    rw [(hderiv x hx).deriv, exercise16_coeff_sum,
      natCast_floor_eq_intCast_floor (show (0 : ℝ) ≤ x by linarith [hx.1])]
    have hx0 : 0 < x := by linarith [hx.1]
    rw [show -s - 1 = -(s + 1) by ring, Real.rpow_neg hx0.le]
    simp only [zetaFloorIntegrand, div_eq_mul_inv]
    ring
  rw [hi] at hab
  have hboundary : (N : ℝ) ^ (-s) * N = (N : ℝ) ^ (1 - s) := by
    rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
    ring
  rw [hboundary] at hab
  linarith

/-- R06E16(a), with the ordered series and all proper Riemann witnesses. -/
theorem exercise16_a {s : ℝ} (hs : 1 < s) :
    Tendsto (zetaPartialSum s) atTop (𝓝 (realZeta s)) ∧
      ∃ I : ℝ, HasImproperRiemannIntegralFromOne (zetaFloorIntegrand s) I ∧
        realZeta s = s * I := by
  let I := ∫ x in Ioi (1 : ℝ), zetaFloorIntegrand s x
  have hi := exercise16_floor_integrable hs
  have ht : Tendsto (fun b : ℝ ↦ ∫ x in 1..b, zetaFloorIntegrand s x) atTop (𝓝 I) :=
    intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_id
  have hN : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ) ^ (1 - s) +
      s * ∫ x in 1..((N + 1 : ℕ) : ℝ), zetaFloorIntegrand s x) atTop (𝓝 (s * I)) := by
    simpa only [neg_sub, zero_add, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (show 0 < s - 1 by linarith)).comp hN).add
        ((tendsto_const_nhds (x := s)).mul (ht.comp hN))
  have hsame : Tendsto (fun N : ℕ ↦ zetaPartialSum s (N + 1)) atTop (𝓝 (s * I)) :=
    hlim.congr' (Eventually.of_forall fun N ↦ (exercise16_finite_identity s (by omega : 1 ≤ N + 1)).symm)
  have hz := (exercise16_ordered_series hs).2
  have heq : realZeta s = s * I :=
    tendsto_nhds_unique (hz.comp (tendsto_add_atTop_nat 1)) hsame
  exact ⟨hz, I, ⟨fun b hb ↦ (exercise16_proper_integrals s hb).1, ht⟩, heq⟩

/-- R06E16: the remainder converges for every `s > 0`, with a proper
ordinary Riemann integral at every cutoff. No zeta series assertion is made. -/
theorem exercise16_remainder_convergence {s : ℝ} (hs : 0 < s) :
    ∃ J : ℝ, HasImproperRiemannIntegralFromOne (zetaRemainderIntegrand s) J := by
  exact ⟨∫ x in Ioi (1 : ℝ), zetaRemainderIntegrand s x,
    (fun b hb ↦ (exercise16_proper_integrals s hb).2),
    intervalIntegral_tendsto_integral_Ioi 1 (exercise16_remainder_integrable hs) tendsto_id⟩

/-- R06E16(b), including actual improper Riemann integrals for both terms. -/
theorem exercise16_b {s : ℝ} (hs : 1 < s) :
    Tendsto (zetaPartialSum s) atTop (𝓝 (realZeta s)) ∧
      ∃ J : ℝ, HasImproperRiemannIntegralFromOne (zetaRemainderIntegrand s) J ∧
        realZeta s = s / (s - 1) - s * J := by
  obtain ⟨hz, I, hI, heq⟩ := exercise16_a hs
  obtain ⟨J, hJ⟩ := exercise16_remainder_convergence (by linarith : 0 < s)
  have hp : IntegrableOn (fun x : ℝ ↦ x ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hplim : Tendsto (fun b : ℝ ↦ ∫ x in 1..b, x ^ (-s)) atTop (𝓝 (1 / (s - 1))) := by
    have hv : (∫ x in Ioi (1 : ℝ), x ^ (-s)) = 1 / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    rw [← hv]
    exact intervalIntegral_tendsto_integral_Ioi 1 hp tendsto_id
  have hsum : I + J = 1 / (s - 1) := by
    have he : (fun b : ℝ ↦ (∫ x in 1..b, zetaFloorIntegrand s x) +
        ∫ x in 1..b, zetaRemainderIntegrand s x) =ᶠ[atTop]
        (fun b : ℝ ↦ ∫ x in 1..b, x ^ (-s)) := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
      have hproper := exercise16_proper_integrals s hb
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_and_integral_eq hb hproper.1).1
        (intervalIntegrable_and_integral_eq hb hproper.2).1]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb] at hx
      change zetaFloorIntegrand s x + zetaRemainderIntegrand s x = x ^ (-s)
      rw [zetaFloorIntegrand, zetaRemainderIntegrand, ← add_div]
      rw [show (⌊x⌋ : ℝ) + (x - (⌊x⌋ : ℝ)) = x by ring]
      exact exercise16_power_identity (x := x) (by linarith [hx.1]) s
    exact tendsto_nhds_unique (hI.2.add hJ.2) (hplim.congr' he.symm)
  refine ⟨hz, J, hJ, ?_⟩
  rw [heq]
  have h : I = 1 / (s - 1) - J := by linarith
  rw [h]
  ring

end Rudin.Chapter06
