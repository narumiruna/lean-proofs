module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! # Chapter 8, Exercise 30

Stirling's formula implies the Gamma ratio limit for every real shift.
Mathlib's factorial Stirling theorem is extended to real arguments by the
log-convexity of Gamma. All Gamma arguments and denominators are positive
on an explicit eventual domain.
-/

@[expose] public section

open Filter Set
open scoped Topology Real

namespace Rudin.Chapter08.Exercise30

noncomputable def logStirlingRemainder (x : ℝ) : ℝ :=
  Real.log (Real.Gamma (x + 1)) - (x + 1 / 2) * Real.log x + x

lemma logGamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log (Real.Gamma x) + Real.log x := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

lemma logGamma_interpolation (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * Real.log n ≤ Real.log (Real.Gamma (n + t + 1)) -
      Real.log (Real.Gamma (n + 1)) ∧
    Real.log (Real.Gamma (n + t + 1)) - Real.log (Real.Gamma (n + 1)) ≤
      t * Real.log (n + 1) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hl := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma
    (fun {y} hy ↦ logGamma_add_one hy) (n := n + 1) (by omega) ht
  have hu := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma
    (fun {y} hy ↦ logGamma_add_one hy) (n := n + 1) (by omega) ht ht1
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hl hu
  have he : (n : ℝ) + 1 + t = n + t + 1 := by ring
  rw [he] at hl hu
  constructor <;> linarith

lemma remainder_interpolation (n : ℕ) (hn : 1 ≤ n) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    |logStirlingRemainder (n + t) - logStirlingRemainder n| ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 < (n : ℝ) + t := by positivity
  have hΓ := logGamma_interpolation n hn ht ht1
  have hlog : Real.log ((n + t) / n) = Real.log (n + t) - Real.log n :=
    Real.log_div hx0.ne' hn0.ne'
  have hu := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hn0)
  rw [hlog] at hu hl
  have hu' : (n : ℝ) * (Real.log (n + t) - Real.log n) ≤ t := by
    have := (mul_le_mul_of_nonneg_left hu hn0.le)
    field_simp at this
    nlinarith
  have hl' : t ≤ ((n : ℝ) + t) * (Real.log (n + t) - Real.log n) := by
    have := (mul_le_mul_of_nonneg_left hl hx0.le)
    simp only [inv_div] at this
    field_simp at this
    nlinarith
  have hlog0 : 0 ≤ Real.log (n + t) - Real.log n := by
    exact sub_nonneg.mpr (Real.log_le_log hn0 (by linarith))
  have hu1 := Real.log_le_sub_one_of_pos (div_pos (show 0 < (n : ℝ) + 1 by positivity) hn0)
  rw [Real.log_div (by positivity) hn0.ne'] at hu1
  have hu1' : (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hu1 hn0.le
    field_simp at this
    nlinarith
  rw [abs_le]
  dsimp only [logStirlingRemainder]
  constructor
  · apply (neg_le_iff_add_nonneg).2
    apply (mul_nonneg_iff_of_pos_left hn0).mp
    have htlog := mul_le_mul_of_nonneg_left hu' (show 0 ≤ t + 1 / 2 by positivity)
    have htt : t * (t + 1 / 2) ≤ 2 := by nlinarith
    have hΓ' := mul_le_mul_of_nonneg_left hΓ.1 hn0.le
    field_simp
    nlinarith
  · apply (le_div_iff₀ hn0).2
    have hΓ' := mul_le_mul_of_nonneg_left hΓ.2 hn0.le
    have htl := mul_le_mul_of_nonneg_left hu1' ht
    have hrem := mul_le_mul_of_nonneg_left hl' hn0.le
    nlinarith [mul_nonneg hn0.le hlog0]

lemma remainder_nat (n : ℕ) (hn : 1 ≤ n) :
    logStirlingRemainder n = Real.log (Stirling.stirlingSeq n) + Real.log 2 / 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logStirlingRemainder, Real.Gamma_nat_eq_factorial,
    Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hn0.ne',
    Real.log_div hn0.ne' (Real.exp_ne_zero 1), Real.log_exp]
  ring

/-- Stirling's formula for real arguments, in logarithmic form. The proof extends
Mathlib's factorial Stirling formula by log-convex interpolation. -/
theorem tendsto_logStirlingRemainder :
    Tendsto logStirlingRemainder atTop
      (𝓝 (Real.log (Real.sqrt Real.pi) + Real.log 2 / 2)) := by
  have hnat : Tendsto (fun n : ℕ ↦ logStirlingRemainder n) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi) + Real.log 2 / 2)) := by
    have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
      (Real.sqrt_pos.2 Real.pi_pos).ne').add_const (Real.log 2 / 2)
    exact h.congr' (eventually_atTop.2 ⟨1, fun n hn ↦ (remainder_nat n hn).symm⟩)
  have hfloor := hnat.comp (tendsto_nat_floor_atTop (α := ℝ))
  have hbound : Tendsto (fun x : ℝ ↦ 2 / (⌊x⌋₊ : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp tendsto_nat_floor_atTop)
  have herr : Tendsto (fun x : ℝ ↦ logStirlingRemainder x -
      logStirlingRemainder ⌊x⌋₊) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hn : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
    have ht : 0 ≤ x - (⌊x⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le (by linarith))
    have ht1 : x - (⌊x⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one x]
    simpa only [Real.norm_eq_abs, add_sub_cancel] using remainder_interpolation ⌊x⌋₊ hn ht ht1
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using herr.add hfloor

/-- The two Gamma arguments and the complete denominator are positive eventually. -/
theorem eventually_gamma_ratio_domain (c : ℝ) :
    ∀ᶠ x : ℝ in atTop, 0 < x ∧ 0 < x + c ∧
      0 < x ^ c * Real.Gamma x := by
  filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
  have hx0 : 0 < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hxc : 0 < x + c := by linarith [le_max_right 0 (-c)]
  exact ⟨hx0, hxc, mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.Gamma_pos_of_pos hx0)⟩

lemma log_gamma_ratio_eq (c x : ℝ) (hx : 0 < x) (hxc : 0 < x + c) :
    Real.log (Real.Gamma (x + c) / (x ^ c * Real.Gamma x)) =
      logStirlingRemainder (x + c) - logStirlingRemainder x +
        x * Real.log (1 + c / x) + (c - 1 / 2) * Real.log (1 + c / x) - c := by
  have hp : 0 < x ^ c := Real.rpow_pos_of_pos hx _
  rw [Real.log_div (Real.Gamma_pos_of_pos hxc).ne'
    (mul_pos hp (Real.Gamma_pos_of_pos hx)).ne',
    Real.log_mul hp.ne' (Real.Gamma_pos_of_pos hx).ne', Real.log_rpow hx]
  have he : 1 + c / x = (x + c) / x := by field_simp
  rw [he, Real.log_div hxc.ne' hx.ne']
  dsimp only [logStirlingRemainder]
  rw [logGamma_add_one hx, logGamma_add_one hxc]
  ring

/-- Exercise 30. Stirling's formula gives the Gamma ratio limit for every real shift. -/
theorem exercise30_gamma_ratio (c : ℝ) :
    Tendsto (fun x : ℝ ↦ Real.Gamma (x + c) / (x ^ c * Real.Gamma x))
      atTop (𝓝 1) := by
  have hs := tendsto_logStirlingRemainder.comp (tendsto_atTop_add_const_right atTop c tendsto_id)
  have hd : Tendsto (fun x : ℝ ↦ logStirlingRemainder (x + c) -
      logStirlingRemainder x) atTop (𝓝 0) := by
    simpa using hs.sub tendsto_logStirlingRemainder
  have hsmall : Tendsto (fun x : ℝ ↦ Real.log (1 + c / x)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun x : ℝ ↦ c / x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa using (tendsto_const_nhds.add hdiv).log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hlog : Tendsto (fun x : ℝ ↦
      Real.log (Real.Gamma (x + c) / (x ^ c * Real.Gamma x))) atTop (𝓝 0) := by
    have h := ((hd.add (Real.tendsto_mul_log_one_add_div_atTop c)).add
      (hsmall.const_mul (c - 1 / 2))).sub_const c
    simp only [zero_add, mul_zero, add_zero, sub_self] at h
    apply h.congr'
    filter_upwards [eventually_gamma_ratio_domain c] with x hx
    exact (log_gamma_ratio_eq c x hx.1 hx.2.1).symm
  have h := (Real.continuous_exp.tendsto 0).comp hlog
  simp only [Real.exp_zero] at h
  apply h.congr'
  filter_upwards [eventually_gamma_ratio_domain c] with x hx
  exact Real.exp_log (div_pos (Real.Gamma_pos_of_pos hx.2.1) hx.2.2)

end Rudin.Chapter08.Exercise30
