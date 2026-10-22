module

public import Math.Rudin.Support.StieltjesMeasureBridge
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# R06E13: the quadratic oscillatory integral

Source: Rudin, Third Edition, Exercise 6.13, book page 140 (PDF page 149).
Finite interval integrals below have literal closed-cell Darboux witnesses.
Improper convergence means convergence of these finite interval values, not
an integral over the whole half-line.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open scoped Topology
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesMeasureBridge

/-- The ordinary continuous-integrand bridge, with the identity integrator. -/
theorem continuous_hasDarboux_integral {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    HasDarbouxRSIntegral g id a b (∫ t in a..b, g t) := by
  have h := continuous_bridge StieltjesFunction.id hab hg
  rwa [← Real.volume_eq_stieltjes_id] at h

/-- A phase with nonzero derivative cannot have cosine of absolute value one
on a nondegenerate interval. -/
theorem exists_abs_cos_lt_one {φ dφ : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt φ (dφ t) t)
    (hne : ∀ t ∈ Ioo a b, dφ t ≠ 0) :
    ∃ t ∈ Icc a b, |Real.cos (φ t)| < 1 := by
  by_contra! h
  have hc (t : ℝ) (ht : t ∈ Icc a b) : |Real.cos (φ t)| = 1 :=
    le_antisymm (Real.abs_cos_le_one _) (h t ht)
  have hs (t : ℝ) (ht : t ∈ Icc a b) : Real.sin (φ t) = 0 := by
    have he := congrArg (fun x : ℝ ↦ x ^ 2) (hc t ht)
    rw [sq_abs] at he
    have := Real.sin_sq_add_cos_sq (φ t)
    nlinarith [sq_nonneg (Real.sin (φ t))]
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hz : HasDerivAt (fun t ↦ Real.sin (φ t)) 0 m := by
    apply (hasDerivAt_const m (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with t ht
    exact hs t ⟨ht.1.le, ht.2.le⟩
  have he := ((hd m hm).sin).unique hz
  have hncos : Real.cos (φ m) ≠ 0 := by
    intro hz
    simpa [hz] using hc m ⟨hm.1.le, hm.2.le⟩
  exact (mul_ne_zero hncos (hne m hm)) he

/-- A tail estimate proves convergence of proper Riemann truncations. No
absolute integrability on an unbounded interval is assumed. -/
theorem improper_integral_of_tail_bound {g ρ : ℝ → ℝ} (hg : Continuous g)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (htail : ∀ a b : ℝ, 1 ≤ a → a ≤ b → |∫ t in a..b, g t| ≤ ρ a) :
    ∃ I : ℝ, (∀ b ≥ (0 : ℝ), HasDarbouxRSIntegral g id 0 b (∫ t in 0..b, g t)) ∧
      Tendsto (fun b : ℝ ↦ ∫ t in 0..b, g t) atTop (𝓝 I) := by
  have hc : CauchySeq (fun b : ℝ ↦ ∫ t in 0..b, g t) := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    obtain ⟨N, hN, hsmall⟩ := ((eventually_ge_atTop (1 : ℝ)).and
      (hρ.eventually (gt_mem_nhds hε))).exists
    refine ⟨N, fun b hb ↦ ?_⟩
    rw [Real.dist_eq, intervalIntegral.integral_interval_sub_left
      (hg.intervalIntegrable 0 b) (hg.intervalIntegrable 0 N)]
    exact (htail N b hN hb).trans_lt hsmall
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨I, fun b hb ↦ continuous_hasDarboux_integral hb hg.continuousOn, hI⟩

/-- The function in Exercise 13. -/
noncomputable def quadraticWindow (x : ℝ) : ℝ :=
  ∫ t in x..x + 1, Real.sin (t ^ 2)

/-- Every finite truncation is an actual proper Riemann integral. -/
theorem quadratic_hasDarboux {a b : ℝ} (hab : a ≤ b) :
    HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (t ^ 2)) id a b
      (∫ t in a..b, Real.sin (t ^ 2)) :=
  continuous_hasDarboux_integral hab (Real.continuous_sin.comp (continuous_id.pow 2)).continuousOn

theorem quadraticWindow_hasDarboux (x : ℝ) :
    HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (t ^ 2)) id x (x + 1)
      (quadraticWindow x) :=
  quadratic_hasDarboux (by linarith)

private theorem quadratic_weight_continuous {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ ↦ 1 / (2 * t ^ 2)) (Icc a b) := by
  apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2))
  intro t ht
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))

private theorem quadratic_cos_weight_continuous {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ ↦ Real.cos (t ^ 2) / (2 * t ^ 2)) (Icc a b) := by
  apply (Real.continuous_cos.comp (continuous_id.pow 2)).continuousOn.div
    (continuousOn_const.mul (continuousOn_id.pow 2))
  intro t ht
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1)))

private theorem quadratic_antideriv (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ -Real.cos (t ^ 2) / (2 * t))
      (Real.sin (t ^ 2) + Real.cos (t ^ 2) / (2 * t ^ 2)) t := by
  convert (((hasDerivAt_pow 2 t).cos.neg).div
    ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht)) using 1
  · ext s
    simp only [Pi.div_apply, Pi.neg_apply, id_eq]
  · dsimp
    field_simp
    ring

/-- Integration by parts on an arbitrary positive finite interval. -/
theorem quadratic_integration_by_parts {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.sin (t ^ 2)) =
      Real.cos (a ^ 2) / (2 * a) - Real.cos (b ^ 2) / (2 * b) -
        ∫ t in a..b, Real.cos (t ^ 2) / (2 * t ^ 2) := by
  have hs : IntervalIntegrable (fun t : ℝ ↦ Real.sin (t ^ 2)) volume a b :=
    (Real.continuous_sin.comp (continuous_id.pow 2)).intervalIntegrable a b
  have hw := (quadratic_cos_weight_continuous (b := b) ha).intervalIntegrable_of_Icc
    (μ := volume) hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun t ht ↦ quadratic_antideriv t (ne_of_gt (ha.trans_le ((uIcc_of_le hab) ▸ ht).1)))
    (hs.add hw)
  rw [intervalIntegral.integral_add hs hw] at h
  simp only [neg_div] at h
  linarith

private theorem quadratic_weight_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (2 * t ^ 2)) = 1 / (2 * a) - 1 / (2 * b) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (f := fun t : ℝ ↦ -(1 / (2 * t))) (f' := fun t : ℝ ↦ 1 / (2 * t ^ 2))
    (fun t ht ↦ by
      have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le ((uIcc_of_le hab) ▸ ht).1)
      convert ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).const_mul 2)
        (mul_ne_zero (by norm_num) ht0)).neg using 1
      · ext s
        simp only [Pi.neg_apply, Pi.div_apply, id_eq]
      · dsimp
        field_simp
        ring)
    ((quadratic_weight_continuous ha).intervalIntegrable_of_Icc hab)
  linarith

/-- The integration-by-parts remainder has a uniform tail bound. -/
theorem quadratic_correction_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, Real.cos (t ^ 2) / (2 * t ^ 2)| ≤
      1 / (2 * a) - 1 / (2 * b) := by
  rw [← quadratic_weight_integral ha hab]
  apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
  apply intervalIntegral.integral_mono_on hab
    ((quadratic_cos_weight_continuous ha).abs.intervalIntegrable_of_Icc hab)
    ((quadratic_weight_continuous ha).intervalIntegrable_of_Icc hab)
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t ^ 2)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)

private theorem quadratic_correction_strict {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    |∫ t in a..b, Real.cos (t ^ 2) / (2 * t ^ 2)| <
      1 / (2 * a) - 1 / (2 * b) := by
  rw [← quadratic_weight_integral ha hab.le]
  apply (intervalIntegral.abs_integral_le_integral_abs hab.le).trans_lt
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    (quadratic_cos_weight_continuous ha).abs (quadratic_weight_continuous ha)
  · intro t ht
    have ht0 : 0 < t := ha.trans ht.1
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t ^ 2)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  · obtain ⟨t, ht, hc⟩ := exists_abs_cos_lt_one (φ := fun t : ℝ ↦ t ^ 2)
      (dφ := fun t ↦ 2 * t) hab
      (fun t _ ↦ by simpa using hasDerivAt_pow 2 t)
      (fun t ht ↦ mul_ne_zero (by norm_num) (ne_of_gt (ha.trans ht.1)))
    refine ⟨t, ht, ?_⟩
    have ht0 : 0 < t := ha.trans_le ht.1
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t ^ 2)]
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr hc

/-- A tail estimate independent of the upper endpoint. -/
theorem quadratic_tail_bound {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |∫ t in a..b, Real.sin (t ^ 2)| ≤ 1 / a := by
  rw [quadratic_integration_by_parts ha hab]
  have hb : 0 < b := ha.trans_le hab
  have hcos (t : ℝ) (ht : 0 < t) : |Real.cos (t ^ 2) / (2 * t)| ≤ 1 / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have h := abs_sub (Real.cos (a ^ 2) / (2 * a) - Real.cos (b ^ 2) / (2 * b))
    (∫ t in a..b, Real.cos (t ^ 2) / (2 * t ^ 2))
  have h' := abs_sub (Real.cos (a ^ 2) / (2 * a)) (Real.cos (b ^ 2) / (2 * b))
  have hw := quadratic_correction_bound ha hab
  have hca := hcos a ha
  have hcb := hcos b hb
  have he : 1 / (2 * a) + 1 / (2 * a) = 1 / a := by ring
  linarith

/-- R06E13(a): the strict decay estimate. -/
theorem exercise13_a {x : ℝ} (hx : 0 < x) : |quadraticWindow x| < 1 / x := by
  rw [quadraticWindow, quadratic_integration_by_parts hx (by linarith)]
  have hb : 0 < x + 1 := by linarith
  have hcos (t : ℝ) (ht : 0 < t) : |Real.cos (t ^ 2) / (2 * t)| ≤ 1 / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t)]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
  have h := abs_sub (Real.cos (x ^ 2) / (2 * x) - Real.cos ((x + 1) ^ 2) / (2 * (x + 1)))
    (∫ t in x..x + 1, Real.cos (t ^ 2) / (2 * t ^ 2))
  have h' := abs_sub (Real.cos (x ^ 2) / (2 * x)) (Real.cos ((x + 1) ^ 2) / (2 * (x + 1)))
  have hw := quadratic_correction_strict hx (by linarith : x < x + 1)
  have hca := hcos x hx
  have hcb := hcos (x + 1) hb
  have he : 1 / (2 * x) + 1 / (2 * x) = 1 / x := by ring
  linarith

/-- The error in the exact scaled formula. -/
noncomputable def quadraticRemainder (x : ℝ) : ℝ :=
  Real.cos ((x + 1) ^ 2) / (x + 1) -
    2 * x * ∫ t in x..x + 1, Real.cos (t ^ 2) / (2 * t ^ 2)

/-- R06E13(b), with the fixed constant `c = 2`. -/
theorem exercise13_b {x : ℝ} (hx : 0 < x) :
    2 * x * quadraticWindow x = Real.cos (x ^ 2) - Real.cos ((x + 1) ^ 2) +
      quadraticRemainder x ∧ |quadraticRemainder x| < 2 / x := by
  have hx1 : 0 < x + 1 := by linarith
  constructor
  · rw [quadraticWindow, quadratic_integration_by_parts hx (by linarith), quadraticRemainder]
    field_simp
    ring
  · have hc : |Real.cos ((x + 1) ^ 2) / (x + 1)| ≤ 1 / (x + 1) := by
      rw [abs_div, abs_of_pos hx1]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) hx1.le
    have hi := quadratic_correction_bound hx (by linarith : x ≤ x + 1)
    have h := abs_sub (Real.cos ((x + 1) ^ 2) / (x + 1))
      (2 * x * ∫ t in x..x + 1, Real.cos (t ^ 2) / (2 * t ^ 2))
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * x)] at h
    have hm := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * x)
    have he : 1 / (x + 1) + 2 * x * (1 / (2 * x) - 1 / (2 * (x + 1))) =
        2 / (x + 1) := by field_simp; ring
    have hlt : 2 / (x + 1) < 2 / x := by
      exact div_lt_div_of_pos_left (by norm_num) hx (by linarith)
    change |Real.cos ((x + 1) ^ 2) / (x + 1) -
      2 * x * ∫ t in x..x + 1, Real.cos (t ^ 2) / (2 * t ^ 2)| < 2 / x
    linarith

/-- The exact remainder tends to zero. -/
theorem quadraticRemainder_tendsto : Tendsto quadraticRemainder atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ 2 / x)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simpa only [Real.norm_eq_abs] using (exercise13_b hx).2.le
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- R06E13(d): convergence of the improper Riemann integral, with witnesses
at every nonnegative truncation. -/
theorem exercise13_d :
    ∃ I : ℝ, (∀ b ≥ (0 : ℝ), HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (t ^ 2))
      id 0 b (∫ t in 0..b, Real.sin (t ^ 2))) ∧
      Tendsto (fun b : ℝ ↦ ∫ t in 0..b, Real.sin (t ^ 2)) atTop (𝓝 I) := by
  apply improper_integral_of_tail_bound (ρ := fun a ↦ 1 / a)
    (Real.continuous_sin.comp (continuous_id.pow 2))
    (tendsto_const_nhds.div_atTop tendsto_id)
  intro a b ha hab
  exact quadratic_tail_bound (by linarith) hab

/-- Bounds with vanishing error and two actual approaching sequences determine
both scaled limits. -/
theorem limsup_liminf_of_bounds_and_sequences {g : ℝ → ℝ} {L U : ℝ}
    (hb : ∀ ε > (0 : ℝ), ∀ᶠ x in atTop, L - ε ≤ g x ∧ g x ≤ U + ε)
    {u v : ℕ → ℝ} (hu : Tendsto u atTop atTop) (hv : Tendsto v atTop atTop)
    (hU : Tendsto (fun n ↦ g (u n)) atTop (𝓝 U))
    (hL : Tendsto (fun n ↦ g (v n)) atTop (𝓝 L)) :
    limsup g atTop = U ∧ liminf g atTop = L := by
  have hlo : IsBoundedUnder (· ≥ ·) atTop g := ⟨L - 1, (hb 1 zero_lt_one).mono fun _ h ↦ h.1⟩
  have hhi : IsBoundedUnder (· ≤ ·) atTop g := ⟨U + 1, (hb 1 zero_lt_one).mono fun _ h ↦ h.2⟩
  constructor
  · apply le_antisymm
    · apply (limsup_le_iff hlo.isCoboundedUnder_le hhi).mpr
      intro y hy
      filter_upwards [hb ((y - U) / 2) (by linarith)] with x hx
      linarith [hx.2]
    · have h := hu.limsup_comp_le_limsup (hlo.mono hu).isCoboundedUnder_le hhi
      rwa [show limsup (g ∘ u) atTop = U from hU.limsup_eq] at h
  · apply le_antisymm
    · have h := hv.liminf_le_liminf_comp (hhi.mono hv).isCoboundedUnder_ge hlo
      rwa [show liminf (g ∘ v) atTop = L from hL.liminf_eq] at h
    · apply (le_liminf_iff hhi.isCoboundedUnder_ge hlo).mpr
      intro y hy
      filter_upwards [hb ((L - y) / 2) (by linarith)] with x hx
      linarith [hx.1]

/-- The target centers make the phase difference tend to an odd multiple of π. -/
noncomputable def quadraticPhaseCenter (n : ℕ) : ℝ :=
  Real.pi * ((n : ℝ) + 1) + (Real.pi - 1) / 2

/-- Round the square of a center down to the required phase class. -/
noncomputable def quadraticPhaseIndex (δ : ℝ) (n : ℕ) : ℕ :=
  ⌊(quadraticPhaseCenter n ^ 2 - δ) / (2 * Real.pi)⌋₊

/-- `δ = 0` gives the upper sequence; `δ = π` gives the lower sequence. -/
noncomputable def quadraticPhaseSample (δ : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.pi * (quadraticPhaseIndex δ n : ℝ) + δ)

private theorem quadraticPhaseCenter_pos (n : ℕ) :
    Real.pi ≤ quadraticPhaseCenter n ∧ 0 < quadraticPhaseCenter n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp := Real.pi_gt_three
  dsimp only [quadraticPhaseCenter]
  constructor <;> nlinarith

private theorem quadraticPhaseSample_sq {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    quadraticPhaseSample δ n ^ 2 = 2 * Real.pi * (quadraticPhaseIndex δ n : ℝ) + δ :=
  Real.sq_sqrt (add_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) hδ)

private theorem quadraticPhaseSample_gap {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (n : ℕ) :
    quadraticPhaseSample δ n ≤ quadraticPhaseCenter n ∧
      |quadraticPhaseSample δ n - quadraticPhaseCenter n| ≤
        2 * Real.pi / quadraticPhaseCenter n := by
  have hy := quadraticPhaseCenter_pos n
  have hy2 : δ ≤ quadraticPhaseCenter n ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have harg : 0 ≤ (quadraticPhaseCenter n ^ 2 - δ) / (2 * Real.pi) := by positivity
  have hlo := Nat.floor_le harg
  have hhi := Nat.lt_floor_add_one ((quadraticPhaseCenter n ^ 2 - δ) / (2 * Real.pi))
  change (quadraticPhaseIndex δ n : ℝ) ≤ _ at hlo
  change _ < (quadraticPhaseIndex δ n : ℝ) + 1 at hhi
  have hlo' := (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hlo
  have hhi' := (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp hhi
  have hx0 : 0 ≤ quadraticPhaseSample δ n := Real.sqrt_nonneg _
  have hxsq := quadraticPhaseSample_sq hδ n
  have hxy : quadraticPhaseSample δ n ≤ quadraticPhaseCenter n := by nlinarith
  refine ⟨hxy, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
  apply (le_div_iff₀ hy.2).mpr
  have := mul_nonneg hx0 (sub_nonneg.mpr hxy)
  nlinarith

theorem quadraticPhaseCenter_tendsto : Tendsto quadraticPhaseCenter atTop atTop := by
  have h := ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop Real.pi_pos).atTop_add
    (tendsto_const_nhds (x := Real.pi + (Real.pi - 1) / 2))
  convert h using 1
  ext n
  dsimp only [quadraticPhaseCenter]
  ring

theorem quadraticPhaseSample_sub_tendsto {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun n ↦ quadraticPhaseSample δ n - quadraticPhaseCenter n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun n ↦ 2 * Real.pi / quadraticPhaseCenter n)
  · exact Eventually.of_forall fun n ↦ by
      simpa only [Real.norm_eq_abs] using (quadraticPhaseSample_gap hδ hδπ n).2
  · exact tendsto_const_nhds.div_atTop quadraticPhaseCenter_tendsto

theorem quadraticPhaseSample_tendsto {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (quadraticPhaseSample δ) atTop atTop := by
  have h := quadraticPhaseCenter_tendsto.atTop_add (quadraticPhaseSample_sub_tendsto hδ hδπ)
  simpa only [add_sub_cancel] using h

private theorem quadraticPhaseSample_cos {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    Real.cos (quadraticPhaseSample δ n ^ 2) = Real.cos δ := by
  rw [quadraticPhaseSample_sq hδ]
  convert Real.cos_add_nat_mul_two_pi δ (quadraticPhaseIndex δ n) using 1
  congr 1
  ring

private theorem quadraticPhaseSample_cos_next {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    Real.cos ((quadraticPhaseSample δ n + 1) ^ 2) =
      Real.cos (δ + Real.pi + 2 * (quadraticPhaseSample δ n - quadraticPhaseCenter n)) := by
  have hs := quadraticPhaseSample_sq hδ n
  calc
    _ = Real.cos ((δ + Real.pi + 2 * (quadraticPhaseSample δ n - quadraticPhaseCenter n)) +
        ((quadraticPhaseIndex δ n + n + 1 : ℕ) : ℝ) * (2 * Real.pi)) := by
      congr 1
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp only [quadraticPhaseCenter]
      nlinarith
    _ = _ := Real.cos_add_nat_mul_two_pi _ _

/-- The rounded phases approach the required endpoint values. -/
theorem quadraticPhaseSample_scaled_tendsto {δ : ℝ} (hδ : 0 ≤ δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun n ↦ quadraticPhaseSample δ n * quadraticWindow (quadraticPhaseSample δ n))
      atTop (𝓝 ((Real.cos δ - Real.cos (δ + Real.pi)) / 2)) := by
  have hx := quadraticPhaseSample_tendsto hδ hδπ
  have he := quadraticPhaseSample_sub_tendsto hδ hδπ
  have hp := (tendsto_const_nhds (x := δ + Real.pi)).add (he.const_mul 2)
  have hc : Tendsto
      (fun n ↦ Real.cos (δ + Real.pi + 2 * (quadraticPhaseSample δ n - quadraticPhaseCenter n)))
      atTop (𝓝 (Real.cos (δ + Real.pi))) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp hp
  have hr := quadraticRemainder_tendsto.comp hx
  have ht := (((tendsto_const_nhds (x := Real.cos δ)).sub hc).add hr).div_const 2
  simp only [add_zero] at ht
  apply Filter.Tendsto.congr' _ ht
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  have h := (exercise13_b hn).1
  rw [quadraticPhaseSample_cos hδ, quadraticPhaseSample_cos_next hδ] at h
  dsimp only [Function.comp_def]
  linarith

/-- Explicit upper and lower phase sequences, not just bounds. -/
theorem exercise13_c_sequences :
    Tendsto (quadraticPhaseSample 0) atTop atTop ∧
    Tendsto (fun n ↦ quadraticPhaseSample 0 n * quadraticWindow (quadraticPhaseSample 0 n))
      atTop (𝓝 1) ∧
    Tendsto (quadraticPhaseSample Real.pi) atTop atTop ∧
    Tendsto (fun n ↦ quadraticPhaseSample Real.pi n * quadraticWindow (quadraticPhaseSample Real.pi n))
      atTop (𝓝 (-1)) := by
  refine ⟨quadraticPhaseSample_tendsto le_rfl Real.pi_pos.le, ?_,
    quadraticPhaseSample_tendsto Real.pi_pos.le le_rfl, ?_⟩
  · simpa using quadraticPhaseSample_scaled_tendsto le_rfl Real.pi_pos.le
  · have h := quadraticPhaseSample_scaled_tendsto Real.pi_pos.le le_rfl
    norm_num only [Real.cos_add_pi, Real.cos_pi, neg_neg] at h
    exact h

/-- R06E13(c): the upper scaled limit is `1` and the lower scaled limit is `-1`. -/
theorem exercise13_c :
    limsup (fun x : ℝ ↦ x * quadraticWindow x) atTop = 1 ∧
      liminf (fun x : ℝ ↦ x * quadraticWindow x) atTop = -1 := by
  obtain ⟨hu, hU, hv, hL⟩ := exercise13_c_sequences
  apply limsup_liminf_of_bounds_and_sequences (u := quadraticPhaseSample 0)
    (v := quadraticPhaseSample Real.pi) _ hu hv hU hL
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have h : |x * quadraticWindow x| < 1 := by
    calc
      _ = x * |quadraticWindow x| := by rw [abs_mul, abs_of_pos hx]
      _ < x * (1 / x) := mul_lt_mul_of_pos_left (exercise13_a hx) hx
      _ = 1 := by field_simp
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

end Rudin.Chapter06
