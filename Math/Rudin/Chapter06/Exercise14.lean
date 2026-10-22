module

public import Math.Rudin.Chapter06.Exercise13
public import Math.Rudin.Support.EulerIrrational
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Topology.Sequences

/-!
# R06E14: the exponential oscillatory integral

Source: Rudin, Third Edition, Exercise 6.14, book page 140 (PDF page 149).
The instruction to repeat Exercise 13 includes the scaled upper and lower
limits and convergence of proper Riemann truncations.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter MeasureTheory
open scoped Topology
open Rudin.Support.StieltjesPrototype

/-- The function in Exercise 14. -/
noncomputable def exponentialWindow (x : ℝ) : ℝ :=
  ∫ t in x..x + 1, Real.sin (Real.exp t)

/-- Every finite truncation has its literal ordinary Riemann integral. -/
theorem exponential_hasDarboux {a b : ℝ} (hab : a ≤ b) :
    HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (Real.exp t)) id a b
      (∫ t in a..b, Real.sin (Real.exp t)) :=
  continuous_hasDarboux_integral hab (Real.continuous_sin.comp Real.continuous_exp).continuousOn

theorem exponentialWindow_hasDarboux (x : ℝ) :
    HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (Real.exp t)) id x (x + 1)
      (exponentialWindow x) :=
  exponential_hasDarboux (by linarith)

private theorem exponential_antideriv (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -Real.cos (Real.exp t) * Real.exp (-t))
      (Real.sin (Real.exp t) + Real.cos (Real.exp t) * Real.exp (-t)) t := by
  convert (Real.hasDerivAt_exp t).cos.neg.mul ((hasDerivAt_id t).neg.exp) using 1
  · ext s
    rfl
  · dsimp
    simp only [Real.exp_neg]
    field_simp

/-- The first finite-interval integration by parts. -/
theorem exponential_integration_by_parts (a b : ℝ) :
    (∫ t in a..b, Real.sin (Real.exp t)) =
      Real.cos (Real.exp a) * Real.exp (-a) - Real.cos (Real.exp b) * Real.exp (-b) -
        ∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t) := by
  have hs : IntervalIntegrable (fun t : ℝ ↦ Real.sin (Real.exp t)) volume a b :=
    (Real.continuous_sin.comp Real.continuous_exp).intervalIntegrable a b
  have hw : IntervalIntegrable (fun t : ℝ ↦ Real.cos (Real.exp t) * Real.exp (-t)) volume a b :=
    ((Real.continuous_cos.comp Real.continuous_exp).mul
      (Real.continuous_exp.comp continuous_neg)).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun t _ ↦ exponential_antideriv t) (hs.add hw)
  rw [intervalIntegral.integral_add hs hw] at h
  simp only [neg_mul] at h
  linarith

private theorem exponential_weight_integral (a b : ℝ) :
    (∫ t in a..b, Real.exp (-t)) = Real.exp (-a) - Real.exp (-b) := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.exp) (a := a) (b := b) (-1)
  simp only [neg_one_mul, integral_exp] at h
  linarith

private theorem exponential_weight2_integral (a b : ℝ) :
    (∫ t in a..b, Real.exp (-2 * t)) = (Real.exp (-2 * a) - Real.exp (-2 * b)) / 2 := by
  have h := intervalIntegral.mul_integral_comp_mul_left (f := Real.exp) (a := a) (b := b) (-2)
  rw [integral_exp] at h
  linarith

/-- The first correction is bounded by the integral of the decaying weight. -/
theorem exponential_correction_bound {a b : ℝ} (hab : a ≤ b) :
    |∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t)| ≤
      Real.exp (-a) - Real.exp (-b) := by
  rw [← exponential_weight_integral a b]
  apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
  apply intervalIntegral.integral_mono_on hab
    (((Real.continuous_cos.comp Real.continuous_exp).mul
      (Real.continuous_exp.comp continuous_neg)).abs.intervalIntegrable a b)
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable a b)
  intro t _
  change |Real.cos (Real.exp t) * Real.exp (-t)| ≤ Real.exp (-t)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)

private theorem exponential_correction_strict {a b : ℝ} (hab : a < b) :
    |∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t)| <
      Real.exp (-a) - Real.exp (-b) := by
  rw [← exponential_weight_integral a b]
  apply (intervalIntegral.abs_integral_le_integral_abs hab.le).trans_lt
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    ((Real.continuous_cos.comp Real.continuous_exp).mul
      (Real.continuous_exp.comp continuous_neg)).abs.continuousOn
    (Real.continuous_exp.comp continuous_neg).continuousOn
  · intro t _
    change |Real.cos (Real.exp t) * Real.exp (-t)| ≤ Real.exp (-t)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
  · obtain ⟨t, ht, hc⟩ := exists_abs_cos_lt_one (φ := Real.exp) (dφ := Real.exp) hab
      (fun t _ ↦ Real.hasDerivAt_exp t) (fun t _ ↦ Real.exp_ne_zero t)
    refine ⟨t, ht, ?_⟩
    change |Real.cos (Real.exp t) * Real.exp (-t)| < Real.exp (-t)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_lt_of_lt_one_left (Real.exp_pos _) hc

/-- Uniform oscillatory tail estimate; no absolute convergence is assumed. -/
theorem exponential_tail_bound {a b : ℝ} (hab : a ≤ b) :
    |∫ t in a..b, Real.sin (Real.exp t)| ≤ 2 * Real.exp (-a) := by
  rw [exponential_integration_by_parts]
  have hcos (t : ℝ) : |Real.cos (Real.exp t) * Real.exp (-t)| ≤ Real.exp (-t) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
  have h := abs_sub (Real.cos (Real.exp a) * Real.exp (-a) -
    Real.cos (Real.exp b) * Real.exp (-b)) (∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t))
  have h' := abs_sub (Real.cos (Real.exp a) * Real.exp (-a)) (Real.cos (Real.exp b) * Real.exp (-b))
  have hi := exponential_correction_bound hab
  linarith [hcos a, hcos b]

/-- R06E14: the strict decay bound holds for every real `x`. -/
theorem exercise14_decay_bound (x : ℝ) : Real.exp x * |exponentialWindow x| < 2 := by
  have hstrict : |exponentialWindow x| < 2 * Real.exp (-x) := by
    rw [exponentialWindow, exponential_integration_by_parts]
    have hcos (t : ℝ) : |Real.cos (Real.exp t) * Real.exp (-t)| ≤ Real.exp (-t) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have h := abs_sub (Real.cos (Real.exp x) * Real.exp (-x) -
      Real.cos (Real.exp (x + 1)) * Real.exp (-(x + 1)))
      (∫ t in x..x + 1, Real.cos (Real.exp t) * Real.exp (-t))
    have h' := abs_sub (Real.cos (Real.exp x) * Real.exp (-x))
      (Real.cos (Real.exp (x + 1)) * Real.exp (-(x + 1)))
    have hi := exponential_correction_strict (by linarith : x < x + 1)
    linarith [hcos x, hcos (x + 1)]
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_lt_mul_of_pos_left hstrict (Real.exp_pos x)]

private theorem exponential_second_antideriv (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.sin (Real.exp t) * Real.exp (-2 * t))
      (Real.cos (Real.exp t) * Real.exp (-t) - 2 * (Real.sin (Real.exp t) * Real.exp (-2 * t))) t := by
  convert (Real.hasDerivAt_exp t).sin.mul (((hasDerivAt_id t).const_mul (-2)).exp) using 1
  · ext s
    rfl
  · dsimp
    have he : Real.exp t * Real.exp (-2 * t) = Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = Real.cos (Real.exp t) * (Real.exp t * Real.exp (-2 * t)) -
          2 * Real.sin (Real.exp t) * Real.exp (-2 * t) := by rw [he]; ring
      _ = _ := by ring

/-- A second integration by parts gives the smaller asymptotic error. -/
theorem exponential_second_integration_by_parts (a b : ℝ) :
    (∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t)) =
      Real.sin (Real.exp b) * Real.exp (-2 * b) - Real.sin (Real.exp a) * Real.exp (-2 * a) +
        2 * ∫ t in a..b, Real.sin (Real.exp t) * Real.exp (-2 * t) := by
  have hc : IntervalIntegrable (fun t : ℝ ↦ Real.cos (Real.exp t) * Real.exp (-t)) volume a b :=
    ((Real.continuous_cos.comp Real.continuous_exp).mul
      (Real.continuous_exp.comp continuous_neg)).intervalIntegrable a b
  have hs : IntervalIntegrable (fun t : ℝ ↦ 2 * (Real.sin (Real.exp t) * Real.exp (-2 * t))) volume a b :=
    (continuous_const.mul ((Real.continuous_sin.comp Real.continuous_exp).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).intervalIntegrable a b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun t _ ↦ exponential_second_antideriv t) (hc.sub hs)
  rw [intervalIntegral.integral_sub hc hs, intervalIntegral.integral_const_mul] at h
  linarith

/-- The second correction estimate is uniform in the upper endpoint. -/
theorem exponential_correction_bound2 {a b : ℝ} (hab : a ≤ b) :
    |∫ t in a..b, Real.cos (Real.exp t) * Real.exp (-t)| ≤ 2 * Real.exp (-2 * a) := by
  have hs : |∫ t in a..b, Real.sin (Real.exp t) * Real.exp (-2 * t)| ≤
      (Real.exp (-2 * a) - Real.exp (-2 * b)) / 2 := by
    rw [← exponential_weight2_integral a b]
    apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
    apply intervalIntegral.integral_mono_on hab
      (((Real.continuous_sin.comp Real.continuous_exp).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).abs.intervalIntegrable a b)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b)
    intro t _
    change |Real.sin (Real.exp t) * Real.exp (-2 * t)| ≤ Real.exp (-2 * t)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)
  have hsin (t : ℝ) : |Real.sin (Real.exp t) * Real.exp (-2 * t)| ≤ Real.exp (-2 * t) := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_sin_le_one _)
  rw [exponential_second_integration_by_parts]
  have h := abs_add_le (Real.sin (Real.exp b) * Real.exp (-2 * b) - Real.sin (Real.exp a) * Real.exp (-2 * a))
    (2 * ∫ t in a..b, Real.sin (Real.exp t) * Real.exp (-2 * t))
  have h' := abs_sub (Real.sin (Real.exp b) * Real.exp (-2 * b)) (Real.sin (Real.exp a) * Real.exp (-2 * a))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith [hsin a, hsin b]

/-- The error in the exact exponential scaled formula. -/
noncomputable def exponentialRemainder (x : ℝ) : ℝ :=
  -Real.exp x * ∫ t in x..x + 1, Real.cos (Real.exp t) * Real.exp (-t)

/-- R06E14: exact asymptotic identity and a fixed constant `C = 3`. -/
theorem exercise14_asymptotic (x : ℝ) :
    Real.exp x * exponentialWindow x = Real.cos (Real.exp x) -
      Real.exp (-1) * Real.cos (Real.exp (x + 1)) + exponentialRemainder x ∧
      |exponentialRemainder x| < 3 * Real.exp (-x) := by
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have he1 : Real.exp x * Real.exp (-(x + 1)) = Real.exp (-1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [exponentialWindow, exponential_integration_by_parts, exponentialRemainder]
    calc
      _ = (Real.exp x * Real.exp (-x)) * Real.cos (Real.exp x) -
          (Real.exp x * Real.exp (-(x + 1))) * Real.cos (Real.exp (x + 1)) -
          Real.exp x * ∫ t in x..x + 1, Real.cos (Real.exp t) * Real.exp (-t) := by ring
      _ = _ := by rw [he, he1]; ring
  · have h := mul_le_mul_of_nonneg_left
      (exponential_correction_bound2 (by linarith : x ≤ x + 1)) (Real.exp_pos x).le
    have he2 : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    change |-Real.exp x * ∫ t in x..x + 1, Real.cos (Real.exp t) * Real.exp (-t)| < _
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos x)]
    nlinarith [Real.exp_pos (-x)]

/-- The exact error tends to zero. -/
theorem exponentialRemainder_tendsto : Tendsto exponentialRemainder atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x : ℝ ↦ 3 * Real.exp (-x))
  · exact Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using (exercise14_asymptotic x).2.le
  · simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 3

/-- R06E14: convergence of the improper Riemann integral, with a proper
Darboux witness at every truncation. -/
theorem exercise14_improper_convergence :
    ∃ I : ℝ, (∀ b ≥ (0 : ℝ), HasDarbouxRSIntegral (fun t : ℝ ↦ Real.sin (Real.exp t))
      id 0 b (∫ t in 0..b, Real.sin (Real.exp t))) ∧
      Tendsto (fun b : ℝ ↦ ∫ t in 0..b, Real.sin (Real.exp t)) atTop (𝓝 I) := by
  apply improper_integral_of_tail_bound (ρ := fun a ↦ 2 * Real.exp (-a))
    (Real.continuous_sin.comp Real.continuous_exp)
    (by simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2)
  intro a b _ hab
  exact exponential_tail_bound hab

/-- The irrationality needed for the two exponential phase sequences.
This uses a finite exponential-series remainder bound. -/
theorem exponential_phase_irrational : Irrational (Real.exp 1) :=
  Rudin.Support.EulerIrrational.irrational_exp_one

/-- Irrational rotation supplies genuine phase sequences in every required
phase class. The first cosine is exact and the second approaches its target. -/
theorem exponential_phase_sequence (δ β : ℝ) (hδ : 0 ≤ δ) :
    ∃ x : ℕ → ℝ, Tendsto x atTop atTop ∧
      (∀ n, Real.cos (Real.exp (x n)) = Real.cos δ) ∧
      Tendsto (fun n ↦ Real.cos (Real.exp (x n + 1))) atTop (𝓝 (Real.cos β)) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let : CompactSpace Real.Angle := AddCircle.compactSpace (2 * Real.pi)
  let a : Real.Angle := ((2 * Real.pi * Real.exp 1 : ℝ) : Real.Angle)
  have hirr : Irrational ((2 * Real.pi * Real.exp 1) / (2 * Real.pi)) := by
    have he : (2 * Real.pi * Real.exp 1) / (2 * Real.pi) = Real.exp 1 := by field_simp
    rw [he]
    exact exponential_phase_irrational
  have hd : DenseRange (fun k : ℤ ↦ k • a) := by
    exact AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  let c : Real.Angle := ((Real.exp 1 * (δ + 2 * Real.pi) : ℝ) : Real.Angle)
  let target : Real.Angle := (β : Real.Angle) - c
  have hcluster : MapClusterPt target atTop (fun n : ℕ ↦ n • a) :=
    ((mapClusterPt_atTop_nsmul_tfae target a).out 1 4).mpr (hd target)
  obtain ⟨ns, hns, hr⟩ := hcluster.tendsto_subseq
  let y : ℕ → ℝ := fun n ↦ δ + ((ns n : ℝ) + 1) * (2 * Real.pi)
  have hypos (n : ℕ) : 0 < y n := by dsimp only [y]; positivity
  have hnCast : Tendsto (fun n ↦ (ns n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
  have hy : Tendsto y atTop atTop := by
    have h := ((hnCast.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).atTop_mul_const
      (by positivity : 0 < 2 * Real.pi)).atTop_add (tendsto_const_nhds (x := δ))
    simpa only [y, add_comm] using h
  have hshift := hr.add (tendsto_const_nhds (x := c))
  have hangle : Tendsto (fun n ↦ ((Real.exp 1 * y n : ℝ) : Real.Angle)) atTop
      (𝓝 (β : Real.Angle)) := by
    have hlim : target + c = (β : Real.Angle) := sub_add_cancel _ _
    rw [hlim] at hshift
    apply Filter.Tendsto.congr' _ hshift
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_def, a, c, y]
    rw [← Real.Angle.natCast_mul_eq_nsmul, ← Real.Angle.coe_add]
    congr 1
    ring
  have hcos : Tendsto (fun n ↦ Real.cos (Real.exp 1 * y n)) atTop (𝓝 (Real.cos β)) := by
    simpa only [Function.comp_def, Real.Angle.cos_coe] using
      Real.Angle.continuous_cos.continuousAt.tendsto.comp hangle
  refine ⟨fun n ↦ Real.log (y n), Real.tendsto_log_atTop.comp hy, ?_, ?_⟩
  · intro n
    rw [Real.exp_log (hypos n)]
    change Real.cos (δ + ((ns n : ℝ) + 1) * (2 * Real.pi)) = Real.cos δ
    simpa only [Nat.cast_add, Nat.cast_one] using Real.cos_add_nat_mul_two_pi δ (ns n + 1)
  · convert hcos using 1
    ext n
    rw [Real.exp_add, Real.exp_log (hypos n), mul_comm]

/-- Applying the asymptotic formula along the actual phase sequences. -/
theorem exponential_scaled_phase_sequence (δ β : ℝ) (hδ : 0 ≤ δ) :
    ∃ x : ℕ → ℝ, Tendsto x atTop atTop ∧
      Tendsto (fun n ↦ Real.exp (x n) * exponentialWindow (x n)) atTop
        (𝓝 (Real.cos δ - Real.exp (-1) * Real.cos β)) := by
  obtain ⟨x, hx, hc, hc'⟩ := exponential_phase_sequence δ β hδ
  refine ⟨x, hx, ?_⟩
  have hr := exponentialRemainder_tendsto.comp hx
  have h := ((tendsto_const_nhds (x := Real.cos δ)).sub
    (hc'.const_mul (Real.exp (-1)))).add hr
  simp only [add_zero] at h
  apply Filter.Tendsto.congr' _ h
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [← hc n]
  exact (exercise14_asymptotic (x n)).1.symm

/-- Both extremal values are approached on sequences tending to infinity. -/
theorem exercise14_limit_sequences :
    ∃ u v : ℕ → ℝ, Tendsto u atTop atTop ∧ Tendsto v atTop atTop ∧
      Tendsto (fun n ↦ Real.exp (u n) * exponentialWindow (u n)) atTop
        (𝓝 (1 + Real.exp (-1))) ∧
      Tendsto (fun n ↦ Real.exp (v n) * exponentialWindow (v n)) atTop
        (𝓝 (-(1 + Real.exp (-1)))) := by
  obtain ⟨u, hu, hU⟩ := exponential_scaled_phase_sequence 0 Real.pi le_rfl
  obtain ⟨v, hv, hL⟩ := exponential_scaled_phase_sequence Real.pi 0 Real.pi_pos.le
  refine ⟨u, v, hu, hv, ?_, ?_⟩
  · simpa only [Real.cos_zero, Real.cos_pi, mul_neg_one, sub_neg_eq_add] using hU
  · have he : Real.cos Real.pi - Real.exp (-1) * Real.cos 0 = -(1 + Real.exp (-1)) := by
      rw [Real.cos_pi, Real.cos_zero, mul_one]
      ring
    rwa [he] at hL

/-- R06E14: the scaled limits are `±(1 + exp(-1))`, not `±2`. -/
theorem exercise14_limits :
    limsup (fun x : ℝ ↦ Real.exp x * exponentialWindow x) atTop = 1 + Real.exp (-1) ∧
      liminf (fun x : ℝ ↦ Real.exp x * exponentialWindow x) atTop = -(1 + Real.exp (-1)) := by
  obtain ⟨u, v, hu, hv, hU, hL⟩ := exercise14_limit_sequences
  apply limsup_liminf_of_bounds_and_sequences _ hu hv hU hL
  intro ε hε
  filter_upwards [exponentialRemainder_tendsto.eventually
    (Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε)] with x hx
  have ha : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hc := abs_le.mp (Real.abs_cos_le_one (Real.exp x))
  have hc' := abs_le.mp (Real.abs_cos_le_one (Real.exp (x + 1)))
  have hl := mul_le_mul_of_nonneg_left hc'.1 ha
  have hu' := mul_le_mul_of_nonneg_left hc'.2 ha
  have hid := (exercise14_asymptotic x).1
  constructor <;> linarith [hx.1, hx.2]

end Rudin.Chapter06
