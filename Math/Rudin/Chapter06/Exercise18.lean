module

public import Math.Rudin.Chapter06.Exercise19
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Field.Periodic

/-!
# R06E18: three curves with one range

The printed third formula is used only off zero. Its endpoint value is explicitly
set to one. Length is the supremum of source partition chord sums from Exercise 19,
with the proved comparison to variation. All norms are the usual complex norm.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Filter
open scoped Topology ENNReal

/-- The usual angular parameterization of the unit circle. -/
noncomputable def circleAngle (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

/-- The first printed curve. -/
noncomputable def exercise18_gamma1 (t : ℝ) : ℂ := circleAngle t

/-- The second printed curve. -/
noncomputable def exercise18_gamma2 (t : ℝ) : ℂ := circleAngle (2 * t)

/-- The real phase before multiplication by `2πi`. -/
noncomputable def exercise18_phase (t : ℝ) : ℝ := t * Real.sin (1 / t)

/-- The continuous endpoint repair; no source reciprocal at zero is asserted. -/
noncomputable def exercise18_gamma3 (t : ℝ) : ℂ :=
  if t = 0 then 1 else circleAngle (2 * Real.pi * exercise18_phase t)

@[simp] theorem circleAngle_norm (t : ℝ) : ‖circleAngle t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I t

theorem circleAngle_continuous : Continuous circleAngle := by
  unfold circleAngle
  fun_prop

@[simp] theorem exercise18_gamma3_zero : exercise18_gamma3 0 = 1 := by
  simp [exercise18_gamma3]

/-- On the printed domain the exponent is exactly the source exponent. -/
theorem exercise18_gamma3_positive {t : ℝ} (ht : 0 < t) :
    exercise18_gamma3 t =
      Complex.exp (2 * Real.pi * Complex.I * t * (Real.sin (1 / t) : ℂ)) := by
  rw [exercise18_gamma3, ite_eq_right_iff.mpr (fun h => (ht.ne' h).elim)]
  simp only [circleAngle, exercise18_phase, Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  ring

private theorem phase_bound (t : ℝ) : |exercise18_phase t| ≤ |t| := by
  simpa [exercise18_phase, abs_mul] using
    mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (1 / t)) (abs_nonneg t)

/-- The phase tends to zero although its derivative oscillates without a finite total variation. -/
theorem exercise18_phase_continuous : Continuous exercise18_phase := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hp : exercise18_phase 0 = 0 := by simp [exercise18_phase]
    rw [ContinuousAt, hp]
    exact squeeze_zero_norm (fun x => by simpa [Real.norm_eq_abs] using phase_bound x)
      (by simpa using (continuous_abs.continuousAt.tendsto :
        Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 |(0 : ℝ)|)))
  · unfold exercise18_phase
    exact continuousAt_id.mul (Real.continuous_sin.continuousAt.comp
      (continuousAt_const.div continuousAt_id ht))

/-- R06E18.endpoint_extension: the repaired function is an actual continuous curve. -/
theorem exercise18_endpoint_extension :
    exercise18_gamma3 0 = 1 ∧ Continuous exercise18_gamma3 := by
  refine ⟨exercise18_gamma3_zero, ?_⟩
  have heq : exercise18_gamma3 = fun t => circleAngle (2 * Real.pi * exercise18_phase t) := by
    funext t
    by_cases ht : t = 0 <;> simp [exercise18_gamma3, ht, exercise18_phase, circleAngle]
  rw [heq]
  exact circleAngle_continuous.comp (continuous_const.mul exercise18_phase_continuous)

/-- The printed reciprocal has no real value at zero. The repaired curve instead
has the explicitly supplied endpoint one. -/
theorem exercise18_printed_endpoint_obstruction :
    (¬ ∃ u : ℝ, (0 : ℝ) * u = 1) ∧ exercise18_gamma3 0 = 1 := by
  simp only [zero_mul, zero_ne_one, exists_const, not_false_eq_true,
    exercise18_gamma3_zero, and_self]

/-- The missing endpoint is forced by continuity, not by totalized division. -/
theorem exercise18_endpoint_unique {γ : ℝ → ℂ} (hc : ContinuousWithinAt γ (Icc 0 (2 * Real.pi)) 0)
    (heq : ∀ t ∈ Ioc 0 (2 * Real.pi), γ t = exercise18_gamma3 t) : γ 0 = 1 := by
  have hpos : 0 < 2 * Real.pi := by positivity
  have hmem : Ioc 0 (2 * Real.pi) ∈ 𝓝[>] (0 : ℝ) :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hpos))
  have hc' : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) :=
    hc.mono_left (nhdsWithin_le_of_mem (Filter.mem_of_superset hmem Ioc_subset_Icc_self))
  have h3 : Tendsto exercise18_gamma3 (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    have h : Tendsto exercise18_gamma3 (𝓝 (0 : ℝ)) (𝓝 (exercise18_gamma3 0)) :=
      exercise18_endpoint_extension.2.continuousAt
    simpa only [exercise18_gamma3_zero] using h.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hc' (h3.congr' (eventually_nhdsWithin_iff.mpr
    (Filter.mem_of_superset (Iic_mem_nhds hpos) (fun t ht hp => (heq t ⟨hp, ht⟩).symm))))

/-- Distance between two angular points, with the usual complex norm. -/
theorem circleAngle_dist (s t : ℝ) :
    dist (circleAngle s) (circleAngle t) = |2 * Real.sin ((s - t) / 2)| := by
  have heq : circleAngle s - circleAngle t =
      circleAngle t * (circleAngle (s - t) - 1) := by
    unfold circleAngle
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [dist_eq_norm, heq, norm_mul, circleAngle_norm, one_mul]
  simpa [circleAngle, mul_comm Complex.I] using Complex.norm_exp_I_mul_ofReal_sub_one (s - t)

theorem circleAngle_lipschitz : LipschitzWith 1 circleAngle := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [circleAngle_dist]
  have h := Real.abs_sin_le_abs (x := (s - t) / 2)
  norm_num only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  norm_num only [NNReal.coe_one, one_mul, Real.dist_eq, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

private theorem circleAngle_periodic : Function.Periodic circleAngle (2 * Real.pi) := by
  intro t
  simpa only [circleAngle, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat, add_mul] using Complex.exp_periodic ((t : ℂ) * Complex.I)

/-- Any angular interval of width `2π` covers the entire unit circle. -/
theorem circleAngle_image_period (s : ℝ) :
    circleAngle '' Icc s (s + 2 * Real.pi) = Metric.sphere (0 : ℂ) 1 := by
  rw [circleAngle_periodic.image_Icc (by positivity)]
  exact Complex.range_exp_mul_I

/-- R06E18: the first curve is continuous. -/
theorem exercise18_gamma1_continuous : Continuous exercise18_gamma1 := circleAngle_continuous

/-- R06E18: the second curve is continuous. -/
theorem exercise18_gamma2_continuous : Continuous exercise18_gamma2 :=
  circleAngle_continuous.comp (continuous_const.mul continuous_id)

/-- The first curve has the full unit-circle range. -/
theorem exercise18_first_range :
    exercise18_gamma1 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 := by
  change circleAngle '' Icc 0 (2 * Real.pi) = _
  simpa only [zero_add] using circleAngle_image_period 0

/-- The second curve has the full unit-circle range, not just a subset. -/
theorem exercise18_second_range :
    exercise18_gamma2 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 := by
  apply subset_antisymm
  · rintro z ⟨t, ht, rfl⟩
    simp [exercise18_gamma2]
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := exercise18_first_range.symm ▸ hz
    refine ⟨t / 2, ⟨by linarith [ht.1], by linarith [ht.2, Real.pi_pos]⟩, ?_⟩
    unfold exercise18_gamma2 exercise18_gamma1
    congr 1
    ring

/-- The repaired formula agrees with the continuous phase formula everywhere.
This equality does not assert that the source reciprocal was defined at zero. -/
theorem exercise18_gamma3_eq_phase (t : ℝ) :
    exercise18_gamma3 t = circleAngle (2 * Real.pi * exercise18_phase t) := by
  by_cases ht : t = 0 <;> simp [exercise18_gamma3, ht, exercise18_phase, circleAngle]

private theorem phase_negative_point :
    exercise18_phase (2 / (3 * Real.pi)) = -(2 / (3 * Real.pi)) := by
  have hi : 1 / (2 / (3 * Real.pi)) = Real.pi / 2 + Real.pi := by field_simp; ring
  simp [exercise18_phase, hi, Real.sin_add_pi, Real.sin_pi_div_two]

/-- The phase has an image interval of width at least one.
It need not attain the value one itself. -/
theorem exercise18_phase_width :
    1 ≤ exercise18_phase (2 * Real.pi) - exercise18_phase (2 / (3 * Real.pi)) := by
  rw [phase_negative_point]
  have hs := Real.sin_ge_sub_cube (show 0 ≤ 1 / (2 * Real.pi) by positivity)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * Real.pi by positivity)
  have hid : 2 * Real.pi * (1 / (2 * Real.pi) - (1 / (2 * Real.pi)) ^ 3 / 6) =
      1 - 1 / (24 * Real.pi ^ 2) := by field_simp; ring
  rw [hid] at hm
  have he : 1 / (24 * Real.pi ^ 2) ≤ 2 / (3 * Real.pi) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.two_le_pi]
  unfold exercise18_phase
  linarith

/-- The third curve also covers the full circle. -/
theorem exercise18_third_range :
    exercise18_gamma3 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 := by
  apply subset_antisymm
  · rintro z ⟨t, ht, rfl⟩
    rw [mem_sphere_zero_iff_norm, exercise18_gamma3_eq_phase, circleAngle_norm]
  · intro z hz
    let l : ℝ := 2 / (3 * Real.pi)
    let q : ℝ → ℝ := fun t => 2 * Real.pi * exercise18_phase t
    have hl : 0 < l := by dsimp [l]; positivity
    have hlR : l ≤ 2 * Real.pi := by
      dsimp [l]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [Real.two_le_pi]
    have hw : q l + 2 * Real.pi ≤ q (2 * Real.pi) := by
      have h := mul_le_mul_of_nonneg_left exercise18_phase_width
        (show 0 ≤ 2 * Real.pi by positivity)
      dsimp [q, l]
      nlinarith
    obtain ⟨θ, hθ, hθz⟩ := (circleAngle_image_period (q l)).symm ▸ hz
    have hθ' : θ ∈ Icc (q l) (q (2 * Real.pi)) := ⟨hθ.1, hθ.2.trans hw⟩
    have hq : ContinuousOn q (Icc l (2 * Real.pi)) :=
      (continuous_const.mul exercise18_phase_continuous).continuousOn
    obtain ⟨t, ht, hqt⟩ := intermediate_value_Icc hlR hq hθ'
    refine ⟨t, ⟨hl.le.trans ht.1, ht.2⟩, ?_⟩
    rw [exercise18_gamma3_eq_phase]
    exact (congrArg circleAngle hqt).trans hθz

/-- R06E18.common_range, after establishing continuity of the endpoint repair. -/
theorem exercise18_common_range :
    Continuous exercise18_gamma3 ∧
    exercise18_gamma1 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 ∧
    exercise18_gamma2 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 ∧
    exercise18_gamma3 '' Icc 0 (2 * Real.pi) = Metric.sphere (0 : ℂ) 1 :=
  ⟨exercise18_endpoint_extension.2, exercise18_first_range,
    exercise18_second_range, exercise18_third_range⟩

/-- Angular speed times parameter length is an upper bound for source length. -/
private theorem linearCircle_length_le (ω L : ℝ) (hω : 0 ≤ ω) :
    curveLength (fun t => circleAngle (ω * t)) 0 L ≤ ENNReal.ofReal (ω * L) := by
  have hlip : LipschitzWith ⟨ω, hω⟩ (fun t => circleAngle (ω * t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    calc
      dist (circleAngle (ω * s)) (circleAngle (ω * t)) ≤ dist (ω * s) (ω * t) := by
        simpa using circleAngle_lipschitz.dist_le_mul (ω * s) (ω * t)
      _ = ω * dist s t := by simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hω]
  rw [curveLength_eq_eVariationOn]
  have h := hlip.lipschitzOnWith.comp_eVariationOn_le (g := id)
    (s := Icc 0 L) (mapsTo_univ _ _)
  simp only [Function.comp_id, eVariationOn_id_Icc, sub_zero] at h
  rw [ENNReal.ofReal_mul hω, ENNReal.ofReal_eq_coe_nnreal hω]
  exact h

/-- Uniform polygonal approximations give the matching lower bound. -/
theorem linearCircle_length (ω L : ℝ) (hω : 0 ≤ ω) (hL : 0 ≤ L) :
    curveLength (fun t => circleAngle (ω * t)) 0 L = ENNReal.ofReal (ω * L) := by
  have hupper := linearCircle_length_le ω L hω
  have hfin : curveLength (fun t => circleAngle (ω * t)) 0 L ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  apply le_antisymm hupper
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  let δ : ℕ → ℝ := fun n => ω * L / (2 * ((n : ℝ) + 1))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ω * L / 2)
    convert h using 1
    · funext n
      dsimp [δ]
      field_simp
    · simp
  have hlim : Tendsto (fun n => ω * L - ω * L * (δ n) ^ 2 / 6) atTop (𝓝 (ω * L)) := by
    simpa using tendsto_const_nhds.sub ((tendsto_const_nhds.mul (hδ.pow 2)).div_const 6)
  apply le_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  let N : ℝ := (n : ℝ) + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let u : ℕ → ℝ := fun i => (min i (n + 1) : ℕ) * L / N
  have hu : Monotone u := by
    intro i j hij
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (min_le_min_right (n + 1) hij)) hL) hN.le
  have hs : ∀ i, u i ∈ Icc 0 L := by
    intro i
    constructor
    · dsimp [u]; positivity
    · apply (div_le_iff₀ hN).mpr
      have hi : ((min i (n + 1) : ℕ) : ℝ) ≤ N := by
        dsimp [N]
        exact_mod_cast (min_le_right i (n + 1))
      exact (mul_le_mul_of_nonneg_right hi hL).trans_eq (mul_comm N L)
  have hsum : ∑ i ∈ Finset.range (n + 1),
      dist (circleAngle (ω * u (i + 1))) (circleAngle (ω * u i)) =
        N * |2 * Real.sin (δ n)| := by
    calc
      _ = ∑ _i ∈ Finset.range (n + 1), |2 * Real.sin (δ n)| := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [circleAngle_dist]
        congr 3
        dsimp [u, δ]
        rw [min_eq_left (by omega : i + 1 ≤ n + 1), min_eq_left (by omega : i ≤ n + 1)]
        push_cast
        dsimp [N]
        field_simp
        ring
      _ = _ := by simp [N, Nat.cast_add, Nat.cast_one]
  have hb : N * |2 * Real.sin (δ n)| ≤
      (curveLength (fun t => circleAngle (ω * t)) 0 L).toReal := by
    have he := eVariationOn.sum_le (f := fun t => circleAngle (ω * t)) (n := n + 1) hu hs
    rw [← curveLength_eq_eVariationOn] at he
    have he' : ENNReal.ofReal (∑ i ∈ Finset.range (n + 1),
        dist (circleAngle (ω * u (i + 1))) (circleAngle (ω * u i))) ≤
          curveLength (fun t => circleAngle (ω * t)) 0 L := by
      simpa [ENNReal.ofReal_sum_of_nonneg, dist_nonneg, edist_dist] using he
    rw [hsum] at he'
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp he'
  have hd : 0 ≤ δ n := by dsimp [δ]; positivity
  have hsin := Real.sin_ge_sub_cube hd
  have habs := le_abs_self (2 * Real.sin (δ n))
  have hid : N * (2 * (δ n - (δ n) ^ 3 / 6)) =
      ω * L - ω * L * (δ n) ^ 2 / 6 := by
    dsimp [δ]
    change N * (2 * (ω * L / (2 * N) - (ω * L / (2 * N)) ^ 3 / 6)) = _
    dsimp [N]
    field_simp
  rw [← hid]
  exact (mul_le_mul_of_nonneg_left (by linarith :
    2 * (δ n - (δ n) ^ 3 / 6) ≤ |2 * Real.sin (δ n)|) hN.le).trans hb

/-- R06E18.first_length, with rectifiability in the source convention. -/
theorem exercise18_first_length :
    curveLength exercise18_gamma1 0 (2 * Real.pi) = ENNReal.ofReal (2 * Real.pi) ∧
      CurveRectifiable exercise18_gamma1 0 (2 * Real.pi) := by
  have h := linearCircle_length 1 (2 * Real.pi) (by norm_num) (by positivity)
  simp only [one_mul] at h
  refine ⟨h, ?_⟩
  change curveLength circleAngle 0 (2 * Real.pi) ≠ ⊤
  rw [h]
  exact ENNReal.ofReal_ne_top

/-- R06E18.second_length. The two traversals have length `4π`. -/
theorem exercise18_second_length :
    curveLength exercise18_gamma2 0 (2 * Real.pi) = ENNReal.ofReal (4 * Real.pi) ∧
      CurveRectifiable exercise18_gamma2 0 (2 * Real.pi) := by
  have h := linearCircle_length 2 (2 * Real.pi) (by norm_num) (by positivity)
  have hm : (2 : ℝ) * (2 * Real.pi) = 4 * Real.pi := by ring
  rw [hm] at h
  refine ⟨h, ?_⟩
  change curveLength (fun t => circleAngle (2 * t)) 0 (2 * Real.pi) ≠ ⊤
  rw [h]
  exact ENNReal.ofReal_ne_top

/-- The source oscillation times; their reciprocals are consecutive sine extrema. -/
noncomputable def exercise18_turnTime (n : ℕ) : ℝ :=
  1 / (Real.pi / 2 + (n : ℝ) * Real.pi)

private theorem turnTime_pos (n : ℕ) : 0 < exercise18_turnTime n := by
  unfold exercise18_turnTime
  positivity

private theorem turnTime_antitone : Antitone exercise18_turnTime := by
  intro i j hij
  apply one_div_le_one_div_of_le (by positivity : 0 < Real.pi / 2 + (i : ℝ) * Real.pi)
  gcongr

private theorem turnTime_mem (n : ℕ) : exercise18_turnTime n ∈ Icc 0 (2 * Real.pi) := by
  refine ⟨(turnTime_pos n).le, ?_⟩
  unfold exercise18_turnTime
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Real.two_le_pi, mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le]

/-- Angular magnitudes at the tail extrema; the first two extrema are not needed. -/
noncomputable def sampleAngle (n : ℕ) : ℝ :=
  2 * Real.pi * exercise18_turnTime (n + 2)

private theorem sampleAngle_eq (n : ℕ) : sampleAngle n = 2 / ((n : ℝ) + 5 / 2) := by
  unfold sampleAngle exercise18_turnTime
  push_cast
  field_simp
  ring

private theorem sampleAngle_bounds (n : ℕ) : 0 ≤ sampleAngle n ∧ sampleAngle n ≤ Real.pi / 2 := by
  rw [sampleAngle_eq]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [Real.two_le_pi, mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le]

private theorem sin_sign (n : ℕ) (x : ℝ) :
    Real.sin ((-1 : ℝ) ^ n * x) = (-1 : ℝ) ^ n * Real.sin x := by
  rcases neg_one_pow_eq_or ℝ n with h | h <;> simp [h]

/-- The phase at the specified extrema alternates, with magnitude of order `1/n`. -/
theorem exercise18_sample_im (n : ℕ) :
    (exercise18_gamma3 (exercise18_turnTime (n + 2))).im =
      (-1 : ℝ) ^ n * Real.sin (sampleAngle n) := by
  have hs : Real.sin (1 / exercise18_turnTime (n + 2)) = (-1 : ℝ) ^ n := by
    simp only [exercise18_turnTime, one_div_one_div, Real.sin_add_nat_mul_pi,
      Real.sin_pi_div_two, mul_one, pow_add]
    norm_num
  have hp : 2 * Real.pi * exercise18_phase (exercise18_turnTime (n + 2)) =
      (-1 : ℝ) ^ n * sampleAngle n := by
    unfold exercise18_phase
    rw [hs]
    unfold sampleAngle
    ring
  rw [exercise18_gamma3_eq_phase, hp]
  have him : ∀ t : ℝ, (circleAngle t).im = Real.sin t := by
    intro t
    unfold circleAngle
    rw [Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [him, sin_sign]

/-- Consecutive chords dominate a positive harmonic sequence. -/
theorem exercise18_harmonic_chord (n : ℕ) :
    1 / ((n : ℝ) + 3) ≤ Real.pi *
      dist (exercise18_gamma3 (exercise18_turnTime ((n + 1) + 2)))
        (exercise18_gamma3 (exercise18_turnTime (n + 2))) := by
  have hsn : 0 ≤ Real.sin (sampleAngle n) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sampleAngle_bounds n).1
      ((sampleAngle_bounds n).2.trans (by linarith [Real.pi_pos]))
  have hss : 0 ≤ Real.sin (sampleAngle (n + 1)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (sampleAngle_bounds (n + 1)).1
      ((sampleAngle_bounds (n + 1)).2.trans (by linarith [Real.pi_pos]))
  have him : |(exercise18_gamma3 (exercise18_turnTime ((n + 1) + 2)) -
      exercise18_gamma3 (exercise18_turnTime (n + 2))).im| =
        Real.sin (sampleAngle (n + 1)) + Real.sin (sampleAngle n) := by
    rw [Complex.sub_im, exercise18_sample_im, exercise18_sample_im, pow_succ]
    have heq : (-1 : ℝ) ^ n * -1 * Real.sin (sampleAngle (n + 1)) -
        (-1 : ℝ) ^ n * Real.sin (sampleAngle n) =
          -((-1 : ℝ) ^ n) * (Real.sin (sampleAngle (n + 1)) + Real.sin (sampleAngle n)) := by ring
    rw [heq, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (add_nonneg hss hsn)]
  have hd : Real.sin (sampleAngle n) ≤
      dist (exercise18_gamma3 (exercise18_turnTime ((n + 1) + 2)))
        (exercise18_gamma3 (exercise18_turnTime (n + 2))) := by
    have h := Complex.abs_im_le_norm
      (exercise18_gamma3 (exercise18_turnTime ((n + 1) + 2)) -
        exercise18_gamma3 (exercise18_turnTime (n + 2)))
    rw [him, ← dist_eq_norm] at h
    linarith
  have hsin := Real.mul_le_sin (sampleAngle_bounds n).1 (sampleAngle_bounds n).2
  have hmul := mul_le_mul_of_nonneg_left hsin Real.pi_pos.le
  have hc : Real.pi * (2 / Real.pi * sampleAngle n) = 2 * sampleAngle n := by
    field_simp
  rw [hc] at hmul
  have hh : 1 / ((n : ℝ) + 3) ≤ 2 * sampleAngle n := by
    rw [sampleAngle_eq]
    have he : 2 * (2 / ((n : ℝ) + 5 / 2)) = 4 / ((n : ℝ) + 5 / 2) := by ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hh.trans (hmul.trans (mul_le_mul_of_nonneg_left hd Real.pi_pos.le))

/-- R06E18.third_nonrectifiable: finite source length would make the harmonic
chord lower bound summable. The antitone parameter times are reversed by the
proved variation composition lemma, not used as unordered partitions. -/
theorem exercise18_third_nonrectifiable :
    curveLength exercise18_gamma3 0 (2 * Real.pi) = ⊤ ∧
      ¬ CurveRectifiable exercise18_gamma3 0 (2 * Real.pi) := by
  have hinf : curveLength exercise18_gamma3 0 (2 * Real.pi) = ⊤ := by
    by_contra hfin
    let τ : ℕ → ℝ := fun n => exercise18_turnTime (n + 2)
    let chord : ℕ → ℝ := fun n =>
      dist (exercise18_gamma3 (τ (n + 1))) (exercise18_gamma3 (τ n))
    have hτ : Antitone τ := fun i j hij => turnTime_antitone (Nat.add_le_add_right hij 2)
    have hv : eVariationOn (exercise18_gamma3 ∘ τ) univ ≤
        curveLength exercise18_gamma3 0 (2 * Real.pi) := by
      rw [curveLength_eq_eVariationOn]
      exact eVariationOn.comp_le_of_antitoneOn exercise18_gamma3 τ (hτ.antitoneOn univ)
        (fun n _ => turnTime_mem (n + 2))
    have hb : ∀ n, ∑ i ∈ Finset.range n, chord i ≤
        (curveLength exercise18_gamma3 0 (2 * Real.pi)).toReal := by
      intro n
      have he := (eVariationOn.sum_le (f := exercise18_gamma3 ∘ τ)
        (n := n) monotone_id (fun _ => mem_univ _)).trans hv
      apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
      simpa [chord, ENNReal.ofReal_sum_of_nonneg, dist_nonneg, edist_dist] using he
    have hsum : Summable chord := summable_of_sum_range_le (fun _ => dist_nonneg) hb
    have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 3)) :=
      (hsum.mul_left Real.pi).of_nonneg_of_le (fun n => by positivity)
        (fun n => exercise18_harmonic_chord n)
    have hh' : Summable (fun n : ℕ => 1 / ((n + 3 : ℕ) : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hh
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 3).mp hh')
  exact ⟨hinf, by simp only [CurveRectifiable, hinf, ne_eq, not_true_eq_false, not_false_eq_true]⟩

/-- The infinite-variation formulation uses the proved source-length comparison. -/
theorem exercise18_third_infinite_variation :
    eVariationOn exercise18_gamma3 (Icc 0 (2 * Real.pi)) = ⊤ := by
  rw [← curveLength_eq_eVariationOn]
  exact exercise18_third_nonrectifiable.1

end Rudin.Chapter06
