module

public import Math.Rudin.Chapter08.Exercise15
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Chapter 8, Exercise 21

Source: Rudin, Third Edition, book page 201 (PDF page 210).
The actual finite Dirichlet kernel has normalized L1 norm within a fixed
constant of `(4 / π²) * log n`. The proof compares each sine lobe with
harmonic sums. All integrands used for comparison are continuous.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Rudin.Chapter08

lemma e21_dirichlet_sine (n : ℕ) (x : ℝ) :
    Real.sin (x / 2) * dirichletKernel n x = Real.sin (((n : ℝ) + 1 / 2) * x) := by
  induction n with
  | zero => simp [dirichletKernel, div_eq_mul_inv, mul_comm]
  | succ n ih =>
    rw [dirichletKernel_succ, mul_add, ih]
    have h := Real.sin_add (((n : ℝ) + 1) * x) (x / 2)
    have h' := Real.sin_sub (((n : ℝ) + 1) * x) (x / 2)
    have he : ((n : ℝ) + 1) * x - x / 2 = ((n : ℝ) + 1 / 2) * x := by ring
    rw [he] at h'
    push_cast
    convert (show Real.sin (((n : ℝ) + 1 / 2) * x) +
      Real.sin (x / 2) * (2 * Real.cos (((n : ℝ) + 1) * x)) =
      Real.sin (((n : ℝ) + 1) * x + x / 2) by linarith) using 1
    congr 1
    ring

lemma e21_reciprocal_error {x : ℝ} (hx : 0 < x) (hπ : x ≤ Real.pi / 2) :
    0 ≤ 1 / Real.sin x - 1 / x ∧ 1 / Real.sin x - 1 / x ≤ 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hlow : x / 2 ≤ Real.sin x := by
    have h := Real.mul_le_sin hx.le hπ
    have hp := Real.pi_pos
    have hp4 := Real.pi_lt_four
    have : x / 2 ≤ 2 / Real.pi * x := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp).mpr
      nlinarith
    exact this.trans h
  have hmul : x - Real.sin x ≤ x * Real.sin x := by
    have hc := Real.sin_ge_sub_cube hx.le
    have hx2 : x ≤ 2 := by linarith [Real.pi_lt_four]
    have hcube : x ^ 3 ≤ 2 * x ^ 2 := by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)]
    nlinarith [mul_le_mul_of_nonneg_left hlow hx.le, sq_nonneg x]
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hs (Real.sin_le hx.le))
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hx).mp
    field_simp
    nlinarith

lemma e21_abs_sin_cell (k : ℕ) :
    (∫ x in (k : ℝ) * Real.pi..((k : ℝ) + 1) * Real.pi, |Real.sin x|) = 2 := by
  have he := intervalIntegral.integral_comp_add_left (fun x : ℝ => |Real.sin x|)
    ((k : ℝ) * Real.pi) (a := 0) (b := Real.pi)
  have hp : Function.Periodic (fun x : ℝ => |Real.sin x|) Real.pi := by
    intro x
    simp [Real.sin_add_pi]
  have heq : (fun x : ℝ => |Real.sin (x + (k : ℝ) * Real.pi)|) = (fun x => |Real.sin x|) := by
    ext x
    exact hp.nat_mul k x
  simp_rw [add_comm ((k : ℝ) * Real.pi), heq] at he
  have hbase : (∫ x in (0 : ℝ)..Real.pi, |Real.sin x|) = 2 := by
    rw [intervalIntegral.integral_congr (fun x hx =>
      abs_of_nonneg (Real.sin_nonneg_of_mem_Icc (by simpa [uIcc_of_le Real.pi_pos.le] using hx))), integral_sin]
    norm_num
  convert he.symm.trans hbase using 1
  congr 1 <;> ring

lemma e21_sinc_cell_lower (k : ℕ) :
    2 / (((k : ℝ) + 1) * Real.pi) ≤
      ∫ x in (k : ℝ) * Real.pi..((k : ℝ) + 1) * Real.pi, |Real.sinc x| := by
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (show (k : ℝ) * Real.pi ≤ ((k : ℝ) + 1) * Real.pi by nlinarith [Real.pi_pos])
    ((Real.continuous_sin.abs.div_const (((k : ℝ) + 1) * Real.pi)).intervalIntegrable _ _)
    (Real.continuous_sinc.abs.intervalIntegrable _ _) ?_
  · simpa only [intervalIntegral.integral_div, e21_abs_sin_cell] using h
  · intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt (by positivity) hx.1
    rw [Real.sinc_of_ne_zero hx0.ne', abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hx0 hx.2.le

lemma e21_sinc_cell_upper {k : ℕ} (hk : 0 < k) :
    (∫ x in (k : ℝ) * Real.pi..((k : ℝ) + 1) * Real.pi, |Real.sinc x|) ≤
      2 / ((k : ℝ) * Real.pi) := by
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume)
    (show (k : ℝ) * Real.pi ≤ ((k : ℝ) + 1) * Real.pi by nlinarith [Real.pi_pos])
    (Real.continuous_sinc.abs.intervalIntegrable _ _)
    ((Real.continuous_sin.abs.div_const ((k : ℝ) * Real.pi)).intervalIntegrable _ _) ?_
  · simpa only [intervalIntegral.integral_div, e21_abs_sin_cell] using h
  · intro x hx
    have hk0 : 0 < (k : ℝ) * Real.pi := mul_pos (by exact_mod_cast hk) Real.pi_pos
    rw [Real.sinc_of_ne_zero (hk0.trans hx.1).ne', abs_div, abs_of_pos (hk0.trans hx.1)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hk0 hx.1.le

lemma e21_sinc_initial : (∫ x in (0 : ℝ)..Real.pi, |Real.sinc x|) ≤ Real.pi := by
  have h := intervalIntegral.integral_mono (μ := volume) Real.pi_pos.le
    (Real.continuous_sinc.abs.intervalIntegrable _ _) intervalIntegrable_const
    Real.abs_sinc_le_one
  simpa using h

lemma e21_sinc_full_lower (n : ℕ) :
    (2 / Real.pi) * (harmonic n : ℝ) ≤
      ∫ x in (0 : ℝ)..(n : ℝ) * Real.pi, |Real.sinc x| := by
  have hs := Finset.sum_le_sum (s := Finset.range n) (fun k _ => e21_sinc_cell_lower k)
  have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (n := n)
    (fun k _ => Real.continuous_sinc.abs.intervalIntegrable ((k : ℝ) * Real.pi)
      (((k + 1 : ℕ) : ℝ) * Real.pi))
  push_cast at he
  rw [he] at hs
  convert hs using 1
  · simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp

lemma e21_sinc_full_upper (n : ℕ) :
    (∫ x in (0 : ℝ)..((n : ℝ) + 1) * Real.pi, |Real.sinc x|) ≤
      Real.pi + (2 / Real.pi) * (harmonic n : ℝ) := by
  induction n with
  | zero => simpa using e21_sinc_initial
  | succ n ih =>
    have hsum := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (Real.continuous_sinc.abs.intervalIntegrable 0 (((n : ℝ) + 1) * Real.pi))
      (Real.continuous_sinc.abs.intervalIntegrable (((n : ℝ) + 1) * Real.pi)
        (((n : ℝ) + 1 + 1) * Real.pi))
    have hu := e21_sinc_cell_upper (Nat.succ_pos n)
    push_cast at hu ⊢
    rw [← hsum]
    have h := add_le_add ih hu
    convert h using 1
    rw [harmonic_succ]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The normalized L1 norm of the finite Dirichlet kernel. -/
def dirichletLebesgueConstant (n : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in -Real.pi..Real.pi, |dirichletKernel n t|

lemma e21_kernel_continuous (n : ℕ) : Continuous (dirichletKernel n) := by
  unfold dirichletKernel
  fun_prop

lemma e21_kernel_half_integral (n : ℕ) :
    dirichletLebesgueConstant n =
      (2 / Real.pi) * ∫ u in (0 : ℝ)..Real.pi / 2, |dirichletKernel n (2 * u)| := by
  have he := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := Real.pi)
    (fun t => |dirichletKernel n t|)
  have even (t : ℝ) : dirichletKernel n (-t) = dirichletKernel n t := by
    simp [dirichletKernel, mul_neg, Real.cos_neg]
  simp only [even, neg_zero] at he
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((e21_kernel_continuous n).abs.intervalIntegrable (-Real.pi) 0)
    ((e21_kernel_continuous n).abs.intervalIntegrable 0 Real.pi)
  have hc := intervalIntegral.integral_comp_mul_left
    (fun t => |dirichletKernel n t|) (show (2 : ℝ) ≠ 0 by norm_num)
    (a := 0) (b := Real.pi / 2)
  simp only [mul_zero, mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num), smul_eq_mul] at hc
  unfold dirichletLebesgueConstant
  rw [← ha, ← he]
  rw [hc]
  ring

lemma e21_kernel_density_bound (n : ℕ) {u : ℝ} (hu : 0 < u) (huπ : u ≤ Real.pi / 2) :
    (2 * (n : ℝ) + 1) * |Real.sinc ((2 * (n : ℝ) + 1) * u)| ≤
      |dirichletKernel n (2 * u)| ∧
    |dirichletKernel n (2 * u)| ≤
      (2 * (n : ℝ) + 1) * |Real.sinc ((2 * (n : ℝ) + 1) * u)| + 1 := by
  have hs : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [Real.pi_pos])
  have ha : 0 < 2 * (n : ℝ) + 1 := by positivity
  have he := e21_dirichlet_sine n (2 * u)
  rw [show 2 * u / 2 = u by ring,
    show ((n : ℝ) + 1 / 2) * (2 * u) = (2 * (n : ℝ) + 1) * u by ring] at he
  have hd : |dirichletKernel n (2 * u)| =
      |Real.sin ((2 * (n : ℝ) + 1) * u)| / Real.sin u := by
    apply (eq_div_iff hs.ne').mpr
    rw [mul_comm, ← abs_of_pos hs, ← abs_mul, he]
  have hc : (2 * (n : ℝ) + 1) * |Real.sinc ((2 * (n : ℝ) + 1) * u)| =
      |Real.sin ((2 * (n : ℝ) + 1) * u)| / u := by
    rw [Real.sinc_of_ne_zero (mul_pos ha hu).ne', abs_div, abs_of_pos (mul_pos ha hu)]
    field_simp
  rw [hd, hc]
  have hb := e21_reciprocal_error hu huπ
  have hp := abs_nonneg (Real.sin ((2 * (n : ℝ) + 1) * u))
  have hp1 := Real.abs_sin_le_one ((2 * (n : ℝ) + 1) * u)
  constructor
  · exact div_le_div_of_nonneg_left hp hs (Real.sin_le hu.le)
  · have h := mul_le_mul_of_nonneg_left hb.2 hp
    simp only [mul_sub, mul_one_div, mul_one] at h
    linarith

lemma e21_density_integral (n : ℕ) :
    (∫ u in (0 : ℝ)..Real.pi / 2,
      (2 * (n : ℝ) + 1) * |Real.sinc ((2 * (n : ℝ) + 1) * u)|) =
      ∫ v in (0 : ℝ)..((n : ℝ) + 1 / 2) * Real.pi, |Real.sinc v| := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
    (fun v => |Real.sinc v|) (by positivity)]
  simp only [smul_eq_mul, mul_zero]
  rw [← mul_assoc, mul_inv_cancel₀ (show 2 * (n : ℝ) + 1 ≠ 0 by positivity), one_mul]
  congr 1
  ring

lemma e21_kernel_integral_bounds (n : ℕ) :
    (∫ v in (0 : ℝ)..((n : ℝ) + 1 / 2) * Real.pi, |Real.sinc v|) ≤
      (∫ u in (0 : ℝ)..Real.pi / 2, |dirichletKernel n (2 * u)|) ∧
    (∫ u in (0 : ℝ)..Real.pi / 2, |dirichletKernel n (2 * u)|) ≤
      (∫ v in (0 : ℝ)..((n : ℝ) + 1 / 2) * Real.pi, |Real.sinc v|) + Real.pi / 2 := by
  have hdi : Continuous (fun u : ℝ =>
      (2 * (n : ℝ) + 1) * |Real.sinc ((2 * (n : ℝ) + 1) * u)|) := by fun_prop
  have hki : Continuous (fun u : ℝ => |dirichletKernel n (2 * u)|) :=
    (e21_kernel_continuous n).abs.comp (by fun_prop)
  constructor
  · rw [← e21_density_integral]
    exact intervalIntegral.integral_mono_on_of_le_Ioo (by positivity)
      (hdi.intervalIntegrable _ _) (hki.intervalIntegrable _ _)
      (fun u hu => (e21_kernel_density_bound n hu.1 hu.2.le).1)
  · have h := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (by positivity)
      (hki.intervalIntegrable 0 (Real.pi / 2)) ((hdi.add continuous_const).intervalIntegrable _ _)
      (fun u hu => (e21_kernel_density_bound n hu.1 hu.2.le).2)
    simp only [Pi.add_apply] at h
    rw [intervalIntegral.integral_add (hdi.intervalIntegrable _ _) intervalIntegrable_const,
      e21_density_integral] at h
    simpa using h

lemma e21_harmonic_bounds (n : ℕ) :
    (4 / Real.pi ^ 2) * (harmonic n : ℝ) ≤ dirichletLebesgueConstant n ∧
    dirichletLebesgueConstant n ≤ 3 + (4 / Real.pi ^ 2) * (harmonic n : ℝ) := by
  have hlow := intervalIntegral.integral_mono_interval (μ := volume)
    (a := (0 : ℝ)) (b := (n : ℝ) * Real.pi)
    (c := (0 : ℝ)) (d := ((n : ℝ) + 1 / 2) * Real.pi)
    le_rfl (by positivity) (by nlinarith [Real.pi_pos])
    (ae_of_all _ (fun x => abs_nonneg (Real.sinc x)))
    (Real.continuous_sinc.abs.intervalIntegrable _ _)
  have hupp := intervalIntegral.integral_mono_interval (μ := volume)
    (a := (0 : ℝ)) (b := ((n : ℝ) + 1 / 2) * Real.pi)
    (c := (0 : ℝ)) (d := ((n : ℝ) + 1) * Real.pi)
    le_rfl (by positivity) (by nlinarith [Real.pi_pos])
    (ae_of_all _ (fun x => abs_nonneg (Real.sinc x)))
    (Real.continuous_sinc.abs.intervalIntegrable _ _)
  have hlo := (e21_sinc_full_lower n).trans (hlow.trans (e21_kernel_integral_bounds n).1)
  have hup := (e21_kernel_integral_bounds n).2.trans
    (add_le_add (hupp.trans (e21_sinc_full_upper n)) le_rfl)
  rw [e21_kernel_half_integral]
  constructor
  · convert mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 / Real.pi by positivity) using 1
    ring
  · convert mul_le_mul_of_nonneg_left hup (show 0 ≤ 2 / Real.pi by positivity) using 1
    field_simp
    ring

/-- A strict logarithmic bound for every positive index, including `n = 1`. -/
theorem exercise21_log_lower_bound : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → C * Real.log n < dirichletLebesgueConstant n := by
  refine ⟨4 / Real.pi ^ 2, by positivity, ?_⟩
  intro n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : Real.log (n : ℝ) < Real.log ((n : ℝ) + 1) :=
    Real.strictMonoOn_log hn0 (show 0 < (n : ℝ) + 1 by positivity) (by linarith)
  have hh := log_add_one_le_harmonic n
  push_cast at hh
  exact (mul_lt_mul_of_pos_left (hlog.trans_le hh) (by positivity)).trans_le
    (e21_harmonic_bounds n).1

/-- Explicit two-sided bounded error with the source coefficient `4 / π²`. -/
theorem exercise21_error_bounds (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ dirichletLebesgueConstant n - (4 / Real.pi ^ 2) * Real.log n ∧
    dirichletLebesgueConstant n - (4 / Real.pi ^ 2) * Real.log n ≤ 3 + 4 / Real.pi ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hh : Real.log (n : ℝ) ≤ (harmonic n : ℝ) :=
    (Real.strictMonoOn_log hn0 (show 0 < (n : ℝ) + 1 by positivity)
      (by linarith : (n : ℝ) < (n : ℝ) + 1)).le.trans
      (by exact_mod_cast log_add_one_le_harmonic n)
  have hl := (mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 / Real.pi ^ 2 by positivity)).trans
    (e21_harmonic_bounds n).1
  have hu := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n)
    (show 0 ≤ 4 / Real.pi ^ 2 by positivity)
  constructor
  · linarith
  · nlinarith [(e21_harmonic_bounds n).2]

/-- The source sequence is bounded above and below, in absolute-value form. -/
theorem exercise21_bounded_error : ∃ B : ℝ, ∀ n : ℕ, 1 ≤ n →
    |dirichletLebesgueConstant n - (4 / Real.pi ^ 2) * Real.log n| ≤ B := by
  refine ⟨3 + 4 / Real.pi ^ 2, fun n hn => ?_⟩
  rw [abs_of_nonneg (exercise21_error_bounds n hn).1]
  exact (exercise21_error_bounds n hn).2

end Rudin.Chapter08
