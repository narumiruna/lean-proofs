module

public import Math.Rudin.Support.RiemannIntegrability
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Chapter 8, Exercise 20

Source: book page 200, PDF page 209. The lower graph consists of logarithmic
chords; the upper graph consists of tangent segments on half-open unit cells.
Both are constructed with natural floors. Their literal Darboux integrals are
proved before using the Riemann–Lebesgue bridge. The graph areas, not Stirling's
formula, give the strict factorial estimates.
-/

@[expose] public section

open Real Set MeasureTheory Finset
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesIntegralLaws
  Rudin.Support.RiemannIntegrability

namespace Rudin.Chapter08

noncomputable def factorialLowerGraph (x : ℝ) : ℝ :=
  (⌊x⌋₊ + 1 - x) * log ⌊x⌋₊ + (x - ⌊x⌋₊) * log (⌊x⌋₊ + 1)

noncomputable def factorialUpperGraph (x : ℝ) : ℝ :=
  x / ⌊x + 1 / 2⌋₊ - 1 + log ⌊x + 1 / 2⌋₊

theorem exercise20_lower_graph (m : ℕ) {x : ℝ} (hx : (m : ℝ) ≤ x ∧ x ≤ m + 1) :
    factorialLowerGraph x = (m + 1 - x) * log m + (x - m) * log (m + 1) := by
  rcases lt_or_eq_of_le hx.2 with h | rfl
  · simp [factorialLowerGraph, Nat.floor_eq_on_Ico m x ⟨hx.1, h⟩]
  · have hf : ⌊(m : ℝ) + 1⌋₊ = m + 1 := by exact_mod_cast Nat.floor_natCast (m + 1)
    simp only [factorialLowerGraph, hf, Nat.cast_add, Nat.cast_one]
    ring

theorem exercise20_upper_graph (m : ℕ) {x : ℝ}
    (hx : (m : ℝ) - 1 / 2 ≤ x ∧ x < m + 1 / 2) :
    factorialUpperGraph x = x / m - 1 + log m := by
  have hf : ⌊x + 1 / 2⌋₊ = m := Nat.floor_eq_on_Ico m _ ⟨by linarith, by linarith⟩
  simp only [factorialUpperGraph, hf]

private theorem lower_segment_le_log {m x : ℝ} (hm : 0 < m)
    (hx : m ≤ x ∧ x ≤ m + 1) :
    (m + 1 - x) * log m + (x - m) * log (m + 1) ≤ log x := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hm (by linarith : 0 < m + 1)
    (by linarith : 0 ≤ m + 1 - x) (by linarith : 0 ≤ x - m)
    (show m + 1 - x + (x - m) = 1 by ring)
  convert h using 1
  simp only [smul_eq_mul]
  congr 1
  ring

private theorem lower_segment_lt_log {m x : ℝ} (hm : 0 < m)
    (hx : m < x ∧ x < m + 1) :
    (m + 1 - x) * log m + (x - m) * log (m + 1) < log x := by
  have h := strictConcaveOn_log_Ioi.2 hm (by linarith : 0 < m + 1)
    (by linarith : m ≠ m + 1)
    (by linarith : 0 < m + 1 - x) (by linarith : 0 < x - m)
    (show m + 1 - x + (x - m) = 1 by ring)
  convert h using 1
  simp only [smul_eq_mul]
  congr 1
  ring

theorem exercise20_log_bounds {x : ℝ} (hx : 1 ≤ x) :
    factorialLowerGraph x ≤ log x ∧ log x ≤ factorialUpperGraph x := by
  have hm : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hmp : 0 < (⌊x⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  constructor
  · exact lower_segment_le_log hmp ⟨Nat.floor_le (by linarith), (Nat.lt_floor_add_one x).le⟩
  · have hn : 1 ≤ ⌊x + 1 / 2⌋₊ := Nat.le_floor (by linarith)
    have hnp : 0 < (⌊x + 1 / 2⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x + 1 / 2⌋₊)
    have h := log_le_sub_one_of_pos (div_pos (by linarith : 0 < x) hnp)
    rw [log_div (by linarith : x ≠ 0) hnp.ne'] at h
    unfold factorialUpperGraph
    linarith

private theorem continuous_ri {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
  have hid : (StieltjesFunction.id : ℝ → ℝ) = id := by ext x; rfl
  simpa only [hid, ← Real.volume_eq_stieltjes_id] using
    Rudin.Support.StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab hf

private theorem lower_segment_integral (m : ℝ) :
    (∫ x in m..m + 1, (m + 1 - x) * log m + (x - m) * log (m + 1)) =
      (log m + log (m + 1)) / 2 := by
  rw [intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ ↦ (m + 1 - x) * log m)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ ↦ (x - m) * log (m + 1))).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_mul_const]
  have hid : IntervalIntegrable (fun x : ℝ ↦ x) volume m (m + 1) :=
    continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hid,
    intervalIntegral.integral_sub hid intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

private theorem log_factorial_succ (n : ℕ) :
    log ((n + 1).factorial : ℝ) = log (n.factorial : ℝ) + log (n + 1) := by
  rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity)]
  push_cast
  ring

theorem exercise20_lower_integral (n : ℕ) :
    HasDarbouxRSIntegral factorialLowerGraph id 1 (n + 1)
      (log ((n + 1).factorial : ℝ) - log (n + 1) / 2) := by
  induction n with
  | zero =>
    have h := continuous_ri (a := 1) (b := 1) le_rfl (f := fun _ ↦ (0 : ℝ)) (by fun_prop)
    have he := hasDarbouxRSIntegral_congr (by norm_num : (1 : ℝ) ≤ 1) h
      (g := factorialLowerGraph) (by
        intro x hx
        have : x = 1 := by simpa using hx
        subst x
        simp [factorialLowerGraph])
    simpa using he
  | succ n ih =>
    have hc : HasDarbouxRSIntegral factorialLowerGraph id ((n : ℝ) + 1) (n + 1 + 1)
        ((log (n + 1) + log (n + 1 + 1)) / 2) := by
      have h := continuous_ri (a := (n : ℝ) + 1) (b := n + 1 + 1) (by linarith)
        (f := fun x ↦ (n + 1 + 1 - x) * log (n + 1) + (x - (n + 1)) * log (n + 1 + 1))
        (by fun_prop)
      rw [lower_segment_integral] at h
      apply hasDarbouxRSIntegral_congr (by linarith) h
      intro x hx
      symm
      simpa only [Nat.cast_add, Nat.cast_one] using
        exercise20_lower_graph (n + 1) (by simpa only [Nat.cast_add, Nat.cast_one, Set.mem_Icc] using hx)
    have h := hasDarbouxRSIntegral_join (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n + 1)
      (by linarith : (n : ℝ) + 1 ≤ n + 1 + 1) ih hc
    convert h using 1
    · push_cast; ring
    · rw [log_factorial_succ (n + 1)]
      push_cast
      ring

private theorem ri_of_eqOn_open {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hg : Continuous g) (he : Set.EqOn f g (Ioo a b)) :
    HasDarbouxRSIntegral f id a b (∫ x in a..b, g x) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  have hi : HasDarbouxRSIntegral f id a b (∫ x in a..b, f x) := by
    apply hasDarbouxRSIntegral_of_ae_continuousWithinAt hab
      (M := max M (max |f a| |f b|))
    · intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · subst x
        exact (le_max_left _ _).trans (le_max_right _ _)
      rcases lt_or_eq_of_le hx.2 with h' | h'
      · rw [he ⟨h, h'⟩]
        exact (hM x hx).trans (le_max_left _ _)
      · subst x
        exact (le_max_right _ _).trans (le_max_right _ _)
    · rw [ae_restrict_iff' measurableSet_Icc]
      filter_upwards [volume.ae_ne a, volume.ae_ne b] with x hxa hxb hx
      have hx' : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
      have he' : f =ᶠ[nhds x] g := by
        filter_upwards [isOpen_Ioo.mem_nhds hx'] with y hy
        exact he hy
      exact (hg.continuousAt.congr he'.symm).continuousWithinAt
  convert hi using 1
  symm
  apply intervalIntegral.integral_congr_uIoo
  simpa only [uIoo_of_le hab] using he

private theorem upper_segment_integral (a b m : ℝ) :
    (∫ x in a..b, x / m - 1 + log m) =
      (b ^ 2 - a ^ 2) / (2 * m) - (b - a) + (b - a) * log m := by
  have hid : IntervalIntegrable (fun x : ℝ ↦ x / m) volume a b :=
    (continuous_id.div_const m).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hid.sub intervalIntegrable_const) intervalIntegrable_const,
    intervalIntegral.integral_sub hid intervalIntegrable_const]
  simp only [intervalIntegral.integral_div, integral_id,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem upper_half_integrals (n : ℕ) :
    HasDarbouxRSIntegral factorialUpperGraph id ((n : ℝ) + 1) (n + 1 + 1)
      ((log (n + 1) + log (n + 1 + 1)) / 2 + 1 / (8 * (n + 1)) - 1 / (8 * (n + 1 + 1))) := by
  have h₁ := ri_of_eqOn_open (a := (n : ℝ) + 1) (b := n + 1 + 1 / 2) (by linarith)
    (f := factorialUpperGraph) (g := fun x ↦ x / (n + 1) - 1 + log (n + 1))
    (by fun_prop) (by
      intro x hx
      simpa only [Nat.cast_add, Nat.cast_one] using exercise20_upper_graph (n + 1)
        (x := x) ⟨by push_cast; linarith [hx.1], by push_cast; exact hx.2⟩)
  have h₂ := ri_of_eqOn_open (a := (n : ℝ) + 1 + 1 / 2) (b := n + 1 + 1) (by linarith)
    (f := factorialUpperGraph) (g := fun x ↦ x / (n + 1 + 1) - 1 + log (n + 1 + 1))
    (by fun_prop) (by
      intro x hx
      simpa only [Nat.cast_add, Nat.cast_one] using exercise20_upper_graph (n + 1 + 1)
        (x := x) ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩)
  rw [upper_segment_integral] at h₁ h₂
  convert hasDarbouxRSIntegral_join (by linarith) (by linarith) h₁ h₂ using 1
  field_simp
  ring

theorem exercise20_upper_integral (n : ℕ) :
    HasDarbouxRSIntegral factorialUpperGraph id 1 (n + 1)
      (log ((n + 1).factorial : ℝ) - log (n + 1) / 2 + 1 / 8 - 1 / (8 * (n + 1))) := by
  induction n with
  | zero =>
    simpa using ri_of_eqOn_open (a := 1) (b := 1) le_rfl
      (f := factorialUpperGraph) (g := fun _ ↦ (0 : ℝ)) (by fun_prop) (by simp)
  | succ n ih =>
    have h := hasDarbouxRSIntegral_join
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n + 1)
      (by linarith : (n : ℝ) + 1 ≤ n + 1 + 1) ih (upper_half_integrals n)
    convert h using 1
    · push_cast; ring
    · rw [log_factorial_succ (n + 1)]
      push_cast
      ring

theorem exercise20_integral_comparison {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in 1..(n : ℝ), factorialLowerGraph x) >
      -1 / 8 + ∫ x in 1..(n : ℝ), factorialUpperGraph x := by
  have hn1 : 1 ≤ n := by omega
  have hnc : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn1]; push_cast; ring
  have hf := exercise20_lower_integral (n - 1)
  have hg := exercise20_upper_integral (n - 1)
  simp only [Nat.sub_add_cancel hn1, he] at hf hg
  rw [(intervalIntegrable_and_integral_eq hnc hf).2,
    (intervalIntegrable_and_integral_eq hnc hg).2]
  have : 0 < 1 / (8 * (n : ℝ)) := by positivity
  linarith

theorem exercise20_log_integral {n : ℕ} (hn : 1 ≤ n) :
    HasDarbouxRSIntegral log id 1 (n : ℝ) ((n : ℝ) * log n - n + 1) := by
  have hnc : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := continuous_ri hnc (f := log)
    (continuousOn_log.mono (by intro t ht; exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)))
  simpa [integral_log] using h

theorem exercise20_log_factorial {n : ℕ} (hn : 2 ≤ n) :
    (7 : ℝ) / 8 < log (n.factorial : ℝ) - (n + 1 / 2) * log n + n ∧
      log (n.factorial : ℝ) - (n + 1 / 2) * log n + n < 1 := by
  have hn1 : 1 ≤ n := by omega
  have hnc : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [Nat.cast_sub hn1]; push_cast; ring
  have hf := exercise20_lower_integral (n - 1)
  have hg := exercise20_upper_integral (n - 1)
  simp only [Nat.sub_add_cancel hn1, he] at hf hg
  obtain ⟨hfi, hfv⟩ := intervalIntegrable_and_integral_eq hnc hf
  obtain ⟨hgi, hgv⟩ := intervalIntegrable_and_integral_eq hnc hg
  have hlc : ContinuousOn log (Icc (1 : ℝ) n) :=
    continuousOn_log.mono (by intro t ht; exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))
  have hli : IntervalIntegrable log volume 1 (n : ℝ) := hlc.intervalIntegrable_of_Icc hnc
  have hle := intervalIntegral.integral_mono_on hnc hli hgi
    (fun x hx ↦ (exercise20_log_bounds hx.1).2)
  have hlt : (∫ x in 1..(n : ℝ), factorialLowerGraph x) < ∫ x in 1..(n : ℝ), log x := by
    apply intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero hnc hfi hli
    · exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ (exercise20_log_bounds hx.1.le).1
    · have hs : Ioo (1 : ℝ) 2 ⊆ Ioc 1 (n : ℝ) := by
        intro x hx
        exact ⟨hx.1, hx.2.le.trans hn2⟩
      have hp : 0 < (volume.restrict (Ioc (1 : ℝ) n)) (Ioo 1 2) := by
        rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr hs]
        norm_num
      apply ne_of_gt (hp.trans_le (measure_mono ?_))
      intro x hx
      change factorialLowerGraph x < log x
      rw [exercise20_lower_graph 1 ⟨by simpa using hx.1.le, by norm_num; exact hx.2.le⟩]
      exact lower_segment_lt_log (by norm_num)
        (by constructor <;> norm_num <;> linarith [hx.1, hx.2])
  rw [integral_log] at hle hlt
  simp only [log_one, mul_zero, sub_zero] at hle hlt
  rw [hfv] at hlt
  rw [hgv] at hle
  have hp : 0 < 1 / (8 * (n : ℝ)) := by positivity
  constructor <;> nlinarith

theorem exercise20_factorial_ratio {n : ℕ} (hn : 2 ≤ n) :
    exp ((7 : ℝ) / 8) < (n.factorial : ℝ) / (((n : ℝ) / exp 1) ^ n * sqrt n) ∧
      (n.factorial : ℝ) / (((n : ℝ) / exp 1) ^ n * sqrt n) < exp 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpos : 0 < (n.factorial : ℝ) / (((n : ℝ) / exp 1) ^ n * sqrt n) := by positivity
  have he : log ((n.factorial : ℝ) / (((n : ℝ) / exp 1) ^ n * sqrt n)) =
      log (n.factorial : ℝ) - (n + 1 / 2) * log n + n := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      Real.log_pow, log_div hnpos.ne' (exp_pos _).ne', log_exp, log_sqrt hnpos.le]
    ring
  have h := exercise20_log_factorial hn
  constructor
  · apply (lt_log_iff_exp_lt hpos).mp
    simpa only [he] using h.1
  · apply (log_lt_iff_lt_exp hpos).mp
    simpa only [he] using h.2

end Rudin.Chapter08
