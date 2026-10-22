module

public import Math.Rudin.Chapter05.Exercise26
public import Math.Rudin.Support.RiemannIntegrability

/-!
# R06E15: a strict integral inequality

Source: Rudin, Third Edition, Exercise 6.15, book page 141 (PDF page 150).
The normalization and conclusions use actual ordinary Darboux integrals.
Derivatives at both endpoints are within derivatives on the closed interval.
The strict inequality follows by excluding a zero square integral: continuity
would give a homogeneous differential equation, whose zero initial value
forces the function to vanish.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set MeasureTheory
open Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesMeasureBridge
  Rudin.Support.RiemannIntegrability

private theorem exercise15_continuous_ri {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) :
    HasDarbouxRSIntegral g id a b (∫ x in a..b, g x) := by
  have hid : (StieltjesFunction.id : ℝ → ℝ) = id := by
    funext x
    exact StieltjesFunction.id_apply x
  simpa only [hid, ← Real.volume_eq_stieltjes_id] using
    continuous_bridge StieltjesFunction.id hab hg

private theorem exercise15_identity {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hn : HasDarbouxRSIntegral (fun x ↦ f x ^ 2) id a b 1) :
    (∫ x in a..b, x * f x * f' x) = -(1 / 2 : ℝ) := by
  have hf : ContinuousOn f (Icc a b) := fun x hx ↦ (hd x hx).continuousWithinAt
  have hn' := (intervalIntegrable_and_integral_eq hab hn).2
  have hprod := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (a := a) (b := b) (u := fun x ↦ x * f x) (u' := fun x ↦ f x + x * f' x)
    (v := f) (v' := f')
    (by
      rw [uIcc_of_le hab]
      intro x hx
      simpa only [one_mul, Pi.mul_def, id_eq] using
        (hasDerivWithinAt_id x (Icc a b)).mul (hd x hx))
    (by simpa only [uIcc_of_le hab] using hd)
    ((hf.add (continuousOn_id.mul hc)).intervalIntegrable_of_Icc hab)
    (hc.intervalIntegrable_of_Icc hab)
  have heq : (fun x ↦ (f x + x * f' x) * f x + x * f x * f' x) =
      (fun x ↦ f x ^ 2 + 2 * (x * f x * f' x)) := by
    funext x
    ring
  have hi₁ : IntervalIntegrable (fun x ↦ f x ^ 2) volume a b := by
    simpa only [Pi.pow_def] using (hf.pow 2).intervalIntegrable_of_Icc hab (μ := volume)
  have hi₂ : IntervalIntegrable (fun x ↦ 2 * (x * f x * f' x)) volume a b := by
    simpa only [Pi.mul_apply, id_eq] using
      (((continuousOn_id.mul hf).mul hc).const_mul 2).intervalIntegrable_of_Icc hab (μ := volume)
  rw [heq, intervalIntegral.integral_add hi₁ hi₂,
    intervalIntegral.integral_const_mul, hn', ha, hb] at hprod
  nlinarith

/-- R06E15, first conclusion, as an actual ordinary Riemann integral. -/
theorem exercise15_integration_identity {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hn : HasDarbouxRSIntegral (fun x ↦ f x ^ 2) id a b 1) :
    HasDarbouxRSIntegral (fun x ↦ x * f x * f' x) id a b (-(1 / 2 : ℝ)) := by
  rw [← exercise15_identity hab hd hc ha hb hn]
  exact exercise15_continuous_ri hab
    ((continuousOn_id.mul (fun x hx ↦ (hd x hx).continuousWithinAt)).mul hc)

private theorem exercise15_square_pos {a b c : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) (ha : f a = 0)
    (hn : HasDarbouxRSIntegral (fun x ↦ f x ^ 2) id a b 1) :
    0 < ∫ x in a..b, (f' x + c * (x * f x)) ^ 2 := by
  have hf : ContinuousOn f (Icc a b) := fun x hx ↦ (hd x hx).continuousWithinAt
  have hn' := (intervalIntegrable_and_integral_eq hab hn).2
  have hlt : a < b := by
    by_contra h
    have he : a = b := le_antisymm hab (not_lt.mp h)
    subst b
    simp only [intervalIntegral.integral_same] at hn'
    norm_num at hn'
  have hs : ContinuousOn (fun x ↦ (f' x + c * (x * f x)) ^ 2) (Icc a b) :=
    (hc.add ((continuousOn_id.mul hf).const_mul c)).pow 2
  have hne : ∃ x ∈ Icc a b, 0 < (f' x + c * (x * f x)) ^ 2 := by
    by_contra! hz
    have hode (x : ℝ) (hx : x ∈ Icc a b) : f' x = -c * x * f x := by
      have hh : (f' x + c * (x * f x)) ^ 2 = 0 := le_antisymm (hz x hx) (sq_nonneg _)
      have hh' := sq_eq_zero_iff.mp hh
      nlinarith
    have hzero := Rudin.Chapter05.exercise26_zero_solution hd ha
      (A := |c| * (|a| + |b|)) (by
        intro x hx
        rw [hode x hx, abs_mul, abs_mul, abs_neg]
        have hx' : |x| ≤ |a| + |b| := by
          apply abs_le.mpr
          constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b, hx.1, hx.2]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx' (abs_nonneg c)) (abs_nonneg (f x)))
    have hi : (∫ x in a..b, f x ^ 2) = 0 := by
      calc
        _ = ∫ x in a..b, (0 : ℝ) := intervalIntegral.integral_congr (by
          intro x hx
          rw [uIcc_of_le hab] at hx
          change f x ^ 2 = 0
          rw [hzero x hx]
          norm_num)
        _ = 0 := by simp
    linarith
  exact intervalIntegral.integral_pos hlt hs
    (fun x _ ↦ sq_nonneg _) hne

/-- R06E15, second conclusion. Equality is excluded by the zero-solution theorem,
not by assuming strictness in Schwarz's inequality. -/
theorem exercise15_strict_product_bound {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hn : HasDarbouxRSIntegral (fun x ↦ f x ^ 2) id a b 1) :
    (1 / 4 : ℝ) < (∫ x in a..b, f' x ^ 2) * (∫ x in a..b, x ^ 2 * f x ^ 2) := by
  have hf : ContinuousOn f (Icc a b) := fun x hx ↦ (hd x hx).continuousWithinAt
  let A := ∫ x in a..b, f' x ^ 2
  let B := ∫ x in a..b, x ^ 2 * f x ^ 2
  have hA : 0 ≤ A := intervalIntegral.integral_nonneg hab (fun _ _ ↦ sq_nonneg _)
  have hcross := exercise15_identity hab hd hc ha hb hn
  have hp := exercise15_square_pos (c := 2 * A) hab hd hc ha hn
  have heq : (fun x ↦ (f' x + 2 * A * (x * f x)) ^ 2) =
      (fun x ↦ f' x ^ 2 + (4 * A) * (x * f x * f' x) +
        (4 * A ^ 2) * (x ^ 2 * f x ^ 2)) := by
    funext x
    ring
  have hi₁ : IntervalIntegrable (fun x ↦ f' x ^ 2) volume a b := by
    simpa only [Pi.pow_def] using (hc.pow 2).intervalIntegrable_of_Icc hab (μ := volume)
  have hi₂ : IntervalIntegrable (fun x ↦ (4 * A) * (x * f x * f' x)) volume a b := by
    simpa only [Pi.mul_apply, id_eq] using
      (((continuousOn_id.mul hf).mul hc).const_mul (4 * A)).intervalIntegrable_of_Icc hab (μ := volume)
  have hi₃ : IntervalIntegrable (fun x ↦ (4 * A ^ 2) * (x ^ 2 * f x ^ 2)) volume a b := by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using
      (((continuousOn_id.pow 2).mul (hf.pow 2)).const_mul (4 * A ^ 2)).intervalIntegrable_of_Icc hab (μ := volume)
  rw [heq, intervalIntegral.integral_add (hi₁.add hi₂) hi₃,
    intervalIntegral.integral_add hi₁ hi₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcross] at hp
  change (1 / 4 : ℝ) < A * B
  change 0 < A + 4 * A * (-(1 / 2 : ℝ)) + 4 * A ^ 2 * B at hp
  by_contra! h
  have : 0 ≤ A * (1 - 4 * (A * B)) := mul_nonneg hA (by linarith)
  nlinarith

/-- The two factors in the strict bound are actual Riemann integrals. -/
theorem exercise15 {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hc : ContinuousOn f' (Icc a b)) (ha : f a = 0) (hb : f b = 0)
    (hn : HasDarbouxRSIntegral (fun x ↦ f x ^ 2) id a b 1) :
    HasDarbouxRSIntegral (fun x ↦ x * f x * f' x) id a b (-(1 / 2 : ℝ)) ∧
    ∃ A B : ℝ, HasDarbouxRSIntegral (fun x ↦ f' x ^ 2) id a b A ∧
      HasDarbouxRSIntegral (fun x ↦ x ^ 2 * f x ^ 2) id a b B ∧ (1 / 4 : ℝ) < A * B := by
  have hf : ContinuousOn f (Icc a b) := fun x hx ↦ (hd x hx).continuousWithinAt
  exact ⟨exercise15_integration_identity hab hd hc ha hb hn, _, _,
    exercise15_continuous_ri hab (hc.pow 2),
    exercise15_continuous_ri hab ((continuousOn_id.pow 2).mul (hf.pow 2)),
    exercise15_strict_product_bound hab hd hc ha hb hn⟩

end Rudin.Chapter06
