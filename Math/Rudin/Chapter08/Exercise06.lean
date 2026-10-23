module

public import Mathlib
public import Mathlib.Topology.Instances.RealVectorSpace

/-! # Chapter 8, Exercise 6
Continuous real exponential homomorphisms, with nonzero meaning not identically
zero. Positivity and nonvanishing are proved, not added as assumptions.
Source: book page 197, PDF page 206.
-/

@[expose] public section

namespace Rudin.Chapter08

/-- The algebraic equation already forces positivity of a nonzero solution. -/
theorem exercise06_positive {f : ℝ → ℝ}
    (hm : ∀ x y, f x * f y = f (x + y)) (hn : ∃ x, f x ≠ 0) :
    f 0 = 1 ∧ ∀ x, 0 < f x := by
  obtain ⟨t, ht⟩ := hn
  have h0 : f 0 = 1 := by
    apply mul_left_cancel₀ ht
    simpa using hm t 0
  have hne (x : ℝ) : f x ≠ 0 := by
    intro hx
    have h := hm x (-x)
    simp [hx, h0] at h
  refine ⟨h0, fun x => ?_⟩
  have he : f x = f (x / 2) ^ 2 := by
    have h := hm (x / 2) (x / 2)
    rw [show x / 2 + x / 2 = x by ring] at h
    nlinarith
  rw [he]
  exact sq_pos_of_ne_zero (hne _)

/-- Part (b): continuity suffices to make the logarithm a real linear map. -/
theorem exercise06_b {f : ℝ → ℝ} (hf : Continuous f)
    (hm : ∀ x y, f x * f y = f (x + y)) (hn : ∃ x, f x ≠ 0) :
    ∃ c : ℝ, ∀ x, f x = Real.exp (c * x) := by
  obtain ⟨h0, hp⟩ := exercise06_positive hm hn
  let g : ℝ →+ ℝ :=
    { toFun := fun x => Real.log (f x)
      map_zero' := by simp [h0]
      map_add' := by
        intro x y
        rw [← hm, Real.log_mul (hp x).ne' (hp y).ne'] }
  have hg : Continuous g := hf.log (fun x => (hp x).ne')
  refine ⟨g 1, fun x => ?_⟩
  have he : g x = g 1 * x := by
    have h := map_real_smul g hg x (1 : ℝ)
    simpa only [smul_eq_mul, mul_one, mul_comm x (g 1)] using h
  calc
    f x = Real.exp (g x) := (Real.exp_log (hp x)).symm
    _ = Real.exp (g 1 * x) := by rw [he]

/-- Part (a), with no extra continuity hypothesis. -/
theorem exercise06_a {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hm : ∀ x y, f x * f y = f (x + y)) (hn : ∃ x, f x ≠ 0) :
    ∃ c : ℝ, ∀ x, f x = Real.exp (c * x) :=
  exercise06_b hf.continuous hm hn

/-- Every function in the classification actually satisfies all hypotheses. -/
theorem exercise06_converse (c : ℝ) :
    Differentiable ℝ (fun x => Real.exp (c * x)) ∧
    (∀ x y, Real.exp (c * x) * Real.exp (c * y) = Real.exp (c * (x + y))) ∧
    (∃ x : ℝ, Real.exp (c * x) ≠ 0) := by
  refine ⟨by fun_prop, ?_, ⟨0, Real.exp_ne_zero _⟩⟩
  intro x y
  rw [mul_add, Real.exp_add]

end Rudin.Chapter08
