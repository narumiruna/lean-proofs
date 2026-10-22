module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace Rudin.Chapter05

open Set Finset

/-- Taylor polynomial from an explicit derivative jet. -/
noncomputable def exercise20_polynomial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℕ → ℝ → E) (n : ℕ) (a t : ℝ) : E :=
  ∑ k ∈ range n, ((t - a) ^ k / (k.factorial : ℝ)) • F k a

private theorem exercise20_monomial_derivative (k : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (k + 1) / ((k + 1).factorial : ℝ))
      (t ^ k / (k.factorial : ℝ)) t := by
  convert ((hasDerivAt_id t).fun_pow (k + 1)).div_const ((k + 1).factorial : ℝ) using 1 <;>
    simp only [id_eq, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, mul_one]
  field_simp

private theorem exercise20_polynomial_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℕ → ℝ → E) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => exercise20_polynomial F (n + 1) 0 x)
      (exercise20_polynomial (fun k => F (k + 1)) n 0 t) t := by
  simp only [exercise20_polynomial, sub_zero, sum_range_succ']
  convert ((HasDerivAt.sum (u := range n) (fun k _ =>
    (exercise20_monomial_derivative k t).smul_const (F (k + 1) 0))).add_const
      (F 0 0)) using 1
  ext x
  simp

/-- Unit-interval Taylor bound. Every lower derivative is supplied explicitly;
    no continuity of the highest derivative is needed. -/
theorem exercise20_unit_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (F : ℕ → ℝ → E) {M : ℝ}
    (hd : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (F k) (F (k + 1) t) (Icc 0 1) t)
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F n t‖ ≤ M) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F 0 t - exercise20_polynomial F n 0 t‖ ≤ M * t ^ n / (n.factorial : ℝ) := by
  induction n generalizing F with
  | zero => simpa [exercise20_polynomial] using hM
  | succ n ih =>
    have hi := ih (fun k => F (k + 1))
      (fun k hk t ht => hd (k + 1) (by omega) t ht) hM
    let R := fun t => F 0 t - exercise20_polynomial F (n + 1) 0 t
    have hr : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt R
        (F 1 t - exercise20_polynomial (fun k => F (k + 1)) n 0 t) (Icc 0 1) t := by
      intro t ht
      exact (hd 0 (by omega) t ht).sub
        (exercise20_polynomial_derivative F n t).hasDerivWithinAt
    have hc : ContinuousOn R (Icc (0 : ℝ) 1) :=
      fun t ht => (hr t ht).continuousWithinAt
    have hb : ∀ t : ℝ, HasDerivAt
        (fun x : ℝ => M * x ^ (n + 1) / ((n + 1).factorial : ℝ))
        (M * t ^ n / (n.factorial : ℝ)) t := by
      intro t
      convert (exercise20_monomial_derivative n t).const_mul M using 1
      · ext x; ring
      · ring
    apply image_norm_le_of_norm_deriv_right_le_deriv_boundary hc
      (fun t ht => (hr t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)) ?_ hb
      (fun t ht => hi t (Ico_subset_Icc_self ht))
    simp [R, exercise20_polynomial, sum_range_succ', zero_pow]

/-- Vector Taylor inequality in either direction, with one-sided derivatives
    at the two endpoints. `F 0` is the function and `F k` its genuine kth derivative.
    The conclusion also includes the zero-order case. -/
theorem exercise20_vector_taylor_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (F : ℕ → ℝ → E) {a b M : ℝ}
    (hd : ∀ k < n, ∀ t ∈ uIcc a b,
      HasDerivWithinAt (F k) (F (k + 1) t) (uIcc a b) t)
    (hM : ∀ t ∈ uIcc a b, ‖F n t‖ ≤ M) :
    ‖F 0 b - exercise20_polynomial F n a b‖ ≤
      M * |b - a| ^ n / (n.factorial : ℝ) := by
  let d := b - a
  let G : ℕ → ℝ → E := fun k t => (d ^ k) • F k (a + t * d)
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, a + t * d ∈ uIcc a b := by
    intro t ht
    rw [Set.mem_uIcc]
    dsimp [d]
    rcases le_total a b with hab | hab
    · left; constructor <;> nlinarith [ht.1, ht.2]
    · right; constructor <;> nlinarith [ht.1, ht.2]
  have hg : ∀ k < n, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (G k) (G (k + 1) t) (Icc 0 1) t := by
    intro k hk t ht
    have hc := (hd k hk _ (hm t ht)).scomp t
      (((hasDerivAt_id t).mul_const d).const_add a).hasDerivWithinAt hm
    convert hc.const_smul (d ^ k) using 1 <;>
      simp [G, Function.comp_def, pow_succ, smul_smul]
    rfl
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖G n t‖ ≤ |d| ^ n * M := by
    intro t ht
    dsimp [G]
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM _ (hm t ht)) (pow_nonneg (abs_nonneg _) _)
  have h := exercise20_unit_bound n G hg hb 1 (by simp)
  simpa [G, d, exercise20_polynomial, smul_smul, mul_div_assoc,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end Rudin.Chapter05
