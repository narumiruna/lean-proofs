module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

/-! # R01E10
Rudin, book pages 22–23 (PDF pages 31–32). The coefficients are exactly the
specified nonnegative real square roots. The sign of the imaginary part selects
between their complex combination and its conjugate, including the boundary case.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The specified real coefficient. -/
noncomputable def exercise10A (w : ℂ) : ℝ := Real.sqrt ((‖w‖ + w.re) / 2)

/-- The specified nonnegative imaginary coefficient. -/
noncomputable def exercise10B (w : ℂ) : ℝ := Real.sqrt ((‖w‖ - w.re) / 2)

/-- The complex number `a + b I` specified in the exercise. -/
noncomputable def exercise10Z (w : ℂ) : ℂ :=
  (exercise10A w : ℂ) + (exercise10B w : ℂ) * Complex.I

/-- Both coefficients are nonnegative and have the prescribed squares. -/
theorem exercise10_coefficients (w : ℂ) :
    0 ≤ exercise10A w ∧ 0 ≤ exercise10B w ∧
    exercise10A w ^ 2 = (‖w‖ + w.re) / 2 ∧
    exercise10B w ^ 2 = (‖w‖ - w.re) / 2 := by
  have h := (abs_le.mp (Complex.abs_re_le_norm w)).1
  have h' := Complex.re_le_norm w
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _,
    Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)⟩

/-- The two real identities needed for the square, with the absolute value explicit. -/
theorem exercise10_coordinate_identities (w : ℂ) :
    exercise10A w ^ 2 - exercise10B w ^ 2 = w.re ∧
    2 * exercise10A w * exercise10B w = |w.im| := by
  obtain ⟨ha, hb, ha2, hb2⟩ := exercise10_coefficients w
  refine ⟨by linarith, ?_⟩
  apply (sq_eq_sq₀ (by positivity) (abs_nonneg w.im)).mp
  calc
    (2 * exercise10A w * exercise10B w) ^ 2 =
        4 * (exercise10A w ^ 2 * exercise10B w ^ 2) := by ring
    _ = |w.im| ^ 2 := by
      rw [ha2, hb2, sq_abs]
      nlinarith [Complex.sq_norm_sub_sq_re w]

/-- For nonnegative imaginary part, the stated `a + b I` squares to `w`. -/
theorem exercise10_nonnegative_imaginary (w : ℂ) (hv : 0 ≤ w.im) :
    exercise10Z w ^ 2 = w := by
  obtain ⟨hr, hi⟩ := exercise10_coordinate_identities w
  rw [abs_of_nonneg hv] at hi
  apply Complex.ext
  · simp [exercise10Z, pow_two, Complex.mul_re] at *
    nlinarith
  · simp [exercise10Z, pow_two, Complex.mul_im]
    linarith

/-- For nonpositive imaginary part, the conjugate of `a + b I` squares to `w`. -/
theorem exercise10_nonpositive_imaginary (w : ℂ) (hv : w.im ≤ 0) :
    star (exercise10Z w) ^ 2 = w := by
  obtain ⟨hr, hi⟩ := exercise10_coordinate_identities w
  rw [abs_of_nonpos hv] at hi
  apply Complex.ext
  · simp [exercise10Z, pow_two, Complex.mul_re] at *
    nlinarith
  · simp [exercise10Z, pow_two, Complex.mul_im]
    linarith

/-- The square root selected by the sign-dependent construction. -/
noncomputable def exercise10Root (w : ℂ) : ℂ :=
  if 0 ≤ w.im then exercise10Z w else star (exercise10Z w)

/-- The selected formula is a square root for every complex number. -/
theorem exercise10_root_sq (w : ℂ) : exercise10Root w ^ 2 = w := by
  unfold exercise10Root
  split_ifs with hv
  · exact exercise10_nonnegative_imaginary w hv
  · exact exercise10_nonpositive_imaginary w (le_of_not_ge hv)

/-- Every root is the selected explicit root or its negative. -/
theorem exercise10_roots_iff (w t : ℂ) :
    t ^ 2 = w ↔ t = exercise10Root w ∨ t = -exercise10Root w := by
  calc
    t ^ 2 = w ↔ t ^ 2 = exercise10Root w ^ 2 := by rw [exercise10_root_sq]
    _ ↔ t = exercise10Root w ∨ t = -exercise10Root w := sq_eq_sq_iff_eq_or_eq_neg

/-- For nonzero `w` these are two distinct roots, and there are no others.
No condition excluding zero imaginary part is imposed. -/
theorem exercise10_nonzero_roots (w : ℂ) (hw : w ≠ 0) :
    exercise10Root w ≠ -exercise10Root w ∧
    exercise10Root w ^ 2 = w ∧ (-exercise10Root w) ^ 2 = w ∧
    (∀ t : ℂ, t ^ 2 = w ↔ t = exercise10Root w ∨ t = -exercise10Root w) := by
  have hn : exercise10Root w ≠ 0 := by
    intro h
    have hs := exercise10_root_sq w
    rw [h, zero_pow (by decide)] at hs
    exact hw hs.symm
  refine ⟨?_, exercise10_root_sq w, ?_, exercise10_roots_iff w⟩
  · intro h
    exact hn (CharZero.neg_eq_self_iff.mp h.symm)
  · simpa using exercise10_root_sq w

/-- Zero is the exceptional value: its unique square root is zero. -/
theorem exercise10_zero_root :
    (∀ t : ℂ, t ^ 2 = 0 ↔ t = 0) ∧ ∃! t : ℂ, t ^ 2 = 0 := by
  exact ⟨fun _ => sq_eq_zero_iff, 0, by simp, fun _ h => sq_eq_zero_iff.mp h⟩

end Rudin.Chapter01
