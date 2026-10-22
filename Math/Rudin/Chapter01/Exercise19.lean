module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R01E19: the distance locus and the positive-radius error

Source: Rudin, Exercise 1.19, book page 23 (PDF page 32).
The original request requires a positive radius for every pair `a,b`.
`exercise19_original_counterexample` refutes that request in dimension one:
no choice of center and positive radius works when `a = b = 0`.

The correction allows radius zero. `exercise19` gives the stated formulas in
all dimensions, including dimension zero. `exercise19_nondegenerate` gives a
positive radius when `a ≠ b`. `exercise19_degenerate` identifies the remaining
locus as a singleton. No source cases are omitted.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- The center `(4 b - a) / 3`, with vector division written as scalar multiplication. -/
noncomputable def exercise19_center {k : ℕ}
    (a b : EuclideanSpace ℝ (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  (1 / 3 : ℝ) • ((4 : ℝ) • b - a)

/-- The corrected radius is nonnegative, not always positive. -/
noncomputable def exercise19_radius {k : ℕ}
    (a b : EuclideanSpace ℝ (Fin k)) : ℝ :=
  2 * ‖b - a‖ / 3

private theorem exercise19_squared_identity {k : ℕ}
    (a b x : EuclideanSpace ℝ (Fin k)) :
    ‖x - a‖ ^ 2 - 4 * ‖x - b‖ ^ 2 =
      -3 * (‖x - exercise19_center a b‖ ^ 2 - (exercise19_radius a b) ^ 2) := by
  simp [exercise19_center, exercise19_radius, norm_sub_sq_real, norm_smul, mul_pow,
    div_pow, inner_sub_right, real_inner_smul_right, real_inner_comm]
  ring

/-- Corrected distance-locus theorem, with the explicit source formulas. -/
theorem exercise19 {k : ℕ} (a b x : EuclideanSpace ℝ (Fin k)) :
    ‖x - a‖ = 2 * ‖x - b‖ ↔
      ‖x - exercise19_center a b‖ = exercise19_radius a b := by
  have hr : 0 ≤ exercise19_radius a b := by
    unfold exercise19_radius
    positivity
  have hi := exercise19_squared_identity a b x
  constructor
  · intro h
    rw [h] at hi
    have hs : ‖x - exercise19_center a b‖ ^ 2 = (exercise19_radius a b) ^ 2 := by
      nlinarith
    exact (sq_eq_sq₀ (norm_nonneg _) hr).mp hs
  · intro h
    have hs : ‖x - a‖ ^ 2 = (2 * ‖x - b‖) ^ 2 := by
      nlinarith
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hs

/-- For distinct centers, the source construction has positive radius. -/
theorem exercise19_nondegenerate {k : ℕ} (a b : EuclideanSpace ℝ (Fin k))
    (hab : a ≠ b) :
    0 < exercise19_radius a b ∧
      ∀ x, ‖x - a‖ = 2 * ‖x - b‖ ↔
        ‖x - exercise19_center a b‖ = exercise19_radius a b := by
  refine ⟨?_, fun x => exercise19 a b x⟩
  unfold exercise19_radius
  have : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  positivity

/-- Coincident centers give exactly the singleton `{a}`, or a radius-zero sphere. -/
theorem exercise19_degenerate {k : ℕ} (a x : EuclideanSpace ℝ (Fin k)) :
    (‖x - a‖ = 2 * ‖x - a‖ ↔ x = a) ∧
    exercise19_center a a = a ∧ exercise19_radius a a = 0 := by
  refine ⟨?_, ?_, by simp [exercise19_radius]⟩
  · constructor
    · intro h
      have : ‖x - a‖ = 0 := by linarith
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    · rintro rfl
      simp
  · unfold exercise19_center
    module

/-- A singleton distance locus cannot be any positive-radius sphere.
The reflection of `a` about a proposed center supplies a second sphere point;
this proves failure for every center and radius, not only the displayed formula. -/
theorem exercise19_degenerate_no_positive_radius {k : ℕ}
    (a : EuclideanSpace ℝ (Fin k)) :
    ¬ ∃ (c : EuclideanSpace ℝ (Fin k)) (r : ℝ), 0 < r ∧
      ∀ x, ‖x - a‖ = 2 * ‖x - a‖ ↔ ‖x - c‖ = r := by
  rintro ⟨c, r, hr, h⟩
  have ha : ‖a - c‖ = r := (h a).mp (by simp)
  have hreflect : ‖c + (c - a) - c‖ = r := by
    simpa only [add_sub_cancel_left, norm_sub_rev] using ha
  have heq : c + (c - a) = a :=
    ((exercise19_degenerate a (c + (c - a))).1).mp ((h _).mpr hreflect)
  have htwice : (2 : ℝ) • (c - a) = 0 := by
    calc
      (2 : ℝ) • (c - a) = (c + (c - a)) - a := by module
      _ = 0 := by rw [heq, sub_self]
  have hc : c = a := sub_eq_zero.mp ((smul_eq_zero.mp htwice).resolve_left (by norm_num))
  rw [hc, sub_self, norm_zero] at ha
  linarith

/-- Concrete refutation of the original universal positive-radius request in `ℝ¹`. -/
theorem exercise19_original_counterexample :
    ¬ ∃ (c : EuclideanSpace ℝ (Fin 1)) (r : ℝ), 0 < r ∧
      ∀ x : EuclideanSpace ℝ (Fin 1),
        ‖x - 0‖ = 2 * ‖x - 0‖ ↔ ‖x - c‖ = r :=
  exercise19_degenerate_no_positive_radius 0

end Rudin.Chapter01

#print axioms Rudin.Chapter01.exercise19
#print axioms Rudin.Chapter01.exercise19_nondegenerate
#print axioms Rudin.Chapter01.exercise19_degenerate
#print axioms Rudin.Chapter01.exercise19_degenerate_no_positive_radius
#print axioms Rudin.Chapter01.exercise19_original_counterexample
