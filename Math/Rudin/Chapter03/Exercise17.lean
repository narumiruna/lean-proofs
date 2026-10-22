module

public import Math.Rudin.Chapter03.Exercise16

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace Rudin.Chapter03

/-- Index zero is the first source term. -/
def exercise17Seq (a x : ℝ) : ℕ → ℝ :=
  Nat.rec x (fun _ y => (a + y) / (1 + y))

@[simp] theorem exercise17Seq_zero (a x : ℝ) : exercise17Seq a x 0 = x := rfl

@[simp] theorem exercise17Seq_succ (a x : ℝ) (n : ℕ) :
    exercise17Seq a x (n + 1) = (a + exercise17Seq a x n) / (1 + exercise17Seq a x n) := rfl

/-- The second form of the recursion printed in the source. -/
theorem exercise17_source_update (a y : ℝ) (hy : 0 < y) :
    (a+y)/(1+y) = y + (a-y^2)/(1+y) := by
  have hd : 1+y ≠ 0 := by linarith
  field_simp
  ring

 theorem exercise17_root (a : ℝ) (ha : 1 < a) : 1 < Real.sqrt a := by
  have := Real.sq_sqrt (by linarith : 0 ≤ a)
  have := Real.sqrt_nonneg a
  nlinarith

 theorem exercise17_positive (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    0 < exercise17Seq a x n := by
  induction n with
  | zero => exact (by have := exercise17_root a ha; dsimp [exercise17Seq]; linarith)
  | succ n ih =>
    rw [exercise17Seq_succ]
    exact div_pos (by linarith) (by linarith)

 theorem exercise17_error_identity (a y : ℝ) (ha : 0 ≤ a) (hy : 0 < y) :
    (a+y)/(1+y) - Real.sqrt a = (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) := by
  have := Real.sq_sqrt ha
  field_simp
  nlinarith

 theorem exercise17_alternation (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    Real.sqrt a < exercise17Seq a x (2*n) ∧
    exercise17Seq a x (2*n+1) < Real.sqrt a := by
  have hr := exercise17_root a ha
  have flip : ∀ y : ℝ, 0 < y →
      (Real.sqrt a < y → (a+y)/(1+y) < Real.sqrt a) ∧
      (y < Real.sqrt a → Real.sqrt a < (a+y)/(1+y)) := by
    intro y hy
    have he := exercise17_error_identity a y (by linarith) hy
    constructor
    · intro h
      have : (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by linarith)
      linarith
    · intro h
      have : 0 < (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) :=
        div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)
      linarith
  induction n with
  | zero => exact ⟨hx, (flip x (exercise17_positive a x ha hx 0)).1 hx⟩
  | succ n ih =>
    have h := (flip _ (exercise17_positive a x ha hx (2*n+1))).2 ih.2
    have h' := (flip _ (exercise17_positive a x ha hx (2*n+2))).1 h
    change Real.sqrt a < exercise17Seq a x (2*n+2) at h
    change exercise17Seq a x (2*n+3) < Real.sqrt a at h'
    simpa only [Nat.mul_succ, Nat.add_assoc] using And.intro h h'

 theorem exercise17_two_step (a y : ℝ) (ha : 1 < a) (hy : 0 < y) :
    (a+(a+y)/(1+y))/(1+(a+y)/(1+y)) - y =
      2*(a-y^2)/(a+1+2*y) := by
  have h1 : 1+y ≠ 0 := by linarith
  have h2 : 1+(a+y)/(1+y) ≠ 0 := by positivity
  have h3 : a+1+2*y ≠ 0 := by linarith
  field_simp
  ring

 theorem exercise17_odd_decreasing (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) :
    StrictAnti (fun n => exercise17Seq a x (2*n)) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hy := exercise17_positive a x ha hx (2*n)
  have hr := (exercise17_alternation a x ha hx n).1
  have hs := Real.sq_sqrt (by linarith : 0 ≤ a)
  have hp := Real.sqrt_nonneg a
  have he := exercise17_two_step a _ ha hy
  have hneg : 2*(a-(exercise17Seq a x (2*n))^2)/(a+1+2*exercise17Seq a x (2*n)) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  change exercise17Seq a x (2*(n+1)) < exercise17Seq a x (2*n)
  rw [show 2*(n+1) = (2*n+1)+1 by omega, exercise17Seq_succ, exercise17Seq_succ]
  linarith

 theorem exercise17_even_increasing (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) :
    StrictMono (fun n => exercise17Seq a x (2*n+1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hy := exercise17_positive a x ha hx (2*n+1)
  have hr := (exercise17_alternation a x ha hx n).2
  have hs := Real.sq_sqrt (by linarith : 0 ≤ a)
  have he := exercise17_two_step a _ ha hy
  have hpos : 0 < 2*(a-(exercise17Seq a x (2*n+1))^2)/(a+1+2*exercise17Seq a x (2*n+1)) :=
    div_pos (by nlinarith) (by positivity)
  change exercise17Seq a x (2*n+1) < exercise17Seq a x (2*(n+1)+1)
  have he' : exercise17Seq a x (2*(n+1)+1) - exercise17Seq a x (2*n+1) =
      2*(a-(exercise17Seq a x (2*n+1))^2)/(a+1+2*exercise17Seq a x (2*n+1)) := by
    convert he using 1; congr 1
  linarith

/-- The cross ratio is exactly geometric, with a negative multiplier. -/
 theorem exercise17_cross_ratio (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    (exercise17Seq a x n - Real.sqrt a)/(exercise17Seq a x n + Real.sqrt a) =
      ((1-Real.sqrt a)/(1+Real.sqrt a))^n * ((x-Real.sqrt a)/(x+Real.sqrt a)) := by
  have hr := exercise17_root a ha
  induction n with
  | zero => simp [exercise17Seq]
  | succ n ih =>
    have hy := exercise17_positive a x ha hx n
    have hs := Real.sq_sqrt (by linarith : 0 ≤ a)
    have hstep : ((a+exercise17Seq a x n)/(1+exercise17Seq a x n)-Real.sqrt a) /
        ((a+exercise17Seq a x n)/(1+exercise17Seq a x n)+Real.sqrt a) =
        ((1-Real.sqrt a)/(1+Real.sqrt a)) *
        ((exercise17Seq a x n-Real.sqrt a)/(exercise17Seq a x n+Real.sqrt a)) := by
      have hd : (a+exercise17Seq a x n)/(1+exercise17Seq a x n)+Real.sqrt a ≠ 0 := by positivity
      field_simp
      linear_combination -2 * Real.sqrt a * (1 + exercise17Seq a x n) * hs
    rw [exercise17Seq_succ, hstep, ih, pow_succ]
    ring

 theorem exercise17_limit (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) :
    Tendsto (exercise17Seq a x) atTop (𝓝 (Real.sqrt a)) := by
  have hr := exercise17_root a ha
  have hq : |(1-Real.sqrt a)/(1+Real.sqrt a)| < 1 := by
    rw [abs_div, abs_of_neg (by linarith : 1-Real.sqrt a < 0),
      abs_of_pos (by linarith : 0 < 1+Real.sqrt a)]
    apply (div_lt_one (by linarith)).2
    linarith
  have ht : Tendsto (fun n => (exercise17Seq a x n-Real.sqrt a)/
      (exercise17Seq a x n+Real.sqrt a)) atTop (𝓝 0) := by
    simp_rw [exercise17_cross_ratio a x ha hx]
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq).mul_const
      ((x-Real.sqrt a)/(x+Real.sqrt a))
  have hl := ((ht.const_add 1).const_mul (Real.sqrt a)).div
    (ht.const_sub 1) (by norm_num : (1:ℝ)-0 ≠ 0)
  have hid : ∀ n, Real.sqrt a * (1+(exercise17Seq a x n-Real.sqrt a)/
      (exercise17Seq a x n+Real.sqrt a)) /
      (1-(exercise17Seq a x n-Real.sqrt a)/(exercise17Seq a x n+Real.sqrt a)) =
      exercise17Seq a x n := by
    intro n
    have hy := exercise17_positive a x ha hx n
    have hd : 1-(exercise17Seq a x n-Real.sqrt a)/(exercise17Seq a x n+Real.sqrt a) ≠ 0 := by
      rw [ne_eq, sub_eq_zero, eq_comm, div_eq_iff (by positivity)]
      linarith
    field_simp [ne_of_gt (by linarith : 0 < Real.sqrt a)]
    ring
  have hl' : Tendsto (fun n => Real.sqrt a * (1+(exercise17Seq a x n-Real.sqrt a)/
      (exercise17Seq a x n+Real.sqrt a)) /
      (1-(exercise17Seq a x n-Real.sqrt a)/(exercise17Seq a x n+Real.sqrt a))) atTop
      (𝓝 (Real.sqrt a)) := by convert hl using 1; simp
  simpa only [hid] using hl'

/-- Linear convergence: the signed successive-error ratio has a nonzero negative limit. -/
 theorem exercise17_rate (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) :
    Tendsto (fun n => (exercise17Seq a x (n+1)-Real.sqrt a) /
      (exercise17Seq a x n-Real.sqrt a)) atTop
      (𝓝 ((1-Real.sqrt a)/(1+Real.sqrt a))) ∧
    0 < (Real.sqrt a-1)/(Real.sqrt a+1) ∧
    (Real.sqrt a-1)/(Real.sqrt a+1) < 1 := by
  have hr := exercise17_root a ha
  have hne : ∀ n, exercise17Seq a x n - Real.sqrt a ≠ 0 := by
    intro n
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simpa only [two_mul] using sub_ne_zero.2 (ne_of_gt (exercise17_alternation a x ha hx k).1)
    · exact sub_ne_zero.2 (ne_of_lt (exercise17_alternation a x ha hx k).2)
  have hid : ∀ n, (exercise17Seq a x (n+1)-Real.sqrt a) /
      (exercise17Seq a x n-Real.sqrt a) = (1-Real.sqrt a)/(1+exercise17Seq a x n) := by
    intro n
    rw [exercise17Seq_succ, exercise17_error_identity a _ (by linarith)
      (exercise17_positive a x ha hx n)]
    field_simp [hne n]
  refine ⟨?_, div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
  simp_rw [hid]
  exact tendsto_const_nhds.div (tendsto_const_nhds.add (exercise17_limit a x ha hx)) (by linarith)

/-- In contrast, Exercise 16 has successive-error ratio tending to zero (quadratic order). -/
 theorem exercise17_newton_comparison (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) :
    Tendsto (fun n => (exercise16Seq a x (n+1)-Real.sqrt a) /
      (exercise16Seq a x n-Real.sqrt a)) atTop (𝓝 0) := by
  have ht := exercise16_limit a x ha hx
  have hid : ∀ n, (exercise16Seq a x (n+1)-Real.sqrt a) /
      (exercise16Seq a x n-Real.sqrt a) =
      (exercise16Seq a x n-Real.sqrt a)/(2*exercise16Seq a x n) := by
    intro n
    rw [(exercise16_error_step a x ha hx n).1]
    have he : exercise16Seq a x n-Real.sqrt a ≠ 0 :=
      sub_ne_zero.2 (ne_of_gt (exercise16_above a x ha hx n))
    field_simp
  simp_rw [hid]
  convert (ht.sub_const (Real.sqrt a)).div (ht.const_mul 2) (by positivity : 2*Real.sqrt a ≠ 0) using 1; simp

/-- The absolute successive-error ratio for the Möbius recursion. -/
theorem exercise17_absolute_rate (a x : ℝ) (ha : 1 < a) (hx : Real.sqrt a < x) :
    Tendsto (fun n => |exercise17Seq a x (n+1)-Real.sqrt a| /
      |exercise17Seq a x n-Real.sqrt a|) atTop
      (𝓝 ((Real.sqrt a-1)/(Real.sqrt a+1))) := by
  have hr := exercise17_root a ha
  have ht := (exercise17_rate a x ha hx).1.abs
  have he : |(1-Real.sqrt a)/(1+Real.sqrt a)| =
      (Real.sqrt a-1)/(Real.sqrt a+1) := by
    rw [abs_div, abs_of_neg (by linarith : 1-Real.sqrt a < 0),
      abs_of_pos (by linarith : 0 < 1+Real.sqrt a)]
    congr 1 <;> ring
  simpa only [abs_div, he] using ht

/-- The quadratic error constant of the faster Newton recursion is exactly `1/(2 sqrt a)`. -/
theorem exercise17_newton_quadratic_rate (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) :
    Tendsto (fun n => (exercise16Seq a x (n+1)-Real.sqrt a) /
      (exercise16Seq a x n-Real.sqrt a)^2) atTop (𝓝 (1/(2*Real.sqrt a))) := by
  have hid : ∀ n, (exercise16Seq a x (n+1)-Real.sqrt a) /
      (exercise16Seq a x n-Real.sqrt a)^2 = 1/(2*exercise16Seq a x n) := by
    intro n
    rw [(exercise16_error_step a x ha hx n).1]
    have he : exercise16Seq a x n-Real.sqrt a ≠ 0 :=
      sub_ne_zero.2 (ne_of_gt (exercise16_above a x ha hx n))
    field_simp
  simp_rw [hid]
  exact tendsto_const_nhds.div ((exercise16_limit a x ha hx).const_mul 2)
    (by positivity : 2*Real.sqrt a ≠ 0)

end Rudin.Chapter03
