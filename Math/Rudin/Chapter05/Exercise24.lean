module

public import Math.Rudin.Chapter05.Exercise22
public import Math.Rudin.Chapter03.Exercise17

@[expose] public section
noncomputable section
open Set Filter Function
open scoped Topology
namespace Rudin.Chapter05

/-- Both maps are used only at positive arguments. -/
def exercise24Newton (a x : ℝ) : ℝ := (x + a/x)/2

def exercise24Mobius (a x : ℝ) : ℝ := (a+x)/(1+x)

/-- Index zero is the first source term. These are the verified Chapter 3 iterations. -/
def exercise24N (a x : ℝ) : ℕ → ℝ := Chapter03.exercise16Seq a x

def exercise24M (a x : ℝ) : ℕ → ℝ := Chapter03.exercise17Seq a x

@[simp] theorem exercise24N_zero (a x : ℝ) : exercise24N a x 0 = x := rfl
@[simp] theorem exercise24M_zero (a x : ℝ) : exercise24M a x 0 = x := rfl
@[simp] theorem exercise24N_succ (a x : ℝ) (n : ℕ) :
    exercise24N a x (n+1) = exercise24Newton a (exercise24N a x n) := rfl
@[simp] theorem exercise24M_succ (a x : ℝ) (n : ℕ) :
    exercise24M a x (n+1) = exercise24Mobius a (exercise24M a x n) := rfl

theorem exercise24_orbits (a x : ℝ) (n : ℕ) :
    exercise22Orbit (exercise24Newton a) x n = exercise24N a x n ∧
    exercise22Orbit (exercise24Mobius a) x n = exercise24M a x n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => simp only [exercise22Orbit_succ, exercise24N_succ, exercise24M_succ,
      ih.1, ih.2, and_self]

theorem exercise24_positive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (n : ℕ) :
    0 < exercise24N a x n ∧ 0 < exercise24M a x n := by
  induction n with
  | zero => exact ⟨hx, hx⟩
  | succ n ih =>
    rw [exercise24N_succ, exercise24M_succ]
    dsimp [exercise24Newton, exercise24Mobius]
    exact ⟨div_pos (add_pos ih.1 (div_pos ha ih.1)) (by norm_num),
      div_pos (add_pos ha ih.2) (by linarith [ih.2])⟩

/-- Exact positive fixed-point sets for both maps. -/
theorem exercise24_fixed_points {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (exercise24Newton a x = x ↔ x = Real.sqrt a) ∧
    (exercise24Mobius a x = x ↔ x = Real.sqrt a) := by
  have hr := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have hn : exercise24Newton a x = x ↔ x^2 = a := by
    dsimp [exercise24Newton]
    constructor
    · intro h; field_simp at h; nlinarith
    · intro h; field_simp; nlinarith
  have hm : exercise24Mobius a x = x ↔ x^2 = a := by
    dsimp [exercise24Mobius]
    rw [div_eq_iff (by positivity : (1+x) ≠ 0)]
    constructor <;> intro h <;> nlinarith
  have he : x^2 = a ↔ x = Real.sqrt a := by
    constructor
    · intro h; nlinarith
    · rintro rfl; exact hs
  exact ⟨hn.trans he, hm.trans he⟩

theorem exercise24_constant {a : ℝ} (ha : 0 < a) (n : ℕ) :
    exercise24N a (Real.sqrt a) n = Real.sqrt a ∧
    exercise24M a (Real.sqrt a) n = Real.sqrt a := by
  have hf := exercise24_fixed_points ha (Real.sqrt_pos.mpr ha)
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [exercise24N_succ, exercise24M_succ, ih.1, ih.2]
    exact ⟨hf.1.mpr rfl, hf.2.mpr rfl⟩

/-- The derivatives are genuine derivatives on the positive domain. -/
theorem exercise24_derivatives {a x : ℝ} (hx : 0 < x) :
    HasDerivAt (exercise24Newton a) ((1-a/x^2)/2) x ∧
    HasDerivAt (exercise24Mobius a) ((1-a)/(1+x)^2) x := by
  constructor
  · convert ((hasDerivAt_id x).add ((hasDerivAt_const x a).div
      (hasDerivAt_id x) hx.ne')).div_const 2 using 1
    · rfl
    · dsimp; ring
  · convert ((hasDerivAt_const x a).add (hasDerivAt_id x)).div
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))
      (by change 1+x ≠ 0; positivity) using 1
    · rfl
    · dsimp; ring

theorem exercise24_derivatives_at_root {a : ℝ} (ha : 0 < a) :
    HasDerivAt (exercise24Newton a) 0 (Real.sqrt a) ∧
    HasDerivAt (exercise24Mobius a) ((1-Real.sqrt a)/(1+Real.sqrt a)) (Real.sqrt a) := by
  have hr := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  obtain ⟨hn, hm⟩ := exercise24_derivatives (a := a) hr
  constructor
  · convert hn using 1
    rw [hs, div_self ha.ne']; norm_num
  · convert hm using 1
    field_simp
    nlinarith

/-- Exact error identities: quadratic for Newton, linear for the Möbius map. -/
theorem exercise24_error {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    exercise24Newton a x - Real.sqrt a = (x-Real.sqrt a)^2/(2*x) ∧
    exercise24Mobius a x - Real.sqrt a =
      (1-Real.sqrt a)*(x-Real.sqrt a)/(1+x) := by
  constructor
  · have := Real.sq_sqrt ha.le
    dsimp [exercise24Newton]
    field_simp
    nlinarith
  · exact Chapter03.exercise17_error_identity a x ha.le hx

/-- A nonfixed positive Newton start goes strictly above the root in one step. -/
theorem exercise24_newton_overshoot {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hne : x ≠ Real.sqrt a) : Real.sqrt a < exercise24Newton a x := by
  have he := (exercise24_error ha hx).1
  have := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) (by positivity : 0 < 2*x)
  linarith

theorem exercise24N_tail (a x : ℝ) (n : ℕ) :
    exercise24N a x (n+1) = exercise24N a (exercise24Newton a x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exercise24N_succ a x (n+1), ih, exercise24N_succ]

/-- Convergence for every positive start, including the fixed start. -/
theorem exercise24_newton_convergence {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (exercise24N a x) atTop (𝓝 (Real.sqrt a)) := by
  by_cases h : x = Real.sqrt a
  · subst x
    have he : exercise24N a (Real.sqrt a) = fun _ => Real.sqrt a :=
      funext (fun n => (exercise24_constant ha n).1)
    rw [he]
    exact tendsto_const_nhds
  have ht := Chapter03.exercise16_limit a (exercise24Newton a x) ha
    (exercise24_newton_overshoot ha hx h)
  apply (tendsto_add_atTop_iff_nat 1).mp
  rw [show (fun n => exercise24N a x (n+1)) = exercise24N a (exercise24Newton a x) from
    funext (exercise24N_tail a x)]
  exact ht

/-- Newton's actual quadratic error constant, for every nonfixed positive start. -/
theorem exercise24_newton_rates {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hne : x ≠ Real.sqrt a) :
    Tendsto (fun n => (exercise24N a x (n+1)-Real.sqrt a) /
      (exercise24N a x n-Real.sqrt a)^2) atTop (𝓝 (1/(2*Real.sqrt a))) ∧
    Tendsto (fun n => (exercise24N a x (n+1)-Real.sqrt a) /
      (exercise24N a x n-Real.sqrt a)) atTop (𝓝 0) := by
  have hb : ∀ n, exercise24N a x n ≠ Real.sqrt a := by
    intro n
    cases n with
    | zero => exact hne
    | succ n =>
      rw [exercise24N_tail]
      exact ne_of_gt (Chapter03.exercise16_above a _ ha (exercise24_newton_overshoot ha hx hne) n)
  have ht := exercise24_newton_convergence ha hx
  have hid : ∀ n, (exercise24N a x (n+1)-Real.sqrt a) /
      (exercise24N a x n-Real.sqrt a)^2 = 1/(2*exercise24N a x n) := by
    intro n
    rw [exercise24N_succ, (exercise24_error ha (exercise24_positive ha hx n).1).1]
    field_simp [sub_ne_zero.mpr (hb n)]
  have hid' : ∀ n, (exercise24N a x (n+1)-Real.sqrt a) /
      (exercise24N a x n-Real.sqrt a) =
      (exercise24N a x n-Real.sqrt a)/(2*exercise24N a x n) := by
    intro n
    rw [exercise24N_succ, (exercise24_error ha (exercise24_positive ha hx n).1).1]
    field_simp [sub_ne_zero.mpr (hb n)]
  constructor
  · simp_rw [hid]
    exact tendsto_const_nhds.div (ht.const_mul 2) (by positivity)
  · simp_rw [hid']
    convert (ht.sub_const (Real.sqrt a)).div (ht.const_mul 2) (by positivity) using 1
    simp

/-- The Möbius cross ratio is exactly geometric for every positive start. -/
theorem exercise24_mobius_cross_ratio {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (n : ℕ) :
    (exercise24M a x n-Real.sqrt a)/(exercise24M a x n+Real.sqrt a) =
      ((1-Real.sqrt a)/(1+Real.sqrt a))^n * ((x-Real.sqrt a)/(x+Real.sqrt a)) := by
  have hr := Real.sqrt_pos.mpr ha
  induction n with
  | zero => simp only [exercise24M_zero, pow_zero, one_mul]
  | succ n ih =>
    have hy := (exercise24_positive ha hx n).2
    have hs := Real.sq_sqrt ha.le
    have hstep : (exercise24Mobius a (exercise24M a x n)-Real.sqrt a) /
        (exercise24Mobius a (exercise24M a x n)+Real.sqrt a) =
        ((1-Real.sqrt a)/(1+Real.sqrt a)) *
        ((exercise24M a x n-Real.sqrt a)/(exercise24M a x n+Real.sqrt a)) := by
      have hd : exercise24Mobius a (exercise24M a x n)+Real.sqrt a ≠ 0 := by
        dsimp [exercise24Mobius]; positivity
      dsimp [exercise24Mobius] at *
      field_simp
      linear_combination -2 * Real.sqrt a * (1 + exercise24M a x n) * hs
    rw [exercise24M_succ, hstep, ih, pow_succ]
    ring

theorem exercise24_multiplier {a : ℝ} (ha : 0 < a) :
    |(1-Real.sqrt a)/(1+Real.sqrt a)| < 1 := by
  have hr := Real.sqrt_pos.mpr ha
  rw [abs_lt]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 1+Real.sqrt a)).mpr
    linarith
  · apply (div_lt_one (by positivity : 0 < 1+Real.sqrt a)).mpr
    linarith

/-- Convergence of the slower iteration on the entire positive domain. -/
theorem exercise24_mobius_convergence {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Tendsto (exercise24M a x) atTop (𝓝 (Real.sqrt a)) := by
  have hr := Real.sqrt_pos.mpr ha
  have ht : Tendsto (fun n => (exercise24M a x n-Real.sqrt a)/
      (exercise24M a x n+Real.sqrt a)) atTop (𝓝 0) := by
    simp_rw [exercise24_mobius_cross_ratio ha hx]
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (exercise24_multiplier ha)).mul_const
      ((x-Real.sqrt a)/(x+Real.sqrt a))
  have hl := ((ht.const_add 1).const_mul (Real.sqrt a)).div
    (ht.const_sub 1) (by norm_num : (1:ℝ)-0 ≠ 0)
  have hid : ∀ n, Real.sqrt a * (1+(exercise24M a x n-Real.sqrt a)/
      (exercise24M a x n+Real.sqrt a)) /
      (1-(exercise24M a x n-Real.sqrt a)/(exercise24M a x n+Real.sqrt a)) =
      exercise24M a x n := by
    intro n
    have hy := (exercise24_positive ha hx n).2
    have hd : 1-(exercise24M a x n-Real.sqrt a)/(exercise24M a x n+Real.sqrt a) ≠ 0 := by
      rw [ne_eq, sub_eq_zero, eq_comm, div_eq_iff (by positivity)]
      linarith
    field_simp [hr.ne']
    ring
  have hl' : Tendsto (fun n => Real.sqrt a * (1+(exercise24M a x n-Real.sqrt a)/
      (exercise24M a x n+Real.sqrt a)) /
      (1-(exercise24M a x n-Real.sqrt a)/(exercise24M a x n+Real.sqrt a))) atTop
      (𝓝 (Real.sqrt a)) := by convert hl using 1; simp
  simpa only [hid] using hl'

/-- A nonfixed Möbius orbit never reaches the root when `a ≠ 1`. -/
theorem exercise24_mobius_nonfixed {a x : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (hx : 0 < x) (hne : x ≠ Real.sqrt a) (n : ℕ) :
    exercise24M a x n ≠ Real.sqrt a := by
  induction n with
  | zero => exact hne
  | succ n ih =>
    have he := (exercise24_error ha (exercise24_positive ha hx n).2).2
    have hh : 1-Real.sqrt a ≠ 0 := by
      intro h
      exact ha1 (Real.sqrt_eq_one.mp (by linarith))
    rw [exercise24M_succ, ← sub_ne_zero]
    rw [he]
    exact div_ne_zero (mul_ne_zero hh (sub_ne_zero.mpr ih)) (by
      have := (exercise24_positive ha hx n).2; positivity)

/-- Actual signed and absolute linear rates, not only a derivative heuristic. -/
theorem exercise24_mobius_rates {a x : ℝ} (ha : 0 < a) (ha1 : a ≠ 1)
    (hx : 0 < x) (hne : x ≠ Real.sqrt a) :
    Tendsto (fun n => (exercise24M a x (n+1)-Real.sqrt a) /
      (exercise24M a x n-Real.sqrt a)) atTop (𝓝 ((1-Real.sqrt a)/(1+Real.sqrt a))) ∧
    Tendsto (fun n => |exercise24M a x (n+1)-Real.sqrt a| /
      |exercise24M a x n-Real.sqrt a|) atTop (𝓝 (|(1-Real.sqrt a)/(1+Real.sqrt a)|)) ∧
    0 < |(1-Real.sqrt a)/(1+Real.sqrt a)| ∧
    |(1-Real.sqrt a)/(1+Real.sqrt a)| < 1 := by
  have hr := Real.sqrt_pos.mpr ha
  have hid : ∀ n, (exercise24M a x (n+1)-Real.sqrt a) /
      (exercise24M a x n-Real.sqrt a) = (1-Real.sqrt a)/(1+exercise24M a x n) := by
    intro n
    rw [exercise24M_succ, (exercise24_error ha (exercise24_positive ha hx n).2).2]
    field_simp [sub_ne_zero.mpr (exercise24_mobius_nonfixed ha ha1 hx hne n)]
  have ht : Tendsto (fun n => (exercise24M a x (n+1)-Real.sqrt a) /
      (exercise24M a x n-Real.sqrt a)) atTop (𝓝 ((1-Real.sqrt a)/(1+Real.sqrt a))) := by
    simp_rw [hid]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (exercise24_mobius_convergence ha hx))
      (by positivity)
  refine ⟨ht, by simpa only [abs_div] using ht.abs, ?_, exercise24_multiplier ha⟩
  apply abs_pos.mpr
  apply div_ne_zero
  · intro h
    exact ha1 (Real.sqrt_eq_one.mp (by linarith))
  · positivity

/-- The sign change in the rate distinguishes alternating and monotone cobwebs. -/
theorem exercise24_rate_signs {a : ℝ} (ha : 0 < a) :
    (1 < a → -1 < (1-Real.sqrt a)/(1+Real.sqrt a) ∧
      (1-Real.sqrt a)/(1+Real.sqrt a) < 0) ∧
    (a < 1 → 0 < (1-Real.sqrt a)/(1+Real.sqrt a) ∧
      (1-Real.sqrt a)/(1+Real.sqrt a) < 1) := by
  have hr := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have hb := abs_lt.mp (exercise24_multiplier ha)
  constructor
  · intro h
    exact ⟨hb.1, div_neg_of_neg_of_pos (by nlinarith) (by positivity)⟩
  · intro h
    exact ⟨div_pos (by nlinarith) (by positivity), hb.2⟩

/-- Newton iterates decrease above the root. A positive start below the root
overshoots it at the first step, then decreases. A root start stays constant. -/
theorem exercise24_newton_diagrams {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (Real.sqrt a < x → StrictAnti (exercise24N a x) ∧
      ∀ n, Real.sqrt a < exercise24N a x n) ∧
    (x < Real.sqrt a → x < exercise24N a x 1 ∧
      StrictAnti (fun n => exercise24N a x (n+1)) ∧
      ∀ n, Real.sqrt a < exercise24N a x (n+1)) ∧
    (x = Real.sqrt a → ∀ n, exercise24N a x n = Real.sqrt a) := by
  refine ⟨fun h => ⟨Chapter03.exercise16_monotone a x ha h,
    Chapter03.exercise16_above a x ha h⟩, ?_, ?_⟩
  · intro h
    have ho := exercise24_newton_overshoot ha hx h.ne
    have he : (fun n => exercise24N a x (n+1)) = exercise24N a (exercise24Newton a x) :=
      funext (exercise24N_tail a x)
    refine ⟨h.trans ho, ?_, ?_⟩
    · rw [he]
      exact Chapter03.exercise16_monotone a _ ha ho
    · intro n
      rw [exercise24N_tail]
      exact Chapter03.exercise16_above a _ ha ho n
  · rintro rfl n
    exact (exercise24_constant ha n).1

/-- For `a > 1`, each nonroot scalar iterate moves to the other side of
`sqrt a`. This does not assert that a planar cobweb segment contains the
fixed point. -/
theorem exercise24_mobius_flip {a y : ℝ} (ha : 1 < a) (hy : 0 < y) :
    (Real.sqrt a < y → exercise24Mobius a y < Real.sqrt a) ∧
    (y < Real.sqrt a → Real.sqrt a < exercise24Mobius a y) := by
  have hr := Chapter03.exercise17_root a ha
  have he := (exercise24_error (by linarith : 0 < a) hy).2
  constructor
  · intro h
    have : (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) (by positivity)
    linarith
  · intro h
    have : 0 < (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) :=
      div_pos (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by positivity)
    linarith

/-- Every two Möbius steps move towards the root when `a > 1`. -/
theorem exercise24_mobius_two_step {a y : ℝ} (ha : 1 < a) (hy : 0 < y) :
    (Real.sqrt a < y → exercise24Mobius a (exercise24Mobius a y) < y) ∧
    (y < Real.sqrt a → y < exercise24Mobius a (exercise24Mobius a y)) := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ a)
  have hr := Real.sqrt_nonneg a
  have he := Chapter03.exercise17_two_step a y ha hy
  change exercise24Mobius a (exercise24Mobius a y) - y =
    2*(a-y^2)/(a+1+2*y) at he
  constructor
  · intro h
    have : 2*(a-y^2)/(a+1+2*y) < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) (by linarith)
    linarith
  · intro h
    have : 0 < 2*(a-y^2)/(a+1+2*y) := div_pos (by nlinarith) (by linarith)
    linarith

/-- Complete alternating-cobweb classification for `a > 1`, for all positive starts.
Even indices here correspond to odd source indices. -/
theorem exercise24_greater_than_one_diagrams {a x : ℝ} (ha : 1 < a) (hx : 0 < x) :
    (Real.sqrt a < x →
      (∀ n, Real.sqrt a < exercise24M a x (2*n) ∧
        exercise24M a x (2*n+1) < Real.sqrt a) ∧
      StrictAnti (fun n => exercise24M a x (2*n)) ∧
      StrictMono (fun n => exercise24M a x (2*n+1))) ∧
    (x < Real.sqrt a →
      (∀ n, exercise24M a x (2*n) < Real.sqrt a ∧
        Real.sqrt a < exercise24M a x (2*n+1)) ∧
      StrictMono (fun n => exercise24M a x (2*n)) ∧
      StrictAnti (fun n => exercise24M a x (2*n+1))) ∧
    (x = Real.sqrt a → ∀ n, exercise24M a x n = Real.sqrt a) := by
  have ha0 : 0 < a := by linarith
  refine ⟨fun h => ⟨Chapter03.exercise17_alternation a x ha h,
    Chapter03.exercise17_odd_decreasing a x ha h,
    Chapter03.exercise17_even_increasing a x ha h⟩, ?_, ?_⟩
  · intro h
    have halt : ∀ n, exercise24M a x (2*n) < Real.sqrt a ∧
        Real.sqrt a < exercise24M a x (2*n+1) := by
      intro n
      induction n with
      | zero => exact ⟨h, (exercise24_mobius_flip ha hx).2 h⟩
      | succ n ih =>
        have h1 := (exercise24_mobius_flip ha (exercise24_positive ha0 hx (2*n+1)).2).1 ih.2
        have h2 := (exercise24_mobius_flip ha (exercise24_positive ha0 hx (2*n+2)).2).2 h1
        change exercise24M a x (2*n+2) < Real.sqrt a at h1
        change Real.sqrt a < exercise24M a x (2*n+3) at h2
        simpa only [Nat.mul_succ, Nat.add_assoc] using And.intro h1 h2
    refine ⟨halt, ?_, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro n
      have h := (exercise24_mobius_two_step ha (exercise24_positive ha0 hx (2*n)).2).2 (halt n).1
      change exercise24M a x (2*n) < exercise24M a x ((2*n+1)+1) at h
      convert h using 1
    · apply strictAnti_nat_of_succ_lt
      intro n
      have h := (exercise24_mobius_two_step ha (exercise24_positive ha0 hx (2*n+1)).2).1 (halt n).2
      change exercise24M a x (((2*n+1)+1)+1) < exercise24M a x (2*n+1) at h
      convert h using 1
  · rintro rfl n
    exact (exercise24_constant ha0 n).2

/-- For `0 < a < 1` the Möbius map preserves the side of the root,
and each step moves strictly towards it unless the start is fixed. -/
theorem exercise24_mobius_small_step {a y : ℝ} (ha : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    (Real.sqrt a < y → Real.sqrt a < exercise24Mobius a y ∧ exercise24Mobius a y < y) ∧
    (y < Real.sqrt a → y < exercise24Mobius a y ∧ exercise24Mobius a y < Real.sqrt a) := by
  have hr := Real.sqrt_pos.mpr ha
  have hs := Real.sq_sqrt ha.le
  have hr1 : Real.sqrt a < 1 := by nlinarith
  have he := (exercise24_error ha hy).2
  constructor
  · intro h
    constructor
    · have : 0 < (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) :=
        div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
      linarith
    · change (a+y)/(1+y) < y
      apply (div_lt_iff₀ (by positivity : 0 < 1+y)).mpr
      nlinarith
  · intro h
    constructor
    · change y < (a+y)/(1+y)
      apply (lt_div_iff₀ (by positivity : 0 < 1+y)).mpr
      nlinarith
    · have : (1-Real.sqrt a)*(y-Real.sqrt a)/(1+y) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by positivity)
      linarith

/-- Complete nonalternating-cobweb classification for `0 < a < 1`. -/
theorem exercise24_less_than_one_diagrams {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    (Real.sqrt a < x → StrictAnti (exercise24M a x) ∧
      ∀ n, Real.sqrt a < exercise24M a x n) ∧
    (x < Real.sqrt a → StrictMono (exercise24M a x) ∧
      ∀ n, exercise24M a x n < Real.sqrt a) ∧
    (x = Real.sqrt a → ∀ n, exercise24M a x n = Real.sqrt a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hb : ∀ n, Real.sqrt a < exercise24M a x n := by
      intro n
      induction n with
      | zero => exact h
      | succ n ih => exact (exercise24_mobius_small_step ha ha1
          (exercise24_positive ha hx n).2).1 ih |>.1
    refine ⟨strictAnti_nat_of_succ_lt (fun n => ?_), hb⟩
    exact (exercise24_mobius_small_step ha ha1 (exercise24_positive ha hx n).2).1 (hb n) |>.2
  · intro h
    have hb : ∀ n, exercise24M a x n < Real.sqrt a := by
      intro n
      induction n with
      | zero => exact h
      | succ n ih => exact (exercise24_mobius_small_step ha ha1
          (exercise24_positive ha hx n).2).2 ih |>.2
    refine ⟨strictMono_nat_of_lt_succ (fun n => ?_), hb⟩
    exact (exercise24_mobius_small_step ha ha1 (exercise24_positive ha hx n).2).2 (hb n) |>.1
  · rintro rfl n
    exact (exercise24_constant ha n).2

/-- Exact horizontal and vertical cobweb segments for both iterations.
Together with the preceding order classifications these specify both diagrams. -/
theorem exercise24_diagram_segments (a x : ℝ) (n : ℕ) (u : ℕ → ℝ)
    (hu : u = exercise24N a x ∨ u = exercise24M a x) :
    segment ℝ (u n, u (n+1)) (u (n+1), u (n+1)) =
      {p | p.1 ∈ uIcc (u n) (u (n+1)) ∧ p.2 = u (n+1)} ∧
    segment ℝ (u (n+1), u (n+1)) (u (n+1), u (n+2)) =
      {p | p.1 = u (n+1) ∧ p.2 ∈ uIcc (u (n+1)) (u (n+2))} := by
  rcases hu with rfl | rfl
  · simpa only [exercise22Graph, exercise22Diagonal, (exercise24_orbits a x _).1] using
      exercise22_d_segments (exercise24Newton a) x n
  · simpa only [exercise22Graph, exercise22Diagonal, (exercise24_orbits a x _).2] using
      exercise22_d_segments (exercise24Mobius a) x n

end Rudin.Chapter05
