module

public import Mathlib

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace Rudin.Chapter03

/-- Index zero is Rudin's first term. -/
def exercise16Seq (a x : ℝ) : ℕ → ℝ :=
  Nat.rec x (fun _ y => (y + a / y) / 2)

 theorem exercise16_step (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) :
    Real.sqrt a < (x + a / x) / 2 ∧ (x + a / x) / 2 < x ∧
    (x + a / x) / 2 - Real.sqrt a = (x - Real.sqrt a)^2 / (2*x) := by
  have hr := Real.sqrt_pos.2 ha
  have hs := Real.sq_sqrt ha.le
  have hxp : 0 < x := hr.trans hx
  have he : 0 < (x - Real.sqrt a)^2 := sq_pos_of_pos (sub_pos.2 hx)
  have hid : (x + a / x) / 2 - Real.sqrt a = (x - Real.sqrt a)^2 / (2*x) := by
    field_simp
    nlinarith
  refine ⟨?_, ?_, hid⟩
  · have := div_pos he (by positivity : 0 < 2*x)
    linarith
  · have hsq : a < x*x := by nlinarith
    have : a / x < x := (div_lt_iff₀ hxp).2 hsq
    linarith

 theorem exercise16_above (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    Real.sqrt a < exercise16Seq a x n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact (exercise16_step a _ ha ih).1

 theorem exercise16_monotone (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) :
    StrictAnti (exercise16Seq a x) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  exact (exercise16_step a _ ha (exercise16_above a x ha hx n)).2.1

 theorem exercise16_limit (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) :
    Tendsto (exercise16Seq a x) atTop (𝓝 (Real.sqrt a)) := by
  have hlower : ∀ n, Real.sqrt a ≤ exercise16Seq a x n :=
    fun n => (exercise16_above a x ha hx n).le
  have hb : BddBelow (Set.range (exercise16Seq a x)) := ⟨Real.sqrt a, by rintro _ ⟨n, rfl⟩; exact hlower n⟩
  have ht := tendsto_atTop_ciInf (exercise16_monotone a x ha hx).antitone hb
  have hr := Real.sqrt_pos.2 ha
  have hL : Real.sqrt a ≤ ⨅ n, exercise16Seq a x n := le_ciInf hlower
  have hLp : 0 < ⨅ n, exercise16Seq a x n := hr.trans_le hL
  have hs : Tendsto (fun n => exercise16Seq a x (n+1)) atTop
      (𝓝 (( (⨅ n, exercise16Seq a x n) + a / (⨅ n, exercise16Seq a x n)) / 2)) :=
    (ht.add (tendsto_const_nhds.div ht hLp.ne')).div_const 2
  have he := tendsto_nhds_unique ((tendsto_add_atTop_iff_nat 1).2 ht) hs
  have heq : (⨅ n, exercise16Seq a x n)^2 = a := by
    field_simp at he
    nlinarith
  have hroot : (⨅ n, exercise16Seq a x n) = Real.sqrt a := by
    have := Real.sq_sqrt ha.le
    nlinarith
  simpa [hroot] using ht

 theorem exercise16_error_step (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    exercise16Seq a x (n+1) - Real.sqrt a =
      (exercise16Seq a x n - Real.sqrt a)^2 / (2 * exercise16Seq a x n) ∧
    (exercise16Seq a x n - Real.sqrt a)^2 / (2 * exercise16Seq a x n) <
      (exercise16Seq a x n - Real.sqrt a)^2 / (2 * Real.sqrt a) := by
  have hn := exercise16_above a x ha hx n
  refine ⟨(exercise16_step a _ ha hn).2.2, ?_⟩
  exact div_lt_div_of_pos_left (sq_pos_of_pos (sub_pos.2 hn))
    (by positivity : 0 < 2 * Real.sqrt a) (by linarith)

 theorem exercise16_error_bound (a x : ℝ) (ha : 0 < a) (hx : Real.sqrt a < x)
    (n : ℕ) (hn : 1 ≤ n) :
    exercise16Seq a x n - Real.sqrt a <
      (2 * Real.sqrt a) * ((x - Real.sqrt a) / (2 * Real.sqrt a))^(2^n) := by
  have hb : 0 < 2 * Real.sqrt a := by positivity
  have hq : 0 < (x - Real.sqrt a) / (2 * Real.sqrt a) := div_pos (sub_pos.2 hx) hb
  have hbase : exercise16Seq a x 1 - Real.sqrt a <
      (2 * Real.sqrt a) * ((x - Real.sqrt a) / (2 * Real.sqrt a))^(2^1) := by
    have h := (exercise16_error_step a x ha hx 0)
    simp only [exercise16Seq, pow_one] at h ⊢
    calc
      _ < (x - Real.sqrt a)^2 / (2 * Real.sqrt a) := h.1 ▸ h.2
      _ = _ := by field_simp
  induction n, hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
    have he := exercise16_error_step a x ha hx n
    have hp : 0 < exercise16Seq a x n - Real.sqrt a :=
      sub_pos.2 (exercise16_above a x ha hx n)
    calc
      _ < (exercise16Seq a x n - Real.sqrt a)^2 / (2 * Real.sqrt a) := he.1 ▸ he.2
      _ < ((2 * Real.sqrt a) * ((x - Real.sqrt a) / (2 * Real.sqrt a))^(2^n))^2 /
          (2 * Real.sqrt a) := by
        apply (div_lt_div_iff_of_pos_right hb).2
        nlinarith
      _ = _ := by rw [show 2^(n+1) = 2^n * 2 by omega, pow_mul]; field_simp

 theorem exercise16_initial_bound :
    (2 - Real.sqrt 3) / (2 * Real.sqrt 3) < (1:ℝ)/10 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3:ℝ)
  apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.sqrt (3:ℝ))).2
  nlinarith

 theorem exercise16_numerical :
    exercise16Seq 3 2 4 - Real.sqrt 3 < 4 / (10:ℝ)^16 ∧
    exercise16Seq 3 2 5 - Real.sqrt 3 < 4 / (10:ℝ)^32 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp := Real.sqrt_nonneg (3:ℝ)
  have hx : Real.sqrt (3:ℝ) < 2 := by nlinarith
  have hq : 0 ≤ (2 - Real.sqrt 3) / (2 * Real.sqrt 3) := by positivity
  have hb : 0 < 2 * Real.sqrt (3:ℝ) := by positivity
  have hsmall : 2 * Real.sqrt (3:ℝ) < 4 := by linarith
  have aux : ∀ n : ℕ, 1 ≤ n → exercise16Seq 3 2 n - Real.sqrt 3 <
      4 * ((1:ℝ)/10)^(2^n) := by
    intro n hn
    calc
      _ < _ := exercise16_error_bound 3 2 (by norm_num) hx n hn
      _ ≤ (2 * Real.sqrt 3) * ((1:ℝ)/10)^(2^n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq exercise16_initial_bound.le _) hb.le
      _ < _ := mul_lt_mul_of_pos_right hsmall (by positivity)
  constructor
  · convert aux 4 (by omega) using 1; norm_num
  · convert aux 5 (by omega) using 1; norm_num

 theorem exercise16_fifth_bound :
    exercise16Seq 3 2 4 - Real.sqrt 3 < 4 / (10:ℝ)^16 := exercise16_numerical.1

 theorem exercise16_sixth_bound :
    exercise16Seq 3 2 5 - Real.sqrt 3 < 4 / (10:ℝ)^32 := exercise16_numerical.2

end Rudin.Chapter03
