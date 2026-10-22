module

public import Mathlib

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace Rudin.Chapter03

/-- Newton's update for a positive integer exponent. -/
def exercise18Update (p : ℕ) (a y : ℝ) : ℝ :=
  (((p:ℝ)-1)*y + a/y^(p-1))/(p:ℝ)

/-- Index zero is Rudin's first term. -/
def exercise18Seq (p : ℕ) (a x : ℝ) : ℕ → ℝ :=
  Nat.rec x (fun _ y => exercise18Update p a y)

@[simp] theorem exercise18Seq_zero (p : ℕ) (a x : ℝ) : exercise18Seq p a x 0 = x := rfl

@[simp] theorem exercise18Seq_succ (p : ℕ) (a x : ℝ) (n : ℕ) :
    exercise18Seq p a x (n + 1) = exercise18Update p a (exercise18Seq p a x n) := rfl

/-- The positive root, not a replacement for the inherited starting bound. -/
def exercise18Root (p : ℕ) (a : ℝ) : ℝ := a ^ ((p:ℝ)⁻¹)

 theorem exercise18_root_spec (p : ℕ) (hp : 1 ≤ p) (a : ℝ) (ha : 0 < a) :
    0 < exercise18Root p a ∧ (exercise18Root p a)^p = a :=
  ⟨Real.rpow_pos_of_pos ha _, Real.rpow_inv_natCast_pow ha.le (by omega)⟩

 theorem exercise18_source_update (p : ℕ) (hp : 1 ≤ p) (a y : ℝ) (_hy : 0 < y) :
    exercise18Update p a y = ((p:ℝ)-1)/(p:ℝ)*y +
      (a/(p:ℝ))*y^(-(p:ℤ)+1) := by
  have he : -(p:ℤ)+1 = -((p-1:ℕ):ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  unfold exercise18Update
  ring

 theorem exercise18_update_positive (p : ℕ) (hp : 1 ≤ p) (a y : ℝ)
    (ha : 0 < a) (hy : 0 < y) : 0 < exercise18Update p a y := by
  have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpm : (0:ℝ) ≤ (p:ℝ)-1 := by
    have : (1:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  exact div_pos (add_pos_of_nonneg_of_pos (mul_nonneg hpm hy.le) (by positivity)) hp'

 theorem exercise18_positive (p : ℕ) (hp : 1 ≤ p) (a x : ℝ)
    (ha : 0 < a) (hx : 0 < x) (n : ℕ) : 0 < exercise18Seq p a x n := by
  induction n with
  | zero => exact hx
  | succ n ih => exact exercise18_update_positive p hp a _ ha ih

/-- Under exactly the inherited hypotheses all powers and denominators are defined. -/
 theorem exercise18_well_defined (p : ℕ) (hp : 1 ≤ p) (a x : ℝ)
    (ha : 0 < a) (hx : Real.sqrt a < x) (n : ℕ) :
    0 < exercise18Seq p a x n ∧ (p:ℝ) ≠ 0 ∧
      (exercise18Seq p a x n)^(p-1) ≠ 0 := by
  have h := exercise18_positive p hp a x ha ((Real.sqrt_pos.2 ha).trans hx) n
  exact ⟨h, by exact_mod_cast (show p ≠ 0 by omega), pow_ne_zero _ h.ne'⟩

 theorem exercise18_unit_exponent (a x : ℝ) (n : ℕ) : exercise18Seq 1 a x (n+1) = a := by
  simp [exercise18Seq_succ, exercise18Update]

 theorem exercise18_unit_limit (a x : ℝ) :
    Tendsto (exercise18Seq 1 a x) atTop (𝓝 a) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  simp only [exercise18_unit_exponent]
  exact tendsto_const_nhds

 theorem exercise18_difference (p : ℕ) (hp : 1 ≤ p) (a y : ℝ) (hy : 0 < y) :
    exercise18Update p a y - y = (a-y^p)/((p:ℝ)*y^(p-1)) := by
  have hpow : y^p = y^(p-1)*y := by rw [← pow_succ, Nat.sub_add_cancel hp]
  unfold exercise18Update
  field_simp
  rw [hpow]
  ring

 theorem exercise18_fixed (p : ℕ) (hp : 1 ≤ p) (r : ℝ) (hr : 0 < r) :
    exercise18Update p (r^p) r = r := by
  have := exercise18_difference p hp (r^p) r hr
  have he : exercise18Update p (r^p) r - r = 0 := by simpa using this
  linarith

/-- The Bernoulli remainder is strictly positive off the root. -/
 theorem exercise18_above_step (p : ℕ) (hp : 2 ≤ p) (r y : ℝ)
    (hr : 0 < r) (hy : 0 < y) (hne : y ≠ r) :
    r < exercise18Update p (r^p) y := by
  have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpow : y^p = y^(p-1)*y := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hbern := one_add_mul_self_lt_rpow_one_add
    (s := r/y-1) (by have := div_pos hr hy; linarith)
    (by intro h; apply hne; have := (div_eq_one_iff_eq hy.ne').1 (by linarith : r/y = 1); exact this.symm)
    (p := (p:ℝ)) (by exact_mod_cast (show 1 < p by omega))
  rw [show 1+(r/y-1) = r/y by ring, Real.rpow_natCast] at hbern
  have hid : exercise18Update p (r^p) y - r =
      (y/(p:ℝ))*((r/y)^p - 1 - (p:ℝ)*(r/y-1)) := by
    unfold exercise18Update
    rw [div_pow, hpow]
    field_simp
    ring
  have hpos : 0 < (y/(p:ℝ))*((r/y)^p - 1 - (p:ℝ)*(r/y-1)) :=
    mul_pos (div_pos hy hp') (by linarith)
  linarith

/-- Equality in the lower bound is possible exactly at the root. -/
theorem exercise18_step_eq_root_iff (p : ℕ) (hp : 2 ≤ p) (r y : ℝ)
    (hr : 0 < r) (hy : 0 < y) : exercise18Update p (r^p) y = r ↔ y = r := by
  constructor
  · intro he
    by_contra hn
    have := exercise18_above_step p hp r y hr hy hn
    linarith
  · rintro rfl
    exact exercise18_fixed p (by omega) y hr

 theorem exercise18_step_classification (p : ℕ) (hp : 2 ≤ p) (r y : ℝ)
    (hr : 0 < r) (hy : 0 < y) :
    (y < r → y < r ∧ r < exercise18Update p (r^p) y) ∧
    (y = r → exercise18Update p (r^p) y = r) ∧
    (r < y → r < exercise18Update p (r^p) y ∧ exercise18Update p (r^p) y < y) := by
  refine ⟨fun h => ⟨h, exercise18_above_step p hp r y hr hy (ne_of_lt h)⟩,
    ?_, ?_⟩
  · intro h
    rw [h]
    exact exercise18_fixed p (by omega) r hr
  · intro h
    refine ⟨exercise18_above_step p hp r y hr hy (ne_of_gt h), ?_⟩
    have hd := exercise18_difference p (by omega) (r^p) y hy
    have hpow := pow_lt_pow_left₀ h hr.le (show p ≠ 0 by omega)
    have hneg : (r^p-y^p)/((p:ℝ)*y^(p-1)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith

/-- Starting above the root gives strict descent and preserves that strict bound. -/
 theorem exercise18_above (p : ℕ) (hp : 2 ≤ p) (r x : ℝ)
    (hr : 0 < r) (hx : r < x) :
    (∀ n, r < exercise18Seq p (r^p) x n) ∧ StrictAnti (exercise18Seq p (r^p) x) := by
  have hb : ∀ n, r < exercise18Seq p (r^p) x n := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact ((exercise18_step_classification p hp r _ hr (hr.trans ih)).2.2 ih).1
  refine ⟨hb, strictAnti_nat_of_succ_lt (fun n => ?_)⟩
  exact ((exercise18_step_classification p hp r _ hr (hr.trans (hb n))).2.2 (hb n)).2

 theorem exercise18_constant (p : ℕ) (hp : 1 ≤ p) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    exercise18Seq p (r^p) r n = r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [exercise18Seq_succ, ih, exercise18_fixed p hp r hr]

 theorem exercise18_shift (p k n : ℕ) (a x : ℝ) :
    exercise18Seq p a (exercise18Seq p a x k) n = exercise18Seq p a x (n+k) := by
  induction n with
  | zero => simp only [exercise18Seq_zero, Nat.zero_add]
  | succ n ih => simp only [Nat.succ_add, exercise18Seq_succ, ih]

/-- A geometric upper bound suffices to prove convergence; it is not an assertion of exact order. -/
 theorem exercise18_contraction (p : ℕ) (hp : 2 ≤ p) (r y : ℝ)
    (hr : 0 < r) (hy : r ≤ y) :
    exercise18Update p (r^p) y - r ≤ (((p:ℝ)-1)/(p:ℝ))*(y-r) := by
  have hyp : 0 < y := hr.trans_le hy
  have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpow : r^p = r^(p-1)*r := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hpowle := pow_le_pow_left₀ hr.le hy (p-1)
  have hdiv : r^p/y^(p-1) ≤ r := by
    apply (div_le_iff₀ (by positivity : 0 < y^(p-1))).2
    rw [hpow]
    nlinarith
  unfold exercise18Update
  apply (sub_le_iff_le_add).2
  apply (div_le_iff₀ hp').2
  have he : ((((p:ℝ)-1)/(p:ℝ))*(y-r)+r)*(p:ℝ) = ((p:ℝ)-1)*y+r := by
    field_simp
    ring
  rw [he]
  linarith

 theorem exercise18_limit_above (p : ℕ) (hp : 2 ≤ p) (r x : ℝ)
    (hr : 0 < r) (hx : r < x) :
    Tendsto (exercise18Seq p (r^p) x) atTop (𝓝 r) := by
  let c : ℝ := ((p:ℝ)-1)/(p:ℝ)
  have hp' : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1:ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c < 1 := by dsimp [c]; apply (div_lt_one hp').2; linarith
  have hb := (exercise18_above p hp r x hr hx).1
  have he : ∀ n, exercise18Seq p (r^p) x n - r ≤ c^n*(x-r) := by
    intro n
    induction n with
    | zero => simp [exercise18Seq]
    | succ n ih =>
      calc
        _ ≤ c*(exercise18Seq p (r^p) x n-r) :=
          exercise18_contraction p hp r _ hr (hb n).le
        _ ≤ c*(c^n*(x-r)) := mul_le_mul_of_nonneg_left ih hc
        _ = _ := by rw [pow_succ]; ring
  have ht : Tendsto (fun n => c^n*(x-r)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc hc1).mul_const (x-r)
  have hzero : Tendsto (fun n => exercise18Seq p (r^p) x n-r) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.2 (hb n).le) he ht
  simpa using hzero.add_const r

/-- Complete classification for every positive start, including the first-step reversal. -/
 theorem exercise18_classification (p : ℕ) (hp : 2 ≤ p) (r x : ℝ)
    (hr : 0 < r) (hx : 0 < x) :
    Tendsto (exercise18Seq p (r^p) x) atTop (𝓝 r) ∧
    (x < r → x < exercise18Seq p (r^p) x 1 ∧ r < exercise18Seq p (r^p) x 1 ∧
      StrictAnti (fun n => exercise18Seq p (r^p) x (n+1))) ∧
    (x = r → ∀ n, exercise18Seq p (r^p) x n = r) ∧
    (r < x → (∀ n, r < exercise18Seq p (r^p) x n) ∧
      StrictAnti (exercise18Seq p (r^p) x)) := by
  have hbelow : x < r → x < exercise18Seq p (r^p) x 1 ∧ r < exercise18Seq p (r^p) x 1 ∧
      StrictAnti (fun n => exercise18Seq p (r^p) x (n+1)) := by
    intro h
    have h1 : r < exercise18Seq p (r^p) x 1 := exercise18_above_step p hp r x hr hx (ne_of_lt h)
    refine ⟨h.trans h1, h1, ?_⟩
    have hm := (exercise18_above p hp r (exercise18Seq p (r^p) x 1) hr h1).2
    have hf := funext (fun n => exercise18_shift p 1 n (r^p) x)
    rw [hf] at hm
    exact hm
  have heq : x = r → ∀ n, exercise18Seq p (r^p) x n = r := by
    rintro rfl n
    exact exercise18_constant p (by omega) x hr n
  have habove := exercise18_above p hp r x hr
  refine ⟨?_, hbelow, heq, habove⟩
  rcases lt_trichotomy x r with h | h | h
  · have ht := exercise18_limit_above p hp r (exercise18Seq p (r^p) x 1) hr (hbelow h).2.1
    have hf := funext (fun n => exercise18_shift p 1 n (r^p) x)
    rw [hf] at ht
    exact (tendsto_add_atTop_iff_nat 1).1 ht
  · have hf : exercise18Seq p (r^p) x = fun _ => r := funext (heq h)
    rw [hf]
    exact tendsto_const_nhds
  · exact exercise18_limit_above p hp r x hr h

/-- Specialization to the unchanged hypotheses of Exercise 16. No p-th-root starting bound is assumed. -/
 theorem exercise18_higher_exponents (p : ℕ) (hp : 2 ≤ p) (a x : ℝ)
    (ha : 0 < a) (hx : Real.sqrt a < x) :
    let r := exercise18Root p a
    0 < r ∧ r^p = a ∧
    Tendsto (exercise18Seq p a x) atTop (𝓝 r) ∧
    (x < r → x < exercise18Seq p a x 1 ∧ r < exercise18Seq p a x 1 ∧
      StrictAnti (fun n => exercise18Seq p a x (n+1))) ∧
    (x = r → ∀ n, exercise18Seq p a x n = r) ∧
    (r < x → (∀ n, r < exercise18Seq p a x n) ∧ StrictAnti (exercise18Seq p a x)) := by
  have hs := exercise18_root_spec p (by omega) a ha
  have h := exercise18_classification p hp (exercise18Root p a) x hs.1
    ((Real.sqrt_pos.2 ha).trans hx)
  rw [hs.2] at h
  exact ⟨hs.1, hs.2, h⟩

/-- The displayed power relation determines the positive root uniquely. -/
theorem exercise18_root_unique (p : ℕ) (hp : 1 ≤ p) (a y : ℝ)
    (ha : 0 < a) (hy : 0 < y) (he : y^p = a) : y = exercise18Root p a := by
  have hs := exercise18_root_spec p hp a ha
  exact (pow_left_inj₀ hy.le hs.1.le (by omega : p ≠ 0)).1 (he.trans hs.2.symm)

/-- The inherited square-root bound really permits a start below the cubic root. -/
 theorem exercise18_below_example :
    Real.sqrt ((1:ℝ)/64) < 3/16 ∧ (3:ℝ)/16 < 1/4 ∧
    ((1:ℝ)/4)^3 = 1/64 ∧ (1:ℝ)/4 < exercise18Seq 3 (1/64) (3/16) 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/64)
  have hn := Real.sqrt_nonneg ((1:ℝ)/64)
  refine ⟨by nlinarith, by norm_num, by norm_num, ?_⟩
  simpa only [exercise18Seq_succ, exercise18Seq_zero, show ((1:ℝ)/4)^3 = 1/64 by norm_num] using
    exercise18_above_step 3 (by omega) (1/4) (3/16) (by norm_num) (by norm_num) (by norm_num)

end Rudin.Chapter03
