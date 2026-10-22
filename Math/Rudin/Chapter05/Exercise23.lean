module

public import Mathlib

@[expose] public section
noncomputable section
open Set Filter Function
open scoped Topology
namespace Rudin.Chapter05

def exercise23Map (x : ℝ) : ℝ := (x^3 + 1) / 3

theorem exercise23_continuous : Continuous exercise23Map := by
  unfold exercise23Map
  fun_prop

theorem exercise23_strictMono : StrictMono exercise23Map := by
  intro x y h
  have := (show Odd (3 : ℕ) by decide).strictMono_pow h
  dsimp [exercise23Map]
  linarith

/-- The three roots, with the exact open intervals from the source. -/
structure Exercise23Roots where
  a : ℝ
  b : ℝ
  c : ℝ
  a_loc : a ∈ Ioo (-2) (-1)
  b_loc : b ∈ Ioo 0 1
  c_loc : c ∈ Ioo 1 2
  a_fixed : exercise23Map a = a
  b_fixed : exercise23Map b = b
  c_fixed : exercise23Map c = c

theorem exercise23_roots_exist : Nonempty Exercise23Roots := by
  let p : ℝ → ℝ := fun x => x^3 - 3*x + 1
  have hp : Continuous p := by fun_prop
  obtain ⟨a, ha, hpa⟩ := intermediate_value_Icc (a := (-2 : ℝ)) (b := -1)
    (by norm_num) hp.continuousOn (show 0 ∈ Icc (p (-2)) (p (-1)) by norm_num [p])
  obtain ⟨b, hb, hpb⟩ := intermediate_value_Icc' (a := (0 : ℝ)) (b := 1)
    (by norm_num) hp.continuousOn (show 0 ∈ Icc (p 1) (p 0) by norm_num [p])
  obtain ⟨c, hc, hpc⟩ := intermediate_value_Icc (a := (1 : ℝ)) (b := 2)
    (by norm_num) hp.continuousOn (show 0 ∈ Icc (p 1) (p 2) by norm_num [p])
  have hal : a ∈ Ioo (-2) (-1) := by
    refine ⟨lt_of_le_of_ne ha.1 ?_, lt_of_le_of_ne ha.2 ?_⟩
    · intro h; subst a; norm_num [p] at hpa
    · intro h; subst a; norm_num [p] at hpa
  have hbl : b ∈ Ioo 0 1 := by
    refine ⟨lt_of_le_of_ne hb.1 ?_, lt_of_le_of_ne hb.2 ?_⟩
    · intro h; subst b; norm_num [p] at hpb
    · intro h; subst b; norm_num [p] at hpb
  have hcl : c ∈ Ioo 1 2 := by
    refine ⟨lt_of_le_of_ne hc.1 ?_, lt_of_le_of_ne hc.2 ?_⟩
    · intro h; subst c; norm_num [p] at hpc
    · intro h; subst c; norm_num [p] at hpc
  refine ⟨⟨a, b, c, hal, hbl, hcl, ?_, ?_, ?_⟩⟩ <;>
    dsimp [exercise23Map] <;> dsimp [p] at * <;> linarith

/-- Fix one such triple; the next theorem proves it lists all fixed points. -/
def exercise23Roots : Exercise23Roots := Classical.choice exercise23_roots_exist

theorem exercise23_factor (r : Exercise23Roots) (x : ℝ) :
    exercise23Map x - x = (x-r.a)*(x-r.b)*(x-r.c)/3 := by
  have ha : r.a^3 - 3*r.a + 1 = 0 := by
    have := r.a_fixed; dsimp [exercise23Map] at this; linarith
  have hb : r.b^3 - 3*r.b + 1 = 0 := by
    have := r.b_fixed; dsimp [exercise23Map] at this; linarith
  have hc : r.c^3 - 3*r.c + 1 = 0 := by
    have := r.c_fixed; dsimp [exercise23Map] at this; linarith
  have hab : r.b - r.a ≠ 0 := by linarith [r.a_loc.2, r.b_loc.1]
  have hac : r.c - r.a ≠ 0 := by linarith [r.a_loc.2, r.c_loc.1]
  have hbc : r.b - r.c ≠ 0 := by linarith [r.b_loc.2, r.c_loc.1]
  have qb : r.b^2 + r.a*r.b + r.a^2 - 3 = 0 := by
    apply (mul_eq_zero.mp (show (r.b-r.a)*(r.b^2+r.a*r.b+r.a^2-3) = 0 by
      linear_combination hb - ha)).resolve_left hab
  have qc : r.c^2 + r.a*r.c + r.a^2 - 3 = 0 := by
    apply (mul_eq_zero.mp (show (r.c-r.a)*(r.c^2+r.a*r.c+r.a^2-3) = 0 by
      linear_combination hc - ha)).resolve_left hac
  have hs : r.a + r.b + r.c = 0 := by
    apply (mul_eq_zero.mp (show (r.b-r.c)*(r.a+r.b+r.c) = 0 by
      linear_combination qb - qc)).resolve_left hbc
  have ht : r.a^2 - 3 = r.b*r.c := by
    linear_combination qb - r.b*hs
  dsimp [exercise23Map]
  linear_combination ha / 3 + (x-r.a)*ht / 3 + (x-r.a)*x*hs / 3

/-- Exactly three fixed points, and all starts at fixed points are constant. -/
theorem exercise23_fixed_points (r : Exercise23Roots) :
    (∀ x : ℝ, exercise23Map x = x ↔ x = r.a ∨ x = r.b ∨ x = r.c) ∧
    (∀ x : ℝ, exercise23Map x = x → ∀ n : ℕ, exercise23Map^[n] x = x) := by
  constructor
  · intro x
    rw [← sub_eq_zero, exercise23_factor r x]
    simp [div_eq_zero_iff, mul_eq_zero, sub_eq_zero, or_assoc]
  · intro x hx n
    exact (show IsFixedPt exercise23Map x from hx).iterate n

/-- The signs determine all four nonconstant dynamical regions. -/
theorem exercise23_step_regions (r : Exercise23Roots) (x : ℝ) :
    (x < r.a → exercise23Map x < x) ∧
    (r.a < x → x < r.b → x < exercise23Map x) ∧
    (r.b < x → x < r.c → exercise23Map x < x) ∧
    (r.c < x → x < exercise23Map x) := by
  have hab : r.a < r.b := by linarith [r.a_loc.2, r.b_loc.1]
  have hbc : r.b < r.c := by linarith [r.b_loc.2, r.c_loc.1]
  have he := exercise23_factor r x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have : (x-r.a)*(x-r.b)*(x-r.c)/3 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
        (mul_pos_of_neg_of_neg (by linarith) (by linarith)) (by linarith)) (by norm_num)
    linarith
  · intro h1 h2
    have : 0 < (x-r.a)*(x-r.b)*(x-r.c)/3 :=
      div_pos (mul_pos_of_neg_of_neg
        (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (by linarith)) (by norm_num)
    linarith
  · intro h1 h2
    have : (x-r.a)*(x-r.b)*(x-r.c)/3 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg
        (mul_pos (by linarith) (by linarith)) (by linarith)) (by norm_num)
    linarith
  · intro h
    have : 0 < (x-r.a)*(x-r.b)*(x-r.c)/3 :=
      div_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)) (by norm_num)
    linarith

/-- Below the left fixed point the orbit tends to negative infinity. -/
theorem exercise23_a (r : Exercise23Roots) {x : ℝ} (hx : x < r.a) :
    Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atBot := by
  have hm := exercise23_strictMono.monotone.antitone_iterate_of_map_le
    ((exercise23_step_regions r x).1 hx).le
  rcases tendsto_atTop_of_antitone hm with h | ⟨l, hl⟩
  · exact h
  have hfix := isFixedPt_of_tendsto_iterate hl exercise23_continuous.continuousAt
  have hle : l ≤ x := le_of_tendsto hl (Eventually.of_forall (fun n => by
    simpa using hm (Nat.zero_le n)))
  rcases (exercise23_fixed_points r).1 l |>.mp hfix with h | h | h
  · linarith
  · linarith [r.a_loc.2, r.b_loc.1]
  · linarith [r.a_loc.2, r.c_loc.1]

/-- Above the right fixed point the orbit tends to positive infinity. -/
theorem exercise23_c (r : Exercise23Roots) {x : ℝ} (hx : r.c < x) :
    Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atTop := by
  have hm := exercise23_strictMono.monotone.monotone_iterate_of_le_map
    ((exercise23_step_regions r x).2.2.2 hx).le
  rcases tendsto_atTop_of_monotone hm with h | ⟨l, hl⟩
  · exact h
  have hfix := isFixedPt_of_tendsto_iterate hl exercise23_continuous.continuousAt
  have hle : x ≤ l := ge_of_tendsto hl (Eventually.of_forall (fun n => by
    simpa using hm (Nat.zero_le n)))
  rcases (exercise23_fixed_points r).1 l |>.mp hfix with h | h | h
  · linarith [r.a_loc.2, r.c_loc.1]
  · linarith [r.b_loc.2, r.c_loc.1]
  · linarith

/-- Every start strictly between the outer fixed points tends to the middle one.
This includes a start at the middle fixed point. -/
theorem exercise23_b (r : Exercise23Roots) {x : ℝ} (hx : r.a < x) (hx' : x < r.c) :
    Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop (𝓝 r.b) := by
  rcases lt_trichotomy x r.b with hxb | rfl | hbx
  · have hm := exercise23_strictMono.monotone.monotone_iterate_of_le_map
      ((exercise23_step_regions r x).2.1 hx hxb).le
    have hb : ∀ n : ℕ, exercise23Map^[n] x ≤ r.b := by
      intro n
      have := (exercise23_strictMono.monotone.iterate n) hxb.le
      simpa only [((show IsFixedPt exercise23Map r.b from r.b_fixed).iterate n).eq] using this
    have hl := tendsto_atTop_ciSup hm (⟨r.b, by rintro _ ⟨n, rfl⟩; exact hb n⟩)
    have hfix := isFixedPt_of_tendsto_iterate hl exercise23_continuous.continuousAt
    have hlow : x ≤ ⨆ n, exercise23Map^[n] x := ge_of_tendsto hl
      (Eventually.of_forall (fun n => by simpa using hm (Nat.zero_le n)))
    have hupp : (⨆ n, exercise23Map^[n] x) ≤ r.b := le_of_tendsto hl (Eventually.of_forall hb)
    have heq : (⨆ n, exercise23Map^[n] x) = r.b := by
      rcases (exercise23_fixed_points r).1 _ |>.mp hfix with h | h | h
      · linarith
      · exact h
      · linarith [r.b_loc.2, r.c_loc.1]
    simpa only [heq] using hl
  · simpa only [fun n => ((show IsFixedPt exercise23Map r.b from r.b_fixed).iterate n).eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r.b) atTop (𝓝 r.b))
  · have hm := exercise23_strictMono.monotone.antitone_iterate_of_map_le
      ((exercise23_step_regions r x).2.2.1 hbx hx').le
    have hb : ∀ n : ℕ, r.b ≤ exercise23Map^[n] x := by
      intro n
      have := (exercise23_strictMono.monotone.iterate n) hbx.le
      simpa only [((show IsFixedPt exercise23Map r.b from r.b_fixed).iterate n).eq] using this
    have hl := tendsto_atTop_ciInf hm (⟨r.b, by rintro _ ⟨n, rfl⟩; exact hb n⟩)
    have hfix := isFixedPt_of_tendsto_iterate hl exercise23_continuous.continuousAt
    have hupp : (⨅ n, exercise23Map^[n] x) ≤ x := le_of_tendsto hl
      (Eventually.of_forall (fun n => by simpa using hm (Nat.zero_le n)))
    have hlow : r.b ≤ ⨅ n, exercise23Map^[n] x := ge_of_tendsto hl (Eventually.of_forall hb)
    have heq : (⨅ n, exercise23Map^[n] x) = r.b := by
      rcases (exercise23_fixed_points r).1 _ |>.mp hfix with h | h | h
      · linarith [r.a_loc.2, r.b_loc.1]
      · exact h
      · linarith
    simpa only [heq] using hl

/-- Exact dynamical regions: no start outside the stated region has the stated limit. -/
theorem exercise23_exact_regions (r : Exercise23Roots) (x : ℝ) :
    (Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atBot ↔ x < r.a) ∧
    (Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop (𝓝 r.b) ↔ r.a < x ∧ x < r.c) ∧
    (Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atTop ↔ r.c < x) := by
  have hbelow : x ≤ r.a → ∀ n : ℕ, exercise23Map^[n] x ≤ r.a := by
    intro h n
    have := (exercise23_strictMono.monotone.iterate n) h
    simpa only [((show IsFixedPt exercise23Map r.a from r.a_fixed).iterate n).eq] using this
  have habove : r.a ≤ x → ∀ n : ℕ, r.a ≤ exercise23Map^[n] x := by
    intro h n
    have := (exercise23_strictMono.monotone.iterate n) h
    simpa only [((show IsFixedPt exercise23Map r.a from r.a_fixed).iterate n).eq] using this
  have hbelow' : x ≤ r.c → ∀ n : ℕ, exercise23Map^[n] x ≤ r.c := by
    intro h n
    have := (exercise23_strictMono.monotone.iterate n) h
    simpa only [((show IsFixedPt exercise23Map r.c from r.c_fixed).iterate n).eq] using this
  have habove' : r.c ≤ x → ∀ n : ℕ, r.c ≤ exercise23Map^[n] x := by
    intro h n
    have := (exercise23_strictMono.monotone.iterate n) h
    simpa only [((show IsFixedPt exercise23Map r.c from r.c_fixed).iterate n).eq] using this
  refine ⟨⟨?_, fun h => exercise23_a r h⟩, ⟨?_, fun h => exercise23_b r h.1 h.2⟩,
    ⟨?_, fun h => exercise23_c r h⟩⟩
  · intro ht
    by_contra! h
    obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_atBot r.a)).exists
    exact (habove h n).not_gt hn
  · intro ht
    constructor
    · by_contra! h
      have := le_of_tendsto ht (Eventually.of_forall (hbelow h))
      linarith [r.a_loc.2, r.b_loc.1]
    · by_contra! h
      have := ge_of_tendsto ht (Eventually.of_forall (habove' h))
      linarith [r.b_loc.2, r.c_loc.1]
  · intro ht
    by_contra! h
    obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_atTop r.c)).exists
    exact (hbelow' h n).not_gt hn

/-- The root triple required by all the classification theorems exists. -/
theorem exercise23_classification :
    ∃ r : Exercise23Roots,
      (∀ x, exercise23Map x = x ↔ x = r.a ∨ x = r.b ∨ x = r.c) ∧
      (∀ x, exercise23Map x = x → ∀ n : ℕ, exercise23Map^[n] x = x) ∧
      (∀ x, Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atBot ↔ x < r.a) ∧
      (∀ x, Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop (𝓝 r.b) ↔ r.a < x ∧ x < r.c) ∧
      (∀ x, Tendsto (fun n : ℕ => exercise23Map^[n] x) atTop atTop ↔ r.c < x) := by
  exact ⟨exercise23Roots, (exercise23_fixed_points exercise23Roots).1,
    (exercise23_fixed_points exercise23Roots).2,
    fun x => (exercise23_exact_regions exercise23Roots x).1,
    fun x => (exercise23_exact_regions exercise23Roots x).2.1,
    fun x => (exercise23_exact_regions exercise23Roots x).2.2⟩

end Rudin.Chapter05
