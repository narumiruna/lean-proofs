module

public import Mathlib

/-! # Chapter 7, Exercise 14

The two literal series in PDF page 177 (book page 168). The construction uses
interleaved binary digits, doubled to ternary digits, with a leading zero.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter07
namespace Schoenberg

/-- Exactly the hypotheses on the plateau function in the source. -/
structure Plateau (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  bounds : ∀ t, f t ∈ Icc 0 1
  periodic : Function.Periodic f 2
  zero : ∀ t ∈ Icc (0 : ℝ) (1 / 3), f t = 0
  one : ∀ t ∈ Icc (2 / 3 : ℝ) 1, f t = 1

/-- The source's first series, with `n + 1` in place of its index `n ≥ 1`. -/
noncomputable def x (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ (2 * n + 1) * t)

/-- The source's second series, with the same index shift. -/
noncomputable def y (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ (2 * n + 2) * t)

noncomputable def curve (f : ℝ → ℝ) (t : ℝ) : ℝ × ℝ := (x f t, y f t)

lemma weights_summable : Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) :=
  (summable_geometric_of_lt_one (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num)).comp_injective (fun _ _ h => Nat.add_right_cancel h)

lemma weights_sum : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1)) = 1 := by
  rw [geom_series_succ _ (by norm_num),
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

lemma term_bound {f : ℝ → ℝ} (hf : Plateau f) (k : ℕ → ℕ) (n : ℕ) (t : ℝ) :
    ‖(2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t)‖ ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hf.bounds _).1)]
  exact mul_le_of_le_one_right (by positivity) (hf.bounds _).2

lemma series_summable {f : ℝ → ℝ} (hf : Plateau f) (k : ℕ → ℕ) (t : ℝ) :
    Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t)) :=
  weights_summable.of_norm_bounded (term_bound hf k · t)

/-- Uniform convergence of the ordered partial sums, on the whole real line. -/
lemma series_uniform {f : ℝ → ℝ} (hf : Plateau f) (k : ℕ → ℕ) :
    TendstoUniformly
      (fun N t => ∑ n ∈ Finset.range N, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t))
      (fun t => ∑' n, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t)) atTop :=
  tendstoUniformly_tsum_nat weights_summable (term_bound hf k)

lemma series_continuous {f : ℝ → ℝ} (hf : Plateau f) (k : ℕ → ℕ) :
    Continuous (fun t => ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t)) := by
  apply continuous_tsum _ weights_summable (term_bound hf k)
  intro n
  exact continuous_const.mul (hf.continuous.comp (continuous_const.mul continuous_id))

lemma series_bounds {f : ℝ → ℝ} (hf : Plateau f) (k : ℕ → ℕ) (t : ℝ) :
    (∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * f (3 ^ k n * t)) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact tsum_nonneg fun n => mul_nonneg (by positivity) (hf.bounds _).1
  · rw [← weights_sum]
    exact (series_summable hf k t).tsum_le_tsum
      (fun n => (le_abs_self _).trans (term_bound hf k n t)) weights_summable

/-- Double a binary digit to obtain a zero-or-two ternary digit. -/
def ternaryDigit (a : Fin 2) : Fin 3 := ⟨2 * a.val, by have := a.isLt; omega⟩

@[simp] lemma ternaryDigit_val (a : Fin 2) : (ternaryDigit a).val = 2 * a.val := rfl

/-- Rudin's point: the leading ternary digit is zero. -/
noncomputable def cantorPoint (a : ℕ → Fin 2) : ℝ :=
  Real.ofDigits (fun n => ternaryDigit (a n)) / 3

/-- Literal form of the series in the hint (`i = n + 1`). -/
lemma cantorPoint_series (a : ℕ → Fin 2) :
    cantorPoint a = ∑' n : ℕ, (2 * (a n).val : ℝ) / 3 ^ (n + 2) := by
  unfold cantorPoint Real.ofDigits
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  simp only [Real.ofDigitsTerm, ternaryDigit_val, Nat.cast_mul, Nat.cast_ofNat]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
  ring

lemma cantorPoint_mem (a : ℕ → Fin 2) : cantorPoint a ∈ cantorSet := by
  have h : Real.ofDigits (fun n => ternaryDigit (a n)) ∈ cantorSet := by
    apply ofDigits_zero_two_sequence_mem_cantorSet
    intro n he
    have hh := congrArg Fin.val he
    simp only [ternaryDigit_val] at hh
    change 2 * (a n).val = 1 at hh
    omega
  rw [cantorSet_eq_union_halves]
  exact Or.inl ⟨_, h, rfl⟩

lemma ternary_step (a : ℕ → Fin 2) :
    3 * Real.ofDigits (fun n => ternaryDigit (a n)) =
      2 * (a 0).val + Real.ofDigits (fun n => ternaryDigit (a (n + 1))) := by
  have h := Real.ofDigits_eq_sum_add_ofDigits (fun n => ternaryDigit (a n)) 1
  simp only [Finset.range_one, Finset.sum_singleton, Real.ofDigitsTerm,
    ternaryDigit_val, Nat.cast_mul, Nat.cast_ofNat, pow_one] at h
  linarith

/-- Removing `n` ternary digits leaves an even integer plus the remaining tail. -/
lemma ternary_shift (a : ℕ → Fin 2) (n : ℕ) :
    ∃ k : ℕ, 3 ^ n * Real.ofDigits (fun i => ternaryDigit (a i)) =
      2 * k + Real.ofDigits (fun i => ternaryDigit (a (i + n))) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨3 * k + (a n).val, ?_⟩
    have hs := ternary_step (fun i => a (i + n))
    simp only [zero_add] at hs
    have he : (fun i => ternaryDigit (a (i + 1 + n))) =
        (fun i => ternaryDigit (a (i + (n + 1)))) := by
      funext i
      congr 2
      omega
    rw [he] at hs
    rw [pow_succ, mul_right_comm, hk]
    push_cast
    nlinarith

/-- A zero-or-two ternary tail lies on the plateau for its first digit. -/
lemma plateau_tail {f : ℝ → ℝ} (hf : Plateau f) (a : ℕ → Fin 2) :
    f (Real.ofDigits (fun n => ternaryDigit (a n))) = (a 0).val := by
  have hs := ternary_step a
  have hn := Real.ofDigits_nonneg (fun n => ternaryDigit (a (n + 1)))
  have hl := Real.ofDigits_le_one (fun n => ternaryDigit (a (n + 1)))
  have ha : (a 0).val = 0 ∨ (a 0).val = 1 := by have := (a 0).isLt; omega
  rcases ha with ha | ha
  · rw [ha] at hs ⊢
    norm_num at hs ⊢
    exact hf.zero _ ⟨by linarith, by linarith⟩
  · rw [ha] at hs ⊢
    norm_num at hs ⊢
    exact hf.one _ ⟨by linarith, by linarith⟩

/-- The key identity in Rudin's hint, including all endpoint digit choices. -/
lemma sample_cantorPoint {f : ℝ → ℝ} (hf : Plateau f) (a : ℕ → Fin 2) (n : ℕ) :
    f (3 ^ (n + 1) * cantorPoint a) = (a n).val := by
  obtain ⟨k, hk⟩ := ternary_shift a n
  have he : 3 ^ (n + 1) * cantorPoint a =
      Real.ofDigits (fun i => ternaryDigit (a (i + n))) + k * 2 := by
    unfold cantorPoint
    rw [pow_succ]
    nlinarith
  rw [he]
  have hp := hf.periodic.nat_mul k
  rw [hp]
  simpa using plateau_tail hf (fun i => a (i + n))

/-- Even slots hold the digits of `u`; odd slots hold the digits of `v`. -/
def interleave (u v : ℕ → Fin 2) (n : ℕ) : Fin 2 :=
  if n % 2 = 0 then u (n / 2) else v (n / 2)

@[simp] lemma interleave_even (u v : ℕ → Fin 2) (n : ℕ) :
    interleave u v (2 * n) = u n := by simp [interleave]

@[simp] lemma interleave_odd (u v : ℕ → Fin 2) (n : ℕ) :
    interleave u v (2 * n + 1) = v n := by simp [interleave, Nat.add_div]

/-- The two series at the constructed point are exactly the two binary expansions. -/
lemma curve_cantorPoint {f : ℝ → ℝ} (hf : Plateau f) (u v : ℕ → Fin 2) :
    curve f (cantorPoint (interleave u v)) = (Real.ofDigits u, Real.ofDigits v) := by
  apply Prod.ext
  · change x f _ = _
    unfold x Real.ofDigits
    apply tsum_congr
    intro n
    rw [sample_cantorPoint hf, interleave_even]
    simp only [Real.ofDigitsTerm, inv_pow]
    ring
  · change y f _ = _
    unfold y Real.ofDigits
    apply tsum_congr
    intro n
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      sample_cantorPoint hf, interleave_odd]
    simp only [Real.ofDigitsTerm, inv_pow]
    ring

end Schoenberg

open Schoenberg

/-- Both specified coordinate series converge uniformly and define a continuous map. -/
theorem exercise14_continuity {f : ℝ → ℝ} (hf : Plateau f) : Continuous (curve f) :=
  (series_continuous hf (fun n => 2 * n + 1)).prodMk
    (series_continuous hf (fun n => 2 * n + 2))

/-- Constructive Cantor surjectivity: interleave any binary expansions of the target. -/
theorem exercise14_constructive_cantor {f : ℝ → ℝ} (hf : Plateau f)
    (p : ℝ × ℝ) (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    ∃ u v : ℕ → Fin 2,
      Real.ofDigits u = p.1 ∧ Real.ofDigits v = p.2 ∧
      cantorPoint (interleave u v) ∈ cantorSet ∧
      curve f (cantorPoint (interleave u v)) = p := by
  obtain ⟨u, _, hu⟩ := Real.ofDigits_SurjOn (by norm_num : 1 < 2) hp.1
  obtain ⟨v, _, hv⟩ := Real.ofDigits_SurjOn (by norm_num : 1 < 2) hp.2
  refine ⟨u, v, hu, hv, cantorPoint_mem _, ?_⟩
  rw [curve_cantorPoint hf, hu, hv]

/-- The image of the literal middle-thirds Cantor set is the whole unit square. -/
theorem exercise14_cantor_surjection {f : ℝ → ℝ} (hf : Plateau f) :
    curve f '' cantorSet = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨series_bounds hf _ t, series_bounds hf _ t⟩
  · intro p hp
    obtain ⟨u, v, _, _, ht, he⟩ := exercise14_constructive_cantor hf p hp
    exact ⟨_, ht, he⟩

/-- The image of the entire interval is exactly the unit square. -/
theorem exercise14_interval_surjection {f : ℝ → ℝ} (hf : Plateau f) :
    curve f '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨series_bounds hf _ t, series_bounds hf _ t⟩
  · rw [← exercise14_cantor_surjection hf]
    exact image_mono cantorSet_subset_unitInterval

end Rudin.Chapter07
