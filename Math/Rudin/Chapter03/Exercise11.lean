module

public import Mathlib

/-! # R03E11: transformations of a positive divergent series
`exercise11_sum a n` is exactly `a 1 + ... + a n`; its value at zero is
zero. Every infinite series below starts with the source index one, using
`k + 1` in ordered partial sums. Summability is used only for nonnegative
real series, with an explicit ordered-convergence equivalence.
-/

@[expose] public section

namespace Rudin.Chapter03
open Filter Topology Finset

noncomputable def exercise11_sum (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, a (k + 1)

def exercise11_converges (f : ℕ → ℝ) : Prop :=
  ∃ s, Tendsto (fun N => ∑ k ∈ range N, f (k + 1)) atTop (nhds s)

theorem exercise11_converges_iff {f : ℕ → ℝ} (hf : ∀ n ≥ 1, 0 ≤ f n) :
    exercise11_converges f ↔ Summable f := by
  constructor
  · rintro ⟨s, hs⟩
    exact (summable_nat_add_iff 1).mp
      ⟨s, (hasSum_iff_tendsto_nat_of_nonneg (fun k => hf _ (by omega)) s).mpr hs⟩
  · intro hs
    exact ⟨_, ((summable_nat_add_iff 1).mpr hs).hasSum.tendsto_sum_nat⟩

theorem exercise11_sum_step (a : ℕ → ℝ) (n : ℕ) :
    exercise11_sum a (n + 1) = exercise11_sum a n + a (n + 1) := by
  exact sum_range_succ _ _

theorem exercise11_sum_mono {a : ℕ → ℝ} (hp : ∀ n ≥ 1, 0 < a n) :
    Monotone (exercise11_sum a) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [exercise11_sum_step]
  exact le_add_of_nonneg_right (hp _ (by omega)).le

theorem exercise11_sum_pos {a : ℕ → ℝ} (hp : ∀ n ≥ 1, 0 < a n)
    {n : ℕ} (hn : 1 ≤ n) : 0 < exercise11_sum a n := by
  have h : exercise11_sum a 1 = a 1 := by simp [exercise11_sum]
  exact (h ▸ hp 1 le_rfl).trans_le (exercise11_sum_mono hp hn)

/-- R03E11(a). -/
theorem exercise11_a (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hd : ¬ exercise11_converges a) :
    ¬ exercise11_converges (fun n => a n / (1 + a n)) := by
  intro hc
  have hq : ∀ n ≥ 1, 0 ≤ a n / (1 + a n) := by
    intro n hn
    exact (div_pos (hp n hn) (by linarith [hp n hn])).le
  have hs := (exercise11_converges_iff hq).mp hc
  have he : ∀ᶠ n in atTop, a n / (1 + a n) ≤ 1 / 2 :=
    hs.tendsto_atTop_zero.eventually_le_const (by norm_num)
  have ha : Summable a := (hs.mul_left 2).of_norm_bounded_eventually (by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [he, eventually_ge_atTop 1] with n hn hn'
    have hp' := hp n hn'
    rw [Real.norm_eq_abs, abs_of_pos hp']
    have hden : 0 < 1 + a n := by linarith
    have hsmall : a n ≤ 1 := by
      have := (div_le_iff₀ hden).mp hn
      linarith
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).mpr
    nlinarith)
  exact hd ((exercise11_converges_iff (fun n hn => (hp n hn).le)).mpr ha)

/-- R03E11(b), with the source's positive integers `N` and `k`. -/
theorem exercise11_b_inequality (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) :
    1 - exercise11_sum a N / exercise11_sum a (N + k) ≤
      ∑ j ∈ range k, a (N + j + 1) / exercise11_sum a (N + j + 1) := by
  have hend := exercise11_sum_pos hp (show 1 ≤ N + k by omega)
  have hcomp : (∑ j ∈ range k, a (N + j + 1)) / exercise11_sum a (N + k) ≤
      ∑ j ∈ range k, a (N + j + 1) / exercise11_sum a (N + j + 1) := by
    rw [sum_div]
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    exact div_le_div_of_nonneg_left (hp _ (by omega)).le
      (exercise11_sum_pos hp (by omega)) (exercise11_sum_mono hp (by omega))
  have hid : (∑ j ∈ range k, a (N + j + 1)) =
      exercise11_sum a (N + k) - exercise11_sum a N := by
    have h := sum_range_add (fun j => a (j + 1)) N k
    change exercise11_sum a (N + k) = exercise11_sum a N + _ at h
    linarith
  rw [hid] at hcomp
  convert hcomp using 1
  field_simp

/-- R03E11(b): failure of ordered convergence. -/
theorem exercise11_b_divergence (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    (hd : ¬ exercise11_converges a) :
    ¬ exercise11_converges (fun n => a n / exercise11_sum a n) := by
  have hns : ¬ Summable (fun n => a (n + 1)) := by
    intro hs
    exact hd ⟨_, hs.hasSum.tendsto_sum_nat⟩
  have ht : Tendsto (exercise11_sum a) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => (hp _ (by omega)).le)).mp hns
  intro hc
  let q := fun n => a n / exercise11_sum a n
  have hqp : ∀ n ≥ 1, 0 ≤ q n := fun n hn =>
    (div_pos (hp n hn) (exercise11_sum_pos hp hn)).le
  have hqs := (exercise11_converges_iff hqp).mp hc
  have bound : ∀ N ≥ 1, 1 ≤ ∑' j, q (j + (N + 1)) := by
    intro N hN
    have hb : ∀ᶠ k in atTop, 1 - exercise11_sum a N / exercise11_sum a (N + k) ≤
        ∑' j, q (j + (N + 1)) := by
      filter_upwards [eventually_ge_atTop 1] with k hk
      refine (exercise11_b_inequality a hp hN hk).trans ?_
      have h := ((summable_nat_add_iff (N + 1)).mpr hqs).sum_le_tsum (range k)
        (fun j _ => hqp _ (by omega))
      simpa [q, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    have hti : Tendsto (fun k => (exercise11_sum a (N + k))⁻¹) atTop (nhds 0) := by
      apply tendsto_inv_atTop_zero.comp
      simpa only [Function.comp_def, Nat.add_comm] using ht.comp (tendsto_add_atTop_nat N)
    have hl : Tendsto (fun k => 1 - exercise11_sum a N / exercise11_sum a (N + k))
        atTop (nhds 1) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.sub (hti.const_mul (exercise11_sum a N))
    exact le_of_tendsto hl hb
  have hz : Tendsto (fun N => ∑' j, q (j + (N + 1))) atTop (nhds 0) :=
    (tendsto_sum_nat_add q).comp (tendsto_add_atTop_nat 1)
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto hz (by
    filter_upwards [eventually_ge_atTop 1] with N hN using bound N hN)
  norm_num at this

/-- R03E11(c). The predecessor denominator is used only for `n ≥ 2`. -/
theorem exercise11_c_inequality (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n)
    {n : ℕ} (hn : 2 ≤ n) :
    a n / exercise11_sum a n ^ 2 ≤
      1 / exercise11_sum a (n - 1) - 1 / exercise11_sum a n := by
  have hx := exercise11_sum_pos hp (show 1 ≤ n - 1 by omega)
  have hy := exercise11_sum_pos hp (show 1 ≤ n by omega)
  have hs : exercise11_sum a n = exercise11_sum a (n - 1) + a n := by
    simpa [show n - 1 + 1 = n by omega] using exercise11_sum_step a (n - 1)
  have hn' := hp n (by omega)
  apply (div_le_iff₀ (sq_pos_of_pos hy)).mpr
  field_simp
  nlinarith

/-- R03E11(c), including the separate first term. -/
theorem exercise11_c_convergence (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n) :
    Summable (fun n => a (n + 1) / exercise11_sum a (n + 1) ^ 2) ∧
    exercise11_converges (fun n => a n / exercise11_sum a n ^ 2) := by
  have hb : ∀ N, (∑ k ∈ range N, a (k + 2) / exercise11_sum a (k + 2) ^ 2) ≤
      1 / exercise11_sum a 1 - 1 / exercise11_sum a (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have h := exercise11_c_inequality a hp (show 2 ≤ N + 2 by omega)
      rw [show N + 2 - 1 = N + 1 by omega] at h
      linarith
  have ht : Summable (fun k => a (k + 2) / exercise11_sum a (k + 2) ^ 2) :=
    summable_of_sum_range_le (fun k => div_nonneg (hp _ (by omega)).le (sq_nonneg _))
      (fun N => (hb N).trans (sub_le_self _
        (one_div_nonneg.mpr (exercise11_sum_pos hp (by omega)).le)))
  have hs : Summable (fun n => a (n + 1) / exercise11_sum a (n + 1) ^ 2) :=
    (summable_nat_add_iff 1).mp ht
  exact ⟨hs, ⟨_, hs.hasSum.tendsto_sum_nat⟩⟩

/-- R03E11(d): the quadratic denominator always gives convergence. -/
theorem exercise11_d_quadratic (a : ℕ → ℝ) (hp : ∀ n ≥ 1, 0 < a n) :
    Summable (fun n => a (n + 1) / (1 + (n + 1 : ℝ) ^ 2 * a (n + 1))) ∧
    exercise11_converges (fun n => a n / (1 + (n : ℝ) ^ 2 * a n)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    simpa [one_div, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (show 1 < 2 by decide))
  have hs : Summable (fun n => a (n + 1) / (1 + (n + 1 : ℝ) ^ 2 * a (n + 1))) := by
    apply hbase.of_nonneg_of_le
    · intro n
      have := hp (n + 1) (by omega)
      positivity
    · intro n
      have hn : (0 : ℝ) < n + 1 := by positivity
      have ha := hp (n + 1) (by omega)
      have hd : 0 < 1 + (n + 1 : ℝ) ^ 2 * a (n + 1) := by positivity
      apply (div_le_div_iff₀ hd (sq_pos_of_pos hn)).mpr
      nlinarith
  refine ⟨hs, ⟨∑' n, a (n + 1) / (1 + (n + 1 : ℝ) ^ 2 * a (n + 1)), ?_⟩⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hs.hasSum.tendsto_sum_nat

/-- Positive background with unit spikes at the powers of two. -/
noncomputable def exercise11_sparse (n : ℕ) : ℝ := by
  classical
  exact 1 / (n + 1 : ℝ) ^ 2 +
    if n ∈ Set.range (fun k : ℕ => 2 ^ k) then 1 else 0

theorem exercise11_sparse_pos (n : ℕ) : 0 < exercise11_sparse n := by
  classical
  unfold exercise11_sparse
  split_ifs <;> positivity

/-- R03E11(d): a positive divergent series whose linear transform converges. -/
theorem exercise11_d_linear_convergent_example :
    (∀ n ≥ 1, 0 < exercise11_sparse n) ∧
    ¬ exercise11_converges exercise11_sparse ∧
    exercise11_converges (fun n => exercise11_sparse n / (1 + (n : ℝ) * exercise11_sparse n)) := by
  classical
  have hinj : Function.Injective (fun k : ℕ => 2 ^ k) := Nat.pow_right_injective (by decide)
  have hdiv : ¬ exercise11_converges exercise11_sparse := by
    intro hc
    have hs := (exercise11_converges_iff (fun n _ => (exercise11_sparse_pos n).le)).mp hc
    have hsub := hs.comp_injective hinj
    have hone : Summable (fun _ : ℕ => (1 : ℝ)) := hsub.of_nonneg_of_le
      (fun _ => by norm_num) (by
        intro k
        simp only [Function.comp_apply, exercise11_sparse,
          Set.mem_range_self, ite_true]
        exact le_add_of_nonneg_left (by positivity))
    have := (summable_const_iff (1 : ℝ)).mp hone
    norm_num at this
  let g : ℕ → ℝ := fun n =>
    if n ∈ Set.range (fun k : ℕ => 2 ^ k) then 1 / (n : ℝ) else 0
  have hg : Summable g := by
    apply (hinj.summable_iff (f := g) (fun n hn => by
      change (if n ∈ Set.range (fun k : ℕ => 2 ^ k) then 1 / (n : ℝ) else 0) = 0
      rw [ite_eq_right hn])).mp
    have heq : (g ∘ (fun k : ℕ => 2 ^ k)) = (fun k => (1 / 2 : ℝ) ^ k) := by
      funext k
      simp [g, one_div, inv_pow]
    rw [heq]
    exact summable_geometric_two
  have hb : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
    simpa [one_div, Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (show 1 < 2 by decide))
  have ht : Summable (fun n => exercise11_sparse n / (1 + (n : ℝ) * exercise11_sparse n)) := by
    apply (hb.add hg).of_norm_bounded_eventually
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have ha := exercise11_sparse_pos n
    have hd : 0 < 1 + (n : ℝ) * exercise11_sparse n := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (div_pos ha hd)]
    by_cases hm : n ∈ Set.range (fun k : ℕ => 2 ^ k)
    · have hle : exercise11_sparse n / (1 + (n : ℝ) * exercise11_sparse n) ≤ 1 / (n : ℝ) := by
        apply (div_le_div_iff₀ hd hn').mpr
        nlinarith
      exact hle.trans (by
        change 1 / (n : ℝ) ≤ 1 / (n + 1 : ℝ) ^ 2 + g n
        dsimp only [g]
        rw [ite_eq_left hm]
        exact le_add_of_nonneg_left (by positivity))
    · simp only [g, hm, ite_false, add_zero]
      have he : exercise11_sparse n = 1 / (n + 1 : ℝ) ^ 2 := by
        simp [exercise11_sparse, hm]
      rw [← he]
      apply (div_le_iff₀ hd).mpr
      nlinarith [mul_nonneg hn'.le (sq_nonneg (exercise11_sparse n))]
  refine ⟨fun n _ => exercise11_sparse_pos n, hdiv, ?_⟩
  apply (exercise11_converges_iff (fun n hn => ?_)).mpr ht
  exact (div_pos (exercise11_sparse_pos n) (by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := exercise11_sparse_pos n
    positivity)).le

/-- R03E11(d): the constant sequence gives divergence of the linear transform. -/
theorem exercise11_d_linear_divergent_example :
    (∀ n ≥ 1, 0 < (fun _ : ℕ => (1 : ℝ)) n) ∧
    ¬ exercise11_converges (fun _ : ℕ => (1 : ℝ)) ∧
    ¬ exercise11_converges (fun n : ℕ => 1 / (1 + (n : ℝ))) := by
  refine ⟨fun _ _ => by norm_num, ?_, ?_⟩
  · intro hc
    have hs := (exercise11_converges_iff (fun _ _ => by norm_num)).mp hc
    have := (summable_const_iff (1 : ℝ)).mp hs
    norm_num at this
  · intro hc
    have hs := (exercise11_converges_iff (fun n _ => by positivity)).mp hc
    have ht : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ht)

/-- R03E11(d): the assumptions do not decide convergence of the linear
transform: both behaviors occur for strictly positive divergent series. -/
theorem exercise11_d_linear_classification :
    (∃ a : ℕ → ℝ, (∀ n ≥ 1, 0 < a n) ∧ ¬ exercise11_converges a ∧
      exercise11_converges (fun n => a n / (1 + (n : ℝ) * a n))) ∧
    (∃ a : ℕ → ℝ, (∀ n ≥ 1, 0 < a n) ∧ ¬ exercise11_converges a ∧
      ¬ exercise11_converges (fun n => a n / (1 + (n : ℝ) * a n))) := by
  refine ⟨⟨exercise11_sparse, exercise11_d_linear_convergent_example⟩, ⟨fun _ => 1, ?_⟩⟩
  simpa using exercise11_d_linear_divergent_example

end Rudin.Chapter03
