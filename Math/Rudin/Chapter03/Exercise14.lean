module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Tactic

/-! # R03E14: arithmetic means and the two Tauberian converses

The sequences have values in `ℂ`. Differences are used only at positive indices.
All convergence statements concern the ordered sequence, not summability.

The source's strict bound `|s_n-s_i| < M ε` needs `M > 0`. For `M = 0`
it can fail. The non-strict bound specified in the inventory is proved here;
it gives the same limsup estimate and converse without an extra hypothesis.
-/

@[expose] public section

namespace Rudin.Chapter03

open Filter Topology Finset

noncomputable section

/-- Arithmetic means, with both endpoints included. -/
def exercise14_mean (s : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ k ∈ range (n + 1), s k

/-- The difference at zero is irrelevant to every weighted sum below. -/
def exercise14_diff (s : ℕ → ℂ) (n : ℕ) : ℂ := s n - s (n - 1)

/-- (a) Convergence is preserved by arithmetic means. -/
theorem exercise14_a {s : ℕ → ℂ} {l : ℂ} (h : Tendsto s atTop (𝓝 l)) :
    Tendsto (exercise14_mean s) atTop (𝓝 l) := by
  have hc := h.cesaro_smul.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ k ∈ range (n + 1), s k)
    atTop (𝓝 l)
  simpa [exercise14_mean, Function.comp_def, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast] using hc

private theorem exercise14_weighted_sum (s : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℂ) * exercise14_diff s k =
      (n + 1 : ℂ) * s n - ∑ k ∈ range (n + 1), s k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ (f := s) (n + 1)]
    simp only [exercise14_diff, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

/-- (d) The weighted-difference identity (also valid at zero). -/
theorem exercise14_d_identity (s : ℕ → ℂ) (n : ℕ) :
    s n - exercise14_mean s n =
      ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ k ∈ Icc 1 n, (k : ℂ) * exercise14_diff s k := by
  have hs : (∑ k ∈ Icc 1 n, (k : ℂ) * exercise14_diff s k) =
      ∑ k ∈ range (n + 1), (k : ℂ) * exercise14_diff s k := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega)]
    simp
  rw [hs, exercise14_weighted_sum, exercise14_mean]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  push_cast
  field_simp

/-- (d) If `n a_n → 0`, convergence of the means gives the same ordered limit. -/
theorem exercise14_d_convergence {s : ℕ → ℂ} {l : ℂ}
    (ha : Tendsto (fun n : ℕ => (n : ℂ) * exercise14_diff s n) atTop (𝓝 0))
    (hs : Tendsto (exercise14_mean s) atTop (𝓝 l)) :
    Tendsto s atTop (𝓝 l) := by
  have hz := exercise14_a ha
  have he : ∀ n, s n = exercise14_mean s n +
      exercise14_mean (fun k => (k : ℂ) * exercise14_diff s k) n := by
    intro n
    simp only [exercise14_mean, exercise14_weighted_sum]
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    push_cast
    field_simp
    ring
  simpa only [← he, add_zero] using hs.add hz

/-- (e) The exact block identity from the source, for `0 ≤ m < n`. -/
theorem exercise14_e_identity (s : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    s n - exercise14_mean s n =
      ((m + 1 : ℕ) : ℂ) / ((n - m : ℕ) : ℂ) *
        (exercise14_mean s n - exercise14_mean s m) +
      (((n - m : ℕ) : ℂ))⁻¹ * ∑ i ∈ Icc (m + 1) n, (s n - s i) := by
  have hsum : (∑ i ∈ Icc (m + 1) n, s i) =
      (∑ i ∈ range (n + 1), s i) - ∑ i ∈ range (m + 1), s i := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sub _ (by omega)]
  rw [sum_sub_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul, hsum]
  have hd : n + 1 - (m + 1) = n - m := by omega
  rw [hd]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hnm : ((n - m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hmn).ne'
  have hc : ((n - m : ℕ) : ℂ) = (n : ℂ) - m := Nat.cast_sub hmn.le
  unfold exercise14_mean
  push_cast
  rw [hc] at hnm ⊢
  field_simp
  ring

private theorem exercise14_telescope (s : ℕ → ℂ) {i n : ℕ} (h : i ≤ n) :
    s n - s i = ∑ k ∈ Icc (i + 1) n, exercise14_diff s k := by
  rw [← Ico_add_one_right_eq_Icc]
  have ht := Finset.sum_Ico_sub (fun k => s (k - 1)) (show i + 1 ≤ n + 1 by omega)
  simpa [exercise14_diff] using ht.symm

/-- (e) Both estimates, with the source's exact endpoints and constants. -/
theorem exercise14_e_estimate {s : ℕ → ℂ} {M : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    {m i n : ℕ} (hmi : m < i) (hin : i ≤ n) :
    ‖s n - s i‖ ≤ (n - i : ℕ) * M / (i + 1 : ℝ) ∧
      (n - i : ℕ) * M / (i + 1 : ℝ) ≤
        (n - m - 1 : ℕ) * M / (m + 2 : ℝ) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 le_rfl)
  have hi : (0 : ℝ) < i + 1 := by positivity
  have hm : (0 : ℝ) < m + 2 := by positivity
  constructor
  · rw [exercise14_telescope s hin]
    calc
      ‖∑ k ∈ Icc (i + 1) n, exercise14_diff s k‖ ≤
          ∑ k ∈ Icc (i + 1) n, M / (i + 1 : ℝ) := by
        apply norm_sum_le_of_le
        intro k hk
        obtain ⟨hik, hkn⟩ := mem_Icc.mp hk
        have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
        have hb := hM k (by omega)
        rw [norm_mul, Complex.norm_natCast] at hb
        apply (le_div_iff₀ hi).2
        calc
          ‖exercise14_diff s k‖ * (i + 1 : ℝ) ≤ ‖exercise14_diff s k‖ * k := by
            gcongr
            exact_mod_cast hik
          _ ≤ M := by nlinarith
      _ = (n - i : ℕ) * M / (i + 1 : ℝ) := by
        simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
        rw [show n + 1 - (i + 1) = n - i by omega]
        ring
  · apply div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) hM0) _ hm _
    · exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show n - i ≤ n - m - 1 by omega)) hM0
    · exact_mod_cast (show m + 2 ≤ i + 1 by omega)

/-- The source's integer choice; only used when `ε ≤ n`. -/
def exercise14_index (ε : ℝ) (n : ℕ) : ℕ := ⌊((n : ℝ) - ε) / (1 + ε)⌋₊

/-- (e) The floor bounds and the resulting ratio bounds. -/
theorem exercise14_e_index_choice {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : ε ≤ (n : ℝ)) :
    let m := exercise14_index ε n
    (m : ℝ) ≤ ((n : ℝ) - ε) / (1 + ε) ∧
    ((n : ℝ) - ε) / (1 + ε) < m + 1 ∧ m < n ∧
    (m + 1 : ℝ) / (n - m : ℕ) ≤ 1 / ε ∧
    (n - m - 1 : ℕ) / (m + 2 : ℝ) < ε := by
  dsimp only
  let m := exercise14_index ε n
  have hp : 0 < 1 + ε := by linarith
  have hx : 0 ≤ ((n : ℝ) - ε) / (1 + ε) := div_nonneg (sub_nonneg.mpr hn) hp.le
  have hlo : (m : ℝ) ≤ ((n : ℝ) - ε) / (1 + ε) := Nat.floor_le hx
  have hhi : ((n : ℝ) - ε) / (1 + ε) < m + 1 := Nat.lt_floor_add_one _
  have hlo' := (le_div_iff₀ hp).mp hlo
  have hhi' := (div_lt_iff₀ hp).mp hhi
  have hmnR : (m : ℝ) < (n : ℝ) := by nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hmn : m < n := by exact_mod_cast hmnR
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn.le
  have hcast' : ((n - m - 1 : ℕ) : ℝ) = (n : ℝ) - m - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n - m by omega), hcast]
    norm_num
  refine ⟨hlo, hhi, hmn, ?_, ?_⟩
  · rw [hcast, div_le_div_iff₀ (by linarith) hε]
    nlinarith
  · rw [hcast', div_lt_iff₀ (by positivity : (0 : ℝ) < m + 2)]
    nlinarith

/-- The index in the source tends to infinity, so the means at that index converge. -/
theorem exercise14_index_tendsto {ε : ℝ} (hε : 0 < ε) :
    Tendsto (exercise14_index ε) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    ((b : ℝ) * (1 + ε) + ε)] with n hn
  apply Nat.le_floor
  apply (le_div_iff₀ (by linarith : 0 < 1 + ε)).2
  linarith

/-- The termwise bound resulting from the source's choice of `m`. -/
theorem exercise14_e_index_estimate {s : ℕ → ℂ} {M ε : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    (hε : 0 < ε) {n i : ℕ} (hn : ε ≤ (n : ℝ))
    (hi : exercise14_index ε n < i) (hin : i ≤ n) :
    ‖s n - s i‖ ≤ M * ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 le_rfl)
  have hc := exercise14_e_index_choice hε hn
  have he := (exercise14_e_estimate hM hi hin)
  calc
    ‖s n - s i‖ ≤ (n - exercise14_index ε n - 1 : ℕ) * M /
        (exercise14_index ε n + 2 : ℝ) := he.1.trans he.2
    _ = M * ((n - exercise14_index ε n - 1 : ℕ) /
        (exercise14_index ε n + 2 : ℝ)) := by ring
    _ ≤ M * ε := mul_le_mul_of_nonneg_left hc.2.2.2.2.le hM0

/-- The printed strict bound is valid when the bound constant is positive. -/
theorem exercise14_e_index_estimate_strict {s : ℕ → ℂ} {M ε : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    (hpos : 0 < M) (hε : 0 < ε) {n i : ℕ} (hn : ε ≤ (n : ℝ))
    (hi : exercise14_index ε n < i) (hin : i ≤ n) :
    ‖s n - s i‖ < M * ε := by
  have hc := exercise14_e_index_choice hε hn
  have he := exercise14_e_estimate hM hi hin
  calc
    ‖s n - s i‖ ≤ (n - exercise14_index ε n - 1 : ℕ) * M /
        (exercise14_index ε n + 2 : ℝ) := he.1.trans he.2
    _ = M * ((n - exercise14_index ε n - 1 : ℕ) /
        (exercise14_index ε n + 2 : ℝ)) := by ring
    _ < M * ε := mul_lt_mul_of_pos_left hc.2.2.2.2 hpos

/-- For the allowed bound `M = 0`, even constant sequences refute the printed
strict estimate at every positive final index and its prescribed floor index. -/
theorem exercise14_e_zero_bound_obstruction :
    (∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff (fun _ => 0) k‖ ≤ (0 : ℝ)) ∧
    Tendsto (exercise14_mean (fun _ => (0 : ℂ))) atTop (𝓝 0) ∧
    ∀ n : ℕ, 1 ≤ n → exercise14_index 1 n < n ∧
      ¬ ‖(0 : ℂ) - 0‖ < (0 : ℝ) * 1 := by
  refine ⟨by simp [exercise14_diff], ?_, ?_⟩
  · exact exercise14_a tendsto_const_nhds
  · intro n hn
    have hc := exercise14_e_index_choice (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    exact ⟨hc.2.2.1, by simp⟩

private theorem exercise14_block_norm (s : ℕ → ℂ) {m n : ℕ} (hmn : m < n)
    {B : ℝ} (hb : ∀ i ∈ Icc (m + 1) n, ‖s n - s i‖ ≤ B) :
    ‖s n - exercise14_mean s n‖ ≤
      (m + 1 : ℝ) / (n - m : ℕ) *
        ‖exercise14_mean s n - exercise14_mean s m‖ + B := by
  have hd : (0 : ℝ) < (n - m : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hmn
  have hmc : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (m + 1)
  have hsum : ‖∑ i ∈ Icc (m + 1) n, (s n - s i)‖ ≤ (n - m : ℕ) * B := by
    calc
      _ ≤ ∑ i ∈ Icc (m + 1) n, B := norm_sum_le_of_le _ hb
      _ = _ := by
        simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
        rw [show n + 1 - (m + 1) = n - m by omega]
  rw [exercise14_e_identity s hmn]
  calc
    _ ≤ ‖((m + 1 : ℕ) : ℂ) / ((n - m : ℕ) : ℂ) *
          (exercise14_mean s n - exercise14_mean s m)‖ +
        ‖(((n - m : ℕ) : ℂ))⁻¹ * ∑ i ∈ Icc (m + 1) n, (s n - s i)‖ :=
      norm_add_le _ _
    _ = (m + 1 : ℝ) / (n - m : ℕ) *
          ‖exercise14_mean s n - exercise14_mean s m‖ +
        ((n - m : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ Icc (m + 1) n, (s n - s i)‖ := by
      simp only [norm_mul, norm_div, norm_inv, Complex.norm_natCast,
        Nat.cast_add, Nat.cast_one, hmc]
    _ ≤ (m + 1 : ℝ) / (n - m : ℕ) *
          ‖exercise14_mean s n - exercise14_mean s m‖ +
        ((n - m : ℕ) : ℝ)⁻¹ * ((n - m : ℕ) * B) := by gcongr
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]

/-- The upper comparison sequence in the prescribed Tauberian argument. -/
def exercise14_error_bound (s : ℕ → ℂ) (l : ℂ) (M ε : ℝ) (n : ℕ) : ℝ :=
  1 / ε * ‖exercise14_mean s n - exercise14_mean s (exercise14_index ε n)‖ +
    M * ε + ‖exercise14_mean s n - l‖

private theorem exercise14_error_bound_tendsto {s : ℕ → ℂ} {l : ℂ} {M ε : ℝ}
    (hs : Tendsto (exercise14_mean s) atTop (𝓝 l)) (hε : 0 < ε) :
    Tendsto (exercise14_error_bound s l M ε) atTop (𝓝 (M * ε)) := by
  have hm := hs.comp (exercise14_index_tendsto hε)
  have h := (((hs.sub hm).norm.const_mul (1 / ε)).add_const (M * ε)).add
    ((hs.sub_const l).norm)
  change Tendsto (fun n => 1 / ε *
    ‖exercise14_mean s n - exercise14_mean s (exercise14_index ε n)‖ +
    M * ε + ‖exercise14_mean s n - l‖) atTop (𝓝 (M * ε))
  simpa using h

private theorem exercise14_error_le {s : ℕ → ℂ} {l : ℂ} {M ε : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖s n - l‖ ≤ exercise14_error_bound s l M ε n := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ε] with n hn
  have hc := exercise14_e_index_choice hε hn
  have hb := exercise14_block_norm s hc.2.2.1 (fun i hi =>
    exercise14_e_index_estimate hM hε hn (by have := (mem_Icc.mp hi).1; omega)
      (mem_Icc.mp hi).2)
  have hr := mul_le_mul_of_nonneg_right hc.2.2.2.1
    (norm_nonneg (exercise14_mean s n - exercise14_mean s (exercise14_index ε n)))
  have ht : ‖s n - l‖ ≤ ‖s n - exercise14_mean s n‖ + ‖exercise14_mean s n - l‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  dsimp only [exercise14_error_bound]
  linarith

/-- (e) The source's limsup estimate, in the extended reals so no boundedness
convention is implicit. It is obtained from the block identity and index choice. -/
theorem exercise14_e_limsup {s : ℕ → ℂ} {l : ℂ} {M : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    (hs : Tendsto (exercise14_mean s) atTop (𝓝 l))
    {ε : ℝ} (hε : 0 < ε) :
    limsup (fun n => (‖s n - l‖ : EReal)) atTop ≤ (M * ε : ℝ) := by
  have he := EReal.tendsto_coe.mpr (exercise14_error_bound_tendsto (M := M) hs hε)
  calc
    _ ≤ limsup (fun n => (exercise14_error_bound s l M ε n : EReal)) atTop :=
      limsup_le_limsup ((exercise14_error_le (l := l) hM hε).mono
        (fun n hn => EReal.coe_le_coe_iff.mpr hn))
    _ = _ := he.limsup_eq

/-- (e) The weaker, bounded-`n a_n` Tauberian converse. -/
theorem exercise14_e_convergence {s : ℕ → ℂ} {l : ℂ} {M : ℝ}
    (hM : ∀ k : ℕ, 1 ≤ k → ‖(k : ℂ) * exercise14_diff s k‖ ≤ M)
    (hs : Tendsto (exercise14_mean s) atTop (𝓝 l)) :
    Tendsto s atTop (𝓝 l) := by
  have ht : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hupper : limsup (fun n => (‖s n - l‖ : EReal)) atTop ≤ 0 := by
    have ht' := EReal.tendsto_coe.mpr (ht.const_mul M)
    simp only [mul_zero, EReal.coe_zero] at ht'
    apply ge_of_tendsto ht'
    exact Eventually.of_forall (fun n => exercise14_e_limsup hM hs (by positivity))
  have hlower : (0 : EReal) ≤ liminf (fun n => (‖s n - l‖ : EReal)) atTop :=
    le_liminf_of_le (by isBoundedDefault)
      (Eventually.of_forall (fun n => by exact_mod_cast norm_nonneg (s n - l)))
  have hz := tendsto_of_le_liminf_of_limsup_le hlower hupper
  have hr : Tendsto (fun n => ‖s n - l‖) atTop (𝓝 (0 : ℝ)) :=
    EReal.tendsto_coe.mp (by simpa only [EReal.coe_zero] using hz)
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hr)

/-- A nondecreasing mass with sparse jumps at fourth powers. -/
def exercise14_mass (n : ℕ) : ℝ := (Nat.sqrt (Nat.sqrt n) : ℝ) ^ 2

/-- Positive spikes, plus a strictly positive sequence tending to zero. -/
def exercise14_positive (n : ℕ) : ℝ :=
  exercise14_mass n - exercise14_mass (n - 1) + 1 / (n + 1 : ℝ)

private theorem exercise14_mass_mono : Monotone exercise14_mass := by
  intro a b hab
  unfold exercise14_mass
  gcongr

/-- All terms in the construction are strictly positive. -/
theorem exercise14_positive_pos (n : ℕ) : 0 < exercise14_positive n := by
  have hm := exercise14_mass_mono (Nat.sub_le n 1)
  have hp : 0 < 1 / (n + 1 : ℝ) := by positivity
  dsimp [exercise14_positive]
  linarith

private theorem exercise14_mass_sum (n : ℕ) :
    (∑ k ∈ range (n + 1),
      (exercise14_mass k - exercise14_mass (k - 1))) = exercise14_mass n := by
  induction n with
  | zero => simp [exercise14_mass]
  | succ n ih =>
    rw [sum_range_succ, ih]
    simp

private theorem exercise14_sqrt_tendsto :
    Tendsto (fun n : ℕ => Nat.sqrt n) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with n hn
  exact Nat.le_sqrt'.mpr hn

private theorem exercise14_mass_ratio_tendsto :
    Tendsto (fun n : ℕ => exercise14_mass n / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (2 : ℝ) / (Nat.sqrt n + 1 : ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_mono (fun n => by simp only [Function.comp_def]; linarith)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp exercise14_sqrt_tendsto)
  apply squeeze_zero (fun n => by unfold exercise14_mass; positivity) _ ht
  intro n
  have hsq : (Nat.sqrt n : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hle : (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le_self n
  have hm : exercise14_mass n ≤ (Nat.sqrt n : ℝ) := by
    unfold exercise14_mass
    exact_mod_cast Nat.sqrt_le' (Nat.sqrt n)
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)
    (by positivity : (0 : ℝ) < Nat.sqrt n + 1)]
  have hmul := mul_le_mul_of_nonneg_right hm
    (by positivity : (0 : ℝ) ≤ Nat.sqrt n + 1)
  nlinarith

/-- The arithmetic means of the positive spike construction tend to zero. -/
theorem exercise14_positive_mean_zero :
    Tendsto (exercise14_mean (fun n => (exercise14_positive n : ℂ))) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hav := hbase.cesaro.comp (tendsto_add_atTop_nat 1)
  have ht := (exercise14_mass_ratio_tendsto.add hav).ofReal
  have he : ∀ n : ℕ, exercise14_mean (fun n => (exercise14_positive n : ℂ)) n =
      ((exercise14_mass n / (n + 1 : ℝ) +
        (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range (n + 1), 1 / (i + 1 : ℝ))) : ℝ) := by
    intro n
    unfold exercise14_mean exercise14_positive
    simp only [Complex.ofReal_add, sum_add_distrib]
    have hs : (∑ k ∈ range (n + 1),
        ((exercise14_mass k - exercise14_mass (k - 1) : ℝ) : ℂ)) =
        (exercise14_mass n : ℂ) := by
      rw [← Complex.ofReal_sum, exercise14_mass_sum]
    rw [hs]
    push_cast
    ring
  change Tendsto (fun n => exercise14_mean (fun n => (exercise14_positive n : ℂ)) n)
    atTop (𝓝 0)
  simp_rw [he]
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_zero,
    Complex.ofReal_zero] using ht

/-- The term at `(k+1)^4` is at least `2k+1`. -/
theorem exercise14_positive_spike (k : ℕ) :
    (2 * k + 1 : ℝ) ≤ exercise14_positive ((k + 1) ^ 4) := by
  have he : (k + 1) ^ 4 = ((k + 1) ^ 2) ^ 2 := by ring
  have hcur : exercise14_mass ((k + 1) ^ 4) = (k + 1 : ℝ) ^ 2 := by
    unfold exercise14_mass
    rw [he, Nat.sqrt_eq', Nat.sqrt_eq']
    push_cast
    rfl
  have hp : 0 < (k + 1) ^ 4 := by positivity
  have hlt : Nat.sqrt (Nat.sqrt ((k + 1) ^ 4 - 1)) < k + 1 := by
    apply Nat.sqrt_lt'.mpr
    apply Nat.sqrt_lt'.mpr
    rw [← he]
    omega
  have hprev : exercise14_mass ((k + 1) ^ 4 - 1) ≤ (k : ℝ) ^ 2 := by
    unfold exercise14_mass
    gcongr
    exact_mod_cast (show Nat.sqrt (Nat.sqrt ((k + 1) ^ 4 - 1)) ≤ k by omega)
  have hpos : 0 < 1 / (((k + 1) ^ 4 : ℕ) + 1 : ℝ) := by positivity
  unfold exercise14_positive
  rw [hcur]
  nlinarith

/-- The upper limit of the positive sequence is positive infinity. -/
theorem exercise14_positive_limsup :
    limsup (fun n => (exercise14_positive n : EReal)) atTop = ⊤ := by
  have hidx : Tendsto (fun k : ℕ => (k + 1) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by decide : 4 ≠ 0)).comp (tendsto_add_atTop_nat 1)
  have hsp : Tendsto (fun k => exercise14_positive ((k + 1) ^ 4)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) _
      (tendsto_natCast_atTop_atTop (R := ℝ))
    intro k
    have := exercise14_positive_spike k
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have he := (EReal.tendsto_coe_atTop.comp hsp).limsup_eq
  apply top_unique
  rw [← he]
  exact hidx.limsup_comp_le_limsup (u := fun n => (exercise14_positive n : EReal))

/-- (c) Yes: the sequence is positive and has infinite upper limit, but its
complex arithmetic means tend to zero. -/
theorem exercise14_c : ∃ s : ℕ → ℝ,
    (∀ n, 0 < s n) ∧
    limsup (fun n => (s n : EReal)) atTop = ⊤ ∧
    Tendsto (exercise14_mean (fun n => (s n : ℂ))) atTop (𝓝 0) :=
  ⟨exercise14_positive, exercise14_positive_pos, exercise14_positive_limsup,
    exercise14_positive_mean_zero⟩

/-- (b) An actual complex sequence with means tending to zero need not converge. -/
theorem exercise14_b : ∃ s : ℕ → ℂ,
    (¬ ∃ l : ℂ, Tendsto s atTop (𝓝 l)) ∧
    Tendsto (exercise14_mean s) atTop (𝓝 0) := by
  refine ⟨fun n => (exercise14_positive n : ℂ), ?_, exercise14_positive_mean_zero⟩
  rintro ⟨l, hl⟩
  have hr : Tendsto exercise14_positive atTop (𝓝 l.re) := by
    change Tendsto (fun n => exercise14_positive n) atTop (𝓝 l.re)
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto l).comp hl
  have he := (EReal.tendsto_coe.mpr hr).limsup_eq
  rw [exercise14_positive_limsup] at he
  exact EReal.coe_ne_top l.re he.symm

end
end Rudin.Chapter03
