module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

namespace Rudin.Chapter05

open Set Filter

noncomputable def exercise19_secant (f : ℝ → ℝ) (α β : ℕ → ℝ) (n : ℕ) : ℝ :=
  (f (β n) - f (α n)) / (β n - α n)

/-- A common sufficient condition behind parts (a) and (b). -/
theorem exercise19_bounded_ratio {f : ℝ → ℝ} {L : ℝ} {α β : ℕ → ℝ}
    (hf : HasDerivAt f L 0) (hα : Tendsto α atTop (nhds 0))
    (hβ : Tendsto β atTop (nhds 0)) (hab : ∀ n, α n < β n)
    (ha : ∀ n, α n ≠ 0) (hb : ∀ n, β n ≠ 0)
    (hr : ∃ C : ℝ, ∀ n, |β n / (β n - α n)| ≤ C) :
    Tendsto (exercise19_secant f α β) atTop (nhds L) := by
  rcases hr with ⟨C, hC⟩
  have hsa := hf.tendsto_slope.comp (tendsto_nhdsWithin_iff.2
    ⟨hα, Eventually.of_forall (fun n => by simpa using ha n)⟩)
  have hsb := hf.tendsto_slope.comp (tendsto_nhdsWithin_iff.2
    ⟨hβ, Eventually.of_forall (fun n => by simpa using hb n)⟩)
  have hsα : Tendsto (fun n => (f (α n) - f 0) / α n - L) atTop (nhds 0) := by
    simpa [slope_def_field] using hsa.sub_const L
  have hsβ : Tendsto (fun n => (f (β n) - f 0) / β n - L) atTop (nhds 0) := by
    simpa [slope_def_field] using hsb.sub_const L
  have hCa : ∀ n, |α n / (β n - α n)| ≤ C + 1 := by
    intro n
    have hn : β n - α n ≠ 0 := ne_of_gt (sub_pos.mpr (hab n))
    have he : α n / (β n - α n) = β n / (β n - α n) - 1 := by field_simp; ring
    rw [he]
    exact (abs_sub _ _).trans (by simpa using add_le_add_right (hC n) 1)
  have hpβ := bdd_le_mul_tendsto_zero' C (Eventually.of_forall hC) hsβ
  have hpα := bdd_le_mul_tendsto_zero' (C + 1) (Eventually.of_forall hCa) hsα
  have hh := (hpβ.sub hpα).add_const L
  convert hh using 1
  · ext n
    dsimp [exercise19_secant]
    field_simp [ha n, hb n, ne_of_gt (sub_pos.mpr (hab n))]
    ring
  · simp

/-- Rudin 5.19(a): intervals which straddle zero. -/
theorem exercise19_a {f : ℝ → ℝ} {L : ℝ} {α β : ℕ → ℝ}
    (hf : HasDerivAt f L 0) (hα : Tendsto α atTop (nhds 0))
    (hβ : Tendsto β atTop (nhds 0))
    (_hdomain : ∀ n, -1 < α n ∧ β n < 1)
    (ha : ∀ n, α n < 0) (hb : ∀ n, 0 < β n) :
    Tendsto (exercise19_secant f α β) atTop (nhds L) := by
  apply exercise19_bounded_ratio hf hα hβ
    (fun n => (ha n).trans (hb n)) (fun n => ne_of_lt (ha n))
    (fun n => ne_of_gt (hb n))
  refine ⟨1, fun n => ?_⟩
  have hn : 0 < β n - α n := by linarith [ha n, hb n]
  rw [abs_of_pos (div_pos (hb n) hn), div_le_one hn]
  linarith [ha n]

/-- Rudin 5.19(b): positive endpoints with the stated bounded ratio. -/
theorem exercise19_b {f : ℝ → ℝ} {L : ℝ} {α β : ℕ → ℝ}
    (hf : HasDerivAt f L 0) (hα : Tendsto α atTop (nhds 0))
    (hβ : Tendsto β atTop (nhds 0))
    (ha : ∀ n, 0 < α n) (hab : ∀ n, α n < β n) (_hb : ∀ n, β n < 1)
    (hr : ∃ C : ℝ, ∀ n, β n / (β n - α n) ≤ C) :
    Tendsto (exercise19_secant f α β) atTop (nhds L) := by
  apply exercise19_bounded_ratio hf hα hβ hab
    (fun n => ne_of_gt (ha n)) (fun n => ne_of_gt ((ha n).trans (hab n)))
  rcases hr with ⟨C, hC⟩
  exact ⟨C, fun n => by rw [abs_of_pos (div_pos ((ha n).trans (hab n))
    (sub_pos.mpr (hab n)))]; exact hC n⟩

/-- Rudin 5.19(c). Derivative existence is explicit; totalized `deriv`
    alone is not a differentiability hypothesis. -/
theorem exercise19_c_at_zero {f : ℝ → ℝ} {α β : ℕ → ℝ}
    (hf : DifferentiableOn ℝ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousAt (deriv f) 0)
    (hα : Tendsto α atTop (nhds 0)) (hβ : Tendsto β atTop (nhds 0))
    (hdomain : ∀ n, -1 < α n ∧ α n < β n ∧ β n < 1) :
    Tendsto (exercise19_secant f α β) atTop (nhds (deriv f 0)) := by
  have hm : ∀ n, ∃ c ∈ Ioo (α n) (β n), deriv f c = exercise19_secant f α β n := by
    intro n
    apply exists_deriv_eq_slope f (hdomain n).2.1
    · exact hf.continuousOn.mono (fun x hx => ⟨(hdomain n).1.trans_le hx.1,
        hx.2.trans_lt (hdomain n).2.2⟩)
    · exact hf.mono (fun x hx => ⟨(hdomain n).1.trans hx.1,
        hx.2.trans (hdomain n).2.2⟩)
  choose c hcm hce using hm
  have hcl : Tendsto c atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hα hβ
      (fun n => (hcm n).1.le) (fun n => (hcm n).2.le)
  exact (hc.tendsto.comp hcl).congr hce

/-- The continuity assumption printed in part (c) implies continuity at zero. -/
theorem exercise19_c {f : ℝ → ℝ} {α β : ℕ → ℝ}
    (hf : DifferentiableOn ℝ f (Ioo (-1 : ℝ) 1))
    (hc : ContinuousOn (deriv f) (Ioo (-1 : ℝ) 1))
    (hα : Tendsto α atTop (nhds 0)) (hβ : Tendsto β atTop (nhds 0))
    (hdomain : ∀ n, -1 < α n ∧ α n < β n ∧ β n < 1) :
    Tendsto (exercise19_secant f α β) atTop (nhds (deriv f 0)) :=
  exercise19_c_at_zero hf
    ((hc 0 (by norm_num)).continuousAt (isOpen_Ioo.mem_nhds (by norm_num))) hα hβ hdomain

/-- A differentiable function with an oscillating derivative near zero. -/
noncomputable def exercise19_example (x : ℝ) : ℝ := x ^ 2 * Real.sin (1 / x)

noncomputable def exercise19_phase (n : ℕ) : ℝ := (n + 1 : ℕ) * (2 * Real.pi)
noncomputable def exercise19_alpha (n : ℕ) : ℝ := 1 / (exercise19_phase n + Real.pi / 2)
noncomputable def exercise19_beta (n : ℕ) : ℝ := 1 / exercise19_phase n

theorem exercise19_example_derivative_zero : HasDerivAt exercise19_example 0 0 := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with x hx
  simp only [exercise19_example, zero_pow (by decide : 2 ≠ 0), zero_mul,
    sub_zero, smul_zero, Real.norm_eq_abs, abs_mul, abs_pow]
  change dist x 0 < ε at hx
  rw [Real.dist_eq, sub_zero] at hx
  have hsin := Real.abs_sin_le_one (1 / x)
  calc
    |x| ^ 2 * |Real.sin (1 / x)| ≤ |x| ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hsin (sq_nonneg _)
    _ ≤ ε * |x| := by nlinarith [abs_nonneg x]

theorem exercise19_example_differentiable : Differentiable ℝ exercise19_example := by
  intro x
  by_cases hx : x = 0
  · subst x; exact exercise19_example_derivative_zero.differentiableAt
  · change DifferentiableAt ℝ (fun x : ℝ => x ^ 2 * Real.sin (1 / x)) x
    fun_prop (disch := assumption)

theorem exercise19_example_endpoints (n : ℕ) :
    -1 < exercise19_alpha n ∧ exercise19_alpha n < exercise19_beta n ∧
      exercise19_beta n < 1 ∧ 0 < exercise19_alpha n := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hp : 1 < exercise19_phase n := by
    dsimp [exercise19_phase]
    nlinarith [Real.pi_gt_three]
  have hpi := Real.pi_pos
  dsimp [exercise19_alpha, exercise19_beta]
  have hα : 0 < 1 / (exercise19_phase n + Real.pi / 2) := by positivity
  exact ⟨by linarith, one_div_lt_one_div_of_lt (by positivity) (by linarith),
    (div_lt_one (by positivity)).2 hp, hα⟩

theorem exercise19_example_endpoint_limits :
    Tendsto exercise19_alpha atTop (nhds 0) ∧ Tendsto exercise19_beta atTop (nhds 0) := by
  have ht : Tendsto exercise19_phase atTop atTop := by
    change Tendsto (fun n : ℕ => (n + 1 : ℕ) * (2 * Real.pi)) atTop atTop
    exact Filter.Tendsto.atTop_mul_const (by positivity : 0 < 2 * Real.pi)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  constructor
  · change Tendsto (fun n => 1 / (exercise19_phase n + Real.pi / 2)) atTop (nhds 0)
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun n => le_add_of_nonneg_right (by positivity : 0 ≤ Real.pi / 2)) ht)
  · change Tendsto (fun n => 1 / exercise19_phase n) atTop (nhds 0)
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp ht

theorem exercise19_example_secant (n : ℕ) :
    exercise19_secant exercise19_example exercise19_alpha exercise19_beta n =
      -(1 - Real.pi / 2 * exercise19_alpha n) / (Real.pi / 2) := by
  have hp : exercise19_phase n ≠ 0 := by
    dsimp [exercise19_phase]
    positivity
  have hq : exercise19_phase n + Real.pi / 2 ≠ 0 := by
    dsimp [exercise19_phase]
    positivity
  have hdiff : exercise19_beta n - exercise19_alpha n ≠ 0 :=
    ne_of_gt (sub_pos.mpr (exercise19_example_endpoints n).2.1)
  have hs : Real.sin (exercise19_phase n) = 0 := by
    simpa [exercise19_phase] using Real.sin_add_nat_mul_two_pi 0 (n + 1)
  have hs' : Real.sin (exercise19_phase n + Real.pi / 2) = 1 := by
    rw [add_comm]
    simpa [exercise19_phase] using Real.sin_add_nat_mul_two_pi (Real.pi / 2) (n + 1)
  rw [exercise19_secant, div_eq_iff hdiff]
  dsimp [exercise19_example, exercise19_alpha, exercise19_beta]
  rw [one_div_one_div, one_div_one_div, hs, hs']
  have hc : Real.pi / 2 ≠ 0 := by positivity
  generalize Real.pi / 2 = c at *
  field_simp [hp, hq, hc]; ring

/-- The secants have the finite limit -2/pi, whereas f'(0)=0. Thus none
    of the additional conditions can be omitted in general. -/
theorem exercise19_different_limit :
    DifferentiableOn ℝ exercise19_example (Ioo (-1 : ℝ) 1) ∧
    HasDerivAt exercise19_example 0 0 ∧
    (∀ n, -1 < exercise19_alpha n ∧ exercise19_alpha n < exercise19_beta n ∧
      exercise19_beta n < 1) ∧
    Tendsto exercise19_alpha atTop (nhds 0) ∧
    Tendsto exercise19_beta atTop (nhds 0) ∧
    Tendsto (exercise19_secant exercise19_example exercise19_alpha exercise19_beta)
      atTop (nhds (-2 / Real.pi)) ∧
    -2 / Real.pi ≠ 0 ∧
    ¬ ContinuousAt (deriv exercise19_example) 0 := by
  have hl : Tendsto (exercise19_secant exercise19_example exercise19_alpha exercise19_beta)
      atTop (nhds (-2 / Real.pi)) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (exercise19_example_endpoint_limits.1.const_mul (Real.pi / 2))).neg).div_const (Real.pi / 2)
    convert hh.congr (fun n => (exercise19_example_secant n).symm) using 1
    simp
    ring
  have hn : -2 / Real.pi ≠ (0 : ℝ) := div_ne_zero (by norm_num) Real.pi_ne_zero
  have hdom : ∀ n, -1 < exercise19_alpha n ∧ exercise19_alpha n < exercise19_beta n ∧
      exercise19_beta n < 1 := fun n =>
    ⟨(exercise19_example_endpoints n).1, (exercise19_example_endpoints n).2.1,
      (exercise19_example_endpoints n).2.2.1⟩
  refine ⟨exercise19_example_differentiable.differentiableOn,
    exercise19_example_derivative_zero, hdom, exercise19_example_endpoint_limits.1,
    exercise19_example_endpoint_limits.2, hl, hn, ?_⟩
  intro hc
  have hh := exercise19_c_at_zero exercise19_example_differentiable.differentiableOn hc
    exercise19_example_endpoint_limits.1 exercise19_example_endpoint_limits.2 hdom
  have he := tendsto_nhds_unique hl hh
  rw [exercise19_example_derivative_zero.deriv] at he
  exact hn he

end Rudin.Chapter05
