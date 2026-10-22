module

public import Math.Rudin.Chapter05.Exercise20
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

namespace Rudin.Chapter05

open Set

/-- The finite-difference estimate in Rudin's hint, valid in every real normed space. -/
theorem exercise15_hint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {a M₀ M₂ x h : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : ∀ t ∈ Ioi a, ‖f t‖ ≤ M₀)
    (h₂ : ∀ t ∈ Ioi a, ‖f₂ t‖ ≤ M₂)
    (hx : a < x) (hh : 0 < h) :
    2 * h * ‖f₁ x‖ ≤ 2 * M₀ + 2 * h ^ 2 * M₂ := by
  let F : ℕ → ℝ → E := fun k => if k = 0 then f else if k = 1 then f₁ else f₂
  have hm : ∀ t ∈ uIcc x (x + 2 * h), t ∈ Ioi a := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact lt_of_lt_of_le hx ht.1
  have hr := exercise20_vector_taylor_bound 2 F
    (fun k hk t ht => by
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · simpa [F] using (hd t (hm t ht)).hasDerivWithinAt
      · simpa [F] using (hd₁ t (hm t ht)).hasDerivWithinAt)
    (fun t ht => by simpa [F] using h₂ t (hm t ht))
  have hr' : ‖f (x + 2 * h) - (f x + (2 * h) • f₁ x)‖ ≤ 2 * h ^ 2 * M₂ := by
    convert hr using 1 <;>
      simp [exercise20_polynomial, Finset.sum_range_succ, F, Nat.factorial,
        abs_of_pos hh]
    ring
  have he : (2 * h) • f₁ x = (f (x + 2 * h) - f x) -
      (f (x + 2 * h) - (f x + (2 * h) • f₁ x)) := by abel
  have hn := norm_sub_le (f (x + 2 * h) - f x)
    (f (x + 2 * h) - (f x + (2 * h) • f₁ x))
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * h)] at hn
  have hn' := norm_sub_le (f (x + 2 * h)) (f x)
  have hx' : x + 2 * h ∈ Ioi a := by change a < x + 2 * h; linarith
  linarith [h₀ x hx, h₀ _ hx']

private theorem exercise15_quadratic {u A B : ℝ} (hu : 0 ≤ u) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h : ∀ h : ℝ, 0 < h → 2 * h * u ≤ 2 * A + 2 * h ^ 2 * B) :
    u ^ 2 ≤ 4 * A * B := by
  by_cases hb : B = 0
  · subst B
    by_cases hz : u = 0
    · simp [hz]
    have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hh := h ((A + 1) / u) (div_pos (by positivity) hup)
    field_simp at hh
    nlinarith
  · have hbp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
    by_cases hz : u = 0
    · rw [hz, zero_pow (by decide : 2 ≠ 0)]
      positivity
    have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hh := h (u / (2 * B)) (div_pos hup (by positivity))
    field_simp at hh
    nlinarith

/-- Pointwise Landau bound. Zero bounds are included. The highest derivative
    need not be continuous. -/
theorem exercise15_pointwise_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {a M₀ M₂ : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : ∀ t ∈ Ioi a, ‖f t‖ ≤ M₀)
    (h₂ : ∀ t ∈ Ioi a, ‖f₂ t‖ ≤ M₂) :
    ∀ x ∈ Ioi a, ‖f₁ x‖ ^ 2 ≤ 4 * M₀ * M₂ := by
  intro x hx
  exact exercise15_quadratic (norm_nonneg _) ((norm_nonneg _).trans (h₀ x hx))
    ((norm_nonneg _).trans (h₂ x hx))
    (fun h hh => exercise15_hint hd hd₁ h₀ h₂ hx hh)

/-- The least-upper-bound form of Landau's inequality, also for vectors. -/
theorem exercise15_derivative_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {a M₀ M₁ M₂ : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : IsLUB ((fun t => ‖f t‖) '' Ioi a) M₀)
    (h₁ : IsLUB ((fun t => ‖f₁ t‖) '' Ioi a) M₁)
    (h₂ : IsLUB ((fun t => ‖f₂ t‖) '' Ioi a) M₂) :
    M₁ ^ 2 ≤ 4 * M₀ * M₂ := by
  have hpoint := exercise15_pointwise_bound hd hd₁
    (fun t ht => h₀.1 ⟨t, ht, rfl⟩) (fun t ht => h₂.1 ⟨t, ht, rfl⟩)
  have hnonneg : 0 ≤ M₁ := (norm_nonneg _).trans (h₁.1 ⟨a + 1, by simp, rfl⟩)
  have hprod : 0 ≤ 4 * M₀ * M₂ := (sq_nonneg _).trans (hpoint (a + 1) (by simp))
  have hle : M₁ ≤ Real.sqrt (4 * M₀ * M₂) := h₁.2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact (Real.le_sqrt (norm_nonneg _) hprod).2 (hpoint x hx))
  nlinarith [Real.sq_sqrt hprod, Real.sqrt_nonneg (4 * M₀ * M₂)]

/-- Finite bounds on f and f'' imply that the least upper bound for f'
    exists; its finiteness is a conclusion, not an additional assumption. -/
theorem exercise15_finite_supremum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {a M₀ M₂ : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : ∀ t ∈ Ioi a, ‖f t‖ ≤ M₀)
    (h₂ : ∀ t ∈ Ioi a, ‖f₂ t‖ ≤ M₂) :
    ∃ M₁ : ℝ, IsLUB ((fun t => ‖f₁ t‖) '' Ioi a) M₁ ∧
      M₁ ^ 2 ≤ 4 * M₀ * M₂ := by
  have hp := exercise15_pointwise_bound hd hd₁ h₀ h₂
  have hprod : 0 ≤ 4 * M₀ * M₂ := (sq_nonneg _).trans (hp (a + 1) (by simp))
  have hbound : BddAbove ((fun t => ‖f₁ t‖) '' Ioi a) := by
    refine ⟨Real.sqrt (4 * M₀ * M₂), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (Real.le_sqrt (norm_nonneg _) hprod).2 (hp t ht)
  have hne : (((fun t => ‖f₁ t‖) '' Ioi a)).Nonempty :=
    ⟨_, ⟨a + 1, by simp, rfl⟩⟩
  have hl := isLUB_csSup hne hbound
  refine ⟨_, hl, ?_⟩
  have hlo : 0 ≤ sSup ((fun t => ‖f₁ t‖) '' Ioi a) :=
    (norm_nonneg _).trans (hl.1 ⟨a + 1, by simp, rfl⟩)
  have hhi : sSup ((fun t => ‖f₁ t‖) '' Ioi a) ≤ Real.sqrt (4 * M₀ * M₂) :=
    hl.2 (by
      rintro _ ⟨t, ht, rfl⟩
      exact (Real.le_sqrt (norm_nonneg _) hprod).2 (hp t ht))
  nlinarith [Real.sq_sqrt hprod, Real.sqrt_nonneg (4 * M₀ * M₂)]

/-- Either zero bound forces the first derivative to vanish. -/
theorem exercise15_zero_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f₁ f₂ : ℝ → E} {a M₀ M₂ : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : ∀ t ∈ Ioi a, ‖f t‖ ≤ M₀)
    (h₂ : ∀ t ∈ Ioi a, ‖f₂ t‖ ≤ M₂) (hz : M₀ = 0 ∨ M₂ = 0) :
    ∀ x ∈ Ioi a, f₁ x = 0 := by
  intro x hx
  have h := exercise15_pointwise_bound hd hd₁ h₀ h₂ x hx
  have hn := norm_nonneg (f₁ x)
  apply norm_eq_zero.mp
  rcases hz with hz | hz <;> rw [hz] at h <;> nlinarith

/-- In particular, the answer to the vector-valued question is yes. -/
theorem exercise15_vector_version {k : ℕ} {f f₁ f₂ : ℝ → EuclideanSpace ℝ (Fin k)}
    {a M₀ M₁ M₂ : ℝ}
    (hd : ∀ t ∈ Ioi a, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ Ioi a, HasDerivAt f₁ (f₂ t) t)
    (h₀ : IsLUB ((fun t => ‖f t‖) '' Ioi a) M₀)
    (h₁ : IsLUB ((fun t => ‖f₁ t‖) '' Ioi a) M₁)
    (h₂ : IsLUB ((fun t => ‖f₂ t‖) '' Ioi a) M₂) :
    M₁ ^ 2 ≤ 4 * M₀ * M₂ :=
  exercise15_derivative_bound hd hd₁ h₀ h₁ h₂

/-- The source's sharp example, extended outside its stated domain only to
    use ordinary functions. All supremum statements use exactly (-1,infinity). -/
noncomputable def exercise15_example (x : ℝ) : ℝ :=
  if x < 0 then 2 * x ^ 2 - 1 else (x ^ 2 - 1) / (x ^ 2 + 1)
noncomputable def exercise15_example₁ (x : ℝ) : ℝ :=
  if x < 0 then 4 * x else 4 * x / (x ^ 2 + 1) ^ 2
noncomputable def exercise15_example₂ (x : ℝ) : ℝ :=
  if x < 0 then 4 else 4 * (1 - 3 * x ^ 2) / (x ^ 2 + 1) ^ 3

private theorem exercise15_glue {l r l' r' : ℝ → ℝ}
    (hl : ∀ x, HasDerivAt l (l' x) x) (hr : ∀ x, HasDerivAt r (r' x) x)
    (he : l 0 = r 0) (he' : l' 0 = r' 0) :
    ∀ x : ℝ, HasDerivAt (fun t => if t < 0 then l t else r t)
      (if x < 0 then l' x else r' x) x := by
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [ite_eq_left hx]
    apply (hl x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with t ht
    change t < 0 at ht
    simp [ht]
  · have hleft : HasDerivWithinAt (fun t => if t < 0 then l t else r t)
        (r' 0) (Iic 0) 0 := by
      rw [← he']
      apply (hl 0).hasDerivWithinAt.congr
      · intro t ht
        by_cases hn : t < 0
        · simp [hn]
        · have : t = 0 := le_antisymm ht (le_of_not_gt hn)
          subst t; simpa using he.symm
      · simpa using he.symm
    have hright : HasDerivWithinAt (fun t => if t < 0 then l t else r t)
        (r' 0) (Ici 0) 0 := by
      apply (hr 0).hasDerivWithinAt.congr
      · intro t ht; simp [not_lt_of_ge ht]
      · simp
    simpa [← hasDerivWithinAt_univ, Iic_union_Ici] using hleft.union hright
  · rw [ite_eq_right (not_lt_of_gt hx)]
    apply (hr x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp [not_lt_of_gt ht]

private theorem exercise15_right_derivatives (x : ℝ) :
    HasDerivAt (fun x : ℝ => (x ^ 2 - 1) / (x ^ 2 + 1))
      (4 * x / (x ^ 2 + 1) ^ 2) x ∧
    HasDerivAt (fun x : ℝ => 4 * x / (x ^ 2 + 1) ^ 2)
      (4 * (1 - 3 * x ^ 2) / (x ^ 2 + 1) ^ 3) x := by
  have hn : x ^ 2 + 1 ≠ 0 := by positivity
  constructor
  · convert (((hasDerivAt_id x).fun_pow 2).sub_const 1).div
      (((hasDerivAt_id x).fun_pow 2).add_const 1) hn using 1
    · rfl
    · norm_num
      field_simp [hn]
      ring
  · convert ((hasDerivAt_id x).const_mul 4).div
      ((((hasDerivAt_id x).fun_pow 2).add_const 1).fun_pow 2) (pow_ne_zero 2 hn) using 1
    · rfl
    · norm_num
      field_simp [hn]
      ring

/-- Both derivatives exist, including the join at zero. -/
theorem exercise15_example_regular :
    (∀ x : ℝ, HasDerivAt exercise15_example (exercise15_example₁ x) x) ∧
    (∀ x : ℝ, HasDerivAt exercise15_example₁ (exercise15_example₂ x) x) := by
  constructor
  · apply exercise15_glue (l := fun x => 2 * x ^ 2 - 1)
      (r := fun x => (x ^ 2 - 1) / (x ^ 2 + 1))
      (l' := fun x => 4 * x) (r' := fun x => 4 * x / (x ^ 2 + 1) ^ 2)
    · intro x
      convert (((hasDerivAt_id x).fun_pow 2).const_mul 2).sub_const 1 using 1
      · rfl
      · norm_num; ring
    · exact fun x => (exercise15_right_derivatives x).1
    · norm_num
    · norm_num
  · apply exercise15_glue (l := fun x => 4 * x)
      (r := fun x => 4 * x / (x ^ 2 + 1) ^ 2)
      (l' := fun _ => 4) (r' := fun x => 4 * (1 - 3 * x ^ 2) / (x ^ 2 + 1) ^ 3)
    · intro x; simpa using (hasDerivAt_id x).const_mul 4
    · exact fun x => (exercise15_right_derivatives x).2
    · norm_num
    · norm_num

 theorem exercise15_example_bounds :
    (∀ x ∈ Ioi (-1 : ℝ), |exercise15_example x| ≤ 1) ∧
    (∀ x ∈ Ioi (-1 : ℝ), |exercise15_example₁ x| ≤ 4) ∧
    (∀ x ∈ Ioi (-1 : ℝ), |exercise15_example₂ x| ≤ 4) := by
  constructor
  · intro x hx
    change -1 < x at hx
    dsimp [exercise15_example]
    split_ifs with hn
    · rw [abs_le]; constructor <;> nlinarith
    · rw [abs_le, le_div_iff₀ (by positivity : 0 < x ^ 2 + 1),
        div_le_iff₀ (by positivity : 0 < x ^ 2 + 1)]
      constructor <;> nlinarith [sq_nonneg x]
  constructor
  · intro x hx
    change -1 < x at hx
    dsimp [exercise15_example₁]
    split_ifs with hn
    · rw [abs_of_neg (by linarith : 4 * x < 0)]; linarith
    · have hx₀ : 0 ≤ x := le_of_not_gt hn
      rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity : 0 < (x ^ 2 + 1) ^ 2)]
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x ^ 2)]
  · intro x hx
    dsimp [exercise15_example₂]
    split_ifs with hn
    · norm_num
    · rw [abs_le, le_div_iff₀ (by positivity : 0 < (x ^ 2 + 1) ^ 3),
        div_le_iff₀ (by positivity : 0 < (x ^ 2 + 1) ^ 3)]
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg (x ^ 2),
        pow_nonneg (sq_nonneg x) 3]

 theorem exercise15_example_function_supremum :
    IsLUB ((fun x => |exercise15_example x|) '' Ioi (-1 : ℝ)) 1 := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩; exact exercise15_example_bounds.1 x hx
  · intro C hC
    have h := hC ⟨0, by norm_num, rfl⟩
    simpa [exercise15_example] using h

 theorem exercise15_example_derivative_supremum :
    IsLUB ((fun x => |exercise15_example₁ x|) '' Ioi (-1 : ℝ)) 4 := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩; exact exercise15_example_bounds.2.1 x hx
  · intro C hC
    have hC₀ : 0 ≤ C := by
      have h := hC ⟨0, by norm_num, rfl⟩
      simpa [exercise15_example₁] using h
    by_contra hn
    have hC₄ : C < 4 := lt_of_not_ge hn
    let x := -(C + 4) / 8
    have hx : x ∈ Ioi (-1 : ℝ) := by dsimp [x]; change -1 < -(C + 4) / 8; linarith
    have hx₀ : x < 0 := by dsimp [x]; linarith
    have h := hC ⟨x, hx, rfl⟩
    simp only [exercise15_example₁, ite_eq_left hx₀, abs_of_neg (by linarith : 4 * x < 0)] at h
    dsimp [x] at h
    linarith

 theorem exercise15_example_second_derivative_supremum :
    IsLUB ((fun x => |exercise15_example₂ x|) '' Ioi (-1 : ℝ)) 4 := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩; exact exercise15_example_bounds.2.2 x hx
  · intro C hC
    have h := hC ⟨0, by norm_num, rfl⟩
    simpa [exercise15_example₂] using h

 theorem exercise15_example_sharpness : (4 : ℝ) ^ 2 = 4 * 1 * 4 := by norm_num

end Rudin.Chapter05
