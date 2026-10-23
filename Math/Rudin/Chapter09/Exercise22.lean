module

public import Math.Rudin.Chapter09.Exercise21

/-! # Exercise 22: the nodal cubic
Source: Rudin, book 242 (PDF 251). Graph predicates refer to the full local zero
set, including both branches at the node.
-/
@[expose] public section
open Set Filter
open scoped Topology
namespace Rudin.Chapter09

noncomputable def exercise22Function (p : ℝ × ℝ) : ℝ :=
  2 * p.1 ^ 3 + 6 * p.1 * p.2 ^ 2 - 3 * p.1 ^ 2 + 3 * p.2 ^ 2

theorem exercise22_smooth : ContDiff ℝ ⊤ exercise22Function := by
  unfold exercise22Function; fun_prop

theorem exercise22_partials (x y : ℝ) :
    HasDerivAt (fun t => exercise22Function (t, y)) (6 * (x ^ 2 + y ^ 2 - x)) x ∧
    HasDerivAt (fun t => exercise22Function (x, t)) (6 * y * (2 * x + 1)) y := by
  constructor
  · convert (((((hasDerivAt_id x).pow 3).const_mul 2).add
      ((hasDerivAt_id x).const_mul (6 * y ^ 2))).sub
      (((hasDerivAt_id x).pow 2).const_mul 3)).add_const (3 * y ^ 2) using 1
    · ext t; dsimp [exercise22Function]; ring
    · simp only [id_eq]; ring
  · convert (((hasDerivAt_id y).pow 2).const_mul (6 * x + 3)).add_const
      (2 * x ^ 3 - 3 * x ^ 2) using 1
    · ext t; dsimp [exercise22Function]; ring
    · simp only [id_eq]; ring

theorem exercise22_stationary (x y : ℝ) :
    (deriv (fun t => exercise22Function (t, y)) x = 0 ∧
      deriv (fun t => exercise22Function (x, t)) y = 0) ↔
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) := by
  rw [(exercise22_partials x y).1.deriv, (exercise22_partials x y).2.deriv]
  constructor
  · rintro ⟨hx, hy⟩
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hy with h | h
      · nlinarith
      · nlinarith [sq_nonneg y]
    subst y
    have he : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨by linarith, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem exercise22_saddle : Saddle exercise22Function (0, 0) := by
  apply saddle_of_curves (p := fun t => (t, 0)) (q := fun t => (0, t))
  · exact continuousAt_id.prodMk continuousAt_const
  · exact continuousAt_const.prodMk continuousAt_id
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
  filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  have hs := sq_pos_of_ne_zero hn
  have h1 := mul_pos hs (show 0 < 3 - 2 * t by linarith)
  dsimp [exercise22Function]
  constructor <;> nlinarith

theorem exercise22_min_increment (x y : ℝ) :
    exercise22Function (x, y) - exercise22Function (1, 0) =
      (x - 1) ^ 2 * (2 * x + 1) + y ^ 2 * (6 * x + 3) := by
  unfold exercise22Function; ring

theorem exercise22_minimum : IsLocalMin exercise22Function (1, 0) ∧
    ∀ᶠ p in 𝓝[≠] ((1, 0) : ℝ × ℝ), exercise22Function (1, 0) < exercise22Function p := by
  have hb : ∀ᶠ p : ℝ × ℝ in 𝓝 (1, 0), 0 < 2 * p.1 + 1 ∧ 0 < 6 * p.1 + 3 :=
    ((isOpen_lt continuous_const (by fun_prop : Continuous (fun p : ℝ × ℝ => 2 * p.1 + 1))).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous (fun p : ℝ × ℝ => 6 * p.1 + 3)))).mem_nhds
        (by norm_num)
  constructor
  · filter_upwards [hb] with p hp
    have he := exercise22_min_increment p.1 p.2
    have h1 := mul_nonneg (sq_nonneg (p.1 - 1)) hp.1.le
    have h2 := mul_nonneg (sq_nonneg p.2) hp.2.le
    change exercise22Function (1, 0) ≤ exercise22Function (p.1, p.2)
    linarith
  · filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hp hn
    have he := exercise22_min_increment p.1 p.2
    have h1 := mul_nonneg (sq_nonneg (p.1 - 1)) hp.1.le
    have h2 := mul_nonneg (sq_nonneg p.2) hp.2.le
    have hne : p.1 ≠ 1 ∨ p.2 ≠ 0 := by
      by_contra! h; exact hn (Prod.ext h.1 h.2)
    change exercise22Function (1, 0) < exercise22Function (p.1, p.2)
    rcases hne with h | h
    · have := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) hp.1; linarith
    · have := mul_pos (sq_pos_of_ne_zero h) hp.2; linarith

theorem exercise22_extrema (x y : ℝ) :
    (IsLocalMin exercise22Function (x, y) ↔ x = 1 ∧ y = 0) ∧
    ¬ IsLocalMax exercise22Function (x, y) := by
  have crit (h : IsLocalMin exercise22Function (x, y) ∨ IsLocalMax exercise22Function (x, y)) :
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) := by
    apply (exercise22_stationary x y).mp
    rcases h with h | h
    · exact ⟨(h.comp_continuous (g := fun t : ℝ => (t, y))
          (continuousAt_id.prodMk continuousAt_const)).deriv_eq_zero,
        (h.comp_continuous (g := fun t : ℝ => (x, t))
          (continuousAt_const.prodMk continuousAt_id)).deriv_eq_zero⟩
    · exact ⟨(h.comp_continuous (g := fun t : ℝ => (t, y))
          (continuousAt_id.prodMk continuousAt_const)).deriv_eq_zero,
        (h.comp_continuous (g := fun t : ℝ => (x, t))
          (continuousAt_const.prodMk continuousAt_id)).deriv_eq_zero⟩
  have notmax : ¬ IsLocalMax exercise22Function (1, 0) := by
    intro h
    have hh := (h.filter_mono nhdsWithin_le_nhds).and exercise22_minimum.2
    obtain ⟨p, hp, hq⟩ := hh.exists
    exact (not_lt_of_ge hp) hq
  constructor
  · constructor
    · intro h
      rcases crit (Or.inl h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact False.elim ((saddle_not_extremum exercise22_saddle).1 h)
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact exercise22_minimum.1
  · intro h
    rcases crit (Or.inr h) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (saddle_not_extremum exercise22_saddle).2 h
    · exact notmax h

/-- The exact horizontal range and the two square-root branches. -/
theorem exercise22_zero_set (x y : ℝ) :
    exercise22Function (x, y) = 0 ↔
      -1 / 2 < x ∧ x ≤ 3 / 2 ∧ y ^ 2 = x ^ 2 * (3 - 2 * x) / (3 + 6 * x) := by
  constructor
  · intro hz
    have he : x ^ 2 * (3 - 2 * x) = (3 + 6 * x) * y ^ 2 := by
      dsimp [exercise22Function] at hz; nlinarith
    have hx : -1 / 2 < x := by
      by_contra! hx
      have hs : 0 < x ^ 2 := sq_pos_of_ne_zero (by linarith)
      have h1 := mul_pos hs (show 0 < 3 - 2 * x by linarith)
      have h2 := mul_nonpos_of_nonpos_of_nonneg (show 3 + 6 * x ≤ 0 by linarith) (sq_nonneg y)
      linarith
    have hx' : x ≤ 3 / 2 := by
      by_contra! hx'
      have h1 := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (show x ≠ 0 by linarith))
        (show 3 - 2 * x < 0 by linarith)
      have h2 := mul_nonneg (show 0 ≤ 3 + 6 * x by linarith) (sq_nonneg y)
      linarith
    refine ⟨hx, hx', ?_⟩
    apply (eq_div_iff (by linarith : 3 + 6 * x ≠ 0)).mpr
    nlinarith
  · rintro ⟨hx, _, he⟩
    have he := (eq_div_iff (by linarith : 3 + 6 * x ≠ 0)).mp he
    dsimp [exercise22Function]
    nlinarith

theorem exercise22_branches (x y : ℝ) :
    exercise22Function (x, y) = 0 ↔
      -1 / 2 < x ∧ x ≤ 3 / 2 ∧
      (y = Real.sqrt (x ^ 2 * (3 - 2 * x) / (3 + 6 * x)) ∨
       y = -Real.sqrt (x ^ 2 * (3 - 2 * x) / (3 + 6 * x))) := by
  rw [exercise22_zero_set]
  constructor
  · rintro ⟨hx, hx', hy⟩
    have hs : 0 ≤ x ^ 2 * (3 - 2 * x) / (3 + 6 * x) := by rw [← hy]; positivity
    exact ⟨hx, hx', (sq_eq_sq_iff_eq_or_eq_neg).mp (hy.trans (Real.sq_sqrt hs).symm)⟩
  · rintro ⟨hx, hx', hy⟩
    have hs : 0 ≤ x ^ 2 * (3 - 2 * x) / (3 + 6 * x) :=
      div_nonneg (mul_nonneg (sq_nonneg x) (by linarith)) (by linarith)
    rcases hy with rfl | rfl <;> simp [Real.sq_sqrt hs, hx, hx']

/-- Rational parametrization of the entire cubic, including the node twice. -/
noncomputable def exercise22Param (t : ℝ) : ℝ × ℝ :=
  (3 * (1 - t ^ 2) / (2 + 6 * t ^ 2), t * (3 * (1 - t ^ 2) / (2 + 6 * t ^ 2)))

theorem exercise22_param_zero (t : ℝ) : exercise22Function (exercise22Param t) = 0 := by
  have hd : 2 + 6 * t ^ 2 ≠ 0 := by positivity
  dsimp [exercise22Function, exercise22Param]
  field_simp
  ring

theorem exercise22_param_surjective (x y : ℝ) :
    exercise22Function (x, y) = 0 ↔ ∃ t, exercise22Param t = (x, y) := by
  constructor
  · intro hz
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by dsimp [exercise22Function] at hz; nlinarith [sq_nonneg y]
      subst y; exact ⟨1, by norm_num [exercise22Param]⟩
    · refine ⟨y / x, ?_⟩
      have hd : 2 + 6 * (y / x) ^ 2 ≠ 0 := by positivity
      have he : 3 * (1 - (y / x) ^ 2) / (2 + 6 * (y / x) ^ 2) = x := by
        apply (div_eq_iff hd).mpr
        field_simp
        dsimp [exercise22Function] at hz
        nlinarith
      simp [exercise22Param, he, hx]
  · rintro ⟨t, ht⟩; rw [← ht]; exact exercise22_param_zero t

theorem exercise22_singular (x y : ℝ) :
    (exercise22Function (x, y) = 0 ∧
      deriv (fun t => exercise22Function (t, y)) x = 0 ∧
      deriv (fun t => exercise22Function (x, t)) y = 0) ↔ x = 0 ∧ y = 0 := by
  rw [exercise22_stationary]
  constructor
  · rintro ⟨hz, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ <;> norm_num [exercise22Function] at *
  · rintro ⟨rfl, rfl⟩; norm_num [exercise22Function]

theorem exercise22_even (x y : ℝ) :
    exercise22Function (x, -y) = exercise22Function (x, y) := by
  unfold exercise22Function; ring

/-- The horizontal tangencies, in exact algebraic coordinates. -/
def exercise22FoldX (x y : ℝ) : Prop :=
  0 < x ∧ 4 * x ^ 2 = 3 ∧ y ^ 2 = x - x ^ 2

theorem exercise22_critical_x_on_zero (x y : ℝ) (hz : exercise22Function (x, y) = 0) :
    x ^ 2 + y ^ 2 - x = 0 ↔ (x = 0 ∧ y = 0) ∨ exercise22FoldX x y := by
  constructor
  · intro hd
    have he : x * (4 * x ^ 2 - 3) = 0 := by
      dsimp [exercise22Function] at hz
      nlinarith [mul_eq_zero_of_right (6 * x + 3) hd]
    rcases mul_eq_zero.mp he with hx | hx
    · left; exact ⟨hx, by rw [hx] at hd; nlinarith [sq_nonneg y]⟩
    · right; refine ⟨?_, by linarith, by linarith⟩
      nlinarith [sq_nonneg y]
  · rintro (⟨rfl, rfl⟩ | ⟨_, _, he⟩)
    · norm_num
    · linarith

/-- Reflection in the x-axis supplies two roots in each nearby vertical fiber. -/
theorem exercise22_even_fibers {a c : ℝ} {p : ℝ → ℝ × ℝ}
    (hp : Tendsto p (𝓝 c) (𝓝 (a, 0)))
    (hz : ∀ᶠ t in 𝓝[≠] c, exercise22Function (p t) = 0 ∧ (p t).2 ≠ 0) :
    MultipleFibersY exercise22Function a 0 := by
  have hx := (continuous_fst.tendsto (a, (0 : ℝ))).comp hp
  have hy := (continuous_snd.tendsto (a, (0 : ℝ))).comp hp
  apply multipleFibers_of_curves (p := fun t => ((p t).2, (p t).1))
    (q := fun t => (-(p t).2, (p t).1)) (hy.prodMk_nhds hx)
  · simpa using hy.neg.prodMk_nhds hx
  · filter_upwards [hz] with t ht
    refine ⟨ht.1, ?_, rfl, ?_⟩
    · change exercise22Function ((p t).1, -(p t).2) = 0
      rw [exercise22_even]; exact ht.1
    · change (p t).2 ≠ -(p t).2
      intro he; exact ht.2 (by linarith)

theorem exercise22_param_continuous : Continuous exercise22Param := by
  have hd (t : ℝ) : 2 + 6 * t ^ 2 ≠ 0 := by positivity
  unfold exercise22Param
  fun_prop (disch := exact hd _)

theorem exercise22_param_node : exercise22Param 1 = (0, 0) := by
  norm_num [exercise22Param]

theorem exercise22_param_punctured :
    ∀ᶠ t in 𝓝[≠] (1 : ℝ), (exercise22Param t).1 ≠ 0 ∧ (exercise22Param t).2 ≠ 0 := by
  have hb : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < t := Ioi_mem_nhds (by norm_num)
  filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  have hd : 2 + 6 * t ^ 2 ≠ 0 := by positivity
  have hx : (exercise22Param t).1 ≠ 0 := by
    dsimp [exercise22Param]
    apply div_ne_zero _ hd
    intro he
    have : t = 1 := by nlinarith
    exact hn this
  exact ⟨hx, mul_ne_zero (ne_of_gt ht) hx⟩

theorem exercise22_node_y : MultipleFibersY exercise22Function 0 0 := by
  apply exercise22_even_fibers (p := exercise22Param) (c := 1)
  · simpa only [exercise22_param_node] using exercise22_param_continuous.tendsto 1
  · filter_upwards [exercise22_param_punctured] with t ht
    exact ⟨exercise22_param_zero t, ht.2⟩

theorem exercise22_fold_y : MultipleFibersY exercise22Function (3 / 2) 0 := by
  obtain ⟨g, hc, hg, hz⟩ := zeroCurve_of_partial
    (exercise22_smooth.contDiffAt.of_le (by norm_num))
    (by norm_num [exercise22Function] : exercise22Function (3 / 2, 0) = 0)
    (exercise22_partials (3 / 2) 0).1 (by norm_num)
  apply exercise22_even_fibers (p := fun t => (g t, t)) (c := 0)
  · simpa only [hg, id_eq] using hc.tendsto.prodMk_nhds
      (Filter.tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  · filter_upwards [hz.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
    exact ⟨ht, hn⟩

noncomputable def exercise22Discriminant (p : ℝ × ℝ) : ℝ :=
  9 + 12 * p.1 - 12 * p.1 ^ 2 - 48 * p.2 ^ 2

noncomputable def exercise22OtherRoot (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (3 - 2 * p.1 + ε * Real.sqrt (exercise22Discriminant p)) / 4

theorem exercise22_other_continuous (ε : ℝ) : Continuous (exercise22OtherRoot ε) := by
  unfold exercise22OtherRoot exercise22Discriminant; fun_prop

/-- Division by the known root leaves this quadratic. -/
theorem exercise22_other_quadratic (ε x y : ℝ) (hε : ε ^ 2 = 1)
    (hD : 0 ≤ exercise22Discriminant (x, y)) :
    let z := exercise22OtherRoot ε (x, y)
    2 * z ^ 2 + (2 * x - 3) * z + 2 * x ^ 2 - 3 * x + 6 * y ^ 2 = 0 := by
  have hs := Real.sq_sqrt hD
  have he : (ε * Real.sqrt (exercise22Discriminant (x, y))) ^ 2 =
      exercise22Discriminant (x, y) := by rw [mul_pow, hε, one_mul, hs]
  dsimp [exercise22OtherRoot]
  dsimp [exercise22Discriminant] at he ⊢
  nlinarith

theorem exercise22_other_zero (ε x y : ℝ) (hε : ε ^ 2 = 1)
    (hD : 0 ≤ exercise22Discriminant (x, y)) (hz : exercise22Function (x, y) = 0) :
    exercise22Function (exercise22OtherRoot ε (x, y), y) = 0 := by
  have he := exercise22_other_quadratic ε x y hε hD
  dsimp only at he
  have hi := mul_eq_zero_of_right (exercise22OtherRoot ε (x, y) - x) he
  dsimp [exercise22Function] at hz ⊢
  nlinarith

theorem exercise22_other_fibers {a b c ε : ℝ} {p : ℝ → ℝ × ℝ}
    (hε : ε ^ 2 = 1) (hb : exercise22OtherRoot ε (a, b) = a)
    (hp : Tendsto p (𝓝 c) (𝓝 (a, b)))
    (hz : ∀ᶠ t in 𝓝[≠] c, exercise22Function (p t) = 0 ∧
      0 ≤ exercise22Discriminant (p t) ∧ (p t).1 ^ 2 + (p t).2 ^ 2 - (p t).1 ≠ 0) :
    MultipleFibersX exercise22Function a b := by
  have hx : Tendsto (fun t => exercise22OtherRoot ε (p t)) (𝓝 c) (𝓝 a) := by
    rw [← hb]; exact ((exercise22_other_continuous ε).tendsto (a, b)).comp hp
  have hy := (continuous_snd.tendsto (a, b)).comp hp
  apply multipleFibers_of_curves hp (hx.prodMk_nhds hy)
  filter_upwards [hz] with t ht
  refine ⟨ht.1, exercise22_other_zero ε _ _ hε ht.2.1 ht.1, rfl, ?_⟩
  intro he
  have hq := exercise22_other_quadratic ε (p t).1 (p t).2 hε ht.2.1
  dsimp only at hq
  rw [← he] at hq
  exact ht.2.2 (by nlinarith)

theorem exercise22_node_x : MultipleFibersX exercise22Function 0 0 := by
  have hp : Tendsto exercise22Param (𝓝 (1 : ℝ)) (𝓝 (0, 0)) := by
    simpa only [exercise22_param_node] using exercise22_param_continuous.tendsto 1
  apply exercise22_other_fibers (ε := -1) (by norm_num)
    (by norm_num [exercise22OtherRoot, exercise22Discriminant]) hp
  have hb : ∀ᶠ t in 𝓝 (1 : ℝ), (exercise22Param t).1 < 1 / 2 ∧
      0 < exercise22Discriminant (exercise22Param t) := by
    exact hp.eventually (show ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), p.1 < 1 / 2 ∧
      0 < exercise22Discriminant p from
      ((isOpen_lt (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
          (continuous_const (y := (1 / 2 : ℝ)))).inter
        (isOpen_lt (continuous_const (y := (0 : ℝ)))
          (by unfold exercise22Discriminant; fun_prop : Continuous exercise22Discriminant))).mem_nhds
        (by norm_num [exercise22Discriminant]))
  filter_upwards [exercise22_param_punctured, hb.filter_mono nhdsWithin_le_nhds] with t ht hb
  refine ⟨exercise22_param_zero t, hb.2.le, ?_⟩
  intro hd
  rcases (exercise22_critical_x_on_zero _ _ (exercise22_param_zero t)).mp hd with h | h
  · exact ht.1 h.1
  · have hh := h.2.1
    have hl := h.1
    change 4 * (exercise22Param t).1 ^ 2 = 3 at hh
    change 0 < (exercise22Param t).1 at hl
    nlinarith [hb.1]

/-- At each horizontal fold two distinct x roots converge to the same point. -/
theorem exercise22_fold_x (a b : ℝ) (h : exercise22FoldX a b) :
    MultipleFibersX exercise22Function a b := by
  obtain ⟨ha, ha2, hb2⟩ := h
  have ha' : 1 / 2 < a := by nlinarith
  have ha'' : a < 1 := by nlinarith
  have hb : b ≠ 0 := by intro hb; rw [hb] at hb2; nlinarith
  have hz : exercise22Function (a, b) = 0 := by
    dsimp [exercise22Function]
    nlinarith [mul_eq_zero_of_right a (show 4 * a ^ 2 - 3 = 0 by linarith)]
  obtain ⟨g, hc, hg, hgzero⟩ := zeroCurve_of_partial (f := fun p => exercise22Function (p.2, p.1))
    (by unfold exercise22Function; fun_prop) hz (exercise22_partials a b).2
    (mul_ne_zero (mul_ne_zero (by norm_num) hb) (by linarith))
  have hD : exercise22Discriminant (a, b) = (6 * a - 3) ^ 2 := by
    dsimp [exercise22Discriminant]; nlinarith
  have hother : exercise22OtherRoot 1 (a, b) = a := by
    dsimp [exercise22OtherRoot]
    rw [hD, Real.sqrt_sq (by linarith : 0 ≤ 6 * a - 3)]
    ring
  have hp : Tendsto (fun t => (t, g t)) (𝓝 a) (𝓝 (a, b)) := by
    simpa only [hg, id_eq] using
      (Filter.tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 a) (𝓝 a)).prodMk_nhds hc.tendsto
  apply exercise22_other_fibers (ε := 1) (by norm_num) hother hp
  have hpos : ∀ᶠ t in 𝓝 a, 0 < t := Ioi_mem_nhds ha
  have hdisc : ∀ᶠ t in 𝓝 a, 0 < exercise22Discriminant (t, g t) := by
    exact hp.eventually (show ∀ᶠ p in 𝓝 (a, b), 0 < exercise22Discriminant p from
      (isOpen_lt continuous_const (by unfold exercise22Discriminant; fun_prop)).mem_nhds
        (by change 0 < exercise22Discriminant (a, b)
            rw [hD]; exact sq_pos_of_ne_zero (by linarith)))
  filter_upwards [hgzero.filter_mono nhdsWithin_le_nhds,
    hpos.filter_mono nhdsWithin_le_nhds, hdisc.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht hpos hdisc hn
  refine ⟨ht, hdisc.le, ?_⟩
  intro hd
  rcases (exercise22_critical_x_on_zero t (g t) ht).mp hd with hh | hh
  · linarith [hh.1]
  · have he : (t - a) * (t + a) = 0 := by nlinarith [hh.2.1]
    rcases mul_eq_zero.mp he with he | he
    · change t ≠ a at hn; exact hn (by linarith)
    · linarith

/-- All and only the two vertical-projection failures. -/
theorem exercise22_graph_y (x y : ℝ) (hz : exercise22Function (x, y) = 0) :
    (¬ ZeroGraphY exercise22Function x y) ↔
      (x = 0 ∧ y = 0) ∨ (x = 3 / 2 ∧ y = 0) := by
  constructor
  · intro hn
    have hd : 6 * y * (2 * x + 1) = 0 := by
      by_contra hd
      exact hn (zeroGraphX_of_partial (by unfold exercise22Function; fun_prop)
        hz (exercise22_partials x y).2 hd)
    have hx := (exercise22_zero_set x y).mp hz |>.1
    have hy : y = 0 := by
      rcases mul_eq_zero.mp hd with h | h
      · nlinarith
      · linarith
    subst y
    have he : x ^ 2 * (2 * x - 3) = 0 := by dsimp [exercise22Function] at hz; nlinarith
    rcases mul_eq_zero.mp he with he | he
    · exact Or.inl ⟨by nlinarith [sq_nonneg x], rfl⟩
    · exact Or.inr ⟨by linarith, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact multipleFibers_not_graph exercise22_node_y
    · exact multipleFibers_not_graph exercise22_fold_y

/-- All and only the three horizontal-projection failures. -/
theorem exercise22_graph_x (x y : ℝ) (hz : exercise22Function (x, y) = 0) :
    (¬ ZeroGraphX exercise22Function x y) ↔
      (x = 0 ∧ y = 0) ∨ exercise22FoldX x y := by
  constructor
  · intro hn
    apply (exercise22_critical_x_on_zero x y hz).mp
    by_contra hd
    exact hn (zeroGraphX_of_partial (exercise22_smooth.contDiffAt.of_le (by norm_num))
      hz (exercise22_partials x y).1 (mul_ne_zero (by norm_num) hd))
  · rintro (⟨rfl, rfl⟩ | h)
    · exact multipleFibers_not_graph exercise22_node_x
    · exact multipleFibers_not_graph (exercise22_fold_x x y h)

theorem exercise22_fold_coordinates (x y : ℝ) :
    exercise22FoldX x y ↔
      x = Real.sqrt 3 / 2 ∧
      (y = Real.sqrt (Real.sqrt 3 / 2 - 3 / 4) ∨
       y = -Real.sqrt (Real.sqrt 3 / 2 - 3 / 4)) := by
  have hr : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hpos : 0 ≤ Real.sqrt (3 : ℝ) / 2 - 3 / 4 := by nlinarith
  have hsq := Real.sq_sqrt hpos
  constructor
  · rintro ⟨hx, hx2, hy2⟩
    have h : (2 * x) ^ 2 = (Real.sqrt (3 : ℝ)) ^ 2 := by nlinarith
    have hxeq : x = Real.sqrt 3 / 2 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h <;> linarith
    refine ⟨hxeq, sq_eq_sq_iff_eq_or_eq_neg.mp ?_⟩
    rw [hsq]
    nlinarith
  · rintro ⟨rfl, hy | hy⟩ <;> refine ⟨by positivity, by nlinarith, ?_⟩ <;>
      rw [hy] <;> nlinarith

theorem exercise22_graph_x_explicit (x y : ℝ) (hz : exercise22Function (x, y) = 0) :
    (¬ ZeroGraphX exercise22Function x y) ↔
      (x = 0 ∧ y = 0) ∨
      (x = Real.sqrt 3 / 2 ∧
        (y = Real.sqrt (Real.sqrt 3 / 2 - 3 / 4) ∨
         y = -Real.sqrt (Real.sqrt 3 / 2 - 3 / 4))) := by
  rw [exercise22_graph_x x y hz, exercise22_fold_coordinates]

/-- The branches meet at the node and at the rightmost point only. -/
theorem exercise22_branch_meetings (x : ℝ) (hx : -1 / 2 < x) (hx' : x ≤ 3 / 2) :
    Real.sqrt (x ^ 2 * (3 - 2 * x) / (3 + 6 * x)) =
      -Real.sqrt (x ^ 2 * (3 - 2 * x) / (3 + 6 * x)) ↔ x = 0 ∨ x = 3 / 2 := by
  have hd : 0 < 3 + 6 * x := by linarith
  have hs : 0 ≤ x ^ 2 * (3 - 2 * x) / (3 + 6 * x) :=
    div_nonneg (mul_nonneg (sq_nonneg x) (by linarith)) hd.le
  constructor
  · intro he
    have hh := Real.sq_sqrt hs
    have hz : Real.sqrt (x ^ 2 * (3 - 2 * x) / (3 + 6 * x)) = 0 := by linarith
    rw [hz, zero_pow (by norm_num)] at hh
    have he : x ^ 2 * (3 - 2 * x) = 0 := (div_eq_zero_iff).mp hh.symm |>.resolve_right (ne_of_gt hd)
    rcases mul_eq_zero.mp he with he | he
    · left; nlinarith [sq_nonneg x]
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- The tangent cone at the node consists of the two lines y=x and y=−x. -/
theorem exercise22_node_expansion (x y t : ℝ) :
    exercise22Function (t * x, t * y) =
      3 * t ^ 2 * (y ^ 2 - x ^ 2) + 2 * t ^ 3 * x * (x ^ 2 + 3 * y ^ 2) := by
  unfold exercise22Function; ring

theorem exercise22_tangent_cone (x y : ℝ) :
    3 * (y ^ 2 - x ^ 2) = 0 ↔ y = x ∨ y = -x := by
  constructor
  · intro h; apply sq_eq_sq_iff_eq_or_eq_neg.mp; linarith
  · rintro (rfl | rfl) <;> ring

/-- The two unbounded arms approach x=−1/2; this exact identity also
shows that the curve never reaches its vertical asymptote. -/
theorem exercise22_asymptote_identity (t : ℝ) :
    (exercise22Param t).1 + 1 / 2 = 2 / (1 + 3 * t ^ 2) := by
  have h1 : 1 + 3 * t ^ 2 ≠ 0 := by positivity
  have h2 : 2 + 6 * t ^ 2 ≠ 0 := by positivity
  dsimp [exercise22Param]
  field_simp
  ring

/-- The actual Fréchet differential, not a formal gradient convention. -/
theorem exercise22_differential (x y u v : ℝ) :
    HasFDerivAt exercise22Function (fderiv ℝ exercise22Function (x, y)) (x, y) ∧
    fderiv ℝ exercise22Function (x, y) (u, v) =
      6 * (x ^ 2 + y ^ 2 - x) * u + 6 * y * (2 * x + 1) * v := by
  have hc : ContDiffAt ℝ 1 exercise22Function (x, y) :=
    exercise22_smooth.contDiffAt.of_le (by norm_num)
  refine ⟨(hc.differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
  rw [scalarDifferential_coordinates,
    (exercise20_partials hc).1.unique (exercise22_partials x y).1,
    (exercise20_partials hc).2.unique (exercise22_partials x y).2]

/-- The compact parameter interval gives the loop to the right of the node;
the two remaining parameter intervals give the left arms. -/
theorem exercise22_loop_parameters (t : ℝ) :
    0 ≤ (exercise22Param t).1 ↔ |t| ≤ 1 := by
  have hd : 0 < 2 + 6 * t ^ 2 := by positivity
  rw [← sq_le_one_iff_abs_le_one]
  change 0 ≤ 3 * (1 - t ^ 2) / (2 + 6 * t ^ 2) ↔ t ^ 2 ≤ 1
  constructor
  · intro h
    have hn := (le_div_iff₀ hd).mp h
    nlinarith
  · intro h; exact div_nonneg (by linarith) hd.le

/-- Both infinite arms have the vertical asymptote x=−1/2. -/
theorem exercise22_asymptotes :
    Tendsto (fun t => (exercise22Param t).1) atTop (𝓝 (-1 / 2)) ∧
    Tendsto (fun t => (exercise22Param t).1) atBot (𝓝 (-1 / 2)) ∧
    Tendsto (fun t => (exercise22Param t).2) atTop atBot ∧
    Tendsto (fun t => (exercise22Param t).2) atBot atTop := by
  have hd : Tendsto (fun t : ℝ => 1 + 3 * t ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 3)
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
  have hx : Tendsto (fun t => (exercise22Param t).1) atTop (𝓝 (-1 / 2)) := by
    have h := (hd.const_div_atTop 2).sub_const (1 / 2)
    convert h using 1
    · ext t; linarith [exercise22_asymptote_identity t]
    · norm_num
  have hx' : Tendsto (fun t => (exercise22Param t).1) atBot (𝓝 (-1 / 2)) := by
    convert hx.comp tendsto_neg_atBot_atTop using 1
    ext t
    simp [exercise22Param]
  refine ⟨hx, hx', ?_, ?_⟩
  · exact (Filter.tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).atTop_mul_neg
      (by norm_num : (-1 / 2 : ℝ) < 0) hx
  · exact (Filter.tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot).atBot_mul_neg
      (by norm_num : (-1 / 2 : ℝ) < 0) hx'

theorem exercise22_frechet_stationary (x y : ℝ) :
    fderiv ℝ exercise22Function (x, y) = 0 ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) := by
  constructor
  · intro h
    apply (exercise22_stationary x y).mp
    rw [(exercise22_partials x y).1.deriv, (exercise22_partials x y).2.deriv]
    have hx := (exercise22_differential x y 1 0).2
    have hy := (exercise22_differential x y 0 1).2
    rw [h] at hx hy
    simpa using And.intro hx.symm hy.symm
  · intro h
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    rw [(exercise22_differential x y u v).2]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

theorem exercise22_stationary_saddles (x y : ℝ) :
    (fderiv ℝ exercise22Function (x, y) = 0 ∧ Saddle exercise22Function (x, y)) ↔
      x = 0 ∧ y = 0 := by
  rw [exercise22_frechet_stationary]
  constructor
  · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hs⟩
    · exact ⟨rfl, rfl⟩
    · exact False.elim ((saddle_not_extremum hs).1 exercise22_minimum.1)
  · rintro ⟨rfl, rfl⟩
    exact ⟨Or.inl ⟨rfl, rfl⟩, exercise22_saddle⟩

end Rudin.Chapter09
