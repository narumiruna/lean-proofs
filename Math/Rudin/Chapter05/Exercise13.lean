module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section
noncomputable section
namespace Rudin.Chapter05
open Set Filter Topology
open scoped Real

/-- The printed prefactor is not defined as a real power for all the stated data:
`a = 1/2`, `x = -1` would require a real square root of `-1`. -/
theorem exercise13_domain_obstruction : ¬ ∃ y : ℝ, y ^ 2 = -1 := by
  rintro ⟨y, hy⟩
  nlinarith [sq_nonneg y]

/-- The explicitly selected correction, not an interpretation of the printed
negative-base power. Real powers here have only nonnegative bases. -/
def exercise13F (a c x : ℝ) : ℝ :=
  if x = 0 then 0 else |x| ^ a * Real.sin (|x| ^ (-c))

namespace Exercise13

abbrev interval : Set ℝ := Icc (-1) 1

def P (a c t : ℝ) : ℝ := t ^ a * Real.sin (t ^ (-c))
def Q (a c t : ℝ) : ℝ :=
  a * t ^ (a - 1) * Real.sin (t ^ (-c)) -
    c * t ^ (a - c - 1) * Real.cos (t ^ (-c))
def R (a c t : ℝ) : ℝ :=
  a * (a - 1) * t ^ (a - 2) * Real.sin (t ^ (-c)) -
    c * (2 * a - c - 1) * t ^ (a - c - 2) * Real.cos (t ^ (-c)) -
    c ^ 2 * t ^ (a - 2 * c - 2) * Real.sin (t ^ (-c))

def D (a c x : ℝ) : ℝ := if x = 0 then 0 else (x / |x|) * Q a c |x|
def E (a c x : ℝ) : ℝ := if x = 0 then 0 else R a c |x|

@[simp] theorem F_zero (a c : ℝ) : exercise13F a c 0 = 0 := by simp [exercise13F]
@[simp] theorem D_zero (a c : ℝ) : D a c 0 = 0 := by simp [D]
@[simp] theorem E_zero (a c : ℝ) : E a c 0 = 0 := by simp [E]

theorem F_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) : exercise13F a c x = P a c x := by
  simp [exercise13F, hx.ne', abs_of_pos hx, P]
theorem D_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) : D a c x = Q a c x := by
  simp [D, hx.ne', abs_of_pos hx]
theorem E_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) : E a c x = R a c x := by
  simp [E, hx.ne', abs_of_pos hx]
theorem F_even (a c x : ℝ) : exercise13F a c (-x) = exercise13F a c x := by
  simp [exercise13F]
theorem D_odd (a c x : ℝ) : D a c (-x) = -D a c x := by
  by_cases hx : x = 0 <;> simp [D, hx, neg_div, neg_mul]

/-- Explicit inverse-phase sequence. Offsets `0`, `pi`, and `pi/2` select
cosine `1`, cosine `-1`, and sine `1`, respectively. -/
def phase (b : ℝ) (n : ℕ) : ℝ := b + (n + 1 : ℝ) * (2 * Real.pi)
def point (c b : ℝ) (n : ℕ) : ℝ := phase b n ^ (-1 / c)

theorem phase_pos {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 < phase b n := by
  unfold phase
  positivity

theorem phase_top (b : ℝ) : Tendsto (phase b) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact tendsto_atTop_add_const_left atTop b
    (hn.atTop_mul_const (by positivity : 0 < 2 * Real.pi))

theorem point_pos {c b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 < point c b n :=
  Real.rpow_pos_of_pos (phase_pos hb n) _

theorem point_zero {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Tendsto (point c b) atTop (𝓝 0) := by
  change Tendsto (fun n => phase b n ^ (-1 / c)) atTop (𝓝 0)
  have hh := (tendsto_rpow_neg_atTop (one_div_pos.mpr hc)).comp (phase_top b)
  simp only [Function.comp_def] at hh
  simpa only [neg_div] using hh

theorem point_phase {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (n : ℕ) :
    point c b n ^ (-c) = phase b n := by
  rw [point, ← Real.rpow_mul (phase_pos hb n).le]
  have h : -1 / c * -c = 1 := by field_simp
  rw [h, Real.rpow_one]

theorem point_sin {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (n : ℕ) :
    Real.sin (point c b n ^ (-c)) = Real.sin b := by
  rw [point_phase hc hb]
  simpa [phase, Nat.cast_add, Nat.cast_one] using Real.sin_add_nat_mul_two_pi b (n + 1)

theorem point_cos {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) (n : ℕ) :
    Real.cos (point c b n ^ (-c)) = Real.cos b := by
  rw [point_phase hc hb]
  simpa [phase, Nat.cast_add, Nat.cast_one] using Real.cos_add_nat_mul_two_pi b (n + 1)

theorem point_mem {c : ℝ} (hc : 0 < c) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n in atTop, point c b n ∈ interval := by
  filter_upwards [(point_zero hc b).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
  exact ⟨by linarith [point_pos (c := c) hb n], hn.le⟩

/-- A nonzero limiting coefficient cannot cancel a nonpositive power at zero. -/
theorem exponent_pos_of_zero {t k : ℕ → ℝ} {p K : ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ n, 0 < t n)
    (hk : Tendsto k atTop (𝓝 K)) (hK : K ≠ 0)
    (h : Tendsto (fun n => t n ^ p * k n) atTop (𝓝 0)) : 0 < p := by
  by_contra hp
  have hpow : Tendsto (fun n => t n ^ p) atTop (𝓝 0) := by
    have hh := h.div hk hK
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [hk.eventually_ne hK] with n hn
    exact mul_div_cancel_right₀ _ hn
  have he : ∀ᶠ n in atTop, 1 ≤ t n ^ p := by
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (htp n) hn.le (le_of_not_gt hp)
  have := ge_of_tendsto hpow he
  norm_num at this

/-- Bounded samples with a nonzero limiting coefficient force a nonnegative exponent. -/
theorem exponent_nonneg_of_bounded {t k : ℕ → ℝ} {p K M : ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ n, 0 < t n)
    (hk : Tendsto k atTop (𝓝 K)) (hK : K ≠ 0)
    (h : ∀ᶠ n in atTop, |t n ^ p * k n| ≤ M) : 0 ≤ p := by
  by_contra hp
  have hz : Tendsto (fun n => t n ^ (-p)) atTop (𝓝 0) := by
    have hh := (Real.continuousAt_rpow_const 0 (-p) (Or.inr (by linarith))).tendsto.comp ht
    simpa only [Function.comp_def, Real.zero_rpow (by linarith : -p ≠ 0)] using hh
  have he : ∀ᶠ n in atTop, |k n| ≤ M * t n ^ (-p) := by
    filter_upwards [h] with n hn
    have hm := mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (htp n).le (-p))
    simpa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (htp n) p),
      mul_assoc, ← Real.rpow_add (htp n), mul_comm, mul_left_comm] using hm
  have hh : |K| ≤ 0 := by
    have hm := hz.const_mul M
    have hkn := hk.abs
    exact le_of_tendsto_of_tendsto hkn (by simpa using hm) he
  exact hK (abs_nonpos_iff.mp hh)

/-- A positive power dominates an arbitrary bounded sine or cosine factor. -/
theorem vanish {p : ℝ} (hp : 0 < p) {g : ℝ → ℝ}
    (hg : ∀ x, |g x| ≤ 1) :
    Tendsto (fun x : ℝ => |x| ^ p * g x) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (a := fun x : ℝ => |x| ^ p)
  · intro x
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) p)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg x) p) (hg x)
  · have hh := ((continuous_abs.continuousAt (x := (0 : ℝ))).rpow_const (Or.inr hp.le)).tendsto
    simpa [Real.zero_rpow hp.ne'] using hh

theorem P_bound (a c : ℝ) {t : ℝ} (ht : 0 ≤ t) : |P a c t| ≤ t ^ a := by
  rw [P, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht a)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg ht a) (Real.abs_sin_le_one _)

theorem F_cont_zero {a : ℝ} (ha : 0 < a) (c : ℝ) : ContinuousAt (exercise13F a c) 0 := by
  have h := vanish ha (fun x => Real.abs_sin_le_one (|x| ^ (-c)))
  rw [ContinuousAt, F_zero]
  apply h.congr'
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x = 0 <;> simp [exercise13F, hx, Real.zero_rpow ha.ne']

theorem F_cont_off (a c : ℝ) {x : ℝ} (hx : x ≠ 0) : ContinuousAt (exercise13F a c) x := by
  have hab : |x| ≠ 0 := abs_ne_zero.mpr hx
  have h : ContinuousAt (fun y : ℝ => |y| ^ a * Real.sin (|y| ^ (-c))) x := by
    fun_prop (disch := aesop)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [exercise13F, hy]

/-- The sine-one samples give the necessity of the continuity threshold. -/
theorem continuous_iff {a c : ℝ} (hc : 0 < c) :
    ContinuousOn (exercise13F a c) interval ↔ 0 < a := by
  constructor
  · intro hf
    have ht := point_zero hc (Real.pi / 2)
    have hb : 0 ≤ Real.pi / 2 := by positivity
    have hl := (hf 0 (by constructor <;> norm_num)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht, point_mem hc hb⟩)
    have he : (fun n => exercise13F a c (point c (Real.pi / 2) n)) =
        (fun n => point c (Real.pi / 2) n ^ a * (1 : ℝ)) := by
      funext n
      rw [F_pos a c (point_pos hb n), P, point_sin hc hb, Real.sin_pi_div_two]
    simp only [Function.comp_def] at hl
    rw [he, F_zero] at hl
    exact exponent_pos_of_zero ht (point_pos hb) tendsto_const_nhds one_ne_zero hl
  · intro ha x hx
    by_cases h : x = 0
    · subst x; exact (F_cont_zero ha c).continuousWithinAt
    · exact (F_cont_off a c h).continuousWithinAt

theorem even_derivative_zero {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x, f (-x) = f x) (h : HasDerivAt f L 0) : L = 0 := by
  have hh : HasDerivAt f L (-(0 : ℝ)) := by simpa using h
  have hn := hh.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have he : f ∘ Neg.neg = f := funext hf
  simp only [he, mul_neg, mul_one] at hn
  linarith [h.unique hn]

theorem F_div_bound (a c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    |exercise13F a c x / x| ≤ |x| ^ (a - 1) := by
  rw [abs_div, Real.rpow_sub (abs_pos.mpr hx), Real.rpow_one]
  exact div_le_div_of_nonneg_right (by
    simpa [exercise13F, hx, P] using P_bound a c (abs_nonneg x)) (abs_nonneg x)

theorem pow_abs_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun x : ℝ => |x| ^ p) (𝓝 0) (𝓝 0) := by
  simpa only [mul_one] using vanish hp (g := fun _ => 1) (by intro x; norm_num)

theorem F_deriv_zero {a : ℝ} (ha : 1 < a) (c : ℝ) : HasDerivAt (exercise13F a c) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  change Tendsto (fun x : ℝ => slope (exercise13F a c) 0 x) (𝓝[≠] 0) (𝓝 0)
  simp only [slope_def_field, F_zero, sub_zero]
  apply squeeze_zero_norm' (a := fun x : ℝ => |x| ^ (a - 1))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact F_div_bound a c hx
  · exact (pow_abs_zero (by linarith)).mono_left inf_le_left

theorem derivative_iff {a c : ℝ} (hc : 0 < c) :
    DifferentiableAt ℝ (exercise13F a c) 0 ↔ 1 < a := by
  constructor
  · intro hf
    have hd := hf.hasDerivAt
    have he := even_derivative_zero (F_even a c) hd
    rw [he] at hd
    have hb : 0 ≤ Real.pi / 2 := by positivity
    have ht := point_zero hc (Real.pi / 2)
    have hn : Tendsto (point c (Real.pi / 2)) atTop (𝓝[≠] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht, Filter.Eventually.of_forall fun n => (point_pos hb n).ne'⟩
    have hl := hd.tendsto_slope.comp hn
    simp only [Function.comp_def, slope_def_field, F_zero, sub_zero] at hl
    have hh : ∀ n, exercise13F a c (point c (Real.pi / 2) n) / point c (Real.pi / 2) n =
        point c (Real.pi / 2) n ^ (a - 1) * (1 : ℝ) := by
      intro n
      rw [F_pos a c (point_pos hb n), P, point_sin hc hb, Real.sin_pi_div_two,
        Real.rpow_sub (point_pos hb n), Real.rpow_one]
      ring
    simp_rw [hh] at hl
    have := exponent_pos_of_zero ht (point_pos hb) tendsto_const_nhds one_ne_zero hl
    linarith
  · intro ha; exact (F_deriv_zero ha c).differentiableAt

theorem P_deriv (a c : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (P a c) (Q a c t) t := by
  have ha := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
  have hc := Real.hasDerivAt_rpow_const (p := -c) (Or.inl ht.ne')
  convert ha.mul hc.sin using 1
  · rfl
  · dsimp [Q]
    have hh : t ^ a * t ^ (-c - 1) = t ^ (a - c - 1) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    symm
    calc
      _ = a * t ^ (a - 1) * Real.sin (t ^ (-c)) -
          c * (t ^ a * t ^ (-c - 1)) * Real.cos (t ^ (-c)) := by ring
      _ = _ := by rw [hh]

theorem Q_deriv (a c : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (Q a c) (R a c t) t := by
  have h1 := Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl ht.ne')
  have h2 := Real.hasDerivAt_rpow_const (p := a - c - 1) (Or.inl ht.ne')
  have h3 := Real.hasDerivAt_rpow_const (p := -c) (Or.inl ht.ne')
  convert ((h1.const_mul a).mul h3.sin).sub ((h2.const_mul c).mul h3.cos) using 1
  · rfl
  · dsimp [R]
    have h4 : t ^ (a - 1) * t ^ (-c - 1) = t ^ (a - c - 2) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    have h5 : t ^ (a - c - 1) * t ^ (-c - 1) = t ^ (a - 2 * c - 2) := by
      rw [← Real.rpow_add ht]; congr 1; ring
    have e1 : a - 1 - 1 = a - 2 := by ring
    have e2 : a - c - 1 - 1 = a - c - 2 := by ring
    rw [e1, e2]
    symm
    calc
      _ = a * (a - 1) * t ^ (a - 2) * Real.sin (t ^ (-c)) -
          (a * c * (t ^ (a - 1) * t ^ (-c - 1)) +
          c * (a - c - 1) * t ^ (a - c - 2)) * Real.cos (t ^ (-c)) -
          c ^ 2 * (t ^ (a - c - 1) * t ^ (-c - 1)) * Real.sin (t ^ (-c)) := by ring
      _ = _ := by rw [h4, h5]; ring

/-- This formula is proved at nonzero points; it does not use a totalized
iterated derivative as evidence for existence. -/
theorem F_deriv_off (a c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (exercise13F a c) (D a c x) x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hh := (P_deriv a c (neg_pos.mpr hx)).comp x (hasDerivAt_neg x)
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y => P a c (-y)) (f' := D a c x)
    · simpa [D, hx.ne, abs_of_neg hx, neg_div, div_self hx.ne, Function.comp_def] using hh
    · filter_upwards [eventually_lt_nhds hx] with y hy
      simp [exercise13F, hy.ne, abs_of_neg hy, P]
  · rw [D_pos a c hx]
    apply (P_deriv a c hx).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact F_pos a c hy

theorem D_deriv_off (a c : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (D a c) (E a c x) x := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hh := ((Q_deriv a c (neg_pos.mpr hx)).comp x (hasDerivAt_neg x)).neg
    apply HasDerivAt.congr_of_eventuallyEq (f := fun y => -Q a c (-y))
    · convert hh using 1
      · funext y; rfl
      · simp [E, hx.ne, abs_of_neg hx]
    · filter_upwards [eventually_lt_nhds hx] with y hy
      simp [D, hy.ne, abs_of_neg hy]
  · rw [E_pos a c hx]
    apply (Q_deriv a c hx).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact D_pos a c hy

/-- Derivatives on the source interval are derivatives within that interval.
In particular, this definition uses one-sided endpoint derivatives. -/
def First (a c : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ x ∈ interval, HasDerivWithinAt (exercise13F a c) (g x) interval x

def Second (g h : ℝ → ℝ) : Prop :=
  ∀ x ∈ interval, HasDerivWithinAt g (h x) interval x

theorem zero_interior : interval ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
theorem zero_mem : (0 : ℝ) ∈ interval := by constructor <;> norm_num

theorem first_exists {a c : ℝ} (ha : 1 < a) : First a c (D a c) := by
  intro x hx
  by_cases h : x = 0
  · subst x; simpa using (F_deriv_zero ha c).hasDerivWithinAt (s := interval)
  · exact (F_deriv_off a c h).hasDerivWithinAt

theorem first_identify {a c : ℝ} (hc : 0 < c) {g : ℝ → ℝ} (hg : First a c g) :
    1 < a ∧ EqOn g (D a c) interval := by
  have ha := (derivative_iff hc).mp ((hg 0 zero_mem).hasDerivAt zero_interior).differentiableAt
  refine ⟨ha, fun x hx => ?_⟩
  have hu := (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) x hx
  exact ((hg x hx).derivWithin hu).symm.trans ((first_exists ha x hx).derivWithin hu)

theorem D_bound (a c x : ℝ) :
    |D a c x| ≤ |a| * |x| ^ (a - 1) + |c| * |x| ^ (a - c - 1) := by
  by_cases hx : x = 0
  · subst x; simp only [D_zero, abs_zero]; positivity
  rw [D, ite_eq_right (by exact hx), abs_mul]
  have hs : |(x / |x|)| = 1 := by rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr hx)]
  rw [hs, one_mul]
  unfold Q
  calc
    _ ≤ |a * |x| ^ (a - 1) * Real.sin (|x| ^ (-c))| +
        |c * |x| ^ (a - c - 1) * Real.cos (|x| ^ (-c))| := abs_sub _ _
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
      exact add_le_add
        (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _))
        (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))

theorem D_vanish {a c : ℝ} (h1 : 0 < a - 1) (h2 : 0 < a - c - 1) :
    Tendsto (D a c) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (fun x => D_bound a c x)
  simpa using ((pow_abs_zero h1).const_mul |a|).add ((pow_abs_zero h2).const_mul |c|)

theorem Q_cos_one {a c : ℝ} (hc : 0 < c) (n : ℕ) :
    Q a c (point c 0 n) = point c 0 n ^ (a - c - 1) * (-c) := by
  simp [Q, point_sin hc (le_refl 0), point_cos hc (le_refl 0)]
  ring

theorem Q_cos_neg {a c : ℝ} (hc : 0 < c) (n : ℕ) :
    Q a c (point c Real.pi n) = point c Real.pi n ^ (a - c - 1) * c := by
  simp [Q, point_sin hc Real.pi_pos.le, point_cos hc Real.pi_pos.le]
  ring

theorem D_bounded_iff {a c : ℝ} (hc : 0 < c) :
    (∃ M : ℝ, ∀ x ∈ interval, |D a c x| ≤ M) ↔ 1 + c ≤ a := by
  constructor
  · rintro ⟨M, hM⟩
    have h : ∀ᶠ n in atTop, |point c 0 n ^ (a - c - 1) * (-c)| ≤ M := by
      filter_upwards [point_mem hc (le_refl 0)] with n hn
      simpa only [D_pos a c (point_pos (le_refl 0) n), Q_cos_one hc] using hM _ hn
    have := exponent_nonneg_of_bounded (point_zero hc 0) (point_pos (le_refl 0))
      tendsto_const_nhds (neg_ne_zero.mpr hc.ne') h
    linarith
  · intro ha
    refine ⟨|a| + |c|, fun x hx => (D_bound a c x).trans ?_⟩
    have hab : |x| ≤ 1 := abs_le.mpr hx
    exact add_le_add
      (mul_le_of_le_one_right (abs_nonneg a)
        (Real.rpow_le_one (abs_nonneg x) hab (by linarith)))
      (mul_le_of_le_one_right (abs_nonneg c)
        (Real.rpow_le_one (abs_nonneg x) hab (by linarith)))

theorem D_cont_iff {a c : ℝ} (hc : 0 < c) :
    ContinuousOn (D a c) interval ↔ 1 + c < a := by
  constructor
  · intro hd
    have ht := point_zero hc 0
    have hl := (hd 0 zero_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht, point_mem hc (le_refl 0)⟩)
    simp only [Function.comp_def, D_zero] at hl
    have he : (fun n => D a c (point c 0 n)) =
        (fun n => point c 0 n ^ (a - c - 1) * (-c)) := by
      funext n; rw [D_pos a c (point_pos (le_refl 0) n), Q_cos_one hc]
    rw [he] at hl
    have := exponent_pos_of_zero ht (point_pos (le_refl 0)) tendsto_const_nhds
      (neg_ne_zero.mpr hc.ne') hl
    linarith
  · intro ha x hx
    by_cases h : x = 0
    · subst x
      have hh : ContinuousAt (D a c) 0 := by
        rw [ContinuousAt, D_zero]; exact D_vanish (by linarith) (by linarith)
      exact hh.continuousWithinAt
    · exact (D_deriv_off a c h).continuousAt.continuousWithinAt

theorem pow_div {t : ℝ} (ht : 0 < t) (p : ℝ) : t ^ p / t = t ^ (p - 1) := by
  rw [Real.rpow_sub ht, Real.rpow_one]

theorem D_div_bound (a c : ℝ) {x : ℝ} (hx : x ≠ 0) :
    |D a c x / x| ≤ |a| * |x| ^ (a - 2) + |c| * |x| ^ (a - c - 2) := by
  rw [abs_div]
  calc
    _ ≤ (|a| * |x| ^ (a - 1) + |c| * |x| ^ (a - c - 1)) / |x| :=
      div_le_div_of_nonneg_right (D_bound a c x) (abs_nonneg x)
    _ = _ := by
      rw [add_div, mul_div_assoc, mul_div_assoc, pow_div (abs_pos.mpr hx), pow_div (abs_pos.mpr hx)]
      congr 2 <;> congr 1 <;> ring

theorem D_deriv_zero {a c : ℝ} (ha : 2 + c < a) (hc : 0 < c) : HasDerivAt (D a c) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  change Tendsto (fun x : ℝ => slope (D a c) 0 x) (𝓝[≠] 0) (𝓝 0)
  simp only [slope_def_field, D_zero, sub_zero]
  apply squeeze_zero_norm' (a := fun x : ℝ =>
    |a| * |x| ^ (a - 2) + |c| * |x| ^ (a - c - 2))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact D_div_bound a c hx
  · apply Tendsto.mono_left (x := 𝓝 (0 : ℝ)) _ inf_le_left
    simpa using ((pow_abs_zero (by linarith : 0 < a - 2)).const_mul |a|).add
      ((pow_abs_zero (by linarith : 0 < a - c - 2)).const_mul |c|)

theorem Q_div_cos_one {a c : ℝ} (hc : 0 < c) (n : ℕ) :
    D a c (point c 0 n) / point c 0 n = point c 0 n ^ (a - c - 2) * (-c) := by
  rw [D_pos a c (point_pos (le_refl 0) n), Q_cos_one hc, mul_div_right_comm,
    pow_div (point_pos (le_refl 0) n)]
  rw [show a - c - 1 - 1 = a - c - 2 by ring]

theorem Q_div_cos_neg {a c : ℝ} (hc : 0 < c) (n : ℕ) :
    D a c (point c Real.pi n) / point c Real.pi n = point c Real.pi n ^ (a - c - 2) * c := by
  rw [D_pos a c (point_pos Real.pi_pos.le n), Q_cos_neg hc, mul_div_right_comm,
    pow_div (point_pos Real.pi_pos.le n)]
  rw [show a - c - 1 - 1 = a - c - 2 by ring]

/-- Both opposite cosine phases are needed to exclude the equality case for
the second derivative at zero. -/
theorem D_derivative_iff {a c : ℝ} (hc : 0 < c) :
    DifferentiableAt ℝ (D a c) 0 ↔ 2 + c < a := by
  constructor
  · intro hd
    have hl (b : ℝ) (hb : 0 ≤ b) :
        Tendsto (fun n => D a c (point c b n) / point c b n) atTop (𝓝 (deriv (D a c) 0)) := by
      have hn : Tendsto (point c b) atTop (𝓝[≠] (0 : ℝ)) :=
        tendsto_nhdsWithin_iff.mpr ⟨point_zero hc b,
          Filter.Eventually.of_forall fun n => (point_pos hb n).ne'⟩
      simpa only [Function.comp_def, slope_def_field, D_zero, sub_zero] using hd.hasDerivAt.tendsto_slope.comp hn
    have h0 := hl 0 (le_refl 0)
    have hpi := hl Real.pi Real.pi_pos.le
    simp_rw [Q_div_cos_one hc] at h0
    simp_rw [Q_div_cos_neg hc] at hpi
    obtain ⟨M, hM⟩ := h0.abs.isBoundedUnder_le
    have hp : 0 ≤ a - c - 2 := exponent_nonneg_of_bounded (point_zero hc 0)
      (point_pos (le_refl 0)) tendsto_const_nhds (neg_ne_zero.mpr hc.ne') hM
    have hne : a - c - 2 ≠ 0 := by
      intro he
      simp only [he, Real.rpow_zero, one_mul] at h0 hpi
      have e0 := tendsto_nhds_unique h0 tendsto_const_nhds
      have e1 := tendsto_nhds_unique hpi tendsto_const_nhds
      linarith
    have := lt_of_le_of_ne hp (Ne.symm hne)
    linarith
  · intro ha; exact (D_deriv_zero ha hc).differentiableAt

theorem second_exists {a c : ℝ} (ha : 2 + c < a) (hc : 0 < c) : Second (D a c) (E a c) := by
  intro x hx
  by_cases h : x = 0
  · subst x; simpa using (D_deriv_zero ha hc).hasDerivWithinAt (s := interval)
  · exact (D_deriv_off a c h).hasDerivWithinAt

theorem second_identify {a c : ℝ} (hc : 0 < c) {g h : ℝ → ℝ}
    (hg : First a c g) (hh : Second g h) :
    2 + c < a ∧ EqOn h (E a c) interval := by
  have he := (first_identify hc hg).2
  have hd : HasDerivAt (D a c) (h 0) 0 :=
    ((hh 0 zero_mem).congr (fun x hx => (he hx).symm) ((he zero_mem).symm)).hasDerivAt zero_interior
  have ha := (D_derivative_iff hc).mp hd.differentiableAt
  refine ⟨ha, fun x hx => ?_⟩
  have hu := (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) x hx
  have hh' := (hh x hx).congr (fun y hy => (he hy).symm) ((he hx).symm)
  exact (hh'.derivWithin hu).symm.trans ((second_exists ha hc x hx).derivWithin hu)

theorem E_bound (a c x : ℝ) :
    |E a c x| ≤ |a * (a - 1)| * |x| ^ (a - 2) +
      |c * (2 * a - c - 1)| * |x| ^ (a - c - 2) +
      c ^ 2 * |x| ^ (a - 2 * c - 2) := by
  by_cases hx : x = 0
  · subst x; simp only [E_zero, abs_zero]; positivity
  rw [E, ite_eq_right (by exact hx)]
  unfold R
  calc
    _ ≤ (|a * (a - 1) * |x| ^ (a - 2) * Real.sin (|x| ^ (-c))| +
        |c * (2 * a - c - 1) * |x| ^ (a - c - 2) * Real.cos (|x| ^ (-c))|) +
        |c ^ 2 * |x| ^ (a - 2 * c - 2) * Real.sin (|x| ^ (-c))| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _), abs_sq]
      exact add_le_add
        (add_le_add (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _))
          (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)))
        (mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _))

theorem E_vanish {a c : ℝ} (h1 : 0 < a - 2) (h2 : 0 < a - c - 2)
    (h3 : 0 < a - 2 * c - 2) : Tendsto (E a c) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (fun x => E_bound a c x)
  simpa using (((pow_abs_zero h1).const_mul |a * (a - 1)|).add
    ((pow_abs_zero h2).const_mul |c * (2 * a - c - 1)|)).add
    ((pow_abs_zero h3).const_mul (c ^ 2))

theorem E_cont_off (a c : ℝ) {x : ℝ} (hx : x ≠ 0) : ContinuousAt (E a c) x := by
  have hab : |x| ≠ 0 := abs_ne_zero.mpr hx
  have h : ContinuousAt (fun y : ℝ => R a c |y|) x := by
    unfold R
    fun_prop (disch := aesop)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [E, hy]

/-- At the sine-one phases the second derivative factors into its leading
power and a coefficient that tends to `-c^2`, not to zero. -/
theorem R_sin_one {a c : ℝ} (hc : 0 < c) (n : ℕ) :
    R a c (point c (Real.pi / 2) n) =
      point c (Real.pi / 2) n ^ (a - 2 * c - 2) *
        (a * (a - 1) * point c (Real.pi / 2) n ^ (2 * c) - c ^ 2) := by
  have hb : 0 ≤ Real.pi / 2 := by positivity
  simp only [R, point_sin hc hb, point_cos hc hb, Real.sin_pi_div_two,
    Real.cos_pi_div_two, mul_one, mul_zero, sub_zero]
  have hh : point c (Real.pi / 2) n ^ (a - 2 * c - 2) *
      point c (Real.pi / 2) n ^ (2 * c) = point c (Real.pi / 2) n ^ (a - 2) := by
    rw [← Real.rpow_add (point_pos hb n)]
    congr 1; ring
  calc
    _ = a * (a - 1) * (point c (Real.pi / 2) n ^ (a - 2 * c - 2) *
        point c (Real.pi / 2) n ^ (2 * c)) -
        c ^ 2 * point c (Real.pi / 2) n ^ (a - 2 * c - 2) := by rw [hh]
    _ = _ := by ring

theorem R_coefficient_limit (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n => a * (a - 1) * point c (Real.pi / 2) n ^ (2 * c) - c ^ 2)
      atTop (𝓝 (-(c ^ 2))) := by
  have hp : 0 < 2 * c := by positivity
  have hh := (Real.continuousAt_rpow_const 0 (2 * c) (Or.inr hp.le)).tendsto.comp
    (point_zero hc (Real.pi / 2))
  simp only [Function.comp_def, Real.zero_rpow hp.ne'] at hh
  simpa using (hh.const_mul (a * (a - 1))).sub_const (c ^ 2)

theorem E_bounded_iff {a c : ℝ} (hc : 0 < c) :
    (∃ M : ℝ, ∀ x ∈ interval, |E a c x| ≤ M) ↔ 2 + 2 * c ≤ a := by
  constructor
  · rintro ⟨M, hM⟩
    have hb : 0 ≤ Real.pi / 2 := by positivity
    have h : ∀ᶠ n in atTop,
        |point c (Real.pi / 2) n ^ (a - 2 * c - 2) *
          (a * (a - 1) * point c (Real.pi / 2) n ^ (2 * c) - c ^ 2)| ≤ M := by
      filter_upwards [point_mem hc hb] with n hn
      simpa only [E_pos a c (point_pos hb n), R_sin_one hc] using hM _ hn
    have := exponent_nonneg_of_bounded (point_zero hc (Real.pi / 2)) (point_pos hb)
      (R_coefficient_limit a hc) (neg_ne_zero.mpr (pow_ne_zero 2 hc.ne')) h
    linarith
  · intro ha
    refine ⟨|a * (a - 1)| + |c * (2 * a - c - 1)| + c ^ 2,
      fun x hx => (E_bound a c x).trans ?_⟩
    have hab : |x| ≤ 1 := abs_le.mpr hx
    exact add_le_add (add_le_add
      (mul_le_of_le_one_right (abs_nonneg _)
        (Real.rpow_le_one (abs_nonneg x) hab (by linarith)))
      (mul_le_of_le_one_right (abs_nonneg _)
        (Real.rpow_le_one (abs_nonneg x) hab (by linarith))))
      (mul_le_of_le_one_right (sq_nonneg c)
        (Real.rpow_le_one (abs_nonneg x) hab (by linarith)))

theorem E_cont_iff {a c : ℝ} (hc : 0 < c) :
    ContinuousOn (E a c) interval ↔ 2 + 2 * c < a := by
  constructor
  · intro hd
    have hb : 0 ≤ Real.pi / 2 := by positivity
    have ht := point_zero hc (Real.pi / 2)
    have hl := (hd 0 zero_mem).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨ht, point_mem hc hb⟩)
    simp only [Function.comp_def, E_zero] at hl
    have he : (fun n => E a c (point c (Real.pi / 2) n)) =
        (fun n => point c (Real.pi / 2) n ^ (a - 2 * c - 2) *
          (a * (a - 1) * point c (Real.pi / 2) n ^ (2 * c) - c ^ 2)) := by
      funext n; rw [E_pos a c (point_pos hb n), R_sin_one hc]
    rw [he] at hl
    have := exponent_pos_of_zero ht (point_pos hb) (R_coefficient_limit a hc)
      (neg_ne_zero.mpr (pow_ne_zero 2 hc.ne')) hl
    linarith
  · intro ha x hx
    by_cases h : x = 0
    · subst x
      have hh : ContinuousAt (E a c) 0 := by
        rw [ContinuousAt, E_zero]
        exact E_vanish (by linarith) (by linarith) (by linarith)
      exact hh.continuousWithinAt
    · exact (E_cont_off a c h).continuousWithinAt

end Exercise13

/-- R05E13(f). Both derivatives exist on the closed interval. The non-strict
threshold includes the bounded, discontinuous equality case. -/
theorem exercise13_f {a c : ℝ} (hc : 0 < c) :
    (∃ g h : ℝ → ℝ, Exercise13.First a c g ∧ Exercise13.Second g h ∧
      ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |h x| ≤ M) ↔ 2 + 2 * c ≤ a := by
  constructor
  · rintro ⟨g, h, hg, hh, M, hM⟩
    have he := (Exercise13.second_identify hc hg hh).2
    apply (Exercise13.E_bounded_iff hc).mp
    exact ⟨M, fun x hx => (he hx) ▸ hM x hx⟩
  · intro ha
    exact ⟨Exercise13.D a c, Exercise13.E a c, Exercise13.first_exists (by linarith),
      Exercise13.second_exists (by linarith) hc, (Exercise13.E_bounded_iff hc).mpr ha⟩

/-- R05E13(g), with existence of the lower derivatives explicitly required. -/
theorem exercise13_g {a c : ℝ} (hc : 0 < c) :
    (∃ g h : ℝ → ℝ, Exercise13.First a c g ∧ Exercise13.Second g h ∧
      ContinuousOn h (Icc (-1) 1)) ↔ 2 + 2 * c < a := by
  constructor
  · rintro ⟨g, h, hg, hh, hcont⟩
    apply (Exercise13.E_cont_iff hc).mp
    exact hcont.congr (fun x hx => ((Exercise13.second_identify hc hg hh).2 hx).symm)
  · intro ha
    exact ⟨Exercise13.D a c, Exercise13.E a c, Exercise13.first_exists (by linarith),
      Exercise13.second_exists (by linarith) hc, (Exercise13.E_cont_iff hc).mpr ha⟩

/-- R05E13(e). The first derivative exists on the interval before the second
derivative at zero is requested. This is equivalent to the local formulation,
since the corrected function is differentiable at every nonzero point. -/
theorem exercise13_e {a c : ℝ} (hc : 0 < c) :
    (∃ g : ℝ → ℝ, Exercise13.First a c g ∧
      DifferentiableWithinAt ℝ g (Icc (-1) 1) 0) ↔ 2 + c < a := by
  constructor
  · rintro ⟨g, hg, hd⟩
    have he := (Exercise13.first_identify hc hg).2
    have hh := hd.hasDerivWithinAt.congr (fun x hx => (he hx).symm)
      ((he Exercise13.zero_mem).symm)
    exact (Exercise13.D_derivative_iff hc).mp (hh.hasDerivAt Exercise13.zero_interior).differentiableAt
  · intro ha
    exact ⟨Exercise13.D a c, Exercise13.first_exists (by linarith),
      (Exercise13.D_deriv_zero ha hc).differentiableAt.differentiableWithinAt⟩

/-- The local form of R05E13(e). The first derivative is required genuinely
on a neighborhood of zero, without any continuity assumption on it. -/
theorem exercise13_e_local {a c : ℝ} (hc : 0 < c) :
    (∃ g : ℝ → ℝ, (∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (exercise13F a c) (g x) x) ∧
      DifferentiableAt ℝ g 0) ↔ 2 + c < a := by
  constructor
  · rintro ⟨g, hg, hd⟩
    have ha := (Exercise13.derivative_iff (a := a) hc).mp hg.self_of_nhds.differentiableAt
    have he : Exercise13.D a c =ᶠ[𝓝 (0 : ℝ)] g := by
      filter_upwards [hg] with x hx
      have hf : HasDerivAt (exercise13F a c) (Exercise13.D a c x) x := by
        by_cases h : x = 0
        · subst x; simpa using Exercise13.F_deriv_zero ha c
        · exact Exercise13.F_deriv_off a c h
      exact hf.unique hx
    exact (Exercise13.D_derivative_iff hc).mp (hd.congr_of_eventuallyEq he)
  · intro ha
    refine ⟨Exercise13.D a c, Filter.Eventually.of_forall ?_,
      (Exercise13.D_deriv_zero ha hc).differentiableAt⟩
    intro x
    by_cases h : x = 0
    · subst x; simpa using Exercise13.F_deriv_zero (by linarith : 1 < a) c
    · exact Exercise13.F_deriv_off a c h

/-- The interval and local formulations of the second derivative at zero
agree for this construction. -/
theorem exercise13_e_local_iff_interval {a c : ℝ} (hc : 0 < c) :
    (∃ g : ℝ → ℝ, (∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt (exercise13F a c) (g x) x) ∧
      DifferentiableAt ℝ g 0) ↔
    (∃ g : ℝ → ℝ, Exercise13.First a c g ∧
      DifferentiableWithinAt ℝ g (Icc (-1) 1) 0) :=
  (exercise13_e_local hc).trans (exercise13_e hc).symm

/-- R05E13(c). Existence is part of the assertion; equality is included. -/
theorem exercise13_c {a c : ℝ} (hc : 0 < c) :
    (∃ g : ℝ → ℝ, Exercise13.First a c g ∧
      ∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |g x| ≤ M) ↔ 1 + c ≤ a := by
  constructor
  · rintro ⟨g, hg, M, hM⟩
    have he := (Exercise13.first_identify hc hg).2
    apply (Exercise13.D_bounded_iff hc).mp
    exact ⟨M, fun x hx => (he hx) ▸ hM x hx⟩
  · intro ha
    exact ⟨Exercise13.D a c, Exercise13.first_exists (by linarith),
      (Exercise13.D_bounded_iff hc).mpr ha⟩

/-- R05E13(d), including genuine first derivatives at every point. -/
theorem exercise13_d {a c : ℝ} (hc : 0 < c) :
    (∃ g : ℝ → ℝ, Exercise13.First a c g ∧ ContinuousOn g (Icc (-1) 1)) ↔ 1 + c < a := by
  constructor
  · rintro ⟨g, hg, hcont⟩
    apply (Exercise13.D_cont_iff hc).mp
    exact hcont.congr (fun x hx => ((Exercise13.first_identify hc hg).2 hx).symm)
  · intro ha
    exact ⟨Exercise13.D a c, Exercise13.first_exists (by linarith),
      (Exercise13.D_cont_iff hc).mpr ha⟩

/-- R05E13(b): a genuine derivative, not a value of the totalized `deriv`. -/
theorem exercise13_b {a c : ℝ} (hc : 0 < c) :
    DifferentiableAt ℝ (exercise13F a c) 0 ↔ 1 < a := Exercise13.derivative_iff hc

/-- R05E13(a), for the explicitly corrected absolute-power function. -/
theorem exercise13_a {a c : ℝ} (hc : 0 < c) :
    ContinuousOn (exercise13F a c) (Icc (-1) 1) ↔ 0 < a :=
  Exercise13.continuous_iff hc

/-- At the first boundedness threshold the derivative is bounded but not continuous. -/
theorem exercise13_first_equality {c : ℝ} (hc : 0 < c) :
    Exercise13.First (1 + c) c (Exercise13.D (1 + c) c) ∧
    (∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |Exercise13.D (1 + c) c x| ≤ M) ∧
    ¬ ContinuousOn (Exercise13.D (1 + c) c) (Icc (-1) 1) := by
  refine ⟨Exercise13.first_exists (by linarith),
    (Exercise13.D_bounded_iff hc).mpr le_rfl, ?_⟩
  intro hh
  exact (lt_irrefl (1 + c)) ((Exercise13.D_cont_iff hc).mp hh)

/-- At the second boundedness threshold both derivatives exist, and the second
derivative is bounded but not continuous. -/
theorem exercise13_second_equality {c : ℝ} (hc : 0 < c) :
    Exercise13.First (2 + 2 * c) c (Exercise13.D (2 + 2 * c) c) ∧
    Exercise13.Second (Exercise13.D (2 + 2 * c) c) (Exercise13.E (2 + 2 * c) c) ∧
    (∃ M : ℝ, ∀ x ∈ Icc (-1) 1, |Exercise13.E (2 + 2 * c) c x| ≤ M) ∧
    ¬ ContinuousOn (Exercise13.E (2 + 2 * c) c) (Icc (-1) 1) := by
  refine ⟨Exercise13.first_exists (by linarith),
    Exercise13.second_exists (by linarith) hc,
    (Exercise13.E_bounded_iff hc).mpr le_rfl, ?_⟩
  intro hh
  exact (lt_irrefl (2 + 2 * c)) ((Exercise13.E_cont_iff hc).mp hh)

end Rudin.Chapter05
