module

public import Math.Rudin.Chapter09.Exercise20
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Exercise 21: a cubic, its extrema, and its complete zero set
Source: Rudin, book 241–242 (PDF 250–251).
The product coordinates below are used only for topology and differentiation,
not to assert a Euclidean distance formula.
-/
@[expose] public section
open Set Filter
open scoped Topology
namespace Rudin.Chapter09

/-- The full zero set in a neighborhood, not just a selected branch.
Continuity and the base value ensure that all nearby independent coordinates
have a zero in this neighborhood. -/
def ZeroGraphX (f : ℝ × ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ U ∈ 𝓝 (a, b), ∃ g : ℝ → ℝ, ContinuousAt g b ∧ g b = a ∧
    ∀ p ∈ U, f p = 0 ↔ p.1 = g p.2

def ZeroGraphY (f : ℝ × ℝ → ℝ) (a b : ℝ) : Prop :=
  ZeroGraphX (fun p => f (p.2, p.1)) b a

/-- Arbitrarily close distinct zeros in the same fiber. -/
def MultipleFibersX (f : ℝ × ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ U ∈ 𝓝 (a, b), ∃ p ∈ U, ∃ q ∈ U,
    f p = 0 ∧ f q = 0 ∧ p.2 = q.2 ∧ p.1 ≠ q.1

def MultipleFibersY (f : ℝ × ℝ → ℝ) (a b : ℝ) : Prop :=
  MultipleFibersX (fun p => f (p.2, p.1)) b a

theorem multipleFibers_not_graph {f : ℝ × ℝ → ℝ} {a b : ℝ}
    (h : MultipleFibersX f a b) : ¬ ZeroGraphX f a b := by
  rintro ⟨U, hU, g, _, _, hg⟩
  obtain ⟨p, hp, q, hq, hpz, hqz, he, hn⟩ := h U hU
  exact hn (by rw [(hg p hp).mp hpz, (hg q hq).mp hqz, he])

theorem zeroGraphX_of_partial {f : ℝ × ℝ → ℝ} {a b d : ℝ}
    (hc : ContDiffAt ℝ 1 f (a, b)) (hz : f (a, b) = 0)
    (hd : HasDerivAt (fun x => f (x, b)) d a) (hn : d ≠ 0) :
    ZeroGraphX f a b := by
  have he := (exercise20_partials hc).1.unique hd
  obtain ⟨S, _⟩ := exercise20_graph hc hz (by rwa [he])
  refine ⟨S.e.source ∩ Prod.snd ⁻¹' S.W,
    inter_mem (S.e.open_source.mem_nhds S.base_mem)
      ((S.open_W.preimage continuous_snd).mem_nhds S.mem_W),
    S.g, S.derivative.continuousAt, S.base_value, ?_⟩
  intro p hp
  exact S.unique p.2 hp.2 p.1 hp.1

/-- A continuous local zero curve furnished by the scalar IFT. -/
theorem zeroCurve_of_partial {f : ℝ × ℝ → ℝ} {a b d : ℝ}
    (hc : ContDiffAt ℝ 1 f (a, b)) (hz : f (a, b) = 0)
    (hd : HasDerivAt (fun x => f (x, b)) d a) (hn : d ≠ 0) :
    ∃ g : ℝ → ℝ, ContinuousAt g b ∧ g b = a ∧
      ∀ᶠ t in 𝓝 b, f (g t, t) = 0 := by
  have he := (exercise20_partials hc).1.unique hd
  obtain ⟨S, _⟩ := exercise20_graph hc hz (by rwa [he])
  exact ⟨S.g, S.derivative.continuousAt, S.base_value,
    Filter.eventually_of_mem (S.open_W.mem_nhds S.mem_W) S.equation⟩

/-- Two convergent zero curves give an obstruction in every neighborhood. -/
theorem multipleFibers_of_curves {f : ℝ × ℝ → ℝ} {a b c : ℝ}
    {p q : ℝ → ℝ × ℝ}
    (hp : Tendsto p (𝓝 c) (𝓝 (a, b)))
    (hq : Tendsto q (𝓝 c) (𝓝 (a, b)))
    (hz : ∀ᶠ t in 𝓝[≠] c,
      f (p t) = 0 ∧ f (q t) = 0 ∧ (p t).2 = (q t).2 ∧ (p t).1 ≠ (q t).1) :
    MultipleFibersX f a b := by
  intro U hU
  have h : ∀ᶠ t in 𝓝[≠] c, p t ∈ U ∧ q t ∈ U :=
    ((hp.eventually hU).and (hq.eventually hU)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨htp, htq⟩, ht⟩ := (h.and hz).exists
  exact ⟨p t, htp, q t, htq, ht⟩

noncomputable def exercise21Function (p : ℝ × ℝ) : ℝ :=
  2 * p.1 ^ 3 - 3 * p.1 ^ 2 + 2 * p.2 ^ 3 + 3 * p.2 ^ 2

theorem exercise21_smooth : ContDiff ℝ ⊤ exercise21Function := by
  unfold exercise21Function; fun_prop

theorem exercise21_partials (x y : ℝ) :
    HasDerivAt (fun t => exercise21Function (t, y)) (6 * x * (x - 1)) x ∧
    HasDerivAt (fun t => exercise21Function (x, t)) (6 * y * (y + 1)) y := by
  constructor
  · convert (((((hasDerivAt_id x).pow 3).const_mul 2).sub
      (((hasDerivAt_id x).pow 2).const_mul 3)).add_const (2 * y ^ 3)).add_const
        (3 * y ^ 2) using 1 <;> dsimp [exercise21Function] <;> ring
  · convert (((hasDerivAt_const y (2 * x ^ 3 - 3 * x ^ 2)).add
      (((hasDerivAt_id y).pow 3).const_mul 2)).add
      (((hasDerivAt_id y).pow 2).const_mul 3)) using 1 <;>
      dsimp [exercise21Function] <;> (try ring) <;> ext t <;> dsimp <;> ring

/-- The two actual coordinate derivatives vanish at exactly four points. -/
theorem exercise21_stationary (x y : ℝ) :
    (deriv (fun t => exercise21Function (t, y)) x = 0 ∧
      deriv (fun t => exercise21Function (x, t)) y = 0) ↔
    (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = -1) := by
  rw [(exercise21_partials x y).1.deriv, (exercise21_partials x y).2.deriv]
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · rcases mul_eq_zero.mp hx with h | h
      · left; nlinarith
      · right; linarith
    · rcases mul_eq_zero.mp hy with h | h
      · left; nlinarith
      · right; linarith
  · rintro ⟨hx | hx, hy | hy⟩ <;> simp [hx, hy]

theorem exercise21_factor (x y : ℝ) :
    exercise21Function (x, y) =
      (x + y) * (2 * x ^ 2 - 2 * x * y + 2 * y ^ 2 - 3 * x + 3 * y) := by
  unfold exercise21Function; ring

/-- A straight line and an ellipse in the rotated coordinates u=x+y, v=x−y. -/
theorem exercise21_zero_set (x y : ℝ) :
    exercise21Function (x, y) = 0 ↔
    y = -x ∨ (x + y) ^ 2 + 3 * (x - y - 1) ^ 2 = 3 := by
  rw [exercise21_factor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; nlinarith
  · rintro (h | h)
    · left; linarith
    · right; nlinarith

theorem exercise21_intersections (x y : ℝ) :
    (y = -x ∧ (x + y) ^ 2 + 3 * (x - y - 1) ^ 2 = 3) ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) := by
  constructor
  · rintro ⟨rfl, h⟩
    have he : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with hx | hx
    · left; simp [hx]
    · right; have : x = 1 := by linarith
      simp [this]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

theorem exercise21_reflection (x y : ℝ) :
    exercise21Function (1 - x, -1 - y) = -exercise21Function (x, y) := by
  unfold exercise21Function; ring

theorem exercise21_swap (x y : ℝ) :
    exercise21Function (-y, -x) = -exercise21Function (x, y) := by
  unfold exercise21Function; ring

/-- Both signs occur in every neighborhood. -/
def Saddle (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) : Prop :=
  ∀ U ∈ 𝓝 a, ∃ p ∈ U, ∃ q ∈ U, f p < f a ∧ f a < f q

theorem saddle_not_extremum {f : ℝ × ℝ → ℝ} {a : ℝ × ℝ}
    (h : Saddle f a) : ¬ IsLocalMin f a ∧ ¬ IsLocalMax f a := by
  constructor
  · intro hm
    obtain ⟨p, hp, q, hq, hl, hr⟩ := h _ hm
    exact (not_lt_of_ge hp) hl
  · intro hm
    obtain ⟨p, hp, q, hq, hl, hr⟩ := h _ hm
    exact (not_lt_of_ge hq) hr

theorem saddle_of_curves {f : ℝ × ℝ → ℝ} {a : ℝ × ℝ}
    {p q : ℝ → ℝ × ℝ}
    (hp : Tendsto p (𝓝 (0 : ℝ)) (𝓝 a))
    (hq : Tendsto q (𝓝 (0 : ℝ)) (𝓝 a))
    (hv : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f (p t) < f a ∧ f a < f (q t)) :
    Saddle f a := by
  intro U hU
  have h : ∀ᶠ t in 𝓝[≠] (0 : ℝ), p t ∈ U ∧ q t ∈ U :=
    ((hp.eventually hU).and (hq.eventually hU)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨hp, hq⟩, hv⟩ := (h.and hv).exists
  exact ⟨p t, hp, q t, hq, hv⟩

theorem exercise21_saddle_origin : Saddle exercise21Function (0, 0) := by
  apply saddle_of_curves (p := fun t => (t, 0)) (q := fun t => (0, t))
  · exact continuousAt_id.prodMk continuousAt_const
  · exact continuousAt_const.prodMk continuousAt_id
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
  have hs := sq_pos_of_ne_zero hn
  have h1 := mul_pos hs (show 0 < 3 - 2 * t by linarith [ht.2])
  have h2 := mul_pos hs (show 0 < 3 + 2 * t by linarith [ht.1])
  dsimp [exercise21Function]
  constructor <;> nlinarith

theorem exercise21_saddle_intersection : Saddle exercise21Function (1, -1) := by
  intro U hU
  have hc : Continuous (fun p : ℝ × ℝ => (1 - p.1, -1 - p.2)) := by fun_prop
  have ht : Tendsto (fun p : ℝ × ℝ => (1 - p.1, -1 - p.2))
      (𝓝 (0, 0)) (𝓝 (1, -1)) := by convert hc.continuousAt.tendsto using 1 <;> norm_num
  obtain ⟨p, hp, q, hq, hl, hr⟩ := exercise21_saddle_origin _ (ht.eventually hU)
  refine ⟨(1 - q.1, -1 - q.2), hq, (1 - p.1, -1 - p.2), hp, ?_⟩
  rw [exercise21_reflection, exercise21_reflection]
  norm_num [exercise21Function] at hl hr ⊢
  exact ⟨by linarith, by linarith⟩

/-- An exact positive-definite increment at the unique minimum. -/
theorem exercise21_min_increment (x y : ℝ) :
    exercise21Function (x, y) - exercise21Function (1, 0) =
      (x - 1) ^ 2 * (2 * x + 1) + y ^ 2 * (2 * y + 3) := by
  unfold exercise21Function; ring

theorem exercise21_minimum : IsLocalMin exercise21Function (1, 0) ∧
    ∀ᶠ p in 𝓝[≠] ((1, 0) : ℝ × ℝ), exercise21Function (1, 0) < exercise21Function p := by
  have hb : ∀ᶠ p : ℝ × ℝ in 𝓝 (1, 0), 0 < 2 * p.1 + 1 ∧ 0 < 2 * p.2 + 3 := by
    exact ((isOpen_lt continuous_const (by fun_prop : Continuous (fun p : ℝ × ℝ => 2 * p.1 + 1))).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous (fun p : ℝ × ℝ => 2 * p.2 + 3)))).mem_nhds
        (by norm_num)
  constructor
  · filter_upwards [hb] with p hp
    have he := exercise21_min_increment p.1 p.2
    have h1 := mul_nonneg (sq_nonneg (p.1 - 1)) hp.1.le
    have h2 := mul_nonneg (sq_nonneg p.2) hp.2.le
    change exercise21Function (1, 0) ≤ exercise21Function (p.1, p.2)
    linarith
  · filter_upwards [hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with p hp hn
    have he := exercise21_min_increment p.1 p.2
    have h1 := mul_nonneg (sq_nonneg (p.1 - 1)) hp.1.le
    have h2 := mul_nonneg (sq_nonneg p.2) hp.2.le
    have hne : p.1 ≠ 1 ∨ p.2 ≠ 0 := by
      by_contra! h; exact hn (Prod.ext h.1 h.2)
    change exercise21Function (1, 0) < exercise21Function (p.1, p.2)
    rcases hne with h | h
    · have := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) hp.1; linarith
    · have := mul_pos (sq_pos_of_ne_zero h) hp.2; linarith

theorem exercise21_maximum : IsLocalMax exercise21Function (0, -1) ∧
    ∀ᶠ p in 𝓝[≠] ((0, -1) : ℝ × ℝ), exercise21Function p < exercise21Function (0, -1) := by
  have hc : Continuous (fun p : ℝ × ℝ => (1 - p.1, -1 - p.2)) := by fun_prop
  have ht : Tendsto (fun p : ℝ × ℝ => (1 - p.1, -1 - p.2))
      (𝓝 (0, -1)) (𝓝 (1, 0)) := by convert hc.continuousAt.tendsto using 1 <;> norm_num
  constructor
  · have h := ht.eventually exercise21_minimum.1
    filter_upwards [h] with p hp
    rw [exercise21_reflection] at hp
    norm_num [exercise21Function] at hp ⊢
    linarith
  · have htp : Tendsto (fun p : ℝ × ℝ => (1 - p.1, -1 - p.2))
        (𝓝[≠] (0, -1)) (𝓝[≠] (1, 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨ht.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with p hp
      intro he
      apply hp
      have h := Prod.mk.inj he
      apply Prod.ext <;> dsimp at h ⊢ <;> linarith [h.1, h.2]
    have h := htp.eventually exercise21_minimum.2
    filter_upwards [h] with p hp
    rw [exercise21_reflection] at hp
    norm_num [exercise21Function] at hp ⊢
    linarith

theorem exercise21_extrema (x y : ℝ) :
    (IsLocalMin exercise21Function (x, y) ↔ x = 1 ∧ y = 0) ∧
    (IsLocalMax exercise21Function (x, y) ↔ x = 0 ∧ y = -1) := by
  have crit (h : IsLocalMin exercise21Function (x, y) ∨ IsLocalMax exercise21Function (x, y)) :
      (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = -1) := by
    apply (exercise21_stationary x y).mp
    rcases h with h | h
    · exact ⟨(h.comp_continuous (g := fun t : ℝ => (t, y))
          (continuousAt_id.prodMk continuousAt_const)).deriv_eq_zero,
        (h.comp_continuous (g := fun t : ℝ => (x, t))
          (continuousAt_const.prodMk continuousAt_id)).deriv_eq_zero⟩
    · exact ⟨(h.comp_continuous (g := fun t : ℝ => (t, y))
          (continuousAt_id.prodMk continuousAt_const)).deriv_eq_zero,
        (h.comp_continuous (g := fun t : ℝ => (x, t))
          (continuousAt_const.prodMk continuousAt_id)).deriv_eq_zero⟩
  have notmin : ¬ IsLocalMin exercise21Function (0, -1) := by
    intro h
    have hh := (h.filter_mono nhdsWithin_le_nhds).and exercise21_maximum.2
    obtain ⟨p, hp, hq⟩ := hh.exists
    exact (not_lt_of_ge hp) hq
  have notmax : ¬ IsLocalMax exercise21Function (1, 0) := by
    intro h
    have hh := (h.filter_mono nhdsWithin_le_nhds).and exercise21_minimum.2
    obtain ⟨p, hp, hq⟩ := hh.exists
    exact (not_lt_of_ge hp) hq
  constructor
  · constructor
    · intro h
      obtain ⟨hx | hx, hy | hy⟩ := crit (Or.inl h) <;> subst x <;> subst y
      · exact False.elim ((saddle_not_extremum exercise21_saddle_origin).1 h)
      · exact False.elim (notmin h)
      · exact ⟨rfl, rfl⟩
      · exact False.elim ((saddle_not_extremum exercise21_saddle_intersection).1 h)
    · rintro ⟨rfl, rfl⟩; exact exercise21_minimum.1
  · constructor
    · intro h
      obtain ⟨hx | hx, hy | hy⟩ := crit (Or.inr h) <;> subst x <;> subst y
      · exact False.elim ((saddle_not_extremum exercise21_saddle_origin).2 h)
      · exact ⟨rfl, rfl⟩
      · exact False.elim (notmax h)
      · exact False.elim ((saddle_not_extremum exercise21_saddle_intersection).2 h)
    · rintro ⟨rfl, rfl⟩; exact exercise21_maximum.1

theorem multipleFibers_affine {f h : ℝ × ℝ → ℝ} {a b u v w z : ℝ}
    (hm : MultipleFibersX f a b) (hu : u ≠ 0)
    (hz : ∀ x y, f (x, y) = 0 → h (u * x + v, w * y + z) = 0) :
    MultipleFibersX h (u * a + v) (w * b + z) := by
  intro U hU
  have ht : Tendsto (fun p : ℝ × ℝ => (u * p.1 + v, w * p.2 + z))
      (𝓝 (a, b)) (𝓝 (u * a + v, w * b + z)) := by
    exact (show Continuous (fun p : ℝ × ℝ => (u * p.1 + v, w * p.2 + z)) by fun_prop).continuousAt
  obtain ⟨p, hp, q, hq, hpz, hqz, he, hn⟩ := hm _ (ht.eventually hU)
  exact ⟨_, hp, _, hq, hz _ _ hpz, hz _ _ hqz, by dsimp; rw [he],
    fun hh => hn (mul_left_cancel₀ hu (add_right_cancel hh))⟩

/-- A second branch meeting the line transversely gives collisions in both projections. -/
theorem exercise21_crossing {a b c : ℝ} (hab : a + b = 0) {p : ℝ → ℝ × ℝ}
    (hp : Tendsto p (𝓝 c) (𝓝 (a, b)))
    (hz : ∀ᶠ t in 𝓝[≠] c, exercise21Function (p t) = 0 ∧ (p t).1 + (p t).2 ≠ 0) :
    MultipleFibersX exercise21Function a b ∧ MultipleFibersY exercise21Function a b := by
  have hx : Tendsto (fun t => (p t).1) (𝓝 c) (𝓝 a) := (continuous_fst.tendsto (a, b)).comp hp
  have hy : Tendsto (fun t => (p t).2) (𝓝 c) (𝓝 b) := (continuous_snd.tendsto (a, b)).comp hp
  constructor
  · apply multipleFibers_of_curves hp (q := fun t => (-(p t).2, (p t).2))
    · simpa only [show -b = a by linarith] using hy.neg.prodMk_nhds hy
    · filter_upwards [hz] with t ht
      refine ⟨ht.1, (exercise21_zero_set _ _).mpr (Or.inl (by ring)), rfl, ?_⟩
      intro he; exact ht.2 (by linarith)
  · apply multipleFibers_of_curves (p := fun t => ((p t).2, (p t).1))
      (q := fun t => (-(p t).1, (p t).1)) (hy.prodMk_nhds hx)
    · simpa only [show -a = b by linarith] using hx.neg.prodMk_nhds hx
    · filter_upwards [hz] with t ht
      refine ⟨ht.1, (exercise21_zero_set _ _).mpr (Or.inl rfl), rfl, ?_⟩
      intro he; exact ht.2 (by linarith)

theorem exercise21_node_origin :
    MultipleFibersX exercise21Function 0 0 ∧ MultipleFibersY exercise21Function 0 0 := by
  let Q : ℝ × ℝ → ℝ := fun p =>
    2 * p.1 ^ 2 - 2 * p.1 * p.2 + 2 * p.2 ^ 2 - 3 * p.1 + 3 * p.2
  have hd : HasDerivAt (fun x => Q (x, 0)) (-3) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul 2).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul 3) using 1
    · ext x; dsimp [Q]; ring
    · norm_num
  obtain ⟨g, hc, hg, hz⟩ := zeroCurve_of_partial (f := Q)
    (by dsimp [Q]; fun_prop) (by norm_num [Q]) hd (by norm_num)
  have ht : Tendsto (fun t => (g t, t)) (𝓝 (0 : ℝ)) (𝓝 (0, 0)) := by
    simpa only [hg, id_eq] using hc.tendsto.prodMk_nhds (Filter.tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  apply exercise21_crossing (by norm_num) ht
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), g t ≠ 1 :=
    hc.eventually (eventually_ne_nhds (show g 0 ≠ 1 by rw [hg]; norm_num))
  filter_upwards [hz.filter_mono nhdsWithin_le_nhds, hn.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht hn htne
  have hf : exercise21Function (g t, t) = 0 := by rw [exercise21_factor]; exact mul_eq_zero_of_right _ ht
  refine ⟨hf, ?_⟩
  intro he
  have hell : (g t + t) ^ 2 + 3 * (g t - t - 1) ^ 2 = 3 := by dsimp [Q] at ht; nlinarith
  rcases (exercise21_intersections _ _).mp ⟨by linarith, hell⟩ with h | h
  · exact htne h.2
  · exact hn h.1

theorem exercise21_node_other :
    MultipleFibersX exercise21Function 1 (-1) ∧ MultipleFibersY exercise21Function 1 (-1) := by
  constructor
  · convert multipleFibers_affine (u := -1) (v := 1) (w := -1) (z := -1)
      exercise21_node_origin.1 (by norm_num) (h := exercise21Function) (by
        intro x y hz
        convert exercise21_reflection x y using 1 <;> first | (rw [hz]; ring) | congr 1 <;> ring) using 1 <;> norm_num
  · convert multipleFibers_affine (u := -1) (v := -1) (w := -1) (z := 1)
      exercise21_node_origin.2 (by norm_num)
      (h := fun p => exercise21Function (p.2, p.1)) (by
        intro x y hz
        change exercise21Function (-1 * y + 1, -1 * x + -1) = 0
        convert exercise21_reflection y x using 1 <;> first | (rw [hz]; ring) | congr 1 <;> ring) using 1 <;> norm_num [MultipleFibersY]

/-- Two distinct roots near the upper vertical tangency, with the same x coordinate. -/
theorem exercise21_fold_y : MultipleFibersY exercise21Function (3 / 2) 0 := by
  obtain ⟨g, hc, hg, hz⟩ := zeroCurve_of_partial
    (exercise21_smooth.contDiffAt.of_le (by norm_num))
    (by norm_num [exercise21Function] : exercise21Function (3 / 2, 0) = 0)
    (exercise21_partials (3 / 2) 0).1 (by norm_num)
  let s : ℝ → ℝ := fun t => (Real.sqrt (1 - 4 * t ^ 2 / 3) - 1) / 2
  have hs : ContinuousAt s 0 := by dsimp [s]; fun_prop
  have hs0 : s 0 = 0 := by norm_num [s]
  have hy : Tendsto (fun t => s t + t) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [hs0, add_zero, id_eq] using hs.tendsto.add (Filter.tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  have hy' : Tendsto (fun t => s t - t) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [hs0, sub_zero, id_eq] using hs.tendsto.sub (Filter.tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  have hx : Tendsto (fun t => g (s t + t)) (𝓝 (0 : ℝ)) (𝓝 (3 / 2)) := by
    rw [← hg]; exact hc.tendsto.comp hy
  apply multipleFibers_of_curves (p := fun t => (s t + t, g (s t + t)))
    (q := fun t => (s t - t, g (s t + t))) (hy.prodMk_nhds hx) (hy'.prodMk_nhds hx)
  have hb : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 - 4 * t ^ 2 / 3 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by norm_num)
  filter_upwards [(hy.eventually hz).filter_mono nhdsWithin_le_nhds,
    hb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hb hn
  have he : 6 * (s t) ^ 2 + 6 * s t + 2 * t ^ 2 = 0 := by
    have hh := Real.sq_sqrt hb.le
    dsimp [s]; nlinarith
  refine ⟨ht, ?_, rfl, ?_⟩
  · change exercise21Function (g (s t + t), s t - t) = 0
    dsimp [exercise21Function] at ht ⊢
    nlinarith [mul_eq_zero_of_right (4 * t) he]
  · dsimp; intro hh; change t ≠ 0 at hn; exact hn (by linarith)

theorem exercise21_fold_y_other : MultipleFibersY exercise21Function (-1 / 2) (-1) := by
  convert multipleFibers_affine (u := -1) (v := -1) (w := -1) (z := 1)
    exercise21_fold_y (by norm_num)
    (h := fun p => exercise21Function (p.2, p.1)) (by
      intro x y hz
      change exercise21Function (-1 * y + 1, -1 * x + -1) = 0
      convert exercise21_reflection y x using 1 <;> first | (rw [hz]; ring) | congr 1 <;> ring) using 1 <;> norm_num [MultipleFibersY]

theorem exercise21_fibers_swap {a b : ℝ} (h : MultipleFibersY exercise21Function a b) :
    MultipleFibersX exercise21Function (-b) (-a) := by
  convert multipleFibers_affine (u := -1) (v := 0) (w := -1) (z := 0)
    h (by norm_num) (h := exercise21Function) (by
      intro x y hz
      simp only [neg_mul, one_mul, add_zero]
      rw [exercise21_swap, hz, neg_zero]) using 1 <;> ring

/-- Exact graph failure, with explicit arbitrary-neighborhood collisions. -/
theorem exercise21_graph_y (x y : ℝ) (hz : exercise21Function (x, y) = 0) :
    (¬ ZeroGraphY exercise21Function x y) ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨
      (x = 3 / 2 ∧ y = 0) ∨ (x = -1 / 2 ∧ y = -1) := by
  have classify (hd : 6 * y * (y + 1) = 0) :
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨
      (x = 3 / 2 ∧ y = 0) ∨ (x = -1 / 2 ∧ y = -1) := by
    have hy : y = 0 ∨ y = -1 := by
      rcases mul_eq_zero.mp hd with h | h
      · left; nlinarith
      · right; linarith
    rcases hy with rfl | rfl
    · have he : x ^ 2 * (2 * x - 3) = 0 := by dsimp [exercise21Function] at hz; nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl ⟨by nlinarith [sq_nonneg x], rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨by linarith, rfl⟩))
    · have he : (x - 1) ^ 2 * (2 * x + 1) = 0 := by dsimp [exercise21Function] at hz; nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inr (Or.inl ⟨by nlinarith [sq_nonneg (x - 1)], rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, rfl⟩))
  constructor
  · intro hn
    apply classify
    by_contra hd
    exact hn (zeroGraphX_of_partial
      (by unfold exercise21Function; fun_prop) hz (exercise21_partials x y).2 hd)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact multipleFibers_not_graph exercise21_node_origin.2
    · exact multipleFibers_not_graph exercise21_node_other.2
    · exact multipleFibers_not_graph exercise21_fold_y
    · exact multipleFibers_not_graph exercise21_fold_y_other

theorem exercise21_graph_x (x y : ℝ) (hz : exercise21Function (x, y) = 0) :
    (¬ ZeroGraphX exercise21Function x y) ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨
      (x = 0 ∧ y = -3 / 2) ∨ (x = 1 ∧ y = 1 / 2) := by
  have classify (hd : 6 * x * (x - 1) = 0) :
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨
      (x = 0 ∧ y = -3 / 2) ∨ (x = 1 ∧ y = 1 / 2) := by
    have hx : x = 0 ∨ x = 1 := by
      rcases mul_eq_zero.mp hd with h | h
      · left; nlinarith
      · right; linarith
    rcases hx with rfl | rfl
    · have he : y ^ 2 * (2 * y + 3) = 0 := by dsimp [exercise21Function] at hz; nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inl ⟨rfl, by nlinarith [sq_nonneg y]⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, by linarith⟩))
    · have he : (y + 1) ^ 2 * (2 * y - 1) = 0 := by dsimp [exercise21Function] at hz; nlinarith
      rcases mul_eq_zero.mp he with h | h
      · exact Or.inr (Or.inl ⟨rfl, by nlinarith [sq_nonneg (y + 1)]⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, by linarith⟩))
  constructor
  · intro hn; apply classify; by_contra hd
    exact hn (zeroGraphX_of_partial (exercise21_smooth.contDiffAt.of_le (by norm_num))
      hz (exercise21_partials x y).1 hd)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact multipleFibers_not_graph exercise21_node_origin.1
    · exact multipleFibers_not_graph exercise21_node_other.1
    · apply multipleFibers_not_graph
      convert exercise21_fibers_swap exercise21_fold_y using 1 <;> norm_num
    · apply multipleFibers_not_graph
      convert exercise21_fibers_swap exercise21_fold_y_other using 1 <;> norm_num

/-- The only singular zeros are the two transverse intersections. -/
theorem exercise21_singular (x y : ℝ) :
    (exercise21Function (x, y) = 0 ∧
      deriv (fun t => exercise21Function (t, y)) x = 0 ∧
      deriv (fun t => exercise21Function (x, t)) y = 0) ↔
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) := by
  rw [exercise21_stationary]
  constructor
  · rintro ⟨hz, (rfl | rfl), (rfl | rfl)⟩ <;> norm_num [exercise21Function] at *
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [exercise21Function]

/-- The graph predicate gives actual existence and uniqueness on a rectangle. -/
theorem ZeroGraphX.rectangle {f : ℝ × ℝ → ℝ} {a b : ℝ} (h : ZeroGraphX f a b) :
    ∃ A ∈ 𝓝 a, ∃ B ∈ 𝓝 b, ∃ g : ℝ → ℝ,
      ContinuousAt g b ∧ g b = a ∧
      (∀ y ∈ B, g y ∈ A) ∧
      ∀ x ∈ A, ∀ y ∈ B, f (x, y) = 0 ↔ x = g y := by
  obtain ⟨U, hU, g, hc, hg, he⟩ := h
  obtain ⟨A, hA, B, hB, hsub⟩ := mem_nhds_prod_iff.mp hU
  have hAg : ∀ᶠ y in 𝓝 b, g y ∈ A := hc.eventually (by rwa [hg])
  exact ⟨A, hA, B ∩ g ⁻¹' A, inter_mem hB hAg, g, hc, hg,
    fun y hy => hy.2, fun x hx y hy => he (x, y) (hsub ⟨hx, hy.1⟩)⟩

theorem scalarDifferential_coordinates (L : ℝ × ℝ →L[ℝ] ℝ) (u v : ℝ) :
    L (u, v) = L (1, 0) * u + L (0, 1) * v := by
  rw [scalarDifferential_split]
  have he : ((0, v) : ℝ × ℝ) = v • (0, 1) := by simp
  rw [he, map_smul]
  simp [mul_comm]

/-- The Fréchet derivative, evaluated on an arbitrary increment. -/
theorem exercise21_differential (x y u v : ℝ) :
    HasFDerivAt exercise21Function (fderiv ℝ exercise21Function (x, y)) (x, y) ∧
    fderiv ℝ exercise21Function (x, y) (u, v) =
      6 * x * (x - 1) * u + 6 * y * (y + 1) * v := by
  have hc : ContDiffAt ℝ 1 exercise21Function (x, y) :=
    exercise21_smooth.contDiffAt.of_le (by norm_num)
  refine ⟨(hc.differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
  rw [scalarDifferential_coordinates,
    (exercise20_partials hc).1.unique (exercise21_partials x y).1,
    (exercise20_partials hc).2.unique (exercise21_partials x y).2]

/-- Explicit branches of the ellipse, with its exact horizontal extent. -/
theorem exercise21_ellipse_branches (x y : ℝ) :
    (x + y) ^ 2 + 3 * (x - y - 1) ^ 2 = 3 ↔
      -1 / 2 ≤ x ∧ x ≤ 3 / 2 ∧
      (y = (2 * x - 3 + Real.sqrt (9 + 12 * x - 12 * x ^ 2)) / 4 ∨
       y = (2 * x - 3 - Real.sqrt (9 + 12 * x - 12 * x ^ 2)) / 4) := by
  constructor
  · intro he
    have hD : 0 ≤ 9 + 12 * x - 12 * x ^ 2 := by
      nlinarith [sq_nonneg (4 * y - 2 * x + 3)]
    have hx : -1 / 2 ≤ x := by nlinarith [sq_nonneg (x + 1 / 2)]
    have hx' : x ≤ 3 / 2 := by nlinarith [sq_nonneg (x - 3 / 2)]
    refine ⟨hx, hx', ?_⟩
    have hs := Real.sq_sqrt hD
    have hh : (4 * y - 2 * x + 3) ^ 2 = (Real.sqrt (9 + 12 * x - 12 * x ^ 2)) ^ 2 := by
      nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with hh | hh
    · left; linarith
    · right; linarith
  · rintro ⟨hx, hx', hy⟩
    have hD : 0 ≤ 9 + 12 * x - 12 * x ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ x + 1 / 2 by linarith) (show 0 ≤ 3 / 2 - x by linarith)]
    have hs := Real.sq_sqrt hD
    rcases hy with hy | hy <;> rw [hy] <;> nlinarith

theorem exercise21_all_branches (x y : ℝ) :
    exercise21Function (x, y) = 0 ↔ y = -x ∨
      (-1 / 2 ≤ x ∧ x ≤ 3 / 2 ∧
      (y = (2 * x - 3 + Real.sqrt (9 + 12 * x - 12 * x ^ 2)) / 4 ∨
       y = (2 * x - 3 - Real.sqrt (9 + 12 * x - 12 * x ^ 2)) / 4)) := by
  rw [exercise21_zero_set, exercise21_ellipse_branches]

/-- At each intersection the leading quadratic has the two different tangent lines. -/
theorem exercise21_node_expansions (x y t : ℝ) :
    exercise21Function (t * x, t * y) =
      3 * t ^ 2 * (y ^ 2 - x ^ 2) + 2 * t ^ 3 * (x ^ 3 + y ^ 3) ∧
    exercise21Function (1 + t * x, -1 + t * y) =
      3 * t ^ 2 * (x ^ 2 - y ^ 2) + 2 * t ^ 3 * (x ^ 3 + y ^ 3) := by
  constructor <;> unfold exercise21Function <;> ring

theorem exercise21_frechet_stationary (x y : ℝ) :
    fderiv ℝ exercise21Function (x, y) = 0 ↔
      (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = -1) := by
  constructor
  · intro h
    apply (exercise21_stationary x y).mp
    rw [(exercise21_partials x y).1.deriv, (exercise21_partials x y).2.deriv]
    have hx := (exercise21_differential x y 1 0).2
    have hy := (exercise21_differential x y 0 1).2
    rw [h] at hx hy
    simpa using And.intro hx.symm hy.symm
  · intro h
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    rw [(exercise21_differential x y u v).2]
    rcases h with ⟨hx | hx, hy | hy⟩ <;> simp [hx, hy]

/-- The saddle classification includes stationarity as well as both signs. -/
theorem exercise21_stationary_saddles (x y : ℝ) :
    (fderiv ℝ exercise21Function (x, y) = 0 ∧ Saddle exercise21Function (x, y)) ↔
      (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = -1) := by
  rw [exercise21_frechet_stationary]
  constructor
  · rintro ⟨⟨hx | hx, hy | hy⟩, hs⟩ <;> subst x <;> subst y
    · exact Or.inl ⟨rfl, rfl⟩
    · exact False.elim ((saddle_not_extremum hs).2 exercise21_maximum.1)
    · exact False.elim ((saddle_not_extremum hs).1 exercise21_minimum.1)
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨⟨Or.inl rfl, Or.inl rfl⟩, exercise21_saddle_origin⟩
    · exact ⟨⟨Or.inr rfl, Or.inr rfl⟩, exercise21_saddle_intersection⟩

end Rudin.Chapter09
