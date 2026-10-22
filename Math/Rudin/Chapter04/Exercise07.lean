module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter04

/-- The formula is total at the origin and has value zero there. -/
noncomputable def exercise07_f (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 * (p 1)^2 / ((p 0)^2 + (p 1)^4)

noncomputable def exercise07_g (p : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  p 0 * (p 1)^2 / ((p 0)^2 + (p 1)^6)

@[simp] theorem exercise07_f_zero : exercise07_f 0 = 0 := by simp [exercise07_f]
@[simp] theorem exercise07_g_zero : exercise07_g 0 = 0 := by simp [exercise07_g]

lemma exercise07_den_f {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    0 < (p 0)^2 + (p 1)^4 := by
  have hn : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext i
    fin_cases i <;> simp_all
  rcases hn with h | h
  · positivity
  · positivity

lemma exercise07_den_g {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    0 < (p 0)^2 + (p 1)^6 := by
  have hn : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    ext i
    fin_cases i <;> simp_all
  rcases hn with h | h <;> positivity

/-- In fact the global bound is one half. -/
theorem exercise07_f_bounded (p : EuclideanSpace ℝ (Fin 2)) :
    |exercise07_f p| ≤ 1 / 2 := by
  by_cases hp : p = 0
  · simp [hp]
  rw [exercise07_f, abs_div, abs_of_pos (exercise07_den_f hp), div_le_iff₀ (exercise07_den_f hp)]
  rw [abs_mul, abs_pow, sq_abs]
  nlinarith [sq_nonneg (|p 0| - (p 1)^2), sq_abs (p 0)]

/-- The image is a bounded subset of the real line. -/
theorem exercise07_f_range_bounded : Bornology.IsBounded (Set.range exercise07_f) := by
  apply Metric.isBounded_iff.mpr
  refine ⟨1, ?_⟩
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  rw [Real.dist_eq]
  calc |exercise07_f p - exercise07_f q| ≤ |exercise07_f p| + |exercise07_f q| := abs_sub _ _
    _ ≤ 1 := by linarith [exercise07_f_bounded p, exercise07_f_bounded q]

lemma exercise07_f_continuousAt {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    ContinuousAt exercise07_f p := by
  unfold exercise07_f
  exact ((PiLp.continuous_apply 2 _ 0).continuousAt.mul
    ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 2)).div
    (((PiLp.continuous_apply 2 _ 0).continuousAt.pow 2).add
      ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 4))
    (ne_of_gt (exercise07_den_f hp))

lemma exercise07_g_continuousAt {p : EuclideanSpace ℝ (Fin 2)} (hp : p ≠ 0) :
    ContinuousAt exercise07_g p := by
  unfold exercise07_g
  exact ((PiLp.continuous_apply 2 _ 0).continuousAt.mul
    ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 2)).div
    (((PiLp.continuous_apply 2 _ 0).continuousAt.pow 2).add
      ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 6))
    (ne_of_gt (exercise07_den_g hp))

lemma exercise07_f_radial (v : EuclideanSpace ℝ (Fin 2)) :
    ContinuousAt (fun t : ℝ => exercise07_f (t • v)) 0 := by
  by_cases hv : v 0 = 0
  · have heq : (fun t : ℝ => exercise07_f (t • v)) = fun _ => 0 := by
      funext t
      simp [exercise07_f, hv]
    rw [heq]
    exact continuousAt_const
  have heq : (fun t : ℝ => exercise07_f (t • v)) =
      fun t => (v 0 * (v 1)^2 * t) / ((v 0)^2 + t^2 * (v 1)^4) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · have hd : (v 0)^2 + t^2 * (v 1)^4 ≠ 0 := by positivity
      have hD : (t * v 0)^2 + (t * v 1)^4 ≠ 0 := by positivity
      simp only [exercise07_f, PiLp.smul_apply, smul_eq_mul]
      field_simp
  rw [heq]
  fun_prop (disch := simp [hv])

lemma exercise07_g_radial (v : EuclideanSpace ℝ (Fin 2)) :
    ContinuousAt (fun t : ℝ => exercise07_g (t • v)) 0 := by
  by_cases hv : v 0 = 0
  · have heq : (fun t : ℝ => exercise07_g (t • v)) = fun _ => 0 := by
      funext t
      simp [exercise07_g, hv]
    rw [heq]
    exact continuousAt_const
  have heq : (fun t : ℝ => exercise07_g (t • v)) =
      fun t => (v 0 * (v 1)^2 * t) / ((v 0)^2 + t^4 * (v 1)^6) := by
    funext t
    by_cases ht : t = 0
    · simp [ht]
    · have hd : (v 0)^2 + t^4 * (v 1)^6 ≠ 0 := by positivity
      have hD : (t * v 0)^2 + (t * v 1)^6 ≠ 0 := by positivity
      simp only [exercise07_g, PiLp.smul_apply, smul_eq_mul]
      field_simp
  rw [heq]
  fun_prop (disch := simp [hv])

/-- Translate a line meeting the origin to the radial parameterization. -/
lemma exercise07_affine_continuity (F : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hoff : ∀ p ≠ 0, ContinuousAt F p)
    (hon : ∀ v, ContinuousAt (fun t : ℝ => F (t • v)) 0)
    (a v : EuclideanSpace ℝ (Fin 2)) : Continuous (fun t : ℝ => F (a + t • v)) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  by_cases hc : a + c • v = 0
  · have ha : a = -(c • v) := eq_neg_of_add_eq_zero_left hc
    have heq : (fun t : ℝ => F (a + t • v)) = fun t => F ((t - c) • v) := by
      funext t
      congr 1
      rw [ha, sub_smul]
      abel
    rw [heq]
    have hsub : ContinuousAt (fun t : ℝ => t - c) c := continuousAt_id.sub continuousAt_const
    exact (hon v).comp_of_eq hsub (by simp)
  · exact ContinuousAt.comp (f := fun t : ℝ => a + t • v) (x := c)
      (hoff _ hc) (by fun_prop)

/-- Every affine line, not only those through zero, has a continuous restriction. -/
theorem exercise07_f_line_continuity (a v : EuclideanSpace ℝ (Fin 2)) :
    Continuous (fun t : ℝ => exercise07_f (a + t • v)) :=
  exercise07_affine_continuity exercise07_f (fun _ => exercise07_f_continuousAt)
    exercise07_f_radial a v

theorem exercise07_g_line_continuity (a v : EuclideanSpace ℝ (Fin 2)) :
    Continuous (fun t : ℝ => exercise07_g (a + t • v)) :=
  exercise07_affine_continuity exercise07_g (fun _ => exercise07_g_continuousAt)
    exercise07_g_radial a v

/-- A continuous parameterization of each affine line gives continuity on that line. -/
lemma exercise07_affine_restriction (F : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a v : EuclideanSpace ℝ (Fin 2))
    (h : Continuous (fun t : ℝ => F (a + t • v))) :
    ContinuousOn F (Set.range (fun t : ℝ => a + t • v)) := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, v i ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hv
    ext i
    exact hn i
  let r : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => (p i - a i) / v i
  have hr : Continuous r := ((PiLp.continuous_apply 2 _ i).sub continuous_const).div_const _
  apply (h.comp hr).continuousOn.congr
  rintro p ⟨t, rfl⟩
  have ht : r (a + t • v) = t := by simp [r, hi]
  simp [ht]

/-- The restriction of f to each affine line, with its subspace topology, is continuous. -/
theorem exercise07_f_line_restriction (a v : EuclideanSpace ℝ (Fin 2)) :
    ContinuousOn exercise07_f (Set.range (fun t : ℝ => a + t • v)) :=
  exercise07_affine_restriction exercise07_f a v (exercise07_f_line_continuity a v)

theorem exercise07_g_line_restriction (a v : EuclideanSpace ℝ (Fin 2)) :
    ContinuousOn exercise07_g (Set.range (fun t : ℝ => a + t • v)) :=
  exercise07_affine_restriction exercise07_g a v (exercise07_g_line_continuity a v)

/-- Polynomial curves used to test continuity and local boundedness. -/
noncomputable def exercise07_curve (k : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![t^k, t]

lemma exercise07_curve_continuous (k : ℕ) : Continuous (exercise07_curve k) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

@[simp] lemma exercise07_curve_zero {k : ℕ} (hk : k ≠ 0) :
    exercise07_curve k 0 = 0 := by
  ext i
  fin_cases i <;> simp [exercise07_curve, hk]

lemma exercise07_f_curve {t : ℝ} (ht : t ≠ 0) :
    exercise07_f (exercise07_curve 2 t) = 1 / 2 := by
  simp only [exercise07_f, exercise07_curve, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

lemma exercise07_g_curve {t : ℝ} (ht : t ≠ 0) :
    exercise07_g (exercise07_curve 3 t) = 1 / (2 * t) := by
  simp only [exercise07_g, exercise07_curve, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- The parabolic approach has constant nonzero value, so f is discontinuous at zero. -/
theorem exercise07_f_discontinuous : ¬ ContinuousAt exercise07_f 0 := by
  intro h
  have hc : ContinuousAt (fun t : ℝ => exercise07_f (exercise07_curve 2 t)) 0 :=
    h.comp_of_eq (exercise07_curve_continuous 2).continuousAt (by simp)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (1 / 4) (by norm_num)
  have ht : δ / 2 ≠ 0 := by positivity
  have hsmall : dist (δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have hbad := hd hsmall
  rw [exercise07_f_curve ht] at hbad
  norm_num at hbad

/-- Every neighborhood contains values of g larger in absolute value than any given bound. -/
theorem exercise07_g_locally_unbounded
    (U : Set (EuclideanSpace ℝ (Fin 2))) (hU : U ∈ 𝓝 0) (M : ℝ) :
    ∃ p ∈ U, M < |exercise07_g p| := by
  have hpre : ∀ᶠ t : ℝ in 𝓝 0, exercise07_curve 3 t ∈ U :=
    (exercise07_curve_continuous 3).continuousAt.tendsto.eventually
      (by simpa using hU)
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hpre
  let t : ℝ := min δ (1 / (2 * (|M| + 1))) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by
    have := min_le_left δ (1 / (2 * (|M| + 1)))
    dsimp [t]
    linarith
  have htb : t < 1 / (2 * (|M| + 1)) := by
    have := min_le_right δ (1 / (2 * (|M| + 1)))
    dsimp [t] at *
    linarith
  refine ⟨exercise07_curve 3 t, hd (by simpa [Real.dist_eq, abs_of_pos ht] using htδ), ?_⟩
  rw [exercise07_g_curve (ne_of_gt ht), abs_of_pos (by positivity)]
  have hmul : t * (2 * (|M| + 1)) < 1 := (lt_div_iff₀ (by positivity)).mp htb
  apply (lt_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  nlinarith [le_abs_self M]

end Rudin.Chapter04
