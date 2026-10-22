module

public import Mathlib

@[expose] public section
noncomputable section
namespace Rudin.Chapter05
open Set Filter
open scoped Topology

/-- The two derivatives are specified on the closed interval. At its endpoints
these are derivatives within the interval, not ambient derivatives. -/
structure Exercise25Data (f p q : ℝ → ℝ) (a b δ M : ℝ) : Prop where
  left_lt_right : a < b
  first : ∀ x ∈ Icc a b, HasDerivWithinAt f (p x) (Icc a b) x
  second : ∀ x ∈ Icc a b, HasDerivWithinAt p (q x) (Icc a b) x
  left_neg : f a < 0
  right_pos : 0 < f b
  delta_pos : 0 < δ
  first_lower : ∀ x ∈ Icc a b, δ ≤ p x
  second_lower : ∀ x ∈ Icc a b, 0 ≤ q x
  second_upper : ∀ x ∈ Icc a b, q x ≤ M

variable {f p q : ℝ → ℝ} {a b δ M ξ x : ℝ}

namespace Exercise25Data
variable (h : Exercise25Data f p q a b δ M)
include h

theorem continuous : ContinuousOn f (Icc a b) :=
  fun x hx => (h.first x hx).continuousWithinAt

theorem continuous_first : ContinuousOn p (Icc a b) :=
  fun x hx => (h.second x hx).continuousWithinAt

theorem first_at {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt f (p x) x :=
  (h.first x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

theorem second_at {x : ℝ} (hx : x ∈ Ioo a b) : HasDerivAt p (q x) x :=
  (h.second x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)

theorem first_pos {x : ℝ} (hx : x ∈ Icc a b) : 0 < p x :=
  h.delta_pos.trans_le (h.first_lower x hx)

theorem curvature_nonneg : 0 ≤ M :=
  (h.second_lower a ⟨le_rfl, h.left_lt_right.le⟩).trans
    (h.second_upper a ⟨le_rfl, h.left_lt_right.le⟩)

theorem strictMono : StrictMonoOn f (Icc a b) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a b) h.continuous
  · intro x hx
    exact (h.first x (interior_subset hx)).mono interior_subset
  · intro x hx
    exact h.first_pos (interior_subset hx)

theorem monotone_first : MonotoneOn p (Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) h.continuous_first
  · intro x hx
    exact (h.second x (interior_subset hx)).mono interior_subset
  · intro x hx
    exact h.second_lower x (interior_subset hx)

end Exercise25Data

/-- R05E25.root. -/
theorem exercise25_root (h : Exercise25Data f p q a b δ M) :
    ∃! ξ, ξ ∈ Ioo a b ∧ f ξ = 0 := by
  obtain ⟨ξ, hξ, hz⟩ := intermediate_value_Icc h.left_lt_right.le h.continuous
    (show (0 : ℝ) ∈ Icc (f a) (f b) from ⟨h.left_neg.le, h.right_pos.le⟩)
  have ha : a < ξ := lt_of_le_of_ne hξ.1 (by intro he; subst ξ; linarith [h.left_neg])
  have hb : ξ < b := lt_of_le_of_ne hξ.2 (by intro he; subst ξ; linarith [h.right_pos])
  refine ⟨ξ, ⟨⟨ha, hb⟩, hz⟩, ?_⟩
  intro y hy
  exact h.strictMono.injOn (Ioo_subset_Icc_self hy.1) hξ (hy.2.trans hz.symm)

/-- The Newton map, used only where its denominator is proved positive. -/
def exercise25Newton (f p : ℝ → ℝ) (x : ℝ) : ℝ := x - f x / p x

/-- Index zero denotes the source's x₁. Explicit `Nat.rec` defines the infinite
sequence, including all terms after a root has been reached. -/
def exercise25Iter (f p : ℝ → ℝ) (x₁ : ℝ) : ℕ → ℝ :=
  Nat.rec x₁ (fun _ x => exercise25Newton f p x)

@[simp] theorem exercise25Iter_zero (x₁ : ℝ) : exercise25Iter f p x₁ 0 = x₁ := rfl
@[simp] theorem exercise25Iter_succ (x₁ : ℝ) (n : ℕ) :
    exercise25Iter f p x₁ (n + 1) = exercise25Newton f p (exercise25Iter f p x₁ n) := rfl

/-- Reaching the root is absorbing. -/
theorem exercise25_absorbing (hz : f ξ = 0) : exercise25Newton f p ξ = ξ := by
  simp [exercise25Newton, hz]

/-- Every term after a reached root equals the root. -/
theorem exercise25_iteration_absorbing (hz : f ξ = 0) {x₁ : ℝ} {n : ℕ}
    (hn : exercise25Iter f p x₁ n = ξ) (k : ℕ) :
    exercise25Iter f p x₁ (n+k) = ξ := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
    rw [← Nat.add_assoc, exercise25Iter_succ, ih, exercise25_absorbing hz]

/-- R05E25.c, off the root. Two applications of Rolle prove Taylor's
formula without any continuity assumption on the second derivative. -/
theorem exercise25_taylor (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hx : x ∈ Ioc ξ b) :
    ∃ t ∈ Ioo ξ x,
      exercise25Newton f p x - ξ = q t * (x - ξ)^2 / (2 * p x) := by
  have hsub : Icc ξ x ⊆ Icc a b := Icc_subset_Icc hξ.1.le hx.2
  have hxmem : x ∈ Icc a b := hsub ⟨hx.1.le, le_rfl⟩
  have hne : ξ - x ≠ 0 := sub_ne_zero.mpr hx.1.ne
  let C := (f ξ - f x - p x * (ξ - x)) / (ξ - x)^2
  let F := fun y => f y - f x - p x * (y - x) - C * (y - x)^2
  let D := fun y => p y - p x - 2 * C * (y - x)
  have hF : ContinuousOn F (Icc ξ x) := by
    dsimp [F]
    exact (((h.continuous.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2))
  have hFd : ∀ y ∈ Ioo ξ x, HasDerivAt F (D y) y := by
    intro y hy
    have hyab : y ∈ Ioo a b := ⟨hξ.1.trans hy.1, hy.2.trans_le hx.2⟩
    convert (((h.first_at hyab).sub_const (f x)).sub
      (((hasDerivAt_id y).sub_const x).const_mul (p x))).sub
      ((((hasDerivAt_id y).sub_const x).pow 2).const_mul C) using 1 <;>
      (try funext z) <;> (try dsimp [F, D]); ring
  have hFeq : F ξ = F x := by
    dsimp [F, C]
    field_simp
    ring
  obtain ⟨c, hc, hcD⟩ := exists_hasDerivAt_eq_zero hx.1 hF hFeq hFd
  have hD : ContinuousOn D (Icc c x) := by
    dsimp [D]
    exact ((h.continuous_first.mono (Icc_subset_Icc (hξ.1.trans hc.1).le hx.2)).sub
      continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hDd : ∀ y ∈ Ioo c x, HasDerivAt D (q y - 2 * C) y := by
    intro y hy
    have hyab : y ∈ Ioo a b := ⟨(hξ.1.trans hc.1).trans hy.1, hy.2.trans_le hx.2⟩
    convert ((h.second_at hyab).sub_const (p x)).sub
      (((hasDerivAt_id y).sub_const x).const_mul (2 * C)) using 1 <;>
      (try funext z) <;> (try dsimp [D]); ring
  have hDeq : D c = D x := by simpa [D] using hcD
  obtain ⟨t, ht, htq⟩ := exists_hasDerivAt_eq_zero hc.2 hD hDeq hDd
  refine ⟨t, ⟨hc.1.trans ht.1, ht.2⟩, ?_⟩
  have hq : q t = 2 * C := sub_eq_zero.mp htq
  have hp : p x ≠ 0 := (h.first_pos hxmem).ne'
  rw [hq]
  dsimp [exercise25Newton, C]
  rw [hz]
  field_simp
  nlinarith [sq_pos_of_ne_zero hne]

/-- The reached-root case has zero error and needs no interior Taylor point. -/
theorem exercise25_taylor_terminated (hz : f ξ = 0) :
    exercise25Newton f p ξ - ξ = 0 ∧ ¬ ∃ t, t ∈ Ioo ξ ξ := by
  simp [exercise25_absorbing hz]

/-- A Newton step stays above the root and never increases. -/
theorem exercise25_step (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hx : x ∈ Icc ξ b) :
    ξ ≤ exercise25Newton f p x ∧ exercise25Newton f p x ≤ x := by
  have hxmem : x ∈ Icc a b := ⟨hξ.1.le.trans hx.1, hx.2⟩
  have hf : 0 ≤ f x := by
    rw [← hz]
    exact h.strictMono.monotoneOn (Ioo_subset_Icc_self hξ) hxmem hx.1
  have hupper : exercise25Newton f p x ≤ x := by
    dsimp [exercise25Newton]
    exact sub_le_self _ (div_nonneg hf (h.first_pos hxmem).le)
  refine ⟨?_, hupper⟩
  rcases hx.1.eq_or_lt with he | hlt
  · subst x
    exact (exercise25_absorbing hz).ge
  · obtain ⟨t, ht, he⟩ := exercise25_taylor h hξ hz ⟨hlt, hx.2⟩
    have hqt := h.second_lower t ⟨hξ.1.le.trans ht.1.le, ht.2.le.trans hx.2⟩
    have hp := h.first_pos hxmem
    have : 0 ≤ exercise25Newton f p x - ξ := by
      rw [he]
      positivity
    linarith

/-- Strict descent holds exactly off the root. -/
theorem exercise25_strict_step (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hx : x ∈ Icc ξ b) :
    exercise25Newton f p x < x ↔ ξ < x := by
  have hxmem : x ∈ Icc a b := ⟨hξ.1.le.trans hx.1, hx.2⟩
  constructor
  · intro he
    exact lt_of_le_of_ne hx.1 (by intro heq; subst x; simp [exercise25_absorbing hz] at he)
  · intro he
    have hf : 0 < f x := by
      rw [← hz]
      exact h.strictMono (Ioo_subset_Icc_self hξ) hxmem he
    exact sub_lt_self _ (div_pos hf (h.first_pos hxmem))

/-- R05E25.a.iteration and R05E25.b.descent. The first source term has
index zero here; its stated strict starting condition is retained. -/
theorem exercise25_iteration (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioc ξ b) :
    ∀ n, exercise25Iter f p x₁ n ∈ Icc ξ b ∧
      0 < p (exercise25Iter f p x₁ n) ∧
      ξ ≤ exercise25Iter f p x₁ (n+1) ∧
      exercise25Iter f p x₁ (n+1) ≤ exercise25Iter f p x₁ n ∧
      (exercise25Iter f p x₁ (n+1) < exercise25Iter f p x₁ n ↔
        ξ < exercise25Iter f p x₁ n) := by
  have hm : ∀ n, exercise25Iter f p x₁ n ∈ Icc ξ b := by
    intro n
    induction n with
    | zero => exact ⟨hx₁.1.le, hx₁.2⟩
    | succ n ih =>
      have hs := exercise25_step h hξ hz ih
      exact ⟨hs.1, hs.2.trans ih.2⟩
  intro n
  have hn := hm n
  have hs := exercise25_step h hξ hz hn
  exact ⟨hn, h.first_pos ⟨hξ.1.le.trans hn.1, hn.2⟩, hs.1, hs.2,
    exercise25_strict_step h hξ hz hn⟩

/-- R05E25.a.tangent. This equation is the tangent line at `(x,f x)`.
Its unique horizontal intercept is the next Newton term. -/
theorem exercise25_tangent (h : Exercise25Data f p q a b δ M)
    (hx : x ∈ Icc a b) (y : ℝ) :
    f x + p x * (y - x) = 0 ↔ y = exercise25Newton f p x := by
  have hp := (h.first_pos hx).ne'
  dsimp [exercise25Newton]
  constructor <;> intro he
  · apply (eq_sub_iff_add_eq).mpr
    apply (mul_right_cancel₀ hp)
    field_simp
    nlinarith
  · rw [he]
    field_simp
    ring

/-- R05E25.b.convergence. Monotone convergence and continuity of `f'`
(which follows from existence of `f''`) identify the limit. -/
theorem exercise25_convergence (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioc ξ b) :
    Tendsto (exercise25Iter f p x₁) atTop (𝓝 ξ) := by
  let u := exercise25Iter f p x₁
  have hi := exercise25_iteration h hξ hz hx₁
  have hm : Antitone u := antitone_nat_of_succ_le (fun n => (hi n).2.2.2.1)
  have hb : BddBelow (range u) := ⟨ξ, by rintro _ ⟨n, rfl⟩; exact (hi n).1.1⟩
  let l := ⨅ n, u n
  have hl : Tendsto u atTop (𝓝 l) := tendsto_atTop_ciInf hm hb
  have hlmem : l ∈ Icc ξ b := isClosed_Icc.mem_of_tendsto hl
    (Eventually.of_forall (fun n => (hi n).1))
  have hlab : l ∈ Icc a b := ⟨hξ.1.le.trans hlmem.1, hlmem.2⟩
  have huab : ∀ n, u n ∈ Icc a b :=
    fun n => ⟨hξ.1.le.trans (hi n).1.1, (hi n).1.2⟩
  have hlf := (h.continuous l hlab).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall huab⟩)
  have hlp := (h.continuous_first l hlab).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall huab⟩)
  have hn : Tendsto (fun n => exercise25Newton f p (u n)) atTop
      (𝓝 (exercise25Newton f p l)) := hl.sub (hlf.div hlp (h.first_pos hlab).ne')
  have hs : Tendsto (fun n => u (n+1)) atTop (𝓝 l) :=
    hl.comp (tendsto_add_atTop_nat 1)
  have he : exercise25Newton f p l = l := tendsto_nhds_unique hn hs
  have hfl : f l = 0 := by
    have hd : f l / p l = 0 := by dsimp [exercise25Newton] at he; linarith
    exact (div_eq_zero_iff).mp hd |>.resolve_right (h.first_pos hlab).ne'
  have heq : l = ξ := h.strictMono.injOn hlab (Ioo_subset_Icc_self hξ) (hfl.trans hz.symm)
  simpa [heq] using hl

/-- The one-step quadratic estimate, including the zero-curvature case. -/
theorem exercise25_quadratic (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hx : x ∈ Icc ξ b) :
    0 ≤ exercise25Newton f p x - ξ ∧
      exercise25Newton f p x - ξ ≤ (M / (2 * δ)) * (x - ξ)^2 := by
  refine ⟨sub_nonneg.mpr (exercise25_step h hξ hz hx).1, ?_⟩
  rcases hx.1.eq_or_lt with he | he
  · subst x
    simp [exercise25_absorbing hz]
  · obtain ⟨t, ht, htay⟩ := exercise25_taylor h hξ hz ⟨he, hx.2⟩
    have hxmem : x ∈ Icc a b := ⟨hξ.1.le.trans hx.1, hx.2⟩
    have htmem : t ∈ Icc a b := ⟨hξ.1.le.trans ht.1.le, ht.2.le.trans hx.2⟩
    rw [htay]
    calc
      q t * (x - ξ)^2 / (2 * p x) = (x - ξ)^2 * (q t / (2 * p x)) := by ring
      _ ≤ (x - ξ)^2 * (M / (2 * δ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg (x - ξ))
        apply div_le_div₀ h.curvature_nonneg (h.second_upper t htmem)
          (by linarith [h.delta_pos])
        linarith [h.first_lower x hxmem]
      _ = _ := by ring

/-- A division-free induction for a nonnegative quadratic error recurrence.
It is valid at `A=0`, including at index zero. -/
theorem exercise25_recurrence_bound {e : ℕ → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (he : ∀ n, 0 ≤ e n) (hs : ∀ n, e (n+1) ≤ A * (e n)^2) :
    ∀ n, e n ≤ A^(2^n-1) * (e 0)^(2^n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 < 2^n := pow_pos (by decide) n
    have hp : 2^(n+1) = 2 * 2^n := by rw [pow_succ]; omega
    calc
      e (n+1) ≤ A * (e n)^2 := hs n
      _ ≤ A * (A^(2^n-1) * (e 0)^(2^n))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (he n) ih 2) hA
      _ = A^(2^(n+1)-1) * (e 0)^(2^(n+1)) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_succ']
        congr 2
        omega

/-- R05E25.d in a form defined for every allowed `M`, including zero.
Index `n` here is the source's `(n+1)`st term. -/
theorem exercise25_denominator_free (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioc ξ b) (n : ℕ) :
    0 ≤ exercise25Iter f p x₁ n - ξ ∧
      exercise25Iter f p x₁ n - ξ ≤
        (M / (2 * δ))^(2^n-1) * (x₁ - ξ)^(2^n) := by
  have hi := exercise25_iteration h hξ hz hx₁
  have hs := fun n => exercise25_quadratic h hξ hz (hi n).1
  refine ⟨sub_nonneg.mpr (hi n).1.1, ?_⟩
  exact exercise25_recurrence_bound (div_nonneg h.curvature_nonneg (by linarith [h.delta_pos]))
    (fun n => sub_nonneg.mpr (hi n).1.1) (fun n => (hs n).2) n

/-- The printed reciprocal estimate is recovered only with a positive `A`.
Here index `n` corresponds to the source's x_(n+1). -/
theorem exercise25_printed_bound (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) {x₁ : ℝ} (hx₁ : x₁ ∈ Ioc ξ b)
    (hA : 0 < M / (2 * δ)) (n : ℕ) :
    0 ≤ exercise25Iter f p x₁ n - ξ ∧
      exercise25Iter f p x₁ n - ξ ≤
        ((M / (2 * δ)) * (x₁ - ξ))^(2^n) / (M / (2 * δ)) := by
  have hb := exercise25_denominator_free h hξ hz hx₁ n
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  have hn : 0 < 2^n := pow_pos (by decide) n
  apply (eq_div_iff hA.ne').mpr
  rw [mul_pow]
  calc
    _ = ((M / (2 * δ))^(2^n-1) * (M / (2 * δ))) * (x₁ - ξ)^(2^n) := by ring
    _ = _ := by rw [← pow_succ]; congr 2; omega

/-- R05E25.zero_bound_domain_obstruction: zero curvature gives a root in
one step; no reciprocal of the zero constant is used. -/
theorem exercise25_zero_curvature (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hM : M = 0) (hx : x ∈ Icc ξ b) :
    M / (2 * δ) = 0 ∧ exercise25Newton f p x = ξ := by
  have hb := exercise25_quadratic h hξ hz hx
  rw [hM, zero_div, zero_mul] at hb
  exact ⟨by simp [hM], by linarith [hb.1, hb.2]⟩

/-- `A=0` is equivalent to `M=0`, since `δ` is positive. -/
theorem exercise25_A_zero_iff (h : Exercise25Data f p q a b δ M) :
    M / (2 * δ) = 0 ↔ M = 0 := by
  have hd : 2 * δ ≠ 0 := mul_ne_zero (by norm_num) h.delta_pos.ne'
  simp [div_eq_zero_iff, hd]

/-- The zero-`A` iteration terminates immediately and stays at the root. -/
theorem exercise25_zero_A_termination (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) (hA : M / (2 * δ) = 0)
    {x₁ : ℝ} (hx₁ : x₁ ∈ Ioc ξ b) (n : ℕ) :
    exercise25Iter f p x₁ (n+1) = ξ := by
  have hM := (exercise25_A_zero_iff h).mp hA
  have hs : exercise25Iter f p x₁ 1 = ξ :=
    (exercise25_zero_curvature h hξ hz hM ⟨hx₁.1.le, hx₁.2⟩).2
  simpa [Nat.add_comm] using exercise25_iteration_absorbing hz hs n

/-- R05E25.e.fixed_point. -/
theorem exercise25_fixed_point (h : Exercise25Data f p q a b δ M)
    (hx : x ∈ Icc a b) : exercise25Newton f p x = x ↔ f x = 0 := by
  have hp := (h.first_pos hx).ne'
  simp [exercise25Newton, sub_eq_self, div_eq_zero_iff, hp]

/-- R05E25.e.derivative, including the source's one-sided endpoints. -/
theorem exercise25_g_derivative (h : Exercise25Data f p q a b δ M)
    (hx : x ∈ Icc a b) :
    HasDerivWithinAt (exercise25Newton f p) (f x * q x / (p x)^2) (Icc a b) x := by
  have hp := (h.first_pos hx).ne'
  convert (hasDerivWithinAt_id x (Icc a b)).sub
    ((h.first x hx).div (h.second x hx) hp) using 1 <;>
    (try funext z) <;> (try dsimp [exercise25Newton]); field_simp; ring

/-- The derivative tends to zero at the root. The second derivative need
only be bounded, not continuous. -/
theorem exercise25_g_derivative_limit (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) :
    Tendsto (fun x => f x * q x / (p x)^2) (𝓝[Icc a b] ξ) (𝓝 0) := by
  have hf : Tendsto f (𝓝[Icc a b] ξ) (𝓝 0) := by
    simpa [hz] using (h.continuous ξ (Ioo_subset_Icc_self hξ)).tendsto
  refine squeeze_zero_norm' ?_ (by simpa using hf.norm.mul_const (M / δ^2))
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_sq,
    abs_of_nonneg (h.second_lower x hx)]
  calc
    |f x| * q x / (p x)^2 ≤ |f x| * M / δ^2 := by
      apply div_le_div₀ (mul_nonneg (abs_nonneg _) h.curvature_nonneg)
        (mul_le_mul_of_nonneg_left (h.second_upper x hx) (abs_nonneg _))
        (sq_pos_of_pos h.delta_pos)
      exact pow_le_pow_left₀ h.delta_pos.le (h.first_lower x hx) 2
    _ = ‖f x‖ * (M / δ^2) := by rw [Real.norm_eq_abs]; ring

/-- The same limit for the actual derivative within the closed interval. -/
theorem exercise25_derivWithin_limit (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) :
    Tendsto (derivWithin (exercise25Newton f p) (Icc a b))
      (𝓝[Icc a b] ξ) (𝓝 0) := by
  apply (exercise25_g_derivative_limit h hξ hz).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ((exercise25_g_derivative h hx).derivWithin
    (uniqueDiffOn_Icc h.left_lt_right x hx)).symm

/-- At the interior root the ordinary derivative of the Newton map is zero. -/
theorem exercise25_g_derivative_root (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) :
    HasDerivAt (exercise25Newton f p) 0 ξ := by
  simpa [hz] using (exercise25_g_derivative h (Ioo_subset_Icc_self hξ)).hasDerivAt
    (Icc_mem_nhds hξ.1 hξ.2)

/-- Because the root is interior, this is also the ordinary derivative limit
on a full neighborhood of the root. No second-derivative continuity is used. -/
theorem exercise25_deriv_limit (h : Exercise25Data f p q a b δ M)
    (hξ : ξ ∈ Ioo a b) (hz : f ξ = 0) :
    Tendsto (deriv (exercise25Newton f p)) (𝓝 ξ) (𝓝 0) := by
  have hl := exercise25_g_derivative_limit h hξ hz
  rw [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hξ.1 hξ.2)] at hl
  apply hl.congr'
  filter_upwards [Ioo_mem_nhds hξ.1 hξ.2] with x hx
  exact ((exercise25_g_derivative h (Ioo_subset_Icc_self hx)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)).deriv.symm

/-- The affine example satisfies all source assumptions, also with `M=0`. -/
theorem exercise25_affine_data {M : ℝ} (hM : 0 ≤ M) :
    Exercise25Data (fun x => x) (fun _ => 1) (fun _ => 0) (-1) 1 1 M := by
  constructor
  · norm_num
  · intro x _; exact (hasDerivAt_id x).hasDerivWithinAt
  · intro x _; exact (hasDerivAt_const x 1).hasDerivWithinAt
  · norm_num
  · norm_num
  · norm_num
  · intro x _; exact le_rfl
  · intro x _; exact le_rfl
  · intro x _; exact hM

/-- R05E25.termination_counterexample. With `f(x)=x`, `x₁=1/2`, the
source's x₂ and x₃ are zero. Strict descent and an interior Taylor point
are both impossible from x₂ onward. This uses `M=1`, so it is independent
of the zero-bound defect. -/
theorem exercise25_termination_counterexample :
    Exercise25Data (fun x => x) (fun _ => 1) (fun _ => 0) (-1) 1 1 1 ∧
    (0 : ℝ) ∈ Ioo (-1) 1 ∧ (fun x : ℝ => x) 0 = 0 ∧
    (1/2 : ℝ) ∈ Ioc 0 1 ∧
    exercise25Iter (fun x => x) (fun _ => 1) (1/2) 1 = 0 ∧
    exercise25Iter (fun x => x) (fun _ => 1) (1/2) 2 = 0 ∧
    ¬ (∀ n, exercise25Iter (fun x => x) (fun _ => 1) (1/2) (n+1) <
      exercise25Iter (fun x => x) (fun _ => 1) (1/2) n) ∧
    ¬ (∃ t ∈ Ioo 0 (exercise25Iter (fun x => x) (fun _ => 1) (1/2) 1),
      exercise25Iter (fun x => x) (fun _ => 1) (1/2) 2 - 0 =
        0 * ((exercise25Iter (fun x => x) (fun _ => 1) (1/2) 1) - 0)^2 / (2 * 1)) := by
  refine ⟨exercise25_affine_data (by norm_num), by norm_num, rfl, by norm_num,
    by norm_num [exercise25Iter_succ, exercise25Iter_zero, exercise25Newton],
    by norm_num [exercise25Iter_succ, exercise25Iter_zero, exercise25Newton], ?_, ?_⟩
  · intro hs
    have hh := hs 1
    norm_num [exercise25Iter_succ, exercise25Iter_zero, exercise25Newton] at hh
  · norm_num [exercise25Iter_succ, exercise25Iter_zero, exercise25Newton]

/-- The reciprocal in the printed bound is not a field inverse when `M=0`:
there is no real number that multiplies `A` to give one. -/
theorem exercise25_zero_bound_domain_obstruction :
    Exercise25Data (fun x => x) (fun _ => 1) (fun _ => 0) (-1) 1 1 0 ∧
    (0 : ℝ) / (2 * 1) = 0 ∧
    ¬ ∃ r : ℝ, ((0 : ℝ) / (2 * 1)) * r = 1 := by
  exact ⟨exercise25_affine_data le_rfl, by norm_num, by norm_num⟩

/-- The cube map is an order isomorphism of the real line. Its inverse is
the real cube root, including negative arguments. -/
def exercise25CubeIso : ℝ ≃o ℝ := by
  have ht : Tendsto (fun x : ℝ => x^3) atTop atTop := tendsto_pow_atTop (by decide)
  have hb : Tendsto (fun x : ℝ => x^3) atBot atBot := by
    convert tendsto_neg_atTop_atBot.comp (ht.comp tendsto_neg_atBot_atTop) using 1
    ext x
    simp only [Function.comp_apply]
    ring
  exact StrictMono.orderIsoOfSurjective (fun x : ℝ => x^3)
    (by exact (show Odd 3 by decide).strictMono_pow)
    ((continuous_id.pow 3).surjective ht hb)

/-- Real cube root, not a complex power or an even extension of a power. -/
def exercise25CubeRoot (x : ℝ) : ℝ := exercise25CubeIso.symm x

@[simp] theorem exercise25_cube_root_cube (x : ℝ) :
    (exercise25CubeRoot x)^3 = x := exercise25CubeIso.apply_symm_apply x

@[simp] theorem exercise25_cube_root_zero : exercise25CubeRoot 0 = 0 := by
  have hi := (show Odd 3 by decide).strictMono_pow (R := ℝ) |>.injective
  apply hi
  simp

theorem exercise25_cube_root_ne_zero (hx : x ≠ 0) : exercise25CubeRoot x ≠ 0 := by
  intro he
  have hi := exercise25_cube_root_cube x
  rw [he] at hi
  exact hx (by simpa using hi.symm)

/-- The cube root has a genuine derivative at each nonzero real point. -/
theorem exercise25_cube_root_derivative (hx : x ≠ 0) :
    HasDerivAt exercise25CubeRoot (3 * (exercise25CubeRoot x)^2)⁻¹ x := by
  have hc : ContinuousAt exercise25CubeRoot x := exercise25CubeIso.symm.continuous.continuousAt
  have hd : HasDerivAt (fun y : ℝ => y^3) (3 * (exercise25CubeRoot x)^2)
      (exercise25CubeRoot x) := by
    exact hasDerivAt_pow 3 (exercise25CubeRoot x)
  exact HasDerivAt.of_local_left_inverse hc hd
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (exercise25_cube_root_ne_zero hx)))
    (Eventually.of_forall exercise25_cube_root_cube)

/-- Newton's map for the real cube root is `x ↦ -2x` off zero. -/
theorem exercise25_cube_root_newton (hx : x ≠ 0) :
    exercise25Newton exercise25CubeRoot (deriv exercise25CubeRoot) x = -2 * x := by
  rw [exercise25Newton, (exercise25_cube_root_derivative hx).deriv, div_inv_eq_mul]
  have hc := exercise25_cube_root_cube x
  nlinarith [hc]

/-- R05E25.f: every nonzero starting point gives the exact alternating,
expanding sequence `(-2)^n*x₁`; no iterate reaches zero. -/
theorem exercise25_cube_root_iterates {x₁ : ℝ} (hx₁ : x₁ ≠ 0) (n : ℕ) :
    exercise25Iter exercise25CubeRoot (deriv exercise25CubeRoot) x₁ n = (-2)^n * x₁ ∧
    exercise25Iter exercise25CubeRoot (deriv exercise25CubeRoot) x₁ n ≠ 0 := by
  induction n with
  | zero => simpa using hx₁
  | succ n ih =>
    rw [exercise25Iter_succ, exercise25_cube_root_newton ih.2, ih.1]
    constructor
    · ring
    · exact mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ (by norm_num)) hx₁)

/-- All cube-root iterates have a genuine, nonzero derivative, so each
Newton quotient is defined in the ordinary field sense. -/
theorem exercise25_cube_root_well_defined {x₁ : ℝ} (hx₁ : x₁ ≠ 0) (n : ℕ) :
    let x := exercise25Iter exercise25CubeRoot (deriv exercise25CubeRoot) x₁ n
    HasDerivAt exercise25CubeRoot (deriv exercise25CubeRoot x) x ∧
      deriv exercise25CubeRoot x ≠ 0 := by
  dsimp only
  have hn := (exercise25_cube_root_iterates hx₁ n).2
  have hd := exercise25_cube_root_derivative hn
  refine ⟨by rwa [hd.deriv], ?_⟩
  rw [hd.deriv]
  exact inv_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (exercise25_cube_root_ne_zero hn)))

/-- Its absolute value tends to infinity, hence Newton's method diverges. -/
theorem exercise25_cube_root_divergence {x₁ : ℝ} (hx₁ : x₁ ≠ 0) :
    Tendsto (fun n => |exercise25Iter exercise25CubeRoot (deriv exercise25CubeRoot) x₁ n|)
      atTop atTop := by
  have he : (fun n => |exercise25Iter exercise25CubeRoot (deriv exercise25CubeRoot) x₁ n|) =
      (fun n => (2 : ℝ)^n * |x₁|) := by
    funext n
    rw [(exercise25_cube_root_iterates hx₁ n).1, abs_mul, abs_pow]
    norm_num
  rw [he]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
    (abs_pos.mpr hx₁)

/-- The missing derivative at zero is a genuine obstruction, not a value
assigned by Lean's totalized `deriv`. Differentiating the inverse identity
would otherwise say `0=1`. -/
theorem exercise25_cube_root_not_differentiable :
    ¬ DifferentiableAt ℝ exercise25CubeRoot 0 := by
  apply not_differentiableAt_of_local_left_inverse_hasDerivAt_zero
    (f := fun y : ℝ => y^3)
  · simpa using hasDerivAt_pow 3 (exercise25CubeRoot 0)
  · exact Eventually.of_forall exercise25_cube_root_cube

end Rudin.Chapter05
