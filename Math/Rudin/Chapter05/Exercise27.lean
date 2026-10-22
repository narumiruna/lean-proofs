module

public import Math.Rudin.Chapter05.Exercise26

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter05

/-- R05E27: the Lipschitz estimate is confined to the closed rectangle. -/
theorem exercise27_lipschitz_uniqueness {a b α β A : ℝ} {φ : ℝ → ℝ → ℝ}
    {y z : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc a b, ∀ u ∈ Icc α β, ∀ v ∈ Icc α β,
      |φ x u - φ x v| ≤ A * |u - v|)
    (hyR : ∀ x ∈ Icc a b, y x ∈ Icc α β)
    (hzR : ∀ x ∈ Icc a b, z x ∈ Icc α β)
    (hy : ∀ x ∈ Icc a b, HasDerivWithinAt y (φ x (y x)) (Icc a b) x)
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (φ x (z x)) (Icc a b) x)
    (hinit : y a = z a) : ∀ x ∈ Icc a b, y x = z x := by
  have h := exercise26_zero_solution (fun x hx => (hy x hx).sub (hz x hx))
    (sub_eq_zero.mpr hinit) (fun x hx => hφ x hx _ (hyR x hx) _ (hzR x hx))
  exact fun x hx => sub_eq_zero.mp (h x hx)

/-- Waiting until time `t`, then following the positive parabolic branch. -/
noncomputable def exercise27_wait (t x : ℝ) : ℝ :=
  if x ≤ t then 0 else (x - t)^2 / 4

/-- The real square-root equation includes its domain condition. -/
def exercise27_sqrt_solution (b : ℝ) (y : ℝ → ℝ) : Prop :=
  y 0 = 0 ∧ ∀ x ∈ Icc 0 b,
    0 ≤ y x ∧ HasDerivWithinAt y (Real.sqrt (y x)) (Icc 0 b) x

private theorem exercise27_parabola_deriv (t x : ℝ) :
    HasDerivAt (fun s : ℝ => (s-t)^2 / 4) ((x-t)/2) x := by
  convert (((hasDerivAt_id x).sub_const t).pow 2).div_const 4 using 1 <;>
    simp only [id_eq, Pi.pow_apply]; ring

/-- Each waiting-time branch has an ambient derivative, including at the join. -/
theorem exercise27_wait_deriv (t x : ℝ) :
    HasDerivAt (exercise27_wait t) (Real.sqrt (exercise27_wait t x)) x := by
  rcases lt_trichotomy x t with h | heq | h
  · have he : exercise27_wait t =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds h] with s hs
      simp [exercise27_wait, hs.le]
    simpa [exercise27_wait, h.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · subst x
    have hl : HasDerivWithinAt (exercise27_wait t) 0 (Iic t) t := by
      apply (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt.congr
      · intro s hs; simp [exercise27_wait, show s ≤ t from hs]
      · simp [exercise27_wait]
    have hr : HasDerivWithinAt (exercise27_wait t) 0 (Ici t) t := by
      have hp := (exercise27_parabola_deriv t t).hasDerivWithinAt (s := Ici t)
      simp only [sub_self, zero_div] at hp
      apply hp.congr
      · intro s hs
        by_cases he : s ≤ t
        · have : s = t := le_antisymm he hs
          simp [this, exercise27_wait]
        · simp [exercise27_wait, he]
      · simp [exercise27_wait]
    have hu := hl.union hr
    simpa [Iic_union_Ici, exercise27_wait] using hu
  · have he : exercise27_wait t =ᶠ[𝓝 x] (fun s => (s-t)^2/4) := by
      filter_upwards [eventually_gt_nhds h] with s hs
      simp [exercise27_wait, not_le.mpr hs]
    have hs : Real.sqrt (exercise27_wait t x) = (x-t)/2 := by
      rw [exercise27_wait, ite_eq_right (not_le.mpr h)]
      rw [show (x-t)^2/4 = ((x-t)/2)^2 by ring, Real.sqrt_sq (by linarith)]
    rw [hs]
    exact (exercise27_parabola_deriv t x).congr_of_eventuallyEq he

/-- All waiting times in the forward interval, including `t=b` (the zero solution). -/
theorem exercise27_wait_solution {b t : ℝ} (ht : t ∈ Icc 0 b) :
    exercise27_sqrt_solution b (exercise27_wait t) := by
  refine ⟨by simp [exercise27_wait, ht.1], fun x hx => ⟨?_, ?_⟩⟩
  · unfold exercise27_wait
    split_ifs <;> positivity
  · exact (exercise27_wait_deriv t x).hasDerivWithinAt

/-- The zero solution remains separate from the nonzero branch for `b>0`. -/
theorem exercise27_nonunique_examples {b : ℝ} (hb : 0 < b) :
    exercise27_sqrt_solution b (fun _ => 0) ∧
    exercise27_sqrt_solution b (fun x => x^2/4) ∧
    ¬ EqOn (fun _ : ℝ => (0 : ℝ)) (fun x => x^2/4) (Icc 0 b) := by
  refine ⟨⟨rfl, fun x hx => ⟨le_rfl, by simpa using
    (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt (s := Icc 0 b)⟩⟩, ?_, ?_⟩
  · refine ⟨by norm_num, fun x hx => ⟨by positivity, ?_⟩⟩
    have hs : Real.sqrt (x^2/4) = x/2 := by
      rw [show x^2/4 = (x/2)^2 by ring, Real.sqrt_sq (div_nonneg hx.1 (by norm_num))]
    rw [hs]
    simpa using (exercise27_parabola_deriv 0 x).hasDerivWithinAt (s := Icc 0 b)
  · intro he
    have := he (right_mem_Icc.mpr hb.le)
    nlinarith

/-- R05E27: every forward real solution is a waiting-time solution.
The endpoint `t=b` represents the identically zero solution on the interval. -/
theorem exercise27_all_nonunique_solutions {b : ℝ} (hb : 0 ≤ b) {y : ℝ → ℝ}
    (hy : exercise27_sqrt_solution b y) :
    ∃ t ∈ Icc 0 b, EqOn y (exercise27_wait t) (Icc 0 b) := by
  have hc : ContinuousOn y (Icc 0 b) := fun x hx => (hy.2 x hx).2.continuousWithinAt
  have hm : MonotoneOn y (Icc 0 b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hc
      (fun x hx => (hy.2 x (interior_subset hx)).2.mono interior_subset)
      (fun x hx => Real.sqrt_nonneg _)
  have hk : IsCompact (Icc 0 b ∩ y ⁻¹' Iic 0) :=
    hc.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc 0
  obtain ⟨t, ht, hmax⟩ := hk.exists_isGreatest ⟨0, ⟨⟨le_rfl, hb⟩, by simp [hy.1]⟩⟩
  have ht0 : y t = 0 := le_antisymm ht.2 (hy.2 t ht.1).1
  have hp : ∀ x ∈ Icc 0 b, t < x → 0 < y x := by
    intro x hx htx
    by_contra hn
    have := hmax ⟨hx, le_of_not_gt hn⟩
    linarith
  refine ⟨t, ht.1, fun x hx => ?_⟩
  by_cases hxt : x ≤ t
  · have hz : y x = 0 := le_antisymm ((hm hx ht.1 hxt).trans_eq ht0) (hy.2 x hx).1
    simp [exercise27_wait, hxt, hz]
  · have htx : t < x := lt_of_not_ge hxt
    have hsub : Icc t x ⊆ Icc 0 b := Icc_subset_Icc ht.1.1 hx.2
    have hd : ∀ s ∈ Ioo t x, HasDerivAt (fun r => Real.sqrt (y r)) (1/2 : ℝ) s := by
      intro s hs
      have hsR : s ∈ Icc 0 b := hsub (Ioo_subset_Icc_self hs)
      have hpos := hp s hsR hs.1
      have h := ((hy.2 s hsR).2.hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt ht.1.1 hs.1) (lt_of_lt_of_le hs.2 hx.2))).sqrt hpos.ne'
      convert h using 1
      field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]
    have hscont : ContinuousOn (fun s => Real.sqrt (y s)) (Icc t x) :=
      Real.continuous_sqrt.comp_continuousOn (hc.mono hsub)
    obtain ⟨s, hs, he⟩ := exists_deriv_eq_slope (fun r => Real.sqrt (y r)) htx hscont
      (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    rw [(hd s hs).deriv, ht0, Real.sqrt_zero, sub_zero] at he
    have heq : Real.sqrt (y x) = (x-t)/2 := by
      have := (eq_div_iff (sub_ne_zero.mpr htx.ne')).mp he
      linarith
    rw [exercise27_wait, ite_eq_right hxt]
    have hsquare := Real.sq_sqrt (hy.2 x hx).1
    rw [heq] at hsquare
    nlinarith

/-- A full if-and-only-if classification on any closed forward interval. -/
theorem exercise27_sqrt_classification {b : ℝ} (hb : 0 ≤ b) {y : ℝ → ℝ} :
    exercise27_sqrt_solution b y ↔
      ∃ t ∈ Icc 0 b, EqOn y (exercise27_wait t) (Icc 0 b) := by
  refine ⟨exercise27_all_nonunique_solutions hb, ?_⟩
  rintro ⟨t, ht, he⟩
  have hw := exercise27_wait_solution ht
  refine ⟨(he (left_mem_Icc.mpr hb)).trans hw.1, fun x hx => ?_⟩
  refine ⟨by rw [he hx]; exact (hw.2 x hx).1, ?_⟩
  rw [he hx]
  exact (hw.2 x hx).2.congr (fun s hs => he hs) (he hx)

end Rudin.Chapter05
