module

public import Math.Rudin.Chapter04.Exercise23

@[expose] public section
namespace Rudin.Chapter04
open Set

/-- A continuous midpoint-convex function with zero endpoint values lies below zero. -/
theorem exercise24_unit_interval {g : ℝ → ℝ} (hc : ContinuousOn g (Icc 0 1))
    (hm : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      g ((x + y) / 2) ≤ (g x + g y) / 2)
    (h0 : g 0 = 0) (h1 : g 1 = 0) : ∀ t ∈ Icc (0 : ℝ) 1, g t ≤ 0 := by
  obtain ⟨c, hc', hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hc
  have hbound : g c ≤ 0 := by
    by_cases h : c ≤ 1 / 2
    · have hc2 : 2 * c ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc'.1], by linarith⟩
      have hi := hm 0 (by simp) (2 * c) hc2
      have he : (0 + 2 * c) / 2 = c := by ring
      rw [he, h0] at hi
      have hh : g (2 * c) ≤ g c := hmax hc2
      linarith
    · have hc2 : 2 * c - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hc'.2]⟩
      have hi := hm (2 * c - 1) hc2 1 (by simp)
      have he : (2 * c - 1 + 1) / 2 = c := by ring
      rw [he, h1] at hi
      have hh : g (2 * c - 1) ≤ g c := hmax hc2
      linarith
  intro t ht
  exact (hmax ht).trans hbound

/-- All weights in the closed unit interval are obtained; in particular the source's
strictly interior weights are obtained. No endpoint continuity of f is assumed. -/
theorem exercise24_midpoint_to_convex {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Ioo a b))
    (hm : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      f ((x + y) / 2) ≤ (f x + f y) / 2) : ConvexOn ℝ (Ioo a b) f := by
  apply exercise23_convex_iff.mp
  intro x hx y hy l hl hl'
  let p : ℝ → ℝ := fun t => t * x + (1 - t) * y
  let q : ℝ → ℝ := fun t => t * f x + (1 - t) * f y
  have hp : MapsTo p (Icc 0 1) (Ioo a b) := by
    intro t ht
    exact (convex_Ioo a b) hx hy ht.1 (by linarith [ht.2]) (by ring)
  have hpcont : Continuous p := by dsimp [p]; fun_prop
  have hqcont : Continuous q := by dsimp [q]; fun_prop
  have hgcont : ContinuousOn (fun t => f (p t) - q t) (Icc 0 1) :=
    (hc.comp hpcont.continuousOn hp).sub hqcont.continuousOn
  have hgmid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      f (p ((s + t) / 2)) - q ((s + t) / 2) ≤
      ((f (p s) - q s) + (f (p t) - q t)) / 2 := by
    intro s hs t ht
    have hi := hm (p s) (hp hs) (p t) (hp ht)
    have he : p ((s + t) / 2) = (p s + p t) / 2 := by dsimp [p]; ring
    rw [he]
    have hqe : q ((s + t) / 2) = (q s + q t) / 2 := by dsimp [q]; ring
    rw [hqe]
    linarith
  have hbnd := exercise24_unit_interval hgcont hgmid (by simp [p, q]) (by simp [p, q])
    l ⟨hl.le, hl'.le⟩
  dsimp [p, q] at hbnd
  linarith

theorem exercise24_source {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Ioo a b))
    (hm : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      f ((x + y) / 2) ≤ (f x + f y) / 2) : exercise23Convex f a b :=
  exercise23_convex_iff.mpr (exercise24_midpoint_to_convex hc hm)

end Rudin.Chapter04
