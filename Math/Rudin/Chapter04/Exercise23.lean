module

public import Mathlib

@[expose] public section
namespace Rudin.Chapter04
open Set

/-- The definition in Exercise 23 uses strictly interior weights. -/
def exercise23Convex (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, ∀ l : ℝ, 0 < l → l < 1 →
    f (l * x + (1 - l) * y) ≤ l * f x + (1 - l) * f y

theorem exercise23_convex_iff {f : ℝ → ℝ} {a b : ℝ} :
    exercise23Convex f a b ↔ ConvexOn ℝ (Ioo a b) f := by
  constructor
  · intro h
    refine ⟨convex_Ioo a b, ?_⟩
    intro x hx y hy l m hl hm hlm
    by_cases h0 : l = 0
    · subst l; simp_all
    by_cases h1 : l = 1
    · subst l; simp_all
    have hm' : m = 1 - l := by linarith
    subst m
    exact h x hx y hy l (lt_of_le_of_ne hl (Ne.symm h0)) (lt_of_le_of_ne (by linarith) h1)
  · intro h x hx y hy l hl hl'
    exact h.2 hx hy hl.le (by linarith) (by ring)

theorem exercise23_convex_continuity {f : ℝ → ℝ} {a b : ℝ}
    (hf : exercise23Convex f a b) : ContinuousOn f (Ioo a b) :=
  (exercise23_convex_iff.mp hf).continuousOn isOpen_Ioo

/-- The outer function need only be nondecreasing on its interval of definition. -/
theorem exercise23_increasing_convex_composition {f h : ℝ → ℝ}
    {S T : Set ℝ} (hf : ConvexOn ℝ S f) (hh : ConvexOn ℝ T h)
    (hm : MonotoneOn h T) (hr : MapsTo f S T) : ConvexOn ℝ S (h ∘ f) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy l m hl hm' hlm
  exact (hm (hr (hf.1 hx hy hl hm' hlm))
    (hh.1 (hr hx) (hr hy) hl hm' hlm) (hf.2 hx hy hl hm' hlm)).trans
    (hh.2 (hr hx) (hr hy) hl hm' hlm)

/-- The exponential in the source is a special case of increasing convex composition. -/
theorem exercise23_exp_convex {f : ℝ → ℝ} {a b : ℝ}
    (hf : exercise23Convex f a b) : exercise23Convex (Real.exp ∘ f) a b := by
  apply exercise23_convex_iff.mpr
  exact exercise23_increasing_convex_composition (exercise23_convex_iff.mp hf)
    convexOn_exp (Real.exp_monotone.monotoneOn _) (fun _ _ => mem_univ _)

theorem exercise23_first_slope_inequality {f : ℝ → ℝ} {a b s t u : ℝ}
    (hf : exercise23Convex f a b) (has : a < s) (hst : s < t)
    (htu : t < u) (hub : u < b) :
    (f t - f s) / (t - s) ≤ (f u - f s) / (u - s) :=
  (exercise23_convex_iff.mp hf).secant_mono_aux2
    ⟨has, hst.trans (htu.trans hub)⟩ ⟨has.trans (hst.trans htu), hub⟩ hst htu

theorem exercise23_second_slope_inequality {f : ℝ → ℝ} {a b s t u : ℝ}
    (hf : exercise23Convex f a b) (has : a < s) (hst : s < t)
    (htu : t < u) (hub : u < b) :
    (f u - f s) / (u - s) ≤ (f u - f t) / (u - t) :=
  (exercise23_convex_iff.mp hf).secant_mono_aux3
    ⟨has, hst.trans (htu.trans hub)⟩ ⟨has.trans (hst.trans htu), hub⟩ hst htu

end Rudin.Chapter04
