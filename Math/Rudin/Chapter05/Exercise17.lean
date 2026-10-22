module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

namespace Rudin.Chapter05

open Set

noncomputable def exercise17_example (x : ℝ) : ℝ := (x ^ 3 + x ^ 2) / 2
noncomputable def exercise17_example₁ (x : ℝ) : ℝ := (3 * x ^ 2 + 2 * x) / 2
noncomputable def exercise17_example₂ (x : ℝ) : ℝ := 3 * x + 1

theorem exercise17_example_derivatives (x : ℝ) :
    HasDerivAt exercise17_example (exercise17_example₁ x) x ∧
    HasDerivAt exercise17_example₁ (exercise17_example₂ x) x ∧
    HasDerivAt exercise17_example₂ 3 x := by
  constructor
  · convert (((hasDerivAt_id x).fun_pow 3).add ((hasDerivAt_id x).fun_pow 2)).div_const 2 using 1
    · rfl
    · simp [exercise17_example₁]
  constructor
  · convert ((((hasDerivAt_id x).fun_pow 2).const_mul 3).add
      ((hasDerivAt_id x).const_mul 2)).div_const 2 using 1
    · rfl
    · dsimp [exercise17_example₂]; ring
  · convert ((hasDerivAt_id x).const_mul 3).add_const 1 using 1
    · rfl
    · simp

private theorem exercise17_rolle {g g' : ℝ → ℝ} {a b : ℝ}
    (ha : (-1 : ℝ) ≤ a) (hb : b ≤ 1) (hab : a < b)
    (hd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt g (g' t) (Icc (-1) 1) t)
    (hzero : g a = g b) : ∃ c ∈ Ioo a b, g' c = 0 := by
  apply exists_hasDerivAt_eq_zero hab
    (fun t ht => ((hd t ⟨ha.trans ht.1, ht.2.trans hb⟩).continuousWithinAt).mono
      (Icc_subset_Icc ha hb)) hzero
  intro t ht
  exact (hd t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- Rudin 5.17. The stronger equality is obtained by repeated Rolle.
    Derivatives at -1 and 1 are only within the closed interval. -/
theorem exercise17_third_derivative_eq {f f₁ f₂ f₃ : ℝ → ℝ}
    (hd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f₁ t) (Icc (-1) 1) t)
    (hd₁ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f₁ (f₂ t) (Icc (-1) 1) t)
    (hd₂ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f₂ (f₃ t) (Icc (-1) 1) t)
    (hm : f (-1) = 0) (hz : f 0 = 0) (hp : f 1 = 1) (hdz : f₁ 0 = 0) :
    ∃ x ∈ Ioo (-1 : ℝ) 1, f₃ x = 3 := by
  let g := fun t => f t - exercise17_example t
  let g₁ := fun t => f₁ t - exercise17_example₁ t
  let g₂ := fun t => f₂ t - exercise17_example₂ t
  let g₃ := fun t => f₃ t - 3
  have hg : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt g (g₁ t) (Icc (-1) 1) t :=
    fun t ht => (hd t ht).sub (exercise17_example_derivatives t).1.hasDerivWithinAt
  have hg₁ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt g₁ (g₂ t) (Icc (-1) 1) t :=
    fun t ht => (hd₁ t ht).sub (exercise17_example_derivatives t).2.1.hasDerivWithinAt
  have hg₂ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt g₂ (g₃ t) (Icc (-1) 1) t :=
    fun t ht => (hd₂ t ht).sub (exercise17_example_derivatives t).2.2.hasDerivWithinAt
  have hgm : g (-1) = 0 := by norm_num [g, exercise17_example, hm]
  have hgz : g 0 = 0 := by simp [g, exercise17_example, hz]
  have hgp : g 1 = 0 := by norm_num [g, exercise17_example, hp]
  have hgd : g₁ 0 = 0 := by simp [g₁, exercise17_example₁, hdz]
  obtain ⟨u, hu, hgu⟩ := exercise17_rolle (by norm_num) (by norm_num)
    (by norm_num : (-1 : ℝ) < 0) hg (hgm.trans hgz.symm)
  obtain ⟨v, hv, hgv⟩ := exercise17_rolle (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) < 1) hg (hgz.trans hgp.symm)
  obtain ⟨s, hs, hgs⟩ := exercise17_rolle hu.1.le (by norm_num) hu.2 hg₁ (hgu.trans hgd.symm)
  obtain ⟨t, ht, hgt⟩ := exercise17_rolle (by norm_num) hv.2.le hv.1 hg₁ (hgd.trans hgv.symm)
  obtain ⟨x, hx, hgx⟩ := exercise17_rolle (hu.1.trans hs.1).le (ht.2.trans hv.2).le
    (hs.2.trans ht.1) hg₂ (hgs.trans hgt.symm)
  refine ⟨x, ⟨(hu.1.trans hs.1).trans hx.1, hx.2.trans (ht.2.trans hv.2)⟩, ?_⟩
  dsimp [g₃] at hgx
  linarith

theorem exercise17_third_derivative_lower_bound {f f₁ f₂ f₃ : ℝ → ℝ}
    (hd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f (f₁ t) (Icc (-1) 1) t)
    (hd₁ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f₁ (f₂ t) (Icc (-1) 1) t)
    (hd₂ : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt f₂ (f₃ t) (Icc (-1) 1) t)
    (hm : f (-1) = 0) (hz : f 0 = 0) (hp : f 1 = 1) (hdz : f₁ 0 = 0) :
    ∃ x ∈ Ioo (-1 : ℝ) 1, 3 ≤ f₃ x := by
  obtain ⟨x, hx, he⟩ := exercise17_third_derivative_eq hd hd₁ hd₂ hm hz hp hdz
  exact ⟨x, hx, he.ge⟩

/-- The cubic has the required data and third derivative identically 3. -/
theorem exercise17_sharpness :
    exercise17_example (-1) = 0 ∧ exercise17_example 0 = 0 ∧
    exercise17_example 1 = 1 ∧ exercise17_example₁ 0 = 0 ∧
    (∀ x : ℝ, HasDerivAt exercise17_example (exercise17_example₁ x) x ∧
      HasDerivAt exercise17_example₁ (exercise17_example₂ x) x ∧
      HasDerivAt exercise17_example₂ 3 x) := by
  norm_num [exercise17_example, exercise17_example₁]
  exact exercise17_example_derivatives

end Rudin.Chapter05
