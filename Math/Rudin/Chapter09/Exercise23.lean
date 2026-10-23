module

public import Math.Rudin.Chapter09.Exercise20
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # The implicit function for `x² y₁ + exp x + y₂ = 0` -/

@[expose] public section

open Set
open scoped Topology ContDiff
namespace Rudin.Chapter09

/-- The source function, with the two free coordinates grouped together. -/
noncomputable def exercise23_f (p : ℝ × (ℝ × ℝ)) : ℝ :=
  p.1 ^ 2 * p.2.1 + Real.exp p.1 + p.2.2

/-- The full differential at `(0,1,-1)` is `(h,k₁,k₂) ↦ h+k₂`. -/
noncomputable def exercise23_L : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem exercise23_zero_value : exercise23_f (0, (1, -1)) = 0 := by
  norm_num [exercise23_f]

theorem exercise23_smooth : ContDiff ℝ 1 exercise23_f := by
  unfold exercise23_f
  fun_prop

theorem exercise23_differential :
    HasFDerivAt exercise23_f exercise23_L (0, (1, -1)) := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ), ((1 : ℝ), (-1 : ℝ))))
  have hy := hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ), ((1 : ℝ), (-1 : ℝ))))
  convert (((hx.pow 2).mul hy.fst).add hx.exp).add hy.snd using 1 <;>
    first | rfl | simp [exercise23_L]

theorem exercise23_nonzero_partial :
    HasDerivAt (fun x => exercise23_f (x, (1, -1))) 1 0 ∧
      deriv (fun x => exercise23_f (x, (1, -1))) 0 ≠ 0 := by
  have hd : HasDerivAt (fun x => exercise23_f (x, (1, -1))) 1 0 := by
    convert exercise23_differential.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) ((1 : ℝ), (-1 : ℝ)))) using 1 <;>
      simp [exercise23_L, Function.comp_def]
  exact ⟨hd, by rw [hd.deriv]; norm_num⟩

/-- The graph is constructed by the scalar inverse-function construction of Exercise 20. -/
noncomputable def exercise23_graph :
    ScalarImplicitGraph exercise23_f 0 (1, -1) exercise23_L :=
  Classical.choice (scalarImplicitGraph_exists exercise23_smooth.contDiffAt
    exercise23_differential exercise23_zero_value (by norm_num [exercise23_L]))

noncomputable def exercise23_g : ℝ × ℝ → ℝ := exercise23_graph.g

def exercise23_W : Set (ℝ × ℝ) := exercise23_graph.W

/-- An actual `C¹` graph on an open neighborhood, with local uniqueness. -/
theorem exercise23_implicit_function :
    IsOpen exercise23_W ∧ (1, -1) ∈ exercise23_W ∧
    ContDiffOn ℝ 1 exercise23_g exercise23_W ∧
    DifferentiableOn ℝ exercise23_g exercise23_W ∧
    exercise23_g (1, -1) = 0 ∧
    (∀ y ∈ exercise23_W, exercise23_f (exercise23_g y, y) = 0) ∧
    (∀ y ∈ exercise23_W, ∃! x, (x, y) ∈ exercise23_graph.e.source ∧
      exercise23_f (x, y) = 0) := by
  refine ⟨exercise23_graph.open_W, exercise23_graph.mem_W, exercise23_graph.smooth,
    exercise23_graph.smooth.differentiableOn (by norm_num), exercise23_graph.base_value,
    exercise23_graph.equation, ?_⟩
  intro y hy
  refine ⟨exercise23_g y, ⟨exercise23_graph.graph_mem y hy,
    exercise23_graph.equation y hy⟩, ?_⟩
  intro x hx
  exact (exercise23_graph.unique y hy x hx.1).mp hx.2

/-- The differential of the constructed graph is `(k₁,k₂) ↦ -k₂`. -/
theorem exercise23_graph_differential :
    HasFDerivAt exercise23_g (-(ContinuousLinearMap.snd ℝ ℝ ℝ)) (1, -1) := by
  have he : -(exercise23_L (1, 0))⁻¹ •
      (exercise23_L.comp (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) =
      -(ContinuousLinearMap.snd ℝ ℝ ℝ) := by
    apply ContinuousLinearMap.ext
    intro y
    simp [exercise23_L]
  exact he ▸ exercise23_graph.derivative

/-- The first partial of this graph exists and equals zero. -/
theorem exercise23_first_partial :
    HasDerivAt (fun y₁ => exercise23_g (y₁, -1)) 0 1 ∧
      deriv (fun y₁ => exercise23_g (y₁, -1)) 1 = 0 := by
  have hd : HasDerivAt (fun y₁ => exercise23_g (y₁, -1)) 0 1 := by
    convert exercise23_graph_differential.comp_hasDerivAt (1 : ℝ)
      ((hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_const (1 : ℝ) (-1 : ℝ))) using 1 <;>
      simp [Function.comp_def]
  exact ⟨hd, hd.deriv⟩

/-- The second partial of the same graph exists and equals minus one. -/
theorem exercise23_second_partial :
    HasDerivAt (fun y₂ => exercise23_g (1, y₂)) (-1) (-1) ∧
      deriv (fun y₂ => exercise23_g (1, y₂)) (-1) = -1 := by
  have hd : HasDerivAt (fun y₂ => exercise23_g (1, y₂)) (-1) (-1) := by
    convert exercise23_graph_differential.comp_hasDerivAt (-1 : ℝ)
      ((hasDerivAt_const (-1 : ℝ) (1 : ℝ)).prodMk (hasDerivAt_id (-1 : ℝ))) using 1 <;>
      simp [Function.comp_def]
  exact ⟨hd, hd.deriv⟩

end Rudin.Chapter09
