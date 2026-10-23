module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

/-! # A rank-one map onto an ellipse

The source and target use the Euclidean norm. The derivative is exhibited as
one nonzero linear functional times one nonzero vector.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter09
open Set

abbrev Exercise24Space := EuclideanSpace ℝ (Fin 2)

def exercise24Function (p : Exercise24Space) : Exercise24Space :=
  !₂[(p 0 ^ 2 - p 1 ^ 2) / (p 0 ^ 2 + p 1 ^ 2), p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2)]

def exercise24Functional (p : Exercise24Space) : Exercise24Space →L[ℝ] ℝ :=
  p 1 • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 -
    p 0 • PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1

def exercise24Vector (p : Exercise24Space) : Exercise24Space :=
  !₂[4 * p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2) ^ 2,
    (p 1 ^ 2 - p 0 ^ 2) / (p 0 ^ 2 + p 1 ^ 2) ^ 2]

def exercise24Derivative (p : Exercise24Space) : Exercise24Space →L[ℝ] Exercise24Space :=
  (exercise24Functional p).smulRight (exercise24Vector p)

theorem exercise24_denominator {p : Exercise24Space} (hp : p ≠ 0) :
    p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by
  intro he
  have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0)]
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 0)]
  apply hp
  ext i
  fin_cases i <;> simp [h0, h1]

theorem exercise24_hasFDerivAt {p : Exercise24Space} (hp : p ≠ 0) :
    HasFDerivAt exercise24Function (exercise24Derivative p) p := by
  have hx := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (0 : Fin 2)
  have hy := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (1 : Fin 2)
  have hd := hx.pow 2 |>.add (hy.pow 2)
  have hn := exercise24_denominator hp
  have hi := (hasFDerivAt_inv hn).comp p hd
  have h0 := ((hx.pow 2).sub (hy.pow 2)).mul hi
  have h1 := (hx.mul hy).mul hi
  rw [← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp 2).mpr
  intro i
  fin_cases i
  · convert h0.hasFDerivWithinAt using 1 <;> ext h <;>
      simp [exercise24Function, exercise24Derivative, exercise24Functional, exercise24Vector,
        ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, div_eq_mul_inv]
    field_simp
    ring
  · convert h1.hasFDerivWithinAt using 1 <;> ext h <;>
      simp [exercise24Function, exercise24Derivative, exercise24Functional, exercise24Vector,
        ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, div_eq_mul_inv]
    field_simp
    ring

theorem exercise24_functional_ne_zero {p : Exercise24Space} (hp : p ≠ 0) :
    exercise24Functional p ≠ 0 := by
  intro he
  have he0 := congrArg (fun L : Exercise24Space →L[ℝ] ℝ ↦ L !₂[1,0]) he
  have he1 := congrArg (fun L : Exercise24Space →L[ℝ] ℝ ↦ L !₂[0,1]) he
  simp [exercise24Functional] at he0 he1
  apply hp
  ext i
  fin_cases i <;> simp [he0, he1]

theorem exercise24_vector_ne_zero {p : Exercise24Space} (hp : p ≠ 0) :
    exercise24Vector p ≠ 0 := by
  intro he
  have hn := pow_ne_zero 2 (exercise24_denominator hp)
  have h0 := congrArg (fun v : Exercise24Space ↦ v 0) he
  have h1 := congrArg (fun v : Exercise24Space ↦ v 1) he
  change 4 * p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2) ^ 2 = 0 at h0
  change (p 1 ^ 2 - p 0 ^ 2) / (p 0 ^ 2 + p 1 ^ 2) ^ 2 = 0 at h1
  have hm : p 0 * p 1 = 0 := by
    have hz := (div_eq_zero_iff.mp h0).resolve_right hn
    nlinarith
  have hs : p 1 ^ 2 - p 0 ^ 2 = 0 := (div_eq_zero_iff.mp h1).resolve_right hn
  rcases mul_eq_zero.mp hm with h | h
  · have h' : p 1 = 0 := by nlinarith
    apply hp; ext i; fin_cases i <;> simp [h, h']
  · have h' : p 0 = 0 := by nlinarith
    apply hp; ext i; fin_cases i <;> simp [h, h']

/-- Rank means the dimension of the range of the genuine Fréchet derivative. -/
theorem exercise24_rank {p : Exercise24Space} (hp : p ≠ 0) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ exercise24Function p).toLinearMap) = 1 := by
  rw [(exercise24_hasFDerivAt hp).fderiv]
  unfold exercise24Derivative
  rw [ContinuousLinearMap.range_smulRight_apply (exercise24_functional_ne_zero hp)]
  exact finrank_span_singleton (exercise24_vector_ne_zero hp)

theorem exercise24_on_ellipse {p : Exercise24Space} (hp : p ≠ 0) :
    (exercise24Function p 0) ^ 2 + 4 * (exercise24Function p 1) ^ 2 = 1 := by
  have hn := exercise24_denominator hp
  change ((p 0 ^ 2 - p 1 ^ 2) / (p 0 ^ 2 + p 1 ^ 2)) ^ 2 +
    4 * (p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2)) ^ 2 = 1
  field_simp
  ring

/-- The entire ellipse is attained, not only a subset of it. -/
theorem exercise24_range :
    exercise24Function '' ({0}ᶜ : Set Exercise24Space) = {p | p 0 ^ 2 + 4 * p 1 ^ 2 = 1} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact exercise24_on_ellipse hq
  · intro hp
    change p 0 ^ 2 + 4 * p 1 ^ 2 = 1 at hp
    by_cases h : p 0 = -1
    · have hy : p 1 = 0 := by rw [h] at hp; nlinarith
      refine ⟨!₂[0,1], by simp, ?_⟩
      ext i
      fin_cases i <;> simp [exercise24Function, h, hy]
    · have hq : (1 + p 0) ^ 2 + (2 * p 1) ^ 2 = 2 * (1 + p 0) := by nlinarith
      have hd : 1 + p 0 ≠ 0 := by intro he; apply h; linarith
      refine ⟨!₂[1 + p 0, 2 * p 1], ?_, ?_⟩
      · intro he
        have he0 := congrArg (fun v : Exercise24Space ↦ v 0) he
        exact hd he0
      · ext i
        fin_cases i
        · change ((1 + p 0) ^ 2 - (2 * p 1) ^ 2) /
            ((1 + p 0) ^ 2 + (2 * p 1) ^ 2) = p 0
          rw [hq]
          apply (div_eq_iff (mul_ne_zero (by norm_num) hd)).mpr
          nlinarith
        · change (1 + p 0) * (2 * p 1) /
            ((1 + p 0) ^ 2 + (2 * p 1) ^ 2) = p 1
          rw [hq]
          field_simp

end Rudin.Chapter09
