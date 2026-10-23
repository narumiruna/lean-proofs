module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-! # R09E13: velocity on the unit sphere
Source: book page 240, PDF page 249. The tangent plane is the orthogonal
complement of the radius. It contains the zero vector.
-/

@[expose] public section
namespace Rudin.Chapter09

theorem exercise13_orthogonality {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (hunit : ∀ t, ‖f t‖ = 1) (t : ℝ) :
    HasDerivAt f (deriv f t) t ∧ inner ℝ (deriv f t) (f t) = 0 := by
  have heq : (fun s => inner ℝ (f s) (f s)) = fun _ => (1 : ℝ) := by
    funext s
    simp [hunit s]
  have hd := ((hf t).hasDerivAt.inner ℝ (hf t).hasDerivAt)
  rw [heq] at hd
  have h := hd.unique (hasDerivAt_const t (1 : ℝ))
  have hc : inner ℝ (f t) (deriv f t) = inner ℝ (deriv f t) (f t) := real_inner_comm _ _
  rw [hc] at h
  exact ⟨(hf t).hasDerivAt, by linarith⟩

/-- The affine tangent plane at a unit point, without a nonzero-velocity condition. -/
def sphereTangentPlane (p : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {q | inner ℝ (q - p) p = 0}

theorem exercise13_geometry {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hf : Differentiable ℝ f) (hunit : ∀ t, ‖f t‖ = 1) (t s : ℝ) :
    f t ∈ Metric.sphere 0 1 ∧
    f t + s • deriv f t ∈ sphereTangentPlane (f t) ∧
    f t + s • (0 : EuclideanSpace ℝ (Fin 3)) ∈ sphereTangentPlane (f t) := by
  have h := (exercise13_orthogonality hf hunit t).2
  simp [hunit, sphereTangentPlane, real_inner_smul_left, h]
end Rudin.Chapter09
