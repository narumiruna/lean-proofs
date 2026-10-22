module

public import Math.Rudin.Chapter05.Exercise26

@[expose] public section

open Set

namespace Rudin.Chapter05

/-- R05E28: the norm is the Euclidean norm, not the product maximum norm. -/
theorem exercise28_vector_zero_estimate {k : ℕ}
    {y v : ℝ → EuclideanSpace ℝ (Fin k)} {a b A : ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt y (v x) (Icc a b) x)
    (ha : y a = 0) (hbound : ∀ x ∈ Icc a b, ‖v x‖ ≤ A * ‖y x‖) :
    ∀ x ∈ Icc a b, y x = 0 :=
  exercise26_norm_zero hd ha hbound

/-- The source k-cell, with independent closed bounds in each coordinate. -/
def exercise28_cell {k : ℕ} (α β : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {y | ∀ j, y j ∈ Icc (α j) (β j)}

/-- R05E28: uniform Lipschitz control is required only on the stated cell.
Neither continuity of the derivative nor ambient endpoint derivatives are assumed. -/
theorem exercise28_system_uniqueness {k : ℕ} {a b A : ℝ} {α β : Fin k → ℝ}
    {Φ : ℝ → EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)}
    {y z : ℝ → EuclideanSpace ℝ (Fin k)}
    (hΦ : ∀ x ∈ Icc a b, ∀ u ∈ exercise28_cell α β,
      ∀ v ∈ exercise28_cell α β, ‖Φ x u - Φ x v‖ ≤ A * ‖u - v‖)
    (hycell : ∀ x ∈ Icc a b, y x ∈ exercise28_cell α β)
    (hzcell : ∀ x ∈ Icc a b, z x ∈ exercise28_cell α β)
    (hy : ∀ x ∈ Icc a b, HasDerivWithinAt y (Φ x (y x)) (Icc a b) x)
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (Φ x (z x)) (Icc a b) x)
    (hinit : y a = z a) : ∀ x ∈ Icc a b, y x = z x := by
  have h := exercise28_vector_zero_estimate
    (fun x hx => (hy x hx).sub (hz x hx)) (sub_eq_zero.mpr hinit)
    (fun x hx => hΦ x hx _ (hycell x hx) _ (hzcell x hx))
  exact fun x hx => sub_eq_zero.mp (h x hx)

end Rudin.Chapter05
