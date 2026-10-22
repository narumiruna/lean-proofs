module

public import Math.Rudin.Chapter05.Exercise20
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

namespace Rudin.Chapter05

open Set

/-- The quotient jet, constructed by the product rule rather than by totalized
    iterated derivatives. The parameter `m` in the results below is `n-1`. -/
noncomputable def exercise18_quotientJet (F : ℕ → ℝ → ℝ) (β : ℝ) : ℕ → ℝ → ℝ :=
  Nat.rec (fun t => (F 0 t - F 0 β) / (t - β))
    (fun k Q t => (F (k + 1) t - (k + 1 : ℝ) * Q t) / (t - β))

@[simp] theorem exercise18_quotientJet_zero (F : ℕ → ℝ → ℝ) (β t : ℝ) :
    exercise18_quotientJet F β 0 t = (F 0 t - F 0 β) / (t - β) := rfl

theorem exercise18_quotientJet_succ (F : ℕ → ℝ → ℝ) (β t : ℝ) (k : ℕ) :
    exercise18_quotientJet F β (k + 1) t =
      (F (k + 1) t - (k + 1 : ℝ) * exercise18_quotientJet F β k t) / (t - β) := rfl

/-- Every claimed quotient derivative genuinely exists on the punctured
    interval, including one-sided derivatives at its original endpoints. -/
theorem exercise18_quotient_derivatives (F : ℕ → ℝ → ℝ) {a b β : ℝ} (m : ℕ)
    (hd : ∀ k < m, ∀ t ∈ Icc a b,
      HasDerivWithinAt (F k) (F (k + 1) t) (Icc a b) t) :
    ∀ k < m, ∀ t ∈ Icc a b \ {β},
      HasDerivWithinAt (exercise18_quotientJet F β k)
        (exercise18_quotientJet F β (k + 1) t) (Icc a b \ {β}) t := by
  intro k
  induction k with
  | zero =>
    intro hk t ht
    have hn : t - β ≠ 0 := sub_ne_zero.mpr (by simpa using ht.2)
    have h := ((hd 0 hk t ht.1).sub_const (F 0 β)).div
      ((hasDerivWithinAt_id t (Icc a b)).sub_const β) hn
    apply (h.mono sdiff_subset).congr_deriv
    simp only [exercise18_quotientJet_succ, exercise18_quotientJet_zero, Nat.cast_zero,
      zero_add, one_mul, mul_one, id_eq]
    field_simp [hn]
  | succ k ih =>
    intro hk t ht
    have hn : t - β ≠ 0 := sub_ne_zero.mpr (by simpa using ht.2)
    have hq := ih (by omega) t ht
    have h := (((hd (k + 1) hk t ht.1).mono sdiff_subset).sub
      (hq.const_mul (k + 1 : ℝ))).div
      ((hasDerivWithinAt_id t (Icc a b \ {β})).sub_const β) hn
    change HasDerivWithinAt
      (fun t => (F (k + 1) t - (k + 1 : ℝ) * exercise18_quotientJet F β k t) / (t - β))
      _ _ _
    apply h.congr_deriv
    simp only [exercise18_quotientJet_succ, Nat.cast_add, Nat.cast_one, mul_one,
      Pi.sub_apply, id_eq]
    field_simp [hn]; ring

/-- The exact quotient identity. The case `m=0` is precisely the source's
    `n=1` case, not a separate nondegenerate-order convention. -/
theorem exercise18_quotient_identity_algebra (F : ℕ → ℝ → ℝ) (m : ℕ)
    {α β : ℝ} (hαβ : α ≠ β) :
    F 0 β = exercise20_polynomial F (m + 1) α β +
      exercise18_quotientJet F β m α * (β - α) ^ (m + 1) / (m.factorial : ℝ) := by
  have hn : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  induction m with
  | zero =>
    simp [exercise20_polynomial, exercise18_quotientJet_zero]
    field_simp
    ring
  | succ m ih =>
    rw [exercise20_polynomial, Finset.sum_range_succ]
    change F 0 β = (exercise20_polynomial F (m + 1) α β +
      ((β - α) ^ (m + 1) / ((m + 1).factorial : ℝ)) * F (m + 1) α) + _
    rw [ih]
    simp only [exercise18_quotientJet_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp; ring

/-- Rudin 5.18 with all derivative-existence requirements and both one-sided
    endpoints. `F 0` is `f`; the jet assumptions express the existence of
    derivatives through order `m=n-1`. -/
theorem exercise18_quotient_taylor_identity (F : ℕ → ℝ → ℝ) {a b α β : ℝ} (m : ℕ)
    (_hα : α ∈ Icc a b) (_hβ : β ∈ Icc a b) (hαβ : α ≠ β)
    (hd : ∀ k < m, ∀ t ∈ Icc a b,
      HasDerivWithinAt (F k) (F (k + 1) t) (Icc a b) t) :
    (∀ k < m, ∀ t ∈ Icc a b \ {β},
      HasDerivWithinAt (exercise18_quotientJet F β k)
        (exercise18_quotientJet F β (k + 1) t) (Icc a b \ {β}) t) ∧
    F 0 β = exercise20_polynomial F (m + 1) α β +
      exercise18_quotientJet F β m α * (β - α) ^ (m + 1) / (m.factorial : ℝ) :=
  ⟨exercise18_quotient_derivatives F m hd, exercise18_quotient_identity_algebra F m hαβ⟩

end Rudin.Chapter05
