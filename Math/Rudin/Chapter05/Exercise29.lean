module

public import Math.Rudin.Chapter05.Exercise28

@[expose] public section

open Set
open scoped BigOperators

namespace Rudin.Chapter05

/-- The companion system for a scalar equation of order `n+1`. Thus `n=0`
is the first-order case. The coordinates use zero-based indices. -/
noncomputable def exercise29_field {n : ℕ} (f : ℝ → ℝ)
    (g : Fin (n+1) → ℝ → ℝ) (x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (Fin.lastCases (f x - ∑ j, g j x * u j)
    (fun j : Fin n => u j.succ))

/-- The first `n` equations are the successive-derivative equations. -/
theorem exercise29_field_successor {n : ℕ} (f : ℝ → ℝ)
    (g : Fin (n+1) → ℝ → ℝ) (x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n+1))) (j : Fin n) :
    exercise29_field f g x u j.castSucc = u j.succ := by
  simp [exercise29_field]

/-- The last equation is the original scalar equation solved for its highest derivative. -/
theorem exercise29_field_last {n : ℕ} (f : ℝ → ℝ)
    (g : Fin (n+1) → ℝ → ℝ) (x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n+1))) :
    exercise29_field f g x u (Fin.last n) = f x - ∑ j, g j x * u j := by
  simp [exercise29_field]

/-- For order one there are no shift equations, and there is one scalar equation. -/
theorem exercise29_field_order_one (f : ℝ → ℝ) (g : Fin 1 → ℝ → ℝ)
    (x : ℝ) (u : EuclideanSpace ℝ (Fin 1)) :
    exercise29_field f g x u 0 = f x - g 0 x * u 0 := by
  simpa using exercise29_field_last f g x u

/-- Genuine finite-order scalar derivative data. Every lower derivative has an
actual relative derivative. No continuity of the highest derivative is imposed.
Values of the auxiliary functions outside the interval have no significance. -/
def exercise29_scalar_solution {n : ℕ} (a b : ℝ) (f : ℝ → ℝ)
    (g : Fin (n+1) → ℝ → ℝ) (c : Fin (n+1) → ℝ) (y : ℝ → ℝ) : Prop :=
  ∃ D : ℕ → ℝ → ℝ,
    EqOn (D 0) y (Icc a b) ∧
    (∀ j < n+1, ∀ x ∈ Icc a b,
      HasDerivWithinAt (D j) (D (j+1) x) (Icc a b) x) ∧
    (∀ x ∈ Icc a b, D (n+1) x + ∑ j, g j x * D j x = f x) ∧
    (∀ j : Fin (n+1), D j a = c j)

/-- The vector equation and all `n+1` initial data. -/
def exercise29_system_solution {n : ℕ} (a b : ℝ) (f : ℝ → ℝ)
    (g : Fin (n+1) → ℝ → ℝ) (c : Fin (n+1) → ℝ)
    (u : ℝ → EuclideanSpace ℝ (Fin (n+1))) : Prop :=
  (∀ x ∈ Icc a b,
    HasDerivWithinAt u (exercise29_field f g x (u x)) (Icc a b) x) ∧
  ∀ j, u a j = c j

private theorem exercise29_deriv_vector_iff {n : ℕ}
    {u : ℝ → EuclideanSpace ℝ (Fin (n+1))}
    {v : EuclideanSpace ℝ (Fin (n+1))} {s : Set ℝ} {x : ℝ} :
    HasDerivWithinAt u v s x ↔
      ∀ j, HasDerivWithinAt (fun t => u t j) (v j) s x := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)
  constructor
  · intro h
    exact hasDerivWithinAt_pi.mp (e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x h)
  · intro h
    have hp := hasDerivWithinAt_pi.mpr h
    exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt x hp

/-- R05E29: equivalence with the actual finite companion system, including
all initial data and order one. -/
theorem exercise29_system_reduction {n : ℕ} {a b : ℝ} (_hab : a ≤ b)
    {f : ℝ → ℝ} {g : Fin (n+1) → ℝ → ℝ} {c : Fin (n+1) → ℝ} {y : ℝ → ℝ} :
    exercise29_scalar_solution a b f g c y ↔
      ∃ u, exercise29_system_solution a b f g c u ∧
        EqOn (fun x => u x 0) y (Icc a b) := by
  constructor
  · rintro ⟨D, hD0, hD, heq, hinit⟩
    let u : ℝ → EuclideanSpace ℝ (Fin (n+1)) :=
      fun x => WithLp.toLp 2 (fun j => D j x)
    refine ⟨u, ⟨?_, hinit⟩, hD0⟩
    intro x hx
    apply exercise29_deriv_vector_iff.mpr
    intro j
    induction j using Fin.lastCases with
    | last =>
      have h := hD n (by omega) x hx
      have he := heq x hx
      have hv : exercise29_field f g x (u x) (Fin.last n) =
          f x - ∑ j, g j x * D j x := by simp [exercise29_field, u]
      rw [hv, show f x - ∑ j, g j x * D j x = D (n+1) x by linarith]
      simpa [u] using h
    | cast j =>
      simpa [exercise29_field, u] using hD j (by omega) x hx
  · rintro ⟨u, hu, hzero⟩
    let D : ℕ → ℝ → ℝ := fun j x =>
      if hj : j < n+1 then u x ⟨j, hj⟩ else f x - ∑ i, g i x * u x i
    have hD : ∀ j : Fin (n+1), ∀ x, D j x = u x j := by
      intro j x
      dsimp only [D]
      rw [dite_eq_left j.isLt]
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · intro x hx
      simpa [D] using hzero hx
    · intro j hj x hx
      have hv := exercise29_deriv_vector_iff.mp (hu.1 x hx) ⟨j, hj⟩
      have hfun : D j = fun t => u t ⟨j, hj⟩ := funext (hD ⟨j, hj⟩)
      rw [hfun]
      convert hv using 1
      by_cases hn : j < n
      · change D (j+1) x = Fin.lastCases _ _ (⟨j, hj⟩ : Fin (n+1))
        have he : (⟨j, hj⟩ : Fin (n+1)) = (⟨j, hn⟩ : Fin n).castSucc := rfl
        rw [he, Fin.lastCases_castSucc, hD ⟨j+1, by omega⟩ x]
        rfl
      · change D (j+1) x = Fin.lastCases _ _ (⟨j, hj⟩ : Fin (n+1))
        have he : (⟨j, hj⟩ : Fin (n+1)) = Fin.last n := Fin.ext (by simp; omega)
        rw [he, Fin.lastCases_last]
        dsimp only [D]
        rw [dite_eq_right (by omega)]
    · intro x hx
      simp only [D, lt_self_iff_false, dite_false]
      simp_rw [show ∀ j : Fin (n+1), (if hj : (j : ℕ) < n+1 then u x ⟨j, hj⟩
        else f x - ∑ i, g i x * u x i) = u x j by intro j; simp [j.isLt]]
      ring
    · intro j
      rw [hD]
      exact hu.2 j

/-- Genuine derivative towers agree with the library's iterated relative
derivative when the interval is nondegenerate. This is not a default-zero
argument: the successor step uses the supplied `HasDerivWithinAt` proof. -/
theorem exercise29_derivative_tower {n : ℕ} {a b : ℝ} (hab : a < b)
    {D : ℕ → ℝ → ℝ} {y : ℝ → ℝ}
    (hzero : EqOn (D 0) y (Icc a b))
    (hd : ∀ j < n+1, ∀ x ∈ Icc a b,
      HasDerivWithinAt (D j) (D (j+1) x) (Icc a b) x) :
    ∀ j ≤ n+1, EqOn (D j) (iteratedDerivWithin j y (Icc a b)) (Icc a b) := by
  intro j
  induction j with
  | zero => simpa using fun _ : 0 ≤ n+1 => hzero
  | succ j ih =>
    intro hj x hx
    have he := ih (by omega)
    rw [iteratedDerivWithin_succ]
    calc
      D (j+1) x = derivWithin (D j) (Icc a b) x :=
        ((hd j (by omega) x hx).derivWithin ((uniqueDiffOn_Icc hab) x hx)).symm
      _ = derivWithin (iteratedDerivWithin j y (Icc a b)) (Icc a b) x :=
        derivWithin_congr he (he hx)

/-- A canonical scalar formulation. Existence of every required derivative is
explicit, in addition to the equation and the initial values. -/
theorem exercise29_scalar_iff_iterated {n : ℕ} {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} {g : Fin (n+1) → ℝ → ℝ} {c : Fin (n+1) → ℝ} {y : ℝ → ℝ} :
    exercise29_scalar_solution a b f g c y ↔
      (∀ j < n+1, ∀ x ∈ Icc a b,
        HasDerivWithinAt (iteratedDerivWithin j y (Icc a b))
          (iteratedDerivWithin (j+1) y (Icc a b) x) (Icc a b) x) ∧
      (∀ x ∈ Icc a b, iteratedDerivWithin (n+1) y (Icc a b) x +
        ∑ j, g j x * iteratedDerivWithin j y (Icc a b) x = f x) ∧
      (∀ j : Fin (n+1), iteratedDerivWithin j y (Icc a b) a = c j) := by
  constructor
  · rintro ⟨D, hzero, hd, heq, hinit⟩
    have ht := exercise29_derivative_tower hab hzero hd
    refine ⟨?_, ?_, ?_⟩
    · intro j hj x hx
      rw [← ht (j+1) (by omega) hx]
      exact (hd j hj x hx).congr (fun s hs => (ht j (by omega) hs).symm)
        ((ht j (by omega) hx).symm)
    · intro x hx
      rw [← ht (n+1) le_rfl hx]
      convert heq x hx using 1
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [ht j (by omega) hx]
    · intro j
      rw [← ht j (by omega) (left_mem_Icc.mpr hab.le)]
      exact hinit j
  · rintro ⟨hd, heq, hinit⟩
    exact ⟨fun j => iteratedDerivWithin j y (Icc a b), by intro x hx; simp, hd, heq, hinit⟩

private theorem exercise29_norm_le_sum {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖v‖ ≤ ∑ j, |v j| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun j : Fin m => |v j|) (fun j hj => abs_nonneg (v j))
  have hn := EuclideanSpace.real_norm_sq_eq v
  simp only [sq_abs] at hs
  have hp : 0 ≤ ∑ j, |v j| := Finset.sum_nonneg (fun j hj => abs_nonneg _)
  nlinarith [norm_nonneg v]

/-- A uniform bound for the companion field follows from bounded coefficients;
it is proved, not added to the scalar equation's hypotheses. -/
theorem exercise29_field_bound {n : ℕ} {f : ℝ → ℝ} {g : Fin (n+1) → ℝ → ℝ}
    {x G : ℝ} (hG : 0 ≤ G) (hg : ∀ j, |g j x| ≤ G)
    (u v : EuclideanSpace ℝ (Fin (n+1))) :
    ‖exercise29_field f g x u - exercise29_field f g x v‖ ≤
      ((n+1 : ℝ) * (1 + (n+1 : ℝ)*G)) * ‖u-v‖ := by
  let N := ‖u-v‖
  let B := (1 + (n+1 : ℝ)*G) * N
  have hcoord : ∀ j, |u j - v j| ≤ N := by
    intro j
    exact PiLp.norm_apply_le (u-v) j
  have hNB : N ≤ B := by
    have hp : 0 ≤ (n+1 : ℝ)*G := mul_nonneg (by positivity) hG
    dsimp only [B]
    nlinarith [mul_nonneg hp (norm_nonneg (u-v))]
  have hsum : |∑ j, g j x * u j - ∑ j, g j x * v j| ≤ (n+1 : ℝ)*G*N := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j, |g j x * u j - g j x * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin (n+1), G*N := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (hg j) (hcoord j) (abs_nonneg _) hG
      _ = _ := by simp; ring
  calc
    _ ≤ ∑ j, |(exercise29_field f g x u - exercise29_field f g x v) j| :=
      exercise29_norm_le_sum _
    _ ≤ ∑ _ : Fin (n+1), B := by
      apply Finset.sum_le_sum
      intro j hj
      induction j using Fin.lastCases with
      | last =>
        have he : (exercise29_field f g x u - exercise29_field f g x v) (Fin.last n) =
            -(∑ j, g j x * u j - ∑ j, g j x * v j) := by
          simp [exercise29_field]
        rw [he, abs_neg]
        exact hsum.trans (by dsimp [B]; nlinarith [norm_nonneg (u-v)])
      | cast j =>
        simpa [exercise29_field] using (hcoord j.succ).trans hNB
    _ = _ := by simp [B]; ring

/-- Uniqueness for the finite companion system. Continuity is required only
of the given coefficients, not of any highest scalar derivative. -/
theorem exercise29_system_uniqueness {n : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    {g : Fin (n+1) → ℝ → ℝ} {c : Fin (n+1) → ℝ}
    (hg : ∀ j, ContinuousOn (g j) (Icc a b))
    {u v : ℝ → EuclideanSpace ℝ (Fin (n+1))}
    (hu : exercise29_system_solution a b f g c u)
    (hv : exercise29_system_solution a b f g c v) : EqOn u v (Icc a b) := by
  have hgc : ContinuousOn (fun x j => g j x) (Icc a b) := continuousOn_pi.mpr hg
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  have huc : ContinuousOn u (Icc a b) := fun x hx => (hu.1 x hx).continuousWithinAt
  have hvc : ContinuousOn v (Icc a b) := fun x hx => (hv.1 x hx).continuousWithinAt
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
  let T := max R S
  have hcellu : ∀ x ∈ Icc a b, u x ∈ exercise28_cell (fun _ => -T) (fun _ => T) := by
    intro x hx j
    have h := (PiLp.norm_apply_le (u x) j).trans ((hR x hx).trans (le_max_left R S))
    exact abs_le.mp h
  have hcellv : ∀ x ∈ Icc a b, v x ∈ exercise28_cell (fun _ => -T) (fun _ => T) := by
    intro x hx j
    have h := (PiLp.norm_apply_le (v x) j).trans ((hS x hx).trans (le_max_right R S))
    exact abs_le.mp h
  refine exercise28_system_uniqueness (A := (n+1 : ℝ)*(1+(n+1 : ℝ)*max G 0))
    (α := fun _ => -T) (β := fun _ => T) ?_ hcellu hcellv hu.1 hv.1 ?_
  · intro x hx w hw z hz
    apply exercise29_field_bound (le_max_right G 0)
    intro j
    exact (norm_le_pi_norm (fun i => g i x) j).trans ((hG x hx).trans (le_max_left G 0))
  · ext j
    exact (hu.2 j).trans (hv.2 j).symm

/-- R05E29: at most one scalar solution for the prescribed `n+1` initial
values. This includes order one and does not assume `ContDiff`. -/
theorem exercise29_linear_ode_uniqueness {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} {g : Fin (n+1) → ℝ → ℝ} {c : Fin (n+1) → ℝ}
    (_hf : ContinuousOn f (Icc a b)) (hg : ∀ j, ContinuousOn (g j) (Icc a b))
    {y z : ℝ → ℝ}
    (hy : exercise29_scalar_solution a b f g c y)
    (hz : exercise29_scalar_solution a b f g c z) : EqOn y z (Icc a b) := by
  obtain ⟨u, hu, huy⟩ := (exercise29_system_reduction hab).mp hy
  obtain ⟨v, hv, hvz⟩ := (exercise29_system_reduction hab).mp hz
  have he := exercise29_system_uniqueness hg hu hv
  intro x hx
  rw [← huy hx, ← hvz hx]
  exact congrArg (fun w : EuclideanSpace ℝ (Fin (n+1)) => w 0) (he hx)

end Rudin.Chapter05
