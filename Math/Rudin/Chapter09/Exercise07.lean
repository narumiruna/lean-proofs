module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

/-!
# R09E07: bounded partial derivatives imply continuity

Source: Rudin, Third Edition, Exercise 9.7, book page 239 (PDF page 248).
The proof follows the coordinate-by-coordinate estimate of Theorem 9.21.
The auxiliary sup-norm coordinate calculation is transferred to Euclidean space
by its continuous coordinate equivalence. No continuity of partials is assumed.
-/

@[expose] public section
namespace Rudin.Chapter09

open Set Metric

/-- The finite coordinate telescoping estimate. -/
theorem coordinate_telescope {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {a : Fin n → ℝ} {r C : ℝ}
    (hstep : ∀ x ∈ ball a r, ∀ i t, Function.update x i t ∈ ball a r →
      dist (f x) (f (Function.update x i t)) ≤ C * dist (x i) t)
    (s : Finset (Fin n)) :
    ∀ x ∈ ball a r, ∀ y ∈ ball a r, (∀ i ∉ s, x i = y i) →
      dist (f x) (f y) ≤ ∑ i ∈ s, C * dist (x i) (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro x hx y hy hxy
      have : x = y := funext fun i => hxy i (by simp)
      simp [this]
  | @insert i s hi ih =>
      intro x hx y hy hxy
      let z := Function.update x i (y i)
      have hr : 0 < r := lt_of_le_of_lt dist_nonneg hx
      have hz : z ∈ ball a r := by
        apply (dist_pi_lt_iff hr).mpr
        intro j
        by_cases hj : j = i
        · subst j
          simpa [z] using (dist_pi_lt_iff hr).mp hy i
        · simpa [z, Function.update_of_ne hj] using (dist_pi_lt_iff hr).mp hx j
      have hzy : ∀ j ∉ s, z j = y j := by
        intro j hj
        by_cases hji : j = i
        · subst j; simp [z]
        · simpa [z, Function.update_of_ne hji] using hxy j (by simp [hji, hj])
      calc
        dist (f x) (f y) ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
        _ ≤ C * dist (x i) (y i) + ∑ j ∈ s, C * dist (z j) (y j) :=
          add_le_add (hstep x hx i (y i) hz) (ih z hz y hy hzy)
        _ = ∑ j ∈ insert i s, C * dist (x j) (y j) := by
          rw [Finset.sum_insert hi]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := fun h => hi (h ▸ hj)
          simp [z, Function.update_of_ne hji]

/-- Bounded existing coordinate derivatives imply continuity in coordinates. -/
theorem continuousOn_of_bounded_coordinate_derivatives {n : ℕ}
    {U : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {p : (Fin n → ℝ) → Fin n → ℝ} {C : ℝ}
    (hU : IsOpen U) (hC : 0 ≤ C)
    (hp : ∀ x ∈ U, ∀ i, HasDerivAt (fun t => f (Function.update x i t)) (p x i) (x i))
    (hbound : ∀ x ∈ U, ∀ i, ‖p x i‖ ≤ C) : ContinuousOn f U := by
  intro a ha
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  have hstep : ∀ x ∈ ball a r, ∀ i t, Function.update x i t ∈ ball a r →
      dist (f x) (f (Function.update x i t)) ≤ C * dist (x i) t := by
    intro x hx i t ht
    let J := Ioo (a i - r) (a i + r)
    have hmem : ∀ s, s ∈ J ↔ Function.update x i s ∈ ball a r := by
      intro s
      rw [mem_ball, dist_pi_lt_iff hr]
      constructor
      · intro hs j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, Real.dist_eq]
          exact abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
        · simpa [Function.update_of_ne hj] using (dist_pi_lt_iff hr).mp hx j
      · intro hs
        have hs' := hs i
        simp only [Function.update_self, Real.dist_eq, abs_lt] at hs'
        exact ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
    have hd : ∀ s ∈ J, HasDerivAt (fun t => f (Function.update x i t))
        (p (Function.update x i s) i) s := by
      intro s hs
      simpa [Function.update_idem] using hp _ (hball ((hmem s).mp hs)) i
    have h := (convex_Ioo (a i - r) (a i + r)).norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hd s hs).differentiableAt)
      (fun s hs => by rw [(hd s hs).deriv]; exact hbound _ (hball ((hmem s).mp hs)) i)
      ((hmem (x i)).mpr (by simpa using hx)) ((hmem t).mpr ht)
    simpa only [← dist_eq_norm, Function.update_eq_self, dist_comm] using h
  have hdist : ∀ x ∈ ball a r, dist (f x) (f a) ≤ (n * C) * dist x a := by
    intro x hx
    calc
      dist (f x) (f a) ≤ ∑ i : Fin n, C * dist (x i) (a i) :=
        coordinate_telescope hstep Finset.univ x hx a (mem_ball_self hr) (by simp)
      _ ≤ ∑ _i : Fin n, C * dist x a :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (dist_le_pi_dist x a i) hC
      _ = (n * C) * dist x a := by simp; ring
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min r (ε / (n * C + 1)), lt_min hr (div_pos hε (by positivity)), ?_⟩
  intro x hx
  have hxball : x ∈ ball a r := lt_of_lt_of_le hx (min_le_left _ _)
  have hxε : dist x a < ε / (n * C + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have hmul := (lt_div_iff₀ (show 0 < (n : ℝ) * C + 1 by positivity)).mp hxε
  have hnonneg : 0 ≤ dist x a := dist_nonneg
  exact (hdist x hxball).trans_lt (by nlinarith)

/-- All coordinate partial derivatives exist and are bounded on the open
Euclidean domain. Therefore the function is continuous there. -/
theorem exercise07 {n : ℕ} {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hE : IsOpen E)
    (hp : ∀ x ∈ E, ∀ i, HasDerivAt
      (fun t => f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i t))) (p x i) (x i))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ E, ∀ i, ‖p x i‖ ≤ C) :
    ContinuousOn f E := by
  obtain ⟨C, hC, hb⟩ := hbound
  have h := continuousOn_of_bounded_coordinate_derivatives
    (f := fun x => f (WithLp.toLp 2 x)) (p := fun x => p (WithLp.toLp 2 x))
    (hE.preimage (PiLp.continuous_toLp 2 _)) hC
    (fun x hx i => hp _ hx i) (fun x hx i => hb _ hx i)
  exact h.comp (PiLp.continuous_ofLp 2 _).continuousOn (fun x hx => hx)

/-- Source formulation with a separate bound for each partial derivative. -/
theorem exercise07_of_coordinate_bounds {n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {p : EuclideanSpace ℝ (Fin n) → Fin n → ℝ}
    (hE : IsOpen E)
    (hp : ∀ x ∈ E, ∀ i, HasDerivAt
      (fun t => f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) i t))) (p x i) (x i))
    (hbound : ∀ i, ∃ C : ℝ, ∀ x ∈ E, ‖p x i‖ ≤ C) : ContinuousOn f E := by
  classical
  choose C hC using hbound
  apply exercise07 hE hp
  refine ⟨∑ i, |C i|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro x hx i
  exact (hC i x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)))

end Rudin.Chapter09
