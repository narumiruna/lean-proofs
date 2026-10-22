module

public import Math.Rudin.Chapter06.Exercise04
public import Math.Rudin.Support.StieltjesComposition
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# R06E05: squares and cubes

Source: Rudin, Third Edition, Exercise 6.5, book page 138 (PDF page 147).
The rational/irrational sign function has constant square but no Riemann
integral on any nondegenerate interval. In contrast, continuous signed
cube-root composition recovers `f` from `f ^ 3`. All integral predicates
use the raw Darboux or tagged sums. No measure integral is used.
-/

@[expose] public section

namespace Rudin.Chapter06

open Set Rudin.Support.StieltjesPrototype Rudin.Support.StieltjesEquivalence
open Rudin.Support.StieltjesRefinement
open Rudin.Support.StieltjesIntegralLaws Rudin.Support.StieltjesComposition

/-- The source counterexample: one on rationals and minus one on irrationals. -/
noncomputable def rationalSign (x : ℝ) : ℝ := 2 * rationalIndicator x - 1

@[simp] theorem rationalSign_rat (q : ℚ) : rationalSign q = 1 := by
  norm_num [rationalSign]

theorem rationalSign_irrational {x : ℝ} (hx : Irrational x) : rationalSign x = -1 := by
  simp [rationalSign, rationalIndicator_irrational hx]

/-- In particular the counterexample is bounded, with absolute value one. -/
theorem rationalSign_abs (x : ℝ) : |rationalSign x| = 1 := by
  classical
  unfold rationalSign rationalIndicator
  split_ifs <;> norm_num

@[simp] theorem rationalSign_square (x : ℝ) : rationalSign x ^ 2 = 1 := by
  classical
  unfold rationalSign rationalIndicator
  split_ifs <;> norm_num

/-- The counterexample has integrable constant square, even on a singleton. -/
theorem exercise05_square_integral {a b : ℝ} (hab : a ≤ b) :
    HasDarbouxRSIntegral (fun x ↦ rationalSign x ^ 2) id a b (b - a) := by
  have hc := hasDarbouxRSIntegral_of_hasRSIntegral hab
    (hasRSIntegral_constant hab (monotone_id.monotoneOn _) 1)
  simpa using hc

/-- Integrability of the sign function would imply integrability of the indicator. -/
theorem exercise05_sign_nonintegrable {a b : ℝ} (hab : a < b) :
    ¬ ∃ v : ℝ, HasDarbouxRSIntegral rationalSign id a b v := by
  rintro ⟨v, hv⟩
  have hc := hasDarbouxRSIntegral_of_hasRSIntegral hab.le
    (hasRSIntegral_constant hab.le (monotone_id.monotoneOn _) 1)
  have hh := hasDarbouxRSIntegral_mul hab.le
    (hasDarbouxRSIntegral_add hab.le hv hc) (1 / 2)
  apply exercise04 hab
  refine ⟨_, hasDarbouxRSIntegral_congr hab.le hh ?_⟩
  intro x _
  dsimp [rationalSign]
  ring

/-- R06E05, square: the bounded ±1 function disproves the implication on every `a < b`. -/
theorem exercise05_square {a b : ℝ} (hab : a < b) :
    (∀ x ∈ Icc a b, |rationalSign x| ≤ 1) ∧
    HasDarbouxRSIntegral (fun x ↦ rationalSign x ^ 2) id a b (b - a) ∧
    ¬ (∃ v : ℝ, HasDarbouxRSIntegral rationalSign id a b v) :=
  ⟨fun x _ ↦ (rationalSign_abs x).le, exercise05_square_integral hab.le,
    exercise05_sign_nonintegrable hab⟩

/-- A real signed cube root. Both real-power bases are nonnegative.
This definition never uses real fractional powers of a negative base. -/
noncomputable def signedCubeRoot (y : ℝ) : ℝ :=
  (max y 0) ^ (1 / 3 : ℝ) - (max (-y) 0) ^ (1 / 3 : ℝ)

/-- The signed cube root is continuous, including at zero. -/
theorem continuous_signedCubeRoot : Continuous signedCubeRoot := by
  exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
    (continuous_id.max continuous_const)).sub
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 3)).comp
      (continuous_id.neg.max continuous_const))

/-- On nonnegative inputs the negative part vanishes. -/
theorem signedCubeRoot_nonneg {y : ℝ} (hy : 0 ≤ y) :
    signedCubeRoot y = y ^ (1 / 3 : ℝ) := by
  simp [signedCubeRoot, max_eq_left hy, max_eq_right (neg_nonpos.mpr hy)]

/-- On nonpositive inputs the positive part vanishes. -/
theorem signedCubeRoot_nonpos {y : ℝ} (hy : y ≤ 0) :
    signedCubeRoot y = -((-y) ^ (1 / 3 : ℝ)) := by
  simp [signedCubeRoot, max_eq_right hy, max_eq_left (neg_nonneg.mpr hy)]

/-- The root recovers every real number from its cube, for either sign and zero. -/
theorem signedCubeRoot_cube (x : ℝ) : signedCubeRoot (x ^ 3) = x := by
  by_cases hx : 0 ≤ x
  · rw [signedCubeRoot_nonneg (pow_nonneg hx _)]
    simpa using Real.pow_rpow_inv_natCast hx (by decide : (3 : ℕ) ≠ 0)
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    have hc : x ^ 3 ≤ 0 := by nlinarith [sq_nonneg x]
    rw [signedCubeRoot_nonpos hc]
    have heq : -(x ^ 3) = (-x) ^ 3 := by ring
    rw [heq]
    have hr := Real.pow_rpow_inv_natCast (neg_nonneg.mpr hx') (by decide : (3 : ℕ) ≠ 0)
    have hr' : ((-x) ^ 3) ^ (1 / 3 : ℝ) = -x := by simpa using hr
    rw [hr']
    ring

/-- Cubing the signed root gives its input, also for negative inputs. -/
theorem cube_signedCubeRoot (y : ℝ) : signedCubeRoot y ^ 3 = y := by
  by_cases hy : 0 ≤ y
  · rw [signedCubeRoot_nonneg hy]
    simpa using Real.rpow_inv_natCast_pow hy (by decide : (3 : ℕ) ≠ 0)
  · have hy' : y ≤ 0 := (lt_of_not_ge hy).le
    rw [signedCubeRoot_nonpos hy', neg_pow]
    have hr := Real.rpow_inv_natCast_pow (neg_nonneg.mpr hy') (by decide : (3 : ℕ) ≠ 0)
    have hr' : ((-y) ^ (1 / 3 : ℝ)) ^ 3 = -y := by simpa using hr
    rw [hr']
    norm_num

/-- Continuous signed-root composition proves the cube implication for raw
Stieltjes integrals, without assuming `f` continuous or nonnegative. -/
theorem exercise05_cube_stieltjes {a b v : ℝ} (hab : a ≤ b) {f α : ℝ → ℝ}
    (hf : HasDarbouxRSIntegral (fun x ↦ f x ^ 3) α a b v) :
    ∃ w : ℝ, HasDarbouxRSIntegral f α a b w := by
  obtain ⟨M, hM⟩ := hf.2.1
  obtain ⟨w, hw⟩ := exists_comp_continuous hab hf
    (fun x hx ↦ abs_le.mp (hM x hx)) continuous_signedCubeRoot.continuousOn
  exact ⟨w, hasDarbouxRSIntegral_congr hab hw
    (fun x _ ↦ signedCubeRoot_cube (f x))⟩

/-- R06E05, cube: integrability of the cube implies Riemann integrability of `f`.
The theorem includes singleton intervals; boundedness of the cube already
suffices, so the source's separate boundedness assumption on `f` is unnecessary. -/
theorem exercise05_cube {a b v : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : HasDarbouxRSIntegral (fun x ↦ f x ^ 3) id a b v) :
    ∃ w : ℝ, HasDarbouxRSIntegral f id a b w :=
  exercise05_cube_stieltjes hab hf

/-- The same cube implication for the equivalent raw tagged integral. -/
theorem exercise05_cube_tagged {a b v : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : HasRSIntegral (fun x ↦ f x ^ 3) id a b v) :
    ∃ w : ℝ, HasRSIntegral f id a b w := by
  obtain ⟨w, hw⟩ := exercise05_cube hab (hasDarbouxRSIntegral_of_hasRSIntegral hab hf)
  exact ⟨w, hasRSIntegral_of_hasDarbouxRSIntegral hab hw⟩

end Rudin.Chapter06
