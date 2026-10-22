module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Tactic

/-!
Restricted forms prototype. It connects Mathlib's exterior derivative to
integration and oriented boundaries for segments and coordinate rectangles.
It does not define smooth chains or a general Stokes integral.
-/

@[expose] public section

namespace Rudin.Support.FormsPrototype

open ContinuousAlternatingMap Set MeasureTheory

/-- A real function represented as an unbundled differential 0-form. -/
noncomputable def zeroForm (f : ℝ → ℝ) (x : ℝ) : ℝ [⋀^Fin 0]→L[ℝ] ℝ :=
  constOfIsEmpty ℝ ℝ (Fin 0) (f x)

/-- Evaluation of a 1-form on the positively oriented unit tangent. -/
noncomputable def unitCoefficient (ω : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ) (x : ℝ) : ℝ :=
  ω x (fun _ ↦ 1)

/-- The oriented segment integral of a 1-form in this coordinate. -/
noncomputable def segmentIntegral (ω : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, unitCoefficient ω x

/-- The boundary of the oriented segment is `[b] - [a]`. -/
def boundaryValue (f : ℝ → ℝ) (a b : ℝ) : ℝ := f b - f a

/-- The exterior derivative agrees with the ordinary derivative on a 0-form. -/
theorem unitCoefficient_extDeriv_zeroForm (f : ℝ → ℝ) (x : ℝ) :
    unitCoefficient (extDeriv (zeroForm f)) x = deriv f x := by
  change (extDeriv (fun y ↦ constOfIsEmpty ℝ ℝ (Fin 0) (f y)) x) (fun _ ↦ 1) = _
  rw [extDeriv_constOfIsEmpty]
  rfl

/-- A nonconstant computation in the actual exterior derivative API. -/
theorem exterior_square (x : ℝ) :
    unitCoefficient (extDeriv (zeroForm (fun y ↦ y ^ 2))) x = 2 * x := by
  rw [unitCoefficient_extDeriv_zeroForm, (hasDerivAt_pow 2 x).deriv]
  norm_num

/-- A genuine integration/boundary identity for 0-forms on an oriented segment.
The hypotheses are differentiability and integrability, not the desired identity. -/
theorem segment_stokes (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x)
    (hi : IntervalIntegrable (deriv f) volume a b) :
    segmentIntegral (extDeriv (zeroForm f)) a b = boundaryValue f a b := by
  simp only [segmentIntegral, unitCoefficient_extDeriv_zeroForm, boundaryValue]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ (hf x hx).hasDerivAt) hi

/-- Orientation reversal changes the sign of the segment integral. -/
theorem segmentIntegral_reverse (ω : ℝ → ℝ [⋀^Fin 1]→L[ℝ] ℝ) (a b : ℝ) :
    segmentIntegral ω b a = -segmentIntegral ω a b :=
  intervalIntegral.integral_symm a b

/-- A concrete nonzero boundary identity, with no integrability hypothesis left to the caller. -/
theorem square_segment (a b : ℝ) :
    segmentIntegral (extDeriv (zeroForm (fun y ↦ y ^ 2))) a b = b ^ 2 - a ^ 2 := by
  apply segment_stokes
  · intro x _
    exact (hasDerivAt_pow 2 x).differentiableAt
  · have heq : deriv (fun y : ℝ ↦ y ^ 2) = fun x ↦ 2 * x := by
      funext x
      rw [(hasDerivAt_pow 2 x).deriv]
      norm_num
    rw [heq]
    exact (continuous_const.mul continuous_id).intervalIntegrable a b

/-- The ordered coordinate frame fixes the positive orientation of the plane. -/
def planeFrame : Fin 2 → ℝ × ℝ := ![(1, 0), (0, 1)]

/-- Coordinate coefficients of an unbundled plane 1-form. -/
noncomputable def planeP (ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (z : ℝ × ℝ) :=
  ω z (fun _ ↦ (1, 0))

noncomputable def planeQ (ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (z : ℝ × ℝ) :=
  ω z (fun _ ↦ (0, 1))

/-- The exterior derivative is the usual coordinate curl. -/
theorem exterior_plane {ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ} {z : ℝ × ℝ}
    (hω : DifferentiableAt ℝ ω z) :
    extDeriv ω z planeFrame =
      fderiv ℝ (planeQ ω) z (1, 0) - fderiv ℝ (planeP ω) z (0, 1) := by
  have h0 : (0 : Fin 2).removeNth planeFrame = fun _ ↦ (0, 1) := by
    funext i
    fin_cases i
    rfl
  have h1 : (1 : Fin 2).removeNth planeFrame = fun _ ↦ (1, 0) := by
    funext i
    fin_cases i
    rfl
  rw [extDeriv_apply hω, Fin.sum_univ_two, h0, h1]
  change (1 : ℤ) • fderiv ℝ (planeQ ω) z (1, 0) +
    (-1 : ℤ) • fderiv ℝ (planeP ω) z (0, 1) = _
  simp [sub_eq_add_neg]

/-- Four oriented edge integrals: bottom, right, reversed top, reversed left. -/
noncomputable def rectangleBoundary
    (ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (a b : ℝ × ℝ) : ℝ :=
  (∫ x in a.1..b.1, planeP ω (x, a.2)) +
  (∫ y in a.2..b.2, planeQ ω (b.1, y)) -
  (∫ x in a.1..b.1, planeP ω (x, b.2)) -
  (∫ y in a.2..b.2, planeQ ω (a.1, y))

/-- Stokes' identity for an actual differential 1-form on a coordinate rectangle.
This uses Bochner area integration and interval edge integration. No general
chain integral, or comparison with Rudin's surface integral, is asserted. -/
theorem rectangle_stokes
    (ω : (ℝ × ℝ) → (ℝ × ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (a b : ℝ × ℝ) (hab : a ≤ b)
    (hω : Differentiable ℝ ω)
    (hi : IntegrableOn (fun z ↦ extDeriv ω z planeFrame) (Icc a b)) :
    (∫ z in Icc a b, extDeriv ω z planeFrame) = rectangleBoundary ω a b := by
  have hP : Differentiable ℝ (planeP ω) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ (fun _ : Fin 1 ↦ (1, 0))).differentiable.comp hω
  have hQ : Differentiable ℝ (planeQ ω) :=
    (ContinuousAlternatingMap.apply ℝ (ℝ × ℝ) ℝ (fun _ : Fin 1 ↦ (0, 1))).differentiable.comp hω
  have heq : (fun z ↦ fderiv ℝ (planeQ ω) z (1, 0) +
      (-fderiv ℝ (planeP ω) z) (0, 1)) = fun z ↦ extDeriv ω z planeFrame := by
    funext z
    simp [exterior_plane (hω z), sub_eq_add_neg]
  have hdiv := MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (planeQ ω) (-planeP ω) (fderiv ℝ (planeQ ω)) (fun z ↦ -fderiv ℝ (planeP ω) z)
    a b hab hQ.continuous.continuousOn hP.neg.continuous.continuousOn
    (fun z _ ↦ (hQ z).hasFDerivAt) (fun z _ ↦ (hP z).hasFDerivAt.neg)
    (by simpa only [heq] using hi)
  simp only [heq, Pi.neg_apply, intervalIntegral.integral_neg] at hdiv
  unfold rectangleBoundary
  linear_combination hdiv

#print axioms exterior_square
#print axioms segment_stokes
#print axioms square_segment
#print axioms exterior_plane
#print axioms rectangle_stokes

end Rudin.Support.FormsPrototype
