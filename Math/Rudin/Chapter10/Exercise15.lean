module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Basic.Real.Basic

/-! # Chapter 10, Exercise 15
Forms are sections of the homogeneous exterior powers of the cotangent space.
Their wedge is multiplication in the actual exterior algebra, not a sign-only model.
The identity is pointwise and needs no regularity assumption on the coefficients.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise15

open ExteriorAlgebra

/-- A differential form with values in the homogeneous exterior power of covectors. -/
abbrev Form (X V : Type*) [AddCommGroup V] [Module ℝ V] (k : ℕ) :=
  X → ↥(exteriorPower ℝ k (Module.Dual ℝ V))

/-- The wedge of forms, viewed in the ambient exterior algebra. -/
def wedge {X V : Type*} [AddCommGroup V] [Module ℝ V] {k m : ℕ}
    (ω : Form X V k) (η : Form X V m) : X → ExteriorAlgebra ℝ (Module.Dual ℝ V) :=
  fun x => (ω x).val * (η x).val

/-- Graded commutation for all homogeneous elements, not just simple wedges. -/
theorem homogeneous_commutation {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k m : ℕ} (a : ↥(exteriorPower ℝ k V)) (b : ↥(exteriorPower ℝ m V)) :
    a.val * b.val = ((-1 : ℤˣ) ^ (k * m)) • (b.val * a.val) := by
  have ha := a.property
  have hb := b.property
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree ℝ _))] at ha hb
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y = ((-1 : ℤˣ) ^ (k * m)) • (y * x))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
  · rintro x y ⟨u, rfl⟩ ⟨v, rfl⟩
    simpa only [Nat.mul_comm] using ιMulti_mul_ιMulti_anticomm ℝ u v
  all_goals simp +contextual [add_mul, mul_add]
  all_goals intros; apply smul_comm

/-- The source identity on any common domain (in particular, any open domain). -/
theorem graded_commutation {X V : Type*} [AddCommGroup V] [Module ℝ V]
    {k m : ℕ} (ω : Form X V k) (η : Form X V m) :
    wedge ω η = fun x => ((-1 : ℤˣ) ^ (k * m)) • wedge η ω x := by
  funext x
  exact homogeneous_commutation (ω x) (η x)

/-- Multiplication has the required total degree. -/
theorem wedge_mem {X V : Type*} [AddCommGroup V] [Module ℝ V]
    {k m : ℕ} (ω : Form X V k) (η : Form X V m) (x : X) :
    wedge ω η x ∈ exteriorPower ℝ (k + m) (Module.Dual ℝ V) := by
  rw [exteriorPower, pow_add]
  exact Submodule.mul_mem_mul (ω x).property (η x).property

/-- The same identity with the literal real scalar from the source. -/
theorem graded_commutation_real {X V : Type*} [AddCommGroup V] [Module ℝ V]
    {k m : ℕ} (ω : Form X V k) (η : Form X V m) :
    wedge ω η = fun x => ((-1 : ℝ) ^ (k * m)) • wedge η ω x := by
  funext x
  rw [congrFun (graded_commutation ω η) x, Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ]
  simp

/-- An overlap of coordinate indices makes the product vanish. -/
theorem wedge_repeated_index {V : Type*} [AddCommGroup V] [Module ℝ V]
    {k m : ℕ} (u : Fin k → V) (v : Fin m → V)
    (i : Fin k) (j : Fin m) (h : u i = v j) :
    ιMulti ℝ k u * ιMulti ℝ m v = 0 := by
  rw [ιMulti_mul_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq (i := Fin.castAdd m i) (j := Fin.natAdd k j)
  · simpa using h
  · apply ne_of_lt
    apply lt_of_lt_of_le (b := k) <;> simp

end Rudin.Chapter10.Exercise15
