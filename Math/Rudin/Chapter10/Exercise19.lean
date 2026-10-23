module

public import Math.Rudin.Chapter10.Exercise18
public import Math.Rudin.Support.OrientedChainChecks

/-!
# Exercise 10.19

Source: book page 292 (PDF 301). The source indices 1,2,3 are represented
by `Fin 3` indices 0,1,2. The exponent is therefore `i.val + 1`.
`B` is an affine map on the entire coordinate plane. The realization
comparison below proves that mapping vertices really composes each affine
triangle with this map. The final equality is in fixed degree two of the
orientation quotient, not an equality of sets or integration functionals.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise19
open Rudin.Support.OrientedChains
open Rudin.Chapter10.Exercise18

/-- The source's `β_{ri} = B_{ri}(J²)`, as an actual oriented affine 2-chain. -/
def β (r : ℝ) (i : Fin 3) : Chain Space 2 := gradedMap (B r i) 3 Exercise17.J2

/-- The literal coordinate insertion formulas of the book. -/
theorem insertion_formulas (r : ℝ) (u : Exercise17.Plane) :
    B r 0 u = ![r, u 0, u 1] ∧
    B r 1 u = ![u 0, r, u 1] ∧
    B r 2 u = ![u 0, u 1, r] := by
  constructor
  · ext j; fin_cases j <;> rfl
  constructor
  · ext j; fin_cases j <;> rfl
  · ext j; fin_cases j <;> rfl

/-- Affine pushforward acts on the actual maps, not only their vertices. -/
theorem insertion_realize (r : ℝ) (i : Fin 3) (v : Fin 3 → Exercise17.Plane)
    (w : Parameters 3) : B r i (realize v w) = realize (B r i ∘ v) w :=
  realize_affine (B r i) v w

theorem β_value (r : ℝ) (i : Fin 3) :
    (β r i).val = square (B r i Exercise17.q0) (B r i Exercise17.q1)
      (B r i Exercise17.q2) (B r i Exercise17.q3) := by
  change mapVertices (B r i) Exercise17.J2.val = _
  rw [Exercise17.J2_value]
  exact Rudin.Support.OrientedChainChecks.map_square _ _ _ _ _

/-- These are the same two realized triangles used in the surface-coverage
proof, with the source's second-triangle minus sign. -/
theorem β_triangles (r : ℝ) (i : Fin 3) :
    β r i = ofVertices (B r i ∘ Exercise17.vertices₁) -
      ofVertices (B r i ∘ Exercise17.vertices₂) := by
  apply Subtype.ext
  simp [β, gradedMap, Exercise17.J2, Exercise17.τ₁, Exercise17.τ₂,
    ofVertices, sub_eq_add_neg]

/-- The exact alternating coordinate-insertion formula, in fixed degree two. -/
theorem cube_face_formula :
    chainBoundary 2 J3 = ∑ i : Fin 3, (-1 : ℤ) ^ (i.val + 1) • (β 0 i - β 1 i) := by
  apply Subtype.ext
  change boundary J3.val = _
  rw [J3_value]
  have he0 : e 0 = Rudin.Support.OrientedChainChecks.e1 := by
    ext j; fin_cases j <;> simp [e, Rudin.Support.OrientedChainChecks.e1]
  have he1 : e 1 = Rudin.Support.OrientedChainChecks.e2 := by
    ext j; fin_cases j <;> simp [e, Rudin.Support.OrientedChainChecks.e2]
  have he2 : e 2 = Rudin.Support.OrientedChainChecks.e3 := by
    ext j; fin_cases j <;> simp [e, Rudin.Support.OrientedChainChecks.e3]
  rw [he0, he1, he2, Rudin.Support.OrientedChainChecks.coordinate_face_signs]
  have hB0 (r : ℝ) : (B r 0 : Exercise17.Plane → Space) =
      Rudin.Support.OrientedChainChecks.insert1 r := by
    funext u; exact (insertion_formulas r u).1
  have hB1 (r : ℝ) : (B r 1 : Exercise17.Plane → Space) =
      Rudin.Support.OrientedChainChecks.insert2 r := by
    funext u; exact (insertion_formulas r u).2.1
  have hB2 (r : ℝ) : (B r 2 : Exercise17.Plane → Space) =
      Rudin.Support.OrientedChainChecks.insert3 r := by
    funext u; exact (insertion_formulas r u).2.2
  simp [Fin.sum_univ_succ, β, gradedMap, Exercise17.J2_value,
    hB0, hB1, hB2, Exercise17.q0, Exercise17.q1, Exercise17.q2, Exercise17.q3,
    Rudin.Support.OrientedChainChecks.q0, Rudin.Support.OrientedChainChecks.q1,
    Rudin.Support.OrientedChainChecks.q2, Rudin.Support.OrientedChainChecks.q3]
  abel

alias face_chain_value := β_value
alias face_triangles := β_triangles

end Rudin.Chapter10.Exercise19
