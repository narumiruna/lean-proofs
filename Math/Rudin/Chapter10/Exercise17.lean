module

public import Math.Rudin.Chapter10.Exercise16
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exercise 10.17

Source: book page 291 (PDF 300), with Definitions 10.26–10.31.
The second simplex has coefficient -1. Its geometric range is unchanged
by this sign. Ranges below are ranges of the actual barycentric affine maps,
including all boundary points. Interiors use the usual real coordinate
space topology; no metric or norm is used to define these regions.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise17
open Rudin.Support.OrientedChains

abbrev Plane := Fin 2 → ℝ

def q0 : Plane := 0
def q1 : Plane := ![1, 0]
def q2 : Plane := ![1, 1]
def q3 : Plane := ![0, 1]
def vertices₁ : Fin 3 → Plane := ![q0, q1, q2]
def vertices₂ : Fin 3 → Plane := ![q0, q3, q2]
def triangle₁ : Parameters 3 → Plane := realize vertices₁
def triangle₂ : Parameters 3 → Plane := realize vertices₂

def τ₁ : Chain Plane 2 := ofVertices vertices₁
def τ₂ : Chain Plane 2 := -ofVertices vertices₂
def J2 : Chain Plane 2 := τ₁ + τ₂

theorem range₁ (x : Plane) : x ∈ Set.range triangle₁ ↔
    0 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 ≤ 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h0 := w.property.1 0
    have h1 := w.property.1 1
    have h2 := w.property.1 2
    have hs := w.property.2
    simp [Fin.sum_univ_succ] at hs
    simp [triangle₁, realize, vertices₁, q0, q1, q2, Fin.sum_univ_succ]
    constructor; linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨![1 - x 0, x 0 - x 1, x 1], ?_⟩, ?_⟩
    · constructor
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]
    · ext i; fin_cases i <;>
        simp [triangle₁, realize, vertices₁, q0, q1, q2, Fin.sum_univ_succ]

theorem range₂ (x : Plane) : x ∈ Set.range triangle₂ ↔
    0 ≤ x 0 ∧ x 0 ≤ x 1 ∧ x 1 ≤ 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h0 := w.property.1 0
    have h1 := w.property.1 1
    have h2 := w.property.1 2
    have hs := w.property.2
    simp [Fin.sum_univ_succ] at hs
    simp [triangle₂, realize, vertices₂, q0, q3, q2, Fin.sum_univ_succ]
    constructor; linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨![1 - x 1, x 1 - x 0, x 0], ?_⟩, ?_⟩
    · constructor
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]
    · ext i; fin_cases i <;>
        simp [triangle₂, realize, vertices₂, q0, q3, q2, Fin.sum_univ_succ]

/-- The closed square, including its diagonal and four edges. -/
theorem square_coverage (x : Plane) :
    x ∈ Set.range triangle₁ ∪ Set.range triangle₂ ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  rw [Set.mem_union, range₁, range₂]
  constructor
  · rintro (⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) i <;>
      fin_cases i <;> constructor <;> dsimp at * <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    rcases le_total (x 0) (x 1) with h | h
    · exact Or.inr ⟨h0.1, h, h1.2⟩
    · exact Or.inl ⟨h1.1, h, h0.2⟩

/-- Interior points satisfy strict coordinate inequalities. The proof uses
an open surjective linear coordinate difference, not an assumed description
of the interior. -/
theorem interior_coordinate_lt {n : ℕ} {S : Set (Fin n → ℝ)}
    {i j : Fin n} (hij : i ≠ j) (hS : ∀ x ∈ S, x i ≤ x j)
    {x : Fin n → ℝ} (hx : x ∈ interior S) : x i < x j := by
  let f : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)
  have hf : Function.Surjective f := by
    intro t
    refine ⟨Pi.single i t, ?_⟩
    simp [f, Ne.symm hij]
  have hsub : S ⊆ f ⁻¹' Set.Iic 0 := by
    intro y hy
    change y i - y j ≤ 0
    exact sub_nonpos.mpr (hS y hy)
  have hm := interior_mono hsub hx
  rw [f.interior_preimage hf, interior_Iic] at hm
  change x i - x j < 0 at hm
  linarith

theorem disjoint_interiors :
    Disjoint (interior (Set.range triangle₁)) (interior (Set.range triangle₂)) := by
  apply Set.disjoint_left.mpr
  intro x h1 h2
  have a := interior_coordinate_lt (i := (1 : Fin 2)) (j := 0) (by decide)
    (fun y hy => (range₁ y).mp hy |>.2.1) h1
  have b := interior_coordinate_lt (i := (0 : Fin 2)) (j := 1) (by decide)
    (fun y hy => (range₂ y).mp hy |>.2.1) h2
  linarith

/-- Columns are the vertex differences in formula (78). -/
def linearMatrix (v : Fin 3 → Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (v j.succ - v 0) i

theorem positive_orientations :
    Matrix.det (linearMatrix vertices₁) = 1 ∧
    (-1 : ℝ) * Matrix.det (linearMatrix vertices₂) = 1 := by
  norm_num [linearMatrix, Matrix.det_fin_two, vertices₁, vertices₂, q0, q1, q2, q3]

theorem J2_value : J2.val = square q0 q1 q2 q3 := by
  simp [J2, τ₁, τ₂, ofVertices, vertices₁, vertices₂, square, List.ofFn_succ, sub_eq_add_neg]

theorem square_boundary :
    (chainBoundary 1 J2).val =
      simplex [q0, q1] + simplex [q1, q2] + simplex [q2, q3] + simplex [q3, q0] := by
  change boundary J2.val = _
  rw [J2_value, boundary_square]

theorem difference_boundary :
    (chainBoundary 1 (τ₁ - τ₂)).val =
      simplex [q0, q1] + simplex [q1, q2] + simplex [q0, q3] + simplex [q3, q2] -
        (2 : ℤ) • simplex [q0, q2] := by
  change boundary (τ₁.val - τ₂.val) = _
  simp only [τ₁, τ₂, ofVertices, vertices₁, vertices₂, List.ofFn_succ]
  simpa using boundary_square_difference q0 q1 q2 q3

alias lower_range := range₁
alias upper_range := range₂

end Rudin.Chapter10.Exercise17
