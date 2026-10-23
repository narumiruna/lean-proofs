module

public import Math.Rudin.Chapter10.Exercise17
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exercise 10.18

Source: book pages 291–292 (PDF 300–301). The six coordinate orders are
012, 021, 102, 120, 201, 210. Their signs are +, -, -, +, +, -.
The maps use the vertices of Definition 10.26, not inequality regions as
substitutes for simplexes. The inverse barycentric weights prove coverage
also when coordinates coincide or are 0 or 1.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise18
open Rudin.Support.OrientedChains

abbrev Space := Fin 3 → ℝ

def e (i : Fin 3) : Space := Pi.single i 1

def order : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

def sign : Fin 6 → ℤ := ![1,-1,-1,1,1,-1]

def vertices (p : Fin 6) : Fin 4 → Space :=
  ![0, e (order p 0), e (order p 0) + e (order p 1), e 0 + e 1 + e 2]

def tetrahedron (p : Fin 6) : Parameters 4 → Space := realize (vertices p)

def σ (p : Fin 6) : Chain Space 3 := sign p • ofVertices (vertices p)

def J3 : Chain Space 3 := σ 0 + σ 1 + σ 2 + σ 3 + σ 4 + σ 5

theorem order_bijective (p : Fin 6) : Function.Bijective (order p) := by
  fin_cases p <;> decide

/-- The table contains every coordinate permutation exactly once. -/
theorem all_permutations : ∀ f : Fin 3 → Fin 3,
    Function.Bijective f → ∃! p : Fin 6, order p = f := by
  unfold Function.Bijective Function.Injective Function.Surjective ExistsUnique
  decide

/-- The last vertex is the sum of the three permuted basis vectors. -/
theorem vertices_permutation (p : Fin 6) :
    vertices p = ![0, e (order p 0), e (order p 0) + e (order p 1),
      e (order p 0) + e (order p 1) + e (order p 2)] := by
  fin_cases p <;> ext j i <;> fin_cases j <;> fin_cases i <;>
    norm_num [vertices, order, e, Pi.single_apply]

/-- The coefficients are the determinant signs of the coordinate permutations. -/
theorem sign_determinant (p : Fin 6) :
    Matrix.det (Matrix.of fun i j : Fin 3 => e (order p j) i) = (sign p : ℝ) := by
  rw [Matrix.det_fin_three]
  fin_cases p <;> norm_num [order, e, sign, Pi.single_apply]

/-- Formula (78): its columns are the actual vertex differences. -/
def linearMatrix (p : Fin 6) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (vertices p j.succ - vertices p 0) i

theorem first_orientation : Matrix.det (linearMatrix 0) = 1 := by
  norm_num [linearMatrix, vertices, order, e, Matrix.det_fin_three, Pi.single_apply]

theorem positive_orientations (p : Fin 6) :
    (sign p : ℝ) * Matrix.det (linearMatrix p) = 1 := by
  fin_cases p <;>
    norm_num [sign, linearMatrix, vertices, order, e, Matrix.det_fin_three, Pi.single_apply]

/-- All three coordinates of the actual affine map, in its permutation order. -/
theorem coordinates (p : Fin 6) (w : Parameters 4) (j : Fin 3) :
    tetrahedron p w (order p j) =
      (![w.val 1 + w.val 2 + w.val 3, w.val 2 + w.val 3, w.val 3] : Space) j := by
  fin_cases p <;> fin_cases j <;>
    simp [tetrahedron, realize, vertices, order, e, Fin.sum_univ_succ] <;> ring

theorem range_iff (p : Fin 6) (x : Space) :
    x ∈ Set.range (tetrahedron p) ↔
      0 ≤ x (order p 2) ∧ x (order p 2) ≤ x (order p 1) ∧
        x (order p 1) ≤ x (order p 0) ∧ x (order p 0) ≤ 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [coordinates, coordinates, coordinates]
    have h0 := w.property.1 0
    have h1 := w.property.1 1
    have h2 := w.property.1 2
    have h3 := w.property.1 3
    have hs := w.property.2
    simp [Fin.sum_univ_succ] at hs
    dsimp
    exact ⟨h3, by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩
    let w : Parameters 4 := ⟨![1 - x (order p 0),
      x (order p 0) - x (order p 1), x (order p 1) - x (order p 2), x (order p 2)], by
      constructor
      · intro i; fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_succ]⟩
    refine ⟨w, ?_⟩
    ext i
    obtain ⟨j, rfl⟩ := (order_bijective p).2 i
    rw [coordinates]
    fin_cases j <;> simp [w]

theorem first_range (x : Space) : x ∈ Set.range (tetrahedron 0) ↔
    0 ≤ x 2 ∧ x 2 ≤ x 1 ∧ x 1 ≤ x 0 ∧ x 0 ≤ 1 := by
  simpa [order] using range_iff 0 x

/-- No strictness assumption is needed, so degenerate boundary points remain. -/
theorem cube_coverage (x : Space) :
    (∃ p, x ∈ Set.range (tetrahedron p)) ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [range_iff]
  constructor
  · rintro ⟨p, h0, h1, h2, h3⟩ i
    obtain ⟨j, rfl⟩ := (order_bijective p).2 i
    fin_cases j <;> constructor <;> dsimp at * <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    by_cases h01 : x 0 ≤ x 1
    · by_cases h12 : x 1 ≤ x 2
      · exact ⟨5, by simpa [order] using And.intro h0.1 ⟨h01, h12, h2.2⟩⟩
      · by_cases h02 : x 0 ≤ x 2
        · exact ⟨3, by simp [order]; exact ⟨h0.1, h02, le_of_not_ge h12, h1.2⟩⟩
        · exact ⟨2, by simp [order]; exact ⟨h2.1, le_of_not_ge h02, h01, h1.2⟩⟩
    · by_cases h02 : x 0 ≤ x 2
      · exact ⟨4, by simp [order]; exact ⟨h1.1, le_of_not_ge h01, h02, h2.2⟩⟩
      · by_cases h12 : x 1 ≤ x 2
        · exact ⟨1, by simp [order]; exact ⟨h1.1, h12, le_of_not_ge h02, h0.2⟩⟩
        · exact ⟨0, by simp [order]; exact ⟨h2.1, le_of_not_ge h12, le_of_not_ge h01, h0.2⟩⟩

theorem interior_order (p : Fin 6) {x : Space}
    (hx : x ∈ interior (Set.range (tetrahedron p))) :
    x (order p 2) < x (order p 1) ∧ x (order p 1) < x (order p 0) := by
  constructor
  · exact Exercise17.interior_coordinate_lt
      (fun h => (by have := (order_bijective p).1 h; contradiction))
      (fun y hy => (range_iff p y).mp hy |>.2.1) hx
  · exact Exercise17.interior_coordinate_lt
      (fun h => (by have := (order_bijective p).1 h; contradiction))
      (fun y hy => (range_iff p y).mp hy |>.2.2.1) hx

theorem disjoint_interiors (p q : Fin 6) (hpq : p ≠ q) :
    Disjoint (interior (Set.range (tetrahedron p)))
      (interior (Set.range (tetrahedron q))) := by
  apply Set.disjoint_left.mpr
  intro x hp hq
  have hp' := interior_order p hp
  have hq' := interior_order q hq
  fin_cases p <;> fin_cases q <;> simp_all [order] <;> linarith

theorem J3_value : J3.val = cube (e 0) (e 1) (e 2) := by
  simp [J3, σ, sign, ofVertices, vertices, order, List.ofFn_succ, cube]
  abel_nf

/-- Six square faces, each expanded into two oriented affine triangles.
Expanding the twenty-four tetrahedron faces cancels the twelve internal
occurrences in pairs; `boundary_cube` proves this before any integration. -/
theorem cube_boundary :
    (chainBoundary 2 J3).val =
      (square (e 0) (e 0 + e 1) (e 0 + e 1 + e 2) (e 0 + e 2) -
        square 0 (e 1) (e 1 + e 2) (e 2)) -
      (square (e 1) (e 0 + e 1) (e 0 + e 1 + e 2) (e 1 + e 2) -
        square 0 (e 0) (e 0 + e 2) (e 2)) +
      (square (e 2) (e 0 + e 2) (e 0 + e 1 + e 2) (e 1 + e 2) -
        square 0 (e 0) (e 0 + e 1) (e 1)) := by
  change boundary J3.val = _
  rw [J3_value, boundary_cube]

/-- The six affine coordinate insertions, with zero-based coordinate indices. -/
def B (r : ℝ) (i : Fin 3) : Exercise17.Plane →ᵃ[ℝ] Space where
  toFun u := Fin.insertNth i r u
  linear := by
    refine
      { toFun := fun u => Fin.insertNth i (0 : ℝ) u
        map_add' := ?_
        map_smul' := ?_ }
    · intro u v
      ext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
    · intro c u
      ext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
  map_vadd' := by
    intro u v
    ext j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp

@[simp] theorem B_same (r : ℝ) (i : Fin 3) (u : Exercise17.Plane) :
    B r i u i = r := by
  change (Fin.insertNth i r u : Space) i = r
  simp

@[simp] theorem B_other (r : ℝ) (i : Fin 3) (u : Exercise17.Plane) (j : Fin 2) :
    B r i u (i.succAbove j) = u j := by
  change (Fin.insertNth i r u : Space) (i.succAbove j) = u j
  simp

/-- Each square face is the union of these two actual affine triangle maps. -/
def faceTriangle (r : ℝ) (i : Fin 3) (b : Bool) : Parameters 3 → Space :=
  B r i ∘ (if b then Exercise17.triangle₂ else Exercise17.triangle₁)

theorem faceTriangle_realize (r : ℝ) (i : Fin 3) (b : Bool) (w : Parameters 3) :
    faceTriangle r i b w = realize
      (B r i ∘ (if b then Exercise17.vertices₂ else Exercise17.vertices₁)) w := by
  cases b <;> exact realize_affine (B r i) _ w

/-- Exact geometric range of each pair of boundary triangles. -/
theorem face_coverage (r : ℝ) (i : Fin 3) (x : Space) :
    (∃ b, x ∈ Set.range (faceTriangle r i b)) ↔
      x i = r ∧ ∀ j : Fin 2, 0 ≤ x (i.succAbove j) ∧ x (i.succAbove j) ≤ 1 := by
  constructor
  · rintro ⟨b, w, rfl⟩
    have hs : ∀ j, 0 ≤ (if b then Exercise17.triangle₂ w else Exercise17.triangle₁ w) j ∧
        (if b then Exercise17.triangle₂ w else Exercise17.triangle₁ w) j ≤ 1 := by
      apply (Exercise17.square_coverage _).mp
      cases b
      · exact Or.inl ⟨w, rfl⟩
      · exact Or.inr ⟨w, rfl⟩
    cases b <;> simpa [faceTriangle, Function.comp_def] using hs
  · rintro ⟨hi, h⟩
    let u : Exercise17.Plane := fun j => x (i.succAbove j)
    have hu := (Exercise17.square_coverage u).mpr h
    have hx : B r i u = x := by
      ext j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simpa using hi.symm
      · simp [u]
    rcases hu with ⟨w, hw⟩ | ⟨w, hw⟩
    · refine ⟨false, w, ?_⟩
      simpa [faceTriangle, Function.comp_def, hw] using hx
    · refine ⟨true, w, ?_⟩
      simpa [faceTriangle, Function.comp_def, hw] using hx

/-- Twelve triangles cover exactly the cube surface, including edges and corners. -/
theorem surface_coverage (x : Space) :
    (∃ (i : Fin 3) (r : Fin 2) (b : Bool),
      x ∈ Set.range (faceTriangle (r.val : ℝ) i b)) ↔
      (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∃ i, x i = 0 ∨ x i = 1 := by
  constructor
  · rintro ⟨i, r, b, hx⟩
    obtain ⟨hi, ho⟩ := (face_coverage (r.val : ℝ) i x).mp ⟨b, hx⟩
    constructor
    · intro j
      refine Fin.succAboveCases i ?_ (fun k => ho k) j
      rw [hi]
      fin_cases r <;> norm_num
    · refine ⟨i, ?_⟩
      fin_cases r <;> simp_all
  · rintro ⟨hc, i, hi | hi⟩
    · obtain ⟨b, hb⟩ := (face_coverage 0 i x).mpr ⟨hi, fun j => hc _⟩
      exact ⟨i, 0, b, by simpa using hb⟩
    · obtain ⟨b, hb⟩ := (face_coverage 1 i x).mpr ⟨hi, fun j => hc _⟩
      exact ⟨i, 1, b, by simpa using hb⟩

end Rudin.Chapter10.Exercise18
