module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Alternating boundaries of ordered vertex chains

Source: Rudin Sections 10.26–10.30, book pages 266–270 (PDF 275–279).
An ordered vertex list is a generator; integer coefficients preserve signs and
multiplicities. The recursive boundary deletes each vertex with alternating
sign. Its square is zero before any geometric identifications are imposed.

This is an augmented, ungraded presentation: the empty list is a formal
simplex in degree -1: `∂[] = 0` and `∂[a] = []`, where the empty-list
generator is nonzero.
On positive-dimensional simplexes this is the source's boundary formula.
This file does not identify permutations with their orientation signs, define
smooth parameterized surfaces, or define form integration. Those comparisons
remain necessary before using this model as a complete oriented-chain API.
-/

@[expose] public section

noncomputable section

namespace Rudin.Support.OrderedChains

variable {E F : Type*}

/-- Formal signed sums of ordered vertex lists, with integer multiplicities. -/
abbrev Chain (E : Type*) := FreeAbelianGroup (List E)

/-- The generator associated to an ordered vertex list. -/
def generator (vertices : List E) : Chain E := FreeAbelianGroup.of vertices

/-- Attach a common initial vertex to every generator, preserving coefficients. -/
def prepend (vertex : E) : Chain E →+ Chain E :=
  FreeAbelianGroup.map (List.cons vertex)

@[simp] theorem prepend_generator (vertex : E) (vertices : List E) :
    prepend vertex (generator vertices) = generator (vertex :: vertices) := rfl

/-- Delete vertices with alternating signs, recursively from the first vertex. -/
def boundaryWord (vertices : List E) : Chain E :=
  List.rec (motive := fun _ => Chain E) 0
    (fun vertex remaining tailBoundary => generator remaining - prepend vertex tailBoundary)
    vertices

@[simp] theorem boundaryWord_nil : boundaryWord ([] : List E) = 0 := rfl

@[simp] theorem boundaryWord_cons (vertex : E) (vertices : List E) :
    boundaryWord (vertex :: vertices) =
      generator vertices - prepend vertex (boundaryWord vertices) := rfl

/-- Extend the alternating boundary additively to chains. -/
def boundary : Chain E →+ Chain E := FreeAbelianGroup.lift boundaryWord

@[simp] theorem boundary_generator (vertices : List E) :
    boundary (generator vertices) = boundaryWord vertices := by
  simp [boundary, generator]

/-- The contraction identity is proved on generators, then extended additively. -/
theorem boundary_prepend (vertex : E) (chain : Chain E) :
    boundary (prepend vertex chain) = chain - prepend vertex (boundary chain) := by
  have h : boundary.comp (prepend vertex) =
      AddMonoidHom.id (Chain E) - (prepend vertex).comp boundary := by
    apply FreeAbelianGroup.lift_ext
    intro vertices
    simp [boundary, prepend, generator]
  exact congrArg (fun f : Chain E →+ Chain E => f chain) h

/-- Each twice-deleted face cancels its oppositely signed occurrence. -/
theorem boundary_boundaryWord (vertices : List E) : boundary (boundaryWord vertices) = 0 := by
  induction vertices with
  | nil => simp
  | cons vertex vertices ih =>
    simp [boundary_prepend, ih]

/-- The boundary of every chain has zero boundary, including multiplicities. -/
theorem boundary_squared (chain : Chain E) : boundary (boundary chain) = 0 := by
  have h : boundary.comp boundary = (0 : Chain E →+ Chain E) := by
    apply FreeAbelianGroup.lift_ext
    intro vertices
    simpa [boundary, generator] using boundary_boundaryWord vertices
  exact congrArg (fun f : Chain E →+ Chain E => f chain) h

/-- The recursive formula is the source's alternating sum of deleted vertices. -/
theorem boundaryWord_eq_sum (vertices : List E) :
    boundaryWord vertices =
      ∑ i ∈ Finset.range vertices.length,
        (-1 : ℤ) ^ i • generator (vertices.eraseIdx i) := by
  induction vertices with
  | nil => simp [boundaryWord]
  | cons vertex vertices ih =>
    rw [boundaryWord_cons, ih]
    simp only [List.length_cons, Finset.sum_range_succ', pow_zero, one_smul,
      List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, map_sum, map_zsmul,
      prepend_generator, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    abel

/-- The augmentation has zero boundary on the empty-list generator. -/
theorem boundary_empty : boundary (generator ([] : List E)) = 0 := by simp

/-- A vertex maps to the degree-minus-one generator, not to the zero chain. -/
theorem boundary_vertex (vertex : E) :
    boundary (generator [vertex]) = generator [] := by simp

/-- The boundary of an edge is its terminal vertex minus its initial vertex. -/
theorem boundary_edge (a b : E) :
    boundary (generator [a, b]) = generator [b] - generator [a] := by
  simp [boundaryWord]

/-- The three oriented faces of an ordered triangle. -/
theorem boundary_triangle (a b c : E) :
    boundary (generator [a, b, c]) =
      generator [b, c] - generator [a, c] + generator [a, b] := by
  simp [boundaryWord]
  abel

/-- Mapping vertices preserves integer coefficients and repeated simplexes. -/
def mapVertices (f : E → F) : Chain E →+ Chain F :=
  FreeAbelianGroup.map (List.map f)

@[simp] theorem mapVertices_generator (f : E → F) (vertices : List E) :
    mapVertices f (generator vertices) = generator (vertices.map f) := rfl

theorem mapVertices_prepend (f : E → F) (vertex : E) (chain : Chain E) :
    mapVertices f (prepend vertex chain) = prepend (f vertex) (mapVertices f chain) := by
  have h : (mapVertices f).comp (prepend vertex) =
      (prepend (f vertex)).comp (mapVertices f) := by
    apply FreeAbelianGroup.lift_ext
    intro vertices
    simp [mapVertices, prepend]
  exact congrArg (fun g : Chain E →+ Chain F => g chain) h

theorem boundaryWord_map (f : E → F) (vertices : List E) :
    boundaryWord (vertices.map f) = mapVertices f (boundaryWord vertices) := by
  induction vertices with
  | nil => simp
  | cons vertex vertices ih =>
    simp [ih, mapVertices_prepend]

/-- Taking boundary commutes with any mapping of the vertices. -/
theorem boundary_mapVertices (f : E → F) (chain : Chain E) :
    boundary (mapVertices f chain) = mapVertices f (boundary chain) := by
  have h : boundary.comp (mapVertices f) = (mapVertices f).comp boundary := by
    apply FreeAbelianGroup.lift_ext
    intro vertices
    simpa [mapVertices, generator, boundary] using boundaryWord_map f vertices
  exact congrArg (fun g : Chain E →+ Chain F => g chain) h

/-- Multiplicity is retained, rather than replacing a chain by its geometric range. -/
theorem boundary_multiplicity (coefficient : ℤ) (chain : Chain E) :
    boundary (coefficient • chain) = coefficient • boundary chain :=
  map_zsmul boundary coefficient chain

end Rudin.Support.OrderedChains
