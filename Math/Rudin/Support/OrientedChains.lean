module

public import Math.Rudin.Support.OrderedChains
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Signed affine chains and their faces

The orientation quotient identifies an adjacent vertex interchange with a minus
sign and kills repeated vertices. Boundary descent is proved from the deletion
formula, not assumed. `Graded E n` has exactly `n` vertices (augmented degree
`n - 1`); `Chain E k` has dimension `k`. The augmented boundary of a vertex is
the empty generator. The ordinary boundary convention in dimension zero is
provided separately.

Sources: Rudin 10.26–10.30, Exercises 10.16–10.19 and 10.32, book pages
266–270, 291–292, 298–299 (PDF 275–279, 300–301, 307–308).
This quotient is algebraic. It does not identify chains with integration
functionals. In particular, nonlinear postcomposition must not be implemented
by mapping vertices.
-/

@[expose] public section
noncomputable section

namespace Rudin.Support.OrientedChains

namespace Raw

open OrderedChains

variable {E F : Type*}

/-- Generating orientation and degeneracy relations, in arbitrary contexts. -/
inductive Relation : OrderedChains.Chain E → Prop
  | swap (a b : E) (tail : List E) :
      Relation (generator (a :: b :: tail) + generator (b :: a :: tail))
  | duplicate (a : E) (tail : List E) : Relation (generator (a :: a :: tail))
  | prepend (a : E) {r : OrderedChains.Chain E} : Relation r → Relation (prepend a r)

/-- Only the explicitly stated orientation and repeated-vertex relations. -/
def relations (E : Type*) : AddSubgroup (OrderedChains.Chain E) :=
  AddSubgroup.closure {r | Relation r}

theorem relation_mem {r : OrderedChains.Chain E} (h : Relation r) : r ∈ relations E :=
  AddSubgroup.subset_closure h

theorem prepend_mem (a : E) {r : OrderedChains.Chain E} (h : r ∈ relations E) :
    prepend a r ∈ relations E := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr => exact relation_mem (.prepend a hr)
  | zero => simp
  | add r s _ _ hr hs => simpa using (relations E).add_mem hr hs
  | neg r _ hr => simpa using (relations E).neg_mem hr

theorem swap_chain_mem (a b : E) (c : OrderedChains.Chain E) :
    prepend a (prepend b c) + prepend b (prepend a c) ∈ relations E := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of tail => exact relation_mem (.swap a b tail)
  | neg tail h => simpa only [map_neg, neg_add] using (relations E).neg_mem h
  | add c d hc hd =>
    simpa only [map_add, add_add_add_comm] using (relations E).add_mem hc hd

theorem repeat_chain_mem (a : E) (c : OrderedChains.Chain E) :
    prepend a (prepend a c) ∈ relations E := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of tail => exact relation_mem (.duplicate a tail)
  | neg tail h => simpa using (relations E).neg_mem h
  | add c d hc hd => simpa using (relations E).add_mem hc hd

theorem boundary_relation {r : OrderedChains.Chain E} (h : Relation r) :
    boundary r ∈ relations E := by
  induction h with
  | swap a b tail =>
    convert swap_chain_mem a b (boundaryWord tail) using 1
    simp [boundaryWord]
    abel
  | duplicate a tail =>
    convert repeat_chain_mem a (boundaryWord tail) using 1
    simp [boundaryWord]
  | prepend a h ih =>
    rw [boundary_prepend]
    exact (relations E).sub_mem (relation_mem h) (prepend_mem a ih)

/-- Boundary stability is a theorem about the generators of the relations. -/
theorem boundary_mem {r : OrderedChains.Chain E} (h : r ∈ relations E) :
    boundary r ∈ relations E := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr => exact boundary_relation hr
  | zero => simp
  | add r s _ _ hr hs => simpa using (relations E).add_mem hr hs
  | neg r _ hr => simpa using (relations E).neg_mem hr

theorem map_relation (f : E → F) {r : OrderedChains.Chain E} (h : Relation r) :
    Relation (mapVertices f r) := by
  induction h with
  | swap a b tail => simpa using Relation.swap (f a) (f b) (tail.map f)
  | duplicate a tail => simpa using Relation.duplicate (f a) (tail.map f)
  | prepend a h ih => simpa [mapVertices_prepend] using Relation.prepend (f a) ih

theorem map_mem (f : E → F) {r : OrderedChains.Chain E} (h : r ∈ relations E) :
    mapVertices f r ∈ relations F := by
  induction h using AddSubgroup.closure_induction with
  | mem r hr => exact relation_mem (map_relation f hr)
  | zero => simp
  | add r s _ _ hr hs => simpa using (relations F).add_mem hr hs
  | neg r _ hr => simpa using (relations F).neg_mem hr

end Raw

variable {E F G : Type*}

/-- Signed chains, modulo the proved orientation relations. -/
abbrev Total (E : Type*) := OrderedChains.Chain E ⧸ Raw.relations E

/-- The projection preserves all integer coefficients. -/
def project : OrderedChains.Chain E →+ Total E := QuotientAddGroup.mk' (Raw.relations E)

/-- An oriented ordered simplex, possibly empty in the augmented model. -/
def simplex (v : List E) : Total E := project (OrderedChains.generator v)

/-- The alternating deletion boundary on the orientation quotient. -/
def boundary : Total E →+ Total E :=
  QuotientAddGroup.lift (Raw.relations E) (project.comp OrderedChains.boundary)
    (by intro r hr; exact (QuotientAddGroup.eq_zero_iff _).mpr (Raw.boundary_mem hr))

@[simp] theorem boundary_project (c : OrderedChains.Chain E) :
    boundary (project c) = project (OrderedChains.boundary c) := rfl

@[simp] theorem boundary_simplex (v : List E) :
    boundary (simplex v) = project (OrderedChains.boundaryWord v) := by
  simp [simplex]

/-- Every twice-deleted face cancels, after quotienting as well as before. -/
theorem boundary_squared (c : Total E) : boundary (boundary c) = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | H c =>
    change boundary (boundary (project c)) = 0
    simp [OrderedChains.boundary_squared]

/-- A contextual adjacent transposition reverses orientation. -/
theorem swap (pre : List E) (a b : E) (tail : List E) :
    simplex (pre ++ a :: b :: tail) = -simplex (pre ++ b :: a :: tail) := by
  apply eq_neg_iff_add_eq_zero.mpr
  change project _ + project _ = 0
  rw [← map_add]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply Raw.relation_mem
  induction pre with
  | nil => exact .swap a b tail
  | cons x xs ih => exact .prepend x ih

/-- Repeated adjacent vertices give zero, not merely two-torsion. -/
theorem repeated (pre : List E) (a : E) (tail : List E) :
    simplex (pre ++ a :: a :: tail) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply Raw.relation_mem
  induction pre with
  | nil => exact .duplicate a tail
  | cons x xs ih => exact .prepend x ih

theorem edge_reverse (a b : E) : simplex [b, a] = -simplex [a, b] :=
  swap [] b a []

@[simp] theorem edge_self (a : E) : simplex [a, a] = 0 := repeated [] a []

theorem boundary_edge (a b : E) :
    boundary (simplex [a, b]) = simplex [b] - simplex [a] := by
  simp [simplex, OrderedChains.boundaryWord]

theorem boundary_triangle (a b c : E) :
    boundary (simplex [a, b, c]) = simplex [b, c] - simplex [a, c] + simplex [a, b] := by
  simpa [simplex] using congrArg project (OrderedChains.boundary_triangle a b c)

/-- The full alternating face formula, with signed integer coefficients. -/
theorem boundary_eq_sum (v : List E) :
    boundary (simplex v) =
      ∑ i ∈ Finset.range v.length, (-1 : ℤ) ^ i • simplex (v.eraseIdx i) := by
  simp [OrderedChains.boundaryWord_eq_sum, map_sum, simplex]

/-- Mapping vertices descends to the orientation quotient. It is a geometric
pushforward only for affine maps; the nonlinear case needs parameterizations. -/
def mapVertices (f : E → F) : Total E →+ Total F :=
  QuotientAddGroup.lift (Raw.relations E) (project.comp (OrderedChains.mapVertices f))
    (by intro r hr; exact (QuotientAddGroup.eq_zero_iff _).mpr (Raw.map_mem f hr))

@[simp] theorem mapVertices_simplex (f : E → F) (v : List E) :
    mapVertices f (simplex v) = simplex (v.map f) := rfl

theorem boundary_mapVertices (f : E → F) (c : Total E) :
    boundary (mapVertices f c) = mapVertices f (boundary c) := by
  induction c using QuotientAddGroup.induction_on with
  | H c => exact congrArg project (OrderedChains.boundary_mapVertices f c)

/-- List deletion agrees with the increasing finite-index face map. -/
theorem eraseIdx_ofFn {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    (List.ofFn v).eraseIdx i.val = List.ofFn (v ∘ i.succAbove) := by
  apply List.ext_getElem
  · have h := List.length_eraseIdx_add_one (l := List.ofFn v) (by simpa using i.isLt)
    simp only [List.length_ofFn] at h ⊢
    omega
  · intro j hj hj'
    have hjn : j < n := by simpa using hj'
    simp only [List.getElem_eraseIdx, List.getElem_ofFn, Function.comp_apply]
    split_ifs with h
    · congr 1
      exact (Fin.succAbove_of_castSucc_lt i ⟨j, hjn⟩ h).symm
    · congr 1
      exact (Fin.succAbove_of_le_castSucc i ⟨j, hjn⟩ (show i.val ≤ j from Nat.le_of_not_gt h)).symm

/-- Signed face formula in finite-index form, compatible with `realize_face`. -/
theorem boundary_ofFn {n : ℕ} (v : Fin (n + 1) → E) :
    boundary (simplex (List.ofFn v)) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • simplex (List.ofFn (v ∘ i.succAbove)) := by
  rw [boundary_eq_sum, List.length_ofFn, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [eraseIdx_ofFn]

/-- The subgroup generated by simplexes with exactly `n` vertices. -/
def degreePart (E : Type*) (n : ℕ) : AddSubgroup (Total E) :=
  AddSubgroup.closure {c | ∃ v : List E, v.length = n ∧ simplex v = c}

/-- A fixed augmented degree, indexed by vertex count. -/
abbrev Graded (E : Type*) (n : ℕ) := degreePart E n

/-- An ordinary fixed-dimensional chain has `k + 1` vertices per generator. -/
abbrev Chain (E : Type*) (k : ℕ) := Graded E (k + 1)

theorem simplex_mem_degree (v : List E) : simplex v ∈ degreePart E v.length :=
  AddSubgroup.subset_closure ⟨v, rfl, rfl⟩

/-- Fixed-degree generator with an explicit finite ordered vertex tuple. -/
def ofVertices {n : ℕ} (v : Fin n → E) : Graded E n :=
  ⟨simplex (List.ofFn v), by simpa using simplex_mem_degree (List.ofFn v)⟩

/-- Every deleted face has one fewer vertex. -/
theorem boundary_mem_degree {n : ℕ} {c : Total E} (hc : c ∈ degreePart E (n + 1)) :
    boundary c ∈ degreePart E n := by
  induction hc using AddSubgroup.closure_induction with
  | mem c hc =>
    obtain ⟨v, hv, rfl⟩ := hc
    rw [boundary_eq_sum]
    apply AddSubgroup.sum_mem
    intro i hi
    apply AddSubgroup.zsmul_mem
    apply AddSubgroup.subset_closure
    refine ⟨v.eraseIdx i, ?_, rfl⟩
    have := List.length_eraseIdx_add_one (Finset.mem_range.mp hi)
    omega
  | zero => simp
  | add c d _ _ hc hd => simpa using (degreePart E n).add_mem hc hd
  | neg c _ hc => simpa using (degreePart E n).neg_mem hc

/-- The augmented fixed-degree boundary. -/
def gradedBoundary (n : ℕ) : Graded E (n + 1) →+ Graded E n where
  toFun c := ⟨boundary c, boundary_mem_degree c.property⟩
  map_zero' := Subtype.ext (map_zero boundary)
  map_add' c d := Subtype.ext (map_add boundary c.val d.val)

/-- The fixed-degree boundary has the actual increasing-index face formula. -/
theorem gradedBoundary_ofVertices {n : ℕ} (v : Fin (n + 1) → E) :
    gradedBoundary n (ofVertices v) =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • ofVertices (v ∘ i.succAbove) := by
  apply Subtype.ext
  simpa [gradedBoundary, ofVertices] using boundary_ofFn v

/-- Ordinary positive-dimensional boundary. -/
def chainBoundary (k : ℕ) : Chain E (k + 1) →+ Chain E k := gradedBoundary (k + 1)

theorem gradedBoundary_squared (n : ℕ) (c : Graded E (n + 2)) :
    gradedBoundary n (gradedBoundary (n + 1) c) = 0 :=
  Subtype.ext (boundary_squared c.val)

theorem chainBoundary_squared (k : ℕ) (c : Chain E (k + 2)) :
    chainBoundary k (chainBoundary (k + 1) c) = 0 :=
  gradedBoundary_squared (k + 1) c

/-- The unaugmented convention kills the boundary of every zero-chain. -/
def ordinaryBoundary (k : ℕ) : Chain E k →+ Total E :=
  if k = 0 then 0 else boundary.comp (degreePart E (k + 1)).subtype

@[simp] theorem ordinaryBoundary_zero (c : Chain E 0) : ordinaryBoundary 0 c = 0 := by
  simp [ordinaryBoundary]

@[simp] theorem ordinaryBoundary_succ (k : ℕ) (c : Chain E (k + 1)) :
    ordinaryBoundary (k + 1) c = boundary c := by simp [ordinaryBoundary]

/-- Fixed-degree vertex maps retain multiplicities and preserve the boundary. -/
theorem mapVertices_mem_degree (f : E → F) {n : ℕ} {c : Total E}
    (hc : c ∈ degreePart E n) : mapVertices f c ∈ degreePart F n := by
  induction hc using AddSubgroup.closure_induction with
  | mem c hc =>
    obtain ⟨v, hv, rfl⟩ := hc
    exact AddSubgroup.subset_closure ⟨v.map f, by simpa using hv, rfl⟩
  | zero => simp
  | add c d _ _ hc hd => simpa using (degreePart F n).add_mem hc hd
  | neg c _ hc => simpa using (degreePart F n).neg_mem hc

def gradedMap (f : E → F) (n : ℕ) : Graded E n →+ Graded F n where
  toFun c := ⟨mapVertices f c, mapVertices_mem_degree f c.property⟩
  map_zero' := Subtype.ext (map_zero (mapVertices f))
  map_add' c d := Subtype.ext (map_add (mapVertices f) c.val d.val)

theorem gradedBoundary_map (f : E → F) (n : ℕ) (c : Graded E (n + 1)) :
    gradedBoundary n (gradedMap f (n + 1) c) = gradedMap f n (gradedBoundary n c) :=
  Subtype.ext (boundary_mapVertices f c)

/-- Two triangles with the square's source signs and a common diagonal. -/
def square (a b c d : E) : Total E := simplex [a, b, c] - simplex [a, d, c]

/-- The internal diagonal cancels, leaving four cyclic oriented edges. -/
theorem boundary_square (a b c d : E) :
    boundary (square a b c d) =
      simplex [a, b] + simplex [b, c] + simplex [c, d] + simplex [d, a] := by
  simp only [square, map_sub, boundary_triangle, edge_reverse c d, edge_reverse d a]
  abel

/-- Subtracting the second signed triangle doubles the internal diagonal. -/
theorem boundary_square_difference (a b c d : E) :
    boundary (simplex [a, b, c] + simplex [a, d, c]) =
      simplex [a, b] + simplex [b, c] + simplex [a, d] + simplex [d, c] -
        (2 : ℤ) • simplex [a, c] := by
  simp only [map_add, boundary_triangle]
  abel

theorem boundary_tetrahedron (a b c d : E) :
    boundary (simplex [a, b, c, d]) =
      simplex [b, c, d] - simplex [a, c, d] + simplex [a, b, d] - simplex [a, b, c] := by
  simp [simplex, OrderedChains.boundaryWord]
  abel

section Cube
variable [AddCommGroup E]

/-- Six signed permutation tetrahedra, with the signs in Exercise 10.18. -/
def cube (x y z : E) : Total E :=
  simplex [0, x, x + y, x + y + z] - simplex [0, x, x + z, x + y + z] -
  simplex [0, y, x + y, x + y + z] + simplex [0, y, y + z, x + y + z] +
  simplex [0, z, x + z, x + y + z] - simplex [0, z, y + z, x + y + z]

/-- All internal triangular faces cancel, leaving twelve boundary triangles.
The six pairs are the coordinate-insertion square faces in Exercise 10.19. -/
theorem boundary_cube (x y z : E) :
    boundary (cube x y z) =
      (square x (x + y) (x + y + z) (x + z) - square 0 y (y + z) z) -
      (square y (x + y) (x + y + z) (y + z) - square 0 x (x + z) z) +
      (square z (x + z) (x + y + z) (y + z) - square 0 x (x + y) y) := by
  simp only [cube, square, map_add, map_sub, boundary_tetrahedron]
  abel

end Cube

section Realization

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Closed barycentric parameter simplex. For `n = 0` it is empty. -/
def Parameters (n : ℕ) :=
  {w : Fin n → ℝ // (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- Insert a zero barycentric coordinate: the actual parameter face inclusion. -/
def face {n : ℕ} (i : Fin (n + 1)) (w : Parameters n) : Parameters (n + 1) :=
  ⟨Fin.insertNth i 0 w.val, by
    constructor
    · intro j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j
      · simp
      · simpa using w.property.1 k
    · rw [Fin.sum_univ_succAbove _ i]
      simpa using w.property.2⟩

/-- Actual affine evaluation, not merely a vertex map. -/
def realize {n : ℕ} (v : Fin n → E) (w : Parameters n) : E := ∑ i, w.val i • v i

/-- Restricting an affine simplex to a parameter face deletes that vertex. -/
theorem realize_face {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1))
    (w : Parameters n) : realize v (face i w) = realize (v ∘ i.succAbove) w := by
  unfold realize face
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- Affine postcomposition is exactly vertex mapping on the realized simplex. -/
theorem realize_affine {n : ℕ} (f : E →ᵃ[ℝ] F) (v : Fin n → E) (w : Parameters n) :
    f (realize v w) = realize (f ∘ v) w := by
  have hf (x : E) : f x = f.linear x + f 0 := congrFun f.decomp x
  calc
    f (realize v w) = (∑ i, w.val i • f.linear (v i)) + f 0 := by
      rw [hf]
      simp only [realize, map_sum, map_smul]
    _ = ∑ i, w.val i • (f.linear (v i) + f 0) := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul,
        w.property.2, one_smul]
    _ = realize (f ∘ v) w := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hf]
      rfl

/-- The source parameter domain `Q^k` in Cartesian coordinates. -/
def CartesianParameters (k : ℕ) :=
  {u : Fin k → ℝ // (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}

/-- The missing barycentric coordinate is `1 - sum u`. -/
def barycentric {k : ℕ} (u : CartesianParameters k) : Parameters (k + 1) :=
  ⟨Fin.cons (1 - ∑ i, u.val i) u.val, by
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact sub_nonneg.mpr u.property.2
      · exact u.property.1 j
    · rw [Fin.sum_univ_succ]
      simp⟩

/-- Comparison with Rudin's literal formula (76), including the base vertex. -/
theorem realize_cartesian {k : ℕ} (v : Fin (k + 1) → E) (u : CartesianParameters k) :
    realize v (barycentric u) = v 0 + ∑ i, u.val i • (v i.succ - v 0) := by
  simp only [realize, barycentric, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
  abel

/-- Parameterized realization permits arbitrary nonlinear postcomposition.
Its faces are restrictions of the same parameterized map. -/
def parameterize {n : ℕ} (T : E → F) (v : Fin n → E) : Parameters n → F :=
  T ∘ realize v

omit [AddCommGroup F] [Module ℝ F] in
theorem parameterize_face {n : ℕ} (T : E → F) (v : Fin (n + 1) → E)
    (i : Fin (n + 1)) : parameterize T v ∘ face i = parameterize T (v ∘ i.succAbove) := by
  funext w
  exact congrArg T (realize_face v i w)

end Realization

namespace Parametric

/-- A full-domain path, used on the unit parameter interval. No regularity is
assumed by the combinatorial boundary laws. -/
abbrev Path (E : Type*) := ℝ → E

def reverse (p : Path E) : Path E := fun t => p (1 - t)

inductive PathRelation : FreeAbelianGroup (Path E) → Prop
  | reversal (p : Path E) : PathRelation (FreeAbelianGroup.of p + FreeAbelianGroup.of (reverse p))
  | constant (a : E) : PathRelation (FreeAbelianGroup.of (fun _ : ℝ => a))

def pathRelations (E : Type*) : AddSubgroup (FreeAbelianGroup (Path E)) :=
  AddSubgroup.closure {r | PathRelation r}

/-- Genuine parameterized paths with reversal signs and zero constant paths.
Maps are compared on all of `ℝ`, not only on the unit interval. -/
abbrev PathChain (E : Type*) := FreeAbelianGroup (Path E) ⧸ pathRelations E

def path (p : Path E) : PathChain E := QuotientAddGroup.mk (FreeAbelianGroup.of p)

theorem path_reverse (p : Path E) : path (reverse p) = -path p := by
  apply eq_neg_iff_add_eq_zero.mpr
  rw [add_comm]
  change QuotientAddGroup.mk' (pathRelations E) _ + QuotientAddGroup.mk' (pathRelations E) _ = 0
  rw [← map_add]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure (.reversal p))

@[simp] theorem path_constant (a : E) : path (fun _ : ℝ => a) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure (.constant a))

def rawPathBoundary : FreeAbelianGroup (Path E) →+ FreeAbelianGroup E :=
  FreeAbelianGroup.lift (fun p => FreeAbelianGroup.of (p 1) - FreeAbelianGroup.of (p 0))

theorem rawPathBoundary_relation {r : FreeAbelianGroup (Path E)} (hr : PathRelation r) :
    rawPathBoundary r = 0 := by
  cases hr <;> simp [rawPathBoundary, reverse]

/-- The endpoint boundary is well-defined on signed parameterized paths. -/
def pathBoundary : PathChain E →+ FreeAbelianGroup E :=
  QuotientAddGroup.lift (pathRelations E) rawPathBoundary (by
    intro r hr
    induction hr using AddSubgroup.closure_induction with
    | mem r hr => exact rawPathBoundary_relation hr
    | zero => exact rawPathBoundary.ker.zero_mem
    | add r s _ _ hr hs => exact rawPathBoundary.ker.add_mem hr hs
    | neg r _ hr => exact rawPathBoundary.ker.neg_mem hr)

@[simp] theorem pathBoundary_path (p : Path E) :
    pathBoundary (path p) = FreeAbelianGroup.of (p 1) - FreeAbelianGroup.of (p 0) := by
  simp [pathBoundary, path, rawPathBoundary, QuotientAddGroup.mk]

/-- Nonlinear postcomposition acts on the whole path, not only its endpoints. -/
def rawPathMap (f : E → F) : FreeAbelianGroup (Path E) →+ FreeAbelianGroup (Path F) :=
  FreeAbelianGroup.map (fun p => f ∘ p)

theorem rawPathMap_relation (f : E → F) {r : FreeAbelianGroup (Path E)}
    (hr : PathRelation r) : PathRelation (rawPathMap f r) := by
  cases hr with
  | reversal p => exact .reversal (f ∘ p)
  | constant a => exact .constant (f a)

def pathMap (f : E → F) : PathChain E →+ PathChain F :=
  QuotientAddGroup.lift (pathRelations E)
    ((QuotientAddGroup.mk' (pathRelations F)).comp (rawPathMap f)) (by
      intro r hr
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      induction hr using AddSubgroup.closure_induction with
      | mem r hr => exact AddSubgroup.subset_closure (rawPathMap_relation f hr)
      | zero => simp
      | add r s _ _ hr hs => simpa using (pathRelations F).add_mem hr hs
      | neg r _ hr => simpa using (pathRelations F).neg_mem hr)

@[simp] theorem pathMap_path (f : E → F) (p : Path E) :
    pathMap f (path p) = path (f ∘ p) := rfl

/-- Genuine nonlinear postcomposition commutes with the endpoint boundary. -/
theorem pathBoundary_map (f : E → F) (c : PathChain E) :
    pathBoundary (pathMap f c) = FreeAbelianGroup.map f (pathBoundary c) := by
  induction c using QuotientAddGroup.induction_on with
  | H c =>
    have h : (pathBoundary.comp (pathMap f)).comp (QuotientAddGroup.mk' (pathRelations E)) =
        ((FreeAbelianGroup.map f).comp pathBoundary).comp
          (QuotientAddGroup.mk' (pathRelations E)) := by
      apply FreeAbelianGroup.lift_ext
      intro p
      change pathBoundary (pathMap f (path p)) = FreeAbelianGroup.map f (pathBoundary (path p))
      simp [Function.comp_apply]
    exact congrArg (fun g : FreeAbelianGroup (Path E) →+ FreeAbelianGroup F => g c) h

section Segment
variable [AddCommGroup E] [Module ℝ E]

/-- The full affine segment parameterization. -/
def segment (a b : E) : Path E := fun t => (1 - t) • a + t • b

/-- Reversing an actual affine realization agrees with swapping its vertices. -/
theorem segment_reverse (a b : E) : reverse (segment a b) = segment b a := by
  funext t
  simp [reverse, segment, add_comm]

@[simp] theorem segment_self (a : E) : path (segment a a) = 0 := by
  have h : segment a a = fun _ : ℝ => a := by
    funext t
    simp [segment, ← add_smul]
  rw [h, path_constant]

/-- Actual affine path boundary agrees with the affine vertex-chain formula. -/
theorem pathBoundary_segment (a b : E) :
    pathBoundary (path (segment a b)) = FreeAbelianGroup.of b - FreeAbelianGroup.of a := by
  simp [segment]

/-- The barycentric realization of two vertices is the full segment map on
unit-interval parameters, not merely the same endpoints. -/
theorem segment_realize (a b : E) (t : Set.Icc (0 : ℝ) 1) :
    realize ![a, b] (barycentric (k := 1) ⟨fun _ => t.val, by
      constructor
      · intro _; exact t.property.1
      · simpa using t.property.2⟩) = segment a b t.val := by
  simp [realize, barycentric, segment, Fin.sum_univ_two]

end Segment

/-- Formal unit-square parameterizations; smoothness can be imposed separately. -/
abbrev SurfaceChain (E : Type*) := FreeAbelianGroup ((ℝ × ℝ) → E)

def surface (S : (ℝ × ℝ) → E) : SurfaceChain E := FreeAbelianGroup.of S

/-- The four oriented restrictions of the actual map, not edges between its
corner images. This distinction is essential for Exercise 10.32. -/
def surfaceBoundary : SurfaceChain E →+ PathChain E :=
  FreeAbelianGroup.lift fun S =>
    path (fun t => S (t, 0)) + path (fun t => S (1, t)) -
    path (fun t => S (t, 1)) - path (fun t => S (0, t))

@[simp] theorem surfaceBoundary_surface (S : (ℝ × ℝ) → E) :
    surfaceBoundary (surface S) =
      path (fun t => S (t, 0)) + path (fun t => S (1, t)) -
      path (fun t => S (t, 1)) - path (fun t => S (0, t)) := by
  simp [surfaceBoundary, surface]

/-- Postcomposition of a surface applies to its full parameterization. -/
def surfaceMap (f : E → F) : SurfaceChain E →+ SurfaceChain F :=
  FreeAbelianGroup.map (fun S => f ∘ S)

/-- Nonlinear pushforward preserves all four actual boundary restrictions. -/
theorem surfaceBoundary_map (f : E → F) (c : SurfaceChain E) :
    surfaceBoundary (surfaceMap f c) = pathMap f (surfaceBoundary c) := by
  have h : surfaceBoundary.comp (surfaceMap f) = (pathMap f).comp surfaceBoundary := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change surfaceBoundary (surface (f ∘ S)) = pathMap f (surfaceBoundary (surface S))
    simp [Function.comp_def]
  exact congrArg (fun g : SurfaceChain E →+ PathChain F => g c) h

/-- Endpoint cancellation proves the boundary-square law for every finite
parameterized square chain, with no Stokes hypothesis. -/
theorem surfaceBoundary_squared (c : SurfaceChain E) :
    pathBoundary (surfaceBoundary c) = 0 := by
  have h : pathBoundary.comp surfaceBoundary = (0 : SurfaceChain E →+ FreeAbelianGroup E) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp [surfaceBoundary, pathBoundary_path]
  exact congrArg (fun f : SurfaceChain E →+ FreeAbelianGroup E => f c) h

/-- Two equal parameterized seam paths occur twice, not once. The only
hypothesis is equality of actual restrictions; no boundary law is assumed. -/
theorem repeated_seam (S : (ℝ × ℝ) → E) (h : ∀ t, S (1, t) = S (0, 1 - t)) :
    surfaceBoundary (surface S) =
      path (fun t => S (t, 0)) - path (fun t => S (t, 1)) +
        (2 : ℤ) • path (fun t => S (1, t)) := by
  have hp : (fun t => S (1, t)) = reverse (fun t => S (0, t)) := funext h
  have hr := path_reverse (fun t => S (0, t))
  rw [← hp] at hr
  rw [surfaceBoundary_surface, hr]
  abel

/-- Rudin's actual Möbius parameterization, in product coordinates. -/
def mobius (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((1 - p.2 * Real.sin p.1) * Real.cos (2 * p.1),
   (1 - p.2 * Real.sin p.1) * Real.sin (2 * p.1), p.2 * Real.cos p.1)

theorem mobius_seam (t : ℝ) : mobius (Real.pi, t) = mobius (0, -t) := by
  norm_num [mobius, Real.sin_two_mul, Real.cos_two_mul]

/-- Rescale the source rectangle to the unit square without changing orientation
when `δ > 0`. The algebraic laws also hold for all other values of `δ`. -/
def mobiusSquare (δ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ × ℝ :=
  mobius (Real.pi * p.1, δ * (2 * p.2 - 1))

/-- The repeated seam is proved for the actual nonlinear source map. -/
theorem mobiusSquare_seam (δ t : ℝ) :
    mobiusSquare δ (1, t) = mobiusSquare δ (0, 1 - t) := by
  simp only [mobiusSquare, mul_one, mul_zero]
  rw [mobius_seam]
  apply congrArg mobius
  exact Prod.ext rfl (by dsimp; ring)

/-- The source's `Γ₁ + Γ₃ + 2 Γ₂`, with `Γ₃` represented by minus the top
edge. This is a parameter-chain equality, not the geometric boundary curve. -/
theorem mobius_boundary (δ : ℝ) :
    surfaceBoundary (surface (mobiusSquare δ)) =
      path (fun t => mobiusSquare δ (t, 0)) - path (fun t => mobiusSquare δ (t, 1)) +
        (2 : ℤ) • path (fun t => mobiusSquare δ (1, t)) :=
  repeated_seam _ (mobiusSquare_seam δ)

end Parametric

end Rudin.Support.OrientedChains
