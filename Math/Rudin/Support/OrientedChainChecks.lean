module

public import Math.Rudin.Support.OrientedChains
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Nontriviality and sign checks for the oriented-chain prototype

Exterior-algebra evaluation proves that fixed-degree simplex generators have
infinite order. Coordinate insertions check the six cube-face signs. Endpoint
evaluation checks that the actual Möbius seam retains its multiplicity.
These results do not identify chains with form-integration functionals.
-/

@[expose] public section

open Rudin.Support
open Rudin.Support.OrientedChains
noncomputable section
namespace Rudin.Support.OrientedChainChecks
abbrev V := ℕ →₀ ℤ
abbrev A := ExteriorAlgebra ℤ V
def b : Module.Basis ℕ ℤ V := Finsupp.basisSingleOne

def word (v : List ℕ) : A := (v.map (fun i => ExteriorAlgebra.ι ℤ (b i))).prod
def ev : OrderedChains.Chain ℕ →+ A := FreeAbelianGroup.lift word
@[simp] theorem ev_gen (v : List ℕ) : ev (OrderedChains.generator v) = word v := by
  simp [ev, OrderedChains.generator]
theorem ev_prepend (a : ℕ) (c : OrderedChains.Chain ℕ) :
    ev (OrderedChains.prepend a c) = ExteriorAlgebra.ι ℤ (b a) * ev c := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of v => simp [OrderedChains.prepend, ev, word]
  | neg c ih => simp [ih]
  | add c d ih jh => simp [ih, jh, mul_add]
theorem ev_relation {r : OrderedChains.Chain ℕ} (h : Raw.Relation r) : ev r = 0 := by
  induction h with
  | swap a c tail =>
    simp only [map_add, ev_gen, word, List.map_cons, List.prod_cons]
    rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]
  | duplicate a tail =>
    simp only [ev_gen, word, List.map_cons, List.prod_cons]
    rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
  | prepend a h ih => rw [ev_prepend, ih, mul_zero]
def witness : Total ℕ →+ A := QuotientAddGroup.lift (Raw.relations ℕ) ev (by
  intro r hr
  induction hr using AddSubgroup.closure_induction with
  | mem r hr => exact ev_relation hr
  | zero => exact ev.ker.zero_mem
  | add r s _ _ hr hs => exact ev.ker.add_mem hr hs
  | neg r _ hr => exact ev.ker.neg_mem hr)

def vertices (n : ℕ) : Fin n → ℕ :=
  Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (Finset.card_range n))

theorem witness_vertices (n : ℕ) : witness (simplex (List.ofFn (vertices n))) =
    b.ExteriorAlgebra (Finset.range n) := by
  change ev (OrderedChains.generator _) = _
  rw [ev_gen, ExteriorAlgebra.basis_apply_ofCard b (Finset.card_range n)]
  simp only [word, List.map_ofFn, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    vertices, Function.comp_def]

theorem fixed_degree_infinite_order (n : ℕ) (m : ℤ) (hm : m ≠ 0) :
    m • simplex (List.ofFn (vertices n)) ≠ 0 := by
  intro h
  have hh := congrArg (fun c => b.ExteriorAlgebra.repr (witness c) (Finset.range n)) h
  simp only [map_zsmul, map_zero, witness_vertices, Module.Basis.repr_self,
    Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_eq_same] at hh
  exact hm (by simpa using hh)

-- Coordinate insertion identity from source Exercise 19.
def e1 : Fin 3 → ℝ := ![1,0,0]
def e2 : Fin 3 → ℝ := ![0,1,0]
def e3 : Fin 3 → ℝ := ![0,0,1]
def q0 : Fin 2 → ℝ := 0
def q1 : Fin 2 → ℝ := ![1,0]
def q2 : Fin 2 → ℝ := ![1,1]
def q3 : Fin 2 → ℝ := ![0,1]
def insert1 (r : ℝ) (u : Fin 2 → ℝ) : Fin 3 → ℝ := ![r,u 0,u 1]
def insert2 (r : ℝ) (u : Fin 2 → ℝ) : Fin 3 → ℝ := ![u 0,r,u 1]
def insert3 (r : ℝ) (u : Fin 2 → ℝ) : Fin 3 → ℝ := ![u 0,u 1,r]
theorem map_square {E F : Type*} (f : E → F) (a b c d : E) :
    mapVertices f (square a b c d) = square (f a) (f b) (f c) (f d) := by
  simp [square]
theorem coordinate_face_signs :
    boundary (cube e1 e2 e3) =
      -(mapVertices (insert1 0) (square q0 q1 q2 q3) -
        mapVertices (insert1 1) (square q0 q1 q2 q3)) +
      (mapVertices (insert2 0) (square q0 q1 q2 q3) -
        mapVertices (insert2 1) (square q0 q1 q2 q3)) -
      (mapVertices (insert3 0) (square q0 q1 q2 q3) -
        mapVertices (insert3 1) (square q0 q1 q2 q3)) := by
  rw [boundary_cube]
  simp only [map_square]
  have h12 : e1 + e2 = ![1,1,0] := by ext i; fin_cases i <;> norm_num [e1,e2]
  have h13 : e1 + e3 = ![1,0,1] := by ext i; fin_cases i <;> norm_num [e1,e3]
  have h23 : e2 + e3 = ![0,1,1] := by ext i; fin_cases i <;> norm_num [e2,e3]
  have h123 : e1 + e2 + e3 = ![1,1,1] := by ext i; fin_cases i <;> norm_num [e1,e2,e3]
  rw [h123,h12,h13,h23]
  have h0 : (0 : Fin 3 → ℝ) = ![0,0,0] := by ext i; fin_cases i <;> rfl
  rw [h0]
  norm_num [insert1, insert2, insert3, q0, q1, q2, q3, e1, e2, e3]
  abel

-- In particular, edge/triangle/tetrahedron quotient equations are not vacuous.
theorem edge_nonzero : simplex (List.ofFn (vertices 2)) ≠ 0 := by
  simpa using fixed_degree_infinite_order 2 1 (by omega)
theorem triangle_nonzero : simplex (List.ofFn (vertices 3)) ≠ 0 := by
  simpa using fixed_degree_infinite_order 3 1 (by omega)
theorem tetrahedron_nonzero : simplex (List.ofFn (vertices 4)) ≠ 0 := by
  simpa using fixed_degree_infinite_order 4 1 (by omega)

-- A nonzero endpoint difference proves the path quotient has infinite-order paths.
theorem segment_nonzero : (Parametric.path (Parametric.segment (0 : ℝ) 1)) ≠ 0 := by
  intro h
  have hh := congrArg Parametric.pathBoundary h
  simp only [Parametric.pathBoundary_segment, map_zero] at hh
  have he : FreeAbelianGroup.of (1 : ℝ) = FreeAbelianGroup.of 0 := sub_eq_zero.mp hh
  have := FreeAbelianGroup.of_injective he
  norm_num at this

-- Repeated vertices need not be adjacent in order to vanish.
theorem nonadjacent_duplicate (a b : ℕ) : simplex [a,b,a] = 0 := by
  have h : simplex [a,b,a] = -simplex [b,a,a] := swap [] a b [a]
  simpa only [show simplex [b,a,a] = 0 from repeated [b] a [], neg_zero] using h

open Parametric

def height (c : PathChain (ℝ × ℝ × ℝ)) : ℝ :=
  (FreeAbelianGroup.lift (fun p : ℝ × ℝ × ℝ => p.2.2)) (pathBoundary c)

theorem height_path (p : Path (ℝ × ℝ × ℝ)) :
    height (path p) = (p 1).2.2 - (p 0).2.2 := by
  simp [height, pathBoundary_path]

theorem seam_height (δ : ℝ) : height (path (fun t => mobiusSquare δ (1,t))) = -2 * δ := by
  rw [height_path]
  norm_num [mobiusSquare, mobius]
  ring

theorem seam_retains_multiplicity (δ : ℝ) (hδ : δ ≠ 0) :
    (2 : ℤ) • path (fun t => mobiusSquare δ (1,t)) ≠
      path (fun t => mobiusSquare δ (1,t)) := by
  intro h
  have hh := congrArg height h
  change (FreeAbelianGroup.lift (fun p : ℝ × ℝ × ℝ => p.2.2))
      (pathBoundary ((2 : ℤ) • path (fun t => mobiusSquare δ (1,t)))) = _ at hh
  simp only [map_zsmul] at hh
  change (2 : ℤ) • height (path (fun t => mobiusSquare δ (1,t))) =
      height (path (fun t => mobiusSquare δ (1,t))) at hh
  rw [seam_height] at hh
  norm_num at hh
  exact hδ (by linarith)

end Rudin.Support.OrientedChainChecks
