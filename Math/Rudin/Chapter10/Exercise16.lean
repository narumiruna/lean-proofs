module

public import Math.Rudin.Support.OrientedChains
public import Math.Rudin.Support.SmoothChains

/-!
# Exercise 10.16

Source: book page 291 (PDF 300). Definitions 10.26–10.30 are on
book pages 266–270 (PDF 275–279). `realize_cartesian` is formula (76),
`realize_face` is restriction to a face, and `boundary_ofFn` is (85).
The ordered proof uses `∂(a*c) = c - a*∂c`: in its second application
both copies of each deleted pair cancel. This holds before the orientation
quotient, so it also holds after the quotient. Additivity gives the chain law.
The empty generator belongs only to the augmented model. The ordinary
boundary of a zero-chain is zero, not that generator.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise16
open Rudin.Support Rudin.Support.OrientedChains

/-- The recursive cancellation is exactly the alternating deletion formula. -/
theorem source_boundary {E : Type*} {k : ℕ} (v : Fin (k + 2) → E) :
    boundary (simplex (List.ofFn v)) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ i.val • simplex (List.ofFn (v ∘ i.succAbove)) :=
  boundary_ofFn v

/-- Cancellation of the twice-occurring deleted faces, before quotienting. -/
theorem deleted_pairs_cancel {E : Type*} (v : List E) :
    OrderedChains.boundary (∑ i ∈ Finset.range v.length,
      (-1 : ℤ) ^ i • OrderedChains.generator (v.eraseIdx i)) = 0 := by
  rw [← OrderedChains.boundaryWord_eq_sum]
  exact OrderedChains.boundary_boundaryWord v

/-- A simplex of dimension at least two has zero second boundary. -/
theorem simplex_boundary_squared {E : Type*} {k : ℕ} (v : Fin (k + 3) → E) :
    chainBoundary k (chainBoundary (k + 1) (ofVertices v)) = 0 :=
  chainBoundary_squared k _

/-- The same cancellation applies to every fixed-dimensional signed chain. -/
theorem chain_boundary_squared {E : Type*} (k : ℕ) (c : Chain E (k + 2)) :
    chainBoundary k (chainBoundary (k + 1) c) = 0 := chainBoundary_squared k c

/-- This includes dimension one: its next boundary is the ordinary zero map. -/
theorem ordinary_second_boundary {E : Type*} (k : ℕ) (c : Chain E (k + 1)) :
    ordinaryBoundary k (chainBoundary k c) = 0 := by
  cases k with
  | zero => exact ordinaryBoundary_zero _
  | succ k =>
    rw [ordinaryBoundary_succ]
    exact boundary_squared c.val

/-- No augmentation is used for zero-chains. -/
theorem zero_chain_boundary {E : Type*} (c : Chain E 0) :
    ordinaryBoundary 0 c = 0 := ordinaryBoundary_zero c

/-- Actual parameter faces, not just lists, have the required vertex deletion. -/
theorem source_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (v : Fin (k + 2) → E) (i : Fin (k + 2)) (w : Parameters (k + 1)) :
    realize v (face i w) = realize (v ∘ i.succAbove) w := realize_face v i w

/-- Every closed barycentric parameter comes from the source's Cartesian
parameter simplex, including parameters on its boundary. -/
theorem barycentric_surjective (k : ℕ) :
    Function.Surjective (barycentric (k := k)) := by
  intro w
  have hs := w.property.2
  rw [Fin.sum_univ_succ] at hs
  let u : CartesianParameters k := ⟨fun i => w.val i.succ, by
    constructor
    · intro i; exact w.property.1 i.succ
    · have h0 := w.property.1 0; linarith⟩
  refine ⟨u, ?_⟩
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [barycentric, Fin.cons_zero, u]
    linarith
  · rfl

/-- Exact range comparison with formula (76), rather than a different
parameter domain with only an informal identification. -/
theorem source_range {E : Type*} [AddCommGroup E] [Module ℝ E]
    {k : ℕ} (v : Fin (k + 1) → E) :
    Set.range (fun u : CartesianParameters k =>
      v 0 + ∑ i, u.val i • (v i.succ - v 0)) = Set.range (realize v) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨barycentric u, realize_cartesian v u⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨u, rfl⟩ := barycentric_surjective k w
    exact ⟨u, (realize_cartesian v u).symm⟩

/- The source also permits differentiable chains. Boundary cancellation is
purely algebraic on their full maps, so no C² assumption is imposed below.
The Euclidean face maps come from the frozen `SmoothChains` interface, but
its C² simplex subtype is deliberately not used for these generators. -/
namespace Parameterized

abbrev Param := SmoothChains.Param
abbrev Chain (n : ℕ) (E : Type*) := FreeAbelianGroup (Param n → E)

variable {E F : Type*}

/-- Restriction of the complete map, including its behavior between vertices. -/
def face {n : ℕ} (S : Param (n + 1) → E) (i : Fin (n + 2)) : Param n → E :=
  S ∘ SmoothChains.relabel i.succAbove

/-- Formula (85), with each face interpreted by source formula (89). -/
def boundary (n : ℕ) : Chain (n + 1) E →+ Chain n E :=
  FreeAbelianGroup.lift fun S =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • FreeAbelianGroup.of (face S i)

@[simp] theorem boundary_generator {n : ℕ} (S : Param (n + 1) → E) :
    boundary n (FreeAbelianGroup.of S) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • FreeAbelianGroup.of (face S i) := by
  simp [boundary]

/-- The two deletion orders give identical full maps, not merely equal vertices. -/
theorem face_face {n : ℕ} (S : Param (n + 2) → E)
    (j : Fin (n + 3)) (i : Fin (n + 2)) :
    face (face S j) i = face (face S (j.succAbove i)) (i.predAbove j) := by
  funext u
  simp only [face, Function.comp_apply, SmoothChains.relabel_comp]
  congr 2
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove j i k).symm

/-- Pair the two orders of deletion. Their coefficients are opposite.
Integer linearity then gives cancellation for every source chain, with no
regularity hypothesis beyond those needed to call its maps differentiable. -/
theorem boundary_squared (n : ℕ) (c : Chain (n + 2) E) :
    boundary n (boundary (n + 1) c) = 0 := by
  have h : (boundary n).comp (boundary (n + 1)) =
      (0 : Chain (n + 2) E →+ Chain n E) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change boundary n (boundary (n + 1) (FreeAbelianGroup.of S)) = 0
    simp only [boundary_generator, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_product', Finset.univ_product_univ]
    refine Finset.sum_involution (s := Finset.univ)
      (fun (p : Fin (n + 3) × Fin (n + 2)) _ =>
        (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
    · intro p _
      rw [face_face, SmoothChains.deletion_sign p.1 p.2, neg_smul, neg_add_cancel]
    · intro p _ _ he
      exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst he)
    · intro _ _; exact Finset.mem_univ _
    · intro p _
      exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
        (Fin.predAbove_predAbove_succAbove p.1 p.2)
  exact DFunLike.congr_fun h c

/-- Degree zero has zero boundary; there is no augmentation. -/
def ordinaryBoundary : (n : ℕ) → Chain n E →+ Chain (n - 1) E :=
  Nat.rec (motive := fun n => Chain n E →+ Chain (n - 1) E) 0 (fun n _ => boundary n)

@[simp] theorem ordinaryBoundary_zero (c : Chain 0 E) : ordinaryBoundary 0 c = 0 := rfl

theorem ordinaryBoundary_squared (n : ℕ) (c : Chain n E) :
    ordinaryBoundary (n - 1) (ordinaryBoundary n c) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact boundary_squared n c

/-- Arbitrary postcomposition acts on whole maps, not their vertex images. -/
def map (n : ℕ) (T : E → F) : Chain n E →+ Chain n F :=
  FreeAbelianGroup.map fun S => T ∘ S

theorem boundary_map (n : ℕ) (T : E → F) (c : Chain (n + 1) E) :
    boundary n (map (n + 1) T c) = map n T (boundary n c) := by
  have h : (boundary n).comp (map (n + 1) T) = (map n T).comp (boundary n) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp [boundary, map, face, Function.comp_def]
  exact DFunLike.congr_fun h c

theorem boundary_multiplicity (n : ℕ) (z : ℤ) (c : Chain (n + 1) E) :
    boundary n (z • c) = z • boundary n c := map_zsmul _ _ _

/-- Exact source comparison for `Φ = T ∘ [p₀,...,pₖ]`: the face is `T`
composed with the affine map having the deleted vertex list. No regularity
of `T` is needed for this identity, so C¹ source maps are included. -/
theorem source_face [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (T : E → F) (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    face (T ∘ (SmoothChains.affine v).val) i =
      T ∘ (SmoothChains.affine (v ∘ i.succAbove)).val := by
  have h := congrArg Subtype.val (SmoothChains.affine_face v i)
  exact congrArg (fun f => T ∘ f) h

/-- Formula (76) is valid on the entire Euclidean parameter space. -/
theorem source_map [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (T : E → F) (v : Fin (n + 1) → E) (u : Param n) :
    (T ∘ (SmoothChains.affine v).val) u =
      T (v 0 + ∑ i, u i • (v i.succ - v 0)) := by
  rw [Function.comp_apply, SmoothChains.affine_formula]

/-- All source parameter faces stay in the closed standard simplex. -/
theorem face_domain {n : ℕ} (i : Fin (n + 2)) {u : Param n}
    (hu : u ∈ SimplexIntegration.standardSimplex n) :
    SmoothChains.relabel i.succAbove u ∈ SimplexIntegration.standardSimplex (n + 1) :=
  SmoothChains.relabel_mem _ hu

end Parameterized

end Rudin.Chapter10.Exercise16
