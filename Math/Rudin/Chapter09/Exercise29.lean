module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic

/-! # Exercise 29: permutation of coordinate derivatives

Coordinate derivatives are successive actual Fréchet derivatives evaluated on
coordinate vectors. The regularity and derivative-existence lemmas precede the
permutation theorem. Its proof uses the adjacent transpositions in `List.Perm`
and the equality of continuous mixed second derivatives, not an assumed
symmetric higher differential.
-/

@[expose] public section
open Set Filter
open scoped Topology
namespace Rudin.Chapter09

abbrev CoordinateSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def coordinateVector {n : ℕ} (i : Fin n) : CoordinateSpace n :=
  EuclideanSpace.single i 1

noncomputable def coordinatePartial {n : ℕ} (i : Fin n)
    (f : CoordinateSpace n → ℝ) (a : CoordinateSpace n) : ℝ :=
  fderiv ℝ f a (coordinateVector i)

noncomputable def mixedPartial {n : ℕ} : List (Fin n) →
    (CoordinateSpace n → ℝ) → CoordinateSpace n → ℝ
  | [], f => f
  | i :: l, f => coordinatePartial i (mixedPartial l f)

/-- Every intermediate partial has the remaining source regularity. -/
theorem mixedPartial_contDiffOn {n m r : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (l : List (Fin n)) (h : l.length + r ≤ m) :
    ContDiffOn ℝ r (mixedPartial l f) E := by
  induction l generalizing r with
  | nil => exact hf.of_le (by exact_mod_cast (show r ≤ m by simpa using h))
  | cons i l ih =>
    have hg := ih (r := r + 1) (by simpa [List.length_cons, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h)
    exact (hg.fderiv_of_isOpen hE (by simp)).clm_apply contDiffOn_const

/-- The total derivative in the recursive definition is an existing derivative. -/
theorem mixedPartial_hasFDerivAt {n m : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (l : List (Fin n)) (hl : l.length < m) {a : CoordinateSpace n} (ha : a ∈ E) :
    HasFDerivAt (mixedPartial l f) (fderiv ℝ (mixedPartial l f) a) a :=
  ((mixedPartial_contDiffOn hE hf l (r := 1) (by omega)).contDiffAt
    (hE.mem_nhds ha)).differentiableAt (by norm_num) |>.hasFDerivAt

/-- Each coordinate partial is also the ordinary one-variable partial. -/
theorem mixedPartial_hasDerivAt {n m : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    (l : List (Fin n)) (hl : l.length < m) {a : CoordinateSpace n} (ha : a ∈ E)
    (i : Fin n) :
    HasDerivAt (fun t : ℝ => mixedPartial l f (a + t • coordinateVector i))
      (mixedPartial (i :: l) f a) 0 := by
  have hp : HasDerivAt (fun t : ℝ => a + t • coordinateVector i) (coordinateVector i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add a
  simpa only [mixedPartial, coordinatePartial, Function.comp_def] using
    (show HasFDerivAt (mixedPartial l f) (fderiv ℝ (mixedPartial l f) a)
      (a + (0 : ℝ) • coordinateVector i) by
        simpa using mixedPartial_hasFDerivAt hE hf l hl ha).comp_hasDerivAt 0 hp

/-- Equality of the two continuous mixed second partials. -/
theorem coordinatePartial_comm {n : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {g : CoordinateSpace n → ℝ} (hg : ContDiffOn ℝ 2 g E)
    {a : CoordinateSpace n} (ha : a ∈ E) (i j : Fin n) :
    coordinatePartial i (coordinatePartial j g) a =
      coordinatePartial j (coordinatePartial i g) a := by
  have hc := hg.contDiffAt (hE.mem_nhds ha)
  have hd := (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  change fderiv ℝ (fun z => fderiv ℝ g z (coordinateVector j)) a (coordinateVector i) =
    fderiv ℝ (fun z => fderiv ℝ g z (coordinateVector i)) a (coordinateVector j)
  simp only [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact hc.isSymmSndFDerivAt (by norm_num) _ _

/-- Exercise 29. Adjacent swaps generate all permutations, including repeated indices. -/
theorem exercise29_permutation_invariance {n m : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ m f E)
    {l q : List (Fin n)} (hp : l.Perm q) (hl : l.length ≤ m) :
    EqOn (mixedPartial l f) (mixedPartial q f) E := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | @cons i l q hp ih =>
    intro a ha
    have he := ih (by simpa using Nat.le_of_succ_le hl)
    have he' : mixedPartial l f =ᶠ[𝓝 a] mixedPartial q f :=
      Filter.mem_of_superset (hE.mem_nhds ha) he
    exact congrArg (fun L : CoordinateSpace n →L[ℝ] ℝ => L (coordinateVector i))
      he'.fderiv_eq
  | swap i j l =>
    intro a ha
    exact coordinatePartial_comm hE
      (mixedPartial_contDiffOn hE hf l (r := 2) (by simpa only [List.length_cons] using hl)) ha j i
  | @trans l q r hp hq ih₁ ih₂ =>
    exact fun a ha => (ih₁ hl ha).trans (ih₂ (hp.length_eq ▸ hl) ha)

/-- The ordered-tuple form of Exercise 29. No injectivity of the indices is required. -/
theorem exercise29_ordered_permutation {n k : ℕ} {E : Set (CoordinateSpace n)}
    (hE : IsOpen E) {f : CoordinateSpace n → ℝ} (hf : ContDiffOn ℝ k f E)
    (i : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) {a : CoordinateSpace n} (ha : a ∈ E) :
    mixedPartial (List.ofFn (i ∘ σ)) f a = mixedPartial (List.ofFn i) f a := by
  exact exercise29_permutation_invariance hE hf (σ.ofFn_comp_perm i)
    (by simp) ha

end Rudin.Chapter09
