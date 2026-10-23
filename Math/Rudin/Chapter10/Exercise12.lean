module

public import Math.Rudin.Support.MultivariateRiemann
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Interval.Finset.Fin

/-! # Chapter 10, Exercise 12
The stick-breaking map uses the source coordinate order. Products and sums
below an index are empty for its first coordinate.
-/

@[expose] public section
noncomputable section
namespace Rudin.Chapter10.Exercise12

open Set Finset
open Rudin.Support.MultivariateRiemann

/-- The actual polynomial stick-breaking map. -/
def T {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  u i * ∏ j ∈ Finset.Iio i, (1 - u j)

/-- The exact partial-sum denominator. -/
def remainder {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 - ∑ j ∈ Finset.Iio i, x j

/-- Division is total; on a collapsed boundary fiber we choose zero. -/
def S {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ := x i / remainder x i

def openCube (n : ℕ) : Set (Fin n → ℝ) := {u | ∀ i, 0 < u i ∧ u i < 1}
def openSimplex (n : ℕ) : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

/-- The coordinate-sum identity, with dimension zero included. -/
theorem coordinate_sum {n : ℕ} (u : Fin n → ℝ) :
    ∑ i, T u i = 1 - ∏ i, (1 - u i) := by
  have h := Finset.prod_one_sub_ordered Finset.univ u
  simp only [Finset.filter_gt_eq_Iio] at h
  dsimp [T]
  linarith

/-- The same telescoping identity for each strict initial segment. -/
theorem prefix_sum {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.Iio i, T u j = 1 - ∏ j ∈ Finset.Iio i, (1 - u j) := by
  have h := Finset.prod_one_sub_ordered (Finset.Iio i) u
  have hf (j : Fin n) (hj : j ∈ Finset.Iio i) :
      {k ∈ Finset.Iio i | k < j} = Finset.Iio j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Iio]
    exact ⟨fun h => h.2, fun h => ⟨lt_trans h (Finset.mem_Iio.mp hj), h⟩⟩
  have he : (∑ j ∈ Finset.Iio i, u j * ∏ k ∈ Finset.Iio i with k < j, (1-u k)) =
      ∑ j ∈ Finset.Iio i, T u j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf j hj]
    rfl
  rw [he] at h
  linarith

theorem remainder_T {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    remainder (T u) i = ∏ j ∈ Finset.Iio i, (1-u j) := by
  rw [remainder, prefix_sum]
  ring

/-- All partial denominators dominate the corresponding simplex coordinate. -/
theorem coordinate_le_remainder {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ piSimplex n)
    (i : Fin n) : x i ≤ remainder x i := by
  have hsum : (∑ j ∈ Finset.Iio i, x j) + x i ≤ ∑ j, x j := by
    rw [add_comm, ← Finset.sum_insert (show i ∉ Finset.Iio i by simp)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hx.1 j)
  dsimp [remainder]
  linarith [hx.2]

/-- The explicit inverse is defined even on closed boundary faces. -/
theorem S_mem_cube {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ piSimplex n) :
    S x ∈ Set.Icc 0 1 := by
  constructor <;> intro i
  · exact div_nonneg (hx.1 i) (le_trans (hx.1 i) (coordinate_le_remainder hx i))
  · dsimp [S]
    by_cases h : remainder x i = 0
    · simp [h]
    · exact (div_le_one (lt_of_le_of_ne
        (le_trans (hx.1 i) (coordinate_le_remainder hx i)) (Ne.symm h))).mpr
        (coordinate_le_remainder hx i)

/-- The total inverse formula is a right inverse on the entire closed simplex. -/
theorem T_S {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ piSimplex n) : T (S x) = x := by
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hp : (∏ j ∈ Finset.Iio i, (1 - S x j)) = remainder x i := by
      rw [← remainder_T]
      unfold remainder
      congr 1
      exact Finset.sum_congr rfl (fun j hj => ih j (Finset.mem_Iio.mp hj))
    rw [T, hp, S]
    by_cases h : remainder x i = 0
    · have hx0 : x i = 0 := le_antisymm (by simpa [h] using coordinate_le_remainder hx i) (hx.1 i)
      simp [h, hx0]
    · exact div_mul_cancel₀ _ h

/-- The polynomial maps the closed cube into the closed simplex. -/
theorem T_mem_simplex {n : ℕ} {u : Fin n → ℝ} (hu : u ∈ Set.Icc 0 1) :
    T u ∈ piSimplex n := by
  constructor
  · intro i
    exact mul_nonneg (hu.1 i) (Finset.prod_nonneg (fun j _ => sub_nonneg.mpr (hu.2 j)))
  · rw [coordinate_sum]
    have h : 0 ≤ ∏ i, (1-u i) := Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hu.2 i))
    linarith

/-- Surjectivity is on closed sets, including all collapsed boundary fibers. -/
theorem surjectivity (n : ℕ) : T '' (Set.Icc (0 : Fin n → ℝ) 1) = piSimplex n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact T_mem_simplex hu
  · intro x hx
    exact ⟨S x, S_mem_cube hx, T_S hx⟩

/-- On the open cube, the exact partial-sum inverse recovers every coordinate. -/
theorem S_T {n : ℕ} {u : Fin n → ℝ} (hu : u ∈ openCube n) : S (T u) = u := by
  funext i
  rw [S, remainder_T, T]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Finset.prod_pos (fun j _ => sub_pos.mpr (hu j).2)))

theorem interior_injectivity (n : ℕ) : Set.InjOn (@T n) (openCube n) := by
  intro u hu v hv h
  rw [← S_T hu, ← S_T hv, h]

/-- Strict positivity of every denominator follows from the simplex inequality. -/
theorem remainder_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ openSimplex n) (i : Fin n) :
    0 < remainder x i := by
  have h : (∑ j ∈ Finset.Iio i, x j) ≤ ∑ j, x j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => (hx.1 j).le)
  dsimp [remainder]
  linarith [hx.2]

theorem T_mem_openSimplex {n : ℕ} {u : Fin n → ℝ} (hu : u ∈ openCube n) :
    T u ∈ openSimplex n := by
  constructor
  · intro i
    exact mul_pos (hu i).1 (Finset.prod_pos (fun j _ => sub_pos.mpr (hu j).2))
  · rw [coordinate_sum]
    have h : 0 < ∏ i, (1-u i) := Finset.prod_pos (fun i _ => sub_pos.mpr (hu i).2)
    linarith

theorem S_mem_openCube {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ openSimplex n) :
    S x ∈ openCube n := by
  intro i
  refine ⟨div_pos (hx.1 i) (remainder_pos hx i), (div_lt_one (remainder_pos hx i)).mpr ?_⟩
  have hsum : (∑ j ∈ Finset.Iio i, x j) + x i ≤ ∑ j, x j := by
    rw [add_comm, ← Finset.sum_insert (show i ∉ Finset.Iio i by simp)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => (hx.1 j).le)
  dsimp [remainder]
  linarith [hx.2]

/-- The inverse on the interiors, with its formula and both compositions. -/
theorem interior_inverse {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ openSimplex n) :
    S x ∈ openCube n ∧ T (S x) = x ∧
      ∀ i, S x i = x i / (1 - ∑ j ∈ Finset.Iio i, x j) := by
  exact ⟨S_mem_openCube hx, T_S ⟨fun i => (hx.1 i).le, hx.2.le⟩, fun _ => rfl⟩

/-- The genuine Fréchet derivative of the polynomial map. -/
def DT {n : ℕ} (u : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    u i • (∑ k ∈ Finset.Iio i,
      (∏ j ∈ (Finset.Iio i).erase k, (1-u j)) • (-ContinuousLinearMap.proj k)) +
    (∏ j ∈ Finset.Iio i, (1-u j)) • ContinuousLinearMap.proj i

theorem hasFDerivAt_T {n : ℕ} (u : Fin n → ℝ) : HasFDerivAt T (DT u) u := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (ContinuousLinearMap.proj i).hasFDerivAt.mul
    (HasFDerivAt.finsetProd (fun j _ => (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.const_sub (1 : ℝ)))

/-- The genuine Fréchet derivative of the partial-sum inverse. -/
def DS {n : ℕ} (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    x i • (-(remainder x i ^ 2)⁻¹ • (-(∑ j ∈ Finset.Iio i, ContinuousLinearMap.proj j))) +
    (remainder x i)⁻¹ • ContinuousLinearMap.proj i

theorem hasFDerivAt_S {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ openSimplex n) :
    HasFDerivAt S (DS x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hr : HasFDerivAt (fun x : Fin n → ℝ => remainder x i)
      (-(∑ j ∈ Finset.Iio i, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) x := by
    simpa [remainder] using
      (HasFDerivAt.sum (u := Finset.Iio i) (x := x) (fun j _ =>
        (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt)).const_sub (1 : ℝ)
  simpa only [S, div_eq_mul_inv, Function.comp_def, Pi.mul_def,
    ContinuousLinearMap.proj_apply] using
    (ContinuousLinearMap.proj i).hasFDerivAt.mul
      ((hasDerivAt_inv (ne_of_gt (remainder_pos hx i))).comp_hasFDerivAt x hr)

/-- The upper off-diagonal entries and diagonal of the forward derivative. -/
theorem DT_entry {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) (hij : i ≤ j) :
    DT u (Pi.single j 1) i = if i = j then ∏ k ∈ Finset.Iio i, (1-u k) else 0 := by
  have hs : (∑ k ∈ Finset.Iio i,
      (∏ l ∈ (Finset.Iio i).erase k, (1-u l)) * -((Pi.single j (1 : ℝ) : Fin n → ℝ) k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := ne_of_lt (lt_of_lt_of_le (Finset.mem_Iio.mp hk) hij)
    simp [hkj]
  simp only [DT, ContinuousLinearMap.pi_apply, _root_.add_apply,
    _root_.smul_apply, _root_.sum_apply, _root_.neg_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, hs, mul_zero, zero_add]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

/-- The corresponding entries of the inverse derivative. -/
theorem DS_entry {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (hij : i ≤ j) :
    DS x (Pi.single j 1) i = if i = j then (remainder x i)⁻¹ else 0 := by
  have hs : (∑ k ∈ Finset.Iio i, (Pi.single j (1 : ℝ) : Fin n → ℝ) k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : k ≠ j := ne_of_lt (lt_of_lt_of_le (Finset.mem_Iio.mp hk) hij)
    simp [hkj]
  simp only [DS, ContinuousLinearMap.pi_apply, _root_.add_apply,
    _root_.smul_apply, _root_.sum_apply, _root_.neg_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, hs, neg_zero, mul_zero, zero_add]
  by_cases h : i = j
  · subst j; simp
  · simp [h]

/-- Counting each factor gives the exponents in the source Jacobian. -/
theorem prefix_product {n : ℕ} (u : Fin n → ℝ) :
    (∏ i, ∏ j ∈ Finset.Iio i, (1-u j)) = ∏ j, (1-u j) ^ (n - 1 - j.val) := by
  simp_rw [← Finset.filter_gt_eq_Iio, Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_filter]
  have he : (Finset.univ.filter fun i : Fin n => j < i) = Finset.Ioi j := by ext i; simp
  rw [he, Finset.prod_const, Fin.card_Ioi]

/-- The determinant is that of the actual derivative, not a formal triangular array. -/
theorem forward_jacobian {n : ℕ} (u : Fin n → ℝ) :
    LinearMap.det (fderiv ℝ T u).toLinearMap = ∏ i, (1-u i) ^ (n - 1 - i.val) := by
  rw [(hasFDerivAt_T u).fderiv, ← LinearMap.det_toMatrix']
  have ht : (LinearMap.toMatrix' (DT u).toLinearMap).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [DT_entry u i j (le_of_lt hij)]
    simp [ne_of_lt hij]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, DT_entry u _ _ le_rfl, ite_true]
  exact prefix_product u

/-- The inverse determinant is the reciprocal of the exact partial-sum product.
The first denominator is one, so this is the source product through `n-1`. -/
theorem inverse_jacobian {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ openSimplex n) :
    LinearMap.det (fderiv ℝ S x).toLinearMap =
      (∏ i, (1 - ∑ j ∈ Finset.Iio i, x j))⁻¹ := by
  rw [(hasFDerivAt_S hx).fderiv, ← LinearMap.det_toMatrix']
  have ht : (LinearMap.toMatrix' (DS x).toLinearMap).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
    rw [DS_entry x i j (le_of_lt hij)]
    simp [ne_of_lt hij]
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, DS_entry x _ _ le_rfl, ite_true,
    remainder, Finset.prod_inv_distrib]

/-- The strict coordinate cube is the topological interior of the closed cube. -/
theorem openCube_eq_interior (n : ℕ) : openCube n = interior (Set.Icc (0 : Fin n → ℝ) 1) := by
  rw [← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  ext u
  simp [openCube, interior_Icc]

/-- The strict simplex inequalities describe its actual topological interior. -/
theorem openSimplex_eq_interior (n : ℕ) : openSimplex n = interior (piSimplex n) := by
  apply Set.Subset.antisymm
  · have hopen : IsOpen (openSimplex n) := by
      have he : openSimplex n = (⋂ i : Fin n, {x : Fin n → ℝ | 0 < x i}) ∩
          {x | ∑ i, x i < 1} := by ext x; simp [openSimplex]
      rw [he]
      exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (by fun_prop) continuous_const)
    apply hopen.subset_interior_iff.mpr
    intro x hx
    exact ⟨fun i => (hx.1 i).le, hx.2.le⟩
  · intro x hx
    have hcube : x ∈ openCube n := by
      rw [openCube_eq_interior]
      exact interior_mono (piSimplex_subset_cube n) hx
    refine ⟨fun i => (hcube i).1, ?_⟩
    cases n with
    | zero => simp
    | succ n =>
      obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
      have hy : x + Pi.single (0 : Fin (n+1)) (ε/2) ∈ piSimplex (n+1) := by
        apply hb
        simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single,
          Real.norm_eq_abs, abs_of_pos (half_pos hε)]
        linarith
      have hs := hy.2
      simp only [Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single'] at hs
      linarith

/-- The source injectivity statement on the literal interior. -/
theorem injective_on_interior (n : ℕ) :
    Set.InjOn (@T n) (interior (Set.Icc (0 : Fin n → ℝ) 1)) := by
  rw [← openCube_eq_interior]
  exact interior_injectivity n

end Rudin.Chapter10.Exercise12
