module

public import Math.Rudin.Support.MultivariateRiemann
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Genuine smooth simplex chains

Sources: Rudin 10.26–10.35 and Exercises 10.16–10.19/10.32 (PDF pages
275–285, 300–301, 307–308). Parameters use the actual Euclidean spaces.

A generator is a full Cartesian map with a proof that it is C² on some open
neighborhood of the closed simplex. Neighborhood choices are not generator
data. Affine parameter maps transport barycentric weights. Face cancellation
is proved on these full maps before quotienting. The orientation quotient
imposes only permutation relations; boundary descent precedes its public sign
API. Auxiliary vertex determinants test nontriviality; they do not define chain
equality or nonlinear postcomposition.

This is formal chain infrastructure, not the quotient by all form-integration
functionals. In particular, no repeated-vertex or torsion-free normalization is
imposed. The affine comparison starts from ordered fixed-degree vertex chains,
not the stronger repeated-vertex quotient in `OrientedChains`. Raw integration
has actual pullback coefficients and source Riemann witnesses in every degree.
Integration descent is proved here in degree one only. Higher-degree descent,
square integral subdivision, higher Stokes, and neighborhood-only form Stokes
remain open. No exercise-completion claim is made.
-/

@[expose] public section
noncomputable section
namespace Rudin.Support.SmoothChains
open Set SimplexIntegration

abbrev Param (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Barycentric coordinates of the full Cartesian parameter space. -/
def weights {n : ℕ} (u : Param n) : Fin (n+1) → ℝ :=
  Fin.cons (1 - ∑ i, u i) (fun i => u i)

@[simp] theorem sum_weights {n : ℕ} (u : Param n) : ∑ i, weights u i = 1 := by
  simp [weights, Fin.sum_univ_succ]

/-- Sum coordinates along a map of finite vertex sets. -/
def transport {n m : ℕ} (f : Fin n → Fin m) (w : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, if f i = j then w i else 0

@[simp] theorem sum_transport {n m : ℕ} (f : Fin n → Fin m) (w : Fin n → ℝ) :
    ∑ j, transport f w j = ∑ i, w i := by
  classical
  simp only [transport]
  rw [Finset.sum_comm]
  simp

@[simp] theorem transport_id {n : ℕ} (w : Fin n → ℝ) : transport id w = w := by
  classical
  funext j
  simp [transport]

theorem transport_comp {n m k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k)
    (w : Fin n → ℝ) : transport g (transport f w) = transport (g ∘ f) w := by
  classical
  funext j
  simp only [transport]
  have aux (b : Fin m) :
      (if g b = j then ∑ i, if f i = b then w i else 0 else 0) =
      ∑ i, if g b = j then (if f i = b then w i else 0) else 0 := by
    split_ifs <;> simp
  simp_rw [aux]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hx (b : Fin m) :
      (if g b = j then (if f i = b then w i else 0) else 0) =
      (if f i = b then (if g (f i) = j then w i else 0) else 0) := by
    by_cases h : f i = b
    · subst b; simp
    · simp [h]
  simp_rw [hx]
  simp

/-- The affine parameter map induced by a vertex map, not a target vertex map. -/
def relabel {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (u : Param n) : Param m :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun j => transport f (weights u) j.succ)

@[simp] theorem relabel_apply {n m : ℕ} (f : Fin (n+1) → Fin (m+1))
    (u : Param n) (j : Fin m) : relabel f u j = transport f (weights u) j.succ := rfl

@[simp] theorem weights_relabel {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (u : Param n) :
    weights (relabel f u) = transport f (weights u) := by
  funext i
  refine Fin.cases ?_ (fun j => rfl) i
  have h := sum_transport f (weights u)
  rw [sum_weights, Fin.sum_univ_succ] at h
  change 1 - ∑ j : Fin m, transport f (weights u) j.succ = transport f (weights u) 0
  linarith

@[simp] theorem relabel_id {n : ℕ} (u : Param n) : relabel id u = u := by
  ext j
  simp [weights]

@[simp] theorem relabel_comp {n m k : ℕ} (f : Fin (n+1) → Fin (m+1))
    (g : Fin (m+1) → Fin (k+1)) (u : Param n) :
    relabel g (relabel f u) = relabel (g ∘ f) u := by
  ext j
  simp [transport_comp]

theorem relabel_smooth {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) :
    ContDiff ℝ 2 (relabel f) := by
  classical
  apply (EuclideanSpace.equiv (Fin m) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro j
  unfold transport weights
  apply ContDiff.sum
  intro i _
  split_ifs
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.cons_zero]
      exact contDiff_const.sub (ContDiff.sum (fun k _ => (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff))
    · simp only [Fin.cons_succ]
      exact (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff
  · exact contDiff_const

theorem mem_simplex_iff_weights {n : ℕ} (u : Param n) :
    u ∈ standardSimplex n ↔ ∀ i, 0 ≤ weights u i := by
  simp only [standardSimplex, mem_ofPred_eq, weights, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, sub_nonneg]
  tauto

theorem relabel_mem {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) {u : Param n}
    (hu : u ∈ standardSimplex n) : relabel f u ∈ standardSimplex m := by
  rw [mem_simplex_iff_weights, weights_relabel]
  intro j
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (mem_simplex_iff_weights u).mp hu i
  · exact le_rfl

/-- C² on some open neighborhood; the neighborhood is proof data only. -/
def Regular {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Param n → E) : Prop :=
  ∃ U, IsOpen U ∧ standardSimplex n ⊆ U ∧ ContDiffOn ℝ 2 f U

/-- Full parameter maps, not vertex tuples or ranges. -/
abbrev Simplex (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {f : Param n → E // Regular f}

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace Simplex

/-- Forget the choice of neighborhood in the existing integration structure. -/
def ofSmooth {n : ℕ} (S : SmoothSimplex n E) : Simplex n E :=
  ⟨S.toFun, S.neighborhood, S.isOpen_neighborhood, S.contains, S.smooth⟩

/-- Choose a neighborhood only when the existing integration API requires it. -/
def toSmooth {n : ℕ} (S : Simplex n E) : SmoothSimplex n E where
  toFun := S.val
  neighborhood := S.property.choose
  isOpen_neighborhood := S.property.choose_spec.1
  contains := S.property.choose_spec.2.1
  smooth := S.property.choose_spec.2.2

@[simp] theorem ofSmooth_toSmooth {n : ℕ} (S : Simplex n E) : ofSmooth S.toSmooth = S := rfl

/-- Restriction by an affine parameter map, on its open preimage neighborhood. -/
def reparam {n m : ℕ} (S : Simplex m E) (f : Fin (n+1) → Fin (m+1)) : Simplex n E :=
  ⟨S.val ∘ relabel f, by
    obtain ⟨U, ho, hs, hd⟩ := S.property
    exact ⟨relabel f ⁻¹' U, ho.preimage (relabel_smooth f).continuous,
      fun _ hu => hs (relabel_mem f hu), hd.comp (relabel_smooth f).contDiffOn
        (fun _ hu => hu)⟩⟩

@[simp] theorem reparam_val {n m : ℕ} (S : Simplex m E) (f : Fin (n+1) → Fin (m+1)) :
    (S.reparam f).val = S.val ∘ relabel f := rfl

@[simp] theorem reparam_comp {n m k : ℕ} (S : Simplex k E)
    (f : Fin (n+1) → Fin (m+1)) (g : Fin (m+1) → Fin (k+1)) :
    (S.reparam g).reparam f = S.reparam (g ∘ f) := by
  apply Subtype.ext
  funext u
  simp [Function.comp_def]

@[simp] theorem reparam_id {n : ℕ} (S : Simplex n E) : S.reparam id = S := by
  apply Subtype.ext
  funext u
  simp

/-- Every face is a restriction of the full map. -/
def face {n : ℕ} (S : Simplex (n+1) E) (i : Fin (n+2)) : Simplex n E :=
  S.reparam i.succAbove

/-- Postcomposition needs C² only on an open set containing the simplex image. -/
def mapOn {n : ℕ} (S : Simplex n E) (f : E → F) (V : Set E) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (hS : MapsTo S.val (standardSimplex n) V) : Simplex n F :=
  ⟨f ∘ S.val, by
    obtain ⟨U, ho, hs, hd⟩ := S.property
    refine ⟨U ∩ S.val ⁻¹' V, ?_, fun u hu => ⟨hs hu, hS hu⟩, ?_⟩
    · exact hd.continuousOn.isOpen_inter_preimage ho hV
    · exact hf.comp (hd.mono inter_subset_left) (fun _ hu => hu.2)⟩

/-- Global C² postcomposition is a convenient special case. -/
def map {n : ℕ} (S : Simplex n E) (f : E → F) (hf : ContDiff ℝ 2 f) : Simplex n F :=
  S.mapOn f univ isOpen_univ hf.contDiffOn (fun _ _ => mem_univ _)

@[simp] theorem map_val {n : ℕ} (S : Simplex n E) (f : E → F) (hf : ContDiff ℝ 2 f) :
    (S.map f hf).val = f ∘ S.val := rfl

@[simp] theorem face_map {n : ℕ} (S : Simplex (n+1) E) (i : Fin (n+2))
    (f : E → F) (hf : ContDiff ℝ 2 f) : (S.map f hf).face i = (S.face i).map f hf := rfl


/-- The two orders of deleting two distinct parameter vertices give the same map. -/
theorem face_face {n : ℕ} (S : Simplex (n+2) E) (j : Fin (n+3)) (i : Fin (n+2)) :
    (S.face j).face i = (S.face (j.succAbove i)).face (i.predAbove j) := by
  simp only [face, reparam_comp]
  congr 1
  funext k
  exact (Fin.succAbove_succAbove_succAbove_predAbove j i k).symm

end Simplex

/-- Integer chains in a fixed ordinary dimension. -/
abbrev Chain (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  FreeAbelianGroup (Simplex n E)

def simplex {n : ℕ} (S : Simplex n E) : Chain n E := FreeAbelianGroup.of S

/-- Alternating face restriction; no orientation quotient is used here. -/
def boundary (n : ℕ) : Chain (n+1) E →+ Chain n E :=
  FreeAbelianGroup.lift (fun S => ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • simplex (S.face i))

@[simp] theorem boundary_simplex {n : ℕ} (S : Simplex (n+1) E) :
    boundary n (simplex S) = ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • simplex (S.face i) := by
  simp [boundary, simplex]

/-- Pairing the two deletion orders reverses their integer coefficients. -/
theorem deletion_sign {n : ℕ} (j : Fin (n+2)) (i : Fin (n+1)) :
    (-1 : ℤ) ^ j.val * (-1 : ℤ) ^ i.val =
      -((-1 : ℤ) ^ (j.succAbove i).val * (-1 : ℤ) ^ (i.predAbove j).val) := by
  by_cases h : i.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc, Fin.val_pred]
    have hj : 0 < j.val := by exact lt_of_le_of_lt (Nat.zero_le _) h
    have he : j.val = (j.val - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]
    ring
  · have h' : j ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']
    simp only [Fin.val_succ, Fin.coe_castPred, pow_succ]
    ring

/-- Every double face cancels its paired occurrence, before any orientation relation. -/
theorem boundary_squared (n : ℕ) (c : Chain (n+2) E) :
    boundary n (boundary (n+1) c) = 0 := by
  have h : (boundary n).comp (boundary (n+1)) = (0 : Chain (n+2) E →+ Chain n E) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change boundary n (boundary (n+1) (simplex S)) = 0
    simp only [boundary_simplex, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_product', Finset.univ_product_univ]
    refine Finset.sum_involution (s := Finset.univ)
      (fun (p : Fin (n+3) × Fin (n+2)) _ => (p.1.succAbove p.2, p.2.predAbove p.1))
      ?_ ?_ ?_ ?_
    · intro p _
      rw [Simplex.face_face, deletion_sign p.1 p.2, neg_smul, neg_add_cancel]
    · intro p _ _ he
      exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst he)
    · intro _ _; exact Finset.mem_univ _
    · intro p _
      exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
        (Fin.predAbove_predAbove_succAbove p.1 p.2)
  exact DFunLike.congr_fun h c

/-- The ordinary boundary, with zero boundary in degree zero and no augmentation. -/
def ordinaryBoundary : (n : ℕ) → Chain n E →+ Chain (n-1) E :=
  Nat.rec (motive := fun n => Chain n E →+ Chain (n-1) E) 0 (fun n _ => boundary n)

@[simp] theorem ordinaryBoundary_zero (c : Chain 0 E) : ordinaryBoundary 0 c = 0 := rfl

@[simp] theorem ordinaryBoundary_succ (n : ℕ) (c : Chain (n+1) E) :
    ordinaryBoundary (n+1) c = boundary n c := rfl

theorem ordinaryBoundary_squared (n : ℕ) (c : Chain n E) :
    ordinaryBoundary (n-1) (ordinaryBoundary n c) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact boundary_squared n c

/-- Nonlinear pushforward acts on full parameter maps. -/
def map (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f) : Chain n E →+ Chain n F :=
  FreeAbelianGroup.map (fun S => S.map f hf)

@[simp] theorem map_simplex {n : ℕ} (S : Simplex n E) (f : E → F) (hf : ContDiff ℝ 2 f) :
    map n f hf (simplex S) = simplex (S.map f hf) := rfl

theorem boundary_map (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f) (c : Chain (n+1) E) :
    boundary n (map (n+1) f hf c) = map n f hf (boundary n c) := by
  have h : (boundary n).comp (map (n+1) f hf) = (map n f hf).comp (boundary n) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change boundary n (map (n+1) f hf (simplex S)) = map n f hf (boundary n (simplex S))
    simp
  exact DFunLike.congr_fun h c

theorem boundary_multiplicity (n : ℕ) (z : ℤ) (c : Chain (n+1) E) :
    boundary n (z • c) = z • boundary n c := map_zsmul _ _ _

theorem map_id (n : ℕ) (c : Chain n E) : map n id contDiff_id c = c := by
  have h : map n (id : E → E) contDiff_id = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro S
    rfl
  exact DFunLike.congr_fun h c

theorem map_comp (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f)
    (g : F → G) (hg : ContDiff ℝ 2 g) (c : Chain n E) :
    map n g hg (map n f hf c) = map n (g ∘ f) (hg.comp hf) c := by
  have h : (map n g hg).comp (map n f hf) = map n (g ∘ f) (hg.comp hf) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    rfl
  exact DFunLike.congr_fun h c

/-- A raw generator is nonzero, including constant and degenerate maps. -/
theorem simplex_ne_zero {n : ℕ} (S : Simplex n E) : simplex S ≠ 0 :=
  FreeAbelianGroup.of_ne_zero S

/-- Coefficient extraction witnesses infinite order, not merely nonzero generators. -/
def coefficient {n : ℕ} (S : Simplex n E) : Chain n E →+ ℤ := by
  classical
  exact FreeAbelianGroup.lift (fun T => if T = S then 1 else 0)

@[simp] theorem coefficient_self {n : ℕ} (S : Simplex n E) : coefficient S (simplex S) = 1 := by
  simp [coefficient, simplex]

theorem multiplicity_injective {n : ℕ} (S : Simplex n E) :
    Function.Injective (fun z : ℤ => z • simplex S) := by
  intro z w h
  have hh := congrArg (coefficient S) h
  simpa using hh

/-- The permutation of the remaining vertices after deleting vertex `i`. -/
def facePerm {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    Equiv.Perm (Fin (n+1)) :=
  (Equiv.Perm.decomposeFin' (i.cycleRange.symm.trans σ)).2

theorem facePerm_decomposition {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    Equiv.Perm.decomposeFin'Symm (σ i) (facePerm σ i) = i.cycleRange.symm.trans σ := by
  have h := Equiv.Perm.decomposeFin'.symm_apply_apply (i.cycleRange.symm.trans σ)
  change Equiv.Perm.decomposeFin'Symm
    (Equiv.Perm.decomposeFin' (i.cycleRange.symm.trans σ)).1 (facePerm σ i) = _ at h
  have hz := congrArg (fun p : Equiv.Perm (Fin (n+2)) => p 0) h
  simp only [Equiv.Perm.decomposeFin'Symm_zero,
    Equiv.trans_apply, Fin.cycleRange_symm_zero] at hz
  rwa [hz] at h

theorem facePerm_apply {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2))
    (j : Fin (n+1)) : (σ i).succAbove (facePerm σ i j) = σ (i.succAbove j) := by
  have h := congrArg (fun p : Equiv.Perm (Fin (n+2)) => p j.succ) (facePerm_decomposition σ i)
  simpa using h

/-- The orientation sign of a deleted face, with both source and target indices. -/
theorem facePerm_sign {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    (-1 : ℤ) ^ i.val * (facePerm σ i).sign =
      (σ.sign : ℤ) * (-1 : ℤ) ^ (σ i).val := by
  have h := congrArg Equiv.Perm.sign (facePerm_decomposition σ i)
  rw [Equiv.Perm.sign_decomposeFin'Symm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_symm, Fin.sign_cycleRange] at h
  have hz := congrArg (fun z : ℤˣ => (z : ℤ)) h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at hz
  have h₁ : ((-1 : ℤ) ^ i.val) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm i.val, pow_mul]; norm_num
  have h₂ : ((-1 : ℤ) ^ (σ i).val) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (σ i).val, pow_mul]; norm_num
  linear_combination ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ (σ i).val) * hz -
    (facePerm σ i).sign * (-1 : ℤ) ^ i.val * h₂ +
    (σ.sign : ℤ) * (-1 : ℤ) ^ (σ i).val * h₁

theorem Simplex.face_reparam {n : ℕ} (S : Simplex (n+1) E)
    (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    (S.reparam σ).face i = (S.face (σ i)).reparam (facePerm σ i) := by
  simp only [Simplex.face, Simplex.reparam_comp]
  congr 1
  funext j
  exact (facePerm_apply σ i j).symm

/-- Only full-map permutation relations are imposed. No equality of image sets
or of vertex values is a defining relation. -/
def orientationRelations (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    AddSubgroup (Chain n E) :=
  AddSubgroup.closure {r | ∃ (S : Simplex n E) (σ : Equiv.Perm (Fin (n+1))),
    r = simplex (S.reparam σ) - (σ.sign : ℤ) • simplex S}

abbrev Oriented (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  Chain n E ⧸ orientationRelations n E

def project (n : ℕ) : Chain n E →+ Oriented n E :=
  QuotientAddGroup.mk' (orientationRelations n E)

private theorem project_reparam {n : ℕ} (S : Simplex n E)
    (σ : Equiv.Perm (Fin (n+1))) :
    project n (simplex (S.reparam σ)) = (σ.sign : ℤ) • project n (simplex S) := by
  apply sub_eq_zero.mp
  rw [← map_zsmul, ← map_sub]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.subset_closure ⟨S, σ, rfl⟩)

/-- Boundary descent is proved by the deleted-face permutation and its sign. -/
theorem boundary_orientationRelations {n : ℕ} {c : Chain (n+1) E}
    (hc : c ∈ orientationRelations (n+1) E) : boundary n c ∈ orientationRelations n E := by
  have hk : (orientationRelations (n+1) E) ≤ ((project n).comp (boundary n)).ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro r ⟨S, σ, rfl⟩
    change project n (boundary n (simplex (S.reparam σ) - (σ.sign : ℤ) • simplex S)) = 0
    simp only [map_sub, map_zsmul, boundary_simplex, map_sum,
      Simplex.face_reparam, project_reparam, smul_smul]
    apply sub_eq_zero.mpr
    simp_rw [facePerm_sign, mul_smul]
    rw [← Finset.smul_sum]
    exact congrArg ((σ.sign : ℤ) • ·) (Equiv.sum_comp σ
      (fun i => (-1 : ℤ) ^ i.val • project n (simplex (S.face i))))
  exact (QuotientAddGroup.eq_zero_iff _).mp (hk hc)

/-- The boundary on oriented genuine smooth chains. -/
def orientedBoundary (n : ℕ) : Oriented (n+1) E →+ Oriented n E :=
  QuotientAddGroup.lift (orientationRelations (n+1) E) ((project n).comp (boundary n))
    (fun _ hc => (QuotientAddGroup.eq_zero_iff _).mpr (boundary_orientationRelations hc))

@[simp] theorem orientedBoundary_project (n : ℕ) (c : Chain (n+1) E) :
    orientedBoundary n (project (n+1) c) = project n (boundary n c) := rfl

/-- General vertex-permutation signs hold in the orientation quotient only. -/
theorem orientation_sign {n : ℕ} (S : Simplex n E) (σ : Equiv.Perm (Fin (n+1))) :
    project n (simplex (S.reparam σ)) = (σ.sign : ℤ) • project n (simplex S) :=
  project_reparam S σ

theorem orientedBoundary_squared (n : ℕ) (c : Oriented (n+2) E) :
    orientedBoundary n (orientedBoundary (n+1) c) = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | H c =>
    change orientedBoundary n (orientedBoundary (n+1) (project (n+2) c)) = 0
    simp [boundary_squared]

/-- Smooth pushforward preserves the orientation relations as well. -/
theorem map_orientationRelations (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f)
    {c : Chain n E} (hc : c ∈ orientationRelations n E) :
    map n f hf c ∈ orientationRelations n F := by
  induction hc using AddSubgroup.closure_induction with
  | mem r hr =>
    obtain ⟨S, σ, rfl⟩ := hr
    apply AddSubgroup.subset_closure
    exact ⟨S.map f hf, σ, by simp only [map_sub, map_zsmul, map_simplex]; rfl⟩
  | zero => simp
  | add c d _ _ hc hd => simpa using (orientationRelations n F).add_mem hc hd
  | neg c _ hc => simpa using (orientationRelations n F).neg_mem hc

def orientedMap (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f) : Oriented n E →+ Oriented n F :=
  QuotientAddGroup.lift (orientationRelations n E) ((project n).comp (map n f hf))
    (fun _ hc => (QuotientAddGroup.eq_zero_iff _).mpr (map_orientationRelations n f hf hc))

@[simp] theorem orientedMap_project (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f) (c : Chain n E) :
    orientedMap n f hf (project n c) = project n (map n f hf c) := rfl

theorem orientedBoundary_map (n : ℕ) (f : E → F) (hf : ContDiff ℝ 2 f)
    (c : Oriented (n+1) E) :
    orientedBoundary n (orientedMap (n+1) f hf c) =
      orientedMap n f hf (orientedBoundary n c) := by
  induction c using QuotientAddGroup.induction_on with
  | H c => exact congrArg (project n) (boundary_map n f hf c)

/-- The actual standard parameter vertices, including dimension zero. -/
def vertex {n : ℕ} (i : Fin (n+1)) : Param n :=
  relabel (fun _ : Fin 1 => i) (0 : Param 0)

@[simp] theorem weights_vertex {n : ℕ} (i j : Fin (n+1)) :
    weights (vertex i) j = if i = j then 1 else 0 := by
  unfold vertex
  rw [weights_relabel]
  simp [transport, weights]

@[simp] theorem relabel_vertex {n m : ℕ} (f : Fin (n+1) → Fin (m+1)) (i : Fin (n+1)) :
    relabel f (vertex i) = vertex (f i) := by
  simp [vertex, Function.comp_def]

theorem weights_smooth {n : ℕ} (i : Fin (n+1)) : ContDiff ℝ 2 (fun u : Param n => weights u i) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact contDiff_const.sub (ContDiff.sum (fun k _ => (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff))
  · exact (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff

/-- Genuine affine realization of an ordered tuple, with no independence assumption. -/
def affine {n : ℕ} (v : Fin (n+1) → E) : Simplex n E :=
  ⟨fun u => ∑ i, weights u i • v i,
    univ, isOpen_univ, subset_univ _,
    (ContDiff.sum (fun i _ => (weights_smooth i).smul contDiff_const)).contDiffOn⟩

/-- Rudin's literal Cartesian formula (76), on the full parameter space. -/
theorem affine_formula {n : ℕ} (v : Fin (n+1) → E) (u : Param n) :
    (affine v).val u = v 0 + ∑ i, u i • (v i.succ - v 0) := by
  simp only [affine, weights, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
  abel

@[simp] theorem affine_vertex {n : ℕ} (v : Fin (n+1) → E) (i : Fin (n+1)) :
    (affine v).val (vertex i) = v i := by
  classical
  change ∑ j, weights (vertex i) j • v j = v i
  simp only [weights_vertex, ite_smul, one_smul, zero_smul]
  simp

/-- Affine realization commutes with every parameter vertex map, including
noninjective maps. This concerns parameter maps, not nonlinear target maps. -/
theorem affine_reparam {n m : ℕ} (v : Fin (m+1) → E) (f : Fin (n+1) → Fin (m+1)) :
    (affine v).reparam f = affine (v ∘ f) := by
  classical
  apply Subtype.ext
  funext u
  change ∑ j, weights (relabel f u) j • v j = ∑ i, weights u i • v (f i)
  simp only [weights_relabel, transport, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

@[simp] theorem affine_face {n : ℕ} (v : Fin (n+2) → E) (i : Fin (n+2)) :
    (affine v).face i = affine (v ∘ i.succAbove) := affine_reparam v i.succAbove

/-- Affine-to-smooth comparison on formal fixed-degree vertex generators. -/
def affineChains (n : ℕ) : FreeAbelianGroup (Fin (n+1) → E) →+ Chain n E :=
  FreeAbelianGroup.lift (fun v => simplex (affine v))

theorem boundary_affine {n : ℕ} (v : Fin (n+2) → E) :
    boundary n (simplex (affine v)) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ i.val • simplex (affine (v ∘ i.succAbove)) := by
  simp

/-- On the quotient, any affine vertex permutation has the source sign. -/
theorem affine_orientation {n : ℕ} (v : Fin (n+1) → E) (σ : Equiv.Perm (Fin (n+1))) :
    project n (simplex (affine (v ∘ σ))) = (σ.sign : ℤ) • project n (simplex (affine v)) := by
  rw [← affine_reparam]
  exact orientation_sign _ σ

/-- An auxiliary detector, not a definition of chain equality: the determinant
of vertex values detects infinite-order generators in every quotient degree. -/
def vertexDet {n : ℕ} (S : Simplex n (Param n)) : ℝ :=
  Matrix.det (fun i j : Fin (n+1) => weights (S.val (vertex i)) j)

theorem vertexDet_reparam {n : ℕ} (S : Simplex n (Param n))
    (σ : Equiv.Perm (Fin (n+1))) : vertexDet (S.reparam σ) = (σ.sign : ℤ) • vertexDet S := by
  have h := Matrix.det_permute σ (fun i j : Fin (n+1) => weights (S.val (vertex i)) j)
  have he : (fun i j : Fin (n+1) => weights ((S.reparam σ).val (vertex i)) j) =
      Matrix.submatrix (fun i j : Fin (n+1) => weights (S.val (vertex i)) j) σ id := by
    ext i j
    change weights (S.val (relabel σ (vertex i))) j = weights (S.val (vertex (σ i))) j
    rw [relabel_vertex]
  unfold vertexDet
  rw [he, h]
  simp only [zsmul_eq_mul]

def orientedDetector (n : ℕ) : Oriented n (Param n) →+ ℝ :=
  QuotientAddGroup.lift (orientationRelations n (Param n))
    (FreeAbelianGroup.lift vertexDet) (by
      apply (AddSubgroup.closure_le _).mpr
      rintro r ⟨S, σ, rfl⟩
      change FreeAbelianGroup.lift vertexDet (simplex (S.reparam σ) - (σ.sign : ℤ) • simplex S) = 0
      simp [simplex, vertexDet_reparam])

/-- The identity simplex is a nontrivial model in every dimension, including zero. -/
def identitySimplex (n : ℕ) : Simplex n (Param n) :=
  ⟨id, univ, isOpen_univ, subset_univ _, contDiff_id.contDiffOn⟩

@[simp] theorem orientedDetector_identity (n : ℕ) :
    orientedDetector n (project n (simplex (identitySimplex n))) = 1 := by
  simp only [orientedDetector, project, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk',
    simplex, FreeAbelianGroup.lift_apply_of]
  have h : (fun i j : Fin (n+1) => weights (vertex i) j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := by
    ext i j
    simp [Matrix.one_apply]
  change Matrix.det (fun i j : Fin (n+1) => weights (vertex i) j) = 1
  rw [h, Matrix.det_one]

theorem oriented_identity_infinite_order (n : ℕ) :
    Function.Injective (fun z : ℤ => z • project n (simplex (identitySimplex n))) := by
  intro z w h
  have hh := congrArg (orientedDetector n) h
  simpa using hh

/-- Barycentric face inclusion is literal insertion of a zero coordinate. -/
theorem transport_succAbove {n : ℕ} (i : Fin (n+1)) (w : Fin n → ℝ) :
    transport i.succAbove w = Fin.insertNth i 0 w := by
  classical
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp [transport, Fin.succAbove_ne]
  · simp [transport, Fin.succAbove_right_injective.eq_iff]

theorem weights_face {n : ℕ} (i : Fin (n+2)) (u : Param n) :
    weights (relabel i.succAbove u) = Fin.insertNth i 0 (weights u) := by
  rw [weights_relabel, transport_succAbove]

/-- The zeroth face has Cartesian coordinates `(1 - sum u, u)`. -/
theorem face_zero_coordinates {n : ℕ} (u : Param n) (j : Fin (n+1)) :
    relabel (0 : Fin (n+2)).succAbove u j = weights u j := by
  rw [relabel_apply, transport_succAbove]
  simp

/-- Every other face inserts zero in the indicated Cartesian coordinate. -/
theorem face_succ_coordinates {n : ℕ} (i : Fin (n+1)) (u : Param n) :
    (fun j => relabel i.succ.succAbove u j) = Fin.insertNth i 0 (fun j => u j) := by
  funext j
  simp only [relabel_apply, transport_succAbove, weights,
    Fin.insertNth_succ_cons, Fin.cons_succ]

/-- The new affine map agrees with the existing barycentric realization. -/
theorem affine_realize {n : ℕ} (v : Fin (n+1) → E) (u : Param n)
    (hu : u ∈ standardSimplex n) :
    (affine v).val u = OrientedChains.realize v
      ⟨weights u, (mem_simplex_iff_weights u).mp hu, sum_weights u⟩ := rfl

/-- Finite-sum integration of the actual pullback coefficients on raw chains.
This definition does not assert descent to the higher orientation quotient. -/
def integral {n : ℕ} (ω : Form n E) : Chain n E →+ ℝ :=
  FreeAbelianGroup.lift (fun S => simplexIntegral ω S.toSmooth)

@[simp] theorem integral_simplex {n : ℕ} (ω : Form n E) (S : Simplex n E) :
    integral ω (simplex S) = simplexIntegral ω S.toSmooth := by
  simp [integral, simplex]

/-- Genuine differentiability follows from the stored open-neighborhood C² proof. -/
theorem Simplex.differentiableAt {n : ℕ} (S : Simplex n E) {u : Param n}
    (hu : u ∈ standardSimplex n) : DifferentiableAt ℝ S.val u :=
  S.toSmooth.differentiableAt hu

theorem integral_integrable {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (hω : ContinuousOn ω (S.val '' standardSimplex n)) :
    MeasureTheory.IntegrableOn (simplexCoefficient ω S.toSmooth) (standardSimplex n) :=
  simplexCoefficient_integrable ω S.toSmooth hω

/-- Every source Riemann stage exists, in every coordinate order, for the actual
coefficient. Only continuity on the simplex image is required for the form. -/
theorem integral_source {n : ℕ} (ω : Form n E) (S : Simplex n E)
    (hω : ContinuousOn ω (S.val '' standardSimplex n)) (σ : Equiv.Perm (Fin n)) :
    MultivariateRiemann.HasSourceIntegral n 0 1
      (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω S.toSmooth ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ MultivariateRiemann.coordinatePermutation σ)
      (integral ω (simplex S)) := by
  rw [integral_simplex]
  exact MultivariateRiemann.simplexIntegral_source ω S.toSmooth hω σ

/-- Naturality of the genuine coefficient is a chain rule, not a vertex identity. -/
theorem coefficient_map {n : ℕ} (ω : Form n F) (S : Simplex n E)
    (f : E → F) (hf : ContDiff ℝ 2 f) {u : Param n} (hu : u ∈ standardSimplex n) :
    simplexCoefficient ω (S.map f hf).toSmooth u =
      simplexCoefficient (pullback ω f) S.toSmooth u := by
  exact congrArg (fun a => a (fun i => EuclideanSpace.single i 1))
    (pullback_comp ω f S.val u (hf.differentiable (by norm_num) _) (S.differentiableAt hu))

theorem integral_map {n : ℕ} (ω : Form n F) (f : E → F) (hf : ContDiff ℝ 2 f)
    (c : Chain n E) : integral ω (map n f hf c) = integral (pullback ω f) c := by
  have h : (integral ω).comp (map n f hf) = integral (pullback ω f) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change integral ω (map n f hf (simplex S)) = integral (pullback ω f) (simplex S)
    simp only [map_simplex, integral_simplex, simplexIntegral]
    apply MeasureTheory.setIntegral_congr_fun (standardSimplex_isCompact n).measurableSet
    intro u hu
    exact coefficient_map ω S f hf hu
  exact DFunLike.congr_fun h c

/-- Actual affine triangle faces, with their integer coefficients. -/
theorem boundary_triangle (a b c : E) :
    boundary 1 (simplex (affine ![a,b,c])) =
      simplex (affine ![b,c]) - simplex (affine ![a,c]) + simplex (affine ![a,b]) := by
  rw [boundary_affine]
  simp [Fin.sum_univ_succ, Function.comp_def, Fin.succAbove]
  abel

/-- Two genuine affine triangles with a common full-map diagonal. -/
def square (a b c d : E) : Chain 2 E :=
  simplex (affine ![a,b,c]) - simplex (affine ![a,d,c])

/-- The diagonal cancels before any quotient. The remaining sides have the
source signs; reversed raw edges are not silently identified. -/
theorem boundary_square (a b c d : E) :
    boundary 1 (square a b c d) =
      simplex (affine ![a,b]) + simplex (affine ![b,c]) -
        simplex (affine ![d,c]) - simplex (affine ![a,d]) := by
  simp only [square, map_sub, boundary_triangle]
  abel

theorem boundary_square_difference (a b c d : E) :
    boundary 1 (simplex (affine ![a,b,c]) + simplex (affine ![a,d,c])) =
      simplex (affine ![a,b]) + simplex (affine ![b,c]) +
        simplex (affine ![a,d]) + simplex (affine ![d,c]) -
          (2 : ℤ) • simplex (affine ![a,c]) := by
  simp only [map_add, boundary_triangle]
  abel

/-- The ordered one-dimensional Euclidean parameter chart. -/
def line (t : ℝ) : Param 1 := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => t)

@[simp] theorem line_apply (t : ℝ) (i : Fin 1) : line t i = t := rfl

def Simplex.path (S : Simplex 1 E) : ℝ → E := fun t => S.val (line t)

/-- Forget smoothness, retaining the full path, reversal signs and constants. -/
def toPaths : Chain 1 E →+ OrientedChains.Parametric.PathChain E :=
  FreeAbelianGroup.lift (fun S => OrientedChains.Parametric.path S.path)

@[simp] theorem toPaths_simplex (S : Simplex 1 E) :
    toPaths (simplex S) = OrientedChains.Parametric.path S.path := by
  simp [toPaths, simplex]

theorem affine_path (a b : E) : (affine ![a,b]).path = OrientedChains.Parametric.segment a b := by
  funext t
  rw [Simplex.path, affine_formula]
  simp [OrientedChains.Parametric.segment, sub_smul, smul_sub]
  module

theorem reparam_swap_line (t : ℝ) :
    relabel (Equiv.swap (0 : Fin 2) 1) (line t) = line (1-t) := by
  ext i
  fin_cases i
  change (∑ x : Fin 2, if Equiv.swap (0 : Fin 2) 1 x = 1 then weights (line t) x else 0) = 1-t
  rw [Fin.sum_univ_two]
  norm_num [weights, Fin.sum_univ_one]

/-- The signed path comparison descends to the genuine orientation quotient. -/
theorem toPaths_orientationRelations {c : Chain 1 E} (hc : c ∈ orientationRelations 1 E) :
    toPaths c = 0 := by
  have hk : orientationRelations 1 E ≤ (toPaths : Chain 1 E →+ _).ker := by
    apply (AddSubgroup.closure_le _).mpr
    rintro r ⟨S, σ, rfl⟩
    have hp : ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by decide
    rcases hp σ with rfl | rfl
    · change toPaths (simplex (S.reparam id) - (1 : ℤ) • simplex S) = 0
      simp
    · have he : (S.reparam (Equiv.swap (0 : Fin 2) 1)).path =
          OrientedChains.Parametric.reverse S.path := by
        funext t
        simp [Simplex.path, reparam_swap_line, OrientedChains.Parametric.reverse]
      change toPaths (simplex (S.reparam (Equiv.swap (0 : Fin 2) 1)) -
        ((Equiv.swap (0 : Fin 2) 1).sign : ℤ) • simplex S) = 0
      simp [he, OrientedChains.Parametric.path_reverse]
  exact hk hc

def orientedToPaths : Oriented 1 E →+ OrientedChains.Parametric.PathChain E :=
  QuotientAddGroup.lift (orientationRelations 1 E) toPaths (fun _ hc => toPaths_orientationRelations hc)

@[simp] theorem orientedToPaths_project (c : Chain 1 E) :
    orientedToPaths (project 1 c) = toPaths c := rfl

theorem toPaths_map (f : E → F) (hf : ContDiff ℝ 2 f) (c : Chain 1 E) :
    toPaths (map 1 f hf c) = OrientedChains.Parametric.pathMap f (toPaths c) := by
  have h : toPaths.comp (map 1 f hf) = (OrientedChains.Parametric.pathMap f).comp toPaths := by
    apply FreeAbelianGroup.lift_ext
    intro S
    rfl
  exact DFunLike.congr_fun h c

/-- The source's two-triangle diagonal in square parameter coordinates. -/
def squareParameters : Chain 2 (ℝ × ℝ) := square (0,0) (1,0) (1,1) (0,1)

/-- Triangulate a genuine C² square map by precomposition with two affine maps.
The map acts on the whole triangles, not on their image corners. -/
def triangulate (S : (ℝ × ℝ) → E) (hS : ContDiff ℝ 2 S) : Chain 2 E :=
  map 2 S hS squareParameters

/-- The smooth triangulation boundary is exactly the existing square boundary.
No surface integration or geometric coverage theorem is used. -/
theorem triangulate_boundary (S : (ℝ × ℝ) → E) (hS : ContDiff ℝ 2 S) :
    toPaths (boundary 1 (triangulate S hS)) =
      OrientedChains.Parametric.surfaceBoundary (OrientedChains.Parametric.surface S) := by
  rw [triangulate, boundary_map, toPaths_map, squareParameters, boundary_square]
  simp only [map_sub, map_add, toPaths_simplex, affine_path,
    OrientedChains.Parametric.pathMap_path,
    OrientedChains.Parametric.surfaceBoundary_surface]
  have hb : OrientedChains.Parametric.segment ((0,0) : ℝ × ℝ) (1,0) = fun t => (t,0) := by
    funext t; simp [OrientedChains.Parametric.segment]
  have hr : OrientedChains.Parametric.segment ((1,0) : ℝ × ℝ) (1,1) = fun t => (1,t) := by
    funext t; simp [OrientedChains.Parametric.segment, Prod.smul_mk, Prod.mk_add_mk]
  have ht : OrientedChains.Parametric.segment ((0,1) : ℝ × ℝ) (1,1) = fun t => (t,1) := by
    funext t; simp [OrientedChains.Parametric.segment, Prod.smul_mk, Prod.mk_add_mk]
  have hl : OrientedChains.Parametric.segment ((0,0) : ℝ × ℝ) (0,1) = fun t => (0,t) := by
    funext t; simp [OrientedChains.Parametric.segment]
  rw [hb, hr, ht, hl]
  rfl

/-- The actual source Möbius map has genuine C² regularity. -/
theorem mobiusSquare_smooth (δ : ℝ) : ContDiff ℝ 2 (OrientedChains.Parametric.mobiusSquare δ) := by
  unfold OrientedChains.Parametric.mobiusSquare OrientedChains.Parametric.mobius
  fun_prop

/-- The triangulated smooth Möbius chain retains the repeated seam. -/
theorem mobius_triangulation_boundary (δ : ℝ) :
    toPaths (boundary 1 (triangulate (OrientedChains.Parametric.mobiusSquare δ) (mobiusSquare_smooth δ))) =
      OrientedChains.Parametric.path (fun t => OrientedChains.Parametric.mobiusSquare δ (t,0)) -
      OrientedChains.Parametric.path (fun t => OrientedChains.Parametric.mobiusSquare δ (t,1)) +
      (2 : ℤ) • OrientedChains.Parametric.path (fun t => OrientedChains.Parametric.mobiusSquare δ (1,t)) := by
  rw [triangulate_boundary]
  exact OrientedChains.Parametric.mobius_boundary δ

/-- Degree-one oriented integration uses the already proved path-orientation
descent. `orientedPathIntegral_project` proves agreement with `integral`. -/
def orientedPathIntegral (ω : PathIntegration.OneForm E) : Oriented 1 E →+ ℝ :=
  (PathIntegration.chainIntegral ω).comp orientedToPaths

theorem line_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : line t ∈ standardSimplex 1 := by
  simpa [standardSimplex] using ht

theorem line_hasDerivAt (t : ℝ) : HasDerivAt line (EuclideanSpace.single 0 1) t := by
  have hp : HasDerivAt (fun t : ℝ => fun _ : Fin 1 => t) (fun _ => 1) t := by
    exact (hasDerivAt_pi).mpr (fun _ => hasDerivAt_id t)
  have h := (EuclideanSpace.equiv (Fin 1) ℝ).symm.hasFDerivAt.comp_hasDerivAt t hp
  have he : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => 1) =
      EuclideanSpace.single (0 : Fin 1) 1 := by
    ext i
    fin_cases i
    simp [EuclideanSpace.single]
  change HasDerivAt line ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => 1)) t at h
  rw [he] at h
  exact h

/-- The one-dimensional coefficient uses the actual derivative of the path. -/
theorem coefficient_path (ω : Form 1 E) (S : Simplex 1 E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    simplexCoefficient ω S.toSmooth (line t) =
      PathIntegration.coefficient (PathIntegration.fromAlternating ω) S.path t := by
  have hd := ((S.differentiableAt (line_mem ht)).hasFDerivAt.comp_hasDerivAt t (line_hasDerivAt t)).deriv
  change ω (S.val (line t)) (fun i => fderiv ℝ S.val (line t) (EuclideanSpace.single i 1)) =
    (PathIntegration.fromAlternating ω (S.val (line t))) (deriv (S.val ∘ line) t)
  rw [hd]
  simp only [PathIntegration.fromAlternating_apply]
  apply congrArg (ω (S.val (line t)))
  funext i
  fin_cases i
  rfl

/-- The genuine simplex integral is the existing path integral. Source existence
and the Euclidean normalization are inherited from `MultivariateRiemann`. -/
theorem integral_eq_pathIntegral (ω : Form 1 E) (S : Simplex 1 E)
    (hω : ContinuousOn ω (S.val '' standardSimplex 1)) :
    integral ω (simplex S) = PathIntegration.pathIntegral (PathIntegration.fromAlternating ω) S.path := by
  have hv := (integral_source ω S hω (Equiv.refl (Fin 1))).value
  rw [← hv]
  change (∫ t in (0 : ℝ)..1,
    (MultivariateRiemann.simplexZeroExtension (simplexCoefficient ω S.toSmooth ∘
      (EuclideanSpace.equiv (Fin 1) ℝ).symm) ∘
      MultivariateRiemann.coordinatePermutation (Equiv.refl (Fin 1))) (Fin.cons t 0)) = _
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hx : Fin.cons t (0 : Fin 0 → ℝ) ∈ MultivariateRiemann.piSimplex 1 := by
    simpa [MultivariateRiemann.piSimplex] using ht'
  have he : MultivariateRiemann.coordinatePermutation (Equiv.refl (Fin 1)) =
      ContinuousLinearEquiv.refl ℝ (Fin 1 → ℝ) := by
    ext x i
    simp
  simp only [Function.comp_apply, he, ContinuousLinearEquiv.refl_apply,
    MultivariateRiemann.simplexZeroExtension, indicator_of_mem hx]
  have hl : (EuclideanSpace.equiv (Fin 1) ℝ).symm (Fin.cons t 0) = line t := by
    ext i
    fin_cases i
    rfl
  rw [hl]
  exact coefficient_path ω S ht'

/-- In degree one the oriented path integral agrees with the actual simplex
pullback integral; hence this is proved orientation descent, not an assumption. -/
theorem orientedPathIntegral_project (ω : Form 1 E) (hω : Continuous ω) (c : Chain 1 E) :
    orientedPathIntegral (PathIntegration.fromAlternating ω) (project 1 c) = integral ω c := by
  have h : (orientedPathIntegral (PathIntegration.fromAlternating ω)).comp (project 1) = integral ω := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change PathIntegration.chainIntegral (PathIntegration.fromAlternating ω)
      (OrientedChains.Parametric.path S.path) = integral ω (simplex S)
    rw [PathIntegration.chainIntegral_path]
    exact (integral_eq_pathIntegral ω S hω.continuousOn).symm
  exact DFunLike.congr_fun h c

/-- Four tetrahedron faces, with literal increasing-index parameter maps. -/
theorem boundary_tetrahedron (a b c d : E) :
    boundary 2 (simplex (affine ![a,b,c,d])) =
      simplex (affine ![b,c,d]) - simplex (affine ![a,c,d]) +
      simplex (affine ![a,b,d]) - simplex (affine ![a,b,c]) := by
  rw [boundary_affine]
  simp [Fin.sum_univ_succ, Function.comp_def, Fin.succAbove]
  abel

/-- Six signed smooth affine tetrahedra with the Exercise 18 coefficients. -/
def cube (x y z : E) : Chain 3 E :=
  simplex (affine ![0,x,x+y,x+y+z]) - simplex (affine ![0,x,x+z,x+y+z]) -
  simplex (affine ![0,y,x+y,x+y+z]) + simplex (affine ![0,y,y+z,x+y+z]) +
  simplex (affine ![0,z,x+z,x+y+z]) - simplex (affine ![0,z,y+z,x+y+z])

/-- Internal faces cancel with their full parameterizations and integer signs.
The remaining twelve triangles are grouped into the six signed square faces. -/
theorem boundary_cube (x y z : E) :
    boundary 2 (cube x y z) =
      (square x (x+y) (x+y+z) (x+z) - square 0 y (y+z) z) -
      (square y (x+y) (x+y+z) (y+z) - square 0 x (x+z) z) +
      (square z (x+z) (x+y+z) (y+z) - square 0 x (x+y) y) := by
  simp only [cube, square, map_add, map_sub, boundary_tetrahedron]
  abel

/-- Fixed-degree ordered affine chains have the usual deletion boundary. -/
def vertexBoundary (n : ℕ) :
    FreeAbelianGroup (Fin (n+2) → E) →+ FreeAbelianGroup (Fin (n+1) → E) :=
  FreeAbelianGroup.lift (fun v => ∑ i : Fin (n+2),
    (-1 : ℤ) ^ i.val • FreeAbelianGroup.of (v ∘ i.succAbove))

theorem affineChains_boundary (n : ℕ) (c : FreeAbelianGroup (Fin (n+2) → E)) :
    boundary n (affineChains (n+1) c) = affineChains n (vertexBoundary n c) := by
  have h : (boundary n).comp (affineChains (E := E) (n+1)) =
      (affineChains n).comp (vertexBoundary n) := by
    apply FreeAbelianGroup.lift_ext
    intro v
    simp [affineChains, vertexBoundary]
  exact DFunLike.congr_fun h c

/-- Chains whose whole parameter-simplex images lie in a specified domain.
The image condition is proof data; it does not store a second parameter map. -/
abbrev InDomain (n : ℕ) (V : Set E) :=
  {S : Simplex n E // MapsTo S.val (standardSimplex n) V}

abbrev DomainChain (n : ℕ) (V : Set E) := FreeAbelianGroup (InDomain n V)

def InDomain.face {n : ℕ} {V : Set E} (S : InDomain (n+1) V) (i : Fin (n+2)) : InDomain n V :=
  ⟨S.val.face i, fun _ hu => S.property (relabel_mem i.succAbove hu)⟩

def forgetDomain (n : ℕ) (V : Set E) : DomainChain n V →+ Chain n E :=
  FreeAbelianGroup.map Subtype.val

def domainBoundary (n : ℕ) (V : Set E) : DomainChain (n+1) V →+ DomainChain n V :=
  FreeAbelianGroup.lift (fun S => ∑ i : Fin (n+2),
    (-1 : ℤ) ^ i.val • FreeAbelianGroup.of (S.face i))

/-- Local smooth postcomposition, without a global regularity assumption. -/
def mapOnChain (n : ℕ) (f : E → F) (V : Set E) (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V) :
    DomainChain n V →+ Chain n F :=
  FreeAbelianGroup.map (fun S => S.val.mapOn f V hV hf S.property)

/-- Source formula (89) for neighborhood-only smooth target maps. -/
theorem boundary_mapOnChain (n : ℕ) (f : E → F) (V : Set E) (hV : IsOpen V)
    (hf : ContDiffOn ℝ 2 f V) (c : DomainChain (n+1) V) :
    boundary n (mapOnChain (n+1) f V hV hf c) = mapOnChain n f V hV hf (domainBoundary n V c) := by
  have h : (boundary n).comp (mapOnChain (n+1) f V hV hf) =
      (mapOnChain n f V hV hf).comp (domainBoundary n V) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp only [AddMonoidHom.comp_apply, mapOnChain,
      domainBoundary, FreeAbelianGroup.lift_apply_of, map_sum, map_zsmul]
    change boundary n (simplex (S.val.mapOn f V hV hf S.property)) = _
    rw [boundary_simplex]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  exact DFunLike.congr_fun h c

theorem forgetDomain_boundary (n : ℕ) (V : Set E) (c : DomainChain (n+1) V) :
    forgetDomain n V (domainBoundary n V c) = boundary n (forgetDomain (n+1) V c) := by
  have h : (forgetDomain n V).comp (domainBoundary n V) =
      (boundary n).comp (forgetDomain (n+1) V) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp [forgetDomain, domainBoundary, boundary, InDomain.face, simplex]
  exact DFunLike.congr_fun h c

/-- The ordinary convention also holds after orientation descent. -/
def orientedOrdinaryBoundary : (n : ℕ) → Oriented n E →+ Oriented (n-1) E :=
  Nat.rec (motive := fun n => Oriented n E →+ Oriented (n-1) E) 0 (fun n _ => orientedBoundary n)

@[simp] theorem orientedOrdinaryBoundary_zero (c : Oriented 0 E) : orientedOrdinaryBoundary 0 c = 0 := rfl

theorem orientedOrdinaryBoundary_squared (n : ℕ) (c : Oriented n E) :
    orientedOrdinaryBoundary (n-1) (orientedOrdinaryBoundary n c) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => exact orientedBoundary_squared n c

/-- Degree zero integrates by evaluation, not by an augmented empty-face value. -/
theorem integral_zero (ω : Form 0 E) (S : Simplex 0 E) :
    integral ω (simplex S) = ω (S.val 0) (fun i => Fin.elim0 i) := by
  have hc : ContinuousOn (simplexCoefficient ω S.toSmooth) (standardSimplex 0) := by
    have he : simplexCoefficient ω S.toSmooth = fun _ => simplexCoefficient ω S.toSmooth 0 :=
      funext (fun _ => congrArg (simplexCoefficient ω S.toSmooth) (Subsingleton.elim _ _))
    rw [he]
    exact continuousOn_const
  have h := (MultivariateRiemann.euclidean_simplex_source hc (Equiv.refl (Fin 0))).2.1.value
  rw [integral_simplex]
  change simplexIntegral ω S.toSmooth = _
  rw [simplexIntegral, ← h]
  change MultivariateRiemann.simplexZeroExtension
    (simplexCoefficient ω S.toSmooth ∘ (EuclideanSpace.equiv (Fin 0) ℝ).symm)
    (MultivariateRiemann.coordinatePermutation (Equiv.refl (Fin 0)) 0) = _
  have hz : MultivariateRiemann.coordinatePermutation (Equiv.refl (Fin 0)) 0 = 0 := map_zero _
  rw [hz, MultivariateRiemann.simplexZeroExtension, indicator_of_mem
    (show (0 : Fin 0 → ℝ) ∈ MultivariateRiemann.piSimplex 0 by simp [MultivariateRiemann.piSimplex])]
  simp only [Function.comp_apply, map_zero, simplexCoefficient, pullback_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- Forgetting a domain proof cannot identify different formal chains. -/
theorem forgetDomain_injective (n : ℕ) (V : Set E) : Function.Injective (forgetDomain n V) := by
  classical
  let back : Chain n E →+ DomainChain n V := FreeAbelianGroup.lift (fun S =>
    if h : MapsTo S.val (standardSimplex n) V then FreeAbelianGroup.of ⟨S,h⟩ else 0)
  have h : back.comp (forgetDomain n V) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro S
    simp [back, forgetDomain, S.property]
  intro c d he
  have hh := congrArg back he
  simpa only [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply] using hh

theorem domainBoundary_squared (n : ℕ) (V : Set E) (c : DomainChain (n+2) V) :
    domainBoundary n V (domainBoundary (n+1) V c) = 0 := by
  apply forgetDomain_injective n V
  simp only [forgetDomain_boundary, map_zero, boundary_squared]

/-- The two Cartesian parameter formulas used in the square triangulation. -/
theorem square_lower_formula (u : Param 2) :
    (affine ![((0,0) : ℝ × ℝ),(1,0),(1,1)]).val u = (u 0 + u 1, u 1) := by
  rw [affine_formula]
  simp [Fin.sum_univ_two]

theorem square_upper_formula (u : Param 2) :
    (affine ![((0,0) : ℝ × ℝ),(0,1),(1,1)]).val u = (u 1, u 0 + u 1) := by
  rw [affine_formula]
  simp [Fin.sum_univ_two]

/-- The first triangle covers exactly the lower half of the unit square. -/
theorem square_lower_image :
    (affine ![((0,0) : ℝ × ℝ),(1,0),(1,1)]).val '' standardSimplex 2 =
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1} := by
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [square_lower_formula]
    have h := hu.2
    simp only [Fin.sum_univ_two] at h
    exact ⟨hu.1 1, by linarith [hu.1 0], h⟩
  · intro hp
    let u : Param 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.1-p.2,p.2]
    refine ⟨u, ?_, ?_⟩
    · change (∀ i : Fin 2, 0 ≤ ![p.1-p.2,p.2] i) ∧ ∑ i : Fin 2, ![p.1-p.2,p.2] i ≤ 1
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two]
      exact ⟨⟨sub_nonneg.mpr hp.2.1, hp.1⟩, by linarith [hp.2.2]⟩
    · rw [square_lower_formula]
      change (p.1-p.2+p.2,p.2) = p
      simp

/-- The second triangle covers exactly the upper half of the unit square. -/
theorem square_upper_image :
    (affine ![((0,0) : ℝ × ℝ),(0,1),(1,1)]).val '' standardSimplex 2 =
      {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1} := by
  ext p
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [square_upper_formula]
    have h := hu.2
    simp only [Fin.sum_univ_two] at h
    exact ⟨hu.1 1, by linarith [hu.1 0], h⟩
  · intro hp
    let u : Param 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![p.2-p.1,p.1]
    refine ⟨u, ?_, ?_⟩
    · change (∀ i : Fin 2, 0 ≤ ![p.2-p.1,p.1] i) ∧ ∑ i : Fin 2, ![p.2-p.1,p.1] i ≤ 1
      simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two]
      exact ⟨⟨sub_nonneg.mpr hp.2.1, hp.1⟩, by linarith [hp.2.2]⟩
    · rw [square_upper_formula]
      change (p.1,p.2-p.1+p.1) = p
      simp

/-- The two actual parameter-triangle images cover the closed square. -/
theorem square_coverage :
    (affine ![((0,0) : ℝ × ℝ),(1,0),(1,1)]).val '' standardSimplex 2 ∪
      (affine ![((0,0) : ℝ × ℝ),(0,1),(1,1)]).val '' standardSimplex 2 =
        Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rw [square_lower_image, square_upper_image]
  ext p
  simp only [mem_union, mem_ofPred_eq, mem_prod, mem_Icc]
  constructor
  · rintro (h | h) <;> constructor <;> constructor <;> linarith [h.1, h.2.1, h.2.2]
  · intro h
    rcases le_total p.1 p.2 with hle | hle
    · exact Or.inr ⟨h.1.1, hle, h.2.2⟩
    · exact Or.inl ⟨h.2.1, hle, h.1.2⟩

end Rudin.Support.SmoothChains
