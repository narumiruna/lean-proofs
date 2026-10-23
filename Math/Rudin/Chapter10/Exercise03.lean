module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace Rudin.Chapter10
open Set Filter
open scoped Topology ContDiff

/-- Definition 10.5: on an open domain, all but one coordinate are unchanged. -/
def PrimitiveOn {n : ℕ} (U : Set (Fin n → ℝ)) (G : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  IsOpen U ∧ ∃ i : Fin n, ∀ x ∈ U, ∀ j, j ≠ i → G x j = x j

/-- The first m output coordinates, followed by the unchanged input coordinates. -/
def exercise03_partial {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ)) (m : ℕ)
    (x : Fin n → ℝ) (j : Fin n) : ℝ := if j.val < m then F x j else x j

/-- Exactly m factors, in source order G_(m-1) ... G_0. -/
def exercise03_comp {E : Type*} (G : ℕ → E → E) (m : ℕ) : E → E :=
  Nat.rec id (fun k f => G k ∘ f) m

@[simp] theorem exercise03_comp_zero {E : Type*} (G : ℕ → E → E) :
    exercise03_comp G 0 = id := rfl

@[simp] theorem exercise03_comp_succ {E : Type*} (G : ℕ → E → E) (m : ℕ) :
    exercise03_comp G (m+1) = G m ∘ exercise03_comp G m := rfl

theorem exercise03_normalization {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hA : HasFDerivAt F (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0) :
    HasFDerivAt (fun x => A.symm (F x)) (ContinuousLinearMap.id ℝ _) 0 := by
  have heq : (A.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).comp (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) =
      ContinuousLinearMap.id ℝ _ := by ext x j; simp
  exact heq ▸ A.symm.hasFDerivAt.comp 0 hA

/-- The partial maps all have identity derivative, so each has a genuine local
inverse. Both inverse identities hold on neighborhoods, not only at zero. -/
theorem exercise03_partial_inverse {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hd : HasFDerivAt F (ContinuousLinearMap.id ℝ _) 0) (m : ℕ) :
    ∃ H : (Fin n → ℝ) → (Fin n → ℝ), H 0 = 0 ∧ ContDiffAt ℝ 1 H 0 ∧
      HasFDerivAt H (ContinuousLinearMap.id ℝ _) 0 ∧
      (∀ᶠ x in 𝓝 0, H (exercise03_partial F m x) = x) ∧
      (∀ᶠ y in 𝓝 0, exercise03_partial F m (H y) = y) := by
  have hp : ContDiffAt ℝ 1 (exercise03_partial F m) 0 := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j.val < m
    · simpa [exercise03_partial, hj] using (contDiffAt_pi.mp hF j)
    · simpa [exercise03_partial, hj] using (contDiffAt_pi.mp
        (contDiffAt_id : ContDiffAt ℝ 1 (id : (Fin n → ℝ) → _) 0) j)
  have hp0 : exercise03_partial F m 0 = 0 := by ext j; simp [exercise03_partial, h0]
  have hpd : HasFDerivAt (exercise03_partial F m) (ContinuousLinearMap.id ℝ _) 0 := by
    apply hasFDerivAt_pi''
    intro j
    by_cases hj : j.val < m
    · simpa [exercise03_partial, hj] using (hasFDerivAt_pi'.mp hd j)
    · simpa [exercise03_partial, hj] using (hasFDerivAt_pi'.mp
        (hasFDerivAt_id (𝕜 := ℝ) (0 : Fin n → ℝ)) j)
  let e := ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)
  have hs := hp.hasStrictFDerivAt' (f' := e) hpd (by norm_num)
  refine ⟨hs.localInverse _ e 0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hp0] using hs.localInverse_apply_image
  · simpa [ContDiffAt.localInverse, hp0] using hp.to_localInverse (f' := e) hpd (by norm_num)
  · simpa [hp0, e] using hs.to_localInverse.hasFDerivAt
  · exact hs.eventually_left_inverse
  · simpa [hp0] using hs.eventually_right_inverse

/-- Extract an open C1 domain from a C1 germ. -/
theorem exercise03_open_domain {n : ℕ} {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : ContDiffAt ℝ 1 G 0) :
    ∃ U, IsOpen U ∧ (0 : Fin n → ℝ) ∈ U ∧ ContDiffOn ℝ 1 G U := by
  obtain ⟨s, hs, h⟩ := hG.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUs, hU, h0⟩ := mem_nhds_iff.mp hs
  exact ⟨U, hU, h0, h.mono hUs⟩

/-- Normalized local factorization. There are exactly n ordered factors; the
zero-dimensional case is the empty composition. Each factor fixes zero and
has identity derivative, and has an open C1 primitive domain. -/
theorem exercise03_factorization {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hd : HasFDerivAt F (ContinuousLinearMap.id ℝ _) 0) :
    ∃ G : ℕ → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ m < n, G m 0 = 0 ∧ HasFDerivAt (G m) (ContinuousLinearMap.id ℝ _) 0 ∧
        ∃ U, (0 : Fin n → ℝ) ∈ U ∧ PrimitiveOn U (G m) ∧ ContDiffOn ℝ 1 (G m) U) ∧
      (∀ᶠ x in 𝓝 0, F x = exercise03_comp G n x) := by
  classical
  choose H hH0 hHc hHd hHl hHr using exercise03_partial_inverse hF h0 hd
  let G : ℕ → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun m y j => if j.val = m then F (H m y) j else y j
  have hg : ∀ m, ContDiffAt ℝ 1 (G m) 0 := by
    intro m
    apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j.val = m
    · simpa [G, hj] using (contDiffAt_pi.mp
        ((show ContDiffAt ℝ 1 F (H m 0) by rw [hH0 m]; exact hF).comp 0 (hHc m)) j)
    · simpa [G, hj] using (contDiffAt_pi.mp
        (contDiffAt_id : ContDiffAt ℝ 1 (id : (Fin n → ℝ) → _) 0) j)
  have hgd : ∀ m, HasFDerivAt (G m) (ContinuousLinearMap.id ℝ _) 0 := by
    intro m
    have hc : HasFDerivAt (fun x => F (H m x)) (ContinuousLinearMap.id ℝ _) 0 := by
      simpa using ((show HasFDerivAt F (ContinuousLinearMap.id ℝ _) (H m 0) by
        rw [hH0 m]; exact hd).comp 0 (hHd m))
    apply hasFDerivAt_pi''
    intro j
    by_cases hj : j.val = m
    · simpa [G, hj] using hasFDerivAt_pi'.mp hc j
    · simpa [G, hj] using hasFDerivAt_pi'.mp (hasFDerivAt_id (𝕜 := ℝ) (0 : Fin n → ℝ)) j
  refine ⟨G, ?_, ?_⟩
  · intro m hm
    obtain ⟨U, hU, hz, hc⟩ := exercise03_open_domain (hg m)
    refine ⟨?_, hgd m, U, hz, ⟨hU, ⟨m,hm⟩, ?_⟩, hc⟩
    · ext j
      simp [G, hH0, h0]
    · intro x hx j hj
      have hj' : j.val ≠ m := fun h => hj (Fin.ext h)
      simp [G, hj']
  · have heq : ∀ m, ∀ᶠ x in 𝓝 0, exercise03_comp G m x = exercise03_partial F m x := by
      intro m
      induction m with
      | zero => exact Filter.Eventually.of_forall (by intro x; ext j; simp [exercise03_comp, exercise03_partial])
      | succ m ih =>
        filter_upwards [ih, hHl m] with x hx hi
        ext j
        simp only [exercise03_comp_succ, Function.comp_apply, hx, G, hi, exercise03_partial]
        split_ifs <;> first | rfl | omega
    filter_upwards [heq n] with x hx
    have hp : exercise03_partial F n x = F x := by
      ext j
      simp [exercise03_partial, j.isLt]
    exact hp ▸ hx.symm

/-- The source normalization followed by exactly n primitive factors. -/
theorem exercise03_a {n : ℕ} {E : Set (Fin n → ℝ)} (hE : IsOpen E)
    (hz : (0 : Fin n → ℝ) ∈ E) {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffOn ℝ 1 F E) (h0 : F 0 = 0)
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hA : HasFDerivAt F (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0) :
    ∃ G : ℕ → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ m < n, G m 0 = 0 ∧ HasFDerivAt (G m) (ContinuousLinearMap.id ℝ _) 0 ∧
        ∃ U, (0 : Fin n → ℝ) ∈ U ∧ PrimitiveOn U (G m) ∧ ContDiffOn ℝ 1 (G m) U) ∧
      (∀ᶠ x in 𝓝 0, A.symm (F x) = exercise03_comp G n x ∧
        F x = A (exercise03_comp G n x)) := by
  obtain ⟨G, hg, heq⟩ := exercise03_factorization
    (A.symm.contDiff.contDiffAt.comp 0 (hF.contDiffAt (hE.mem_nhds hz)))
    (by simp [h0]) (exercise03_normalization A hA)
  refine ⟨G, hg, heq.mono ?_⟩
  intro x hx
  exact ⟨hx, by rw [← hx]; simp⟩

/-- The recursive expression is the fold of a list of length exactly m. -/
theorem exercise03_comp_eq_fold {E : Type*} (G : ℕ → E → E) (m : ℕ) (x : E) :
    exercise03_comp G m x =
      (List.ofFn (fun i : Fin m => G i.val)).foldl (fun y f => f y) x := by
  induction m with
  | zero => simp [exercise03_comp]
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat]
    simpa only [exercise03_comp_succ, Function.comp_apply, Fin.val_castSucc, Fin.val_last] using
      congrArg (G m) ih

/-- The source conclusion with a family indexed by Fin n: exactly n primitive
maps, including an empty family when n = 0. A is the actual derivative at zero. -/
theorem exercise03_a_finite {n : ℕ} {E : Set (Fin n → ℝ)} (hE : IsOpen E)
    (hz : (0 : Fin n → ℝ) ∈ E) {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiffOn ℝ 1 F E) (h0 : F 0 = 0)
    (A : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hA : HasFDerivAt F (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) 0) :
    ∃ G : Fin n → (Fin n → ℝ) → (Fin n → ℝ),
      (∀ m, G m 0 = 0 ∧ HasFDerivAt (G m) (ContinuousLinearMap.id ℝ _) 0 ∧
        ∃ U, (0 : Fin n → ℝ) ∈ U ∧ PrimitiveOn U (G m) ∧ ContDiffOn ℝ 1 (G m) U) ∧
      (List.ofFn G).length = n ∧
      (∀ᶠ x in 𝓝 0,
        A.symm (F x) = (List.ofFn G).foldl (fun y g => g y) x ∧
        F x = A ((List.ofFn G).foldl (fun y g => g y) x)) := by
  obtain ⟨G, hg, heq⟩ := exercise03_a hE hz hF h0 A hA
  refine ⟨fun i => G i.val, fun i => hg i.val i.isLt, by simp, ?_⟩
  simpa only [exercise03_comp_eq_fold] using heq

/-- The planar flip, in ordered Cartesian coordinates. -/
def exercise03_flip (x : Fin 2 → ℝ) : Fin 2 → ℝ := ![x 1, x 0]

/-- No regularity assumption on either primitive factor is needed for the
obstruction. The second domain contains the image of the first. -/
theorem exercise03_b {U V : Set (Fin 2 → ℝ)}
    (hU : U ∈ 𝓝 (0 : Fin 2 → ℝ))
    {G H : (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hG : PrimitiveOn U G) (hH : PrimitiveOn V H) (hm : MapsTo G U V) :
    ¬ EqOn (H ∘ G) exercise03_flip U := by
  intro heq
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let p : Fin 2 → ℝ := ![r/2, 0]
  let q : Fin 2 → ℝ := ![0, r/2]
  have hz : (0 : Fin 2 → ℝ) ∈ U := mem_of_mem_nhds hU
  have hp : p ∈ U := by
    apply hball
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro i
    fin_cases i <;> simp [p, Real.norm_eq_abs, abs_of_pos hr] <;> linarith
  have hq : q ∈ U := by
    apply hball
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro i
    fin_cases i <;> simp [q, Real.norm_eq_abs, abs_of_pos hr] <;> linarith
  obtain ⟨_, i, hi⟩ := hG
  obtain ⟨_, j, hj⟩ := hH
  have hf (x) (hx : x ∈ U) (k : Fin 2) :
      H (G x) k = exercise03_flip x k := congrFun (heq hx) k
  fin_cases i <;> fin_cases j
  · have h1 := hj (G p) (hm hp) 1 (by decide)
    have h2 := hi p hp 1 (by decide)
    have h3 := hf p hp 1
    simp [exercise03_flip, p] at h2 h3
    linarith
  · have he (x) (hx : x ∈ U) : G x 0 = x 1 := by
      have h1 := hj (G x) (hm hx) 0 (by decide)
      have h2 := hf x hx 0
      simpa [exercise03_flip, ← h1] using h2
    have hg : G p = G 0 := by
      ext k
      fin_cases k
      · simp [he p hp, he 0 hz, p]
      · simp [hi p hp 1 (by decide), hi 0 hz 1 (by decide), p]
    have h1 := hf p hp 1
    have h2 := hf 0 hz 1
    rw [hg] at h1
    simp [exercise03_flip, p] at h1 h2
    linarith
  · have he (x) (hx : x ∈ U) : G x 1 = x 0 := by
      have h1 := hj (G x) (hm hx) 1 (by decide)
      have h2 := hf x hx 1
      simpa [exercise03_flip, ← h1] using h2
    have hg : G q = G 0 := by
      ext k
      fin_cases k
      · simp [hi q hq 0 (by decide), hi 0 hz 0 (by decide), q]
      · simp [he q hq, he 0 hz, q]
    have h1 := hf q hq 0
    have h2 := hf 0 hz 0
    rw [hg] at h1
    simp [exercise03_flip, q] at h1 h2
    linarith
  · have h1 := hj (G q) (hm hq) 0 (by decide)
    have h2 := hi q hq 0 (by decide)
    have h3 := hf q hq 0
    simp [exercise03_flip, q] at h2 h3
    linarith

end Rudin.Chapter10
