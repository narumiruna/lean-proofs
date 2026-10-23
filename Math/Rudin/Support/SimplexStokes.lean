module

public import Math.Rudin.Support.MultivariateRiemann
public import Math.Rudin.Support.SmoothChains
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Analytic Stokes on smooth simplexes

`stokes` proves the signed canonical-face identity in every positive source
dimension. `stokes_source` proves integrability and the literal repeated source
integral in every coordinate order. The hypotheses require C¹ forms and C² maps
only on open neighborhoods of the image and the compact source simplex.

The proof uses coordinate FTC, the frozen scalar slice comparison, scalar
barycentric reflection, and alternating-map algebra. Faces restrict full maps.
`euclideanFace_eq_relabel` identifies them with the frozen `SmoothChains` faces;
`domainChain_stokes` extends the identity to integer chains in an open domain.
No higher-degree orientation-quotient integral descent is claimed here.

Dimension-zero integration is evaluation. The one-dimensional signs give
terminal minus initial value. The two-dimensional signs are `+,-,+`. The
nonlinear, nonhorizontal check has nonconstant exterior coefficient `4y` and
both integrals equal to `2/3`.

Sources: Rudin Theorem 10.33 and Remarks 10.35, PDF pages 281–285.
-/

@[expose] public section
noncomputable section

namespace Rudin.Support.SimplexStokes

open Set MeasureTheory SimplexIntegration MultivariateRiemann

/-- The closed fiber includes both endpoints, even when its length is zero. -/
theorem cons_mem_simplex {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ piSimplex n)
    {t : ℝ} (ht : t ∈ Icc 0 (1 - ∑ i, x i)) :
    Fin.cons t x ∈ piSimplex (n+1) := by
  constructor
  · intro i
    refine Fin.cases ht.1 (fun j => hx.1 j) i
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    linarith [ht.2]

/-- Slice integration needs continuity only on the closed simplex. -/
theorem simplex_integral_succ_of_continuousOn {n : ℕ}
    {f : (Fin (n+1) → ℝ) → ℝ} (hf : ContinuousOn f (piSimplex (n+1))) :
    (∫ x in piSimplex (n+1), f x) =
      ∫ x in piSimplex n, ∫ t in 0..(1 - ∑ i, x i), f (Fin.cons t x) := by
  obtain ⟨g, hg, he⟩ := continuous_extension (piSimplex_isCompact (n+1)).isClosed hf
  rw [← setIntegral_congr_fun (piSimplex_isCompact (n+1)).measurableSet he,
    simplex_integral_succ hg]
  apply setIntegral_congr_fun (piSimplex_isCompact n).measurableSet
  intro x hx
  apply intervalIntegral.integral_congr
  intro t ht
  exact he (cons_mem_simplex hx (by
    simpa only [uIcc_of_le (sub_nonneg.mpr hx.2)] using ht))

/-- The actual derivative in the first coordinate. -/
def firstPartial {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single 0 1)

/-- C¹ on an open neighborhood supplies continuous ambient derivatives on the
closed simplex. No value outside the neighborhood is constrained. -/
theorem firstPartial_continuousOn {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : ContinuousOn (firstPartial f) (piSimplex (n+1)) := by
  intro x hx
  have h := (hf x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))
  exact ((h.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt

/-- Coordinate FTC on each closed fiber follows from neighborhood C¹ regularity. -/
theorem firstPartial_slice {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) {x : Fin n → ℝ} (hx : x ∈ piSimplex n) :
    (∫ t in 0..(1 - ∑ i, x i), firstPartial f (Fin.cons t x)) =
      f (Fin.cons (1 - ∑ i, x i) x) - f (Fin.cons 0 x) := by
  have hm : MapsTo (fun t => Fin.cons t x) (Icc 0 (1 - ∑ i, x i))
      (piSimplex (n+1)) := fun _ ht => cons_mem_simplex hx ht
  have hc : ContinuousOn (fun t => firstPartial f (Fin.cons t x))
      (Icc 0 (1 - ∑ i, x i)) :=
    (firstPartial_continuousOn hU hsub hf).comp (by fun_prop) hm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => f (Fin.cons t x))
  · intro t ht
    have ht' : t ∈ Icc 0 (1 - ∑ i, x i) := by
      simpa only [uIcc_of_le (sub_nonneg.mpr hx.2)] using ht
    have hd : HasDerivAt (fun t : ℝ => (Fin.cons t x : Fin (n+1) → ℝ))
        (Pi.single 0 1) t := by
      apply hasDerivAt_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using! hasDerivAt_id t
      · simpa using! hasDerivAt_const t (x j)
    exact ((hf _ (hsub (hm ht'))).contDiffAt
      (hU.mem_nhds (hsub (hm ht')))).differentiableAt (by norm_num)
        |>.hasFDerivAt.comp_hasDerivAt t hd
  · exact ContinuousOn.intervalIntegrable_of_Icc (sub_nonneg.mpr hx.2) hc

/-- The analytic two-face difference for one coordinate, in every dimension.
The hypotheses prove integrability rather than assume an integral identity. -/
theorem firstPartial_integral {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    IntegrableOn (firstPartial f) (piSimplex (n+1)) ∧
    (∫ x in piSimplex (n+1), firstPartial f x) =
      ∫ x in piSimplex n, (f (Fin.cons (1 - ∑ i, x i) x) - f (Fin.cons 0 x)) := by
  have hc := firstPartial_continuousOn hU hsub hf
  refine ⟨hc.integrableOn_compact (piSimplex_isCompact (n+1)), ?_⟩
  rw [simplex_integral_succ_of_continuousOn hc]
  exact setIntegral_congr_fun (piSimplex_isCompact n).measurableSet
    (fun x hx => firstPartial_slice hU hsub hf hx)

/-- Move the chosen coordinate to the first integration position. The remaining
coordinates keep their original order. -/
def slicePermutation {n : ℕ} (i : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv n).trans (finSuccEquiv' i).symm

@[simp] theorem slicePermutation_cons {n : ℕ} (i : Fin (n+1)) (t : ℝ)
    (x : Fin n → ℝ) :
    coordinatePermutation (slicePermutation i) (Fin.cons t x) = i.insertNth t x := by
  ext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;>
    simp [coordinatePermutation_apply, slicePermutation]

@[simp] theorem slicePermutation_single {n : ℕ} (i : Fin (n+1)) :
    coordinatePermutation (slicePermutation i) (Pi.single 0 (1 : ℝ)) = Pi.single i 1 := by
  ext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;>
    simp [coordinatePermutation_apply, slicePermutation, Fin.succAbove_ne]

/-- Slicing in an arbitrary coordinate, in the canonical increasing order on
the other coordinates. -/
theorem simplex_integral_insertNth {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex (n+1))) (i : Fin (n+1)) :
    (∫ x in piSimplex (n+1), f x) =
      ∫ x in piSimplex n, ∫ t in 0..(1 - ∑ j, x j), f (i.insertNth t x) := by
  let c := coordinatePermutation (slicePermutation i)
  have hc : MapsTo c (piSimplex (n+1)) (piSimplex (n+1)) := by
    intro x hx
    change x ∈ c ⁻¹' piSimplex (n+1)
    rwa [permutation_preimage_simplex]
  have he := (permutation_volume (slicePermutation i)).setIntegral_preimage_emb
    c.toHomeomorph.measurableEmbedding f (piSimplex (n+1))
  rw [permutation_preimage_simplex] at he
  rw [← he]
  change (∫ x in piSimplex (n+1), (f ∘ c) x) = _
  rw [simplex_integral_succ_of_continuousOn (hf.comp c.continuous.continuousOn hc)]
  simp only [Function.comp_apply, c, slicePermutation_cons]

/-- Exchange a coordinate with the missing barycentric coordinate. -/
def barycentricReflection {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    Fin (n+1) → ℝ := i.insertNth (1 - ∑ j, x j) (i.removeNth x)

@[simp] theorem sum_insertNth {n : ℕ} (i : Fin (n+1)) (t : ℝ) (x : Fin n → ℝ) :
    ∑ j, i.insertNth t x j = t + ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

@[simp] theorem barycentricReflection_insertNth {n : ℕ} (i : Fin (n+1))
    (t : ℝ) (x : Fin n → ℝ) :
    barycentricReflection i (i.insertNth t x) =
      i.insertNth ((1 - ∑ j, x j) - t) x := by
  simp only [barycentricReflection, sum_insertNth, Fin.removeNth_insertNth]
  congr 1
  ring

theorem barycentricReflection_continuous {n : ℕ} (i : Fin (n+1)) :
    Continuous (barycentricReflection i) := by
  unfold barycentricReflection Fin.removeNth
  fun_prop

theorem barycentricReflection_mapsTo {n : ℕ} (i : Fin (n+1)) :
    MapsTo (barycentricReflection i) (piSimplex (n+1)) (piSimplex (n+1)) := by
  intro x hx
  constructor
  · intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa [barycentricReflection] using sub_nonneg.mpr hx.2
    · simpa [barycentricReflection, Fin.removeNth] using hx.1 (i.succAbove k)
  · simp only [barycentricReflection, sum_insertNth, Fin.removeNth]
    have hs := Fin.sum_univ_succAbove x i
    linarith [hx.1 i]

/-- A barycentric reflection preserves simplex integrals. The proof uses scalar
slice substitution, not an unproved affine-volume normalization. -/
theorem integral_barycentricReflection {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex (n+1))) (i : Fin (n+1)) :
    (∫ x in piSimplex (n+1), f (barycentricReflection i x)) =
      ∫ x in piSimplex (n+1), f x := by
  have hc := hf.comp (barycentricReflection_continuous i).continuousOn
    (barycentricReflection_mapsTo i)
  change (∫ x in piSimplex (n+1), (f ∘ barycentricReflection i) x) = _
  rw [simplex_integral_insertNth hc i, simplex_integral_insertNth hf i]
  apply setIntegral_congr_fun (piSimplex_isCompact n).measurableSet
  intro x hx
  simp only [Function.comp_apply, barycentricReflection_insertNth]
  have he := intervalIntegral.integral_comp_sub_left (fun t => f (i.insertNth t x))
    (a := (0 : ℝ)) (b := 1 - ∑ j, x j) (1 - ∑ j, x j)
  simpa only [sub_self, sub_zero] using he

/-- The sloping face, parameterized by all coordinates except `i`. -/
def upperFace {n : ℕ} (i : Fin (n+1)) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  i.insertNth (1 - ∑ j, x j) x

theorem upperFace_continuous {n : ℕ} (i : Fin (n+1)) : Continuous (upperFace i) := by
  unfold upperFace
  fun_prop

theorem upperFace_mapsTo {n : ℕ} (i : Fin (n+1)) :
    MapsTo (upperFace i) (piSimplex n) (piSimplex (n+1)) := by
  intro x hx
  constructor
  · intro j
    refine Fin.succAboveCases i ?_ (fun k => ?_) j
    · simpa [upperFace] using sub_nonneg.mpr hx.2
    · simpa [upperFace] using hx.1 k
  · simp [upperFace]

/-- The noncanonical sloping chart is a reflection and a coordinate permutation
of the canonical chart. This identity is pointwise, including the boundary. -/
theorem upperFace_succ {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → ℝ) :
    upperFace i.succ x = upperFace 0
      (coordinatePermutation (slicePermutation i) (barycentricReflection 0 x)) := by
  obtain ⟨a, y, rfl⟩ := Fin.exists_cons x
  have hb : barycentricReflection 0 (Fin.cons a y) = Fin.cons (1 - (a + ∑ j, y j)) y := by
    simp [barycentricReflection, Fin.sum_univ_succ]
  rw [hb, slicePermutation_cons]
  simp only [upperFace, sum_insertNth, Fin.insertNth_zero, Fin.insertNth_succ_cons]
  congr 1 <;> (try simp [Fin.sum_univ_succ]); ring

/-- All sloping-face scalar charts have the same integral. This is a proved
change of parameters, not a face-cancellation hypothesis. -/
theorem integral_upperFace {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : ContinuousOn f (piSimplex (n+1))) (i : Fin (n+1)) :
    (∫ x in piSimplex n, f (upperFace i x)) =
      ∫ x in piSimplex n, f (upperFace 0 x) := by
  cases n with
  | zero => have : i = 0 := Fin.eq_zero i; subst i; rfl
  | succ n =>
    refine Fin.cases rfl (fun j => ?_) i
    let c := coordinatePermutation (slicePermutation j)
    have hm : MapsTo c (piSimplex (n+1)) (piSimplex (n+1)) := by
      intro x hx
      change x ∈ c ⁻¹' piSimplex (n+1)
      rwa [permutation_preimage_simplex]
    have hc := hf.comp (upperFace_continuous 0).continuousOn (upperFace_mapsTo 0)
    have hcc := hc.comp c.continuous.continuousOn hm
    simp_rw [upperFace_succ]
    change (∫ x in piSimplex (n+1), ((f ∘ upperFace 0) ∘ c)
      (barycentricReflection 0 x)) = _
    rw [integral_barycentricReflection hcc 0]
    have he := (permutation_volume (slicePermutation j)).setIntegral_preimage_emb
      c.toHomeomorph.measurableEmbedding (f ∘ upperFace 0) (piSimplex (n+1))
    rw [permutation_preimage_simplex] at he
    exact he

/-- The actual coordinate partial derivative, without a supplied derivative field. -/
def coordinatePartial {n : ℕ} (i : Fin (n+1)) (f : (Fin (n+1) → ℝ) → ℝ)
    (x : Fin (n+1) → ℝ) : ℝ := fderiv ℝ f x (Pi.single i 1)

/-- Coordinate FTC in every direction for a C¹ function on an open neighborhood. -/
theorem coordinatePartial_integral {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (i : Fin (n+1)) :
    IntegrableOn (coordinatePartial i f) (piSimplex (n+1)) ∧
    (∫ x in piSimplex (n+1), coordinatePartial i f x) =
      ∫ x in piSimplex n, (f (i.insertNth (1 - ∑ j, x j) x) - f (i.insertNth 0 x)) := by
  let c := coordinatePermutation (slicePermutation i)
  have hm : MapsTo c (piSimplex (n+1)) (piSimplex (n+1)) := by
    intro x hx
    change x ∈ c ⁻¹' piSimplex (n+1)
    rwa [permutation_preimage_simplex]
  have hsub' : piSimplex (n+1) ⊆ c ⁻¹' U := fun x hx => hsub (hm hx)
  have hf' : ContDiffOn ℝ 1 (f ∘ c) (c ⁻¹' U) :=
    hf.comp c.contDiff.contDiffOn (fun _ h => h)
  have hc : ContinuousOn (coordinatePartial i f) (piSimplex (n+1)) := by
    intro x hx
    exact ((((hf x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))).continuousAt_fderiv
      (by norm_num)).clm_apply continuousAt_const).continuousWithinAt
  have heq : EqOn (firstPartial (f ∘ c)) ((coordinatePartial i f) ∘ c)
      (piSimplex (n+1)) := by
    intro x hx
    rw [firstPartial, fderiv_comp x
      (((hf _ (hsub (hm hx))).contDiffAt (hU.mem_nhds (hsub (hm hx)))).differentiableAt
        (by norm_num)) c.differentiableAt]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv,
      ContinuousLinearEquiv.coe_coe, c, slicePermutation_single]
    rfl
  have he := (permutation_volume (slicePermutation i)).setIntegral_preimage_emb
    c.toHomeomorph.measurableEmbedding (coordinatePartial i f) (piSimplex (n+1))
  rw [permutation_preimage_simplex] at he
  refine ⟨hc.integrableOn_compact (piSimplex_isCompact (n+1)), ?_⟩
  rw [← he]
  change (∫ x in piSimplex (n+1), ((coordinatePartial i f) ∘ c) x) = _
  rw [← setIntegral_congr_fun (piSimplex_isCompact (n+1)).measurableSet heq,
    (firstPartial_integral (hU.preimage c.continuous) hsub' hf').2]
  simp only [Function.comp_apply, c, slicePermutation_cons]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Subtracting the first vector from all later vectors preserves an alternating
map. The proof changes one coordinate at a time. -/
theorem alternating_sub_first {n : ℕ} (A : E [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (v : Fin (n+1) → E) :
    A (Fin.cons (v 0) (fun j => v j.succ - v 0)) = A v := by
  classical
  have hs (s : Finset (Fin (n+1))) (h0 : 0 ∉ s) :
      A (fun j => if j ∈ s then v j - v 0 else v j) = A v := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      have h0' : 0 ≠ j ∧ 0 ∉ s := by simpa only [Finset.mem_insert, not_or] using h0
      have hj0 : j ≠ 0 := Ne.symm h0'.1
      have h0s : 0 ∉ s := h0'.2
      let w := fun k => if k ∈ s then v k - v 0 else v k
      have hw0 : w 0 = v 0 := ite_eq_right h0s
      have hwj : w j = v j := ite_eq_right hj
      have he : (fun k => if k ∈ insert j s then v k - v 0 else v k) =
          Function.update w j (w j - w 0) := by
        funext k
        by_cases hk : k = j
        · subst k; simp [hwj, hw0]
        · simp [Finset.mem_insert, hk, w]
      rw [he]
      change A.toAlternatingMap (Function.update w j (w j - w 0)) = _
      rw [A.toAlternatingMap.map_update_sub]
      have hz : A.toAlternatingMap (Function.update w j (w 0)) = 0 :=
        A.toAlternatingMap.map_update_self w hj0
      rw [hz, sub_zero, Function.update_eq_self]
      exact ih h0s
  have h := hs (Finset.univ.erase 0) (by simp)
  convert h using 1
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

/-- The sloping-face alternating expansion has exactly the Stokes signs. -/
theorem alternating_upperFace {n : ℕ}
    (A : (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    A (fun j => Pi.single j.succ 1 - Pi.single 0 1) =
      ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
        A (i.removeNth (fun j => (Pi.single j 1 : Fin (n+1) → ℝ))) := by
  let l : (Fin (n+1) → ℝ) →L[ℝ] ℝ := ∑ j, ContinuousLinearMap.proj j
  let B := ContinuousAlternatingMap.alternatizeUncurryFin (l.smulRight A)
  have hl (j : Fin (n+1)) : l (Pi.single j 1) = 1 := by
    simp [l]
  have he := alternating_sub_first B (fun j => (Pi.single j 1 : Fin (n+1) → ℝ))
  have hright : B (fun j => (Pi.single j 1 : Fin (n+1) → ℝ)) =
      ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
        A (i.removeNth (fun j => (Pi.single j 1 : Fin (n+1) → ℝ))) := by
    simp [B, ContinuousAlternatingMap.alternatizeUncurryFin_apply, hl]
  have hleft : B (Fin.cons (Pi.single 0 1)
      (fun j => Pi.single j.succ 1 - Pi.single 0 1)) =
        A (fun j => Pi.single j.succ 1 - Pi.single 0 1) := by
    simp [B, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      Fin.sum_univ_succ, hl, map_sub]
  rw [hleft, hright] at he
  exact he

/-- The linear part of the canonical sloping face. -/
def upperLinear (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.cons (-∑ j, ContinuousLinearMap.proj j)
    (fun j => ContinuousLinearMap.proj j))

@[simp] theorem upperLinear_apply {n : ℕ} (x : Fin n → ℝ) :
    upperLinear n x = Fin.cons (-∑ j, x j) x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [upperLinear]

theorem upperFace_zero_eq {n : ℕ} (x : Fin n → ℝ) :
    upperFace 0 x = Pi.single 0 1 + upperLinear n x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [upperFace, sub_eq_add_neg]

/-- The linear canonical face with coordinate `i` equal to zero. -/
def lowerLinear {n : ℕ} (i : Fin (n+1)) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (i.insertNth 0 (fun j => ContinuousLinearMap.proj j))

@[simp] theorem lowerLinear_apply {n : ℕ} (i : Fin (n+1)) (x : Fin n → ℝ) :
    lowerLinear i x = i.insertNth 0 x := by
  ext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp [lowerLinear]

theorem upperFace_hasFDerivAt {n : ℕ} (x : Fin n → ℝ) :
    HasFDerivAt (upperFace (0 : Fin (n+1))) (upperLinear n) x := by
  have h := ((upperLinear n).hasFDerivAt (x := x)).const_add (Pi.single 0 (1 : ℝ))
  simpa only [← upperFace_zero_eq] using h

@[simp] theorem upperLinear_single {n : ℕ} (j : Fin n) :
    upperLinear n (Pi.single j 1) = Pi.single j.succ 1 - Pi.single 0 1 := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [Pi.single_apply]

@[simp] theorem lowerLinear_single {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    lowerLinear i (Pi.single j 1) = Pi.single (i.succAbove j) 1 := by
  ext k
  refine Fin.succAboveCases i ?_ (fun l => ?_) k <;>
    simp [Pi.single_apply, Fin.succAbove_right_injective.eq_iff]

/-- The canonical affine faces in the order `[e₀,…,eₙ]`, then the faces
`[0,e₀,…,omit eᵢ,…,eₙ]`. -/
def standardFace {n : ℕ} (i : Fin (n+2)) : (Fin n → ℝ) → (Fin (n+1) → ℝ) :=
  Fin.cases (upperFace 0) (fun j => lowerLinear j) i

@[simp] theorem standardFace_zero {n : ℕ} :
    standardFace (0 : Fin (n+2)) = upperFace 0 := rfl

@[simp] theorem standardFace_succ {n : ℕ} (i : Fin (n+1)) :
    standardFace i.succ = lowerLinear i := rfl

theorem standardFace_contDiff {n : ℕ} (i : Fin (n+2)) :
    ContDiff ℝ 2 (standardFace i) := by
  refine Fin.cases ?_ (fun j => (lowerLinear j).contDiff) i
  simp only [standardFace_zero, funext upperFace_zero_eq]
  exact contDiff_const.add (upperLinear n).contDiff

theorem standardFace_mapsTo {n : ℕ} (i : Fin (n+2)) :
    MapsTo (standardFace i) (piSimplex n) (piSimplex (n+1)) := by
  refine Fin.cases (upperFace_mapsTo 0) (fun j => ?_) i
  intro x hx
  constructor
  · intro k
    refine Fin.succAboveCases j ?_ (fun l => ?_) k <;> simp [hx.1]
  · simpa using hx.2

/-- The increasing coordinate tuple with coordinate `i` omitted. -/
def omittedCoefficient {n : ℕ} (ω : Form n (Fin (n+1) → ℝ)) (i : Fin (n+1))
    (x : Fin (n+1) → ℝ) : ℝ :=
  ω x (fun j => Pi.single (i.succAbove j) 1)

theorem omittedCoefficient_contDiffOn {n : ℕ} {ω : Form n (Fin (n+1) → ℝ)}
    {U : Set (Fin (n+1) → ℝ)} (hω : ContDiffOn ℝ 1 ω U) (i : Fin (n+1)) :
    ContDiffOn ℝ 1 (omittedCoefficient ω i) U :=
  (ContinuousAlternatingMap.apply ℝ (Fin (n+1) → ℝ) ℝ
    (fun j => Pi.single (i.succAbove j) 1)).contDiff.comp_contDiffOn hω

/-- The local coordinate Stokes calculation, before replacing tangents by the
actual derivatives of the canonical affine faces. -/
theorem coordinate_stokes_coefficients {n : ℕ} {ω : Form n (Fin (n+1) → ℝ)}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hω : ContDiffOn ℝ 1 ω U) :
    (∫ x in piSimplex (n+1), extDeriv ω x (fun j => Pi.single j 1)) =
      (∫ x in piSimplex n,
        ω (upperFace 0 x) (fun j => Pi.single j.succ 1 - Pi.single 0 1)) -
      ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
        ∫ x in piSimplex n, omittedCoefficient ω i (i.insertNth 0 x) := by
  have hC (i) := omittedCoefficient_contDiffOn hω i
  have hc (i) := (hC i).continuousOn.mono hsub
  have hu (i) : ContinuousOn (fun x => omittedCoefficient ω i (upperFace 0 x))
      (piSimplex n) := (hc i).comp (upperFace_continuous 0).continuousOn (upperFace_mapsTo 0)
  have hl (i : Fin (n+1)) : ContinuousOn (fun x => omittedCoefficient ω i (i.insertNth 0 x))
      (piSimplex n) := by
    apply (hc i).comp (by fun_prop)
    intro x hx
    constructor
    · intro j
      refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp [hx.1]
    · simpa using hx.2
  have hp (i) := coordinatePartial_integral hU hsub (hC i) i
  have he (i) : (∫ x in piSimplex (n+1), coordinatePartial i (omittedCoefficient ω i) x) =
      (∫ x in piSimplex n, omittedCoefficient ω i (upperFace 0 x)) -
        ∫ x in piSimplex n, omittedCoefficient ω i (i.insertNth 0 x) := by
    rw [(hp i).2]
    change (∫ x in piSimplex n, (omittedCoefficient ω i ∘ upperFace i) x -
      omittedCoefficient ω i (i.insertNth 0 x)) = _
    rw [integral_sub
      (((hc i).comp (upperFace_continuous i).continuousOn (upperFace_mapsTo i)).integrableOn_compact
        (piSimplex_isCompact n)) ((hl i).integrableOn_compact (piSimplex_isCompact n))]
    exact congrArg (fun z => z - ∫ x in piSimplex n, omittedCoefficient ω i (i.insertNth 0 x))
      (integral_upperFace (hc i) i)
  have hext : (∫ x in piSimplex (n+1), extDeriv ω x (fun j => Pi.single j 1)) =
      ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
        ∫ x in piSimplex (n+1), coordinatePartial i (omittedCoefficient ω i) x := by
    calc
      _ = ∫ x in piSimplex (n+1), ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
          coordinatePartial i (omittedCoefficient ω i) x := by
        apply setIntegral_congr_fun (piSimplex_isCompact (n+1)).measurableSet
        intro x hx
        dsimp only
        rw [extDeriv_apply (((hω x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))).differentiableAt
            (by norm_num))]
        simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
        rfl
      _ = _ := by
        rw [integral_finsetSum _ (fun i _ => (hp i).1.const_mul _)]
        simp only [integral_const_mul]
  have hupper : (∫ x in piSimplex n,
      ω (upperFace 0 x) (fun j => Pi.single j.succ 1 - Pi.single 0 1)) =
        ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
          ∫ x in piSimplex n, omittedCoefficient ω i (upperFace 0 x) := by
    simp_rw [alternating_upperFace]
    change (∫ x in piSimplex n, ∑ i : Fin (n+1), (-1 : ℝ) ^ i.val *
      omittedCoefficient ω i (upperFace 0 x)) = _
    rw [integral_finsetSum _ (fun i _ =>
      ((hu i).integrableOn_compact (piSimplex_isCompact n)).const_mul _)]
    simp only [integral_const_mul]
  rw [hext, hupper]
  simp_rw [he, mul_sub]
  rw [Finset.sum_sub_distrib]

@[simp] theorem pullback_standardFace_zero {n : ℕ} (ω : Form n (Fin (n+1) → ℝ))
    (x : Fin n → ℝ) :
    pullback ω (standardFace (0 : Fin (n+2))) x (fun j => Pi.single j 1) =
      ω (upperFace 0 x) (fun j => Pi.single j.succ 1 - Pi.single 0 1) := by
  simp only [standardFace_zero, pullback_apply, (upperFace_hasFDerivAt x).fderiv,
    upperLinear_single]

@[simp] theorem pullback_standardFace_succ {n : ℕ} (ω : Form n (Fin (n+1) → ℝ))
    (i : Fin (n+1)) (x : Fin n → ℝ) :
    pullback ω (standardFace i.succ) x (fun j => Pi.single j 1) =
      omittedCoefficient ω i (i.insertNth 0 x) := by
  simp only [standardFace_succ, pullback_apply, ContinuousLinearMap.fderiv]
  change ω (lowerLinear i x) (fun j => lowerLinear i (Pi.single j 1)) = _
  simp only [lowerLinear_single]
  rw [lowerLinear_apply]
  rfl

/-- Stokes for an arbitrary-degree form on the standard coordinate simplex.
Every face integrand is the actual pullback by the canonical affine map. -/
theorem coordinate_stokes {n : ℕ} {ω : Form n (Fin (n+1) → ℝ)}
    {U : Set (Fin (n+1) → ℝ)} (hU : IsOpen U) (hsub : piSimplex (n+1) ⊆ U)
    (hω : ContDiffOn ℝ 1 ω U) :
    (∫ x in piSimplex (n+1), extDeriv ω x (fun j => Pi.single j 1)) =
      ∑ i : Fin (n+2), (-1 : ℝ) ^ i.val *
        ∫ x in piSimplex n, pullback ω (standardFace i) x (fun j => Pi.single j 1) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ, mul_neg_one,
    neg_mul, Finset.sum_neg_distrib, pullback_standardFace_zero, pullback_standardFace_succ]
  exact coordinate_stokes_coefficients hU hsub hω

/-- Local C² maps and local C¹ forms give a local C¹ actual pullback, in any degree. -/
theorem pullback_contDiffAt {n : ℕ} {ω : Form n F} {S : E → F} {x : E}
    (hω : ContDiffAt ℝ 1 ω (S x)) (hS : ContDiffAt ℝ 2 S x) :
    ContDiffAt ℝ 1 (pullback ω S) x := by
  have hp := (ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
    (𝕜 := ℝ) (ι := Fin n) (G := ℝ) (fderiv ℝ S x)).contDiffAt (n := 1)
  exact (hp.comp x (hS.fderiv_right (by norm_num))).clm_apply
    (hω.comp x (hS.of_le (by norm_num)))

/-- Stokes for a full C² map from a coordinate simplex. Only open neighborhoods
of the source simplex and its image carry regularity assumptions. -/
theorem map_stokes {n : ℕ} (ω : Form n E) (S : (Fin (n+1) → ℝ) → E)
    {W : Set (Fin (n+1) → ℝ)} (hW : IsOpen W) (hsource : piSimplex (n+1) ⊆ W)
    (hS : ContDiffOn ℝ 2 S W) {U : Set E} (hU : IsOpen U)
    (hω : ContDiffOn ℝ 1 ω U) (himage : S '' piSimplex (n+1) ⊆ U) :
    (∫ x in piSimplex (n+1), pullback (extDeriv ω) S x (fun j => Pi.single j 1)) =
      ∑ i : Fin (n+2), (-1 : ℝ) ^ i.val *
        ∫ x in piSimplex n, pullback ω (S ∘ standardFace i) x (fun j => Pi.single j 1) := by
  let V := W ∩ S ⁻¹' U
  have hV : IsOpen V := hS.continuousOn.isOpen_inter_preimage hW hU
  have hsub : piSimplex (n+1) ⊆ V := fun x hx => ⟨hsource hx, himage ⟨x, hx, rfl⟩⟩
  have hη : ContDiffOn ℝ 1 (pullback ω S) V := by
    intro x hx
    exact (pullback_contDiffAt ((hω _ hx.2).contDiffAt (hU.mem_nhds hx.2))
      ((hS x hx.1).contDiffAt (hW.mem_nhds hx.1))).contDiffWithinAt
  have hdS (x) (hx : x ∈ piSimplex (n+1)) : ContDiffAt ℝ 2 S x :=
    (hS x (hsource hx)).contDiffAt (hW.mem_nhds (hsource hx))
  calc
    _ = ∫ x in piSimplex (n+1), extDeriv (pullback ω S) x (fun j => Pi.single j 1) := by
      apply setIntegral_congr_fun (piSimplex_isCompact (n+1)).measurableSet
      intro x hx
      dsimp only
      rw [exterior_pullback ω S x
        (((hω _ (himage ⟨x, hx, rfl⟩)).contDiffAt
          (hU.mem_nhds (himage ⟨x, hx, rfl⟩))).differentiableAt (by norm_num)) (hdS x hx)]
    _ = _ := by
      rw [coordinate_stokes hV hsub hη]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply setIntegral_congr_fun (piSimplex_isCompact n).measurableSet
      intro x hx
      dsimp only
      rw [pullback_comp ω S (standardFace i) x
        ((hdS _ (standardFace_mapsTo i hx)).differentiableAt (by norm_num))
        ((standardFace_contDiff i).differentiable (by norm_num) x)]

/-- C¹ regularity gives continuity of the actual exterior derivative. -/
theorem extDeriv_continuousAt {n : ℕ} {ω : Form n E} {x : E}
    (hω : ContDiffAt ℝ 1 ω x) : ContinuousAt (extDeriv ω) x :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).continuous.continuousAt.comp
    (hω.continuousAt_fderiv (by norm_num))

/-- Ambient exterior derivatives are continuous on every subset of a C¹ open domain. -/
theorem extDeriv_continuousOn {n : ℕ} {ω : Form n E} {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U) : ContinuousOn (extDeriv ω) U := by
  intro x hx
  exact (extDeriv_continuousAt ((hω x hx).contDiffAt (hU.mem_nhds hx))).continuousWithinAt

/-- Exterior pullback on the whole closed simplex, with only neighborhood hypotheses. -/
theorem simplex_exterior_pullback {n k : ℕ} (ω : Form k E) (S : SmoothSimplex n E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex n ⊆ U) :
    EqOn (extDeriv (pullback ω S.toFun)) (pullback (extDeriv ω) S.toFun)
      (standardSimplex n) := by
  intro x hx
  exact exterior_pullback ω S.toFun x
    (((hω _ (himage ⟨x, hx, rfl⟩)).contDiffAt
      (hU.mem_nhds (himage ⟨x, hx, rfl⟩))).differentiableAt (by norm_num))
    ((S.smooth x (S.contains hx)).contDiffAt
      (S.isOpen_neighborhood.mem_nhds (S.contains hx)))

/-- Existence and literal source comparison for the exterior integral. -/
theorem exterior_integral_source {n : ℕ} (ω : Form n E) (S : SmoothSimplex (n+1) E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex (n+1) ⊆ U) (σ : Equiv.Perm (Fin (n+1))) :
    IntegrableOn (simplexCoefficient (extDeriv ω) S) (standardSimplex (n+1)) ∧
    HasSourceIntegral (n+1) 0 1
      (simplexZeroExtension (simplexCoefficient (extDeriv ω) S ∘
        (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm) ∘ coordinatePermutation σ)
      (simplexIntegral (extDeriv ω) S) := by
  have hc := (extDeriv_continuousOn hU hω).mono himage
  exact ⟨simplexCoefficient_integrable _ S hc, simplexIntegral_source _ S hc σ⟩

/-- Canonical affine face map in Euclidean coordinates. -/
def euclideanFace {n : ℕ} (i : Fin (n+2)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1)) :=
  (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm ∘ standardFace i ∘
    (EuclideanSpace.equiv (Fin n) ℝ)

theorem euclideanFace_contDiff {n : ℕ} (i : Fin (n+2)) :
    ContDiff ℝ 2 (euclideanFace i) :=
  (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm.contDiff.comp
    ((standardFace_contDiff i).comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff)

theorem euclideanFace_mapsTo {n : ℕ} (i : Fin (n+2)) :
    MapsTo (euclideanFace i) (standardSimplex n) (standardSimplex (n+1)) :=
  fun _ hx => standardFace_mapsTo i hx

/-- Restrict the full C² map to a canonical face. The open neighborhood is the
actual preimage of the original neighborhood. -/
def face {n : ℕ} (S : SmoothSimplex (n+1) E) (i : Fin (n+2)) : SmoothSimplex n E where
  toFun := S.toFun ∘ euclideanFace i
  neighborhood := euclideanFace i ⁻¹' S.neighborhood
  isOpen_neighborhood := S.isOpen_neighborhood.preimage (euclideanFace_contDiff i).continuous
  contains := fun _ hx => S.contains (euclideanFace_mapsTo i hx)
  smooth := S.smooth.comp (euclideanFace_contDiff i).contDiffOn (fun _ hx => hx)

theorem face_image_subset {n : ℕ} (S : SmoothSimplex (n+1) E) (i : Fin (n+2)) :
    (face S i).toFun '' standardSimplex n ⊆ S.toFun '' standardSimplex (n+1) := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨euclideanFace i x, euclideanFace_mapsTo i hx, rfl⟩

/-- Coordinate transport preserves the actual derivative and the ordered basis. -/
theorem simplexIntegral_coordinates {n : ℕ} (ω : Form n E) (S : SmoothSimplex n E) :
    simplexIntegral ω S = ∫ x in piSimplex n,
      pullback ω (S.toFun ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm) x
        (fun j => Pi.single j 1) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  have he := (coordinates_symm_volume n).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding (simplexCoefficient ω S) (standardSimplex n)
  rw [coordinates_symm_simplex] at he
  unfold simplexIntegral
  rw [← he]
  apply setIntegral_congr_fun (piSimplex_isCompact n).measurableSet
  intro x hx
  dsimp only
  rw [simplexCoefficient, pullback_apply, pullback_apply,
    fderiv_comp (f := (EuclideanSpace.equiv (Fin n) ℝ).symm) (g := S.toFun) x
      (S.differentiableAt hx) e.symm.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv,
    ContinuousLinearEquiv.coe_coe]
  congr 1

/-- Arbitrary-dimensional analytic simplex Stokes. Regularity is required only
on open neighborhoods of the compact source simplex and its image. The map can
be nonlinear, noninjective, and degenerate. Faces restrict the full map. -/
theorem stokes {n : ℕ} (ω : Form n E) (S : SmoothSimplex (n+1) E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex (n+1) ⊆ U) :
    simplexIntegral (extDeriv ω) S =
      ∑ i : Fin (n+2), (-1 : ℝ) ^ i.val * simplexIntegral ω (face S i) := by
  let e := EuclideanSpace.equiv (Fin (n+1)) ℝ
  have h := map_stokes ω (S.toFun ∘ e.symm)
    (S.isOpen_neighborhood.preimage e.symm.continuous)
    (fun x hx => S.contains hx)
    (S.smooth.comp e.symm.contDiff.contDiffOn (fun _ hx => hx)) hU hω
    (by rintro y ⟨x, hx, rfl⟩; exact himage ⟨e.symm x, hx, rfl⟩)
  rw [simplexIntegral_coordinates]
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [simplexIntegral_coordinates]
  congr 1

/-- Stokes with integrability and literal source witnesses for the exterior
integral and every actual face. All coordinate orders are included. -/
theorem stokes_source {n : ℕ} (ω : Form n E) (S : SmoothSimplex (n+1) E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex (n+1) ⊆ U) :
    IntegrableOn (simplexCoefficient (extDeriv ω) S) (standardSimplex (n+1)) ∧
    (∀ i : Fin (n+2), IntegrableOn (simplexCoefficient ω (face S i)) (standardSimplex n)) ∧
    (∀ σ : Equiv.Perm (Fin (n+1)), HasSourceIntegral (n+1) 0 1
      (simplexZeroExtension (simplexCoefficient (extDeriv ω) S ∘
        (EuclideanSpace.equiv (Fin (n+1)) ℝ).symm) ∘ coordinatePermutation σ)
      (∑ i : Fin (n+2), (-1 : ℝ) ^ i.val * simplexIntegral ω (face S i))) ∧
    (∀ (i : Fin (n+2)) (σ : Equiv.Perm (Fin n)), HasSourceIntegral n 0 1
      (simplexZeroExtension (simplexCoefficient ω (face S i) ∘
        (EuclideanSpace.equiv (Fin n) ℝ).symm) ∘ coordinatePermutation σ)
      (simplexIntegral ω (face S i))) := by
  have hc (i) := hω.continuousOn.mono ((face_image_subset S i).trans himage)
  refine ⟨(exterior_integral_source ω S hU hω himage (Equiv.refl _)).1,
    (fun i => simplexCoefficient_integrable ω (face S i) (hc i)), ?_,
    (fun i σ => simplexIntegral_source ω (face S i) (hc i) σ)⟩
  intro σ
  rw [← stokes ω S hU hω himage]
  exact (exterior_integral_source ω S hU hω himage σ).2

/-- The analytic faces are exactly the frozen chain API's affine relabels. -/
theorem euclideanFace_eq_relabel {n : ℕ} (i : Fin (n+2)) :
    euclideanFace i = SmoothChains.relabel i.succAbove := by
  refine Fin.cases ?_ (fun j => ?_) i
  · funext u
    ext k
    rw [SmoothChains.face_zero_coordinates]
    simp only [euclideanFace, Function.comp_apply, standardFace_zero, upperFace,
      Fin.insertNth_zero, SmoothChains.weights]
    rfl
  · funext u
    ext k
    have h := congrFun (SmoothChains.face_succ_coordinates j u) k
    simpa [euclideanFace] using! h.symm

theorem face_integral_eq {n : ℕ} (ω : Form n E) (S : SmoothChains.Simplex (n+1) E)
    (i : Fin (n+2)) : simplexIntegral ω (face S.toSmooth i) =
      simplexIntegral ω (S.face i).toSmooth := by
  simp only [simplexIntegral, simplexCoefficient, face, SmoothChains.Simplex.toSmooth,
    euclideanFace_eq_relabel, SmoothChains.Simplex.face, SmoothChains.Simplex.reparam]

/-- Generator Stokes uses the independently developed chain boundary literally. -/
theorem smoothChains_stokes {n : ℕ} (ω : Form n E) (S : SmoothChains.Simplex (n+1) E)
    {U : Set E} (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.val '' standardSimplex (n+1) ⊆ U) :
    SmoothChains.integral (extDeriv ω) (SmoothChains.simplex S) =
      SmoothChains.integral ω (SmoothChains.boundary n (SmoothChains.simplex S)) := by
  rw [SmoothChains.integral_simplex, stokes ω S.toSmooth hU hω himage]
  simp only [SmoothChains.boundary_simplex, map_sum, map_zsmul,
    SmoothChains.integral_simplex, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    face_integral_eq]

/-- Stokes extends to finite integer chains whose full images lie in the open
form domain. No global regularity or boundary identity is assumed. -/
theorem domainChain_stokes {n : ℕ} (ω : Form n E) {U : Set E} (hU : IsOpen U)
    (hω : ContDiffOn ℝ 1 ω U) (c : SmoothChains.DomainChain (n+1) U) :
    SmoothChains.integral (extDeriv ω) (SmoothChains.forgetDomain (n+1) U c) =
      SmoothChains.integral ω
        (SmoothChains.boundary n (SmoothChains.forgetDomain (n+1) U c)) := by
  have h : (SmoothChains.integral (extDeriv ω)).comp (SmoothChains.forgetDomain (n+1) U) =
      (SmoothChains.integral ω).comp
        ((SmoothChains.boundary n).comp (SmoothChains.forgetDomain (n+1) U)) := by
    apply FreeAbelianGroup.lift_ext
    intro S
    change SmoothChains.integral (extDeriv ω) (SmoothChains.simplex S.val) =
      SmoothChains.integral ω (SmoothChains.boundary n (SmoothChains.simplex S.val))
    exact smoothChains_stokes ω S.val hU hω (by rintro y ⟨x, hx, rfl⟩; exact S.property hx)
  exact DFunLike.congr_fun h c

/-- Exact-form integrals depend only on the ordinary boundary (Remark 10.35b). -/
theorem exact_integrals_eq {n : ℕ} (ω : Form n E) {U : Set E} (hU : IsOpen U)
    (hω : ContDiffOn ℝ 1 ω U) (c d : SmoothChains.DomainChain (n+1) U)
    (hboundary : SmoothChains.boundary n (SmoothChains.forgetDomain (n+1) U c) =
      SmoothChains.boundary n (SmoothChains.forgetDomain (n+1) U d)) :
    SmoothChains.integral (extDeriv ω) (SmoothChains.forgetDomain (n+1) U c) =
      SmoothChains.integral (extDeriv ω) (SmoothChains.forgetDomain (n+1) U d) := by
  rw [domainChain_stokes ω hU hω, domainChain_stokes ω hU hω, hboundary]

/-- Dimension zero is evaluation with mass one. -/
theorem simplexIntegral_zero (ω : Form 0 E) (S : SmoothSimplex 0 E) :
    simplexIntegral ω S = ω (S.toFun 0) (fun i => Fin.elim0 i) := by
  have h := SmoothChains.integral_zero ω (SmoothChains.Simplex.ofSmooth S)
  rw [SmoothChains.integral_simplex] at h
  exact h

/-- In dimension one the signs give terminal value minus initial value. -/
theorem stokes_one (ω : Form 0 E) (S : SmoothSimplex 1 E) {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex 1 ⊆ U) :
    simplexIntegral (extDeriv ω) S =
      ω (S.toFun (EuclideanSpace.single 0 1)) (fun i => Fin.elim0 i) -
        ω (S.toFun 0) (fun i => Fin.elim0 i) := by
  rw [stokes ω S hU hω himage, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_one_mul,
    simplexIntegral_zero]
  have h0 : euclideanFace (0 : Fin 2) (0 : EuclideanSpace ℝ (Fin 0)) =
      EuclideanSpace.single 0 1 := by
    ext j
    fin_cases j
    simp [euclideanFace, upperFace, EuclideanSpace.single]
  have h1 : euclideanFace (1 : Fin 2) (0 : EuclideanSpace ℝ (Fin 0)) = 0 := by
    change (EuclideanSpace.equiv (Fin 1) ℝ).symm (lowerLinear 0 0) = 0
    simp
  change ω (S.toFun (euclideanFace 0 0)) _ + -ω (S.toFun (euclideanFace 1 0)) _ = _
  rw [h0, h1, sub_eq_add_neg]

/-- The dimension-two boundary has the signs `+,-,+`. -/
theorem stokes_two (ω : Form 1 E) (S : SmoothSimplex 2 E) {U : Set E}
    (hU : IsOpen U) (hω : ContDiffOn ℝ 1 ω U)
    (himage : S.toFun '' standardSimplex 2 ⊆ U) :
    simplexIntegral (extDeriv ω) S =
      simplexIntegral ω (face S 0) - simplexIntegral ω (face S 1) +
        simplexIntegral ω (face S 2) := by
  rw [stokes ω S hU hω himage, Fin.sum_univ_three]
  norm_num
  ring

/-- A pair-coordinate C² map defines an actual Euclidean parameter triangle. -/
def pairSimplex (S : (ℝ × ℝ) → E) (hS : ContDiff ℝ 2 S) : SmoothSimplex 2 E where
  toFun := S ∘ pairCoordinates
  neighborhood := univ
  isOpen_neighborhood := isOpen_univ
  contains := subset_univ _
  smooth := (hS.comp pairCoordinates.contDiff).contDiffOn

theorem pairSimplex_integral (ω : Form 2 E) (S : (ℝ × ℝ) → E)
    (hS : ContDiff ℝ 2 S) (hω : Continuous ω) :
    simplexIntegral ω (pairSimplex S hS) = formIntegral ω S := by
  rw [simplexIntegral_eq_formIntegral ω _ hω.continuousOn]
  congr 1

/-- Both coordinate components survive the nonlinear pullback. -/
theorem nonlinear_both_pullback :
    pullback (TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1)) verticalSquare =
      TriangleStokes.coordinateForm (fun p => -(p.2 ^ 2)) (fun p => 2 * p.1 * p.2) := by
  funext p
  ext v
  simp [pullback_apply, TriangleStokes.coordinateForm_apply,
    (verticalSquare_hasFDerivAt p).fderiv, verticalSquare]
  ring

/-- The exterior coefficient is nonconstant and contains both form components. -/
theorem nonlinear_both_coefficient (p : ℝ × ℝ) :
    triangleCoefficient
      (extDeriv (TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1))) verticalSquare p =
        4 * p.2 := by
  let ω := TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1)
  have hω : Differentiable ℝ ω :=
    (differentiable_snd.neg.smul_const _).add (differentiable_fst.smul_const _)
  have h := exterior_pullback ω verticalSquare p (hω _) verticalSquare_smooth.contDiffAt
  change extDeriv (pullback (TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1))
    verticalSquare) p = _ at h
  rw [nonlinear_both_pullback] at h
  rw [triangleCoefficient, ← h, TriangleStokes.exterior_coordinateForm _ _ (by fun_prop) (by fun_prop)]
  have hP := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).fun_neg.fderiv
  have hQ := (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_mul 2).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))).fderiv
  change fderiv ℝ (fun p : ℝ × ℝ => 2 * p.1 * p.2) p = _ at hQ
  rw [hP, hQ]
  simp
  ring

/-- A nonlinear, nonhorizontal regression for the full theorem: the surface and
literal signed canonical face integrals both equal `2/3`. -/
theorem nonlinear_both_stokes :
    let ω := TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1)
    let S := pairSimplex verticalSquare verticalSquare_smooth
    simplexIntegral (extDeriv ω) S = 2 / 3 ∧
      (∑ i : Fin 3, (-1 : ℝ) ^ i.val * simplexIntegral ω (face S i)) = 2 / 3 := by
  dsimp only
  let ω := TriangleStokes.coordinateForm (fun p => -p.2) (fun p => p.1)
  have hω : ContDiff ℝ 1 ω :=
    (contDiff_snd.neg.smul_const _).add (contDiff_fst.smul_const _)
  have hc : Continuous (extDeriv ω) :=
    continuous_iff_continuousAt.mpr (fun _ => extDeriv_continuousAt hω.contDiffAt)
  have hv : simplexIntegral (extDeriv ω) (pairSimplex verticalSquare verticalSquare_smooth) = 2 / 3 := by
    rw [pairSimplex_integral _ _ _ hc]
    unfold formIntegral triangleIntegral
    simp only [ω, nonlinear_both_coefficient]
    have hs (x : ℝ) : (∫ y in 0..(1-x), 4 * y) = 2 * (1-x)^2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    simp_rw [hs]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^2)]
    norm_num [integral_pow]
  refine ⟨hv, ?_⟩
  rw [← stokes ω _ isOpen_univ hω.contDiffOn (subset_univ _)]
  exact hv

end Rudin.Support.SimplexStokes
