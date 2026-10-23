module

public import Math.Rudin.Chapter10.Exercise22
public import Math.Rudin.Chapter10.Exercise29

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Rudin.Chapter10.Exercise27
open Set MeasureTheory
open Rudin.Chapter10.Exercise22

/-- Literal base-coordinate formulas; the first base coordinate does not occur. -/
def g1 (f : Fin 3 → Space → ℝ) (b c : ℝ) (p : Space) : ℝ :=
  (∫ s in c..p 2, f 1 (WithLp.toLp 2 ![p 0, p 1, s])) -
  (∫ t in b..p 1, f 2 (WithLp.toLp 2 ![p 0, t, c]))
def g2 (f : Fin 3 → Space → ℝ) (c : ℝ) (p : Space) : ℝ :=
  -(∫ s in c..p 2, f 0 (WithLp.toLp 2 ![p 0, p 1, s]))

def radialCoefficients (i : Fin 3) (p : Space) : ℝ := p i / ‖p‖ ^ 3

/-- The zero branch is used only when the transverse numerator is zero. -/
def radialAntiderivative (A t : ℝ) : ℝ :=
  if A = 0 then 0 else t / (A * Real.sqrt (A + t ^ 2))

theorem radialAntiderivative_deriv {A : ℝ} (hA : 0 < A) (t : ℝ) :
    HasDerivAt (radialAntiderivative A) (1 / Real.sqrt (A + t ^ 2) ^ 3) t := by
  have hp : 0 < A + t ^ 2 := add_pos_of_pos_of_nonneg hA (sq_nonneg _)
  have hs : Real.sqrt (A + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hd := (((hasDerivAt_id t).pow 2).const_add A).sqrt (ne_of_gt hp)
  have hh := (hasDerivAt_id t).div (hd.const_mul A) (mul_ne_zero (ne_of_gt hA) hs)
  convert hh using 1
  · funext s
    simp [radialAntiderivative, ne_of_gt hA]
  · have he := Real.sq_sqrt (le_of_lt hp)
    norm_num only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul, mul_one]
    field_simp
    rw [he]
    ring

/-- The zero transverse-radius case is treated separately, not by FTC at a singularity. -/
theorem radial_integral {A k : ℝ} (hA : 0 ≤ A) (hk : k ^ 2 ≤ A) (a b : ℝ) :
    IntervalIntegrable (fun t => k / Real.sqrt (A + t ^ 2) ^ 3) volume a b ∧
    (∫ t in a..b, k / Real.sqrt (A + t ^ 2) ^ 3) =
      k * (radialAntiderivative A b - radialAntiderivative A a) := by
  by_cases hAz : A = 0
  · have hkz : k = 0 := by rw [hAz] at hk; nlinarith [sq_nonneg k]
    simp [hkz]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hc : Continuous (fun t : ℝ => k / Real.sqrt (A + t ^ 2) ^ 3) := by
      apply Continuous.div continuous_const
      · fun_prop
      · intro t
        exact pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr
          (add_pos_of_pos_of_nonneg hAp (sq_nonneg _))))
    refine ⟨hc.intervalIntegrable a b, ?_⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => (radialAntiderivative_deriv hAp t).const_mul k)
      (by simpa only [mul_one_div] using hc.intervalIntegrable a b)
    simpa only [mul_one_div, mul_sub] using h

/-- Closed expressions retain both base coordinates, including axis cases. -/
theorem radial_evaluation (b c : ℝ) (p : Space) :
    g1 radialCoefficients b c p =
      p 1 * (radialAntiderivative (p 0 ^ 2 + p 1 ^ 2) (p 2) -
        radialAntiderivative (p 0 ^ 2 + p 1 ^ 2) c) -
      c * (radialAntiderivative (p 0 ^ 2 + c ^ 2) (p 1) -
        radialAntiderivative (p 0 ^ 2 + c ^ 2) b) ∧
    g2 radialCoefficients c p =
      -(p 0 * (radialAntiderivative (p 0 ^ 2 + p 1 ^ 2) (p 2) -
        radialAntiderivative (p 0 ^ 2 + p 1 ^ 2) c)) := by
  have h1 := (radial_integral (k := p 1) (A := p 0 ^ 2 + p 1 ^ 2)
    (by positivity) (by nlinarith [sq_nonneg (p 0)]) c (p 2)).2
  have h2 := (radial_integral (k := c) (A := p 0 ^ 2 + c ^ 2)
    (by positivity) (by nlinarith [sq_nonneg (p 0)]) b (p 1)).2
  have h0 := (radial_integral (k := p 0) (A := p 0 ^ 2 + p 1 ^ 2)
    (by positivity) (by nlinarith [sq_nonneg (p 1)]) c (p 2)).2
  simp only [g1, g2, radialCoefficients, radius_formula]
  constructor
  · convert congrArg₂ (· - ·) h1 h2 using 1
    congr 2
    funext t
    dsimp
    congr 3
    ring
  · exact congrArg Neg.neg h0

def primitive (f : Fin 3 → Space → ℝ) (b c : ℝ) :
    Rudin.Support.SimplexIntegration.Form 1 Space := fun p =>
  g1 f b c p • coordinateOne 0 + g2 f c p • coordinateOne 1

/-- At base height zero the evaluated coefficients are those of the printed lambda. -/
theorem radial_primitive_zero_height (b : ℝ) (p : Space) :
    primitive radialCoefficients b 0 p = lambda p := by
  have he := radial_evaluation b 0 p
  ext v
  simp only [primitive, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, coordinateOne_apply, smul_eq_mul,
    he.1, he.2, zero_mul, sub_zero]
  rw [lambda_apply, radius_formula]
  by_cases ha : p 0 ^ 2 + p 1 ^ 2 = 0
  · simp [radialAntiderivative, axisRadiusSq, ha]
  · simp [radialAntiderivative, axisRadiusSq, ha, div_eq_mul_inv]
    ring

/-- Open coordinate cells use all three source coordinate intervals. -/
def openCell (lo hi : Fin 3 → ℝ) : Set Space :=
  {p | ∀ i, lo i < p i ∧ p i < hi i}

theorem openCell_isOpen (lo hi : Fin 3 → ℝ) : IsOpen (openCell lo hi) := by
  have : openCell lo hi = ⋂ i, (fun p : Space => p i) ⁻¹' Ioo (lo i) (hi i) := by
    ext p; simp [openCell]
  rw [this]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (EuclideanSpace.proj i).continuous)

/-- Each off-axis point admits a genuine local cell containing base height zero.
This does not assert that a fixed arbitrary cell contains that height. -/
theorem compatible_local_cell {p : Space} (hp : p ∈ offAxis) :
    ∃ lo hi : Fin 3 → ℝ, p ∈ openCell lo hi ∧
      (WithLp.toLp 2 ![p 0,p 1,0] : Space) ∈ openCell lo hi ∧
      openCell lo hi ⊆ offAxis := by
  have hzlo : min (p 2) 0 - 1 < p 2 := by linarith [min_le_left (p 2) 0]
  have hzhi : p 2 < max (p 2) 0 + 1 := by linarith [le_max_left (p 2) 0]
  have hzlo0 : min (p 2) 0 - 1 < 0 := by linarith [min_le_right (p 2) 0]
  have hzhi0 : 0 < max (p 2) 0 + 1 := by linarith [le_max_right (p 2) 0]
  by_cases hx : p 0 = 0
  · have hy : p 1 ≠ 0 := by intro hy; simpa [offAxis, hx, hy] using hp
    have hyabs : 0 < |p 1| := abs_pos.mpr hy
    refine ⟨![p 0 - 1, p 1 - |p 1| / 2, min (p 2) 0 - 1],
      ![p 0 + 1, p 1 + |p 1| / 2, max (p 2) 0 + 1], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> dsimp <;> constructor <;> linarith
    · intro i; fin_cases i <;> dsimp <;> constructor <;> linarith
    · intro q hq
      have hyq := hq 1
      have hne : q 1 ≠ 0 := by
        intro he
        rcases lt_or_gt_of_ne hy with h | h
        · rw [abs_of_neg h] at hyq
          dsimp at hyq
          linarith
        · rw [abs_of_pos h] at hyq
          dsimp at hyq
          linarith
      change 0 < q 0 ^ 2 + q 1 ^ 2
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hne)
  · have hxabs : 0 < |p 0| := abs_pos.mpr hx
    refine ⟨![p 0 - |p 0| / 2, p 1 - 1, min (p 2) 0 - 1],
      ![p 0 + |p 0| / 2, p 1 + 1, max (p 2) 0 + 1], ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> dsimp <;> constructor <;> linarith
    · intro i; fin_cases i <;> dsimp <;> constructor <;> linarith
    · intro q hq
      have hxq := hq 0
      have hne : q 0 ≠ 0 := by
        intro he
        rcases lt_or_gt_of_ne hx with h | h
        · rw [abs_of_neg h] at hxq
          dsimp at hxq
          linarith
        · rw [abs_of_pos h] at hxq
          dsimp at hxq
          linarith
      change 0 < q 0 ^ 2 + q 1 ^ 2
      exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hne) (sq_nonneg _)

open Rudin.Support

/-- Source integration with the usual sign convention for reversed endpoints. -/
def HasSourceInterval (F : ℝ → ℝ) (a b I : ℝ) : Prop :=
  if a ≤ b then StieltjesPrototype.HasDarbouxRSIntegral F id a b I
  else StieltjesPrototype.HasDarbouxRSIntegral F id b a (-I)

theorem sourceInterval_of_continuous {F : ℝ → ℝ} {a b : ℝ}
    (hF : ContinuousOn F (uIcc a b)) :
    IntervalIntegrable F volume a b ∧ HasSourceInterval F a b (∫ t in a..b, F t) := by
  refine ⟨hF.intervalIntegrable, ?_⟩
  unfold HasSourceInterval
  split_ifs with hab
  · have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hab
      (by simpa only [uIcc_of_le hab] using hF)
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id] using h
  · have hba := le_of_not_ge hab
    have h := StieltjesMeasureBridge.continuous_bridge StieltjesFunction.id hba
      (by simpa only [uIcc_of_ge hba] using hF)
    simpa only [show (↑StieltjesFunction.id : ℝ → ℝ) = id from rfl,
      ← Real.volume_eq_stieltjes_id, intervalIntegral.integral_symm a b] using h

def replaceCoordinate (p : Space) (i : Fin 3) (t : ℝ) : Space :=
  WithLp.toLp 2 (Function.update (fun j => p j) i t)

theorem replaceCoordinate_continuous (p : Space) (i : Fin 3) :
    Continuous (replaceCoordinate p i) := by
  unfold replaceCoordinate
  fun_prop

theorem coordinate_segment_in_cell {lo hi : Fin 3 → ℝ} {p : Space}
    (hp : p ∈ openCell lo hi) (i : Fin 3) {a : ℝ} (ha : a ∈ Ioo (lo i) (hi i)) :
    MapsTo (replaceCoordinate p i) (uIcc a (p i)) (openCell lo hi) := by
  intro t ht j
  by_cases hji : j = i
  · subst j
    have hc : lo i < t ∧ t < hi i := by
      rcases le_total a (p i) with h | h
      · rw [uIcc_of_le h] at ht
        exact ⟨ha.1.trans_le ht.1, ht.2.trans_lt (hp i).2⟩
      · rw [uIcc_of_ge h] at ht
        exact ⟨(hp i).1.trans_le ht.1, ht.2.trans_lt ha.2⟩
    simpa [replaceCoordinate] using hc
  · simpa [replaceCoordinate, Function.update_of_ne hji] using hp j

theorem coordinate_integral_source {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContinuousOn F (openCell lo hi)) {p : Space} (hp : p ∈ openCell lo hi)
    (i : Fin 3) {a : ℝ} (ha : a ∈ Ioo (lo i) (hi i)) :
    IntervalIntegrable (fun t => F (replaceCoordinate p i t)) volume a (p i) ∧
    HasSourceInterval (fun t => F (replaceCoordinate p i t)) a (p i)
      (∫ t in a..p i, F (replaceCoordinate p i t)) := by
  apply sourceInterval_of_continuous
  exact hF.comp (replaceCoordinate_continuous p i).continuousOn
    (coordinate_segment_in_cell hp i ha)

theorem radial_continuousOn_punctured (i : Fin 3) :
    ContinuousOn (radialCoefficients i) punctured := by
  intro p hp
  exact ((radial_coefficient_hasFDerivAt hp i).continuousAt).continuousWithinAt

/-- Source validity of every literal integral, without assuming the transverse radius is nonzero. -/
theorem radial_source_integrals {lo hi : Fin 3 → ℝ} {base p : Space}
    (hbase : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi)
    (hpunct : openCell lo hi ⊆ punctured) :
    (∀ i : Fin 3, IntervalIntegrable
      (fun s => radialCoefficients i (WithLp.toLp 2 ![p 0,p 1,s])) volume (base 2) (p 2) ∧
      HasSourceInterval (fun s => radialCoefficients i (WithLp.toLp 2 ![p 0,p 1,s]))
        (base 2) (p 2) (∫ s in base 2..p 2,
          radialCoefficients i (WithLp.toLp 2 ![p 0,p 1,s]))) ∧
    (IntervalIntegrable
      (fun t => radialCoefficients 2 (WithLp.toLp 2 ![p 0,t,base 2])) volume (base 1) (p 1) ∧
      HasSourceInterval (fun t => radialCoefficients 2 (WithLp.toLp 2 ![p 0,t,base 2]))
        (base 1) (p 1) (∫ t in base 1..p 1,
          radialCoefficients 2 (WithLp.toLp 2 ![p 0,t,base 2]))) := by
  have hc (i : Fin 3) := (radial_continuousOn_punctured i).mono hpunct
  have hz (s : ℝ) : replaceCoordinate p 2 s = WithLp.toLp 2 ![p 0,p 1,s] := by
    ext j; fin_cases j <;> simp [replaceCoordinate]
  constructor
  · intro i
    simpa only [hz] using coordinate_integral_source (hc i) hp 2 (hbase 2)
  · let q : Space := replaceCoordinate p 2 (base 2)
    have hq : q ∈ openCell lo hi :=
      coordinate_segment_in_cell hp 2 (hbase 2) (left_mem_uIcc)
    have hq1 : q 1 = p 1 := by simp [q, replaceCoordinate]
    have hy (t : ℝ) : replaceCoordinate q 1 t = WithLp.toLp 2 ![p 0,t,base 2] := by
      ext j; fin_cases j <;> simp [q, replaceCoordinate]
    simpa only [hy, hq1] using coordinate_integral_source (hc 2) hq 1 (hbase 1)

/-- Compatible local cells give genuine C1 primitives, not only coefficient identities. -/
theorem radial_local_primitive {p : Space} (hp : p ∈ offAxis) :
    ∃ lo hi : Fin 3 → ℝ, p ∈ openCell lo hi ∧
      (WithLp.toLp 2 ![p 0,p 1,0] : Space) ∈ openCell lo hi ∧
      openCell lo hi ⊆ offAxis ∧
      ContDiffOn ℝ 1 (primitive radialCoefficients (p 1) 0) (openCell lo hi) ∧
      ∀ q ∈ openCell lo hi,
        extDeriv (primitive radialCoefficients (p 1) 0) q = zeta q := by
  obtain ⟨lo, hi, hpc, hbase, hsub⟩ := compatible_local_cell hp
  have he : primitive radialCoefficients (p 1) 0 = lambda := by
    funext q
    exact radial_primitive_zero_height _ _
  refine ⟨lo, hi, hpc, hbase, hsub, ?_, ?_⟩
  · rw [he]
    exact lambda_smooth.mono hsub
  · intro q hq
    rw [he]
    exact lambda_exterior (hsub hq)

/-- A cell around a nonzero axis point cannot be assigned base height zero. -/
theorem incompatible_zero_height_cell :
    (WithLp.toLp 2 ![0,0,2] : Space) ∈ openCell ![-1,-1,1] ![1,1,3] ∧
    openCell ![-1,-1,1] ![1,1,3] ⊆ punctured ∧
    ∀ a b : ℝ, (WithLp.toLp 2 ![a,b,0] : Space) ∉ openCell ![-1,-1,1] ![1,1,3] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro q hq hzero
    have h2 := hq 2
    norm_num [hzero] at h2
  · intro a b h
    have h2 := h 2
    norm_num at h2

/-- Repeated endpoints have their source integral, even at admissible axis points. -/
theorem axis_zero_length_model :
    g1 radialCoefficients 0 2 (WithLp.toLp 2 ![0,0,2]) = 0 ∧
    g2 radialCoefficients 2 (WithLp.toLp 2 ![0,0,2]) = 0 := by
  simp [g1, g2]

open scoped Topology
open Filter
open Rudin.Support.SimplexIntegration

/-- Coordinate tangent vectors and the projection that removes one coordinate. -/
def basis (i : Fin 3) : Space := EuclideanSpace.single i 1

def cut (i : Fin 3) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space - (EuclideanSpace.proj i).smulRight (basis i)

theorem replace_eq (p : Space) (i : Fin 3) (t : ℝ) :
    replaceCoordinate p i t = cut i p + t • basis i := by
  ext j
  by_cases h : j = i <;> simp [replaceCoordinate, cut, basis, h,
    Function.update_of_ne, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]

theorem cut_basis {i j : Fin 3} (h : j ≠ i) : cut i (basis j) = basis j := by
  simp [cut, basis, h]

def coordinateIntegral (F : Space → ℝ) (i : Fin 3) (a : ℝ) (p : Space) : ℝ :=
  ∫ t in a..p i, F (replaceCoordinate p i t)

def coordPartial (F : Space → ℝ) (i : Fin 3) (p : Space) : ℝ :=
  fderiv ℝ F p (basis i)

theorem affine_mem_uIcc (a b : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    a + (b-a)*t ∈ uIcc a b := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h) ht.1,
      mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht.2)]
  · rw [uIcc_of_ge h]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h) ht.1,
      mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht.2)]

/-- Rescaling gives C¹ on the actual open cell, including reversed and equal bounds. -/
theorem coordinateIntegral_c1 {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3) {a : ℝ}
    (ha : a ∈ Ioo (lo i) (hi i)) :
    ContDiffOn ℝ 1 (coordinateIntegral F i a) (openCell lo hi) := by
  let H (q : Space × ℝ) : ℝ :=
    (q.1 i-a) * F (replaceCoordinate q.1 i (a+(q.1 i-a)*q.2))
  have hH (p : Space) (hp : p ∈ openCell lo hi) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 H (p,t) := by
    have hm := coordinate_segment_in_cell hp i ha (affine_mem_uIcc a (p i) ht)
    have hc := (hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)
    have hmap : ContDiff ℝ 1
        (fun q : Space × ℝ => replaceCoordinate q.1 i (a+(q.1 i-a)*q.2)) := by
      simp only [replace_eq]
      fun_prop
    exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp (p,t) contDiffAt_fst
      |>.sub contDiffAt_const).mul (hc.comp (p,t) hmap.contDiffAt)
  have h := Exercise29.integral_c1 (openCell_isOpen lo hi) hH
  convert h using 1
  funext p
  exact Exercise29.integral_affine (fun q : Space × ℝ => F (replaceCoordinate q.1 i q.2)) p a (p i)

/-- Differentiate a transverse coordinate under the integral sign. -/
theorem coordinateIntegral_partial_ne {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) {i j : Fin 3} (hji : j ≠ i)
    {a : ℝ} (ha : a ∈ Ioo (lo i) (hi i)) {p : Space} (hp : p ∈ openCell lo hi) :
    coordPartial (coordinateIntegral F i a) j p =
      ∫ t in a..p i, coordPartial F j (replaceCoordinate p i t) := by
  let H (q : Space × ℝ) : ℝ :=
    (q.1 i-a) * F (replaceCoordinate q.1 i (a+(q.1 i-a)*q.2))
  let z (t : ℝ) := replaceCoordinate p i (a+(p i-a)*t)
  have hH (q : Space) (hq : q ∈ openCell lo hi) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 H (q,t) := by
    have hm := coordinate_segment_in_cell hq i ha (affine_mem_uIcc a (q i) ht)
    have hc := (hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)
    have hmap : ContDiff ℝ 1
        (fun q : Space × ℝ => replaceCoordinate q.1 i (a+(q.1 i-a)*q.2)) := by
      simp only [replace_eq]
      fun_prop
    exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp (q,t) contDiffAt_fst
      |>.sub contDiffAt_const).mul (hc.comp (q,t) hmap.contDiffAt)
  let D (t : ℝ) := (fderiv ℝ H (p,t)).comp (ContinuousLinearMap.inl ℝ Space ℝ)
  have hD : IntervalIntegrable D volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc := (hH p hp t (by simpa using ht)).continuousAt_fderiv (by norm_num)
    exact ((hc.comp (by fun_prop : ContinuousAt (fun t : ℝ => (p,t)) t)).clm_comp
      continuousAt_const).continuousWithinAt
  have hd := Exercise29.integral_hasFDerivAt (openCell_isOpen lo hi) hH hp
  have he : coordinateIntegral F i a = fun q => ∫ t in (0 : ℝ)..1, H (q,t) := by
    funext q
    exact Exercise29.integral_affine (fun q : Space × ℝ => F (replaceCoordinate q.1 i q.2)) q a (q i)
  change fderiv ℝ (coordinateIntegral F i a) p (basis j) = _
  rw [he, hd.fderiv, ContinuousLinearMap.intervalIntegral_apply hD]
  rw [Exercise29.integral_affine (fun q : Space × ℝ =>
    coordPartial F j (replaceCoordinate q.1 i q.2)) p a (p i)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  have hm := coordinate_segment_in_cell hp i ha (affine_mem_uIcc a (p i) ht')
  have hf := ((hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)).differentiableAt one_ne_zero
  have hmap : HasFDerivAt (fun q : Space => replaceCoordinate q i (a+(q i-a)*t))
      (cut i + t • (EuclideanSpace.proj i).smulRight (basis i)) p := by
    simp only [replace_eq]
    convert (cut i).hasFDerivAt.add
      (((((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := p)).sub_const a).mul_const t |>.const_add a).smul_const (basis i)) using 1
    all_goals ext w k; simp [PiLp.smul_apply, mul_comm, mul_assoc]
  have hh := (((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt (x := p)).sub_const a).mul
    (hf.hasFDerivAt.comp p hmap)
  have hprod : HasFDerivAt (fun q : Space => (q,t)) (ContinuousLinearMap.inl ℝ Space ℝ) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  have hfull : HasFDerivAt H (fderiv ℝ H (p,t)) (p,t) :=
    ((hH p hp t ht').differentiableAt one_ne_zero).hasFDerivAt
  have hh' : HasFDerivAt (fun q => H (q,t)) (D t) p := by
    convert hfull.comp p hprod using 1
    rfl
  have heD := hh'.unique hh
  change D t (basis j) = (p i-a) * coordPartial F j (z t)
  change ((fderiv ℝ H (p,t)).comp (ContinuousLinearMap.inl ℝ Space ℝ)) (basis j) = _
  have hhD : (fderiv ℝ H (p,t)).comp (ContinuousLinearMap.inl ℝ Space ℝ) = _ := heD
  rw [hhD]
  simp [coordPartial, cut, basis, Ne.symm hji, z, smul_eq_mul]

@[simp] theorem replace_self (p : Space) (i : Fin 3) :
    replaceCoordinate p i (p i) = p := by
  ext j
  simp [replaceCoordinate]

@[simp] theorem replace_replace (p : Space) (i : Fin 3) (a b : ℝ) :
    replaceCoordinate (replaceCoordinate p i a) i b = replaceCoordinate p i b := by
  ext j
  simp [replaceCoordinate]

theorem replace_mem {lo hi : Fin 3 → ℝ} {p : Space}
    (hp : p ∈ openCell lo hi) (i : Fin 3) {t : ℝ}
    (ht : t ∈ Ioo (lo i) (hi i)) : replaceCoordinate p i t ∈ openCell lo hi := by
  intro j
  by_cases h : j = i
  · subst j; simpa [replaceCoordinate] using ht
  · simpa [replaceCoordinate, h] using hp j

theorem replace_hasDerivAt (p : Space) (i : Fin 3) (t : ℝ) :
    HasDerivAt (replaceCoordinate p i) (basis i) t := by
  simp only [funext (replace_eq p i)]
  simpa using ((hasDerivAt_id t).smul_const (basis i)).const_add (cut i p)

theorem coordinateIntegral_partial_self {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3)
    {a : ℝ} (ha : a ∈ Ioo (lo i) (hi i)) {p : Space} (hp : p ∈ openCell lo hi) :
    coordPartial (coordinateIntegral F i a) i p = F p := by
  have hI := ((coordinateIntegral_c1 hF i ha p hp).contDiffAt
    ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have hc : ContinuousOn (fun t => F (replaceCoordinate p i t)) (Ioo (lo i) (hi i)) :=
    hF.continuousOn.comp (replaceCoordinate_continuous p i).continuousOn (fun t ht => replace_mem hp i ht)
  have hI' : HasFDerivAt (coordinateIntegral F i a) (fderiv ℝ (coordinateIntegral F i a) p)
      (replaceCoordinate p i (p i)) := by simpa using hI.hasFDerivAt
  have hslice := hI'.comp_hasDerivAt (p i) (replace_hasDerivAt p i (p i))
  have he : (fun t => coordinateIntegral F i a (replaceCoordinate p i t)) =
      (fun t => ∫ s in a..t, F (replaceCoordinate p i s)) := by
    funext t
    simp [coordinateIntegral, replaceCoordinate, Function.update_idem]
  have hf := intervalIntegral.integral_hasDerivAt_right
    (coordinate_integral_source hF.continuousOn hp i ha).1
    (hc.stronglyMeasurableAtFilter isOpen_Ioo (p i) (hp i))
    ((hc _ (hp i)).continuousAt (isOpen_Ioo.mem_nhds (hp i)))
  rw [show (coordinateIntegral F i a ∘ replaceCoordinate p i) =
    (fun t => ∫ s in a..t, F (replaceCoordinate p i s)) from he] at hslice
  simpa [coordPartial] using hslice.unique hf

theorem coordPartial_continuousOn {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3) :
    ContinuousOn (coordPartial F i) (openCell lo hi) := by
  intro p hp
  exact ((((hF p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).continuousAt_fderiv
    (by norm_num)).clm_apply continuousAt_const).continuousWithinAt

/-- FTC on the source segment, with no order condition on its endpoints. -/
theorem coordinateIntegral_derivative {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3)
    {a : ℝ} (ha : a ∈ Ioo (lo i) (hi i)) {p : Space} (hp : p ∈ openCell lo hi) :
    (∫ t in a..p i, coordPartial F i (replaceCoordinate p i t)) =
      F p - F (replaceCoordinate p i a) := by
  have hd (t : ℝ) (ht : t ∈ uIcc a (p i)) :
      HasDerivAt (fun t => F (replaceCoordinate p i t))
        (coordPartial F i (replaceCoordinate p i t)) t := by
    have hm := coordinate_segment_in_cell hp i ha ht
    exact (((hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)).differentiableAt
      one_ne_zero).hasFDerivAt.comp_hasDerivAt t (replace_hasDerivAt p i t)
  simpa only [replace_self] using intervalIntegral.integral_eq_sub_of_hasDerivAt
    hd (coordinate_integral_source (coordPartial_continuousOn hF i) hp i ha).1

theorem coordinateSlice_c1 {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3) {a : ℝ}
    (ha : a ∈ Ioo (lo i) (hi i)) :
    ContDiffOn ℝ 1 (fun p => F (replaceCoordinate p i a)) (openCell lo hi) := by
  apply hF.comp
  · simp only [replace_eq]
    fun_prop
  · intro p hp; exact replace_mem hp i ha

theorem coordinateSlice_partial_self {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) (i : Fin 3) {a : ℝ}
    (ha : a ∈ Ioo (lo i) (hi i)) {p : Space} (hp : p ∈ openCell lo hi) :
    coordPartial (fun q => F (replaceCoordinate q i a)) i p = 0 := by
  have hm := replace_mem hp i ha
  have hf := ((hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)).differentiableAt one_ne_zero
  have hd : HasFDerivAt (fun q => replaceCoordinate q i a) (cut i) p := by
    simp only [replace_eq]
    exact (cut i).hasFDerivAt.add_const _
  have hh := hf.hasFDerivAt.comp p hd
  change fderiv ℝ (F ∘ fun q => replaceCoordinate q i a) p (basis i) = 0
  rw [hh.fderiv]
  simp [cut, basis]

theorem g1_as_integrals (f : Fin 3 → Space → ℝ) (b c : ℝ) :
    g1 f b c = fun p => coordinateIntegral (f 1) 2 c p -
      coordinateIntegral (fun q => f 2 (replaceCoordinate q 2 c)) 1 b p := by
  funext p
  unfold g1 coordinateIntegral
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro t ht
  · apply congrArg (f 1)
    ext j; fin_cases j <;> simp [replaceCoordinate]
  · apply congrArg (f 2)
    ext j; fin_cases j <;> simp [replaceCoordinate]

theorem g2_as_integral (f : Fin 3 → Space → ℝ) (c : ℝ) :
    g2 f c = fun p => -coordinateIntegral (f 0) 2 c p := by
  funext p
  unfold g2 coordinateIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  apply congrArg (f 0)
  ext j; fin_cases j <;> simp [replaceCoordinate]

/-- Both literal coefficients are C¹; only the supplied cell is used. -/
theorem coefficients_c1 {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) {base : Space}
    (hb : base ∈ openCell lo hi) :
    ContDiffOn ℝ 1 (g1 f (base 1) (base 2)) (openCell lo hi) ∧
    ContDiffOn ℝ 1 (g2 f (base 2)) (openCell lo hi) := by
  rw [g1_as_integrals, g2_as_integral]
  exact ⟨(coordinateIntegral_c1 (hf 1) 2 (hb 2)).sub
    (coordinateIntegral_c1 (coordinateSlice_c1 (hf 2) 2 (hb 2)) 1 (hb 1)),
    (coordinateIntegral_c1 (hf 0) 2 (hb 2)).neg⟩

/-- The actual transverse and vertical partial derivatives of the literal formulas. -/
theorem coefficients_partials {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) {base p : Space}
    (hb : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi) :
    coordPartial (g1 f (base 1) (base 2)) 2 p = f 1 p ∧
    coordPartial (g2 f (base 2)) 2 p = -f 0 p ∧
    coordPartial (g1 f (base 1) (base 2)) 1 p =
      (∫ t in base 2..p 2, coordPartial (f 1) 1 (replaceCoordinate p 2 t)) -
        f 2 (replaceCoordinate p 2 (base 2)) ∧
    coordPartial (g2 f (base 2)) 0 p =
      -(∫ t in base 2..p 2, coordPartial (f 0) 0 (replaceCoordinate p 2 t)) := by
  have hA := coordinateIntegral_c1 (hf 1) 2 (hb 2)
  have hB := coordinateIntegral_c1 (coordinateSlice_c1 (hf 2) 2 (hb 2)) 1 (hb 1)
  have hC := coordinateIntegral_c1 (hf 0) 2 (hb 2)
  have dA := ((hA p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have dB := ((hB p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have dC := ((hC p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have hsub (j) : coordPartial (g1 f (base 1) (base 2)) j p =
      coordPartial (coordinateIntegral (f 1) 2 (base 2)) j p -
      coordPartial (coordinateIntegral (fun q => f 2 (replaceCoordinate q 2 (base 2))) 1 (base 1)) j p := by
    rw [g1_as_integrals]
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) (dA.hasFDerivAt.sub dB.hasFDerivAt).fderiv
  have hneg (j) : coordPartial (g2 f (base 2)) j p =
      -coordPartial (coordinateIntegral (f 0) 2 (base 2)) j p := by
    rw [g2_as_integral]
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) dC.hasFDerivAt.neg.fderiv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsub, coordinateIntegral_partial_self (hf 1) 2 (hb 2) hp,
      coordinateIntegral_partial_ne (coordinateSlice_c1 (hf 2) 2 (hb 2)) (by decide) (hb 1) hp]
    have hz : (∫ t in base 1..p 1,
        coordPartial (fun q => f 2 (replaceCoordinate q 2 (base 2))) 2
          (replaceCoordinate p 1 t)) = 0 := by
      rw [← intervalIntegral.integral_zero (a := base 1) (b := p 1)]
      apply intervalIntegral.integral_congr
      intro t ht
      exact coordinateSlice_partial_self (hf 2) 2 (hb 2)
        (coordinate_segment_in_cell hp 1 (hb 1) ht)
    rw [hz, sub_zero]
  · rw [hneg, coordinateIntegral_partial_self (hf 0) 2 (hb 2) hp]
  · rw [hsub, coordinateIntegral_partial_ne (hf 1) (by decide) (hb 2) hp,
      coordinateIntegral_partial_self (coordinateSlice_c1 (hf 2) 2 (hb 2)) 1 (hb 1) hp]
  · rw [hneg, coordinateIntegral_partial_ne (hf 0) (by decide) (hb 2) hp]

/-- The source 2-form, in its printed cyclic coordinate order. -/
def omega (f : Fin 3 → Space → ℝ) : Form 2 Space := fun p =>
  f 0 p • coordinateTwo 1 2 + f 1 p • coordinateTwo 2 0 + f 2 p • coordinateTwo 0 1

theorem omega_c1 {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) :
    ContDiffOn ℝ 1 (omega f) (openCell lo hi) :=
  ((hf 0).smul contDiffOn_const |>.add ((hf 1).smul contDiffOn_const)).add
    ((hf 2).smul contDiffOn_const)

/-- Closedness supplies the sum of genuine coordinate derivatives. -/
theorem closed_sum {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) {p : Space}
    (hp : p ∈ openCell lo hi) (hc : extDeriv (omega f) p = 0) :
    coordPartial (f 0) 0 p + coordPartial (f 1) 1 p + coordPartial (f 2) 2 p = 0 := by
  have hd (i) := ((hf i p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have hw := ((omega_c1 hf p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have he := congrArg (fun w : Space [⋀^Fin 3]→L[ℝ] ℝ => w basis) hc
  rw [extDeriv_apply hw, Fin.sum_univ_three] at he
  have h0 : (fun q => omega f q ((0 : Fin 3).removeNth basis)) = f 0 := by
    funext q
    norm_num [omega, basis, coordinateTwo_apply, Fin.removeNth, Fin.tail, Fin.succAbove]
  have h1 : (fun q => omega f q ((1 : Fin 3).removeNth basis)) = fun q => -f 1 q := by
    funext q
    norm_num [omega, basis, coordinateTwo_apply, Fin.removeNth, Fin.tail, Fin.succAbove]
  have h2 : (fun q => omega f q ((2 : Fin 3).removeNth basis)) = f 2 := by
    funext q
    norm_num [omega, basis, coordinateTwo_apply, Fin.removeNth, Fin.tail, Fin.succAbove]
  rw [h0, h1, h2, fderiv_fun_neg] at he
  simpa [coordPartial] using he

theorem primitive_c1 {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) {base : Space}
    (hb : base ∈ openCell lo hi) :
    ContDiffOn ℝ 1 (primitive f (base 1) (base 2)) (openCell lo hi) :=
  ((coefficients_c1 hf hb).1.smul contDiffOn_const).add
    ((coefficients_c1 hf hb).2.smul contDiffOn_const)

/-- The remaining coefficient follows by closedness under the vertical integral and FTC. -/
theorem primitive_curl {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi))
    (hc : ∀ p ∈ openCell lo hi, extDeriv (omega f) p = 0) {base p : Space}
    (hb : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi) :
    coordPartial (g2 f (base 2)) 0 p - coordPartial (g1 f (base 1) (base 2)) 1 p = f 2 p := by
  obtain ⟨h12,h22,h11,h20⟩ := coefficients_partials hf hb hp
  rw [h11, h20]
  have hi (i : Fin 3) := (coordinate_integral_source
    (coordPartial_continuousOn (hf i) i) hp 2 (hb 2)).1
  have he : (∫ t in base 2..p 2,
      coordPartial (f 0) 0 (replaceCoordinate p 2 t)) +
      (∫ t in base 2..p 2, coordPartial (f 1) 1 (replaceCoordinate p 2 t)) =
      -(∫ t in base 2..p 2, coordPartial (f 2) 2 (replaceCoordinate p 2 t)) := by
    rw [← intervalIntegral.integral_add (hi 0) (hi 1), ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have hm := coordinate_segment_in_cell hp 2 (hb 2) ht
    have hs := closed_sum hf hm (hc _ hm)
    linarith
  rw [coordinateIntegral_derivative (hf 2) 2 (hb 2) hp] at he
  linarith

/-- The prescribed integral primitive has the actual exterior derivative omega. -/
theorem primitive_identity {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi))
    (hc : ∀ p ∈ openCell lo hi, extDeriv (omega f) p = 0) {base : Space}
    (hb : base ∈ openCell lo hi) :
    ContDiffOn ℝ 1 (primitive f (base 1) (base 2)) (openCell lo hi) ∧
    ∀ p ∈ openCell lo hi, extDeriv (primitive f (base 1) (base 2)) p = omega f p := by
  refine ⟨primitive_c1 hf hb, ?_⟩
  intro p hp
  have hd := ((primitive_c1 hf hb p hp).contDiffAt
    ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have h1 := (((coefficients_c1 hf hb).1 p hp).contDiffAt
    ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have h2 := (((coefficients_c1 hf hb).2 p hp).contDiffAt
    ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have heval (v : Fin 1 → Space) :
      HasFDerivAt (fun q => primitive f (base 1) (base 2) q v)
        ((v 0 0) • fderiv ℝ (g1 f (base 1) (base 2)) p +
          (v 0 1) • fderiv ℝ (g2 f (base 2)) p) p := by
    convert (h1.hasFDerivAt.mul_const (v 0 0)).add
      (h2.hasFDerivAt.mul_const (v 0 1)) using 1
    funext q
    simp [primitive, coordinateOne_apply, smul_eq_mul]
  obtain ⟨h12,h22,h11,h20⟩ := coefficients_partials hf hb hp
  have hcurl := primitive_curl hf hc hb hp
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  intro v hv
  change extDeriv (primitive f (base 1) (base 2)) p _ = omega f p _
  rw [extDeriv_apply hd, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  rw [(heval _).fderiv, (heval _).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  generalize h0 : v 0 = i
  generalize h1v : v 1 = j
  fin_cases i <;> fin_cases j <;>
    norm_num [omega, coordinateTwo_apply, Fin.removeNth, Fin.tail,
      EuclideanSpace.basisFun_apply, h0, h1v] <;>
    simp_all [coordPartial, basis] <;> linarith

theorem source_integrals {lo hi : Fin 3 → ℝ} {base p : Space}
    {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) (openCell lo hi))
    (hbase : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi)
    :
    (∀ i : Fin 3, IntervalIntegrable
      (fun s => f i (WithLp.toLp 2 ![p 0,p 1,s])) volume (base 2) (p 2) ∧
      HasSourceInterval (fun s => f i (WithLp.toLp 2 ![p 0,p 1,s]))
        (base 2) (p 2) (∫ s in base 2..p 2,
          f i (WithLp.toLp 2 ![p 0,p 1,s]))) ∧
    (IntervalIntegrable
      (fun t => f 2 (WithLp.toLp 2 ![p 0,t,base 2])) volume (base 1) (p 1) ∧
      HasSourceInterval (fun t => f 2 (WithLp.toLp 2 ![p 0,t,base 2]))
        (base 1) (p 1) (∫ t in base 1..p 1,
          f 2 (WithLp.toLp 2 ![p 0,t,base 2]))) := by
  have hc := hf
  have hz (s : ℝ) : replaceCoordinate p 2 s = WithLp.toLp 2 ![p 0,p 1,s] := by
    ext j; fin_cases j <;> simp [replaceCoordinate]
  constructor
  · intro i
    simpa only [hz] using coordinate_integral_source (hc i) hp 2 (hbase 2)
  · let q : Space := replaceCoordinate p 2 (base 2)
    have hq : q ∈ openCell lo hi :=
      coordinate_segment_in_cell hp 2 (hbase 2) (left_mem_uIcc)
    have hq1 : q 1 = p 1 := by simp [q, replaceCoordinate]
    have hy (t : ℝ) : replaceCoordinate q 1 t = WithLp.toLp 2 ![p 0,t,base 2] := by
      ext j; fin_cases j <;> simp [q, replaceCoordinate]
    simpa only [hy, hq1] using coordinate_integral_source (hc 2) hq 1 (hbase 1)


/-- The generic identity also applies to punctured cells meeting the z-axis. -/
theorem radial_cell_primitive {lo hi : Fin 3 → ℝ} {base : Space}
    (hb : base ∈ openCell lo hi) (hpunct : openCell lo hi ⊆ punctured) :
    ContDiffOn ℝ 1 (primitive radialCoefficients (base 1) (base 2)) (openCell lo hi) ∧
    ∀ p ∈ openCell lo hi,
      extDeriv (primitive radialCoefficients (base 1) (base 2)) p = zeta p := by
  have hf (i : Fin 3) : ContDiffOn ℝ 1 (radialCoefficients i) (openCell lo hi) := by
    intro p hp
    have hn : p ≠ 0 := hpunct hp
    exact ((EuclideanSpace.proj i).contDiff.contDiffAt.div
      ((contDiffAt_norm ℝ hn).pow 3) (pow_ne_zero 3 (norm_ne_zero_iff.mpr hn))).contDiffWithinAt
  have he : omega radialCoefficients = zeta := rfl
  simpa only [he] using primitive_identity hf (fun p hp => by rw [he]; exact zeta_closed (hpunct hp)) hb

/-- Zero-length bounds are valid for arbitrary coefficients, not only radial ones. -/
theorem base_values (f : Fin 3 → Space → ℝ) (base : Space) :
    g1 f (base 1) (base 2) base = 0 ∧ g2 f (base 2) base = 0 := by
  simp [g1, g2]

theorem first_base_coordinate_unused (f : Fin 3 → Space → ℝ) (a a' b c : ℝ) :
    primitive f ((WithLp.toLp 2 ![a,b,c] : Space) 1) ((WithLp.toLp 2 ![a,b,c] : Space) 2) =
    primitive f ((WithLp.toLp 2 ![a',b,c] : Space) 1) ((WithLp.toLp 2 ![a',b,c] : Space) 2) := rfl

theorem cell_boundary_excluded (lo hi : Fin 3 → ℝ) (p : Space) (i : Fin 3)
    (h : p i = lo i ∨ p i = hi i) : p ∉ openCell lo hi := by
  intro hp
  rcases h with h | h
  · exact (lt_irrefl _ (h ▸ (hp i).1))
  · exact (lt_irrefl _ (h ▸ (hp i).2))

/-- A nonradial, nonconstant polynomial closed 2-form. -/
def polynomialCoefficients : Fin 3 → Space → ℝ :=
  ![fun _ => 0, fun p => p 0 ^ 2, fun _ => 1]

theorem polynomial_coefficients_c1 (i : Fin 3) :
    ContDiff ℝ 1 (polynomialCoefficients i) := by
  fin_cases i <;> simp [polynomialCoefficients] <;> fun_prop

theorem polynomial_closed (p : Space) : extDeriv (omega polynomialCoefficients) p = 0 := by
  have hw : DifferentiableAt ℝ (omega polynomialCoefficients) p := by
    have hs : ContDiff ℝ 1 (omega polynomialCoefficients) :=
      (((polynomial_coefficients_c1 0).smul contDiff_const).add
        ((polynomial_coefficients_c1 1).smul contDiff_const)).add
        ((polynomial_coefficients_c1 2).smul contDiff_const)
    exact hs.contDiffAt.differentiableAt one_ne_zero
  have he : extDeriv (omega polynomialCoefficients) p (EuclideanSpace.basisFun (Fin 3) ℝ) = 0 := by
    rw [extDeriv_apply hw, Fin.sum_univ_three]
    have h0 : (fun q => omega polynomialCoefficients q ((0 : Fin 3).removeNth
        (EuclideanSpace.basisFun (Fin 3) ℝ))) = fun _ => (0 : ℝ) := by
      funext q
      norm_num [omega, polynomialCoefficients, Fin.removeNth, Fin.tail, Fin.succAbove,
        EuclideanSpace.basisFun_apply]
    have h1 : (fun q => omega polynomialCoefficients q ((1 : Fin 3).removeNth
        (EuclideanSpace.basisFun (Fin 3) ℝ))) = fun q => -(q 0 ^ 2) := by
      funext q
      norm_num [omega, polynomialCoefficients, Fin.removeNth, Fin.tail, Fin.succAbove,
        EuclideanSpace.basisFun_apply]
    have h2 : (fun q => omega polynomialCoefficients q ((2 : Fin 3).removeNth
        (EuclideanSpace.basisFun (Fin 3) ℝ))) = fun _ => (1 : ℝ) := by
      funext q
      norm_num [omega, polynomialCoefficients, Fin.removeNth, Fin.tail, Fin.succAbove,
        EuclideanSpace.basisFun_apply]
    have hd := (((EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).hasFDerivAt (x := p)).pow 2).neg
    change HasFDerivAt (fun q : Space => -(q 0 ^ 2)) _ p at hd
    rw [h0, h1, h2, hd.fderiv]
    simp [EuclideanSpace.basisFun_apply]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [AlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (extDeriv (omega polynomialCoefficients) p).toAlternatingMap]
  change (extDeriv (omega polynomialCoefficients) p (EuclideanSpace.basisFun (Fin 3) ℝ)) • _ = _
  rw [he, zero_smul]
  rfl

theorem polynomial_values (b c : ℝ) (p : Space) :
    g1 polynomialCoefficients b c p = p 0 ^ 2 * (p 2-c) - (p 1-b) ∧
    g2 polynomialCoefficients c p = 0 := by
  simp [g1, g2, polynomialCoefficients, mul_comm]

/-- The theorem is instantiated with closedness, not with derivative identities. -/
theorem polynomial_primitive_test {lo hi : Fin 3 → ℝ} {base p : Space}
    (hb : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi) :
    extDeriv (primitive polynomialCoefficients (base 1) (base 2)) p =
      omega polynomialCoefficients p ∧ omega polynomialCoefficients p ≠ 0 := by
  refine ⟨(primitive_identity (fun i => (polynomial_coefficients_c1 i).contDiffOn)
    (fun q _ => polynomial_closed q) hb).2 p hp, ?_⟩
  intro he
  have h := congrArg (fun w : Space [⋀^Fin 2]→L[ℝ] ℝ => w ![basis 0,basis 1]) he
  norm_num [omega, polynomialCoefficients, basis] at h

/-- Both bounds are reversed; the displayed values retain both base coordinates. -/
theorem reversed_bounds_test :
    g1 polynomialCoefficients 3 4 (WithLp.toLp 2 ![2,1,2]) = -6 ∧
    g2 polynomialCoefficients 4 (WithLp.toLp 2 ![2,1,2]) = 0 := by
  convert polynomial_values 3 4 (WithLp.toLp 2 ![2,1,2]) using 1; norm_num

theorem coordinateSlice_partial_ne {lo hi : Fin 3 → ℝ} {F : Space → ℝ}
    (hF : ContDiffOn ℝ 1 F (openCell lo hi)) {i j : Fin 3} (hji : j ≠ i) {a : ℝ}
    (ha : a ∈ Ioo (lo i) (hi i)) {p : Space} (hp : p ∈ openCell lo hi) :
    coordPartial (fun q => F (replaceCoordinate q i a)) j p =
      coordPartial F j (replaceCoordinate p i a) := by
  have hm := replace_mem hp i ha
  have hf := ((hF _ hm).contDiffAt ((openCell_isOpen lo hi).mem_nhds hm)).differentiableAt one_ne_zero
  have hd : HasFDerivAt (fun q => replaceCoordinate q i a) (cut i) p := by
    simp only [replace_eq]
    exact (cut i).hasFDerivAt.add_const _
  have hh := hf.hasFDerivAt.comp p hd
  change fderiv ℝ (F ∘ fun q => replaceCoordinate q i a) p (basis j) = _
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, cut_basis hji, coordPartial]

/-- The other transverse derivatives are also obtained under the integral sign. -/
theorem remaining_transverse_partials {lo hi : Fin 3 → ℝ} {f : Fin 3 → Space → ℝ}
    (hf : ∀ i, ContDiffOn ℝ 1 (f i) (openCell lo hi)) {base p : Space}
    (hb : base ∈ openCell lo hi) (hp : p ∈ openCell lo hi) :
    coordPartial (g1 f (base 1) (base 2)) 0 p =
      (∫ t in base 2..p 2, coordPartial (f 1) 0 (replaceCoordinate p 2 t)) -
      (∫ t in base 1..p 1, coordPartial (f 2) 0
        (replaceCoordinate (replaceCoordinate p 1 t) 2 (base 2))) ∧
    coordPartial (g2 f (base 2)) 1 p =
      -(∫ t in base 2..p 2, coordPartial (f 0) 1 (replaceCoordinate p 2 t)) := by
  have hA := coordinateIntegral_c1 (hf 1) 2 (hb 2)
  have hB := coordinateIntegral_c1 (coordinateSlice_c1 (hf 2) 2 (hb 2)) 1 (hb 1)
  have hC := coordinateIntegral_c1 (hf 0) 2 (hb 2)
  have dA := ((hA p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have dB := ((hB p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  have dC := ((hC p hp).contDiffAt ((openCell_isOpen lo hi).mem_nhds hp)).differentiableAt one_ne_zero
  constructor
  · rw [g1_as_integrals]
    change fderiv ℝ _ p (basis 0) = _
    rw [fderiv_fun_sub dA dB, sub_apply]
    change coordPartial _ 0 p - coordPartial _ 0 p = _
    rw [coordinateIntegral_partial_ne (hf 1) (by decide) (hb 2) hp,
      coordinateIntegral_partial_ne (coordinateSlice_c1 (hf 2) 2 (hb 2)) (by decide) (hb 1) hp]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    exact coordinateSlice_partial_ne (hf 2) (by decide) (hb 2)
      (coordinate_segment_in_cell hp 1 (hb 1) ht)
  · rw [g2_as_integral]
    change fderiv ℝ _ p (basis 1) = _
    rw [fderiv_fun_neg, neg_apply]
    change -coordPartial _ 1 p = _
    rw [coordinateIntegral_partial_ne (hf 0) (by decide) (hb 2) hp]

/-- Nonzero-length axis segments remain inside the punctured cell; no zero-height
base is substituted. The resulting 1-form is zero at this point but has nonzero derivative. -/
theorem axis_cell_test :
    let base : Space := WithLp.toLp 2 ![0,0,2]
    let p : Space := WithLp.toLp 2 ![0,0,3]
    g1 radialCoefficients (base 1) (base 2) p = 0 ∧
    g2 radialCoefficients (base 2) p = 0 ∧
    extDeriv (primitive radialCoefficients (base 1) (base 2)) p = zeta p ∧
    zeta p ≠ 0 := by
  dsimp
  have hb : (WithLp.toLp 2 ![0,0,2] : Space) ∈ openCell ![-1,-1,1] ![1,1,4] := by
    intro i; fin_cases i <;> norm_num
  have hp : (WithLp.toLp 2 ![0,0,3] : Space) ∈ openCell ![-1,-1,1] ![1,1,4] := by
    intro i; fin_cases i <;> norm_num
  have hs : openCell ![-1,-1,1] ![1,1,4] ⊆ punctured := by
    intro q hq he
    have := hq 2
    norm_num [he] at this
  refine ⟨?_, ?_, (radial_cell_primitive hb hs).2 _ hp, ?_⟩
  · norm_num [g1, radialCoefficients]
  · norm_num [g2, radialCoefficients]
  · intro he
    have h := congrArg (fun w : Space [⋀^Fin 2]→L[ℝ] ℝ => w ![basis 0,basis 1]) he
    norm_num [zeta_apply, basis, radius_formula] at h

end Rudin.Chapter10.Exercise27





