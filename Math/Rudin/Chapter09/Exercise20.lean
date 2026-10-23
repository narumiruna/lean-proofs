module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic

/-! # Scalar implicit graphs and the geometry of the inverse-function proof -/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace Rudin.Chapter09

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- Split a scalar differential into its two coordinate parts. -/
theorem scalarDifferential_split (L : ℝ × Y →L[ℝ] ℝ) (x : ℝ) (y : Y) :
    L (x, y) = L (1, 0) * x + L (0, y) := by
  have h : (x, y) = x • (1, (0 : Y)) + (0, y) := by simp
  rw [h, map_add, map_smul]
  simp [mul_comm]

/-- The derivative of `(x,y) ↦ (f(x,y),y)` is invertible when `D₁f ≠ 0`. -/
noncomputable def scalarGraphEquiv (L : ℝ × Y →L[ℝ] ℝ) (h : L (1, 0) ≠ 0) :
    (ℝ × Y) ≃L[ℝ] (ℝ × Y) :=
  ContinuousLinearEquiv.ofBijective (L.prod (ContinuousLinearMap.snd ℝ ℝ Y)) (by
    apply LinearMap.ker_eq_bot.mpr
    intro p q hpq
    change (L p, p.2) = (L q, q.2) at hpq
    have hy : p.2 = q.2 := (Prod.mk.inj hpq).2
    have hx : L p = L q := (Prod.mk.inj hpq).1
    change L (p.1, p.2) = L (q.1, q.2) at hx
    rw [scalarDifferential_split L p.1 p.2, scalarDifferential_split L q.1 q.2, hy] at hx
    exact Prod.ext (mul_left_cancel₀ h (add_right_cancel hx)) hy) (by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨u, y⟩
    refine ⟨((u - L (0, y)) / L (1, 0), y), ?_⟩
    apply Prod.ext
    · change L ((u - L (0, y)) / L (1, 0), y) = u
      rw [scalarDifferential_split]
      field_simp
      ring
    · rfl)

@[simp] theorem scalarGraphEquiv_apply (L : ℝ × Y →L[ℝ] ℝ) (h) (p) :
    scalarGraphEquiv L h p = (L p, p.2) := rfl

theorem scalarGraphEquiv_symm_zero (L : ℝ × Y →L[ℝ] ℝ) (h) (y : Y) :
    (scalarGraphEquiv L h).symm (0, y) = (-L (0, y) / L (1, 0), y) := by
  apply (scalarGraphEquiv L h).injective
  simp only [ContinuousLinearEquiv.apply_symm_apply, scalarGraphEquiv_apply]
  apply Prod.ext
  · change 0 = L (-L (0, y) / L (1, 0), y)
    rw [scalarDifferential_split]
    field_simp
    ring
  · rfl

/-- A local graph includes the actual coordinate change and its inverse on the zero line.
`W` is open; uniqueness is among points in the open source of `e`, not global. -/
structure ScalarImplicitGraph (f : ℝ × Y → ℝ) (a : ℝ) (b : Y)
    (L : ℝ × Y →L[ℝ] ℝ) where
  e : OpenPartialHomeomorph (ℝ × Y) (ℝ × Y)
  coordinateChange : ∀ p, e p = (f p, p.2)
  base_mem : (a, b) ∈ e.source
  W : Set Y
  open_W : IsOpen W
  mem_W : b ∈ W
  g : Y → ℝ
  base_value : g b = a
  smooth : ContDiffOn ℝ 1 g W
  derivative : HasFDerivAt g
    (-(L (1, 0))⁻¹ • (L.comp (ContinuousLinearMap.inr ℝ ℝ Y))) b
  zero_line : ∀ y ∈ W, (0, y) ∈ e.target ∧ e.symm (0, y) = (g y, y)
  graph_mem : ∀ y ∈ W, (g y, y) ∈ e.source
  equation : ∀ y ∈ W, f (g y, y) = 0
  unique : ∀ y ∈ W, ∀ x, (x, y) ∈ e.source → (f (x, y) = 0 ↔ x = g y)

/-- Construct the graph by the inverse function theorem, with only local `C¹` input. -/
theorem scalarImplicitGraph_exists {f : ℝ × Y → ℝ} {a : ℝ} {b : Y}
    (hf : ContDiffAt ℝ 1 f (a, b)) {L : ℝ × Y →L[ℝ] ℝ}
    (hd : HasFDerivAt f L (a, b)) (hz : f (a, b) = 0) (hn : L (1, 0) ≠ 0) :
    Nonempty (ScalarImplicitGraph f a b L) := by
  let F : ℝ × Y → ℝ × Y := fun p => (f p, p.2)
  let A := scalarGraphEquiv L hn
  have hF : ContDiffAt ℝ 1 F (a, b) := hf.prodMk contDiffAt_snd
  have hD : HasFDerivAt F (A : (ℝ × Y) →L[ℝ] (ℝ × Y)) (a, b) :=
    hd.prodMk hasFDerivAt_snd
  let e := hF.toOpenPartialHomeomorph F hD (by norm_num)
  let G := hF.localInverse hD (by norm_num)
  let g : Y → ℝ := fun y => (G (0, y)).1
  have hbase : F (a, b) = (0, b) := by simp [F, hz]
  have hGb : G (0, b) = (a, b) := by
    rw [← hbase]; exact hF.localInverse_apply_image hD (by norm_num)
  have hGc : ContDiffAt ℝ 1 G (0, b) := by
    rw [← hbase]; exact hF.to_localInverse hD (by norm_num)
  have hgc : ContDiffAt ℝ 1 g b :=
    (hGc.comp b (contDiffAt_const.prodMk contDiffAt_id)).fst
  have hGd : HasFDerivAt G (A.symm : (ℝ × Y) →L[ℝ] (ℝ × Y)) (0, b) := by
    rw [← hbase]
    exact (hF.hasStrictFDerivAt' hD (by norm_num)).to_localInverse.hasFDerivAt
  have hgd : HasFDerivAt g
      (-(L (1, 0))⁻¹ • (L.comp (ContinuousLinearMap.inr ℝ ℝ Y))) b := by
    have hdg := (hGd.comp b ((hasFDerivAt_const (0 : ℝ) b).prodMk
      (hasFDerivAt_id b))).fst
    have heq : (ContinuousLinearMap.fst ℝ ℝ Y).comp
        ((A.symm : (ℝ × Y) →L[ℝ] (ℝ × Y)).comp
          ((0 : Y →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Y))) =
        -(L (1, 0))⁻¹ • (L.comp (ContinuousLinearMap.inr ℝ ℝ Y)) := by
      ext y
      simp [A, scalarGraphEquiv_symm_zero, div_eq_mul_inv, mul_comm]
    rw [heq] at hdg
    exact hdg
  have he : ∀ p, e p = F p := fun _ => rfl
  have hs : (a, b) ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hD (by norm_num)
  have ht : (0, b) ∈ e.target := by simpa only [he, hbase] using e.map_source hs
  have htarget : {y : Y | (0, y) ∈ e.target} ∈ 𝓝 b :=
    (e.open_target.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht
  obtain ⟨W, hWsub, hWopen, hbW⟩ := mem_nhds_iff.mp
    (inter_mem htarget (hgc.eventually (by norm_num)))
  have hline (y : Y) (hy : y ∈ W) : e.symm (0, y) = (g y, y) := by
    have hr := e.right_inv (hWsub hy).1
    have hsnd : (e.symm (0, y)).2 = y := congrArg Prod.snd hr
    exact Prod.ext rfl hsnd
  refine ⟨{
    e := e
    coordinateChange := he
    base_mem := hs
    W := W
    open_W := hWopen
    mem_W := hbW
    g := g
    base_value := congrArg Prod.fst hGb
    smooth := fun y hy =>
      (show ContDiffAt ℝ 1 g y from (hWsub hy).2).contDiffWithinAt
    derivative := hgd
    zero_line := fun y hy => ⟨(hWsub hy).1, hline y hy⟩
    graph_mem := ?_
    equation := ?_
    unique := ?_ }⟩
  · intro y hy
    rw [← hline y hy]
    exact e.map_target (hWsub hy).1
  · intro y hy
    have hr := e.right_inv (hWsub hy).1
    rw [hline y hy] at hr
    exact congrArg Prod.fst hr
  · intro y hy x hx
    constructor
    · intro hzero
      have hh : e (x, y) = (0, y) := by change (f (x, y), y) = _; rw [hzero]
      have hi := e.left_inv hx
      rw [hh, hline y hy] at hi
      exact (congrArg Prod.fst hi).symm
    · rintro rfl
      have hr := e.right_inv (hWsub hy).1
      rw [hline y hy] at hr
      exact congrArg Prod.fst hr

/-- Exercise 20: the scalar theorem and its graphical proof, with the tangent slope. -/
theorem exercise20_graph {f : ℝ × ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffAt ℝ 1 f (a, b)) (hz : f (a, b) = 0)
    (hn : fderiv ℝ f (a, b) (1, 0) ≠ 0) :
    ∃ S : ScalarImplicitGraph f a b (fderiv ℝ f (a, b)),
      HasDerivAt S.g
        (-fderiv ℝ f (a, b) (0, 1) / fderiv ℝ f (a, b) (1, 0)) b := by
  obtain ⟨S⟩ := scalarImplicitGraph_exists hf (hf.differentiableAt (by norm_num)).hasFDerivAt hz hn
  refine ⟨S, ?_⟩
  convert S.derivative.hasDerivAt using 1
  simp [div_eq_mul_inv, mul_comm]

/-- The coordinate derivatives exist; the displayed slope uses genuine partial derivatives. -/
theorem exercise20_partials {f : ℝ × ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffAt ℝ 1 f (a, b)) :
    HasDerivAt (fun x => f (x, b)) (fderiv ℝ f (a, b) (1, 0)) a ∧
    HasDerivAt (fun y => f (a, y)) (fderiv ℝ f (a, b) (0, 1)) b := by
  have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt
  constructor
  · convert hd.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a b)) using 1
    rfl
  · convert hd.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b)) using 1
    rfl

/-- The local zero set is a graph and the coordinate change maps it onto a vertical line. -/
theorem exercise20_proof_graph {f : ℝ × ℝ → ℝ} {a b : ℝ}
    {L : ℝ × ℝ →L[ℝ] ℝ} (S : ScalarImplicitGraph f a b L) :
    {p | p ∈ S.e.source ∧ p.2 ∈ S.W ∧ f p = 0} =
      (fun y => (S.g y, y)) '' S.W ∧
    S.e '' {p | p ∈ S.e.source ∧ p.2 ∈ S.W ∧ f p = 0} =
      {q | q.1 = 0 ∧ q.2 ∈ S.W} := by
  constructor
  · ext p
    constructor
    · rintro ⟨hp, hy, hz⟩
      exact ⟨p.2, hy, Prod.ext ((S.unique p.2 hy p.1 hp).mp hz).symm rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨S.graph_mem y hy, hy, S.equation y hy⟩
  · ext q
    constructor
    · rintro ⟨p, ⟨hp, hy, hz⟩, rfl⟩
      simpa [S.coordinateChange, hz] using hy
    · rintro ⟨hz, hy⟩
      refine ⟨(S.g q.2, q.2), ⟨S.graph_mem q.2 hy, hy, S.equation q.2 hy⟩, ?_⟩
      rw [S.coordinateChange, S.equation q.2 hy]
      exact Prod.ext hz.symm rfl

end Rudin.Chapter09
