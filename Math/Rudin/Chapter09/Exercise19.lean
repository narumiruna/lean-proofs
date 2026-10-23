module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Tactic

/-! # Local solution graphs for the two affine branches

The source's solvability is local to a solution, not global uniqueness.
The fourth coordinate is constant on each branch and cannot parametrize it.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff
namespace Rudin.Chapter09

/-- The three literal source equations. -/
def exercise19System (x y z u : ℝ) : Prop :=
  3 * x + y - z + u ^ 2 = 0 ∧ x - y + 2 * z + u = 0 ∧
    2 * x + 2 * y - 3 * z + 2 * u = 0

theorem exercise19_classification (x y z u : ℝ) :
    exercise19System x y z u ↔
      (u = 0 ∨ u = 3) ∧ x = -z / 4 - u ∧ y = 7 * z / 4 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hu : u * (u - 3) = 0 := by nlinarith
    refine ⟨?_, by linarith, by linarith⟩
    rcases mul_eq_zero.mp hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (by linarith)
  · rintro ⟨hu, hx, hy⟩
    rcases hu with rfl | rfl <;> subst x <;> subst y <;>
      norm_num [exercise19System] <;> ring_nf <;> trivial

/-- A unit-width band excludes the other affine branch. -/
theorem exercise19_branch_isolated {u u₀ : ℝ} (h₀ : u₀ = 0 ∨ u₀ = 3)
    (hu : u = 0 ∨ u = 3) (hnear : |u - u₀| < 1) : u = u₀ := by
  rcases h₀ with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num at *

theorem exercise19_solve_in_z {x₀ y₀ z₀ u₀ : ℝ}
    (h₀ : exercise19System x₀ y₀ z₀ u₀) (x y z u : ℝ) (hu : |u - u₀| < 1) :
    exercise19System x y z u ↔ x = -z / 4 - u₀ ∧ y = 7 * z / 4 ∧ u = u₀ := by
  rw [exercise19_classification] at h₀ ⊢
  constructor
  · rintro ⟨hb, hx, hy⟩
    have he := exercise19_branch_isolated h₀.1 hb hu
    exact ⟨by simpa [he] using hx, hy, he⟩
  · rintro ⟨hx, hy, rfl⟩; exact ⟨h₀.1, hx, hy⟩

theorem exercise19_solve_in_y {x₀ y₀ z₀ u₀ : ℝ}
    (h₀ : exercise19System x₀ y₀ z₀ u₀) (x y z u : ℝ) (hu : |u - u₀| < 1) :
    exercise19System x y z u ↔ x = -y / 7 - u₀ ∧ z = 4 * y / 7 ∧ u = u₀ := by
  rw [exercise19_solve_in_z h₀ x y z u hu]
  constructor
  · rintro ⟨hx, hy, he⟩; exact ⟨by linarith, by linarith, he⟩
  · rintro ⟨hx, hz, he⟩; exact ⟨by linarith, by linarith, he⟩

theorem exercise19_solve_in_x {x₀ y₀ z₀ u₀ : ℝ}
    (h₀ : exercise19System x₀ y₀ z₀ u₀) (x y z u : ℝ) (hu : |u - u₀| < 1) :
    exercise19System x y z u ↔ y = -7 * (x + u₀) ∧ z = -4 * (x + u₀) ∧ u = u₀ := by
  rw [exercise19_solve_in_z h₀ x y z u hu]
  constructor
  · rintro ⟨hx, hy, he⟩; exact ⟨by linarith, by linarith, he⟩
  · rintro ⟨hy, hz, he⟩; exact ⟨by linarith, by linarith, he⟩

/-- Four coordinates are used only for the topology, not a replacement norm claim. -/
abbrev Exercise19Space := Fin 4 → ℝ

def exercise19Band (u₀ : ℝ) : Set Exercise19Space := {p | |p 3 - u₀| < 1}

theorem exercise19_band_open (u₀ : ℝ) : IsOpen (exercise19Band u₀) :=
  isOpen_lt (by fun_prop) continuous_const

theorem exercise19_band_contains (x y z u : ℝ) :
    (![x,y,z,u] : Exercise19Space) ∈ exercise19Band u := by simp [exercise19Band]

/-- The three explicit graphs are smooth on the open parameter interval ℝ. -/
theorem exercise19_smooth_graphs (u₀ : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ ↦ (![-z / 4 - u₀, 7 * z / 4, z, u₀] : Exercise19Space)) ∧
    ContDiff ℝ ∞ (fun y : ℝ ↦ (![-y / 7 - u₀, y, 4 * y / 7, u₀] : Exercise19Space)) ∧
    ContDiff ℝ ∞ (fun x : ℝ ↦ (![x, -7 * (x + u₀), -4 * (x + u₀), u₀] : Exercise19Space)) := by
  constructor
  · apply contDiff_pi.mpr; intro i; fin_cases i <;> simp <;> fun_prop
  constructor <;> apply contDiff_pi.mpr <;> intro i <;> fin_cases i <;> simp <;> fun_prop

/-- One explicit open neighborhood gives all three unique graph descriptions. -/
theorem exercise19_local_graphs {x₀ y₀ z₀ u₀ : ℝ}
    (h₀ : exercise19System x₀ y₀ z₀ u₀) :
    ∃ U : Set Exercise19Space, IsOpen U ∧ ![x₀,y₀,z₀,u₀] ∈ U ∧
      ∀ p ∈ U,
        (exercise19System (p 0) (p 1) (p 2) (p 3) ↔
          p = ![-p 2 / 4 - u₀, 7 * p 2 / 4, p 2, u₀]) ∧
        (exercise19System (p 0) (p 1) (p 2) (p 3) ↔
          p = ![-p 1 / 7 - u₀, p 1, 4 * p 1 / 7, u₀]) ∧
        (exercise19System (p 0) (p 1) (p 2) (p 3) ↔
          p = ![p 0, -7 * (p 0 + u₀), -4 * (p 0 + u₀), u₀]) := by
  refine ⟨exercise19Band u₀, exercise19_band_open u₀,
    exercise19_band_contains _ _ _ _, ?_⟩
  intro p hp
  change |p 3 - u₀| < 1 at hp
  have hz := exercise19_solve_in_z h₀ (p 0) (p 1) (p 2) (p 3) hp
  have hy := exercise19_solve_in_y h₀ (p 0) (p 1) (p 2) (p 3) hp
  have hx := exercise19_solve_in_x h₀ (p 0) (p 1) (p 2) (p 3) hp
  simpa [funext_iff, Fin.forall_fin_succ] using And.intro hz (And.intro hy hx)

/-- Arbitrarily close distinct solutions have the same fourth coordinate. -/
theorem exercise19_failure_in_u {x₀ y₀ z₀ u₀ : ℝ}
    (h₀ : exercise19System x₀ y₀ z₀ u₀) {V : Set Exercise19Space}
    (hV : V ∈ 𝓝 (![x₀,y₀,z₀,u₀] : Exercise19Space)) :
    ∃ p ∈ V, exercise19System (p 0) (p 1) (p 2) (p 3) ∧
      p 3 = u₀ ∧ p ≠ ![x₀,y₀,z₀,u₀] := by
  let L : ℝ → Exercise19Space := fun x ↦ ![x, -7 * (x + u₀), -4 * (x + u₀), u₀]
  have hc : Continuous L := (exercise19_smooth_graphs u₀).2.2.continuous
  have hs := (exercise19_solve_in_x h₀ x₀ y₀ z₀ u₀ (by simp)).mp h₀
  have hb : L x₀ = ![x₀,y₀,z₀,u₀] := by simp [L, hs.1, hs.2.1]
  have hp : L ⁻¹' V ∈ 𝓝 x₀ := hc.continuousAt.preimage_mem_nhds (hb ▸ hV)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hp
  have hm : x₀ + r / 2 ∈ Metric.ball x₀ r := by
    simp [Metric.mem_ball, abs_of_pos hr]
    linarith
  refine ⟨L (x₀ + r / 2), hrs hm, ?_, by simp [L], ?_⟩
  · apply (exercise19_classification _ _ _ _).mpr
    change (u₀ = 0 ∨ u₀ = 3) ∧
      x₀ + r / 2 = -(-4 * (x₀ + r / 2 + u₀)) / 4 - u₀ ∧
      -7 * (x₀ + r / 2 + u₀) = 7 * (-4 * (x₀ + r / 2 + u₀)) / 4
    refine ⟨(exercise19_classification _ _ _ _).mp h₀ |>.1, ?_, ?_⟩ <;> ring
  · intro he
    have he0 := congrFun he 0
    simp [L] at he0
    linarith

end Rudin.Chapter09
