module

public import Mathlib

@[expose] public section

open Set Filter
open scoped Topology

namespace Rudin.Chapter04

/-- The intermediate value property, with no ordering restriction on the two inputs. -/
def Exercise19IntermediateValue (f : ℝ → ℝ) : Prop :=
  ∀ a b c, f a < c → c < f b → ∃ x ∈ uIoo a b, f x = c

/-- A closed level set cannot be crossed near a point outside it. -/
theorem exercise19_no_crossing {f : ℝ → ℝ}
    (hiv : Exercise19IntermediateValue f) {r x : ℝ}
    (hc : IsClosed {y | f y = r}) (hx : f x ≠ r) :
    ∀ᶠ y in 𝓝 x, (f x < r → f y < r) ∧ (r < f x → r < f y) := by
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hc.isOpen_compl.mem_nhds hx)
  filter_upwards [Ioo_mem_nhds hl hu] with y hy
  have hne : f y ≠ r := hsub hy
  have hseg : uIoo x y ⊆ Ioo l u :=
    uIoo_subset_uIcc_self.trans (ordConnected_Ioo.uIcc_subset ⟨hl, hu⟩ hy)
  constructor
  · intro hxr
    by_contra! h
    obtain ⟨z, hz, he⟩ := hiv x y r hxr (lt_of_le_of_ne h hne.symm)
    exact hsub (hseg hz) he
  · intro hrx
    by_contra! h
    obtain ⟨z, hz, he⟩ := hiv y x r (lt_of_le_of_ne h hne) hrx
    rw [uIoo_comm] at hz
    exact hsub (hseg hz) he

/-- Darboux's property and closed rational fibers imply continuity everywhere. -/
theorem exercise19_closed_rational_fibers {f : ℝ → ℝ}
    (hiv : Exercise19IntermediateValue f)
    (hclosed : ∀ r : ℚ, IsClosed {x | f x = (r : ℝ)}) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨r, hlr, hrx⟩ := exists_rat_btwn hl
    filter_upwards [exercise19_no_crossing hiv (hclosed r) (ne_of_gt hrx)] with y hy
    exact hlr.trans (hy.2 hrx)
  · intro u hu
    obtain ⟨r, hxr, hru⟩ := exists_rat_btwn hu
    filter_upwards [exercise19_no_crossing hiv (hclosed r) (ne_of_lt hxr)] with y hy
    exact (hy.1 hxr).trans hru

end Rudin.Chapter04
