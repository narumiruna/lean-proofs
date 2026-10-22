module

public import Math.Rudin.Chapter02.Exercise17

/-! # Exercise 2.18

There is a nonempty perfect real set with no rational members. A finer Polish
topology makes the irrational reals closed. A continuous injection of binary
sequence space into that closed uncountable set gives a compact perfect set
in the usual real topology. Only the usual real topology occurs in the result.
-/

@[expose] public section
namespace Rudin.Chapter02

open Set Topology

/-- A compact nonempty perfect set of irrational real numbers exists. -/
theorem exists_nonempty_perfect_irrational_set :
    ∃ P : Set ℝ, P.Nonempty ∧ Perfect P ∧ IsCompact P ∧
      Disjoint P (range ((↑) : ℚ → ℝ)) := by
  let t₀ : TopologicalSpace ℝ := inferInstance
  let Q : Set ℝ := range ((↑) : ℚ → ℝ)
  have hQ : Q.Countable := countable_range _
  have hunc : ¬ Qᶜ.Countable := by
    intro h
    have hall : (univ : Set ℝ).Countable := by
      simpa using h.union hQ
    exact not_countable_univ hall
  obtain ⟨t, ht, hp, hclosed, _⟩ := hQ.measurableSet.isClopenable.compl
  obtain ⟨f, hf, hc, hi⟩ :=
    @IsClosed.exists_nat_bool_injection_of_not_countable ℝ t hp Qᶜ hclosed hunc
  let : TopologicalSpace ℝ := t₀
  have hid : @Continuous ℝ ℝ t t₀ id := continuous_id_of_le ht
  have hc' : Continuous f :=
    @Continuous.comp (ℕ → Bool) ℝ ℝ Pi.topologicalSpace t t₀ f id hid hc
  refine ⟨range f, range_nonempty f, perfect_range_binary f hc' hi, ?_, ?_⟩
  · simpa only [image_univ] using isCompact_univ.image hc'
  · exact disjoint_left.mpr (fun x hx hq => hf hx hq)

/-- A fixed choice of the real set constructed above. -/
noncomputable def irrationalPerfectSet : Set ℝ :=
  Classical.choose exists_nonempty_perfect_irrational_set

theorem irrationalPerfectSet_nonempty : irrationalPerfectSet.Nonempty :=
  (Classical.choose_spec exists_nonempty_perfect_irrational_set).1

theorem irrationalPerfectSet_perfect : Perfect irrationalPerfectSet :=
  (Classical.choose_spec exists_nonempty_perfect_irrational_set).2.1

theorem irrationalPerfectSet_isClosed : IsClosed irrationalPerfectSet :=
  irrationalPerfectSet_perfect.closed

theorem irrationalPerfectSet_isCompact : IsCompact irrationalPerfectSet :=
  (Classical.choose_spec exists_nonempty_perfect_irrational_set).2.2.1

theorem irrationalPerfectSet_disjoint_rationals :
    Disjoint irrationalPerfectSet (range ((↑) : ℚ → ℝ)) :=
  (Classical.choose_spec exists_nonempty_perfect_irrational_set).2.2.2

theorem irrationalPerfectSet_no_rational (q : ℚ) : (q : ℝ) ∉ irrationalPerfectSet := by
  intro hq
  exact Set.disjoint_left.mp irrationalPerfectSet_disjoint_rationals hq (mem_range_self q)

theorem irrationalPerfectSet_irrational {x : ℝ} (hx : x ∈ irrationalPerfectSet) :
    Irrational x := by
  rintro ⟨q, hq⟩
  exact irrationalPerfectSet_no_rational q (hq ▸ hx)

end Rudin.Chapter02
