module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic

/-!
# R01E20: cuts with greatest elements permitted

Source: Exercise 20, book page 23 (PDF 32); Appendix, Steps 1–4,
book pages 17–18 (PDF 26–27); Definition 1.12, book page 5 (PDF 14).
Only Appendix property (III) is removed. The carrier is an actual nonempty
proper lower subset of `ℚ`. Strict order is proper inclusion. Addition is
exactly the set of pairwise sums, without taking a closure.

A1 is closure, A2 commutativity, A3 associativity, A4 a left identity,
and A5 an inverse for every element. The identity here is `Set.Iic 0`.
The cut `Set.Iio 0` has no inverse for that identity.
-/

@[expose] public section

namespace Rudin.Chapter01

/-- Appendix properties (I) and (II), with no condition on greatest elements. -/
structure Exercise20Cut where
  carrier : Set ℚ
  nonempty : carrier.Nonempty
  proper : carrier ≠ Set.univ
  lower : IsLowerSet carrier

namespace Exercise20Cut

instance : Membership ℚ Exercise20Cut := ⟨fun a q => q ∈ a.carrier⟩

@[ext] theorem ext {a b : Exercise20Cut} (h : a.carrier = b.carrier) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- An element outside a cut is greater than every element inside it. -/
theorem member_lt_nonmember (a : Exercise20Cut) {r s : ℚ}
    (hr : r ∈ a) (hs : s ∉ a) : r < s := by
  by_contra h
  exact hs (a.lower (le_of_not_gt h) hr)

noncomputable instance : LinearOrder Exercise20Cut where
  le a b := a.carrier ⊆ b.carrier
  lt a b := a.carrier ⊂ b.carrier
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ hab hba := ext (Set.Subset.antisymm hab hba)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_total a b := by
    classical
    by_cases h : a.carrier ⊆ b.carrier
    · exact Or.inl h
    · right
      obtain ⟨r, hr, hnr⟩ := Set.not_subset.mp h
      intro s hs
      exact a.lower (le_of_lt (b.member_lt_nonmember hs hnr)) hr
  toDecidableLE := Classical.decRel _

/-- The actual union of a nonempty, bounded-above family. -/
def union (A : Set Exercise20Cut) (hne : A.Nonempty) (hb : BddAbove A) :
    Exercise20Cut where
  carrier := {q | ∃ a ∈ A, q ∈ a}
  nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨q, hq⟩ := a.nonempty
    exact ⟨q, a, ha, hq⟩
  proper := by
    obtain ⟨b, hb⟩ := hb
    obtain ⟨q, hq⟩ := (Set.ne_univ_iff_exists_notMem b.carrier).mp b.proper
    intro h
    have : q ∈ ({q | ∃ a ∈ A, q ∈ a} : Set ℚ) := by rw [h]; trivial
    obtain ⟨a, ha, hqa⟩ := this
    exact hq (hb ha hqa)
  lower := by
    intro p q hpq hq
    obtain ⟨a, ha, hqa⟩ := hq
    exact ⟨a, ha, a.lower hpq hqa⟩

/-- Setwise addition satisfies the two retained cut properties. -/
def add (a b : Exercise20Cut) : Exercise20Cut where
  carrier := {q | ∃ r ∈ a, ∃ s ∈ b, r + s = q}
  nonempty := by
    obtain ⟨r, hr⟩ := a.nonempty
    obtain ⟨s, hs⟩ := b.nonempty
    exact ⟨r + s, r, hr, s, hs, rfl⟩
  proper := by
    obtain ⟨r', hr'⟩ := (Set.ne_univ_iff_exists_notMem a.carrier).mp a.proper
    obtain ⟨s', hs'⟩ := (Set.ne_univ_iff_exists_notMem b.carrier).mp b.proper
    intro h
    have : r' + s' ∈ ({q | ∃ r ∈ a, ∃ s ∈ b, r + s = q} : Set ℚ) := by
      rw [h]; trivial
    obtain ⟨r, hr, s, hs, heq⟩ := this
    have := a.member_lt_nonmember hr hr'
    have := b.member_lt_nonmember hs hs'
    linarith
  lower := by
    intro q p hpq hq
    obtain ⟨r, hr, s, hs, rfl⟩ := hq
    refine ⟨p - s, a.lower (by linarith) hr, s, hs, ?_⟩
    ring

instance : Add Exercise20Cut := ⟨add⟩

/-- The new zero includes its endpoint. -/
def zero : Exercise20Cut where
  carrier := Set.Iic 0
  nonempty := ⟨0, by simp⟩
  proper := (Set.ne_univ_iff_exists_notMem _).mpr ⟨1, by norm_num⟩
  lower := isLowerSet_Iic _

instance : Zero Exercise20Cut := ⟨zero⟩

/-- This cut still has no greatest element, and is not the new zero. -/
def strictZero : Exercise20Cut where
  carrier := Set.Iio 0
  nonempty := ⟨-1, by norm_num⟩
  proper := (Set.ne_univ_iff_exists_notMem _).mpr ⟨0, by simp⟩
  lower := isLowerSet_Iio _

end Exercise20Cut

/-- The model contains exactly the sets satisfying source (I) and (II). -/
theorem exercise20_cut_properties (S : Set ℚ) :
    (∃ a : Exercise20Cut, a.carrier = S) ↔
      S.Nonempty ∧ S ≠ Set.univ ∧ ∀ p ∈ S, ∀ q : ℚ, q < p → q ∈ S := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.nonempty, a.proper, fun p hp q hqp => a.lower hqp.le hp⟩
  · rintro ⟨hne, hproper, hlower⟩
    refine ⟨⟨S, hne, hproper, ?_⟩, rfl⟩
    intro p q hqp hp
    rcases hqp.eq_or_lt with rfl | hlt
    · exact hp
    · exact hlower p hp q hlt

/-- Strict order is strict inclusion, and any two cuts satisfy trichotomy. -/
theorem exercise20_order (a b : Exercise20Cut) :
    (a < b ↔ a.carrier ⊂ b.carrier) ∧ (a < b ∨ a = b ∨ b < a) :=
  ⟨Iff.rfl, lt_trichotomy a b⟩

/-- The least upper bound is the union, with exactly the source membership rule. -/
theorem exercise20_union_isLUB (A : Set Exercise20Cut) (hne : A.Nonempty)
    (hb : BddAbove A) :
    IsLUB A (Exercise20Cut.union A hne hb) ∧
      ∀ q : ℚ, q ∈ Exercise20Cut.union A hne hb ↔ ∃ a ∈ A, q ∈ a := by
  refine ⟨⟨?_, ?_⟩, fun _ => Iff.rfl⟩
  · intro a ha q hq
    exact ⟨a, ha, hq⟩
  · intro b hb q hq
    obtain ⟨a, ha, hqa⟩ := hq
    exact hb ha hqa

/-- Every nonempty bounded-above family has a least upper bound. -/
theorem exercise20_least_upper_bounds (A : Set Exercise20Cut)
    (hne : A.Nonempty) (hb : BddAbove A) : ∃ c, IsLUB A c :=
  ⟨Exercise20Cut.union A hne hb, (exercise20_union_isLUB A hne hb).1⟩

/-- A1: the cut-valued sum has exactly the pairwise sums as its carrier. -/
theorem exercise20_addition_closed (a b : Exercise20Cut) :
    ∃ c : Exercise20Cut, c.carrier = {q | ∃ r ∈ a, ∃ s ∈ b, r + s = q} :=
  ⟨a + b, rfl⟩

/-- Membership in addition does not introduce any extra closure points. -/
theorem exercise20_mem_add (a b : Exercise20Cut) (q : ℚ) :
    q ∈ a + b ↔ ∃ r ∈ a, ∃ s ∈ b, r + s = q := Iff.rfl

/-- A2. -/
theorem exercise20_addition_commutative (a b : Exercise20Cut) : a + b = b + a := by
  apply Exercise20Cut.ext
  ext q
  change (∃ r ∈ a, ∃ s ∈ b, r + s = q) ↔ (∃ s ∈ b, ∃ r ∈ a, s + r = q)
  constructor <;> rintro ⟨r, hr, s, hs, h⟩ <;> exact ⟨s, hs, r, hr, by linarith⟩

/-- A3. -/
theorem exercise20_addition_associative (a b c : Exercise20Cut) :
    (a + b) + c = a + (b + c) := by
  apply Exercise20Cut.ext
  ext q
  constructor
  · rintro ⟨t, ⟨r, hr, s, hs, rfl⟩, u, hu, h⟩
    exact ⟨r, hr, s + u, ⟨s, hs, u, hu, rfl⟩, by linarith⟩
  · rintro ⟨r, hr, t, ⟨s, hs, u, hu, rfl⟩, h⟩
    exact ⟨r + s, ⟨r, hr, s, hs, rfl⟩, u, hu, by linarith⟩

/-- A4: the new zero is `Iic 0`, and is a two-sided identity. -/
theorem exercise20_zero (a : Exercise20Cut) :
    (0 : Exercise20Cut).carrier = Set.Iic 0 ∧ 0 + a = a ∧ a + 0 = a := by
  have hr : a + 0 = a := by
    apply Exercise20Cut.ext
    ext q
    constructor
    · rintro ⟨r, hr, s, hs, rfl⟩
      exact a.lower (by change s ≤ 0 at hs; linarith) hr
    · intro hq
      exact ⟨q, hq, 0, (show (0 : ℚ) ≤ 0 from le_rfl), add_zero q⟩
  exact ⟨rfl, (exercise20_addition_commutative 0 a).trans hr, hr⟩

/-- Greatest elements really are allowed: the new zero has greatest element zero. -/
theorem exercise20_zero_has_greatest : IsGreatest (0 : Exercise20Cut).carrier 0 :=
  ⟨(show (0 : ℚ) ≤ 0 from le_rfl), fun _ h => h⟩

/-- A5 fails for the strict negative cut, relative to the new zero. -/
theorem exercise20_inverse_failure :
    Exercise20Cut.strictZero.carrier = Set.Iio 0 ∧
      ¬ ∃ b : Exercise20Cut, Exercise20Cut.strictZero + b = 0 := by
  refine ⟨rfl, ?_⟩
  rintro ⟨b, hb⟩
  have hz : (0 : ℚ) ∈ Exercise20Cut.strictZero + b := by
    rw [hb]
    exact (show (0 : ℚ) ≤ 0 from le_rfl)
  obtain ⟨r, hr, s, hs, hrs⟩ := (exercise20_mem_add _ _ _).mp hz
  change r < 0 at hr
  have hhalf : r / 2 + s ∈ Exercise20Cut.strictZero + b :=
    ⟨r / 2, by change r / 2 < 0; linarith, s, hs, rfl⟩
  rw [hb] at hhalf
  change r / 2 + s ≤ 0 at hhalf
  linarith

/-- Explicit negation of the universal inverse axiom. -/
theorem exercise20_not_A5 :
    ¬ ∀ a : Exercise20Cut, ∃ b : Exercise20Cut, a + b = 0 := by
  intro h
  exact exercise20_inverse_failure.2 (h Exercise20Cut.strictZero)

end Rudin.Chapter01
