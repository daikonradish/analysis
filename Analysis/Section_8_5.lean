import Mathlib.Tactic
import Analysis.Section_8_4

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.5: Ordered sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of {name}`PartialOrder`, {name}`LinearOrder`, and {name}`WellFoundedLT`, with some API.
- Strong induction.
- Zorn's lemma.

-/

namespace Chapter8

/-- Definition 8.5.1 - Here we just review the Mathlib {name}`PartialOrder` class. -/

example {X:Type} [PartialOrder X] (x:X) : x ≤ x := le_refl x
example {X:Type} [PartialOrder X] {x y:X} (h₁: x ≤ y) (h₂: y ≤ x) : x = y := antisymm h₁ h₂
example {X:Type} [PartialOrder X] {x y z:X} (h₁: x ≤ y) (h₂: y ≤ z) : x ≤ z := le_trans h₁ h₂
example {X:Type} [PartialOrder X] (x y:X) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

@[implicit_reducible] def PartialOrder.mk {X:Type} [LE X]
  (hrefl: ∀ x:X, x ≤ x)
  (hantisymm: ∀ x y:X, x ≤ y → y ≤ x → x = y)
  (htrans: ∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) : PartialOrder X :=
{
  le := (· ≤ ·)
  le_refl := hrefl
  le_antisymm := hantisymm
  le_trans := htrans
}

example {X:Type} : PartialOrder (Set X) := by infer_instance
example {X:Type} (A B: Set X) : A ≤ B ↔ A ⊆ B := by rfl

/-- Definition 8.5.3.  Here we just review the Mathlib {name}`LinearOrder` class. -/
example {X:Type} [LinearOrder X] : PartialOrder X := by infer_instance
def IsTotal (X:Type) [PartialOrder X] : Prop := ∀ x y:X, x ≤ y ∨ y ≤ x
example {X:Type} [LinearOrder X] : IsTotal X := le_total

open Classical in
@[implicit_reducible] noncomputable def LinearOrder.mk {X:Type} [PartialOrder X]
  (htotal: IsTotal X) : LinearOrder X :=
{
   le_total := htotal
   toDecidableLE := decRel LE.le
}

/- Examples 8.5.4 -/
#check (inferInstance : LinearOrder ℕ)
#check (inferInstance : LinearOrder ℚ)
#check (inferInstance : LinearOrder ℝ)
#check (inferInstance : LinearOrder EReal)


@[implicit_reducible] noncomputable def LinearOrder.subtype {X:Type} [LinearOrder X] (A: Set X) : LinearOrder A :=
LinearOrder.mk (by
  intro a b
  exact le_total a b
  )

theorem IsTotal.subtype {X:Type} [PartialOrder X] {A: Set X} (hA: IsTotal X) : IsTotal A := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA x y; simp_all

theorem IsTotal.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) (hAB: B ⊆ A) : IsTotal B := by
  intro ⟨ x, hx ⟩ ⟨ y, hy ⟩
  specialize hA ⟨ x, hAB hx ⟩ ⟨ y, hAB hy ⟩; simp_all

abbrev X_8_5_4 : Set (Set ℕ) := { {1,2}, {2}, {2,3}, {2,3,4}, {5} }
example : ¬ IsTotal X_8_5_4 := by
  unfold IsTotal
  push_neg
  use ⟨{2}, by simp⟩
  use ⟨{5}, by simp⟩
  constructor <;> simp

/-- Definition 8.5.5 (Maximal and minimal elements).  Here we use Mathlib's {name}`IsMax` and {name}`IsMin`. -/
theorem IsMax.iff {X:Type} [PartialOrder X] (x:X) :
  IsMax x ↔ ¬ ∃ y, x < y := by rw [isMax_iff_forall_not_lt]; grind

theorem IsMin.iff {X:Type} [PartialOrder X] (x:X) :
  IsMin x ↔ ¬ ∃ y, x > y := by rw [isMin_iff_forall_not_lt]; grind

/-- Examples 8.5.6 -/
example : IsMin (⟨ {2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMin.iff]
  push_neg
  intro ⟨x, hx⟩ hgt
  cases hx <;> simp_all <;> grind
example : IsMax (⟨ {1,2}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]
  push_neg
  intro ⟨x, hx⟩ hlt
  cases hx <;> simp_all [Set.ssubset_def, Set.subset_def]
  grind
example : IsMax (⟨ {2,3,4}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMax.iff]
  push_neg
  intro ⟨x, hx⟩ hlt
  cases hx <;> simp_all [Set.ssubset_def, Set.subset_def]
  grind
example : IsMin (⟨ {5}, by aesop ⟩ : X_8_5_4) ∧ IsMax (⟨ {5}, by aesop ⟩ : X_8_5_4) := by
  rw [IsMin.iff, IsMax.iff]
  constructor
  · push_neg
    intro ⟨x, hx⟩ hgt
    simp_all
    cases hx <;> grind
  · push_neg
    intro ⟨x, hx⟩ hlt
    simp_all
    cases hx <;> grind


example : ¬ IsMin (⟨ {2,3}, by aesop ⟩ : X_8_5_4) ∧ ¬ IsMax (⟨ {2,3}, by aesop ⟩ : X_8_5_4) := by
  constructor
  · rw [IsMin.iff]
    push_neg
    use ⟨{2}, by simp⟩
    simp
    constructor <;> simp
  · rw [IsMax.iff]
    push_neg
    use ⟨{2, 3, 4}, by simp⟩
    simp
    constructor <;> simp

/-- Example 8.5.7 -/
example : IsMin (0:ℕ) := by
  rw [IsMin.iff]
  push_neg
  intro y
  simp
example (n:ℕ) : ¬ IsMax n := by
  rw [IsMax.iff]
  push_neg
  by_contra! h
  specialize h (n+1)
  simp at h
example (n:ℤ): ¬ IsMin n ∧ ¬ IsMax n := by
  constructor
  · rw [IsMin.iff]
    push_neg
    by_contra! h
    specialize h (n - 1)
    simp at h
  · rw [IsMax.iff]
    push_neg
    by_contra! h
    specialize h (n + 1)
    simp at h

/-- Definition 8.5.8.  We use `[LinearOrder X] [WellFoundedLT X]` to describe well-ordered sets. -/
theorem WellFoundedLT.iff (X:Type) [LinearOrder X] :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := by
  unfold WellFoundedLT IsMin
  rw [isWellFounded_iff, WellFounded.wellFounded_iff_has_min]
  peel with A hA; constructor
  . intro ⟨ x, hxA, h ⟩; use ⟨ x, hxA ⟩; intro ⟨ y, hy ⟩ this; specialize h y hy
    simp at *; order
  intro ⟨ ⟨ x, hx ⟩, h ⟩; refine ⟨ _, hx, ?_ ⟩; intro y hy; specialize h (b := ⟨ _, hy ⟩)
  simp at h; contrapose! h; simp [h]; order

theorem WellFoundedLT.iff' {X:Type} [PartialOrder X] (h: IsTotal X) :
  WellFoundedLT X ↔ ∀ A:Set X, A.Nonempty → ∃ x:A, IsMin x := @iff X (LinearOrder.mk h)

/-- Example 8.5.9 -/
example : WellFoundedLT ℕ := by
  rw [WellFoundedLT.iff]
  intro A hA; use ⟨ _, (Nat.min_spec hA).1 ⟩
  simp [IsMin]; grind [Nat.min_spec]

/-- Exercise 8.1.2 -/
example : ¬ WellFoundedLT ℤ := by
  rw [WellFoundedLT.iff]
  push_neg
  use Set.univ
  simp
  intro a; use a - 1; simp

example : ¬ WellFoundedLT ℚ := by
  rw [WellFoundedLT.iff]
  push_neg
  use Set.univ
  simp
  intro a; use a - 1; simp

example : ¬ WellFoundedLT ℝ := by
  rw [WellFoundedLT.iff]
  push_neg
  use Set.univ
  simp
  intro a; use a - 1; simp

/-- Exercise 8.5.8 -/
lemma Finset.has_max {X : Type} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert x S ha ih =>
      by_cases hne : S.Nonempty
      · choose m hmS hmmax using ih hne
        by_cases hxm : x ≤ m
        · use m
          constructor
          · simp; right; exact hmS
          · intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with rfl | hs
            · exact hxm
            · exact hmmax y hs
        · push_neg at hxm
          use x
          constructor
          · simp
          · intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with rfl | hs
            · simp
            · specialize hmmax y hs
              grind
      · push_neg at hne
        use x
        simp
        grind

theorem IsMax.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMax x := by
  haveI : Fintype X := Fintype.ofFinite X
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  obtain ⟨x, _, hx⟩ := Finset.has_max (Finset.univ : Finset X) hne
  use x
  rw [IsMax.iff]
  push_neg
  intro y
  exact hx y (by simp)

lemma Finset.has_min {X : Type} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert x S ha ih =>
      by_cases hne : S.Nonempty
      · choose m hmS hmmax using ih hne
        by_cases hxm : m ≤ x
        · use m
          constructor
          · simp; right; exact hmS
          · intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with rfl | hs
            · exact hxm
            · exact hmmax y hs
        · push_neg at hxm
          use x
          constructor
          · simp
          · intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with rfl | hs
            · simp
            · specialize hmmax y hs
              grind
      · push_neg at hne
        use x
        simp
        grind

theorem IsMin.ofFinite {X:Type} [LinearOrder X] [Finite X] [Nonempty X] : ∃ x:X, IsMin x := by
  haveI : Fintype X := Fintype.ofFinite X
  have hne : (Finset.univ : Finset X).Nonempty := Finset.univ_nonempty
  obtain ⟨x, _, hx⟩ := Finset.has_min (Finset.univ : Finset X) hne
  use x
  rw [IsMin.iff]
  push_neg
  intro y
  exact hx y (by simp)


/-- Exercise 8.5.8 -/
theorem WellFoundedLT.ofFinite {X:Type} [LinearOrder X] [Finite X] : WellFoundedLT X := by
  rw [WellFoundedLT.iff]
  intro A hA
  have : Nonempty A := by exact Set.Nonempty.to_subtype hA
  apply IsMin.ofFinite


example {X:Type} [LinearOrder X] [WellFoundedLT X] (A: Set X) : WellFoundedLT A := by
  rw [WellFoundedLT.iff]
  intro B hB
  -- apply WellFounded to the image of B in X
  have hwf := (WellFoundedLT.iff X).mp ‹_› (Subtype.val '' B) (by aesop)
  obtain ⟨⟨x, hxB⟩, hmin⟩ := hwf
  simp at hxB
  obtain ⟨hxA, hxB'⟩ := hxB
  use ⟨⟨x, hxA⟩, hxB'⟩
  -- show it is minimal
  intro ⟨⟨y, hyA⟩, hyB⟩ hle
  apply hmin (b := ⟨y, (by simp; exact ⟨hyA, hyB⟩)⟩) hle


theorem WellFoundedLT.subset {X:Type} [PartialOrder X] {A B: Set X} (hA: IsTotal A) [hwell: WellFoundedLT A] (hAB: B ⊆ A) : WellFoundedLT B := by
  set hAlin : LinearOrder A := LinearOrder.mk hA
  set hBlin : LinearOrder B := LinearOrder.mk (hA.subset hAB)
  rw [iff' hA] at hwell; rw [iff' (hA.subset hAB)]; intro C hC
  have ⟨ ⟨ ⟨ x, hx ⟩, hx' ⟩, hmin ⟩ := hwell ((B.embeddingOfSubset _ hAB) '' C) (by aesop)
  simp at hx'; choose y hy hyC this using hx'; use ⟨ _, hyC ⟩
  simp_all [IsMin, Set.embeddingOfSubset]
  intro a ha_B ha_C
  apply hmin _ (hAB ha_B) <;> trivial

/-- Proposition 8.5.10 / Exercise 8.5.10 -/
theorem WellFoundedLT.strong_induction {X:Type} [LinearOrder X] [WellFoundedLT X] {P:X → Prop}
  (h: ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  intro n
  let Y := {m : X | ∃ k ≤ m, ¬(P k)}
  suffices hempty : Y = ∅ by
    unfold Y at hempty
    by_contra! hnotP
    contrapose hempty
    push_neg
    use n
    simp
    use n
  by_contra! hnonempty
  have hhasmin := (WellFoundedLT.iff X).mp (inferInstance)
  -- Y is a subset of a well-ordered set, so choose its minimum kmin
  choose kmin hmin using hhasmin _ hnonempty
  choose k₀ hle hnotPk₀ using kmin.property
  rcases hle.eq_or_lt with heq | hlt
  · -- show that kmin couldn't have been in Y,
    -- because the proposition P holds for kmin
    have hall : ∀ j < kmin.val, P j := by
      intro j hj
      by_contra hPj
      have hjY : j ∈ Y := by
        unfold Y
        simp
        use j
      contrapose hmin
      unfold IsMin; push_neg
      use ⟨j, hjY⟩
      constructor
      · exact le_of_lt hj
      · exact hj
    have := h kmin hall
    rw [heq] at hnotPk₀
    exact absurd this hnotPk₀
  · -- Show that kmin couldn't have been the minimum,
    -- because there's an element that's smaller than k in Y.
    have hin : k₀ ∈ Y := by
      unfold Y
      simp
      use k₀
    have hnotmin : ¬ (IsMin kmin) := by
      unfold IsMin
      push_neg
      use ⟨k₀, by exact hin⟩
      constructor
      · exact hle
      · exact hlt
    exact absurd hmin hnotmin

/-- Definition 8.5.12 (Upper bounds and strict upper bounds) -/
abbrev IsUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  ∀ y ∈ A, y ≤ x

/-- Connection with Mathlib's {name}`upperBounds` -/
theorem IsUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsUpperBound A x ↔ x ∈ upperBounds A := by simp [IsUpperBound, upperBounds]

abbrev IsStrictUpperBound {X:Type} [PartialOrder X] (A:Set X) (x:X) : Prop :=
  IsUpperBound A x ∧ x ∉ A

theorem IsStrictUpperBound.iff {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ ∀ y ∈ A, y < x := by
  unfold IsStrictUpperBound IsUpperBound
  constructor
  · intro ⟨hupper, hnotA⟩ y hA
    specialize hupper y hA
    rcases hupper.lt_or_eq with hlt | heq
    · exact hlt
    · rw [heq] at hA
      exact absurd hA hnotA
  · intro hltx
    constructor
    · intro a hA
      specialize hltx a hA
      exact le_of_lt hltx
    · by_contra hin
      specialize hltx x hin
      exact (lt_self_iff_false x).mp hltx

theorem IsStrictUpperBound.iff' {X:Type} [PartialOrder X] (A:Set X) (x:X) :
  IsStrictUpperBound A x ↔ x ∈ upperBounds A \ A := by
  simp [IsStrictUpperBound, IsUpperBound.iff]

example : IsUpperBound (.Icc 1 2: Set ℝ) 2 := by
  intro h hy
  simp at hy
  exact hy.2

example : ¬ IsStrictUpperBound (.Icc 1 2: Set ℝ) 2 := by
  unfold IsStrictUpperBound
  push_neg
  intro x
  simp

example : IsStrictUpperBound (.Icc 1 2: Set ℝ) 3 := by
  constructor
  · intro y hy; simp at hy; linarith
  · simp; norm_num

/-- A convenient way to simplify the notion of having {name}`x₀` as a minimal element.-/
theorem IsMin.iff_lowerbound {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) (x₀ : X) : (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩:Y)) ↔ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . rintro ⟨ hx₀, hmin ⟩; simp [IsMin, hx₀] at *
    peel hmin with x hx _; specialize hY ⟨ _, hx ⟩ ⟨ _, hx₀ ⟩; aesop
  intro h; use h.1; simp [IsMin]; aesop

theorem IsMin.iff_lowerbound' {X:Type} [PartialOrder X] {Y: Set X} (hY: IsTotal Y) : (∃ x₀ : Y, IsMin x₀) ↔ ∃ x₀, x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x := by
  constructor
  . intro ⟨ ⟨ x₀, hx₀ ⟩, hmin ⟩
    have : ∃ (hx₀ : x₀ ∈ Y), IsMin (⟨ _, hx₀ ⟩:Y) := by use hx₀
    rw [iff_lowerbound hY x₀] at this; use x₀
  intro ⟨ x₀, hx₀, hmin ⟩; choose hx₀ _ using (iff_lowerbound hY x₀).mpr ⟨ hx₀, hmin ⟩; use ⟨ _, hx₀ ⟩

/-- Exercise 8.5.11 -/
example {X:Type} [PartialOrder X] {Y Y':Set X} (hY: IsTotal Y) (hY': IsTotal Y') (hY_well: WellFoundedLT Y) (hY'_well: WellFoundedLT Y') (hYY': IsTotal (Y ∪ Y': Set X)) : WellFoundedLT (Y ∪ Y': Set X) := by
  rw [WellFoundedLT.iff' hYY']
  intro A hAnonempty
  let Yrestrict : Set Y := { y | ∃ a ∈ A, (a : X) = (y : X) }
  let Y'restrict : Set Y' := { y' | ∃ a ∈ A, (a : X) = (y' : X)}
  have hcover : Yrestrict.Nonempty ∨ Y'restrict.Nonempty := by
    choose a ha using hAnonempty
    rcases a.property with hinY | hinY'
    · left; use ⟨a, hinY⟩
      unfold Yrestrict
      simp; exact ha
    · right; use ⟨a, hinY'⟩
      unfold Y'restrict
      simp; exact ha
  rw [WellFoundedLT.iff' hY] at hY_well
  rw [WellFoundedLT.iff' hY'] at hY'_well
  by_cases! hYnon : Yrestrict.Nonempty <;> by_cases! hY'non : Y'restrict.Nonempty
  · specialize hY_well Yrestrict hYnon
    choose y hymin using hY_well
    specialize hY'_well Y'restrict hY'non
    choose y' hy'min using hY'_well
    rcases hYY' ⟨y, by simp⟩ ⟨y', by simp⟩ with h1 | h2
    · obtain ⟨a, haA, hav⟩ := y.property
      use ⟨⟨y, by simp⟩, by grind⟩
      rw [IsMin.iff] at hymin hy'min ⊢
      push_neg at hymin hy'min ⊢
      intro z hz
      obtain ⟨⟨z', hz'⟩, hz'A⟩ := z
      rcases hz' with hzinY | hzinY'
      · have hmemY : ⟨z', hzinY⟩ ∈ Yrestrict := by
          unfold Yrestrict
          simp
          exact hz'A
        specialize hymin ⟨⟨z', hzinY⟩, hmemY⟩
        exact hymin hz
      · have hmemY' : ⟨z', hzinY'⟩ ∈ Y'restrict := by
          unfold Y'restrict
          simp
          exact hz'A
        specialize hy'min ⟨⟨z', hzinY'⟩, hmemY'⟩
        -- unfold everything back up to X
        have hz_X     : z' < (y : X)    := hz
        have h1_X     : (y : X) ≤ y'    := h1
        have hy'min_X : ¬ z' < (y' : X) := hy'min
        order
    · obtain ⟨a, haA, hav⟩ := y'.property
      use ⟨⟨y', by simp⟩, by grind⟩
      rw [IsMin.iff] at hymin hy'min ⊢
      push_neg at hymin hy'min ⊢
      intro z hz
      obtain ⟨⟨z', hz'⟩, hz'A⟩ := z
      rcases hz' with hzinY | hzinY'
      · have hmemY : ⟨z', hzinY⟩ ∈ Yrestrict := by
          unfold Yrestrict
          simp
          exact hz'A
        specialize hymin ⟨⟨z', hzinY⟩, hmemY⟩
        have hz_X     : z' < (y' : X)    := hz
        have h1_X     : (y' : X) ≤ y     := h2
        have hy'min_X : ¬ z' < (y : X)  := hymin
        order
      · have hmemY' : ⟨z', hzinY'⟩ ∈ Y'restrict := by
          unfold Y'restrict
          simp
          exact hz'A
        specialize hy'min ⟨⟨z', hzinY'⟩, hmemY'⟩
        exact hy'min hz
  · specialize hY_well Yrestrict hYnon
    choose y hymin using hY_well
    have hy := y.property
    unfold Yrestrict at hy
    choose a ha hayy using hy
    use ⟨⟨y, by rw [← hayy]; exact a.property⟩, by grind⟩
    rw [IsMin.iff] at hymin ⊢
    push_neg at hymin ⊢
    intro z hz
    obtain ⟨⟨z', hz'⟩, hz'A⟩ := z
    have hzinY : z' ∈ Y := by
      rcases hz' with hinY | hinY'
      · exact hinY
      · have : Y'restrict.Nonempty := by
          use ⟨z', hinY'⟩
          unfold Y'restrict
          simp
          exact hz'A
        exact absurd this (by exact Set.not_nonempty_iff_eq_empty.mpr hY'non)
    have hmemY : ⟨z', hzinY⟩ ∈ Yrestrict := by
      unfold Yrestrict
      simp
      exact hz'A
    specialize hymin ⟨⟨z', hzinY⟩, hmemY⟩
    exact hymin hz
  · specialize hY'_well Y'restrict hY'non
    choose y hymin using hY'_well
    have hy := y.property
    unfold Y'restrict at hy
    choose a ha hayy using hy
    use ⟨⟨y, by rw [← hayy]; exact a.property⟩, by grind⟩
    rw [IsMin.iff] at hymin ⊢
    push_neg at hymin ⊢
    intro z hz
    obtain ⟨⟨z', hz'⟩, hz'A⟩ := z
    have hzinY' : z' ∈ Y' := by
      rcases hz' with hinY | hinY'
      · have : Yrestrict.Nonempty := by
          use ⟨z', hinY⟩
          unfold Yrestrict
          simp
          exact hz'A
        exact absurd this (by exact Set.not_nonempty_iff_eq_empty.mpr hYnon)
      · exact hinY'
    have hmemY' : ⟨z', hzinY'⟩ ∈ Y'restrict := by
      unfold Y'restrict
      simp
      exact hz'A
    specialize hymin ⟨⟨z', hzinY'⟩, hmemY'⟩
    exact hymin hz
  · have : ¬ (Yrestrict.Nonempty ∨ Y'restrict.Nonempty) := by
      push_neg; constructor
      · exact hYnon
      · exact hY'non
    exact absurd hcover this


/-- Lemma 8.5.14-/
theorem WellFoundedLT.partialOrder {X:Type} [PartialOrder X] (x₀ : X) :
  ∃ Y : Set X, IsTotal Y ∧
  WellFoundedLT Y        ∧
  (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩: Y))
  ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
  -- This proof is based on the original text with some technical simplifications.

  -- The class of well-ordered subsets `Y` of `X` that contain `x₀` as a minimal element is not named in the text,
  -- but it is convenient to give it a name (`Ω₀`) for the formalization.  Here we use `IsMin.iff_lowerbound` to
  -- simplify the notion of minimality.
  let Ω₀ := { Y : Set X | IsTotal Y ∧ WellFoundedLT Y ∧ x₀ ∈ Y ∧ ∀ x ∈ Y, x₀ ≤ x}
  suffices : ∃ Y ∈ Ω₀, ¬ ∃ x, IsStrictUpperBound Y x
  . have ⟨ Y, ⟨ hY, hY'⟩, hstrict ⟩ := this; use Y, hY
    rw [IsMin.iff_lowerbound hY x₀]; tauto
  by_contra! hs
  let s : Ω₀ → X := fun Y ↦ (hs Y Y.property).choose
  replace hs (Y:Ω₀) : IsStrictUpperBound Y (s Y) := (hs Y Y.property).choose_spec

  have hpt: {x₀} ∈ Ω₀ := by
    have htotal : IsTotal ({x₀}: Set X) := by simp [IsTotal]
    let _lin : LinearOrder ({x₀}: Set X) := LinearOrder.mk htotal
    simp [Ω₀, htotal]; apply WellFoundedLT.ofFinite
  let pt : Ω₀ := ⟨ _, hpt ⟩

  -- The operation of sending a set `Y` in `Ω₀` to the smaller set `{y ∈ Y.val | y < x}`, which is also
  -- in `Ω₀` if `x ∈ Y.val \ {x₀}`, is not named explicitly in the text, but we give it a name `F` for
  -- the formalization.
  have hF {Y:Set X} (hY: Y ∈ Ω₀) {x:X} (hxy : x ∈ Y \ {x₀}) : {y ∈ Y | y < x} ∈ Ω₀ := by
    simp [Ω₀, IsTotal] at hY ⊢; choose _ hmin using hY.2.2; simp_all
    split_ands
    . convert WellFoundedLT.subset (hwell := hY.2) (B := {y ∈ Y | y < x}) _ _
      . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩; simp; solve_by_elim [hY.1]
      intro _; simp; tauto
    have := hmin _ hxy.1; contrapose! hxy; order
  classical
  let F : Ω₀ → X → Ω₀ := fun Y x ↦ if hxy : x ∈ Y.val \ {x₀} then ⟨ {y ∈ (Y:Set X) | y < x}, hF Y.property hxy ⟩ else pt
  replace hF {Y : Ω₀} {x : X} (hxy : x ∈ (Y:Set X) \ {x₀}) : F Y x = { y ∈ (Y:Set X) | y < x } := by
    simp_all [F]

  -- The set `Ω` captures the notion of a `good set`.
  set Ω := { Y : Ω₀ | ∀ x ∈ (Y:Set X) \ {x₀}, x = s (F Y x) }
  have hΩ : pt ∈ Ω := by
    unfold Ω
    simp
    intro x hx hnot
    unfold pt at hx
    simp at hx
    contradiction

  -- Exercise 8.5.13
  have ex_8_5_13 {Y Y':Ω} (x:X) (h: x ∈ (Y':Set X) \ Y) : IsStrictUpperBound Y x := by
    rw [IsStrictUpperBound.iff]                    -- ⊢ ∀ y ∈ (Y:Set X), y < x
    have goodY  : ∀ z ∈ (Y :Set X) \ {x₀}, z = s (F Y.val  z) := Y.property
    have goodY' : ∀ z ∈ (Y':Set X) \ {x₀}, z = s (F Y'.val z) := Y'.property
    choose hYtotal hYwell hYx₀ hYmin using Y.val.property
    choose hY'total hY'well hY'x₀ hY'min using Y'.val.property
    set J : Set X :=
      { z | z ∈ (Y:Set X) ∧ z ∈ (Y':Set X) ∧
            {y ∈ (Y:Set X) | y < z} = {y' ∈ (Y':Set X) | y' < z} } with hJdef
    have hJx₀  : x₀ ∈ J := by
      unfold J; simp
      constructor
      · tauto
      · constructor
        · tauto
        · ext z
          simp; intro hz
          apply iff_of_false
          · intro hzY
            specialize hYmin z hzY
            order
          · intro hzY'
            specialize hY'min z hzY'
            order

    have hdownY  : ∀ a ∈ J, ∀ c ∈ (Y :Set X), c < a → c ∈ J := by
      intro j hJ c hY hcltj
      unfold J at hJ ⊢; simp at hJ ⊢
      obtain ⟨hjY, hjY', hjseg⟩ := hJ
      constructor
      · constructor
        · exact hY
        · have : c ∈ {y ∈ (Y:Set X) | y < j} := by tauto
          rw [hjseg] at this; simp at this
          tauto
      · constructor
        · exact hY
        · ext z; simp
          intro hzlt
          constructor
          · intro hzY
            have : z ∈ {y ∈ (Y:Set X) | y < j} := by
              constructor
              · exact hzY
              · order
            rw [hjseg] at this
            exact this.1
          · intro hzY'
            have : z ∈ {y ∈ (Y':Set X) | y < j} := by
              constructor
              · exact hzY'
              · order
            rw [← hjseg] at this
            exact this.1
    have hdownY' : ∀ a ∈ J, ∀ c ∈ (Y':Set X), c < a → c ∈ J := by
      intro j hJ c hY' hcltj
      unfold J at hJ ⊢; simp at hJ ⊢
      obtain ⟨hjY, hjY', hjseg⟩ := hJ
      constructor
      · constructor
        · have : c ∈ {y ∈ (Y':Set X) | y < j} := by tauto
          rw [← hjseg] at this; simp at this
          tauto
        · exact hY'
      · constructor
        · have : c ∈ {y ∈ (Y':Set X) | y < j} := by tauto
          rw [← hjseg] at this; simp at this
          tauto
        · ext z; simp
          intro hzlt
          constructor
          · intro hzY
            have : z ∈ {y ∈ (Y:Set X) | y < j} := by
              constructor
              · exact hzY
              · order
            rw [hjseg] at this
            exact this.1
          · intro hzY'
            have : z ∈ {y ∈ (Y':Set X) | y < j} := by
              constructor
              · exact hzY'
              · order
            rw [← hjseg] at this
            exact this.1
    have hJsubY  : J ⊆ (Y :Set X) := by
      intro z hz
      unfold J at hz
      simp at hz; tauto
    have hJsubY' : J ⊆ (Y':Set X) := by
      intro z hz
      unfold J at hz
      simp at hz; tauto
    have minOfDiff : ∀ (Z : Ω₀), ((Z:Set X) \ J).Nonempty →
      ∃ m, m ∈ (Z:Set X) ∧ m ∉ J ∧ ∀ z ∈ (Z:Set X), z ∉ J → m ≤ z := by
      intro Z hne
      obtain ⟨htot, hwf, _, _⟩ := Z.property
      set _lin : LinearOrder (Z:Set X) := LinearOrder.mk htot
      set S : Set (Z:Set X) := { y | (y:X) ∉ J } with hS
      have hSne : S.Nonempty := by
        obtain ⟨m, hmZ, hmJ⟩ := hne
        exact ⟨⟨m, hmZ⟩, hmJ⟩
      obtain ⟨⟨m, hmS⟩, hmin⟩ := (WellFoundedLT.iff (Z:Set X)).mp hwf S hSne
      refine ⟨(m:X), m.2, hmS, ?_⟩
      intro z hzZ hzJ
      have hzS : (⟨z, hzZ⟩ : (Z:Set X)) ∈ S := hzJ
      have key : m ≤ (⟨z, hzZ⟩ : (Z:Set X)) := by
        rcases le_total (⟨z, hzZ⟩ : (Z:Set X)) m with h' | h'
        · have hms : (⟨m, hmS⟩ : S) ≤ ⟨⟨z, hzZ⟩, hzS⟩ := hmin (by exact_mod_cast h')
          exact_mod_cast hms
        · exact h'
      exact_mod_cast key
    have segOfMin : ∀ (Z : Ω₀),
    J ⊆ (Z:Set X) →
    (∀ b ∈ J, ∀ c ∈ (Z:Set X), c < b → c ∈ J) →
    ∀ {m}, (m ∈ (Z:Set X) ∧ m ∉ J ∧ ∀ z ∈ (Z:Set X), z ∉ J → m ≤ z) →
    J = {z ∈ (Z:Set X) | z < m} := by
      intro Z hsub hdown m hm
      obtain ⟨hmZ, hmJ, hmin⟩ := hm
      obtain ⟨htot, _, _, _⟩ := Z.property
      set _lin : LinearOrder (Z:Set X) := LinearOrder.mk htot
      ext z
      simp only [Set.mem_setOf_eq]
      constructor
      · -- z ∈ J  ⟹  z ∈ Z ∧ z < m
        intro hzJ
        have hzZ : z ∈ (Z:Set X) := hsub hzJ
        refine ⟨hzZ, ?_⟩
        have hne : z ≠ m := fun he => hmJ (he ▸ hzJ)
        have hcmp : z ≤ m ∨ m ≤ z := by
          have h := le_total (⟨z, hzZ⟩ : (Z:Set X)) ⟨m, hmZ⟩
          exact_mod_cast h
        rcases hcmp with hle | hle
        · exact lt_of_le_of_ne hle hne
        · exact absurd (hdown z hzJ m hmZ (lt_of_le_of_ne hle (Ne.symm hne))) hmJ
      · -- z ∈ Z ∧ z < m  ⟹  z ∈ J
        rintro ⟨hzZ, hzlt⟩
        by_contra hzJ
        have := hmin z hzZ hzJ        -- m ≤ z
        order
    -- core: J = Y as sets (rules out J = Y' via x, kills the J⊊Y ∧ J⊊Y' case via s-collision)
    have hJY : J = (Y:Set X) := by
      by_contra! hne
      have hdYnonemp : ((Y :Set X) \ J).Nonempty := by
        by_contra! h'
        apply hne
        apply Set.Subset.antisymm hJsubY
        apply Set.diff_eq_empty.mp
        exact h'
      have hxnotJ : x ∉ J := by
        intro h'
        have := hJsubY h'
        exact h.2 this
      have hdY'nonemp : ((Y':Set X) \ J).Nonempty := by
        use x
        exact ⟨h.1, hxnotJ⟩
      obtain ⟨a,  haY,  haJ,  hamin ⟩ := minOfDiff Y  hdYnonemp
      obtain ⟨a', ha'Y', ha'J, ha'min⟩ := minOfDiff Y' hdY'nonemp
      have segY  : J = {z ∈ (Y :Set X) | z < a } := segOfMin Y  hJsubY  hdownY  ⟨haY,  haJ,  hamin⟩
      have segY' : J = {z ∈ (Y':Set X) | z < a'} := segOfMin Y' hJsubY' hdownY' ⟨ha'Y', ha'J, ha'min⟩
      have ha_ne  : a ≠ x₀ := by
        intro h
        rw [h] at haJ
        tauto
      have ha'_ne : a' ≠ x₀ := by
        intro h
        rw [h] at ha'J
        tauto
      have haa' : a = a' := by
        have hFeq : F Y.val a = F Y'.val a' := by
          apply Subtype.ext                       -- reduce to equality of the underlying sets
          rw [hF ⟨haY, ha_ne⟩, ← segY]
          rw [hF ⟨ha'Y', ha'_ne⟩, ← segY']
        calc a = s (F Y.val a)   := by exact goodY a ⟨haY,  ha_ne⟩
             _ = s (F Y'.val a') := by rw [hFeq]
             _ = a'              := by exact (goodY' a' ⟨ha'Y',  ha'_ne⟩).symm
      apply haJ
      unfold J
      refine ⟨haY, ?_, ?_⟩
      · rwa [← haa'] at ha'Y'
      · rw [← segY, haa', ← segY']
    -- least element of Y' \ J  (nonempty: x lives there); least via has_min + totality
    obtain ⟨a', ha'mem, ha'least⟩ :
        ∃ a', a' ∈ (Y':Set X) \ J ∧ ∀ z ∈ (Y':Set X) \ J, a' ≤ z := by
      have : ((Y':Set X) \ J).Nonempty := by
        use x
        constructor
        · exact h.1
        · rw [hJY]; exact h.2
      obtain ⟨a', ha'Y', ha'J, ha'min⟩ := minOfDiff Y'.val this
      use a'
      constructor
      · tauto
      · intro z hz
        specialize ha'min z hz.1 hz.2
        exact ha'min
    -- J = {y' ∈ Y' | y' < a'}, i.e. Y = that initial segment
    have hseg : (Y:Set X) = {y' ∈ (Y':Set X) | y' < a'} := by
      have := segOfMin Y'.val hJsubY' hdownY' ⟨ha'mem.1, ha'mem.2, fun z hz hz' => ha'least z ⟨hz, hz'⟩⟩
      rw [← this]
      exact hJY.symm

    -- finish
    intro y hy
    rw [hseg] at hy
    have ha'x : a' ≤ x := ha'least x ⟨h.1, by rw [hJY]; exact h.2⟩
    exact lt_of_lt_of_le hy.2 ha'x

  have : IsTotal Ω := by
    unfold IsTotal; by_contra!; obtain ⟨ ⟨ ⟨ Y, hY1 ⟩, hY2 ⟩, ⟨ ⟨ Y', hY'1⟩, hY'2 ⟩, h1, h2 ⟩ := this
    simp_all [Set.not_subset]
    choose x₁ hx₁ hx₁' using h1; choose x₂ hx₂ hx₂' using h2
    observe h1 : IsStrictUpperBound Y x₂
    observe h2 : IsStrictUpperBound Y' x₁
    simp [IsStrictUpperBound.iff] at h1 h2
    specialize h1 _ hx₁; specialize h2 _ hx₂; order
  set Y_infty : Set X := ⋃ Y:Ω, Y
  have hmem : x₀ ∈ Y_infty := by simp [Y_infty]; use pt; grind
  have hmin {x:X} (hx: x ∈ Y_infty) : x₀ ≤ x := by
    unfold Y_infty at hx
    choose Y hY hxmem using hx
    choose k hk using hY
    simp at hk
    rw [← hk] at hxmem
    choose htotal hwell hx₀ hmin using k.val.property
    specialize hmin x hxmem
    exact hmin
  have htotal : IsTotal Y_infty := by
    intro ⟨ x, hx ⟩ ⟨ x', hx'⟩; simp [Y_infty] at hx hx'
    obtain ⟨ Y, ⟨ hYΩ₀, hYΩ ⟩, hxY ⟩ := hx; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx'
    specialize this ⟨ _, hYΩ ⟩ ⟨ _, hY'Ω ⟩; simp [Ω₀] at this ⊢ hYΩ₀ hY'Ω₀
    obtain this | this := this
    . replace hY'Ω₀ := hY'Ω₀.1 ⟨ _, this hxY ⟩ ⟨ _, hxY' ⟩; simpa using hY'Ω₀
    replace hYΩ₀ := hYΩ₀.1 ⟨ _, hxY ⟩ ⟨ _, this hxY' ⟩; simpa using hYΩ₀
  have hwell : WellFoundedLT Y_infty := by
    rw [iff' htotal]; intro A ⟨ ⟨a, ha⟩, haA ⟩
    simp [Y_infty] at ha; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, haY ⟩ := ha
    simp [Ω₀, iff' hYΩ₀.1] at hYΩ₀
    choose b hb hbY hbmin using hYΩ₀.2.1 {x:Y | ∃ x':A, (x:X) = x'} (by use ⟨ _, haY ⟩; simp [ha, haA])
    simp at hbY; choose hbY_infty hbA using hbY
    rw [IsMin.iff_lowerbound' (IsTotal.subtype htotal)]
    use ⟨ _, hbY_infty ⟩, hbA; intro ⟨ x, hx ⟩ hxA
    simp [Y_infty] at hx ⊢; obtain ⟨ Y', ⟨ hY'Ω₀, hY'Ω ⟩, hxY' ⟩ := hx
    by_cases! hxY : x ∈ Y
    · rcases hYΩ₀.1 ⟨b, hb⟩ ⟨x, hxY⟩ with h | h
      · exact h
      · have hx_in : (⟨x, hxY⟩ : ↑Y) ∈ {p : ↑Y | ∃ x' : A, (p:X) = x'} := ⟨⟨⟨x, hx⟩, hxA⟩, rfl⟩
        have := hbmin (b := ⟨⟨x, hxY⟩, hx_in⟩) h
        exact this
    · have := ex_8_5_13 (Y := ⟨_, hYΩ⟩) (Y' := ⟨_, hY'Ω⟩) x ⟨hxY', hxY⟩
      rw [IsStrictUpperBound.iff] at this
      specialize this b hb
      order
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    unfold Ω₀
    simp; refine ⟨htotal, hwell, hmem, ?_⟩
    intro x hx
    specialize hmin hx
    exact hmin
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hsub : IsStrictUpperBound Y_infty sY_infty := hs ⟨_, hY_inftyΩ₀⟩
  rw [IsStrictUpperBound.iff] at hsub
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp at hx hy
    rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
    · left; rfl
    · right
      apply le_of_lt
      specialize hsub y hy'
      exact hsub
    · left
      apply le_of_lt
      specialize hsub x hx'
      exact hsub
    · exact htotal ⟨x, hx'⟩ ⟨y, hy'⟩
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    rw [WellFoundedLT.iff' hYs_total]
    intro A ⟨⟨a, ha⟩, haA⟩
    by_cases hoverlap : ∃ w ∈ A, (w:X) ∈ Y_infty
    · obtain ⟨w, hwA, hwY⟩ := hoverlap
      --choose x hwZ hwY using hw
      set S : Set Y_infty := { p | (⟨(p:X), Set.mem_union_left _ p.2⟩ : ↑(Y_infty ∪ {sY_infty})) ∈ A } with hS
      -- S is nonempty: w lands in it
      have hSne : S.Nonempty := by
        refine ⟨⟨(w:X), hwY⟩, ?_⟩
        show (⟨(w:X), Set.mem_union_left _ hwY⟩ : ↑(Y_infty ∪ {sY_infty})) ∈ A
        exact hwA
      obtain ⟨⟨m, hmS⟩, hmin⟩ := (WellFoundedLT.iff' htotal).mp hwell S hSne
      refine ⟨⟨⟨(m:X), Set.mem_union_left _ m.2⟩, ?_⟩, ?_⟩
      · exact hmS
      · rw [IsMin.iff] at hmin ⊢
        intro hy
        choose y hygt using hy
        apply hmin
        have hyin : (y:X) ∈ Y_infty := by
          rcases y.1.2 with h | h
          · exact h
          · -- h : (y:X) = sY_infty, derive a contradiction from hygt
            exfalso
            have hlt : (y:X) < (m:X) := by exact_mod_cast hygt
            have hms : (m:X) < sY_infty := hsub _ m.2
            rw [h] at hlt
            order
        use ⟨⟨y, by exact hyin⟩, by unfold S; simp⟩
        exact hygt
    · push_neg at hoverlap
      have : a = sY_infty := by
        simp at ha
        rcases ha with ha1 | ha2
        · exact ha1
        · have : a ∉ Y_infty := by exact hoverlap ⟨_, ha⟩ haA
          exact absurd ha2 this
      use ⟨⟨a, ha⟩, haA⟩
      intro ⟨⟨z, hz⟩, hzA⟩ hzm
      simp at hz
      rcases hz with rfl | hzY
      · simp; rw [this]
      · simp at hzm ⊢
        exact absurd hzY (hoverlap _ hzA)
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := by left; exact hmem
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by
    intro x hx
    rcases hx with hY | hsY
    · exact hmin hY
    · simp at hsY; rw [hsY]
      specialize hsub x₀ hmem
      order
  have hYs_Ω₀ : (Y_infty ∪ {sY_infty}) ∈ Ω₀ := by
    simpa [-Set.union_singleton, Ω₀, hYs_total, hYs_well, hYs_mem]
  specialize hs ⟨ _, hY_inftyΩ₀ ⟩
  simp [IsStrictUpperBound.iff] at hs
  have hYs_Ω : ⟨ _, hYs_Ω₀ ⟩ ∈ Ω := by
    simp [Ω, -Set.mem_insert_iff, -and_imp]
    intro x hx hxx₀
    rcases hx with rfl | hx
    . unfold sY_infty; congr 1
      symm; apply Subtype.val_injective; convert hF _
      . ext; simp; constructor
        . grind
        rintro ⟨ _ | _, _ ⟩
        . order
        assumption
      simp; specialize hs (y := x₀) (by simp [hmem]); order
    have hx' := hx; simp [Y_infty] at hx'; obtain ⟨ Y, ⟨hYΩ₀, hYΩ⟩, hxY ⟩ := hx'
    have hYΩ' := hYΩ; simp [Ω] at hYΩ
    convert hYΩ _ hxY hxx₀ using 2
    apply Subtype.val_injective
    rw [hF, hF]
    . ext y; simp [Y_infty]; intro hyx; constructor
      . rintro (rfl | ⟨ Y', ⟨hY'Ω₀, hY'Ω⟩, hyY' ⟩)
        . specialize hs _ hx; order
        by_contra!
        specialize ex_8_5_13 (Y := ⟨_, hYΩ'⟩) (Y' := ⟨_, hY'Ω⟩) y (by grind)
        rw [IsStrictUpperBound.iff] at ex_8_5_13
        specialize ex_8_5_13 x (by simp [hxY]); order
      grind
    all_goals simp [hxY, hx, hxx₀]
  have hs_mem : sY_infty ∈ Y_infty := Set.mem_iUnion_of_mem ⟨ _, hYs_Ω ⟩ (by simp)
  specialize hs _ hs_mem; order

#check WellFoundedLT.partialOrder
/-- Lemma 8.5.15 (Zorn's lemma) / Exercise 8.5.14 -/
theorem Zorns_lemma {X:Type} [PartialOrder X] [Nonempty X]
  (hchain: ∀ Y:Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨Y, hYtot, _ ,⟨hx₀Y, _⟩, hnotstrict⟩ := WellFoundedLT.partialOrder x₀
  obtain ⟨b, hb⟩ := hchain Y ⟨hYtot, by use x₀⟩
  have hbY : b ∈ Y := by
    by_contra h'
    apply hnotstrict
    use b
  use b
  intro z hblez
  have hzUB : IsUpperBound Y z := by
    intro y hy
    have := hb y hy
    order
  by_cases hzY : z ∈ Y
  · exact hb z hzY
  · have hstrict : ∃ x, IsStrictUpperBound Y x := by
      use z
    exact absurd hstrict hnotstrict

/-- Exercise 8.5.1 -/
def empty_set_partial_order [h₀: LE Empty] : Decidable (∃ h : PartialOrder Empty, h.le = h₀.le) := by
  apply isTrue
  use {
    le               := fun x _ => True
    le_refl          := by
      intro x; simp
    le_antisymm      := by
      intro x y; tauto
    le_trans         := by
      intro a b c; tauto
    lt_iff_le_not_ge := by
      intro a b; simp
  }
  ext x y
  simp
  grind

def empty_set_linear_order [h₀: LE Empty] : Decidable (∃ h : LinearOrder Empty, h.le = h₀.le) := by
  apply isTrue
  use {
    le               := fun x _ => True
    le_refl          := by
      intro x; simp
    le_antisymm      := by
      intro x y; tauto
    le_trans         := by
      intro a b c; tauto
    lt_iff_le_not_ge := by
      intro a b; simp
    le_total := by
      intro a b; tauto
    min_def := by simp
    max_def := by simp
    toDecidableLE := by
      intro x y
      simp; tauto
  }
  ext x y
  simp
  grind

def empty_set_well_order [h₀: LT Empty]: Decidable (Nonempty (WellFoundedLT Empty)) := by
  exact isTrue ⟨⟨⟨fun a ↦ a.elim⟩⟩⟩

/-- Exercise 8.5.2 -/
example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ ¬ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) := by
  use Fin 3
  use ⟨fun a b => a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp
  · intro x y hxy hyx
    grind
  · push_neg
    use 0
    use 1
    use 2
    simp

example : ∃ (X:Type) (h₀: LE X), (∀ x:X, x ≤ x) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x y:X, x ≤ y → y ≤ x → x = y) := by
  use Fin 2
  use ⟨fun _ _ => True⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x; simp
  · intro x y z hxy hyz; simp
  · push_neg
    use 0
    use 1
    simp

example : ∃ (X:Type) (h₀: LE X), (∀ x y:X, x ≤ y → y ≤ x → x = y) ∧ (∀ x y z:X, x ≤ y → y ≤ z → x ≤ z) ∧ ¬ (∀ x:X, x ≤ x) := by
  use Fin 2
  use ⟨fun a b => a < b⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy hyx
    grind
  · intro x y z hxy hyz; simp
    grind
  · push_neg
    use 0
    simp

/-- Exercise 8.5.3: The divisibility ordering on PNat. -/
@[reducible] def PNat.divOrder : PartialOrder PNat where
  le x y := ∃ n : PNat, y = n * x
  lt x y := (∃ n : PNat, y = n * x) ∧ ¬∃ n : PNat, x = n * y
  le_refl := by
    intro a
    use 1; simp
  le_antisymm := by
    intro a b ha hb
    choose n₁ hn₁ using ha
    choose n₂ hn₂ using hb
    have hn : n₁ * n₂ = 1 := by
      have h : (n₂ * n₁) * a = 1 * a := by
        rw [mul_assoc, ← hn₁, one_mul]
        exact hn₂.symm
      have := mul_right_cancel h
      rw [mul_comm]
      exact this
    have hn1 : n₁ = 1 := by
      have := congrArg PNat.val hn
      simp at this
      exact this.1
    have hn2 : n₂ = 1 := by
      have := congrArg PNat.val hn
      simp at this
      exact this.2
    grind
  le_trans := by
    intro a b c hab hbc
    choose n₁ hn₁ using hab
    choose n₂ hn₂ using hbc
    use n₁ * n₂
    grind
  lt_iff_le_not_ge := fun _ _ ↦ Iff.rfl

theorem PNat.divOrder_exists :
    ∃ (h₀ : PartialOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) :=
  ⟨PNat.divOrder, rfl⟩

theorem PNat.divOrder_not_linear :
    ¬∃ (h₀ : LinearOrder PNat), h₀.le = (fun x y ↦ ∃ n, y = n * x) := by
  intro ⟨h₀, h⟩
  have htot := h₀.le_total 2 3
  rw [h] at htot; simp at htot
  rcases htot with ⟨n, hn⟩ | ⟨n, hn⟩
  · have := congrArg PNat.val hn
    simp at this
    omega
  · have := congrArg PNat.val hn
    simp at this
    omega


/-- Exercise 8.5.4 -/
example : ¬ ∃ x : {x:ℝ| x > 0}, IsMin x := by
  push_neg
  intro x hx
  rw [IsMin.iff] at hx; push_neg at hx
  specialize hx ⟨x.val / 2, by simp; exact x.property⟩
  simp at hx
  change x.val ≤ x.val / 2 at hx
  have hxpos : x.val > 0 := by exact x.property
  linarith


/-- Exercise 8.5.5 -/
example {X Y:Type} [PartialOrder Y] (f:X → Y) : ∃ h₀: PartialOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  use {
    le := fun x y ↦ f x < f y ∨ x = y,
    le_refl := by
      intro x; right; rfl
    le_antisymm := by
      intro a b ha hb
      cases ha <;> cases hb <;> grind
    le_trans := by
      intro a b c hab hbc
      cases hab <;> cases hbc <;> grind
  }
  rfl

def Ex_8_5_5_b : Decidable (∀ (X Y:Type) (h: LinearOrder Y) (f:X → Y), ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y)) := by
  apply isFalse
  push_neg
  use Fin 2
  use Fin 1
  use inferInstance
  use fun _ => 0
  intro h₀ h
  have heq : ∀ x y : Fin 2, h₀.le x y ↔ x = y := by
    intro x y; grind
  have := h₀.le_total (0: Fin 2) 1
  cases this <;> simp_all


-- Final part of Exercise 8.5.5; if the answer to the previous part is "no", modify the hypotheses to make it true.
theorem Ex_8_5_5_b' (X Y:Type) (h: LinearOrder Y) (f:X → Y) (hf: Function.Injective f): -- need f to be injective.
    ∃ h₀: LinearOrder X, h₀.le = (fun x y ↦ f x < f y ∨ x = y) := by
  use {
    le := (fun x y ↦ f x < f y ∨ x = y)
    le_refl := by simp
    le_antisymm := by
      intro a b hab hba
      rcases hab with hfab | heab <;> rcases hba with hfba | heba
      · exact absurd hfab (by exact Std.not_gt_of_lt hfba)
      · exact heba.symm
      · exact heab
      · exact heab
    le_trans := by
      intro a b c hab hbc
      rcases hab with hfab | heab <;> rcases hbc with hfbc | hebc
      · left; exact Std.lt_trans hfab hfbc
      · left; rwa [hebc] at hfab
      · left; rwa [← heab] at hfbc
      · right; rwa [hebc] at heab
    le_total := by
      by_contra! h'
      choose a b hab hab' using h'
      have hefab : f a = f b := by
        apply le_antisymm
        · exact hab'.1
        · exact hab.1
      exact hab.2 (hf hefab)
    toDecidableLE := by
      intro x y
      simp
      exact Classical.propDecidable (f x < f y ∨ x = y)
  }
  rfl

/-- Exercise 8.5.6 -/
abbrev OrderIdeals (X: Type) [PartialOrder X] : Set (Set X) := .Iic '' (.univ : Set X)

noncomputable def OrderIdeals.iso {X: Type} [PartialOrder X] : X ≃o OrderIdeals X := {
  toFun x  := ⟨ .Iic x, by simp ⟩
  invFun x := Classical.choose x.2
  left_inv := by
    intro x
    have h := Classical.choose_spec (⟨.Iic x, by simp⟩ : OrderIdeals X).2
    apply Set.Iic_injective
    exact h.2
  right_inv := by
    intro ⟨S, hS⟩
    ext y
    simp
    constructor
    · intro hy
      grind
    · intro hy
      grind
  map_rel_iff' := by
    intro a b
    simp
  }


/-- Exercise 8.5.7 -/
example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMin x) (hy: IsMin y) : x = y := by
  rw [IsMin.iff] at hx hy; push_neg at hx hy
  specialize hx y
  specialize hy x
  apply le_antisymm
  · exact hx
  · exact hy

example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
  rw [IsMax.iff] at hx hy; push_neg at hx hy
  specialize hx y
  specialize hy x
  apply le_antisymm
  · exact hy
  · exact hx

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by
  by_contra! hinfin
  have hmin' : ∀ Y : Set X, Y.Nonempty → ∃ a ∈ Y, ∀ b ∈ Y, a ≤ b := by
    intro Y hY
    specialize hmin Y hY
    choose x hx using hmin
    use x
    constructor
    · exact x.property
    · rw [IsMin.iff] at hx; push_neg at hx
      intro b hb
      specialize hx ⟨b, hb⟩
      exact hx
  let x₀ := Classical.choose (hmin Set.univ (by simp))
  have hx₀min : IsMin x₀ := Classical.choose_spec (hmin Set.univ (by simp))
  have hx₉min' : IsMin x₀.val := by
    rw [IsMin.iff] at hx₀min ⊢
    push_neg at hx₀min ⊢
    intro y
    specialize hx₀min ⟨y, by tauto⟩
    exact hx₀min
  classical
  set g : Finset X → X := fun s => if h : (s : Set X)ᶜ.Nonempty then Classical.choose (hmin' _ h) else x₀ with hg
  set S : ℕ → Finset X := fun n => (fun s => insert (g s) s)^[n] ∅ with hS
  set f : ℕ → X := fun n => g (S n) with hf
  have hS0 : S 0 = ∅ := by
    unfold S
    simp
  have hSnext : ∀ n, S (n+1) = insert (f n) (S n) := by
    intro n
    conv_lhs =>
      unfold S
      rw [Function.iterate_succ_apply']
      rfl
  have hmem : ∀ n, ((S n) : Set X)ᶜ.Nonempty := by
    intro n
    have hfin := (S n).finite_toSet
    have hcompl := Set.Finite.infinite_compl hfin
    exact Set.Infinite.nonempty hcompl
  have hfpick : ∀ n, f n ∉ S n := by
    intro n
    have hspec := Classical.choose_spec (hmin' _ (hmem n))
    unfold f g
    rw [dif_pos (hmem n)]
    exact hspec.1
  have hfmono : ∀ n, f n < f (n + 1) := by
    intro n
    have hspec := Classical.choose_spec (hmin' _ (hmem n))
    have hnot := hfpick (n+1)
    rw [hSnext, Finset.mem_insert] at hnot
    push_neg at hnot
    have hle : f n ≤ f (n+1) := by
      have := hspec.2
      have hmemc : f (n + 1) ∈ ((S n) : Set X)ᶜ := hnot.2
      specialize this (f (n+1)) hmemc
      simp at this
      simpa only [hf, hg, dif_pos (hmem n)] using this
    order
  set I : Set X := f '' (Set.univ)
  have hInonemp : I.Nonempty := by
    use f 0
    unfold I
    simp
  choose M hM using hmax I hInonemp
  choose n hn using M.property
  rw [IsMax.iff] at hM
  push_neg at hM
  specialize hM ⟨f (n+1), by use n+1; tauto⟩
  have : f (n+1) ≤ f n := by
    have hM' : f (n + 1) ≤ (M : X) := hM
    rw [hn.2]
    exact hM'
  specialize hfmono n
  order


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by
    intro ⟨x, y⟩
    simp
  le_antisymm := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    simp
    intro h1 h2
    rcases h1 with hlt | heq <;> rcases h2 with hlt' | heq'
    · exfalso; order
    · exfalso; order
    · exfalso; order
    · apply Prod.ext
      · simp; exact heq.1
      · simp
        apply le_antisymm
        · exact heq.2
        · exact heq'.2
  le_trans := by
    intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩
    simp
    intro h1 h2
    rcases h1 with hlt | heq <;> rcases h2 with hlt' | heq'
    · left; order
    · left; order
    · left; order
    · right; constructor
      · order
      · order
}

noncomputable instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  lt := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y < y')
  le_refl := by
    intro ⟨x, y⟩
    simp
  le_trans := by
    intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ⟨x₃, y₃⟩
    simp
    intro h1 h2
    rcases h1 with hlt | heq <;> rcases h2 with hlt' | heq'
    · left; order
    · left; order
    · left; order
    · right; constructor
      · order
      · order
  le_antisymm := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    simp
    intro h1 h2
    rcases h1 with hlt | heq <;> rcases h2 with hlt' | heq'
    · exfalso; order
    · exfalso; order
    · exfalso; order
    · apply Prod.ext
      · simp; exact heq.1
      · simp
        apply le_antisymm
        · exact heq.2
        · exact heq'.2
  le_total := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    simp
    by_contra! h'
    obtain ⟨h1, h2⟩ := h'
    by_cases! heq : x = x'
    · have h1' := h1.2 heq
      have h2' := h2.2 heq.symm
      order
    · rcases heq.gt_or_lt with hgt | hlt
      · order
      · order
  lt_iff_le_not_ge := by
    intro ⟨x, y⟩ ⟨x', y'⟩
    simp
    constructor
    · intro h
      rcases h with h1 | ⟨h2, h3⟩
      · constructor
        · left; exact h1
        · constructor <;> order
      · constructor
        · right
          constructor
          · exact h2
          · order
        · constructor
          · order
          · intro _
            exact h3
    · rintro ⟨h1, h2⟩
      rcases h1 with h11 | h12
      · left; exact h11
      · right; constructor
        · exact h12.1
        · exact h2.2 h12.1.symm
  toDecidableLE := by
    intro a b
    simp
    exact
      Classical.propDecidable
        (match a with
        | (x, y) =>
          match b with
          | (x', y') => x < x' ∨ x = x' ∧ y ≤ y')

}

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
  WellFoundedLT (Lex' (X × Y)) := by
    have hminX := (WellFoundedLT.iff X).mp ‹_›
    have hminY := (WellFoundedLT.iff Y).mp ‹_›
    --rw [WellFoundedLT.iff' (by apply le_total)]
    apply (WellFoundedLT.iff' (by apply le_total)).mpr
    intro S hSnonemp
    have hfstnonemp : (Prod.fst '' S).Nonempty := hSnonemp.image Prod.fst
    obtain ⟨x₀, hx₀min⟩ := hminX _ hfstnonemp
    have hsndnonemp : {y : Y | (x₀.val, y) ∈ S}.Nonempty := by
      obtain ⟨p, hp, hpx⟩ := x₀.property
      use p.2
      simp
      rw [← hpx]
      simp
      exact hp
    obtain ⟨y₀, hy₀min⟩ := hminY _ hsndnonemp
    use ⟨⟨x₀.val, y₀.val⟩, by exact y₀.property⟩
    intro ⟨⟨x', y'⟩, hS⟩
    simp
    intro hle
    rcases hle with hlt | hlt'
    · rw [IsMin.iff] at hx₀min
      push_neg at hx₀min
      specialize hx₀min ⟨x', by use (x', y'); simp; exact hS⟩
      have : x' < x₀.val := hlt
      have : x₀ ≤ x' := hx₀min
      exfalso
      order
    · right; constructor
      · exact hlt'.1.symm
      · rw [IsMin.iff] at hy₀min
        push_neg at hy₀min
        specialize hy₀min ⟨y', by simp; rwa [← hlt'.1]⟩
        exact hy₀min

/-- Exercise 8.5.15 -/
structure PartialInj (Y X : Type) where
  dom : Set Y
  toFun : dom → X
  inj : Function.Injective toFun

instance PartialInj.partialOrder {Y X : Type} : PartialOrder (PartialInj Y X) := {
  le p₁ p₂ := ∃ h : p₁.dom ⊆ p₂.dom, ∀ a : p₁.dom, p₂.toFun ⟨a.val, h a.property⟩ = p₁.toFun a
  le_antisymm := by
    intro ⟨p₁, f₁, i₁⟩ ⟨p₂, f₂, i₂⟩ h₁ h₂; simp at h₁ h₂
    choose sub₁ hsub₁ using h₁
    choose sub₂ hsub₂ using h₂
    have hdomeq : p₁ = p₂ := by
      apply Set.Subset.antisymm <;> assumption
    subst hdomeq
    have hfuneq : f₁ = f₂ := by
      ext a
      specialize hsub₂ a a.property
      simp at hsub₂
      exact hsub₂
    subst hfuneq
    simp
  le_refl := by
    intro p
    simp
  le_trans := by
    intro p₁ p₂ p₃ ha hb
    choose suba hsuba using ha
    choose subb hsubb using hb
    have hdom : p₁.dom ⊆ p₃.dom := by
      apply Set.Subset.trans <;> assumption
    use hdom
    intro a
    specialize hsuba a
    specialize hsubb ⟨a, by exact suba a.property⟩
    rwa [← hsubb] at hsuba
}

#check Set.iUnionLift

instance PartialInj.nonempty {Y X : Type} : Nonempty (PartialInj Y X) :=
  ⟨{ dom := ∅
     toFun := fun a => absurd a.property (Set.notMem_empty a.val)
     inj := fun a _ _ => (Set.notMem_empty a.val a.prop).elim }⟩

lemma chain_partialInj {Y X} : ∀ C : Set (PartialInj Y X), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
  intro C ⟨htotal, hnonemp⟩
  have hcoherent :  ∀ (p q : {p : PartialInj Y X // p ∈ C}) (y : Y) (hp : y ∈ p.1.dom) (hq : y ∈ q.1.dom),
    p.1.toFun ⟨y, hp⟩ = q.1.toFun ⟨y, hq⟩ := by
    intro p q y hp hq
    rcases htotal p q with hpq | hqp
    · obtain ⟨hsub, hagree⟩ := hpq
      exact (hagree ⟨y, hp⟩).symm
    · obtain ⟨hsub, hagree⟩ := hqp
      exact hagree ⟨y, hq⟩
  use {
    dom := ⋃ (p : { p : PartialInj Y X // p ∈ C }), p.1.dom
    toFun := Set.iUnionLift
      (S:=fun p : { p : PartialInj Y X // p ∈ C } => p.1.dom)
      (f:=fun p => p.1.toFun)
      hcoherent
      (T:=⋃ (p : { p : PartialInj Y X // p ∈ C }), p.1.dom)
      (hT:=by rfl)
    inj := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      apply Subtype.ext
      simp
      obtain ⟨pa, hpa⟩ := Set.mem_iUnion.mp ha
      obtain ⟨pb, hpb⟩ := Set.mem_iUnion.mp hb
      rw [Set.iUnionLift_mk (i:=pa) ⟨a, hpa⟩, Set.iUnionLift_mk (i:=pb) ⟨b, hpb⟩] at hab
      rcases htotal pa pb with hleab | hleba
      · obtain ⟨hsub, hagree⟩ := hleab
        have heq : pb.1.toFun ⟨a, hsub hpa⟩ = pb.1.toFun ⟨b, hpb⟩ := by
          rw [← hab]
          apply hcoherent
        have := pb.1.inj heq
        simpa using this
      · obtain ⟨hsub, hagree⟩ := hleba
        have heq : pa.1.toFun ⟨a, hpa⟩ = pa.1.toFun ⟨b, hsub hpb⟩ := by
          rw [hab]
          apply hcoherent
        have := pa.1.inj heq
        simpa using this
  }
  intro p hp
  have : p.dom ⊆ ⋃ (p : { p : PartialInj Y X // p ∈ C }), p.1.dom := by
    simp
    exact Set.subset_biUnion_of_mem hp
  use this
  intro y
  simp
  exact Set.iUnionLift_mk
        (S:=fun q : { p : PartialInj Y X // p ∈ C } => q.1.dom)
        (f:=fun q : { p : PartialInj Y X // p ∈ C } => q.1.toFun)
        (hf:=hcoherent)
        (hT:=this)
        (i:= ⟨p, hp⟩) y y.2

open Classical in
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by
    choose m hm using Zorns_lemma (X:=PartialInj Y X) chain_partialInj
    have hentire : m.dom = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      by_contra! hy
      by_cases hsurj : ∃ z : X, z ∉ Set.range m.toFun
      · choose z hz using hsurj
        set m' : PartialInj Y X := {
          dom := m.dom ∪ {y}
          toFun := fun a => if hdom : a.val ∈ m.dom then m.toFun ⟨a.val, hdom⟩ else z
          inj := by
            intro ⟨a, ha⟩ ⟨b, hb⟩ hab
            simp at hab ⊢
            split_ifs at hab with h1 h2 h3
            · simpa using m.inj hab
            · have : z ∈ Set.range m.toFun := by
                rw [← hab]
                simp
              exact absurd this hz
            · have : z ∈ Set.range m.toFun := by
                rw [hab]
                simp
              exact absurd this hz
            · have hay : a = y := by
                rw [Set.mem_union] at ha
                rcases ha with ha' | rfl
                · exact absurd ha' h1
                · rfl
              have hby : b = y := by
                rw [Set.mem_union] at hb
                rcases hb with hb' | rfl
                · exact absurd hb' h3
                · rfl
              rwa [hby]
        }
        rw [IsMax.iff] at hm; push_neg at hm
        specialize hm m'
        apply hm
        constructor
        · simp
          have : m.dom ⊆ m'.dom := by
            show m.dom ⊆ m.dom ∪ {y}
            simp
          use this
          intro a ha
          unfold m'
          simp
          rw [dif_pos ha]
        · simp
          intro hsub
          have : ¬ (m'.dom ⊆ m.dom) := by
            unfold m'
            simp
            refine Set.not_subset.mpr ?_
            use y
            simp
            exact hy
          exact absurd hsub this
      · push_neg at hsurj
        have hsurj' : Function.Surjective m.toFun := by
          intro z
          specialize hsurj z
          choose k hl using hsurj
          use k
        have hf : Function.Injective (fun x => (Function.surjInv hsurj' x).val)  := by
          intro a b hab
          exact Function.injective_surjInv hsurj' (Subtype.ext hab)
        apply h
        exact ⟨_, hf⟩
    use fun x => m.toFun ⟨x, by rw [hentire]; tauto⟩
    intro a b hab
    simp at hab
    simpa using m.inj hab

/-- Exercise 8.5.16: The set of partial orderings on X, ordered by "coarser than",
is itself a partial order. -/
instance PartialOrder.coarserOrder (X : Type) : PartialOrder (PartialOrder X) where
  le p1 p2 := ∀ x y : X, p1.le x y → p2.le x y
  le_refl := by simp
  le_trans p1 p2 p3 h12 h23 := fun x y h => h23 x y (h12 x y h)
  le_antisymm p1 p2 h12 h21 := by ext x y; exact ⟨h12 x y, h21 x y⟩

/-- The divisibility ordering on PNat is coarser than the usual ordering. -/
example : PNat.divOrder ≤ (inferInstance : PartialOrder PNat) := by
  intro x y h
  obtain ⟨n, rfl⟩ := h
  show x ≤ n * x
  exact Nat.le_mul_of_pos_left x n.pos

/-- The discrete ordering (x ≤ y ↔ x = y) is the unique minimal element. -/
@[reducible] def PartialOrder.discrete (X : Type) : PartialOrder X where
  le x y := x = y
  le_refl := fun _ ↦ rfl
  le_antisymm := fun _ _ h _ ↦ h
  le_trans := fun _ _ _ h1 h2 ↦ h1.trans h2

theorem PartialOrder.discrete_isBot (X : Type) (p : PartialOrder X) :
    PartialOrder.discrete X ≤ p := by
  intro x y hxy
  have : x = y := by exact hxy
  rw [hxy]

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by
  intro x hx
  apply PartialOrder.discrete_isBot

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) :
    p = discrete X := by
    have := discrete_isBot X p
    apply le_antisymm
    · exact h this
    · exact this

/-- A partial ordering is maximal in the coarser order iff it is total. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by
  constructor
  · intro hmax
    by_contra htot
    unfold IsTotal at htot
    push_neg at htot
    choose x y hxy hyx using htot
    let p' : PartialOrder X := {
      le a b := p.le a b ∨ (p.le a x ∧ p.le y b)
      lt a b := (p.le a b ∨ (p.le a x ∧ p.le y b)) ∧ ¬(p.le b a ∨ (p.le b x ∧ p.le y a))
      le_refl := by
        intro a
        left
        rfl
      le_trans := by
        intro a b c hab hbc
        rcases hab with hab | ⟨hab₁, hab₂⟩ <;> rcases hbc with hbc | ⟨hbc₁, hbc₂⟩
        · left; order
        · right; constructor
          · order
          · exact hbc₂
        · right; constructor
          · exact hab₁
          · order
        · right; constructor
          · exact hab₁
          · exact hbc₂
      le_antisymm := by
        intro a b hab hba
        rcases hab with hab | ⟨hab₁, hab₂⟩ <;> rcases hba with hba | ⟨hbc₁, hbc₂⟩
        · order
        · have : y ≤ x := by order
          exact absurd this hyx
        · have : y ≤ x := by order
          exact absurd this hyx
        · have : y ≤ x := by order
          exact absurd this hyx
      lt_iff_le_not_ge := by
        intro a b; constructor
        · intro h; grind
        · intro ⟨h₁, h₂⟩; constructor
          · push_neg at h₂
            rcases h₁ with hnow | hlater
            · order
            · right; exact hlater
          · grind
    }
    have hle : p ≤ p' := by
      intro x y hxy
      left; exact hxy
    have hnle : ¬ (p' ≤ p) := by
      by_contra! h'
      change ∀ x y : X, p'.le x y → p.le x y at h'
      have : p'.le x y := by
        right; constructor <;> apply p.le_refl
      exact absurd (h' x y this) hxy
    exact absurd (hmax hle) hnle
  · intro htot p' hp a b hab
    rcases htot a b with h | h
    · exact h
    · have h1 : a = b := p'.le_antisymm a b hab (hp b a h)
      rw [h1]
      exact p.le_refl b


#check Zorns_lemma
abbrev ExtendedOrder {X : Type} (p : PartialOrder X) := {q : PartialOrder X // p ≤ q}


instance ExtendedOrder.nonempty {X : Type} {p : PartialOrder X} : Nonempty (ExtendedOrder p) := by
  use p

lemma extendedOrder_def {X : Type} (p : PartialOrder X) : ExtendedOrder p = {q : PartialOrder X // p ≤ q} := by
  rfl

lemma chain_extendedOrder {X : Type} {p : PartialOrder X} : ∀ C : Set (ExtendedOrder p), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
  intro C ⟨htot, hnon⟩
  set U : PartialOrder X := {
    le a b := ∃ q ∈ C, q.val.le a b
    lt a b := (∃ q ∈ C, q.val.le a b) ∧ ¬ (∃ q ∈ C, q.val.le b a)
    le_refl := by
      intro a
      obtain ⟨q, hq⟩ := hnon
      use q; constructor
      · exact hq
      · apply q.val.le_refl
    le_trans := by
      intro a b c hab hbc
      choose q hqC haleb using hab
      choose q' hq'C hblec using hbc
      rcases htot ⟨q, hqC⟩ ⟨q', hq'C⟩ with hq | hq'
      · use q'; constructor
        · exact hq'C
        · have haleb' := hq a b haleb
          exact q'.val.le_trans _ _ _ haleb' hblec
      · use q; constructor
        · exact hqC
        · have hblec' : q.val.le b c := hq' b c hblec
          exact q.val.le_trans _ _ _ haleb hblec'
    le_antisymm := by
      intro a b hab hba
      choose q hqC haleb using hab
      choose q' hq'C hblea using hba
      change q.val.le a b at haleb
      change q'.val.le b a at hblea
      rcases htot ⟨q, hqC⟩ ⟨q', hq'C⟩ with hq | hq'
      · have haleb' := hq a b haleb
        apply q'.val.le_antisymm
        · exact haleb'
        · exact hblea
      · have hblea' := hq' b a hblea
        apply q.val.le_antisymm
        · exact haleb
        · exact hblea'
  }
  have hpU : p ≤ U := by
    obtain ⟨q, hq⟩ := hnon
    apply le_trans q.property
    intro a b hab
    use q
  use ⟨U, hpU⟩
  intro q hq a b hab
  change q.val.le a b at hab
  change U.le a b
  use q

/-- Any partial ordering extends to a total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by
  choose m hm using Zorns_lemma (X:=ExtendedOrder p) chain_extendedOrder
  use m.val
  constructor
  · exact m.property
  · intro a b
    by_contra! h'
    obtain ⟨hnotab, hnotba⟩ := h'
    rw [IsMax.iff] at hm; push_neg at hm
    set U : PartialOrder X := {
      le x y := m.val.le x y ∨ (m.val.le x a ∧ m.val.le b y)
      lt x y := (m.val.le x y ∨ (m.val.le x a ∧ m.val.le b y)) ∧
          ¬ (m.val.le y x ∨ (m.val.le y a ∧ m.val.le b x))
      le_refl := by
        intro x
        left
        apply m.val.le_refl
      le_trans := by
        intro x y z hxy hyz
        rcases hxy with hxy1 | hxy2 <;> rcases hyz with hyz1 | hyz2
        · left; exact m.val.le_trans _ _ _ hxy1 hyz1
        · right; constructor
          · exact m.val.le_trans _ _ _ hxy1 hyz2.1
          · exact hyz2.2
        · right; constructor
          · exact hxy2.1
          · exact m.val.le_trans _ _ _ hxy2.2 hyz1
        · right; constructor
          · exact hxy2.1
          . exact hyz2.2
      le_antisymm := by
        intro x y hxy hyx
        rcases hxy with hxy1 | hxy2 <;> rcases hyx with hyx1 | hyx2
        · exact m.val.le_antisymm _ _ hxy1 hyx1
        · have hby := m.val.le_trans _ _ _ hyx2.2 hxy1
          have hba := m.val.le_trans _ _ _ hby hyx2.1
          exact absurd hba hnotba
        · have hbx := m.val.le_trans _ _ _ hxy2.2 hyx1
          have hba := m.val.le_trans _ _ _ hbx hxy2.1
          exact absurd hba hnotba
        · have hba := m.val.le_trans _ _ _ hxy2.2 hyx2.1
          exact absurd hba hnotba
    }
    have hpU : p ≤ U := by
      intro x y hxy
      left
      apply m.property
      exact hxy
    specialize hm ⟨U, hpU⟩
    have hmleU : m ≤ ⟨U, hpU⟩ := by
      intro x y hxy
      left
      exact hxy
    have hmeqU : m ≠ ⟨U, hpU⟩ := by
      intro heq
      apply hnotab
      rw [heq] -- change the ≤ relation from the m.le relation to the U.le relation.
      change U.le a b
      right
      constructor <;> apply m.val.le_refl
    have hmltU :  m < ⟨U, hpU⟩ := by order
    exact hm hmltU


abbrev PartialTransversal {I U : Type} (X : I → Set U) : Type :=
  { Y : Set U // ∀ α, (Y ∩ X α).Subsingleton }

instance PartialTransversal.nonempty {I U : Type} {X : I → Set U} : Nonempty (PartialTransversal X) := by
  use ∅
  intro i
  simp

lemma chain_partialTransversal {I U : Type} {X : I → Set U} : ∀ C : Set (PartialTransversal X), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
  intro C ⟨htot, hnon⟩
  set ub : Set U := ⋃ c ∈ C, c.val
  have hub : ∀ α, (ub ∩ X α).Subsingleton := by
    intro i u hub
    intro u' hub'
    obtain ⟨hu_ub, hu_X⟩ := hub
    obtain ⟨hu'_ub, hu'_X⟩ := hub'
    rw [Set.mem_iUnion₂] at hu_ub hu'_ub
    obtain ⟨c, hc, hu_c⟩ := hu_ub
    obtain ⟨c', hc', hu'_c'⟩ := hu'_ub
    rcases htot ⟨c, hc⟩ ⟨c', hc'⟩ with ha | ha'
    · simp at ha
      have hu_in_c' : u ∈ c'.val := ha hu_c
      apply c'.property i
      · exact ⟨hu_in_c', hu_X⟩
      · exact ⟨hu'_c', hu'_X⟩
      --exact c'.property i ⟨hu_in_c', hu_X⟩ ⟨hu'_c', hu'_X⟩
    · simp at ha'
      have hu'_in_c : u' ∈ c.val := ha' hu'_c'
      apply c.property i
      · exact ⟨hu_c, hu_X⟩
      · exact ⟨hu'_in_c, hu'_X⟩
  use ⟨ub, hub⟩
  intro a ha
  show a.val ⊆ ub
  unfold ub
  exact Set.subset_biUnion_of_mem ha


/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by
    choose m hm using Zorns_lemma (X:=PartialTransversal X) chain_partialTransversal
    use m.val
    intro i
    have hsingle := m.property i
    have hnonempty : (m.val ∩ X i).Nonempty := by
      by_contra! h'
      obtain ⟨x₀⟩ := hne i
      set ub : Set U := m.val ∪ {x₀.val}
      have hub : ∀ α, (ub ∩ X α).Subsingleton := by
        unfold ub
        intro k
        by_cases hki : k = i
        · rw [← hki] at h'
          rw [Set.union_inter_distrib_right, h', Set.empty_union]
          exact Set.Subsingleton.singleton_inter
        · rw [Set.union_inter_distrib_right]
          have hx₀ : (x₀:U) ∉ X k := by
            intro hmem
            have := h (Set.mem_univ k) (Set.mem_univ i) hki
            change Disjoint (X k) (X i) at this
            have hxi : (x₀:U) ∈ X i := by exact x₀.property
            have notthis :  ¬ Disjoint (X k) (X i) := by
              refine Set.not_disjoint_iff.mpr ?_
              use x₀
            exact notthis this
          have hempty : {x₀.val} ∩ X k = ∅ := by
            simp; exact hx₀
          rw [hempty, Set.union_empty]
          exact m.property k
      rw [IsMax.iff] at hm
      push_neg at hm
      specialize hm ⟨ub, hub⟩
      have hmleub : m < ⟨ub, hub⟩ := by
        change m.val ⊂ ub
        have := x₀.property
        refine Set.ssubset_union_left_iff.mpr ?_
        intro hmem
        contrapose! h'
        use x₀; constructor
        · simpa using hmem
        · exact this
      exact hm hmleub
    obtain ⟨u, hu⟩ := hnonempty
    rw [hsingle.eq_singleton_of_mem hu]
    simp


abbrev TotalChain (X : Type) [PartialOrder X] : Type :=
  { S : Set X // IsTotal S }

instance TotalChain.nonempty {X : Type} [PartialOrder X] : Nonempty (TotalChain X) := by
  use ∅
  intro a b; simp

lemma chain_totalChain {X : Type} [PartialOrder X] : ∀ C : Set (TotalChain X), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
  intro C ⟨htot, hnon⟩
  set ub : Set X := ⋃ c ∈ C, c.val
  have hub : IsTotal ub := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp
    rw [Set.mem_iUnion₂] at ha hb
    obtain ⟨c, hc, ha_c⟩ := ha
    obtain ⟨c', hc', hb_c'⟩ := hb
    rcases htot ⟨c, hc⟩ ⟨c', hc'⟩ with hle | hle
    · simp at hle
      have ha_c' : a ∈ c'.val := hle ha_c
      exact c'.property ⟨a, ha_c'⟩ ⟨b, hb_c'⟩
    · simp at hle
      have hb_c : b ∈ c.val := hle hb_c'
      exact c.property ⟨a, ha_c⟩ ⟨b, hb_c⟩
  use ⟨ub, hub⟩
  intro c hc
  show c.val ⊆ ub
  unfold ub
  exact Set.subset_biUnion_of_mem hc


#check Zorns_lemma
/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by
    choose m hm using Zorns_lemma (X:=TotalChain X) chain_totalChain
    use m
    constructor
    · simp
      exact m.property
    · intro S hStotal hsub
      exact hm (b := ⟨S, hStotal⟩) hsub

theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) :
    ∃ x : X, IsMax x := by
  choose M hM using hhausdorff
  obtain ⟨htotal, hmaximal⟩ := hM
  simp at hmaximal
  have hMnonempty : M.Nonempty := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    let singleton : Set X := {x₀}
    have hsingtot : IsTotal singleton := by
      intro a b
      have ha : a = x₀ := by aesop
      have hb : b = x₀ := by aesop
      left
      grind
    by_contra! hempty
    specialize hmaximal hsingtot (by rw [hempty]; tauto)
    rw [hempty] at hmaximal
    change {x₀} ⊆ ∅ at hmaximal
    simp at hmaximal
  choose x hx using hchain M ⟨htotal, hMnonempty⟩
  use x
  intro α hα
  by_cases haM : α ∈ M
  · exact hx α haM
  · set ub := M ∪ {α}
    have htotub : IsTotal ub := by
      intro a b
      rcases a.property with haM | hasing <;> rcases b.property with hbM | hbsing
      · exact htotal ⟨a, haM⟩ ⟨b, hbM⟩
      · simp at hbsing
        left
        specialize hx a haM
        change a.val ≤ b.val
        order
      · simp at hasing
        right
        specialize hx b hbM
        change b.val ≤ a.val
        order
      · simp at hasing hbsing
        left
        change a.val ≤ b.val
        order
    specialize hmaximal htotub (by unfold ub; tauto)
    unfold ub at hmaximal
    exfalso
    contrapose! hmaximal
    refine Set.not_subset.mpr ?_
    use α; constructor
    · simp
    · exact haM

/-- Exercise 8.5.19: A well-ordered subset of X: a subset with a linear order and
well-foundedness. -/
structure WellOrderedSubset (X : Type) where
  carrier : Set X
  ord : LinearOrder carrier
  wf : @WellFoundedLT carrier ord.toLT

/-- (W, ≤) is an initial segment of (W', ≤') if W ⊆ W', the orderings agree on W,
and W = \{y ∈ W' : y <' x\} for some x ∈ W'. -/
def WellOrderedSubset.IsInitialSegment {X : Type}
    (W W' : WellOrderedSubset X) : Prop :=
  ∃ x : W'.carrier,
    W.carrier = Subtype.val '' {z : W'.carrier | W'.ord.lt z x} ∧
    ∀ (a b : W.carrier) (ha : a.1 ∈ W'.carrier) (hb : b.1 ∈ W'.carrier),
      W.ord.le a b ↔ W'.ord.le ⟨a, ha⟩ ⟨b, hb⟩

theorem WellOrderedSubset.IsInitialSegment.subset {X : Type}
    {W W' : WellOrderedSubset X} (h : W.IsInitialSegment W') :
    W.carrier ⊂ W'.carrier := by
  choose x hxcarrier hiff using h
  rw [Set.ssubset_iff_of_subset]
  · use x; constructor
    · exact x.property
    · intro h'
      rw [hxcarrier] at h'
      simp at h'
  · rw [hxcarrier]
    intro a ha
    simp at ha
    exact ha.1

/-- The ordering on well-ordered subsets: equal or initial segment. -/
instance WellOrderedSubset.instPartialOrder (X : Type) :
    PartialOrder (WellOrderedSubset X) where
  le W W' := W = W' ∨ W.IsInitialSegment W'
  le_refl := fun W ↦ Or.inl rfl
  le_antisymm := by
    intro W W' h1 h2
    rcases h1 with rfl | h1
    · rfl
    rcases h2 with rfl | h2
    · rfl
    exact (h1.subset.asymm h2.subset).elim
  le_trans := by
    intro W₁ W₂ W₃ hW₁₂ hW₂₃
    rcases hW₁₂ with hW₁₂ | hW₁₂' <;> rcases hW₂₃ with hW₂₃ | hW₂₃'
    · left; rwa [hW₁₂]
    · right; rwa [hW₁₂]
    · right; rwa [← hW₂₃]
    · right
      have h₁₂ := WellOrderedSubset.IsInitialSegment.subset hW₁₂'
      have h₂₃ := WellOrderedSubset.IsInitialSegment.subset hW₂₃'
      have h₁₃ : W₁.carrier ⊂ W₃.carrier := by exact ssubset_trans h₁₂ h₂₃
      choose z₂ hz₂carrier₁ htransfer₁₂ using hW₁₂'
      choose z₃ hz₃carrier₂ htransfer₂₃ using hW₂₃'
      have hzmem₃ : z₂.val ∈ W₃.carrier := by exact h₂₃.1 z₂.property
      use ⟨z₂, hzmem₃⟩
      constructor
      · ext y; constructor
        · intro hyW₁
          simp
          have hyW₃ : y ∈ W₃.carrier := by exact h₁₃.1 hyW₁
          use hyW₃
          rw [hz₂carrier₁] at hyW₁
          simp at hyW₁; obtain ⟨hyW₂, hylt₂⟩ := hyW₁
          change W₂.ord.lt ⟨y, hyW₂⟩ z₂ at hylt₂
          have hyle₂ : W₂.ord.le ⟨y, hyW₂⟩ z₂ := by
            exact @le_of_lt _ W₂.ord.toPreorder _ _ hylt₂
          apply @lt_of_le_not_ge _ W₃.ord.toPreorder _ _
          · specialize htransfer₂₃ ⟨y, hyW₂⟩ z₂ hyW₃ hzmem₃
            exact htransfer₂₃.mp hyle₂
          · intro hle
            specialize htransfer₂₃ z₂ ⟨y, hyW₂⟩ hzmem₃ hyW₃
            have htransferred₃₂ := htransfer₂₃.mpr hle
            have := @lt_of_lt_of_le _ W₂.ord.toPreorder _ _ _ hylt₂ htransferred₃₂
            simp at this
        · intro hyltz₃
          simp at hyltz₃
          obtain ⟨hyW₃, hylt₃⟩ := hyltz₃
          rw [hz₂carrier₁]; simp
          have hz₂ltz₃ : W₃.ord.lt ⟨↑z₂, hzmem₃⟩ z₃ := by
            have hz₂mem := z₂.property
            obtain ⟨w, hw, hweq⟩ := (Set.ext_iff.mp hz₃carrier₂ z₂).mp hz₂mem
            simp at hw hweq
            rwa [show w = ⟨z₂, hzmem₃⟩ from Subtype.ext hweq] at hw
          have hyW₂ : y ∈ W₂.carrier := by
            rw [hz₃carrier₂]; simp
            use hyW₃
            exact @lt_trans _ W₃.ord.toPreorder _ _ _ hylt₃ hz₂ltz₃
          use hyW₂
          have hyle₃ := @le_of_lt _ W₃.ord.toPreorder _ _ hylt₃
          apply @lt_of_le_not_ge _ W₂.ord.toPreorder _ _
          · specialize htransfer₂₃ ⟨y, hyW₂⟩ z₂ hyW₃ hzmem₃
            exact htransfer₂₃.mpr hyle₃
          · intro hle
            specialize htransfer₂₃ z₂ ⟨y, hyW₂⟩ hzmem₃ hyW₃
            have htransferred₂₃ := htransfer₂₃.mp hle
            have := @lt_of_le_of_lt _ W₃.ord.toPreorder _ _ _  htransferred₂₃ hylt₃
            simp at this
      · intro a b ha₃ hb₃
        have ha₁ := a.property
        have hb₁ := b.property
        have ha₂ : a.val ∈ W₂.carrier := by exact h₁₂.1 ha₁
        have hb₂ : b.val ∈ W₂.carrier := by exact h₁₂.1 hb₁
        specialize htransfer₁₂ a b ha₂ hb₂
        specialize htransfer₂₃ ⟨a, ha₂⟩ ⟨b, hb₂⟩ ha₃ hb₃
        constructor
        · intro hab₁
          apply htransfer₂₃.mp
          exact htransfer₁₂.mp hab₁
        · intro hab₃
          simp at htransfer₁₂ htransfer₂₃
          apply htransfer₁₂.mpr
          exact htransfer₂₃.mpr hab₃


lemma WellOrderedSubset.le_subset {X:Type} {W W' : WellOrderedSubset X}
  (h : W ≤ W') : W.carrier ⊆ W'.carrier := by
  rcases h with heq | hseg
  · rw [heq]
  · have := WellOrderedSubset.IsInitialSegment.subset hseg
    exact subset_of_ssubset this

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by
  intro W hle
  rcases hle with rfl | hx
  · rfl
  · choose x hx' using hx
    exfalso
    exact x.property.elim

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by
  classical
  constructor
  · intro hmax
    by_contra! hnotuniv
    rw [Set.ne_univ_iff_exists_notMem] at hnotuniv
    choose x₀ hx₀ using hnotuniv
    let carrier' : Set X := insert x₀ W.carrier
    have hcarrier {x:carrier'} (hnotx : x ≠ x₀) : x.val ∈ W.carrier := by
      have := x.property
      unfold carrier' at this
      exact Set.mem_of_mem_insert_of_ne this hnotx
    let le' (a b : carrier') := if hb : b.val = x₀ then True
          else if ha : a.val = x₀ then False
          else W.ord.le ⟨a, hcarrier ha⟩ ⟨b, hcarrier hb⟩
    let lt' (a b : carrier') := if ha : a.val = x₀ then False
          else if hb : b.val = x₀ then True
          else W.ord.lt ⟨a, by grind⟩ ⟨b, by grind⟩
    let W' : WellOrderedSubset X := {
      carrier := carrier'
      ord := {
        le := le'
        lt := lt'
        le_refl := by
          intro a
          unfold le'
          simp
        le_antisymm := by
          intro a b hab hba
          unfold le' at hab hba
          simp at hab hba
          by_cases! hax : a.val = x₀ <;> by_cases! hbx : b.val = x₀
          · grind
          · simp_all
          · simp_all
          · simp_all
            have haW : a.val ∈ W.carrier := by exact hcarrier hax
            have hbW : b.val ∈ W.carrier := by exact hcarrier hbx
            have := W.ord.le_antisymm ⟨a.val, haW⟩ ⟨b.val, hbW⟩ hab hba
            simp at this
            exact Subtype.ext this
        le_trans := by
          intro a b c hab hbc
          unfold le' at hab hbc ⊢
          simp at hab hbc
          by_cases! hax : a.val = x₀
            <;> by_cases! hbx : b.val = x₀
            <;> by_cases! hcx : c.val = x₀
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          · simp_all
          · have haW : a.val ∈ W.carrier := by exact hcarrier hax
            have hbW : b.val ∈ W.carrier := by exact hcarrier hbx
            have hcW : c.val ∈ W.carrier := by exact hcarrier hcx
            have := W.ord.le_trans ⟨a.val, haW⟩ ⟨b.val, hbW⟩ ⟨c.val, hcW⟩
            simp_all
        le_total := by
          intro a b
          unfold le'
          by_cases! hax : a.val = x₀ <;> by_cases! hbx : b.val = x₀
          · simp_all
          · simp_all
          · simp_all
          · have haW : a.val ∈ W.carrier := by exact hcarrier hax
            have hbW : b.val ∈ W.carrier := by exact hcarrier hbx
            have := W.ord.le_total ⟨a.val, haW⟩ ⟨b.val, hbW⟩
            simp_all
        lt_iff_le_not_ge := by
          intro a b
          unfold lt' le'; simp_all
          by_cases! hax : a.val = x₀ <;> by_cases! hbx : b.val = x₀
          · simp_all
          · simp_all
          · simp_all
          · have haW : a.val ∈ W.carrier := by exact hcarrier hax
            have hbW : b.val ∈ W.carrier := by exact hcarrier hbx
            convert W.ord.lt_iff_le_not_ge ⟨a.val, haW⟩ ⟨b.val, hbW⟩
            simp_all
        toDecidableLE := by exact Classical.decRel _
      }
      wf := by
        rw [WellFoundedLT.iff]
        intro A hA
        let g : {p // p ∈ W.carrier} → {p // p ∈ insert x₀ W.carrier} := fun b => ⟨b.1, Set.mem_insert_of_mem _ b.2⟩
        by_cases hmeetsold : ∃ a ∈ A, (a : X) ∈ W.carrier
        · obtain ⟨a₀, ha₀, ha₀'⟩ := hmeetsold
          obtain ⟨m, hmA, hmin⟩ := W.wf.wf.has_min (g ⁻¹' A) (by use ⟨a₀, ha₀'⟩; simp; unfold g; tauto)
          use ⟨⟨m, by refine Set.mem_insert_of_mem x₀ ?_; exact m.property⟩, by grind⟩
          intro m' hm'
          unfold le' at hm'
          show le' (⟨↑m, _⟩ : {p // p ∈ insert x₀ W.carrier}) m'.val
          unfold le'
          by_cases! hm'x₀ : m' = x₀
          · simp_all
          · have := hcarrier hm'x₀
            grind
        · push_neg at hmeetsold
          have hAx₀ : ∀ a ∈ A, a = x₀ := by
            intro a ha
            specialize hmeetsold a ha
            have := a.property
            unfold carrier' at this
            exact (this.resolve_right hmeetsold)
          use ⟨
            ⟨x₀, by exact Set.mem_insert x₀ W.carrier⟩,
            by
              obtain ⟨a₀, ha₀⟩ := hA
              specialize hAx₀ a₀ ha₀
              grind
          ⟩
          intro a ha
          specialize hAx₀ a a.property
          show le' (⟨x₀, _⟩ : {p // p ∈ insert x₀ W.carrier}) a.val
          unfold le'
          simp_all
    }
    rw [IsMax.iff] at hmax
    push_neg at hmax
    specialize hmax W'
    have hlt : W ≤ W' := by
      right
      have hx₀W' : x₀ ∈ W'.carrier := by
        show x₀ ∈ carrier'
        unfold carrier'
        simp
      use ⟨x₀, hx₀W'⟩
      constructor
      · ext y; constructor
        · intro hyWcarrier
          have hyW'carrier : y ∈ W'.carrier := by
            show y ∈ carrier'
            unfold carrier'
            simp; right; exact hyWcarrier
          simp
          use hyW'carrier
          show lt' ⟨y, _⟩ ⟨x₀, _⟩
          unfold lt'
          simp
          intro hyx₀
          have : x₀ ∈ W.carrier := by exact Set.mem_of_eq_of_mem hyx₀.symm hyWcarrier
          exact absurd this hx₀
        · intro hlt
          simp at hlt
          obtain ⟨h1, h2⟩ := hlt
          change y ∈ carrier' at h1
          unfold carrier' at h1
          rcases h1 with hinsert | hWcarrier
          · have hyW' : y ∈ W'.carrier := by exact Set.mem_of_eq_of_mem hinsert hx₀W'
            change W'.ord.lt ⟨y, hyW'⟩ ⟨x₀, hx₀W'⟩ at h2
            have : W'.ord.lt ⟨y, hyW'⟩ ⟨y, hyW'⟩ := by
              have : (⟨x₀, hx₀W'⟩ : {p // p ∈ W'.carrier}) = ⟨y, hyW'⟩ := Subtype.ext hinsert.symm
              rwa [this] at h2
            simp at this
          · exact hWcarrier
      · intro a b ha hb
        change _ ∈ carrier' at ha
        change _ ∈ carrier' at hb
        unfold carrier' at ha hb
        constructor
        · intro hab
          change le' ⟨a, ha⟩ ⟨b, hb⟩
          unfold le'
          simp_all
          intro hnotbx₀
          rcases ha with hinserta | hwacarrier <;> rcases hb with hinsertb | hwbcarrier
          · exact absurd hinsertb hnotbx₀
          · have := a.property
            have : x₀ ∈ W.carrier := by exact Set.mem_of_eq_of_mem hinserta.symm this
            exact absurd this hx₀
          · have := b.property
            have : x₀ ∈ W.carrier := by exact Set.mem_of_eq_of_mem hinsertb.symm this
            exact absurd this hx₀
          · intro hnotax₀
            have : x₀ ∈ W.carrier := by exact Set.mem_of_eq_of_mem hnotax₀.symm hwacarrier
            exact absurd this hx₀
        · intro hab
          change le' ⟨a, ha⟩ ⟨b, hb⟩ at hab
          unfold le' at hab
          simp at hab
          rcases ha with hinserta | hwacarrier <;> rcases hb with hinsertb | hwbcarrier
          · have : a = b := by refine SetCoe.ext ?_; rwa [hinsertb]
            grind
          · have : x₀ ∈ W.carrier := by
              have := a.property
              rwa [hinserta] at this
            exact absurd this hx₀
          · have : x₀ ∈ W.carrier := by
              have := b.property
              rwa [hinsertb] at this
            exact absurd this hx₀
          · have hbx₀ : b ≠ x₀ := by exact ne_of_mem_of_not_mem hwbcarrier hx₀
            have := hab hbx₀
            exact this.2
    have hneq : W ≠ W' := by
      grind
    have hlt : W < W' := by exact lt_of_le_of_ne hlt hneq
    exact hmax hlt
  · intro huniv W' hW'
    rcases hW' with heq | hseg
    · left; exact heq.symm
    · right
      choose x₀ hsubtype hiff using hseg
      have hx₀W : x₀.val ∈ W.carrier := by
        rw [huniv]
        tauto
      use ⟨x₀, hx₀W⟩; constructor
      · ext y; constructor
        · intro hyW'; simp
          have hyW : y ∈ W.carrier := by
            rw [huniv]
            tauto
          use hyW
          have hlt' : W'.ord.lt ⟨y, hyW'⟩ ⟨x₀, x₀.property⟩ := by
              rw [hsubtype] at hyW
              simp at hyW
              obtain ⟨hyW1, hyW2⟩ := hyW
              exact hyW2
          apply (@lt_iff_le_not_ge _ W.ord.toPreorder  ⟨y, hyW⟩ ⟨x₀, hx₀W⟩).mpr
          constructor
          · specialize hiff ⟨y, hyW⟩ ⟨x₀, hx₀W⟩ hyW' x₀.property
            have hle' : W'.ord.le ⟨y, hyW'⟩ ⟨x₀, x₀.property⟩ := by
              exact @le_of_lt _ W'.ord.toPreorder _ _ hlt'
            exact hiff.mpr hle'
          · by_contra h'
            specialize hiff ⟨x₀, hx₀W⟩ ⟨y, hyW⟩ x₀.property hyW'
            have hle' : W'.ord.le  ⟨x₀, x₀.property⟩ ⟨y, hyW'⟩ := by
              exact hiff.mp h'
            have := @lt_of_lt_of_le _ W'.ord.toPreorder _ _ _ hlt' hle'
            simp at this
        · intro h
          simp at h
          obtain ⟨hyW, hyltx₀⟩ := h
          rw [hsubtype] at hyW
          simp at hyW
          obtain ⟨hyW', hltx₀'⟩ := hyW
          exact hyW'
      · intro a b ha hb
        specialize hiff ⟨a, ha⟩ ⟨b, hb⟩ (by simp) (by simp)
        exact hiff.symm


lemma chain_WellOrderedSubset {X:Type} : ∀ C : Set (WellOrderedSubset X), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
  intro C ⟨htotal, hnonemp⟩
  let carrier' : Set X := ⋃ c ∈ C, c.carrier
  let le' (a b : carrier') : Prop :=
    ∃ (S : WellOrderedSubset X) (_ : S ∈ C) (ha : a.val ∈ S.carrier) (hb : b.val ∈ S.carrier),
    S.ord.le ⟨a, ha⟩ ⟨b, hb⟩
  let lt' (a b : carrier') : Prop :=
    ∃ (S : WellOrderedSubset X) (_ : S ∈ C) (ha : a.val ∈ S.carrier) (hb : b.val ∈ S.carrier),
    S.ord.lt ⟨a, ha⟩ ⟨b, hb⟩
  have mem_carrier' :
          ∀ (a : carrier'), ∃ S, S ∈ C ∧ a.val ∈ S.carrier := by
        intro a
        have := a.property
        unfold carrier' at this
        rw [Set.mem_iUnion₂] at this
        choose S hS hin using this
        use S
  have seg_lt :
          ∀ (S S' : WellOrderedSubset X), S.IsInitialSegment S' →
            ∀ (p q : X)
              (hpS : p ∈ S.carrier) (hpS' : p ∈ S'.carrier) (hqS' : q ∈ S'.carrier),
            q ∉ S.carrier → S'.ord.lt ⟨p, hpS'⟩ ⟨q, hqS'⟩ := by
        intro S S' hseg p q hpS hpS' hqS' hqnotS
        obtain ⟨x₀, hcar, hcompat⟩ := hseg
        -- x₀ : ↥S'.carrier,  hcar : S.carrier = Subtype.val '' {z | z < x₀}
        -- Step 1: p ∈ S.carrier ⇒ ⟨p,hpS'⟩ < x₀  (p is in the segment, i.e. below x₀)
        have hp_lt : S'.ord.lt ⟨p, hpS'⟩ x₀ := by
          rw [hcar] at hpS
          obtain ⟨z, hz, hzp⟩ := hpS    -- z : ↥S'.carrier, hz : z < x₀, hzp : z.val = p
          -- ⟨p,hpS'⟩ = z (same val), so ⟨p,hpS'⟩ < x₀
          have : (⟨p, hpS'⟩ : S'.carrier.Elem) = z := Subtype.ext hzp.symm
          rw [this]; exact hz
        -- Step 2: q ∉ S.carrier ⇒ ¬ ⟨q,hqS'⟩ < x₀  ⇒  x₀ ≤ ⟨q,hqS'⟩
        have hq_ge : S'.ord.le x₀ ⟨q, hqS'⟩ := by
          by_contra hlt
          push_neg at hlt              -- hlt : ⟨q,hqS'⟩ < x₀
          apply hqnotS
          rw [hcar]                    -- goal: q ∈ Subtype.val '' {z | z < x₀}
          exact ⟨⟨q, hqS'⟩, hlt, rfl⟩
        -- Step 3: p < x₀ ≤ q  ⇒  p < q
        exact @lt_of_lt_of_le _ S'.ord.toPreorder _ _ _ hp_lt hq_ge
  have transfer : ∀ (S S' : WellOrderedSubset X), S ∈ C → S' ∈ C →
            ∀ (p q : X) (hpS : p ∈ S.carrier) (hqS : q ∈ S.carrier)
              (hpS' : p ∈ S'.carrier) (hqS' : q ∈ S'.carrier),
            S'.ord.le ⟨p,hpS'⟩ ⟨q,hqS'⟩ → S.ord.le ⟨p,hpS⟩ ⟨q,hqS⟩ := by
          intro S S' hS hS' p q hpS hqS hpS' hqS' hle
          rcases htotal ⟨S,hS⟩ ⟨S',hS'⟩ with h | h
          · rcases h with heq | hseg
            · subst heq; simpa using hle
            · obtain ⟨x₀, hcar, hcompat⟩ := hseg
              exact (hcompat ⟨p, hpS⟩ ⟨q, hqS⟩ hpS' hqS').mpr hle
          · rcases h with heq | hseg
            · subst heq; simpa using hle
            · obtain ⟨x₀, hcar, hcompat⟩ := hseg
              exact (hcompat ⟨p, hpS'⟩ ⟨q, hqS'⟩ hpS hqS).mp hle
  let ub : WellOrderedSubset X := {
    carrier := carrier'
    ord := {
      le := le'
      lt := lt'
      le_refl := by
        intro a
        unfold le'
        obtain ⟨S, hSC, haS⟩ := Set.mem_iUnion₂.mp a.property
        use S, hSC, haS, haS
        simp
      le_antisymm := by
        intro a b hab hba
        unfold le' at hab hba; simp at hab hba
        choose S₁ hC₁ ha₁ hb₁ hab₁ using hab
        choose S₂ hC₂ hb₂ ha₂ hba₂ using hba
        rcases htotal ⟨S₁, hC₁⟩ ⟨S₂, hC₂⟩ with hle₁ | hle₂
        · rcases hle₁ with heq₁ | hseg₁
          · simp_all
            subst heq₁
            have hantisymm := S₁.ord.le_antisymm ⟨a, ha₁⟩ ⟨b, hb₁⟩ hab₁ hba₂
            have hantisymm' := congrArg Subtype.val hantisymm; simp at hantisymm'
            exact SetCoe.ext hantisymm'
          · simp at hseg₁
            have hssubset₁ := WellOrderedSubset.IsInitialSegment.subset hseg₁
            simp at hssubset₁
            choose s₂ hsub₁ hiff using hseg₁
            specialize hiff ⟨a, ha₁⟩ ⟨b, hb₁⟩ (by exact Set.mem_preimage.mp ha₂) (by exact Set.mem_preimage.mp hb₂)
            have hab₂ := hiff.mp hab₁; simp at hab₂
            have hantisymm := S₂.ord.le_antisymm ⟨a, ha₂⟩ ⟨b, hb₂⟩ hab₂ hba₂
            have hantisymm' := congrArg Subtype.val hantisymm; simp at hantisymm'
            exact SetCoe.ext hantisymm'
        · rcases hle₂ with heq₂ | hseg₂
          · simp_all
            subst heq₂
            have hantisymm := S₂.ord.le_antisymm ⟨a, ha₁⟩ ⟨b, hb₁⟩ hab₁ hba₂
            have hantisymm' := congrArg Subtype.val hantisymm; simp at hantisymm'
            exact SetCoe.ext hantisymm'
          · simp at hseg₂
            have hssubset₂ := WellOrderedSubset.IsInitialSegment.subset hseg₂
            simp at hssubset₂
            choose s₂ hsub₁ hiff using hseg₂
            specialize hiff ⟨b, hb₂⟩ ⟨a, ha₂⟩ (by exact Set.mem_preimage.mp hb₁) (by exact Set.mem_preimage.mp ha₁)
            have hba₁ := hiff.mp hba₂; simp at hba₁
            have hantisymm := S₁.ord.le_antisymm ⟨a, ha₁⟩ ⟨b, hb₁⟩ hab₁ hba₁
            have hantisymm' := congrArg Subtype.val hantisymm; simp at hantisymm'
            exact SetCoe.ext hantisymm'
      le_trans := by
        intro a b c hab hbc
        unfold le' at hab hbc
        choose S₁ hC₁ ha₁ hb₁ hab₁ using hab
        choose S₂ hC₂ hb₂ hc₂ hbc₂ using hbc
        rcases htotal ⟨S₁, hC₁⟩ ⟨S₂, hC₂⟩ with hle₁ | hle₂
        · rcases hle₁ with heq₁ | hseg₁
          · simp_all
            subst heq₁
            use S₁, hC₁, ha₁, hc₂
            exact S₁.ord.le_trans _ _ _ hab₁ hbc₂
          · simp at hseg₁
            have hssubset₁ := WellOrderedSubset.IsInitialSegment.subset hseg₁
            simp at hssubset₁
            refine ⟨S₂, hC₂, hssubset₁.1 ha₁, hc₂, ?_⟩
            choose s₂ _ hiff₂ using hseg₁
            specialize hiff₂ ⟨a, ha₁⟩ ⟨b, hb₁⟩ (hssubset₁.1 ha₁) hb₂
            have hab₂ := hiff₂.mp hab₁; simp at hab₂
            exact S₂.ord.le_trans _ _ _ hab₂ hbc₂
        · rcases hle₂ with heq₂ | hseg₂
          · simp_all
            subst heq₂
            use S₂, hC₂, ha₁, hc₂
            exact S₂.ord.le_trans _ _ _ hab₁ hbc₂
          · simp at hseg₂
            have hssubset₂ := WellOrderedSubset.IsInitialSegment.subset hseg₂
            simp at hssubset₂
            refine ⟨S₁, hC₁, ha₁, hssubset₂.1 hc₂, ?_⟩
            choose s₁ _ hiff₁ using hseg₂
            specialize hiff₁ ⟨b, hb₂⟩ ⟨c, hc₂⟩ hb₁ (hssubset₂.1 hc₂)
            have hbc₁ := hiff₁.mp hbc₂
            exact S₁.ord.le_trans _ _ _ hab₁ hbc₁
      le_total := by
        intro a b
        unfold le'
        simp_all
        have ha := a.property
        have hb := b.property
        unfold carrier' at ha hb
        rw [Set.mem_iUnion₂] at ha hb
        choose C₁ hC₁ haC₁ using ha
        choose C₂ hC₂ hbC₂ using hb
        rcases htotal ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ with hle₁ | hle₂
        · rcases hle₁ with heq₁ | hseg₁
          · simp at heq₁
            subst heq₁
            simp_all
            rcases C₁.ord.le_total ⟨a, haC₁⟩ ⟨b, hbC₂⟩ with hab | hba
            · left; exact ⟨C₁, ⟨hC₂, ⟨haC₁, hbC₂, hab⟩⟩⟩
            · right; exact ⟨C₁, ⟨hC₂, ⟨hbC₂, haC₁, hba⟩⟩⟩
          · simp at hseg₁
            have hssubset₁ := WellOrderedSubset.IsInitialSegment.subset hseg₁
            simp at hssubset₁
            rcases C₂.ord.le_total ⟨a, hssubset₁.1 haC₁⟩ ⟨b, hbC₂⟩ with hab | hba
            · left; exact ⟨C₂, ⟨hC₂, ⟨hssubset₁.1 haC₁, hbC₂, hab⟩⟩⟩
            · right; exact ⟨C₂, ⟨hC₂, ⟨hbC₂, hssubset₁.1 haC₁, hba⟩⟩⟩
        · rcases hle₂ with heq₂ | hseg₂
          · simp at heq₂
            subst heq₂
            simp_all
            rcases C₂.ord.le_total ⟨a, haC₁⟩ ⟨b, hbC₂⟩ with hab | hba
            · left; exact ⟨C₂, ⟨hC₁, ⟨haC₁, hbC₂, hab⟩⟩⟩
            · right; exact ⟨C₂, ⟨hC₁, ⟨hbC₂, haC₁, hba⟩⟩⟩
          · simp at hseg₂
            have hssubset₂ := WellOrderedSubset.IsInitialSegment.subset hseg₂
            simp at hssubset₂
            rcases C₁.ord.le_total ⟨a, haC₁⟩ ⟨b, hssubset₂.1 hbC₂⟩ with hab | hba
            · left; exact ⟨C₁, ⟨hC₁, ⟨haC₁, hssubset₂.1 hbC₂, hab⟩⟩⟩
            · right; exact ⟨C₁, ⟨hC₁, ⟨hssubset₂.1 hbC₂, haC₁, hba⟩⟩⟩
      toDecidableLE := by exact Classical.decRel _
      lt_iff_le_not_ge := by
        intro a b
        unfold lt' le'
        constructor
        · intro hlt
          choose S hC haS hbS hlt using hlt
          constructor
          · refine ⟨S, hC, haS, hbS, ?_⟩
            exact @le_of_lt _ S.ord.toPreorder _ _ hlt
          · by_contra! h'
            obtain ⟨S', hC', hbS', haS', hle⟩ := h'
            rcases htotal ⟨S, hC⟩ ⟨S', hC'⟩ with hle | hle'
            · rcases hle with heq | hseg
              · simp at heq
                subst heq
                exact @not_lt_of_ge _ S.ord.toPreorder _ _ hle hlt
              · choose s hsub hiff using hseg
                specialize hiff ⟨b, hbS⟩ ⟨a, haS⟩ hbS' haS'
                have hle' := hiff.mpr hle
                exact @not_lt_of_ge _ S.ord.toPreorder _ _ hle' hlt
            · rcases hle' with heq' | hseg'
              · simp at heq'
                subst heq'
                exact @not_lt_of_ge _ S'.ord.toPreorder _ _ hle hlt
              · choose s' hsub' hiff' using hseg'
                specialize hiff' ⟨b, hbS'⟩ ⟨a, haS'⟩ hbS haS
                have hle' := hiff'.mp hle
                exact @not_lt_of_ge _ S.ord.toPreorder _ _ hle' hlt
        · rintro ⟨h1, h2⟩
          push_neg at h2
          obtain ⟨S, hC, hbS, haS, hle⟩ := h1
          specialize h2 S hC haS hbS
          refine ⟨S, hC, hbS, haS, ?_⟩
          exact h2
    }
    wf := by
      constructor
      show WellFounded lt'
      rw [WellFounded.wellFounded_iff_has_min]

      have transfer_lt :
          ∀ (S S' : WellOrderedSubset X), S ∈ C → S' ∈ C →
            ∀ (p q : X)
              (hpS : p ∈ S.carrier) (hqS : q ∈ S.carrier)
              (hpS' : p ∈ S'.carrier) (hqS' : q ∈ S'.carrier),
            S'.ord.lt ⟨p, hpS'⟩ ⟨q, hqS'⟩ → S.ord.lt ⟨p, hpS⟩ ⟨q, hqS⟩ := by
        intro S S' hS hS' p q hpS hqS hpS' hqS' hlt
        rcases htotal ⟨S, hS⟩ ⟨S', hS'⟩ with hle | hle
        · -- S ≤ S' : S = S' or S.IsInitialSegment S'
          rcases hle with heq | hseg
          · -- S = S' : same order, proof-irrelevant memberships
            simp at heq
            subst heq
            -- hlt : S.ord.lt ⟨p,hpS'⟩ ⟨q,hqS'⟩ ; goal same up to proof irrel
            simpa using hlt
          · -- hseg : S.IsInitialSegment S'.  compat is ≤-iff; derive < via lt_iff_le_not_ge.
            obtain ⟨x₀, hcar, hcompat⟩ := hseg
            refine (@lt_iff_le_not_ge _ S.ord.toPreorder _ _).mpr ⟨?_, ?_⟩
            · exact (hcompat ⟨p, hpS⟩ ⟨q, hqS⟩ hpS' hqS').mpr ((@lt_iff_le_not_ge _ S'.ord.toPreorder _ _).mp hlt).1
            · intro hcon
              exact ((@lt_iff_le_not_ge _ S'.ord.toPreorder _ _).mp hlt).2 ((hcompat ⟨q, hqS⟩ ⟨p, hpS⟩ hqS' hpS').mp hcon)
        · -- S' ≤ S : S' = S or S'.IsInitialSegment S
          rcases hle with heq | hseg
          · simp at heq
            subst heq
            simpa using hlt
          · -- hseg : S'.IsInitialSegment S.  Now S is the LARGER one.
            obtain ⟨x₀, hcar, hcompat⟩ := hseg
            simp at hcompat
            refine (@lt_iff_le_not_ge _ S.ord.toPreorder _ _).mpr ⟨?_, ?_⟩
            · have hle' := @le_of_lt _ S'.ord.toPreorder _ _ hlt
              exact (hcompat p hpS' q hqS' hpS hqS).mp hle'
            · intro hcon
              have hcon' := (hcompat q hqS' p hpS' hqS hpS).mpr hcon
              have := @lt_of_lt_of_le _ S'.ord.toPreorder _ _ _ hlt hcon'
              simp at this

      intro s hs
      obtain ⟨a₀, ha₀⟩ := hs
      obtain ⟨S, hSC, ha₀S⟩ := mem_carrier' a₀
      let incl : S.carrier.Elem → carrier'.Elem := fun z => ⟨z.val, Set.mem_biUnion hSC z.property⟩
      let s_S : Set S.carrier.Elem := incl ⁻¹' s
      have hs_S_ne : s_S.Nonempty :=
        ⟨⟨a₀.val, ha₀S⟩, by
          show incl ⟨a₀.val, ha₀S⟩ ∈ s
          -- incl ⟨a₀.val, ha₀S⟩ = a₀  by Subtype.ext rfl
          have : incl ⟨a₀.val, ha₀S⟩ = a₀ := Subtype.ext rfl
          rw [this]; exact ha₀⟩
      obtain ⟨m, hms_S, hm_min⟩ := S.wf.wf.has_min s_S hs_S_ne
      refine ⟨incl m, hms_S, ?_⟩
      intro x hxs hlt
      obtain ⟨T, hTC, hxT, hmT, hlt_T⟩ := hlt
      by_cases hxS : x.val ∈ S.carrier
      · have hx_sS : (⟨x.val, hxS⟩ : S.carrier.Elem) ∈ s_S := by
          show incl ⟨x.val, hxS⟩ ∈ s
          have : incl ⟨x.val, hxS⟩ = x := Subtype.ext rfl
          rw [this]; exact hxs
        have hlt_S : S.ord.lt ⟨x.val, hxS⟩ ⟨m.val, m.property⟩ :=
          transfer_lt S T hSC hTC x.val m.val hxS m.property hxT hmT hlt_T
        -- hm_min says ¬ S.ord.lt ⟨x.val,hxS⟩ m ; but m = ⟨m.val, m.property⟩
        exact hm_min ⟨x.val, hxS⟩ hx_sS (by
          -- ⟨m.val, m.property⟩ = m  by Subtype.eta / rfl
          simpa using hlt_S)
      · rcases htotal ⟨S, hSC⟩ ⟨T, hTC⟩ with hle | hle
        · -- S ≤ T in C.  Get S.IsInitialSegment T (S = T impossible: x ∈ T, x ∉ S).
          rcases hle with heq | hseg
          · -- S = T : then x.val ∈ T = S, contra hxS\
            simp at heq
            exact hxS (heq ▸ hxT)
          · -- hseg : S.IsInitialSegment T
            have hmT : m.val ∈ T.carrier := (WellOrderedSubset.IsInitialSegment.subset hseg).1 m.property -- NO: need m.val ∈ T, not x; fix below
            have hlt_mx : T.ord.lt ⟨m.val, hmT⟩ ⟨x.val, hxT⟩ := seg_lt S T hseg m.val x.val m.property hmT hxT hxS
            simp at hlt_T hlt_mx
            have := asymm hlt_mx
            exact this hlt_T
        · -- T ≤ S : then x.val ∈ T ⊆ S, contra hxS
          simp at hle
          have : x.val ∈ S.carrier := (WellOrderedSubset.le_subset hle) hxT
          exact hxS this
  }

  use ub
  intro c' hc'
  by_cases hfull : c'.carrier = carrier'
  · -- c' exhausts the union ⇒ c' = ub  (left disjunct)
    left
    obtain ⟨cc, cord, cwf⟩ := c'
    subst hfull
    congr 1
    apply LinearOrder.ext
    intro a b
    show cord.le a b ↔ le' a b
    constructor
    · intro hle
      exact ⟨⟨carrier', cord, cwf⟩, hc', a.2, b.2, hle⟩
    · rintro ⟨S, hSC, haS, hbS, hle⟩
      exact transfer ⟨carrier', cord, cwf⟩ S hc' hSC a.1 b.1 a.2 b.2 haS hbS hle
  · right
    -- IsInitialSegment c' ub : ∃ x₀ : ub.carrier, c'.carrier = val '' {z | z <_ub x₀} ∧ (orders agree)
    have hsub : c'.carrier ⊆ carrier' := fun x hx => Set.mem_biUnion hc' hx
    have hproper : c'.carrier ⊂ carrier' := ⟨hsub, fun h => hfull (hsub.antisymm h)⟩
    let diffSet : Set (carrier') := {z | z.1 ∉ c'.carrier}
    have hdiff_ne : diffSet.Nonempty := by
      choose k hk using Set.exists_of_ssubset hproper
      use ⟨k, hk.1⟩
      exact hk.2
    choose x₀ hx₉diff hx₀min using ub.wf.wf.has_min diffSet hdiff_ne
    refine ⟨x₀, ?_, ?_⟩
    · ext y; simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro hy
        refine ⟨⟨y, hsub hy⟩, ?_, rfl⟩
        show lt' ⟨y, hsub hy⟩ x₀
        obtain ⟨T, hTC, hx₀T⟩ := mem_carrier' x₀
        rcases htotal ⟨c', hc'⟩ ⟨T, hTC⟩ with hle | hle
        · rcases hle with heq | hseg
          · simp at heq
            exfalso; apply hx₉diff
            rw [heq]; exact hx₀T
          · -- c'.IsInitialSegment T : seg_lt gives y <_T x₀.1
            simp at hseg
            have hsub' := (WellOrderedSubset.IsInitialSegment.subset hseg).1 hy
            refine ⟨T, hTC, hsub' , hx₀T, ?_⟩
            · exact seg_lt c' T hseg y x₀.1 hy hsub' hx₀T hx₉diff
        · rcases hle with heq | hseg
          · simp at heq
            exfalso; apply hx₉diff
            rw [← heq]; exact hx₀T
          · exfalso; apply hx₉diff
            exact (WellOrderedSubset.IsInitialSegment.subset hseg).1 hx₀T
      · rintro ⟨z, hz_lt, rfl⟩
        by_contra hzc
        exact hx₀min z hzc hz_lt
    · intro a b ha hb
      show c'.ord.le a b ↔ le' ⟨a.1, ha⟩ ⟨b.1, hb⟩
      constructor
      · intro hle
        exact ⟨c', hc', a.2, b.2, hle⟩
      · rintro ⟨S, hSC, haS, hbS, hle⟩
        exact transfer c' S hc' hSC a.1 b.1 a.2 b.2 haS hbS hle



/-- The well-ordering principle: every set has a well-ordering. -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by
  haveI : Nonempty (WellOrderedSubset X) := ⟨WellOrderedSubset.empty X⟩
  choose M hM using Zorns_lemma (X:= WellOrderedSubset X) chain_WellOrderedSubset
  have hfull := (WellOrderedSubset.isMax_iff_full X _).mp hM
  have hmem : ∀ x : X, x ∈ M.carrier := by
    rw [hfull]; tauto
  let f : X → M.carrier := fun x => ⟨x, hmem x⟩
  have hf : Function.Injective f := by
    intro a b hab
    unfold f at hab
    simp at hab
    exact hab
  use @LinearOrder.lift' X M.carrier M.ord f hf
  constructor
  exact InvImage.wf f M.wf.wf


/-- Well-ordering principle implies axiom of choice. Well-order the disjoint union
`Σ i, X i`, then pick the minimum of each fiber. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) :
    Nonempty (∀ i, X i) := by
    obtain ⟨l, hl⟩ := hwo (Σ i, X i)
    set S : I → Set (Σ i, X i) := fun i => {p | p.1 = i} with hS_def
    have hSne : ∀ i, (S i).Nonempty := by
      intro i
      unfold S
      have := hne i
      obtain ⟨s⟩ := this
      use ⟨i, s⟩
      simp
    constructor
    intro i
    have hmem : (hl.wf.min (S i) (hSne i)) ∈ S i := hl.wf.min_mem (S i) (hSne i)
    unfold S at hmem
    rw [Set.mem_setOf_eq] at hmem
    change (hl.wf.min (S i) (hSne i)).1 = i at hmem
    exact (congrArg X hmem).mp (hl.wf.min (S i) (hSne i)).2

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by
    let P := {Ω' : Set (Set X) | Ω' ⊆ Ω ∧ Ω'.Pairwise Disjoint}
    have chain_P : ∀ C : Set (P), IsTotal C ∧ C.Nonempty → ∃ ub, IsUpperBound C ub := by
      intro C ⟨htotal, hnonemp⟩
      let ub : Set (Set X) := ⋃ c ∈ C, c.val
      have hmem : ub ⊆ Ω := by
        intro b hb
        unfold ub at hb
        rw [Set.mem_iUnion₂] at hb
        choose S hS hbS using hb
        have := S.property
        unfold P at this
        have := this.1
        exact Set.mem_of_subset_of_mem this hbS
      have hpwdisj : ub.Pairwise Disjoint := by
        intro A hA B hB hAB
        unfold ub at hA hB
        rw [Set.mem_iUnion] at hA hB
        choose A' φA hA' hφA using hA
        choose B' φB hB' hφB using hB
        simp at hA' hB'
        have hPA' := A'.property
        have hPB' := B'.property
        obtain ⟨_, hpairA⟩ := hPA'
        obtain ⟨_, hpairB⟩ := hPB'
        rcases htotal ⟨A', hA'.1⟩ ⟨B', hB'.1⟩ with hAle | hBle
        · simp at hAle
          refine hpairB (hAle ?_) ?_ hAB
          · simp
            rwa [← hA'.2] at hφA
          · rwa [← hB'.2] at hφB
        · simp at hBle
          refine hpairA ?_ (hBle ?_) hAB
          · rwa [← hA'.2] at hφA
          · rwa [← hB'.2] at hφB
      use ⟨ub, ⟨hmem, hpwdisj⟩⟩
      intro ⟨a, ha⟩ haC
      show a ⊆ ub
      unfold ub
      intro x hx
      rw [Set.mem_iUnion₂]
      use ⟨a, ha⟩
    haveI : Nonempty P := by
      use ∅
      unfold P; constructor
      · exact Set.empty_subset Ω
      · exact Set.pairwise_empty Disjoint
    choose m hm using Zorns_lemma chain_P
    refine ⟨m, ?_, ?_, ?_⟩
    · exact m.property.1
    · exact m.property.2
    · intro C hCΩ
      by_contra! h'
      have hCdisj : ∀ A ∈ m.val, Disjoint C A := by
        intro A hAΩ'
        rw [Set.disjoint_iff_inter_eq_empty]
        exact h' A hAΩ'
      have hstillΩ : insert C m.val ⊆ Ω := by
        intro S hS
        rcases hS with rfl | h
        · exact hCΩ
        · have := m.property
          unfold P at this
          have := this.1
          tauto
      have hstilldisj : (insert C m.val).Pairwise Disjoint := by
        intro A hA B hB hAB
        rcases hA with rfl | hA <;> rcases hB with rfl | hB
        · exfalso; grind
        · exact hCdisj B hB
        · specialize hCdisj A hA
          exact hCdisj.symm
        · exact m.property.2 hA hB hAB
      have hle : m ≤ ⟨insert C m, hstillΩ, hstilldisj⟩ := by
        show m.val ⊆ insert C m
        simp
      have := hm hle
      change insert C m.val ⊆ m.val at this
      have hCemp : C = ∅ := by
        have hCmem := this (Set.mem_insert C ↑m)
        rw [← Set.inter_self C]
        exact h' C hCmem
      rw [hCemp] at hCΩ
      exact hne hCΩ


/-- The maximal disjoint subcollection property implies Exercise 8.4.2, hence is
equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by

    -- Chapter8.maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    -- ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧ ∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty
    set Ω : Set (Set (I ⊕ U)) := { P | ∃ α, ∃ u ∈ X α, P = {Sum.inl α, Sum.inr u} } with hΩ
    have hemptynotΩ : ∅ ∉ Ω := by
      by_contra! h
      unfold Ω at h
      simp at h
      choose i u huxi hempty using h
      have hmem : Sum.inl i ∈ ({Sum.inl i, Sum.inr u} : Set (I ⊕ U)) := by tauto
      rw [← hempty] at hmem
      simp at hmem
    specialize hmds _ Ω hemptynotΩ
    choose Ω' hsub hdisj hnon using hmds
    set Ω₀ := Sum.inr ⁻¹' (⋃₀ Ω')
    use Ω₀
    intro i
    obtain ⟨u₀, hu₀⟩ := hne i
    set C : Set (I ⊕ U) := {Sum.inl i, Sum.inr u₀}
    have hCΩ : C ∈ Ω := by
      unfold C Ω
      simp
      use i, u₀
    choose A hAΩ' hCAnon using hnon _ hCΩ
    obtain ⟨β, v, hv, hAeq⟩ := hsub hAΩ'
    obtain ⟨x, hxC, hxA⟩ := hCAnon
    unfold C at hxC
    rw [hAeq] at hxA
    have hiβ : i = β := by
      rcases hxC with hl₁ | hr₁ <;> rcases hxA with hl₂ | hr₂
      · rw [hl₁] at hl₂
        simpa using hl₂
      · simp at hr₂
        rw [hl₁] at hr₂
        simp at hr₂
      · simp at hr₁
        rw [hl₂] at hr₁
        simp at hr₁
      · simp at hr₁ hr₂
        rw [hr₁] at hr₂
        simp at hr₂
        rw [hr₂] at hu₀
        by_contra! h'
        have hdisj : Disjoint (X i) (X β) := by
          apply h
          · tauto
          · tauto
          · exact h'
        have hnotdisj : ¬ Disjoint (X i) (X β) := by
          rw [Set.disjoint_left]
          push_neg
          use v
        exact absurd hdisj hnotdisj
    subst hiβ
    have hset : Ω₀ ∩ X i = {v} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      constructor
      · constructor
        · unfold Ω₀
          simp
          use A; constructor
          · tauto
          · rw [hAeq]
            tauto
        · exact hv
      · intro z ⟨hzΩ₀, hzXi⟩
        unfold Ω₀ at hzΩ₀
        obtain ⟨B, hBΩ', hzB⟩ := hzΩ₀
        obtain ⟨γ, w, hw, hBeq⟩ := hsub hBΩ'
        have hiγ : i = γ := by
          rw [hBeq] at hzB
          simp at hzB
          rw [← hzB] at hw
          by_contra! h'
          have hdisj : Disjoint (X i) (X γ) := by
            apply h
            · tauto
            · tauto
            · exact h'
          have hnotdisj : ¬ Disjoint (X i) (X γ) := by
            rw [Set.disjoint_left]
            push_neg
            use z
          exact absurd hdisj hnotdisj
        have hAB : A = B := by
          by_contra! hAB'
          have hdisj' := hdisj (by tauto) (by tauto) hAB'
          have hmem' : Sum.inl i ∈ A := by
            rw [hAeq]; simp
          have hmem'' : Sum.inl i ∈ B := by
            rw [hiγ,  hBeq]; simp
          rw [Set.disjoint_left] at hdisj'
          apply hdisj' _ hmem''
          exact hmem'
        rw [hAeq, hBeq, hiγ] at hAB
        have hvw : v = w := by grind
        rw [hvw]
        rw [← hiγ] at hw
        rw [hBeq] at hzB
        simp at hzB
        exact hzB
    rw [hset]
    simp

end Chapter8
