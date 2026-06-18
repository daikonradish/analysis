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
  choose kmin hmin using hhasmin _ hnonempty
  choose k₀ hle hnotPk₀ using kmin.property
  rcases hle.eq_or_lt with heq | hlt
  · have hall : ∀ j < kmin.val, P j := by
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
  · have hin : k₀ ∈ Y := by
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
example {X:Type} [PartialOrder X] {Y Y':Set X} (hY: IsTotal Y) (hY': IsTotal Y') (hY_well: WellFoundedLT Y) (hY'_well: WellFoundedLT Y') (hYY': IsTotal (Y ∪ Y': Set X)) : WellFoundedLT (Y ∪ Y': Set X) := by sorry

/-- Lemma 8.5.14-/
theorem WellFoundedLT.partialOrder {X:Type} [PartialOrder X] (x₀ : X) : ∃ Y : Set X, IsTotal Y ∧ WellFoundedLT Y ∧ (∃ hx₀ : x₀ ∈ Y, IsMin (⟨ x₀, hx₀ ⟩: Y)) ∧ ¬ ∃ x, IsStrictUpperBound Y x := by
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
    /-  have hdiff (Y : Ω) (Y' : Ω) (d : X) (hY : d ∈ (Y:Set X)) (hY' : d ∉ (Y':Set X))
      (hd : d ≠ x₀) (hagree : ∀ c, c < d → (c ∈ (Y:Set X) ↔ c ∈ (Y':Set X))) :
      IsStrictUpperBound (Y': Set X) d := by
      choose hYtotal hYwell hYx₀ hYmin using Y.val.property
      choose hY'total hY'well hY'x₀ hY'min using Y'.val.property
      rw [IsStrictUpperBound.iff]
      intro y hy
      by_contra h'
      have hdYx₀ : d ∈ (Y:Set X) \ {x₀} := by
        constructor
        · exact hY
        · simp; exact hd
      have hdFY : d = s (F Y.val d) := by
        apply Y.property
        exact hdYx₀
      have hpredecessor : F Y.val d = {c ∈ (Y:Set X) | c < d} := by
        have := hF hdYx₀
        exact this
      have hchain : {c ∈ (Y:Set X) | c < d} = {c ∈ (Y':Set X) | c < d} := by
        ext c
        simp
        intro hc
        specialize hagree c hc
        exact hagree
      set _Y'lin := LinearOrder.mk hY'total
      set Z : Set (Y':Set X) := { q | d ≤ q.val }
      have hZnonempty : Z.Nonempty := by

        use ⟨y, hy⟩
        unfold Z; simp
        sorry
      -/



    have hinter (Y : Ω) (Y' : Ω) : (Y : Set X) ∩ Y' ∈ Ω₀ := by
      choose hYtotal hYwell hYx₀ hYmin using Y.val.property
      choose hY'total hY'well hY'x₀ hY'min using Y'.val.property
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro ⟨a, haY, haY'⟩ ⟨b, hbY, hbY'⟩
        simp
        exact hYtotal ⟨a, haY⟩ ⟨b, hbY⟩
      · haveI : WellFoundedLT (Y : Set X) := hYwell
        apply WellFoundedLT.subset (A := (Y : Set X)) (B := _)
        · exact hYtotal
        · intro y hy; simp at hy; tauto
      · tauto
      · intro y hy
        simp at hy
        specialize hYmin y hy.1
        exact hYmin


    have hY := Y.val.property
    have hY' := Y'.val.property
    have hYΩ := Y.property
    have hY'Ω := Y'.property
    choose hYtotal hYwell hYx₀ hYmin using hY
    choose hY'total hY'well hY'x₀ hY'min using hY'
    set Y'' : Set X := (Y:Set X) ∩ Y'
    have hY'' : Y'' ∈ Ω₀ := by
      unfold Y'' Ω₀
      refine ⟨?_, ?_, ?_, ?_⟩
      ·
        sorry
      · sorry
      · sorry
      · sorry
    sorry


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
    sorry
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
    sorry
  have hY_inftyΩ₀ : Y_infty ∈ Ω₀ := by
    sorry
  set sY_infty : X := s ⟨ _, hY_inftyΩ₀ ⟩
  have hYs_total : IsTotal (Y_infty ∪ {sY_infty} : Set X) := by
    sorry
  have hYs_well : WellFoundedLT (Y_infty ∪ {sY_infty} : Set X) := by
    sorry
  have hYs_mem : x₀ ∈ Y_infty ∪ {sY_infty} := by sorry
  have hYs_min : ∀ x ∈ Y_infty ∪ {sY_infty}, x₀ ≤ x := by sorry
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


/-- Lemma 8.5.15 (Zorn's lemma) / Exercise 8.5.14 -/
theorem Zorns_lemma {X:Type} [PartialOrder X] [Nonempty X]
  (hchain: ∀ Y:Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) : ∃ x:X, IsMax x := by
  by_contra! h'
  have hstrict (A : Set X) (hex : ∃ x, IsUpperBound A x) :  ∃ x, IsStrictUpperBound A x := by
    choose B hB using hex
    have hnotmax := h' B; simp at hnotmax
    choose b hb using hnotmax
    use b
    rw [IsUpperBound.iff] at hB
    rw [IsStrictUpperBound.iff]
    intro a ha
    have := hB ha
    exact lt_of_le_of_lt (hB ha) hb
  obtain ⟨x₀⟩ :=  ‹Nonempty X›
  choose Y hYtotal hYwell hmin hnonstrict using WellFoundedLT.partialOrder x₀
  have hYx₀ : x₀ ∈ Y := by exact hmin.choose
  have hYnonempty : Y.Nonempty := by use x₀
  have h₁ := hchain Y ⟨hYtotal, hYnonempty⟩
  have h₂ := hstrict Y h₁
  exact hnonstrict h₂

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
  sorry

example {Y:Type} [LinearOrder Y] {x y:Y} (hx: IsMax x) (hy: IsMax y) : x = y := by
 sorry

/-- Exercise 8.5.9 -/
example {X:Type} [LinearOrder X] (hmin: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMin x) (hmax: ∀ Y: Set X, Y.Nonempty → ∃ x:Y, IsMax x) : Finite X := by sorry


/-- Exercise 8.5.12.  Here we make a copy of Mathlib's {name}`Lex` wrapper for lexicographical orderings.  This wrapper is needed
because products `X × Y` of ordered sets are given the default instance of the product partial order instead of
the lexicographical one. -/
def Lex' (α : Type) := α

instance Lex'.partialOrder {X Y: Type} [PartialOrder X] [PartialOrder Y] : PartialOrder (Lex' (X × Y)) := {
  le := fun ⟨ x, y ⟩ ⟨ x', y' ⟩ ↦ (x < x') ∨ (x = x' ∧ y ≤ y')
  le_refl := by sorry
  le_antisymm := by sorry
  le_trans := by sorry
}

instance Lex'.linearOrder {X Y:Type} [LinearOrder X] [LinearOrder Y] : LinearOrder (Lex' (X × Y)) := by sorry

instance Lex'.WellFoundedLT {X Y:Type} [LinearOrder X] [WellFoundedLT X] [LinearOrder Y] [WellFoundedLT Y]:
  WellFoundedLT (Lex' (X × Y)) := by sorry


/-- Exercise 8.5.15 -/
theorem inj_trichotomy {X Y : Type}
    (h : ¬∃ f : X → Y, Function.Injective f) :
    ∃ g : Y → X, Function.Injective g := by sorry

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
    PartialOrder.discrete X ≤ p := by sorry

theorem PartialOrder.discrete_isMin (X : Type) :
    @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE
      (PartialOrder.discrete X) := by sorry

theorem PartialOrder.discrete_unique_min (X : Type) (p : PartialOrder X)
    (h : @IsMin (PartialOrder X) (coarserOrder X).toPreorder.toLE p) :
    p = discrete X := by sorry

/-- A partial ordering is maximal in the coarser order iff it is total. -/
theorem PartialOrder.isMax_iff_isTotal (X : Type) (p : PartialOrder X) :
    @IsMax (PartialOrder X) (coarserOrder X).toPreorder.toLE p ↔
    @IsTotal X p := by sorry

/-- Any partial ordering extends to a total ordering (by Zorn's lemma). -/
theorem PartialOrder.extends_to_total (X : Type) (p : PartialOrder X) :
    ∃ q : PartialOrder X, p ≤ q ∧ @IsTotal X q := by sorry

/-- Exercise 8.5.17: Use Zorn's lemma to reprove Exercise 8.4.2 -/
theorem exists_set_singleton_intersect' {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

/-- Exercise 8.5.18 -/
theorem hausdorff_of_zorns_lemma {X : Type} [PartialOrder X] :
    ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M := by sorry

theorem zorns_lemma_of_hausdorff {X : Type} [PartialOrder X] [Nonempty X]
    (hhausdorff : ∃ M : Set X, Maximal (fun (S : Set X) => IsTotal S) M)
    (hchain : ∀ Y : Set X, IsTotal Y ∧ Y.Nonempty → ∃ x, IsUpperBound Y x) :
    ∃ x : X, IsMax x := by sorry

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
    W.carrier ⊂ W'.carrier := by sorry

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
  le_trans := by sorry

/-- The empty well-ordered subset. -/
def WellOrderedSubset.empty (X : Type) : WellOrderedSubset X where
  carrier := ∅
  ord := { PartialOrder.discrete (∅ : Set X) with
    le_total := fun ⟨_, h⟩ ↦ h.elim
    toDecidableLE := fun ⟨_, h⟩ ↦ h.elim }
  wf := ⟨⟨fun ⟨_, h⟩ ↦ h.elim⟩⟩

theorem WellOrderedSubset.empty_isMin (X : Type) :
    @IsMin (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE
      (empty X) := by sorry

/-- The maximal elements are precisely the well-orderings of all of X. -/
theorem WellOrderedSubset.isMax_iff_full (X : Type) (W : WellOrderedSubset X) :
    @IsMax (WellOrderedSubset X) (instPartialOrder X).toPreorder.toLE W ↔
    W.carrier = Set.univ := by sorry

/-- The well-ordering principle: every set has a well-ordering. -/
theorem well_ordering_principle (X : Type) :
    ∃ (l : LinearOrder X), @WellFoundedLT X l.toLT := by sorry

/-- Well-ordering principle implies axiom of choice. Well-order the disjoint union
`Σ i, X i`, then pick the minimum of each fiber. -/
theorem axiom_of_choice_of_well_ordering
    (hwo : ∀ T : Type, ∃ (l : LinearOrder T), @WellFoundedLT T l.toLT)
    {I : Type} {X : I → Type} (hne : ∀ i, Nonempty (X i)) :
    Nonempty (∀ i, X i) := by sorry

/-- Exercise 8.5.20 -/
theorem maximal_disjoint_subcollection {X : Type} (Ω : Set (Set X)) (hne : ∅ ∉ Ω) :
    ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
      (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty) := by sorry

/-- The maximal disjoint subcollection property implies Exercise 8.4.2, hence is
equivalent to the axiom of choice. -/
theorem exists_set_singleton_intersect_of_maximal_disjoint
    (hmds : ∀ (X : Type) (Ω : Set (Set X)), ∅ ∉ Ω →
      ∃ Ω' ⊆ Ω, Ω'.Pairwise Disjoint ∧
        (∀ C ∈ Ω, ∃ A ∈ Ω', (C ∩ A).Nonempty))
    {I U : Type} {X : I → Set U}
    (h : Set.PairwiseDisjoint .univ X) (hne : ∀ α, Nonempty (X α)) :
    ∃ Y : Set U, ∀ α, Nat.card (Y ∩ X α : Set U) = 1 := by sorry

end Chapter8
