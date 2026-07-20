import Mathlib.Tactic
import Analysis.Section_3_1

/-!
# Analysis I, Section 3.2: Russell's paradox

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

This section is mostly optional, though it does make explicit the axiom of foundation which is
used in a minor role in an exercise in Section 3.5.

Main constructions and results of this section:

- Russell's paradox (ruling out the axiom of universal specification).
- The axiom of regularity (foundation) - an axiom designed to avoid Russell's paradox.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter3

export SetTheory (Set Object)

variable [SetTheory]

/-- Axiom 3.8 (Universal specification) -/
abbrev axiom_of_universal_specification : Prop :=
  ∀ P : Object → Prop, ∃ A : Set, ∀ x : Object, x ∈ A ↔ P x

theorem Russells_paradox : ¬ axiom_of_universal_specification := by
  -- This proof is written to follow the structure of the original text.
  intro h
  set P : Object → Prop := fun x ↦ ∃ X:Set, x = X ∧ x ∉ X
  choose Ω hΩ using h P
  by_cases h: (Ω:Object) ∈ Ω
  . have : P (Ω:Object) := (hΩ _).mp h
    obtain ⟨ Ω', ⟨ hΩ1, hΩ2⟩ ⟩ := this
    simp at hΩ1
    rw [←hΩ1] at hΩ2
    contradiction
  have : P (Ω:Object) := by use Ω
  rw [←hΩ] at this
  contradiction

/-- Axiom 3.9 (Regularity) -/
theorem SetTheory.Set.axiom_of_regularity {A:Set} (h: A ≠ ∅) :
    ∃ x:A, ∀ S:Set, x.val = S → Disjoint S A := by
  choose x h h' using regularity_axiom A (nonempty_def h)
  use ⟨x, h⟩
  intro S hS; specialize h' S hS
  rw [disjoint_iff, eq_empty_iff_forall_notMem]
  contrapose! h'; simp at h'
  aesop

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the empty set.
-/
theorem SetTheory.Set.emptyset_exists (h: axiom_of_universal_specification):
    ∃ (X:Set), ∀ x, x ∉ X := by
  set P : Object → Prop := fun _ => False
  have := h P
  unfold P at this
  simp at this
  exact this

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the singleton set.
-/
theorem SetTheory.Set.singleton_exists (h: axiom_of_universal_specification) (x:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x := by
  set P : Object → Prop := fun y => y = x
  exact h P

/--
  Exercise 3.2.1.  The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the pair set.
-/
theorem SetTheory.Set.pair_exists (h: axiom_of_universal_specification) (x₁ x₂:Object):
    ∃ (X:Set), ∀ y, y ∈ X ↔ y = x₁ ∨ y = x₂ := by
  set P : Object → Prop := fun y =>  y = x₁ ∨ y = x₂
  exact h P

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the union operation.
-/
theorem SetTheory.Set.union_exists (h: axiom_of_universal_specification) (A B:Set):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ z ∈ A ∨ z ∈ B := by
  set P : Object → Prop := fun y => y ∈ A ∨ y ∈ B
  exact h P

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the specify operation.
-/
theorem SetTheory.Set.specify_exists (h: axiom_of_universal_specification) (A:Set) (P: A → Prop):
    ∃ (Z:Set), ∀ z, z ∈ Z ↔ ∃ h : z ∈ A, P ⟨ z, h ⟩ := by
  set P' : Object → Prop := fun x => ∃ h : x ∈ A , P ⟨x, h⟩
  exact h P'

/--
  Exercise 3.2.1. The spirit of the exercise is to establish these results without using either
  Russell's paradox, or the replace operation.
-/
theorem SetTheory.Set.replace_exists (h: axiom_of_universal_specification) (A:Set)
  (P: A → Object → Prop) (hP: ∀ x y y', P x y ∧ P x y' → y = y') :
    ∃ (Z:Set), ∀ y, y ∈ Z ↔ ∃ a : A, P a y := by
  set P' : Object → Prop := fun x => ∃ a : A, P a x
  exact h P'

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_self (A:Set) : (A:Object) ∉ A := by
  set A' : Set := {(A : Object)}
  have h_non_empty : A' ≠ ∅ := by
    have ha: (A:Object) ∈ A' := by rw [mem_singleton];
    exact nonempty_of_inhabited ha
  have h := axiom_of_regularity h_non_empty
  choose x hx using h
  have hx' : (x:Object) ∈ A' := by aesop
  change (x:Object) ∈ {set_to_object A} at hx'
  rw [mem_singleton] at hx'
  rw [hx'] at hx
  simp at hx
  rw [disjoint_iff] at hx
  unfold A' at hx
  rw [eq_empty_iff_forall_notMem] at hx
  contrapose! hx
  use A; simp
  exact (mem_coe A (set_to_object A)).mp hx

/-- Exercise 3.2.2 -/
theorem SetTheory.Set.not_mem_mem (A B:Set) : (A:Object) ∉ B ∨ (B:Object) ∉ A := by
  set U : Set := {(A:Object), (B:Object)}
  have hAU : (A:Object) ∈ U := by unfold U; simp
  have hUnon : U ≠ ∅ := by
    unfold U
    exact nonempty_of_inhabited hAU
  have h := axiom_of_regularity hUnon
  unfold U at h
  simp at h
  rcases h with h | h
  · rw [disjoint_iff, eq_empty_iff_forall_notMem] at h
    right
    specialize h B
    contrapose! h
    rw [mem_inter]; constructor
    · exact h
    · simp
  · rw [disjoint_iff, eq_empty_iff_forall_notMem] at h
    left
    specialize h A
    contrapose! h
    rw [mem_inter]; constructor
    · exact h
    · simp


/-- Exercise 3.2.3 -/
theorem SetTheory.Set.univ_iff : axiom_of_universal_specification ↔
  ∃ (U:Set), ∀ x, x ∈ U := by
  constructor
  · intro h
    set P : Object → Prop := fun _ => True
    choose U hU using h P
    use U
    intro x
    specialize hU x
    unfold P at hU
    simpa using hU
  · intro h
    choose U hU using h
    unfold axiom_of_universal_specification
    intro P
    set P' : U → Prop := fun x => P x
    use specify U P'
    intro x
    unfold P'
    have := hU x
    apply specification_axiom' P' ⟨x, this⟩

/-- Exercise 3.2.3 -/
theorem SetTheory.Set.no_univ : ¬ ∃ (U:Set), ∀ (x:Object), x ∈ U := by
  by_contra! h
  choose U hU using h
  specialize hU U
  exact absurd hU (not_mem_self U)


end Chapter3
