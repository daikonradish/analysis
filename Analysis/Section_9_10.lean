import Mathlib.Tactic
/-!
# Analysis I, Section 9.10: Limits at infinity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Bare-bones API for the Mathlib versions of adherent at infinity, and limits at infinity.
-/

namespace Chapter9

/-- Definition 9.10.1 (Infinite adherent point).  We use {lean}`¬ BddAbove X` as our notation for `+∞` being an adherent point -/
theorem BddAbove.unbounded_iff (X:Set ℝ) : ¬ BddAbove X ↔ ∀ M, ∃ x ∈ X, x > M := by
  simp [bddAbove_def]

theorem BddAbove.unbounded_iff' (X:Set ℝ) : ¬ BddAbove X ↔ sSup ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊤ := by
  erw [sSup_eq_top, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, ⟨x, hx, rfl⟩; revert M; simp [EReal.forall]; tauto
  intro h M; specialize h (M:EReal) (EReal.coe_lt_top M)
  obtain ⟨_, ⟨x, hx, rfl⟩, hMx⟩ := h; exact ⟨x, hx, EReal.coe_lt_coe_iff.mp hMx⟩

theorem BddBelow.unbounded_iff (X:Set ℝ) : ¬ BddBelow X ↔ ∀ M, ∃ x ∈ X, x < M := by
  simp [bddBelow_def]

theorem BddBelow.unbounded_iff' (X:Set ℝ) : ¬ BddBelow X ↔ sInf ((fun x:ℝ ↦ (x:EReal)) '' X) = ⊥ := by
  simp [sInf_eq_bot, unbounded_iff]
  constructor
  . intro h M hM; choose x hx hxM using h M.toReal
    use x, hx; revert M; simp [EReal.forall]
  intro h M; specialize h (M:EReal) ?_ <;>simp_all

/-- Definition 9.10.13 (Limit at infinity) -/
theorem Filter.Tendsto.AtTop.iff {X: Set ℝ} (f:ℝ → ℝ) (L:ℝ) : Filter.Tendsto f (.atTop ⊓ .principal X) (nhds L) ↔ ∀ ε > (0:ℝ), ∃ M, ∀ x ∈ X ∩ .Ici M, |f x - L| < ε := by
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  simp [Filter.eventually_inf_principal]
  aesop

/-- Exercise 9.10.4 -/
example : Filter.Tendsto (fun x:ℝ ↦ 1/x) (.atTop ⊓ .principal (.Ioi 0)) (nhds 0) := by
  rw [Filter.Tendsto.AtTop.iff]
  intro ε hε
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
  simp only [sub_zero]
  use 2 / ε
  intro x hx
  obtain ⟨hx0, hxε⟩ := hx
  rw [abs_of_pos (by positivity)]
  field_simp at hxε ⊢
  linarith

open Classical in
/-- Exercise 9.10.1 -/
example (a:ℕ → ℝ) (L:ℝ) : Filter.Tendsto (fun x:ℝ ↦ (if h:(∃ n:ℕ, x = n) then a h.choose else 0)) (.atTop ⊓ .principal ((fun n:ℕ ↦ (n:ℝ)) '' .univ)) (nhds L) ↔ Filter.atTop.Tendsto a (nhds L) := by
  constructor
  . intro htt
    rw [Filter.Tendsto.AtTop.iff] at htt
    rw [Metric.tendsto_atTop]
    intro ε hε
    choose M hM using htt ε hε
    use ⌈M⌉₊
    intro n hn
    specialize hM n (by simp; exact Nat.ceil_le.mp hn)
    rw [dif_pos (by use n)] at hM
    simp at hM
    rwa [Real.dist_eq]
  . intro htt
    rw [Metric.tendsto_atTop] at htt
    rw [Filter.Tendsto.AtTop.iff]
    intro ε hε
    choose N hN using htt ε hε
    use N
    intro x hx; simp at hx
    obtain ⟨hexist, hxN⟩ := hx
    choose y hy using hexist
    have h : ∃ (n:ℕ), x = n := by use y; exact hy.symm
    -- lol it's like hunting rabbits
    rw [dif_pos h]
    have := h.choose_spec
    specialize hN y (by simp; rw [← hy] at hxN; simpa using hxN)
    -- now we're playing whackamole
    rw [Real.dist_eq] at hN
    rw [this] at hy
    norm_cast at hy
    rw [← hy]
    exact hN

end Chapter9
