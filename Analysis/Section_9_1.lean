import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Analysis.Section_6_4
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/
open Classical

variable (I : Type*)

/- Definition 9.1.1 (Intervals) -/
#check Set.Icc_def
#check Set.Ico_def
#check Set.Ioc_def
#check Set.Ioo_def
#check Set.Ici_def
#check Set.Ioi_def
#check Set.Iic_def
#check Set.Iio_def

#check EReal.image_coe_Icc
#check EReal.image_coe_Ico
#check EReal.image_coe_Ioc
#check EReal.image_coe_Ioo
#check EReal.image_coe_Ici
#check EReal.image_coe_Ioi
#check EReal.image_coe_Iic
#check EReal.image_coe_Iio

/-- Example 9.1.4 -/
example {a b: EReal} (h: a > b) : Set.Icc a b = ∅ := by
  exact Set.Icc_eq_empty_of_lt h

example {a b: EReal} (h: a ≥ b) : Set.Ico a b = ∅ := by
  exact Set.Ico_eq_empty_of_le h

example {a b: EReal} (h: a ≥ b) : Set.Ioc a b = ∅ := by
  exact Set.Ioc_eq_empty_of_le h

example {a b: EReal} (h: a ≥ b) : Set.Ioo a b = ∅ := by
  exact Set.Ioo_eq_empty_of_le h

example {a b: EReal} (h: a = b) : Set.Icc a b = {a} := by
  rw [Set.Icc_eq_singleton_iff]; constructor
  · rfl
  · exact h.symm

/--
Definition 9.1.5.  Note that a slightly different {name}`Real.Adherent` was defined in
Chapter 6.4
-/
abbrev Real.adherent' (ε:ℝ) (x:ℝ) (X: Set ℝ) := ∃ y ∈ X, |x - y| ≤ ε

/-- Example 9.1.7 -/
example : (0.5:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  unfold Real.adherent'
  use 0.9
  constructor <;> norm_num

example : ¬ (0.1:ℝ).adherent' 1.1 (.Ioo 0 1) := by
  push_neg
  intro y ⟨h1, h2⟩
  rw [abs_of_pos (by linarith)]
  linarith

example : (0.5:ℝ).adherent' 1.1 {1,2,3} := by
  use 1; simp
  norm_num


namespace Chapter9

/-- Definition 9.1.8 (Adherent points). -/
abbrev AdherentPt (x:ℝ) (X:Set ℝ) := ∀ ε > (0:ℝ), ε.adherent' x X

example : AdherentPt 1 (.Ioo 0 1) := by
  intro ε hε
  unfold Real.adherent'
  use 1-(min ε 1)/2
  constructor
  · simp; constructor
    · by_cases! hε1 : ε ≤ 1
      · have hmin : min ε 1 = ε := by grind
        rw [hmin]
        linarith
      · have hmin : min ε 1 = 1 := by grind
        rw [hmin]
        norm_num
    · exact hε
  · rw [abs_of_nonneg]
    · simp
      by_cases! hε1 : ε ≤ 1
      · have hmin : min ε 1 = ε := by grind
        rw [hmin]; linarith
      · have hmin : min ε 1 = 1 := by grind
        rw [hmin]; linarith
    · simp
      suffices 0 ≤ min ε 1 by linarith
      apply le_min <;> linarith

example : ¬ AdherentPt 2 (.Ioo 0 1) := by
  intro had
  specialize had 1 (by positivity)
  unfold Real.adherent' at had
  contrapose! had
  intro y ⟨hy0, hy1⟩
  rw [abs_of_pos (by linarith)]
  linarith

/-- Definition 9.1.10 (Closure).  Here we identify this definition with the Mathlib version. -/
theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem subset_closure (X:Set ℝ): X ⊆ closure X := by
  intro x hx
  rw [closure_def']
  intro ε hε
  use x; constructor
  · exact hx
  · simp; linarith

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_union (X Y:Set ℝ): closure (X ∪ Y) = closure X ∪ closure Y := by
  ext y; constructor
  · intro hxy
    by_contra! h'; simp at h'
    obtain ⟨hcX, hcY⟩ := h'
    rw [closure_def'] at hxy hcX hcY
    unfold AdherentPt at hcX hcY
    push_neg at hcX hcY
    choose ε₁ hε₁ hballε₁ using hcX
    choose ε₂ hε₂ hballε₂ using hcY
    specialize hxy (min ε₁ ε₂) (by positivity)
    choose y' hXY' hball' using hxy
    rcases hXY' with hX' | hY'
    · specialize hballε₁ y' hX'
      have : ε₁ < min ε₁ ε₂ := by linarith
      simp at this
    · specialize hballε₂ y' hY'
      have : ε₂ < min ε₁ ε₂ := by linarith
      simp at this
  · intro hxy ; simp at hxy
    simp only [closure_def'] at hxy ⊢
    intro ε hε
    rcases hxy with hX | hY
    · specialize hX ε hε
      choose x hx using hX
      use x; constructor
      · left; exact hx.1
      · exact hx.2
    · specialize hY ε hε
      choose y hy using hY
      use y; constructor
      · right; exact hy.1
      · exact hy.2

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_inter (X Y:Set ℝ): closure (X ∩ Y) ⊆ closure X ∩ closure Y := by
  intro y hXY
  simp only [Set.mem_inter_iff, closure_def'] at hXY ⊢
  constructor
  · intro ε hε
    specialize hXY ε hε
    choose x hxy using hXY
    use x
    exact ⟨hxy.1.1, hxy.2⟩
  · intro ε hε
    specialize hXY ε hε
    choose x hxy using hXY
    use x
    exact ⟨hxy.1.2, hxy.2⟩

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_subset {X Y:Set ℝ} (h: X ⊆ Y): closure X ⊆ closure Y := by
  intro x hX
  simp only [closure_def'] at hX ⊢
  intro ε hε
  choose y hy using hX ε hε
  use y
  exact ⟨h hy.1, hy.2⟩

/-- Lemma 9.1.11 / Exercise 9.1.1 -/
theorem closure_of_subset_closure {X Y:Set ℝ} (h: X ⊆ Y) (h' : Y ⊆ closure X): closure Y = closure X := by
  have hX := subset_closure X
  have hY := subset_closure Y
  have h1 := closure_subset h
  have h2 := closure_subset h'
  suffices closure (closure X) = closure X by
    rw [this] at h2
    exact Set.Subset.antisymm h2 h1
  apply Set.Subset.antisymm
  · intro x' hX'
    simp only [closure_def'] at hX' ⊢
    intro ε hε
    choose a₁ ha₁ hdist₁ using hX' (ε/2) (by positivity)
    simp only [closure_def'] at ha₁
    choose a₂ ha₂ hdist₂ using ha₁ (ε/2) (by positivity)
    use a₂; constructor
    · exact ha₂
    · calc _ = |(x' - a₁) + (a₁ - a₂)| := by ring_nf
           _ ≤ |x' - a₁| + |a₁ - a₂|   := by exact abs_add_le _ _
           _ ≤ ε / 2 + ε / 2           := by linarith
           _ = ε                       := by norm_num
  · exact closure_subset hX


/-- Lemma 9.1.12 -/
theorem closure_of_Ioo {a b:ℝ} (h:a < b) : closure (.Ioo a b) = .Icc a b := by
  -- This proof is written to follow the structure of the original text.
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  . intro h; contrapose! h
    obtain h' | h' := le_or_gt a x
    . specialize h h'
      use x-b, by linarith
      intro y ⟨ _, _ ⟩; observe : x-y ≤ |x-y|; linarith
    use a-x, by linarith
    intro y ⟨ _, _ ⟩; observe : -(x-y) ≤ |x-y|; linarith
  intro ⟨ h1, h2 ⟩
  by_cases ha : x = a
  . subst ha
    intro ε hε
    by_cases! hinterval : ε < b - x
    · use x + ε; simp
      constructor
      · exact ⟨hε, by linarith⟩
      · rw [abs_of_pos hε]
    · use x + (b - x) / 2; simp
      constructor
      · exact ⟨h, by linarith⟩
      · rw [abs_div, abs_of_pos (by linarith)]; simp
        linarith
  by_cases hb : x = b
  . subst hb
    intro ε hε
    by_cases! hinterval : ε < x - a
    · use x - ε; simp
      constructor
      · exact ⟨by linarith, hε⟩
      · rw [abs_of_pos (by linarith)]
    · use x - (x - a) / 2; simp
      constructor
      · exact ⟨by linarith, h⟩
      · rw [abs_div, abs_of_pos (by linarith)]; simp
        linarith
  intro ε _; use x, (by exact ⟨lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 hb⟩); simp; order

theorem closure_of_Ioc {a b:ℝ} (h:a < b) : closure (.Ioc a b) = .Icc a b := by
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  · intro h'
    contrapose! h'
    rcases le_or_gt a x with hle | hgt
    · specialize h' hle
      use (x - b) / 2, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_pos (by linarith)]; linarith
    · use a - x, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_neg (by linarith)]; linarith
  · intro ⟨h1, h2⟩
    · by_cases! ha : x = a
      . subst ha
        intro ε hε
        by_cases! hinterval : ε < b - x
        · use x + ε; simp
          constructor
          · exact ⟨hε, by linarith⟩
          · rw [abs_of_pos hε]
        · use x + (b - x) / 2; simp
          constructor
          · exact ⟨h, by linarith⟩
          · rw [abs_div, abs_of_pos (by linarith)]; simp
            linarith
      · intro ε hε
        use x; constructor
        · exact ⟨by apply lt_of_le_of_ne h1; exact ha.symm, by exact h2⟩
        · simp; positivity

theorem closure_of_Ico {a b:ℝ} (h:a < b) : closure (.Ico a b) = .Icc a b := by
  ext x; simp [closure_def, AdherentPt, Real.adherent']
  constructor
  · intro h'
    contrapose! h'
    rcases le_or_gt a x with hle | hgt
    · specialize h' hle
      use x - b, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_pos (by linarith)]; linarith
    · use (a - x) / 2, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_neg (by linarith)]; linarith
  · intro ⟨h1, h2⟩
    by_cases hb : x = b
    . subst hb
      intro ε hε
      by_cases! hinterval : ε < x - a
      · use x - ε; simp
        constructor
        · exact ⟨by linarith, hε⟩
        · rw [abs_of_pos (by linarith)]
      · use x - (x - a) / 2; simp
        constructor
        · exact ⟨by linarith, h⟩
        · rw [abs_div, abs_of_pos (by linarith)]; simp
          linarith
    · intro ε hε
      use x; constructor
      · exact ⟨by exact h1, by exact lt_of_le_of_ne h2 hb⟩
      · simp; positivity

theorem closure_of_Icc {a b:ℝ} (h:a ≤ b) : closure (.Icc a b) = .Icc a b := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h'
    contrapose! h'
    rcases le_or_gt a x with hle | hgt
    · specialize h' hle
      use (x - b) / 2, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_pos (by linarith)]; linarith
    · use (a - x) / 2, by linarith
      intro y ⟨hay, hyb⟩; rw [abs_of_neg (by linarith)]; linarith
  · intro ⟨h1, h2⟩ ε hε
    use x; constructor
    · exact ⟨h1, h2⟩
    · simp; positivity

theorem closure_of_Ioi {a:ℝ} : closure (.Ioi a) = .Ici a := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    use a - x, by linarith
    intro y hy; rw [abs_of_neg (by linarith)]; simp; exact hy
  · intro h ε hε
    rcases h.eq_or_lt with heq | hlt
    · subst heq
      use a + ε; constructor
      · linarith
      · simp; rw [abs_of_pos (by linarith)]
    · use x; constructor
      · exact hlt
      · simp; positivity

theorem closure_of_Ici {a:ℝ} : closure (.Ici a) = .Ici a := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    use (a - x) / 2, by linarith
    intro y hy; rw [abs_of_neg (by linarith)]; simp; linarith
  · intro h ε hε
    use x; constructor
    · exact h
    · simp; positivity

theorem closure_of_Iio {a:ℝ} : closure (.Iio a) = .Iic a := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    use x - a, by linarith
    intro y hy; rw [abs_of_pos (by linarith)]; simp; exact hy
  · intro h ε hε
    rcases h.eq_or_lt with heq | hlt
    · subst heq
      use x - ε; constructor
      · linarith
      · simp; rw [abs_of_pos (by linarith)]
    · use x; constructor
      · exact hlt
      · simp; positivity

theorem closure_of_Iic {a:ℝ} : closure (.Iic a) = .Iic a := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    use (x- a ) / 2, by linarith
    intro y hy; rw [abs_of_pos (by linarith)]; linarith
  · intro h ε hε
    use x; constructor
    · exact h
    · simp; positivity


theorem closure_of_R : closure (.univ: Set ℝ) = .univ := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  intro ε hε
  use x; simp; positivity

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_N :
  closure ((fun n:ℕ ↦ (n:ℝ)) '' .univ) = ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    by_cases! h0 : x < 0
    · use - (x / 2); constructor
      · simp; linarith
      · intro n
        rw [abs_of_neg (by linarith)]
        simp; linarith
    · use (min (x - ⌊x⌋₊) (⌈x⌉₊ - x)) / 2; constructor
      · simp; constructor
        · contrapose! h; use ⌊x⌋₊
          apply le_antisymm
          · exact Nat.floor_le h0
          · exact h
        · contrapose! h; use ⌈x⌉₊
          apply le_antisymm
          · exact h
          · exact Nat.le_ceil x
      · intro n
        specialize h n
        have hpos : 0 < |x - n| := by exact abs_sub_pos.mpr h.symm
        suffices min (x - ⌊x⌋₊) (⌈x⌉₊ - x) ≤ |x - n| by linarith
        rcases le_total (n:ℝ) x with hnx | hxn
        · have hfloor : n ≤ ⌊x⌋₊ := by exact Nat.le_floor hnx
          have hfloor' : (n:ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfloor
          rw [abs_of_nonneg (by linarith)]
          calc _ ≤ x - ⌊x⌋₊ := by apply min_le_left
               _ ≤ x - n    := by linarith
        · have hceil : n ≥ ⌈x⌉₊ := by exact Nat.ceil_le.mpr hxn
          have hceil' : (n:ℝ)  ≥ ⌈x⌉₊ := by exact_mod_cast hceil
          rw [abs_of_nonpos (by linarith)]
          calc _ ≤ (⌈x⌉₊ - x) := by apply min_le_right
               _ ≤ n - x      := by linarith
               _ = -(x - n)   := by ring_nf
  · intro h z hz
    choose n hn using h
    use n; rw [hn]; simp; positivity

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Z :
  closure ((fun n:ℤ ↦ (n:ℝ)) '' .univ) = ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    contrapose! h
    use (min (x - ⌊x⌋) (⌈x⌉ - x)) / 2; constructor
    · suffices (min (x - ⌊x⌋) (⌈x⌉ - x)) > 0 by linarith
      simp only [lt_min_iff]; constructor
      · contrapose! h
        use ⌊x⌋; apply le_antisymm
        · exact Int.floor_le x
        · linarith
      · contrapose! h
        use ⌈x⌉; apply le_antisymm
        · linarith
        · exact Int.le_ceil x
    · intro n
      specialize h n
      have hpos : 0 < |x - n| := by exact abs_sub_pos.mpr h.symm
      suffices min (x - ⌊x⌋) (⌈x⌉ - x) ≤ |x - n| by linarith
      rcases le_total (n:ℝ) x with hnx | hxn
      · have hfloor : n ≤ ⌊x⌋ := by exact Int.le_floor.mpr hnx
        have hfloor' : (n:ℝ) ≤ ⌊x⌋ := by exact_mod_cast hfloor
        rw [abs_of_nonneg (by linarith)]
        calc _ ≤ x - ⌊x⌋ := by apply min_le_left
              _ ≤ x - n    := by linarith
      · have hceil : n ≥ ⌈x⌉ := by exact Int.ceil_le.mpr hxn
        have hceil' : (n:ℝ)  ≥ ⌈x⌉ := by exact_mod_cast hceil
        rw [abs_of_nonpos (by linarith)]
        calc _ ≤ (⌈x⌉ - x) := by apply min_le_right
              _ ≤ n - x      := by linarith
              _ = -(x - n)   := by ring_nf
  · intro h z hz
    choose n hn using h
    use n; rw [hn]; simp; positivity

/-- Lemma 9.1.13 / Exercise 9.1.2 -/
theorem closure_of_Q :
  closure ((fun n:ℚ ↦ (n:ℝ)) '' .univ) = .univ := by
  ext x; rw [closure_def]; simp
  simp [AdherentPt, Real.adherent']
  intro ε hε
  choose q hq1 hq2 using exists_rat_btwn (x:=x - ε) (y:=x + ε) (by linarith)
  use q; rw [abs_le]; constructor <;> linarith


/-- Lemma 9.1.14 / Exercise 9.1.4-/
theorem limit_of_AdherentPt (X: Set ℝ) (x:ℝ) :
  AdherentPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [AdherentPt, Real.adherent']
  constructor
  · intro h
    set a : ℕ → ℝ := fun n => Classical.choose (h (1 / ((n:ℝ) + 1)) (by positivity))
    have hainX (n : ℕ) : a n ∈ X := by exact (Classical.choose_spec (h (1 / ((n:ℝ) + 1)) (by positivity))).1
    have haovern (n : ℕ) : |x - a n| ≤ 1 / (n+1) := by exact (Classical.choose_spec (h (1 / ((n:ℝ) + 1)) (by positivity))).2
    use a; constructor
    · intro n; exact hainX n
    · simp_rw [Metric.tendsto_atTop, Real.dist_eq]
      intro ε hε
      choose N hN using exists_nat_gt (1/ε)
      use max 1 N; intro n hn; simp at hn
      have hnpos : n > 0 := by omega
      calc _ = |x - a n|     := by apply abs_sub_comm
           _ ≤ 1 / ((n:ℝ)+1) := by exact haovern n
           _ ≤ 1 / (n:ℝ)     := by gcongr; linarith
           _ ≤ 1 / (N:ℝ)     := by gcongr; linarith [one_div_pos.mpr hε, hN]; exact hn.2
           _ < ε             := by
              have hNpos : (0:ℝ) < N  := by linarith [one_div_pos.mpr hε]
              have hNne : (N : ℝ) ≠ 0 := by linarith
              field_simp at hN ⊢
              exact hN
  · intro h
    choose a hainX htendsto using h
    intro ε hε
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at htendsto
    specialize htendsto ε hε
    choose N hN using htendsto
    specialize hN N (by rfl)
    use a N; constructor
    · exact hainX N
    · calc _ = |a N - x| := by apply abs_sub_comm
           _ ≤ ε         := by linarith


theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Examples 9.1.16 -/
theorem Icc_closed {a b:ℝ} : IsClosed (.Icc a b) := by
  rw [isClosed_def]
  exact closure_Icc a b

/-- Examples 9.1.16 -/
theorem Ici_closed (a:ℝ) : IsClosed (.Ici a) := by
  rw [isClosed_def]
  exact closure_of_Ici

/-- Examples 9.1.16 -/
theorem Iic_closed (a:ℝ) : IsClosed (.Iic a) := by
  rw [isClosed_def]
  exact closure_of_Iic

/-- Examples 9.1.16 -/
theorem R_closed : IsClosed (.univ : Set ℝ) := by
  rw [isClosed_def]
  exact closure_of_R

/-- Examples 9.1.16 -/
theorem Ico_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ico a b) := by
  rw [isClosed_def']
  push_neg
  use b; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    by_cases! hinterval : ε < b - a
    · use b - ε; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_pos (by linarith)]; simp
    · use a + (b - a) / 2; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_pos (by linarith)]; simp; linarith
  · simp

/-- Examples 9.1.16 -/
theorem Ioc_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioc a b) := by
  rw [isClosed_def']
  push_neg
  use a; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    by_cases! hinterval : ε < b - a
    · use a + ε; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_neg (by linarith)]; simp
    · use a + (b - a) / 2; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_neg (by linarith)]; simp; linarith
  · simp

/-- Examples 9.1.16 -/
theorem Ioo_not_closed {a b:ℝ} (h: a < b) : ¬ IsClosed (.Ioo a b) := by
  rw [isClosed_def']
  push_neg
  use a; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    by_cases! hinterval : ε < b - a
    · use a + ε; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_neg (by linarith)]; simp
    · use a + (b - a) / 2; constructor
      · exact ⟨by linarith, by linarith⟩
      · rw [abs_of_neg (by linarith)]; simp; linarith
  · simp

/-- Examples 9.1.16 -/
theorem Ioi_not_closed (a:ℝ) : ¬ IsClosed (.Ioi a) := by
  rw [isClosed_def']
  push_neg
  use a; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    use a + ε; constructor
    · linarith
    · rw [abs_of_neg (by linarith)]; simp
  · simp

/-- Examples 9.1.16 -/
theorem Iio_not_closed (a:ℝ) : ¬ IsClosed (.Iio a) := by
  rw [isClosed_def']
  push_neg
  use a; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    use a - ε; constructor
    · linarith
    · rw [abs_of_pos (by linarith)]; simp
  · simp

/-- Examples 9.1.16 -/
theorem N_closed : IsClosed ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def]
  exact closure_of_N

/-- Examples 9.1.16 -/
theorem Z_closed : IsClosed ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def]
  exact closure_of_Z

/-- Examples 9.1.16 -/
theorem Q_not_closed : ¬ IsClosed ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isClosed_def']
  push_neg
  use Real.sqrt 2; constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    choose a ha using exists_rat_btwn (x:=Real.sqrt 2-ε) (y:=Real.sqrt 2+ε) (by linarith)
    use a
    rw [abs_le]; constructor <;> linarith
  · simp; by_contra! h
    choose q hq using h
    exact irrational_sqrt_two ⟨q, hq⟩

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

/-- Definition 9.1.18 (Limit points) -/
abbrev LimitPt (x:ℝ) (X: Set ℝ) := AdherentPt x (X \ {x})

/-- Identification with Mathlib's {name}`AccPt`-/
theorem LimitPt.iff_AccPt (x:ℝ) (X: Set ℝ) : LimitPt x X ↔ AccPt x (.principal X) := by
  rw [accPt_principal_iff_clusterPt,←AdherentPt_def]

/-- Definition 9.1.19 (Isolated points). -/
abbrev IsolatedPt (x:ℝ) (X: Set ℝ) := x ∈ X ∧ ∃ ε>0, ∀ y ∈ X \ {x}, |x-y| > ε

/-- Example 9.1.19 -/
example : AdherentPt 3 ((.Ioo 1 2) ∪ {3}) := by
  simp [AdherentPt, Real.adherent']
  intro ε hε
  left; linarith

example : ¬ LimitPt 3 ((.Ioo 1 2) ∪ {3}) := by
  simp [LimitPt, AdherentPt, Real.adherent']
  use 0.5; constructor
  · norm_num
  · intro x hx1 hx2 hx3
    rw [lt_abs]
    left; linarith

example : IsolatedPt 3 ((.Ioo 1 2) ∪ {3}) := by
  simp [IsolatedPt]
  use 0.5; constructor
  · norm_num
  · intro y hy1 hy2 hy3
    rw [lt_abs]
    left; linarith

/-- Remark 9.1.20 -/
theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [limit_of_AdherentPt]

/-- Lemma 9.1.21 -/
theorem mem_Icc_isLimit {a b x:ℝ} (h: a < b) (hx: x ∈ Set.Icc a b) : LimitPt x (.Icc a b) := by
  -- This proof is written to follow the structure of the original text, with some slight simplifications.
  simp at hx
  rw [LimitPt.iff_limit]
  obtain hxb | hxb := le_iff_lt_or_eq.1 hx.2
  . use (fun n:ℕ ↦ (x + 1/(n+(b-x)⁻¹)))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : n + (b - x)⁻¹ > 0 := by linarith
      have : (n+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ ≤ n + (b - x)⁻¹ := by linarith
      have : (n + (b - x)⁻¹)⁻¹ ≤ b-x := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 (b - x)⁻¹ (by norm_num) using 2 with n; simp
  · use fun n : ℕ ↦ x - 1/(n + (x - a)⁻¹)
    constructor
    · intro n
      have : x - a > 0 := by linarith
      have : (x-a)⁻¹ > 0 := by positivity
      have : n + (x-a)⁻¹ > 0 := by linarith
      have : (n + (x-a)⁻¹)⁻¹ > 0 := by positivity
      have : (x-a)⁻¹ ≤ n + (x-a)⁻¹ := by linarith
      have : (n + (x-a)⁻¹)⁻¹ ≤ x-a := by rwa [inv_le_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/(k+(x-a)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 (x-a)⁻¹ (by norm_num) using 2 with n; simp

theorem mem_Ico_isLimit {a b x:ℝ} (hx: x ∈ Set.Ico a b) : LimitPt x (.Ico a b) := by
    simp at hx
    rw [LimitPt.iff_limit]
    use (fun n : ℕ ↦ x + 1/((n+1) + (b-x)⁻¹))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : (n+1) + (b - x)⁻¹ > 0 := by linarith
      have : ((n+1)+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ < (n+1) + (b - x)⁻¹ := by linarith
      have : ((n+1) + (b - x)⁻¹)⁻¹ < b-x := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((b - x)⁻¹+1) (by norm_num) using 2 with n
    simp; linarith

theorem mem_Ioc_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioc a b) : LimitPt x (.Ioc a b) := by
  simp at hx
  rw [LimitPt.iff_limit]
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a)⁻¹)
  constructor
  · intro n
    have : x - a > 0 := by linarith
    have : (x-a)⁻¹ > 0 := by positivity
    have : (n+1) + (x-a)⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ > 0 := by positivity
    have : (x-a)⁻¹ < (n+1) + (x-a)⁻¹ := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ < x-a := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a)⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a)⁻¹+1) (by norm_num) using 2 with n
  simp; linarith

theorem mem_Ioo_isLimit {a b x:ℝ} (hx: x ∈ Set.Ioo a b) : LimitPt x (.Ioo a b) := by
  simp at hx
  rw [LimitPt.iff_limit]
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a)⁻¹)
  constructor
  · intro n
    have : x - a > 0 := by linarith
    have : (x-a)⁻¹ > 0 := by positivity
    have : (n+1) + (x-a)⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ > 0 := by positivity
    have : (x-a)⁻¹ < (n+1) + (x-a)⁻¹ := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ < x-a := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a)⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a)⁻¹+1) (by norm_num) using 2 with n
  simp; linarith

theorem mem_Ici_isLimit {a x:ℝ} (hx: x ∈ Set.Ici a) : LimitPt x (.Ici a) := by
    simp at hx
    set b := x + 1
    rw [LimitPt.iff_limit]
    use (fun n : ℕ ↦ x + 1/((n+1) + (b-x)⁻¹))
    constructor
    . intro n; simp
      have : b - x > 0 := by linarith
      have : (b - x)⁻¹ > 0 := by positivity
      have : (n+1) + (b - x)⁻¹ > 0 := by linarith
      have : ((n+1)+(b - x)⁻¹)⁻¹ > 0 := by positivity
      have : (b-x)⁻¹ < (n+1) + (b - x)⁻¹ := by linarith
      have : ((n+1) + (b - x)⁻¹)⁻¹ < b-x := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
      grind
    convert (Filter.Tendsto.const_add x (a := 0) ?_) using 1; · simp
    convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(b-x)⁻¹)) ?_ tendsto_natCast_atTop_atTop
    convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((b - x)⁻¹+1) (by norm_num) using 2 with n
    simp; linarith

theorem mem_Ioi_isLimit {a x:ℝ} (hx: x ∈ Set.Ioi a) : LimitPt x (.Ioi a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a)⁻¹)
  constructor
  · intro n
    have : x - a > 0 := by linarith
    have : (x-a)⁻¹ > 0 := by positivity
    have : (n+1) + (x-a)⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ > 0 := by positivity
    have : (x-a)⁻¹ < (n+1) + (x-a)⁻¹ := by linarith
    have : ((n+1) + (x-a)⁻¹)⁻¹ < x-a := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a)⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a)⁻¹+1) (by norm_num) using 2 with n
  simp; linarith

theorem mem_Iic_isLimit {a x:ℝ} (hx: x ∈ Set.Iic a) : LimitPt x (.Iic a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  set a' := x - 1
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a')⁻¹)
  constructor
  · intro n; simp
    have : x - a' > 0 := by linarith
    have : (x-a')⁻¹ > 0 := by positivity
    have : (n+1) + (x-a')⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ > 0 := by positivity
    have : (x-a')⁻¹ < (n+1) + (x-a')⁻¹ := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ < x-a' := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a')⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a')⁻¹+1) (by norm_num) using 2 with n
  simp; linarith

theorem mem_Iio_isLimit {a x:ℝ} (hx: x ∈ Set.Iio a) : LimitPt x (.Iio a) := by
  simp at hx
  rw [LimitPt.iff_limit]
  set a' := x - 1
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a')⁻¹)
  constructor
  · intro n; simp
    have : x - a' > 0 := by linarith
    have : (x-a')⁻¹ > 0 := by positivity
    have : (n+1) + (x-a')⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ > 0 := by positivity
    have : (x-a')⁻¹ < (n+1) + (x-a')⁻¹ := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ < x-a' := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a')⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a')⁻¹+1) (by norm_num) using 2 with n
  simp; linarith

theorem mem_R_isLimit {x:ℝ} : LimitPt x (.univ) := by
  rw [LimitPt.iff_limit]
  set a' := x - 1
  use fun n : ℕ ↦ x - 1/((n+1) + (x - a')⁻¹)
  constructor
  · intro n; simp
    have : x - a' > 0 := by linarith
    have : (x-a')⁻¹ > 0 := by positivity
    have : (n+1) + (x-a')⁻¹ > 0 := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ > 0 := by positivity
    have : (x-a')⁻¹ < (n+1) + (x-a')⁻¹ := by linarith
    have : ((n+1) + (x-a')⁻¹)⁻¹ < x-a' := by rwa [inv_lt_comm₀ ?_ ?_] <;> positivity
    grind
  convert (Filter.Tendsto.const_sub x (c := 0) ?_) using 1; · simp
  convert Filter.Tendsto.comp (f := fun (k:ℕ) ↦ (k:ℝ)) (g := fun k ↦ 1/((k+1)+(x-a')⁻¹)) ?_ tendsto_natCast_atTop_atTop
  convert tendsto_mul_add_inv_atTop_nhds_zero 1 ((x-a')⁻¹+1) (by norm_num) using 2 with n
  simp; linarith


/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded`-/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

/-- Example 9.1.23 -/
theorem Icc_bounded (a b:ℝ) : Bornology.IsBounded (.Icc a b) := by
  rw [isBounded_def]
  use (max (|a|+1) (|b|)); constructor
  · simp; left; positivity
  · intro x hx; simp at hx
    simp; constructor <;> grind

/-- Example 9.1.23 -/
theorem Ici_unbounded (a: ℝ) : ¬ Bornology.IsBounded (.Ici a) := by
  rw [isBounded_def]; push_neg
  intro M hM h
  have : (max a M) + 1 ∈ Set.Ici a := by simp; grind
  specialize h this
  simp at h
  grind

/-- Example 9.1.23 -/
theorem N_unbounded : ¬ Bornology.IsBounded ((fun n:ℕ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; push_neg
  intro M hM h
  simp at h
  have : ((⌈M⌉₊ + 1):ℝ) ∈ (Set.range fun (n:ℕ) => (n:ℝ)) := by
    use (⌈M⌉₊ + 1)
    simp
  specialize h this
  simp at h
  obtain ⟨h1, h2⟩ := h
  have := Nat.le_ceil M
  grind

/-- Example 9.1.23 -/
theorem Z_unbounded : ¬ Bornology.IsBounded ((fun n:ℤ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; push_neg
  intro M hM h
  simp at h
  have : ((⌈M⌉ + 1):ℝ) ∈ (Set.range fun (n:ℤ) => (n:ℝ)) := by
    use (⌈M⌉ + 1)
    simp
  specialize h this
  simp at h
  obtain ⟨h1, h2⟩ := h
  have := Int.le_ceil M
  grind

/-- Example 9.1.23 -/
theorem Q_unbounded : ¬ Bornology.IsBounded ((fun n:ℚ ↦ (n:ℝ)) '' .univ) := by
  rw [isBounded_def]; push_neg
  intro M hM h
  simp at h
  choose q hq1 hq2 using exists_rat_btwn (x:=M) (y:=M+1) (by linarith)
  have : (q:ℝ) ∈ (Set.range fun (q:ℚ) => (q:ℝ)) := by
    use q
  specialize h this
  simp at h
  linarith

/-- Example 9.1.23 -/
theorem R_unbounded : ¬ Bornology.IsBounded (.univ: Set ℝ) := by
  rw [isBounded_def]; push_neg
  intro M hM h
  simp at h
  choose hokay himpossible using Set.Subset.antisymm_iff.mp h
  have : M + 1 ∈ Set.univ := by tauto
  specialize himpossible this
  simp at himpossible
  linarith



open Classical in
noncomputable def lr (a : ℕ → ℝ) (M : ℝ) : ℕ → ℝ × ℝ
  | 0 => (-M, M)
  | k + 1 =>
    let p := lr a M k
    let m := (p.1 + p.2) / 2
    if (∃ᶠ n in Filter.atTop, a n ∈ Set.Icc p.1 m) then (p.1, m) else (m, p.2)

lemma lr_l_le_r (a : ℕ → ℝ) (M : ℝ) (n : ℕ) (hMPos : M > 0) :
  (lr a M n).1 ≤ (lr a M n).2 := by
  induction' n with k ih
  . unfold lr; simp; linarith
  . unfold lr; simp
    split_ifs with h
    . simp; linarith
    . simp; linarith

lemma lr_width (a : ℕ → ℝ) (M : ℝ) (n : ℕ) : (lr a M n).2 - (lr a M n).1 = 2 * M / 2^n := by
  induction' n with k ih
  . unfold lr; simp; linarith
  . unfold lr; simp
    set l := (lr a M k).1
    set r := (lr a M k).2
    split_ifs with h
    . simp
      conv_lhs => rw [show (l + r) / 2 - l = (r - l) / 2 by field_simp; ring_nf]
      conv_rhs =>
        rw [pow_add]; simp
        rw [show 2 * M / (2 ^ k * 2) = M / (2 ^ k) by field_simp]
      field_simp at ih ⊢; exact ih
    . simp
      conv_lhs => rw [show r - (l + r) / 2 = (r - l) / 2 by field_simp; ring_nf]
      conv_rhs =>
        rw [pow_add]; simp
        rw [show 2 * M / (2 ^ k * 2) = M / (2 ^ k) by field_simp]
      field_simp at ih ⊢; exact ih

lemma lr_bisect (a : ℕ → ℝ) {l r: ℝ} (h : ∃ᶠ n in Filter.atTop, a n ∈ Set.Icc l r) :
  (∃ᶠ n in Filter.atTop, a n ∈ Set.Icc l ((l+r)/2))  ∨  (∃ᶠ n in Filter.atTop, a n ∈ Set.Icc ((l+r)/2) r) := by
  rw [← Filter.frequently_or_distrib]
  apply h.mono
  intro n hn
  by_cases! han : a n ≤ ((l + r) / 2)
  . left; simp at hn han ⊢; constructor <;> linarith
  . right; simp at hn han ⊢; constructor <;> linarith

lemma lr_freq (a : ℕ → ℝ) (M : ℝ) (h0 : ∃ᶠ n in Filter.atTop, a n ∈ Set.Icc (-M) M) (n : ℕ) :
  ∃ᶠ k in Filter.atTop, a k ∈ Set.Icc (lr a M n).1 (lr a M n).2 := by
  induction' n with k ih
  . simp_rw [
      show (lr a M 0).1 = -M by rfl,
      show (lr a M 0).2 = M by rfl
    ]
    exact h0
  . unfold lr
    replace ih := lr_bisect a ih
    simp only [] at *
    split_ifs with h
    . simp; tauto
    . simp; tauto

lemma lr_nest (a : ℕ → ℝ) (M : ℝ) (hMpos : M > 0) (n : ℕ) :
    (lr a M n).1 ≤ (lr a M (n+1)).1 ∧ (lr a M (n+1)).2 ≤ (lr a M n).2 := by
  have hle := lr_l_le_r a M n hMpos
  match n with
  | 0     =>
    unfold lr
    simp
    rw [
      show (lr a M 0).1 = -M by rfl,
      show (lr a M 0).2 = M by rfl
    ]
    constructor
    . split_ifs with h
      . simp
      . simp; linarith
    . split_ifs with h
      . simp; linarith
      . simp
  | k + 1 =>
    have hle' := lr_l_le_r a M k hMpos
    conv_rhs => unfold lr
    simp [-Set.mem_Icc]
    split_ifs with h1 h2 h3 <;> constructor <;> simp only [] at *
    . conv_rhs => unfold lr
      simp [-Set.mem_Icc, h1]
    . field_simp
      conv_lhs => unfold lr
      simp [-Set.mem_Icc, h2]
      linarith
    . conv_rhs => unfold lr
      simp [-Set.mem_Icc, h1]
    . conv_lhs => unfold lr
      simp [-Set.mem_Icc, h2]
      linarith
    . conv_rhs => unfold lr
      simp [-Set.mem_Icc, h1]
      linarith
    . conv_lhs => unfold lr
      simp [-Set.mem_Icc, h3]
    · conv_rhs => unfold lr
      simp [-Set.mem_Icc, h1]
      linarith
    . conv_lhs => unfold lr
      simp [-Set.mem_Icc, h3]


/-- Theorem 9.1.24 / Exercise 9.1.13 (Heine-Borel theorem for the line)-/
theorem Heine_Borel (X: Set ℝ) :
  IsClosed X ∧ Bornology.IsBounded X ↔ ∀ a : ℕ → ℝ, (∀ n, a n ∈ X) →
  (∃ n : ℕ → ℕ, StrictMono n
    ∧ ∃ L ∈ X, Filter.atTop.Tendsto (fun j ↦ a (n j)) (nhds L)) := by
  constructor
  · rintro ⟨hclosed, hbounded⟩ a ha
    rw [isBounded_def] at hbounded
    choose M hMpos hMbound using hbounded
    have habound : ∀ n, a n ∈ Set.Icc (-M) M := by
      intro n
      specialize ha n
      exact hMbound ha
    replace habound : ∃ᶠ n in Filter.atTop, a n ∈ Set.Icc (-M) M := by
      exact Filter.Frequently.of_forall habound
    have hmono : Monotone (fun n => (lr a M n).1) := by
      apply monotone_nat_of_le_succ
      intro n
      exact (lr_nest a M (by linarith) n).1
    have hbdd : BddAbove (Set.range (fun n => (lr a M n).1)) := by
      use M
      intro n hn
      simp at hn
      choose y hy using hn
      suffices hlr : ∀ n, (lr a M n).2 ≤ M by
        specialize hlr y
        have := lr_l_le_r a M y (by linarith)
        linarith
      intro k
      induction' k with z ih
      · rw [lr]
      · have := (lr_nest a M (by linarith) z).2
        linarith
    have hconv := tendsto_atTop_ciSup hmono hbdd
    set L := ⨆ i, (lr a M i).1 with hL
    obtain ⟨φ, hφmono, hφmem⟩ := Filter.extraction_forall_of_frequently (fun n => lr_freq _ _ habound n)
    have hwidth0 : Filter.Tendsto (fun n => 2 * M / 2 ^ n) Filter.atTop (nhds 0) := by
      convert (tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜:=ℝ) (r:=(1/2)) (by norm_num) (by norm_num)).const_mul (2 * M) using 1
      · funext x
        field_simp
        rw [← mul_pow]
        simp
      · simp
    have hconv' : Filter.Tendsto (fun n => (lr a M n).2) Filter.atTop (nhds L) := by
      have : (fun n => (lr a M n).2) = (fun n => (lr a M n).1 + 2 * M / 2 ^ n) := by
        funext n
        have := lr_width a M n
        linarith
      rw [this]
      simpa using hconv.add hwidth0
    use φ
    have hsqueeze : Filter.Tendsto (fun n => a (φ n)) Filter.atTop (nhds L) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hconv hconv'
      · intro n; simp
        exact (hφmem n).1
      · intro n; simp
        exact (hφmem n).2
    constructor
    · exact hφmono
    · use L; constructor
      · rw [isClosed_iff_limits_mem] at hclosed
        refine hclosed (a ∘ φ) L ?_ hsqueeze
        intro n
        exact ha (φ n)
      · exact hsqueeze
  · intro h
    constructor
    · rw [isClosed_def']
      intro x hx
      choose a haX httX using (limit_of_AdherentPt _ _).mp hx
      specialize h a haX
      choose τ hτmono hsubseq using h
      choose L hLX httL using hsubseq
      have hxL : L = x := by
        have : Filter.Tendsto (fun j ↦ a (τ j)) Filter.atTop (nhds x) := by
          apply httX.comp
          exact hτmono.tendsto_atTop
        exact tendsto_nhds_unique httL this
      rwa [← hxL]
    · rw [isBounded_def]
      contrapose! h
      have h' : ∀ M > 0, ∃ x ∈ X , |x| ≥ M := by
        intro M hM
        specialize h M hM
        contrapose! h
        intro x hx
        specialize h x hx
        simp; grind
      set a : ℕ → ℝ := fun n => Classical.choose (h' (n+1:ℝ) (by positivity))
      have haX (n : ℕ) : a n ∈ X := by exact (Classical.choose_spec (h'  (n+1:ℝ) (by positivity))).1
      have hagt (n : ℕ) : |a n| > n := by
        have : |a n| ≥ n + 1 := (Classical.choose_spec (h'  (n+1:ℝ) (by positivity))).2
        linarith
      have hatop : Filter.Tendsto |a| Filter.atTop Filter.atTop := by
        apply Filter.tendsto_atTop_mono (f := fun (n:ℕ) => (↑n : ℝ)) (g := |a|)
        · intro n; specialize hagt n; exact le_of_lt hagt
        · exact tendsto_natCast_atTop_atTop
      use a, haX
      intro τ hτ L hLX httL
      have hτtop : Filter.Tendsto (fun j ↦ |a (τ j)|) Filter.atTop Filter.atTop := by
        apply hatop.comp
        exact StrictMono.tendsto_atTop hτ
      apply hτtop.not_tendsto (b₂:= nhds |L|)
      · exact (disjoint_nhds_atTop |L|).symm
      · exact httL.abs

/-- Exercise 9.1.3 -/
example : ∃ (X Y:Set ℝ), closure (X ∩ Y) ≠ closure X ∩ closure Y := by
  set X : Set ℝ := Set.range Rat.cast
  set Y : Set ℝ := {x | Irrational x}
  have hXY : X ∩ Y = ∅ := by
    unfold X Y
    by_contra! h
    choose q hqrat hqnot using h
    exact absurd hqrat hqnot
  have hclXY : closure (X ∩ Y) = ∅ := by
    exact (closure_empty_iff _).mpr hXY
  have hclX : closure X = Set.univ := by
    unfold X
    convert closure_of_Q
    simp
  have hclY : closure Y = Set.univ := by
    unfold Y
    rw [closure_def]
    apply Set.Subset.antisymm
    · tauto
    · intro y hy
      simp [AdherentPt, Real.adherent']
      intro ε hε
      choose z hz using exists_irrational_btwn (x:=y-ε) (y:=y+ε) (by linarith)
      use z; grind
  have hclXclY : closure X ∩ closure Y = Set.univ := by
    rw [hclX, hclY]
    simp
  use X, Y
  rw [hclXY, hclXclY]
  exact Set.empty_ne_univ

/-- Exercise 9.1.5 -/
example (X:Set ℝ) : IsClosed (closure X) := by
  rw [isClosed_def]
  apply Set.Subset.antisymm
  · intro x' hX'
    simp only [closure_def'] at hX' ⊢
    intro ε hε
    choose a₁ ha₁ hdist₁ using hX' (ε/2) (by positivity)
    simp only [closure_def'] at ha₁
    choose a₂ ha₂ hdist₂ using ha₁ (ε/2) (by positivity)
    use a₂; constructor
    · exact ha₂
    · calc _ = |(x' - a₁) + (a₁ - a₂)| := by ring_nf
           _ ≤ |x' - a₁| + |a₁ - a₂|   := by exact abs_add_le _ _
           _ ≤ ε / 2 + ε / 2           := by linarith
           _ = ε                       := by norm_num
  · exact subset_closure (closure X)

/-- Exercise 9.1.6 -/
example {X Y:Set ℝ} (hY: IsClosed Y) (hXY: X ⊆ Y) : closure X ⊆ Y := by
  by_contra! hclX
  rw [Set.not_subset] at hclX
  choose a haclX hnotY using hclX
  simp [closure_def', AdherentPt, Real.adherent'] at haclX
  contrapose! hY
  simp [isClosed_def', AdherentPt, Real.adherent']
  use a
  grind

lemma closed_union {X Y: Set ℝ} (hX: IsClosed X) (hY: IsClosed Y) : IsClosed (X ∪ Y) := by
  rw [isClosed_def'] at hX hY ⊢
  simp [AdherentPt, Real.adherent'] at hX hY ⊢
  intro x hx
  specialize hX x
  specialize hY x
  by_contra! h
  have hnX : ¬ (∀ (ε : ℝ), 0 < ε → ∃ y ∈ X, |x - y| ≤ ε) := by
    intro hX'
    specialize hX hX'
    exact absurd hX h.1
  have hnY : ¬ (∀ (ε : ℝ), 0 < ε → ∃ y ∈ Y, |x - y| ≤ ε) := by
    intro hY'
    specialize hY hY'
    exact absurd hY h.2
  push_neg at hnX hnY
  choose ε₁ hε₁ hεdist₁ using hnX
  choose ε₂ hε₂ hεdist₂ using hnY
  choose z hz hzdist using hx (min ε₁ ε₂) (by positivity)
  rcases hz with hzX | hzY
  · specialize hεdist₁ z hzX
    grind
  · specialize hεdist₂ z hzY
    grind

/-- Exercise 9.1.7 -/
example {n:ℕ} (X: Fin n → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋃ i, X i) := by
  have key : ∀ s : Set (Fin n), s.Finite → IsClosed (⋃ i ∈ s, X i) := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => simp
    | @insert a s ha ih iha =>
      have : ⋃ i ∈ insert a s, X i = X a ∪  (⋃ i ∈ s, X i) := by simp
      rw [this]
      apply closed_union
      · exact hX a
      · exact iha
  simpa using key Set.univ Set.finite_univ


/-- Exercise 9.1.8 -/
example {I:Type} (X: I → Set ℝ) (hX: ∀ i, IsClosed (X i)) :
  IsClosed (⋂ i, X i) := by
  simp only [isClosed_def', AdherentPt, Real.adherent'] at hX ⊢
  rintro x hε i ⟨ι, hι⟩
  simp at hι
  specialize hX ι x
  rw [← hι]
  suffices (∀ ε > 0, ∃ y ∈ X ι, |x - y| ≤ ε) by exact hX this
  intro ε' hε'
  choose y hymem hydist using hε ε' hε'
  use y; constructor
  · apply hymem; tauto
  · exact hydist

theorem adherentPt_is_limitPt_or_IsolatedPt {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  simp [LimitPt]
  by_cases! hisolate : IsolatedPt x X
  · right; exact hisolate
  · left
    simp [IsolatedPt] at hisolate; push_neg at hisolate
    simp [AdherentPt, Real.adherent'] at hx ⊢
    intro ε hε
    choose y hymem hydist using hx ε hε
    by_cases hxmem : x ∈ X
    · choose z hzmem hznotx hzdist using hisolate hxmem ε hε
      use z
    · use y; refine ⟨⟨hymem, ?_,⟩, hydist⟩
      exact ne_of_mem_of_not_mem hymem hxmem

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} (hx: AdherentPt x X) : LimitPt x X ∨ IsolatedPt x X := by
  exact adherentPt_is_limitPt_or_IsolatedPt hx

/-- Exercise 9.1.9 -/
example {X:Set ℝ} {x:ℝ} : ¬ (LimitPt x X ∧ IsolatedPt x X) := by
  simp [LimitPt, IsolatedPt]
  push_neg
  intro hlimit hxmem ε hε
  simp [AdherentPt, Real.adherent'] at hlimit
  choose y hymem hydist using hlimit ε hε
  use y; exact ⟨hymem.1, hymem.2, hydist⟩


/-- Exercise 9.1.10 -/
example {X:Set ℝ} (hX: X ≠ ∅) : Bornology.IsBounded X ↔
  sSup ((fun x:ℝ ↦ (x:EReal)) '' X) < ⊤ ∧
  sInf ((fun x:ℝ ↦ (x:EReal)) '' X) > ⊥ := by
  constructor
  · intro hbd
    rw [isBounded_def] at hbd
    choose M hMpos hMbound using hbd
    constructor
    · refine EReal.lt_iff_exists_real_btwn.mpr ?_
      use M+1; refine ⟨?_, by exact EReal.coe_lt_top _⟩
      have key : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) ≤ M := by
        apply sSup_le
        intro b hb; simp at hb
        choose x hxmem hxb using hb
        rw [← hxb]
        exact_mod_cast (hMbound hxmem).2
      observe : M < M + 1
      exact key.trans_lt (EReal.coe_lt_coe this)
    · refine EReal.lt_iff_exists_real_btwn.mpr ?_
      use -M-1; refine ⟨by exact EReal.bot_lt_coe _, ?_⟩
      have key : -M ≤ sInf ((fun x : ℝ ↦ (x : EReal)) '' X) := by
        apply le_sInf
        intro b hb; simp at hb
        choose x hxmem hxb using hb
        rw [← hxb]
        exact_mod_cast (hMbound hxmem).1
      observe : -M-1 < -M
      exact (EReal.coe_lt_coe this).trans_le key
  · rintro ⟨hlttop, hgtbot⟩
    have hnottop := hlttop.ne
    have hnotbot := hgtbot.ne
    set M₁ : ℝ := (sSup ((fun x : ℝ ↦ (x : EReal)) '' X)).toReal with hM₁
    set M₂ : ℝ := (sInf ((fun x : ℝ ↦ (x : EReal)) '' X)).toReal with hM₂
    have hub : sSup ((fun x : ℝ ↦ (x : EReal)) '' X) ≤ (M₁:EReal) := by
      rw [hM₁]
      exact EReal.le_coe_toReal hnottop
    have hlb : (M₂:EReal) ≤ sInf ((fun x : ℝ ↦ (x : EReal)) '' X) := by
      rw [hM₂]
      exact EReal.coe_toReal_le (id (Ne.symm hnotbot))
    rw [isBounded_def]
    use max |M₁| |M₂| + 1; constructor
    · positivity
    · intro a ha; simp
      have hmem : (a:EReal) ∈ ((fun x : ℝ ↦ (x : EReal)) '' X) := by
        simp; exact ha
      have hgtM₂ : (M₂:EReal) ≤ (a:EReal) := by
        have := sInf_le hmem
        order
      have hltM₁ : (a:EReal) ≤ (M₁:EReal) := by
        have := le_sSup hmem
        order
      have hgtM₂' : M₂ ≤ a := by exact_mod_cast hgtM₂
      have hltM₁' : a ≤ M₁ := by exact_mod_cast hltM₁
      constructor <;> grind


/-- Exercise 9.1.11 -/
example {X:Set ℝ} (hX: Bornology.IsBounded X) : Bornology.IsBounded (closure X) := by
  rw [isBounded_def] at hX ⊢
  choose M hMpos hMbound using hX
  use M+1; constructor
  · linarith
  · intro x hclx
    simp [closure_def', AdherentPt, Real.adherent'] at hclx
    choose y hyX hydist using hclx 1 (by positivity)
    specialize hMbound hyX; simp at hMbound
    rw [abs_le] at hydist
    simp; grind

/-- Exercise 9.1.12.  As a followup: prove or disprove this exercise with {lean}`[Fintype I]` removed. -/
lemma bounded_union {X Y: Set ℝ} (hX: Bornology.IsBounded X) (hY: Bornology.IsBounded Y) : Bornology.IsBounded (X ∪ Y) := by
  rw [isBounded_def] at hX hY ⊢
  choose M₁ hMpos₁ hMb₁ using hX
  choose M₂ hMpos₂ hMb₂ using hY
  use max M₁ M₂; constructor
  · positivity
  · intro z hz
    rcases hz with hx | hy
    · specialize hMb₁ hx
      simp at hMb₁ ⊢
      grind
    · specialize hMb₂ hy
      simp at hMb₂ ⊢
      grind

example {I:Type} [Fintype I] (X: I → Set ℝ) (hX: ∀ i, Bornology.IsBounded (X i)) :
  Bornology.IsBounded (⋃ i, X i) := by
  suffices h : ∀ (S : Finset I), Bornology.IsBounded (⋃ i ∈ S, X i) by
    convert h Finset.univ using 1
    simp
  intro S
  induction S using Finset.induction_on with
  | empty =>
    rw [isBounded_def]
    use 1; simp
  | @insert a s ha ih =>
    have : ⋃ i ∈ insert a s, X i = X a ∪  (⋃ i ∈ s, X i) := by simp
    rw [this]
    apply bounded_union
    · exact hX a
    · exact ih

/-- Exercise 9.1.14 -/
example (I: Finset ℝ) : IsClosed (I:Set ℝ) ∧ Bornology.IsBounded (I:Set ℝ) := by
  constructor
  · rw [isClosed_def']
    intro x hx
    rcases adherentPt_is_limitPt_or_IsolatedPt hx with hlim | hiso
    · rw [LimitPt] at hlim
      simp [AdherentPt, Real.adherent'] at hx hlim
      by_contra hxI
      rw [Finset.mem_coe] at hxI
      have key : ∀ (s : Finset ℝ), x ∉ s → ∃ δ > 0, ∀ y ∈ s, δ ≤ |x - y| := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp; use 1; norm_num
        | @insert a s ha ih =>
          intro hxins
          simp at hxins
          obtain ⟨hxa, hxs⟩ := hxins
          obtain ⟨δ, hδ, hbound⟩ := ih hxs
          have hda : 0 < |x - a| := by grind
          use min δ |x - a|; constructor <;> grind
      obtain ⟨δ, hδ, hbound⟩ := key I hxI
      obtain ⟨y, hyI, hyle⟩ := hx (δ / 2) (by linarith)
      have hb : δ ≤ |x - y| := hbound y hyI
      linarith
    · rw [IsolatedPt] at hiso
      exact hiso.1
  · have key : ∀ (s : Finset ℝ), ∃ bd > 0, ∀ y ∈ s, |y| ≤ bd := by
      intro s
      induction s using Finset.induction_on with
      | empty => use 1; simp
      | @insert a s ha ih =>
        choose bd hbdpos hbdd using ih
        use max |a| bd; constructor
        · positivity
        · intro y hy; simp at hy
          rcases hy with ha | hs <;> grind
    choose bd hbdpos hbdd using key I
    rw [isBounded_def]
    use bd; refine ⟨hbdpos, ?_⟩
    intro i hi
    specialize hbdd i hi
    simp
    grind

/-- Exercise 9.1.15 -/
example {E:Set ℝ} (hE: Bornology.IsBounded E) (hnon: E.Nonempty): AdherentPt (sSup E) E ∧ AdherentPt (sSup E) Eᶜ := by
  rw [isBounded_def] at hE
  choose M hMpos hMbb using hE
  have hEbdab : BddAbove E := by
    use M
    intro m hm
    exact (hMbb hm).2
  constructor
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    have : sSup E - ε < sSup E := by linarith
    obtain ⟨a, haE, ha⟩ := exists_lt_of_lt_csSup hnon this
    use a; refine ⟨haE, ?_⟩
    rw [abs_le]; constructor
    · have := le_csSup hEbdab haE
      linarith
    · linarith
  · simp [AdherentPt, Real.adherent']
    intro ε hε
    have : sSup E  < sSup E + ε := by linarith
    use sSup E + ε; constructor
    · by_contra! h
      have := le_csSup hEbdab h; simp at this
      linarith
    · simp; grind

end Chapter9
