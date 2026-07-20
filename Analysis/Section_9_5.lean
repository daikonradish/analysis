import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.5: Left and right limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Left and right limits.
-/

namespace Chapter9

/-- Definition 9.5.1.  We give left and right limits the "junk" value of 0 if the limit does not exist. -/
abbrev RightLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev right_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h : RightLimitExists X f x₀ then h.choose else 0

abbrev LeftLimitExists (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop := ∃ L, (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)

open Classical in
noncomputable abbrev left_limit (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : ℝ := if h: LeftLimitExists X f x₀ then h.choose else 0

theorem right_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds L)) : RightLimitExists X f x₀ ∧ right_limit X f x₀ = L := by
  have h' : RightLimitExists X f x₀ := by use L
  simp [right_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Ioi x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem left_limit.eq {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} {L:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds L)) : LeftLimitExists X f x₀ ∧ left_limit X f x₀ = L := by
  have h' : LeftLimitExists X f x₀ := by use L
  simp [left_limit, h']
  have hne : (nhdsWithin x₀ (X ∩ .Iio x₀)).NeBot := by
    rwa [←mem_closure_iff_nhdsWithin_neBot, closure_def']
  exact tendsto_nhds_unique h'.choose_spec h

theorem right_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: RightLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (right_limit X f x₀)) := by
  simp [right_limit, h]; exact h.choose_spec

theorem left_limit.eq' {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: LeftLimitExists X f x₀) :
  (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (left_limit X f x₀)) := by
  simp [left_limit, h]; exact h.choose_spec

/-- Example 9.5.2.  The second part of this example is no longer operative as we assign "junk" values to our functions instead of leaving them undefined. -/
example : right_limit .univ Real.sign 0 = 1 := by
  have hlim : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto Real.sign (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp at hx; unfold Real.sign
    rw [if_neg (by linarith), if_pos (by linarith)]
  have had: AdherentPt 0 (.univ ∩ .Ioi 0) := by
    intro ε hε
    use ε / 2
    simp; grind
  exact (right_limit.eq had hlim).2

example : left_limit .univ Real.sign 0 = -1 := by
  have hlim : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto Real.sign (nhds (-1)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp at hx; unfold Real.sign
    rw [if_pos (by linarith)]
  have had: AdherentPt 0 (.univ ∩ .Iio 0) := by
    intro ε hε
    use -(ε / 2)
    simp; grind
  exact (left_limit.eq had hlim).2

theorem right_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Ioi x₀))
  (h: RightLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Ioi x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (right_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

theorem left_limit.conv {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (had: AdherentPt x₀ (X ∩ .Iio x₀))
  (h: LeftLimitExists X f x₀)
  (a:ℕ → ℝ) (ha: ∀ n, a n ∈ X ∩ .Iio x₀)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (left_limit X f x₀)) := by
  choose L hL using h
  apply Convergesto.comp _ ha hconv
  rwa [Convergesto.iff, (eq had hL).2]

/-- Proposition 9.5.3 -/
theorem ContinuousAt.iff_eq_left_right_limit {X: Set ℝ} {f: ℝ → ℝ} {x₀:ℝ} (h: x₀ ∈ X)
  (had_left: AdherentPt x₀ (X ∩ .Iio x₀)) (had_right: AdherentPt x₀ (X ∩ .Ioi x₀)) :
  ContinuousWithinAt f X x₀ ↔ (RightLimitExists X f x₀ ∧ right_limit X f x₀ = f x₀) ∧ (LeftLimitExists X f x₀ ∧ left_limit X f x₀ = f x₀) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro hcontwithin
    -- 0 ↔ 2 : ContinuousWithinAt ↔ ε-δ balls
    have hball := ((ContinuousWithinAt.tfae X f x₀).out 0 2).mp hcontwithin
    constructor
    · have hnhdswithin : (nhdsWithin x₀ (X ∩ .Ioi x₀)).Tendsto f (nhds (f x₀)) := by
        simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
        intro ε hε
        choose δ hδpos hδ using hball ε hε
        use δ; constructor
        · exact hδpos
        · intro x hx hdist
          exact hδ x hx.1 hdist
      exact right_limit.eq had_right hnhdswithin
    · have hnhdswithin : (nhdsWithin x₀ (X ∩ .Iio x₀)).Tendsto f (nhds (f x₀)) := by
        simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
        intro ε hε
        choose δ hδpos hδ using hball ε hε
        use δ; constructor
        · exact hδpos
        · intro x hx hdist
          exact hδ x hx.1 hdist
      exact left_limit.eq had_left hnhdswithin
  intro ⟨ ⟨ hre, hright⟩, ⟨ hle, lheft ⟩ ⟩
  set L := f x₀
  have := (ContinuousWithinAt.tfae X f x₀).out 0 2
  rw [this]
  intro ε hε
  apply right_limit.eq' at hre
  apply left_limit.eq' at hle
  rw [hright, ←Convergesto.iff] at hre
  rw [lheft, ←Convergesto.iff] at hle
  simp [Convergesto, Real.CloseNear, Real.CloseFn] at hre hle
  choose δ_plus hδ_plus hre using hre ε hε
  choose δ_minus hδ_minus hle using hle ε hε
  use min δ_plus δ_minus, (by positivity)
  intro x hx hxx₀
  simp at hxx₀; obtain ⟨hxx₀plus, hxx₀minus⟩ := hxx₀
  rw [abs_lt] at hxx₀plus hxx₀minus
  obtain hlt | rfl | hgt := lt_trichotomy x x₀
  . exact hle x hx hlt (by linarith) (by linarith)
  . simp; exact hε
  exact hre x hx hgt (by linarith) (by linarith)

abbrev HasJumpDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ ≠ left_limit X f x₀

example : HasJumpDiscontinuity .univ Real.sign 0 := by
  have hadright : AdherentPt 0 (.univ ∩ .Ioi 0) := by
    intro ε hε
    use ε / 2; simp; grind
  have hnhdswhtnright : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto Real.sign (nhds 1) := by
    simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
    intro ε hε
    use ε; constructor
    · exact hε
    · intro x hx hdist; simp at hx
      unfold Real.sign
      rw [if_neg (by linarith), if_pos (by linarith)]; simp
      exact hε
  have hright := right_limit.eq hadright hnhdswhtnright
  have hadleft : AdherentPt 0 (.univ ∩ .Iio 0) := by
    intro ε hε
    use (-ε / 2); simp; grind
  have hnhdswhtnleft : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto Real.sign (nhds (-1)) := by
    simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
    intro ε hε
    use ε; constructor
    · exact hε
    · intro x hx hdist; simp at hx
      unfold Real.sign
      rw [if_pos (by linarith)]; simp
      exact hε
  have hleft := left_limit.eq hadleft hnhdswhtnleft
  refine ⟨hright.1, hleft.1, ?_⟩
  rw [hright.2, hleft.2]
  norm_num

abbrev HasRemovableDiscontinuity (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) : Prop :=
  RightLimitExists X f x₀ ∧ LeftLimitExists X f x₀ ∧ right_limit X f x₀ = left_limit X f x₀
  ∧ right_limit X f x₀ ≠ f x₀

example : HasRemovableDiscontinuity .univ f_9_3_17 0 := by
  have hadright : AdherentPt 0 (.univ ∩ .Ioi 0) := by
    intro ε hε
    use ε / 2; simp; grind
  have hnhdswhtnright : (nhdsWithin 0 (.univ ∩ .Ioi 0)).Tendsto f_9_3_17 (nhds 0) := by
    simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
    intro ε hε
    use ε; constructor
    · exact hε
    · intro x hx hdist; simp at hx
      unfold f_9_3_17
      rw [if_neg (by linarith)]; simp
      exact hε
  have hright := right_limit.eq hadright hnhdswhtnright
  have hadleft : AdherentPt 0 (.univ ∩ .Iio 0) := by
    intro ε hε
    use (-ε / 2); simp; grind
  have hnhdswhtnleft : (nhdsWithin 0 (.univ ∩ .Iio 0)).Tendsto f_9_3_17 (nhds 0) := by
    simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
    intro ε hε
    use ε; constructor
    · exact hε
    · intro x hx hdist; simp at hx
      unfold f_9_3_17
      rw [if_neg (by linarith)]; simp
      exact hε
  have hleft := left_limit.eq hadleft hnhdswhtnleft
  refine ⟨hright.1, hleft.1, ?_, ?_⟩
  · rw [hright.2, hleft.2]
  · conv_rhs => unfold f_9_3_17
    rw [hright.2, if_pos (by linarith)]
    norm_num

example : ¬ HasRemovableDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  unfold HasRemovableDiscontinuity
  push_neg
  intro hright hleft hlimeq
  choose L hL using hright
  simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq] at hL
  choose δ hδpos hδ using hL 1 (by positivity)
  contrapose hδ
  push_neg
  simp
  set x := min (δ / 2) (1/(|L|+1))
  use x; refine ⟨?_, ?_, ?_⟩
  · positivity
  · unfold x; rw [abs_of_pos (by positivity)]
    simp; left; exact hδpos
  · have h  : x > 0 := by positivity
    have h' : x⁻¹ > 0 := by positivity
    have h1 : x ≤ 1/(|L|+1) := by unfold x; simp
    have h2 : x * (|L| + 1) ≤ 1 := by field_simp at h1; linarith
    have h3 : |L| + 1 ≤ x⁻¹ := by field_simp; linarith
    grind

example : ¬ HasJumpDiscontinuity .univ (fun x ↦ 1/x) 0 := by
  unfold HasJumpDiscontinuity
  push_neg
  intro hright hleft
  choose L hL using hright
  simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq] at hL
  choose δ hδpos hδ using hL 1 (by positivity)
  contrapose hδ
  push_neg
  simp
  set x := min (δ / 2) (1/(|L|+1))
  use x; refine ⟨?_, ?_, ?_⟩
  · positivity
  · unfold x; rw [abs_of_pos (by positivity)]
    simp; left; exact hδpos
  · have h  : x > 0 := by positivity
    have h' : x⁻¹ > 0 := by positivity
    have h1 : x ≤ 1/(|L|+1) := by unfold x; simp
    have h2 : x * (|L| + 1) ≤ 1 := by field_simp at h1; linarith
    have h3 : |L| + 1 ≤ x⁻¹ := by field_simp; linarith
    grind


/- Exercise 9.5.1: Write down a definition of what it would mean for a limit of a function to be `+∞` or `-∞`, apply to `fun x ↦ 1/x`, and state and prove a version of Proposition 9.3.9. -/
abbrev ConvergesToPosInfinity (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin x₀ X) Filter.atTop

abbrev ConvergesToNegInfinity (X : Set ℝ) (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin x₀ X) Filter.atBot

theorem converges_to_pos_infinity_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToPosInfinity X f x₀ ↔ ∀ B:ℝ, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → B ≤ f x := by
  constructor
  · intro hconv
    unfold ConvergesToPosInfinity at hconv
    rw [Filter.tendsto_atTop] at hconv
    intro B
    specialize hconv B
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hconv
    simp_rw [Real.dist_eq] at hconv
    choose δ hδpos hδ using hconv
    use δ; constructor
    · exact hδpos
    · intro x hx hxdist
      exact hδ hxdist hx
  · intro hB
    unfold ConvergesToPosInfinity
    rw [Filter.tendsto_atTop]
    simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    intro B
    choose δ hδpos hδ using hB B
    use δ; constructor
    · exact hδpos
    · simp_rw [Real.dist_eq]
      intro x hx hxmem
      exact hδ x hxmem hx

theorem converges_to_neg_infinity_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToNegInfinity X f x₀ ↔ ∀ B:ℝ, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → f x ≤ B := by
  constructor
  · intro hconv
    unfold ConvergesToNegInfinity at hconv
    rw [Filter.tendsto_atBot] at hconv
    intro B
    specialize hconv B
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hconv
    simp_rw [Real.dist_eq] at hconv
    choose δ hδpos hδ using hconv
    use δ; constructor
    · exact hδpos
    · intro x hx hxdist
      exact hδ hxdist hx
  · intro hB
    unfold ConvergesToNegInfinity
    rw [Filter.tendsto_atBot]
    simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    intro B
    choose δ hδpos hδ using hB B
    use δ; constructor
    · exact hδpos
    · simp_rw [Real.dist_eq]
      intro x hx hxmem
      exact hδ x hxmem hx

-- sequential characterization
theorem converges_to_pos_infinity_sequential_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToPosInfinity X f x₀ ↔
    ∀ (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n ∈ X) (hconv : Filter.Tendsto a Filter.atTop (nhds x₀)),
      Filter.Tendsto (fun n => f (a n)) Filter.atTop Filter.atTop := by
  constructor
  · intro hconv a ha httx₀
    unfold ConvergesToPosInfinity at hconv
    simp_rw [Filter.tendsto_atTop, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq] at hconv
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at httx₀
    simp_rw [Filter.tendsto_atTop, Filter.eventually_atTop]
    intro B
    choose ε hεpos hε using hconv B
    choose N hN using httx₀ ε hεpos
    use N; intro n hn
    specialize hN n hn
    exact hε hN (ha n)
  · intro hconv
    contrapose! hconv
    unfold ConvergesToPosInfinity at hconv
    simp_rw [Filter.tendsto_atTop, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq] at hconv
    push_neg at hconv
    choose B hB using hconv
    have hn : ∀ n : ℕ, ∃ x ∈ X, |x - x₀| < 1/((n:ℝ)+1) ∧ f x < B := by
      intro n
      choose x hxmem hx hfx using hB (1/((n:ℝ)+1)) (by positivity)
      use x
    choose a hamem hadist haB using hn
    use a; refine ⟨hamem, ?_, ?_⟩
    · rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (g0 := tendsto_one_div_add_atTop_nhds_zero_nat)
      · intro n; apply abs_nonneg
      · intro n; rw [Real.dist_eq]
        linarith [hadist n]
    · intro hdiverge
      simp_rw [Filter.tendsto_atTop, Filter.eventually_atTop] at hdiverge
      choose N hN using hdiverge (B + 100000)
      specialize hN N (by rfl)
      specialize haB N
      linarith


theorem converges_to_neg_infinity_sequential_iff (X: Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  ConvergesToNegInfinity X f x₀ ↔
    ∀ (a : ℕ → ℝ) (ha : ∀ n : ℕ, a n ∈ X) (hconv : Filter.Tendsto a Filter.atTop (nhds x₀)),
      Filter.Tendsto (fun n => f (a n)) Filter.atTop Filter.atBot := by
  constructor
  · intro hconv a ha httx₀
    unfold ConvergesToPosInfinity at hconv
    simp_rw [Filter.tendsto_atBot, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq] at hconv
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at httx₀
    simp_rw [Filter.tendsto_atBot, Filter.eventually_atTop]
    intro B
    choose ε hεpos hε using hconv B
    choose N hN using httx₀ ε hεpos
    use N; intro n hn
    specialize hN n hn
    exact hε hN (ha n)
  · intro hconv
    contrapose! hconv
    unfold ConvergesToNegInfinity at hconv
    simp_rw [Filter.tendsto_atBot, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq] at hconv
    push_neg at hconv
    choose B hB using hconv
    have hn : ∀ n : ℕ, ∃ x ∈ X, |x - x₀| < 1/((n:ℝ)+1) ∧ B < f x := by
      intro n
      choose x hxmem hx hfx using hB (1/((n:ℝ)+1)) (by positivity)
      use x
    choose a hamem hadist haB using hn
    use a; refine ⟨hamem, ?_, ?_⟩
    · rw [tendsto_iff_dist_tendsto_zero]
      apply squeeze_zero (g0 := tendsto_one_div_add_atTop_nhds_zero_nat)
      · intro n; apply abs_nonneg
      · intro n; rw [Real.dist_eq]
        linarith [hadist n]
    · intro hdiverge
      simp_rw [Filter.tendsto_atBot, Filter.eventually_atTop] at hdiverge
      choose N hN using hdiverge (B - 100000)
      specialize hN N (by rfl)
      specialize haB N
      linarith

example : ConvergesToPosInfinity (.Ioi 0) (fun x ↦ 1/x) 0 := by
  simp_rw [Filter.tendsto_atTop, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq]
  intro B
  by_cases! hB : B ≤ 0
  · use 1; simp;
    intro y hy hypos
    field_simp
    nlinarith
  · use 1 / B; simp
    constructor
    · exact hB
    · intro y hy hypos
      field_simp at hy ⊢
      rw [abs_of_pos hypos] at hy
      linarith

end Chapter9
