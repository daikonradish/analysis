import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.ContinuousOn
import Analysis.Section_9_3
/-!
# Analysis I, Section 9.4: Continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuity of functions, using the Mathlib notions

-/

namespace Chapter9

/--
Definition 9.4.1.  Here we use the Mathlib definition of continuity.  The hypothesis {lean}`x₀ ∈ X` is not needed!
-/
theorem ContinuousWithinAt.iff (X:Set ℝ) (f: ℝ → ℝ)  (x₀:ℝ) :
  ContinuousWithinAt f X x₀ ↔ Convergesto X f (f x₀) x₀ := by
  rw [ContinuousWithinAt.eq_1, Convergesto.iff, nhdsWithin.eq_1]

#check ContinuousOn.eq_1
#check continuousOn_univ
#check continuousWithinAt_univ


/-- Example 9.4.2 --/
example (c x₀:ℝ) : ContinuousWithinAt (fun x ↦ c) .univ x₀ := by
  rw [ContinuousWithinAt.iff]
  apply Convergesto.const


example (c x₀:ℝ) : ContinuousAt (fun x ↦ c) x₀ := by
  unfold ContinuousAt
  simp


example (c:ℝ) : ContinuousOn (fun x:ℝ ↦ c) .univ := by
  rw [ContinuousOn.eq_1]
  intro x hx
  rw [ContinuousWithinAt.iff]
  apply Convergesto.const


example (c:ℝ) : Continuous (fun x:ℝ ↦ c) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold ContinuousAt
  simp

/-- Example 9.4.3 --/
example : Continuous (fun x:ℝ ↦ x) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_id' x

/-- Example 9.4.4 --/
example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt Real.sign x₀ := by
  unfold ContinuousAt Real.sign
  rcases h.lt_or_gt with hneg | hpos
  · rw [if_pos (by linarith)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Iio_mem_nhds hneg] with r hr
    simp at hr
    rw [if_pos (by linarith)]
  · rw [if_neg (by linarith), if_pos (by linarith)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioi_mem_nhds hpos] with r hr
    simp at hr
    rw [if_neg (by linarith), if_pos (by linarith)]


example  :¬ ContinuousAt Real.sign 0 := by
  unfold Real.sign
  intro h
  have htt := h.tendsto
  rw [if_neg (by linarith), if_neg (by linarith)] at htt
  have hleft := htt.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0))
  have hleft' : Filter.Tendsto (fun (r:ℝ) ↦ if r < 0 then (-1:ℝ) else if 0 < r then 1 else 0)
    (nhdsWithin 0 (Set.Iio 0)) (nhds (-1)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp at hr ⊢
    grind
  have heq := tendsto_nhds_unique hleft hleft'
  simp at heq


/-- Example 9.4.5 --/
example (x₀:ℝ) : ¬ ContinuousAt f_9_3_21 x₀ := by
  unfold f_9_3_21
  intro h
  have htt := h.tendsto
  rw [Metric.tendsto_nhds_nhds] at htt
  specialize htt (1/2) (by linarith)
  contrapose htt
  push_neg
  intro δ hδ
  simp_rw [Real.dist_eq]
  by_cases!  hratx₀ : x₀ ∈ (fun (q:ℚ) ↦ (q:ℝ)) '' Set.univ
  · choose x hxl hxr using exists_irrational_btwn (x:=x₀-δ) (y:=x₀+δ) (by linarith)
    use x; constructor
    · grind
    · rw [if_neg, if_pos]
      · norm_num
      · exact hratx₀
      · contrapose hxl
        unfold Irrational; push_neg
        simp at hxl ⊢
        exact hxl
  · choose x hxl hxr using exists_rat_btwn (x:=x₀-δ) (y:=x₀+δ) (by linarith)
    use x; constructor
    · grind
    · rw [if_pos, if_neg]
      · norm_num
      · exact hratx₀
      · simp

/-- Example 9.4.6 --/
noncomputable abbrev f_9_4_6 (x:ℝ) : ℝ := if x ≥ 0 then 1 else 0

example {x₀:ℝ} (h: x₀ ≠ 0) : ContinuousAt f_9_4_6 x₀ := by
  unfold ContinuousAt f_9_4_6
  rcases h.lt_or_gt with hneg | hpos
  · rw [if_neg (by linarith)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Iio_mem_nhds hneg] with r hr
    rw [if_neg (by grind)]
  · rw [if_pos (by linarith)]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioi_mem_nhds hpos] with r hr
    rw [if_pos (by grind)]

example : ¬ ContinuousAt f_9_4_6 0 := by
  unfold f_9_4_6
  intro h
  have htt := h.tendsto
  rw [Metric.tendsto_nhds_nhds] at htt
  specialize htt (1/2) (by positivity)
  simp_rw [Real.dist_eq] at htt
  contrapose! htt
  intro δ hδ
  simp_rw [sub_zero]
  use -(δ/2); constructor
  · grind
  · rw [if_neg (by linarith), if_pos (by linarith)]
    norm_num

example : ContinuousWithinAt f_9_4_6 (.Ici 0) 0 := by
  rw [ContinuousWithinAt.eq_1]
  unfold f_9_4_6
  rw [if_pos (by linarith)]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [if_pos (by grind)]

/-- Proposition 9.4.7 / Exercise 9.4.1. -/
theorem ContinuousWithinAt.tfae (X:Set ℝ) (f: ℝ → ℝ) (x₀:ℝ) :
  [
    ContinuousWithinAt f X x₀,
    ∀ a:ℕ → ℝ, (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds x₀) → Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)),
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| < δ → |f x - f x₀| < ε,
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x-x₀| ≤ δ → |f x - f x₀| ≤ ε
  ].TFAE := by
    tfae_have 1 → 2 := by
      intro hcontwithin a ha htt
      have htt' := hcontwithin.tendsto
      rw [Metric.tendsto_atTop] at htt ⊢
      rw [Metric.tendsto_nhdsWithin_nhds] at htt'
      simp_rw [Real.dist_eq] at htt htt' ⊢
      intro ε hε
      choose δ hδpos hδ using htt' ε hε
      choose N hN using htt δ hδpos
      use N; intro n hn
      specialize hN n (by linarith)
      exact hδ (ha n) hN
    tfae_have 2 → 3 := by
      intro hseq ε hε
      contrapose! hseq
      have hseq' : ∀ N : ℕ, ∃ x ∈ X, |x - x₀| < 1/(N+1) ∧ ε ≤ |f x - f x₀| := by
        intro N
        exact hseq (1/(N+1)) (by positivity)
      choose a haN hadist hfdist using hseq'
      use a, haN
      constructor
      · rw [tendsto_iff_dist_tendsto_zero]
        apply squeeze_zero (g0 := tendsto_one_div_add_atTop_nhds_zero_nat)
        · intro _; apply dist_nonneg
        · intro n; rw [Real.dist_eq]
          linarith [hadist n]
      · intro htt
        rw [Metric.tendsto_atTop] at htt
        simp_rw [Real.dist_eq] at htt
        choose N hN using htt ε hε
        specialize hfdist N
        specialize hN N (by linarith)
        linarith
    tfae_have 3 → 4 := by
      intro h ε hε
      contrapose! h
      use ε, hε
      intro δ hδ
      choose x hxmem hxδ hfε using h (δ/2) (by positivity)
      use x; refine ⟨hxmem, ?_, ?_⟩
      · linarith
      · linarith
    tfae_have 4 → 1 := by
      intro h
      rw [Metric.continuousWithinAt_iff]
      simp_rw [Real.dist_eq]
      intro ε hε
      choose δ hδ hdist using h (ε/2) (by positivity)
      use (δ/2); refine ⟨by positivity, ?_⟩
      intro x hx hhalfdist
      specialize hdist x hx (by linarith)
      linarith
    tfae_finish


/-- Remark 9.4.8. -/
theorem _root_.Filter.Tendsto.comp_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h_cont: ContinuousWithinAt f X x₀) {a: ℕ → ℝ} (ha: ∀ n, a n ∈ X)
  (hconv: Filter.atTop.Tendsto a (nhds x₀)):
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds (f x₀)) := by
  have := (ContinuousWithinAt.tfae X f x₀).out 0 1
  grind

/- Proposition 9.4.9 -/
theorem ContinuousWithinAt.add {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f + g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.add hg using 1


theorem ContinuousWithinAt.sub {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f - g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.sub hg using 1

theorem ContinuousWithinAt.max {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (max f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.max hg using 1


theorem ContinuousWithinAt.min {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (min f g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.min hg using 1


theorem ContinuousWithinAt.mul' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ}
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f * g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.mul hg using 1

theorem ContinuousWithinAt.div' {X:Set ℝ} (f g: ℝ → ℝ) {x₀:ℝ} (hM: g x₀ ≠ 0)
  (hf: ContinuousWithinAt f X x₀) (hg: ContinuousWithinAt g X x₀) :
  ContinuousWithinAt (f / g) X x₀ := by
  rw [iff] at hf hg ⊢; convert hf.div hM hg using 1

/-- Proposition 9.4.10 / Exercise 9.4.3  -/
theorem Continuous.exp {a:ℝ} (ha: a>0) : Continuous (fun x:ℝ ↦ a ^ x) := by
  refine Real.continuous_const_rpow ?_
  linarith

/-- Proposition 9.4.11 / Exercise 9.4.4 -/
theorem Continuous.exp' (p:ℝ) : ContinuousOn (fun x:ℝ ↦ x ^ p) (.Ioi 0) := by
  intro x hx
  apply continuousWithinAt_id.rpow_const
  simp at hx ⊢
  left; linarith

/-- Proposition 9.4.12 -/
theorem Continuous.abs : Continuous (fun x:ℝ ↦ |x|) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  simp_rw [Real.dist_eq]
  use ε, hε
  intro a ha
  grind

/-- Proposition 9.4.13 / Exercise 9.4.5 -/
theorem ContinuousWithinAt.comp {X Y: Set ℝ} {f g:ℝ → ℝ} (hf: ∀ x ∈ X, f x ∈ Y) (x₀:ℝ)
  (hf_cont: ContinuousWithinAt f X x₀) (hg_cont: ContinuousWithinAt g Y (f x₀)):
  ContinuousWithinAt (g ∘ f) X x₀ := by
  rw [Metric.continuousWithinAt_iff] at hf_cont hg_cont ⊢
  intro ε hε
  choose η hηpos hη using hg_cont ε hε
  choose δ hδpos hδ using hf_cont η hηpos
  use δ; refine ⟨hδpos, ?_⟩
  intro x hx hdist
  specialize hδ hx hdist
  exact hη (hf x hx) hδ


/-- Example 9.4.14 -/
example : Continuous (fun x:ℝ ↦ 3*x + 1) := by
  exact (continuous_id.const_mul 3).add_const 1

example : Continuous (fun x:ℝ ↦ (5:ℝ)^x) := by
  apply Continuous.exp (by linarith)

example : Continuous (fun x:ℝ ↦ (5:ℝ)^(3*x+1)) := by
  apply Continuous.rpow
  · apply continuous_const
  · exact (continuous_id.const_mul 3).add_const 1
  · intro _; left; norm_num

example : Continuous (fun x:ℝ ↦ |x^2-8*x+8|^(Real.sqrt 2) / (x^2 + 1)) := by
  apply Continuous.div
  · apply Continuous.rpow
    · apply _root_.Continuous.abs
      have hsq : Continuous fun (x:ℝ) ↦ x ^ 2 := continuous_id.pow 2
      have h8 : Continuous fun (x:ℝ) ↦ -8 * x := continuous_id.const_mul (-8)
      convert hsq.add (h8.add_const 8) using 1
      ext x; simp; grind
    · apply continuous_const
    · intro x; right; norm_num
  · exact (continuous_id.pow 2).add_const 1
  · intro x
    have : x ^ 2 ≥  0 := by exact sq_nonneg x
    linarith

/-- Exercise 9.4.6 -/
theorem ContinuousOn.restrict {X Y:Set ℝ} {f: ℝ → ℝ} (hY: Y ⊆ X) (hf: ContinuousOn f X) : ContinuousOn f Y := by

  sorry

/-- Exercise 9.4.7 -/
theorem Continuous.polynomial {n:ℕ} (c: Fin n → ℝ) : Continuous (fun x:ℝ ↦ ∑ i, c i * x ^ (i:ℕ)) := by
  sorry
