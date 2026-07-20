import Mathlib.Tactic
import Analysis.Section_10_2


/-!
# Analysis I, Section 10.3: Monotone functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relations between monotonicity and differentiability.

-/

namespace Chapter10

#check _root_.HasDerivWithinAt.mean_value
/-- Proposition 10.3.1 / Exercise 10.3.1 -/
theorem derivative_of_monotone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Monotone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≥ 0 := by
  have hderivwithin := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hderivwithin
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := by exact hx₀.neBot
  refine ge_of_tendsto hderivwithin ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [slope_def_field]
  rcases lt_trichotomy a x₀ with hlt | heq | hgt
  . have h1 : a - x₀ ≤  0 := by linarith
    have h2 : f a - f x₀ ≤ 0 := by
      suffices f a ≤ f x₀ by linarith
      apply hmono
      linarith
    exact div_nonneg_of_nonpos h2 h1
  . subst heq; simp
  . have h1 : 0 ≤ a - x₀ := by linarith
    have h2 : 0 ≤ f a - f x₀ := by
      suffices  f x₀ ≤ f a by linarith
      apply hmono
      linarith
    exact div_nonneg h2 h1

theorem derivative_of_antitone (X:Set ℝ) {x₀:ℝ} (hx₀: ClusterPt x₀ (.principal (X \ {x₀})))
  {f:ℝ → ℝ} (hmono: Antitone f) (hderiv: DifferentiableWithinAt ℝ f X x₀) :
    derivWithin f X x₀ ≤ 0 := by
  have hderivwithin := hderiv.hasDerivWithinAt
  rw [hasDerivWithinAt_iff_tendsto_slope] at hderivwithin
  haveI : (nhdsWithin x₀ (X \ {x₀})).NeBot := by exact hx₀.neBot
  refine le_of_tendsto hderivwithin ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [slope_def_field]
  rcases lt_trichotomy a x₀ with hlt | heq | hgt
  . have h1 : a - x₀ ≤ 0 := by linarith
    have h2 : 0 ≤ f a - f x₀ := by
      suffices f x₀ ≤ f a by linarith
      apply hmono
      linarith
    exact div_nonpos_of_nonneg_of_nonpos h2 h1
  . subst heq; simp
  . have h1 : 0 ≤ a - x₀ := by linarith
    have h2 : f a - f x₀ ≤ 0 := by
      suffices f a ≤ f x₀ by linarith
      apply hmono
      linarith
    exact div_nonpos_of_nonpos_of_nonneg h2 h1

/-- Proposition 10.3.3 / Exercise 10.3.4 -/
theorem strictMono_of_positive_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hpos: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x > 0) :
    StrictMonoOn f (.Icc a b) := by
  intro x hx y hy hxy
  have hinab : Set.Icc x y ⊆ Set.Icc a b := by
    intro p hp
    simp at hx hy hp ⊢
    constructor <;> linarith
  have hxyderiv: DifferentiableOn ℝ f (.Ioo x y) := by
    apply hderiv.mono
    apply Set.Ioo_subset_Icc_self.trans
    exact hinab
  have hxycont : ContinuousOn f (.Icc x y) := by
    have habcont : ContinuousOn f (.Icc a b) := by
      apply ContinuousOn.of_differentiableOn
      exact hderiv
    apply habcont.mono
    exact hinab
  choose m hminxy hmderivinxy using _root_.HasDerivWithinAt.mean_value hxy hxycont hxyderiv
  specialize hpos m (by grind)
  -- extract the equality
  have hmderivinab :  HasDerivWithinAt f ((f y - f x) / (y - x)) (Set.Icc a b) m := by
    have hatm : HasDerivAt f ((f y - f x) / (y - x)) m := by
      apply hmderivinxy.hasDerivAt
      apply Ioo_mem_nhds
      . exact hminxy.1
      . exact hminxy.2
    exact hatm.hasDerivWithinAt
  have huniqinab := uniqueDiffOn_Icc (a:=a) (b:=b) (by grind) m (by grind)
  have hfeq := hmderivinab.derivWithin huniqinab
  rw [hfeq] at hpos
  have hxy' : y - x > 0 := by linarith
  have hmulpos := mul_pos hpos hxy'
  field_simp at hmulpos
  linarith

theorem strictAnti_of_negative_derivative {a b:ℝ} {f:ℝ → ℝ}
  (hderiv: DifferentiableOn ℝ f (.Icc a b)) (hneg: ∀ x ∈ Set.Ioo a b, derivWithin f (.Icc a b) x < 0) :
    StrictAntiOn f (.Icc a b) := by
  -- theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  --(hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  --∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  intro x hx y hy hxy
  have hxycont : ContinuousOn f (Set.Icc x y) := by
    apply hderiv.continuousOn.mono
    grind
  have hxyderiv : DifferentiableOn ℝ f (.Ioo x y) := by
    apply hderiv.mono
    grind
  choose m hmxy hmderiv using _root_.HasDerivWithinAt.mean_value hxy hxycont hxyderiv
  specialize hneg m (by grind)
  have hderivinab : HasDerivWithinAt f ((f y - f x) / (y - x)) (Set.Icc a b) m := by
    have hatm := hmderiv.hasDerivAt (by apply Ioo_mem_nhds; grind; grind)
    exact hatm.hasDerivWithinAt
  have huniqueinab := uniqueDiffOn_Icc (a:=a) (b:=b) (by grind) m (by grind)
  have hfeq := hderivinab.derivWithin huniqueinab
  rw [hfeq] at hneg
  have hxy' : y - x > 0 := by linarith
  have hmulneg := mul_neg_of_pos_of_neg hxy' hneg
  field_simp at hmulneg
  linarith


/-- Example 10.3.2 -/
example : ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ ¬ DifferentiableAt ℝ f 0 := by
  use fun x => if x ≤ 0 then x else x^2
  refine ⟨?_, ?_, ?_⟩
  . have hg'cont : Continuous (fun (x:ℝ) => x ^ 2) := by
      exact continuous_id.pow 2
    have hf'cont : Continuous (fun (x:ℝ) => x) := by
      exact continuous_id
    exact Continuous.if_le (f:=id) (g:=0) (hf':=hf'cont) (hg':=hg'cont) (hf:=continuous_id) (hg:=continuous_const)
      (by intro x hx; simp at hx; subst hx; simp)
  . intro x y hxy
    simp
    split_ifs <;> first | linarith | nlinarith
  . intro hdiff
    have hderivat := hdiff.hasDerivAt
    generalize deriv (fun (x:ℝ) ↦ if x ≤ 0 then x else x ^ 2) 0 = d at hderivat
    have hleft := hderivat.hasDerivWithinAt (s:=Set.Iic 0)
    have hleft' : HasDerivWithinAt (fun (x:ℝ) ↦  x) 1 (Set.Iic 0) 0 := by
      simpa using (hasDerivAt_id 0).hasDerivWithinAt
    have hleft'' : HasDerivWithinAt (fun (x:ℝ) ↦ if x ≤ 0 then x else x ^ 2) 1 (Set.Iic 0) 0 := by
      refine hleft'.congr ?_ ?_
      . intro x hx; simp at hx ⊢
        intro hx'; exfalso; linarith
      . simp
    have hright := hderivat.hasDerivWithinAt (s:=Set.Ici 0)
    have hright' : HasDerivWithinAt (fun (x:ℝ) ↦  x ^ 2) 0 (Set.Ici 0) 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).hasDerivWithinAt
    have hright'' : HasDerivWithinAt (fun (x:ℝ) ↦ if x ≤ 0 then x else x ^ 2) 0 (Set.Ici 0) 0 := by
      refine hright'.congr ?_ ?_
      . intro x hx; simp
        intro hx'
        simp at hx; have : x = 0 := by linarith
        subst this; simp
      . simp
    have huleft : UniqueDiffWithinAt ℝ (Set.Iic (0:ℝ)) 0 := by exact uniqueDiffWithinAt_Iic 0
    have huright : UniqueDiffWithinAt ℝ (Set.Ici (0:ℝ)) 0 := by exact uniqueDiffWithinAt_Ici 0
    have hdleft := hleft.derivWithin huleft
    have hd0 := hleft''.derivWithin huleft
    have hdright := hright.derivWithin huright
    have hd1 := hright''.derivWithin huright
    linarith

example : ∃ f: ℝ → ℝ, StrictMono f ∧ Differentiable ℝ f ∧ deriv f 0 = 0 := by
  use fun x => x ^ 3
  refine ⟨?_, ?_, ?_⟩
  . intro x y hxy
    simp
    rw [show 3 = 1 + 2 by norm_num]
    rw [pow_add, pow_add]; simp
    by_cases! hx : x ≥ 0 <;> by_cases! hy : y ≥ 0
    . observe : x ^ 2 ≥ 0
      observe : y ^ 2 ≥ 0
      gcongr
    . exfalso; linarith
    . observe : y ^ 2 ≥ 0
      observe : y * y ^ 2 ≥ 0
      observe : x ^ 2 > 0
      observe : x * x ^ 2 < 0
      linarith
    . observe : x ^ 2 ≥ 0
      observe : y ^ 2 ≥ 0
      have := mul_pos_of_neg_of_neg hx hy
      nlinarith
  . exact differentiable_id.pow 3
  . have := (hasDerivAt_pow 3 (0:ℝ)).deriv
    convert this
    simp

/-- Exercise 10.3.5 -/
example : ∃ (X : Set ℝ) (f : ℝ → ℝ), DifferentiableOn ℝ f X ∧
  (∀ x ∈ X, derivWithin f X x > 0) ∧ ¬ StrictMonoOn f X  := by
  use Set.Ioo (-1:ℝ) 0 ∪ Set.Ioo 0 1
  use fun x => if x ≤ 0 then x else x-1
  refine ⟨?_, ?_, ?_⟩
  . refine (differentiableOn_union_iff_of_isOpen ?AOpen ?BOpen?).mpr ⟨?diffA, ?diffB⟩
    . exact isOpen_Ioo
    . exact isOpen_Ioo
    . have hid : DifferentiableOn ℝ (fun x => x) (Set.Ioo (-1:ℝ) 0) := by
        exact differentiableOn_id
      apply hid.congr
      intro x hx; simp at hx
      simp; linarith
    . have hid : DifferentiableOn ℝ (fun x => x - 1) (Set.Ioo (0:ℝ) 1) := by
        exact differentiableOn_id.sub_const 1
      apply hid.congr
      intro x hx; simp at hx
      simp; intro hx'
      exfalso; linarith
  . have hdA : ∀ p ∈ (Set.Ioo (-1:ℝ) 0), derivWithin (fun x => x) (Set.Ioo (-1:ℝ) 0) p = 1 := by
      intro p hp
      refine (derivative_unique' (Set.Ioo (-1) 0) ?clusterPt ?hasDerivWithinAt ?differentiableWithinAt).symm
      . simp_rw [← mem_closure_iff_clusterPt, Metric.mem_closure_iff, Real.dist_eq]
        intro ε hε; simp at hp; obtain ⟨hl, hr⟩ := hp
        set δ := min (ε / 2) ((p+1)/2)
        have : p + 1 > 0 := by linarith
        have hδpos : δ > 0 := by positivity
        have hδε : δ < ε := by grind
        have hδp1 : δ < (p + 1) := by grind
        use p - δ; constructor <;> grind
      . apply hasDerivWithinAt_id
      · exact differentiableWithinAt_id
    have hdB : ∀ p ∈ (Set.Ioo (0:ℝ) 1), derivWithin (fun x => x - 1) (Set.Ioo (0:ℝ) 1) p = 1 := by
      intro p hp
      refine (derivative_unique' (Set.Ioo (0:ℝ) 1) ?clusterPt' ?hasDerivWithinAt' ?differentiableWithinAt').symm
      . simp_rw [← mem_closure_iff_clusterPt, Metric.mem_closure_iff, Real.dist_eq]
        intro ε hε; simp at hp; obtain ⟨hl, hr⟩ := hp
        set δ := min (ε / 2) (p/2)
        have : p + 1 > 0 := by linarith
        have hδpos : δ > 0 := by positivity
        have hδε : δ < ε := by grind
        have hδp1 : δ < (p + 1) := by grind
        use p - δ; constructor <;> grind
      . apply (hasDerivWithinAt_id _ _).sub_const
      . apply differentiableWithinAt_id.sub_const
    intro p hp
    rcases hp with hA | hB
    . have heventually : ((Set.Ioo (-1:ℝ) 0) ∪ (Set.Ioo (0:ℝ) 1) : Set ℝ) =ᶠ[nhds p] Set.Ioo (-1:ℝ) 0 := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [isOpen_Ioo.mem_nhds hA] with x hx
        simp; intro hx' hx''
        simp at hx; exact hx
      rw [derivWithin_congr_set heventually]
      suffices derivWithin (fun (x:ℝ) => if x ≤ 0 then x else x - 1) (Set.Ioo (-1) 0) p = 1 by linarith
      have heqon : Set.EqOn (fun (x:ℝ) => if x ≤ 0 then x else x - 1) (fun x => x) (Set.Ioo (-1) 0) := by
        intro x hx; simp at hx ⊢; linarith
      rw [derivWithin_congr heqon (by simp at hA ⊢; linarith)]
      exact hdA p hA
    . have heventually : ((Set.Ioo (-1:ℝ) 0 ∪ Set.Ioo 0 1):Set ℝ) =ᶠ[nhds p] Set.Ioo 0 1 := by
        rw [Filter.eventuallyEq_set]
        filter_upwards [isOpen_Ioo.mem_nhds hB] with x hx
        simp; intro hx' hx''
        simp at hx ⊢; exact hx
      rw [derivWithin_congr_set heventually]
      suffices derivWithin (fun (x:ℝ) ↦ if x ≤ 0 then x else x - 1) (Set.Ioo 0 1) p = 1 by linarith
      have heqon : Set.EqOn (fun (x:ℝ) ↦ if x ≤ 0 then x else x - 1) (fun x => x - 1) (Set.Ioo 0 1) := by
        intro x hx
        simp at hx ⊢; intro hx'
        exfalso; linarith
      rw [derivWithin_congr heqon (by simp at hB ⊢; intro hp'; exfalso; linarith)]
      exact hdB p hB
  . intro hmono
    have h1 : -0.1 ∈ (Set.Ioo (-1:ℝ) 0 ∪ Set.Ioo 0 1) := by
      left; constructor <;> norm_num
    have h2 : 0.5 ∈ (Set.Ioo (-1:ℝ) 0 ∪ Set.Ioo 0 1) := by
      right; constructor <;> norm_num
    specialize hmono h1 h2 (by norm_num)
    simp at hmono
    rw [if_pos (by norm_num), if_neg (by norm_num)] at hmono
    norm_num at hmono

end Chapter10
