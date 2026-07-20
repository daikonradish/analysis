import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic


/-!
# Analysis I, Section 10.1: Basic definitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`HasDerivWithinAt`, {name}`derivWithin`, and {name}`DifferentiableWithinAt`.

Note that the Mathlib conventions differ slightly from that in the text, in that
differentiability is defined even at points that are not limit points of the domain;
derivatives in such cases may not be unique, but {name}`derivWithin` still selects one such
derivative in such cases (or {lean}`0`, if no derivative exists).

-/

namespace Chapter10

variable (x₀ : ℝ)

/-- Definition 10.1.1 (Differentiability at a point).  For the Mathlib notion {name}`HasDerivWithinAt`, the
hypothesis that {name}`x₀` is a limit point is not needed. -/
theorem _root_.HasDerivWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ)
  (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔ (nhdsWithin x₀ (X \ {x₀})).Tendsto (fun x ↦ (f x - f x₀) / (x - x₀))
   (nhds L) :=  by
  rw [hasDerivWithinAt_iff_tendsto_slope, iff_iff_eq, slope_fun_def_field]

theorem _root_.DifferentiableWithinAt.iff (X: Set ℝ) (x₀ : ℝ) (f: ℝ → ℝ) :
  DifferentiableWithinAt ℝ f X x₀ ↔ ∃ L, HasDerivWithinAt f L X x₀ := by
  constructor
  . intro h; use derivWithin f X x₀; exact h.hasDerivWithinAt
  intro ⟨ L, h ⟩; exact h.differentiableWithinAt

theorem _root_.DifferentiableWithinAt.of_hasDeriv {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ} {L:ℝ}
  (hL: HasDerivWithinAt f L X x₀) : DifferentiableWithinAt ℝ f X x₀ := by
  rw [DifferentiableWithinAt.iff]; use L


theorem derivative_unique {X: Set ℝ} {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L L':ℝ}
  (hL: HasDerivWithinAt f L X x₀) (hL': HasDerivWithinAt f L' X x₀) :
  L = L' := by
    rw [_root_.HasDerivWithinAt.iff] at hL hL'
    rw [ClusterPt.eq_1] at hx₀
    solve_by_elim [tendsto_nhds_unique]

#check DifferentiableWithinAt.hasDerivWithinAt

theorem derivative_unique' (X: Set ℝ) {x₀ : ℝ}
  (hx₀: ClusterPt x₀ (.principal (X \ {x₀}))) {f: ℝ → ℝ} {L :ℝ}
  (hL: HasDerivWithinAt f L X x₀)
  (hdiff : DifferentiableWithinAt ℝ f X x₀):
  L = derivWithin f X x₀ := by
  solve_by_elim [derivative_unique, DifferentiableWithinAt.hasDerivWithinAt]

lemma square_has_deriv_within (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) .univ x₀ := by
  rw [_root_.HasDerivWithinAt.iff]
  have hden : Filter.Tendsto (fun x ↦  x + x₀) (nhdsWithin x₀ (Set.univ \ {x₀})) (nhds (2 * x₀)) := by
    rw [show 2 * x₀ = x₀ + x₀ by linarith]
    have hcont : Continuous (fun x => x + x₀) := by
      apply Continuous.add
      . exact continuous_id
      . exact continuous_const
    exact (hcont.tendsto x₀).mono_left nhdsWithin_le_nhds
  have heq : (fun x ↦ x + x₀) =ᶠ[nhdsWithin x₀ (Set.univ \ {x₀})] (fun x ↦ (x ^ 2 - x₀ ^ 2) / (x - x₀)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    simp at ha
    rw [sq_sub_sq]
    field_simp
    grind
  apply Filter.Tendsto.congr' heq
  exact hden

/-- Example 10.1.3 -/
example (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^2) (2 * x₀) .univ x₀ := by
  apply square_has_deriv_within

example (x₀:ℝ) : DifferentiableWithinAt ℝ (fun x ↦ x^2) .univ x₀ := by
  rw [_root_.DifferentiableWithinAt.iff]
  have := square_has_deriv_within x₀
  use 2 * x₀

example (x₀:ℝ) : derivWithin (fun x ↦ x^2) .univ x₀ = 2 * x₀ := by
  apply HasDerivWithinAt.derivWithin (square_has_deriv_within x₀)
  exact uniqueDiffWithinAt_univ

/-- Remark 10.1.4 -/
example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (hfg: f = g):
  DifferentiableWithinAt ℝ f X x₀ ↔ DifferentiableWithinAt ℝ g X x₀ := by rw [hfg]


example (X: Set ℝ) (x₀ : ℝ) {f g: ℝ → ℝ} (L:ℝ) (hfg: f = g):
  HasDerivWithinAt f L X x₀ ↔ HasDerivWithinAt g L X x₀ := by rw [hfg]

example : ∃ (X: Set ℝ) (x₀ :ℝ) (f g: ℝ → ℝ) (L:ℝ) (hfg: f x₀ = g x₀),
  HasDerivWithinAt f L X x₀ ∧ ¬ HasDerivWithinAt g L X x₀ := by
  use .univ
  use 0
  use fun _ => 0
  use fun x => if 0 ≤ x then x else 0
  use 0
  use (by simp)
  constructor
  . rw [HasDerivWithinAt.iff]
    simp
    have hcont : Continuous (fun (x:ℝ) => (0:ℝ)) := by exact continuous_const
    have htt := hcont.tendsto 0
    apply htt.mono_left
    exact nhdsWithin_le_nhds
  . intro hderiv
    rw [HasDerivWithinAt.iff] at hderiv
    simp at hderiv
    have hle : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) (Set.univ \ {0}) := by
      apply nhdsWithin_mono
      intro x hx
      simp at hx ⊢
      linarith
    have hnhdswithn := hderiv.mono_left hle
    have heq : (fun x ↦ (if 0 ≤ x then x else 0) / x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ ↦ (1:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp at hx
      rw [if_pos (by linarith)]
      simp; linarith
    have hweird := hnhdswithn.congr' heq
    have hsane : Filter.Tendsto (fun (x:ℝ) ↦ (1:ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have h1 : Continuous (fun (x:ℝ) ↦ (1:ℝ)) := by
        exact continuous_const
      exact (h1.tendsto 0).mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique hsane hweird
    linarith


/-- Example 10.1.6 -/

abbrev f_10_1_6 : ℝ → ℝ := abs

lemma abs_from_right : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
  unfold f_10_1_6
  simp
  have hcont : Continuous (fun (x:ℝ) => (1:ℝ)) := by exact continuous_const
  have hle : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhds 0 := by exact nhdsWithin_le_nhds
  have hnhdswth := (hcont.tendsto 0).mono_left hle
  apply hnhdswth.congr'
  filter_upwards [self_mem_nhdsWithin] with n hn
  simp at hn
  rw [abs_of_pos hn]
  field_simp

example : (nhdsWithin 0 (.Ioi 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds 1) := by
  exact abs_from_right

lemma abs_from_left : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
  unfold f_10_1_6
  simp
  have hcont : Continuous (fun (x:ℝ) => -(1:ℝ)) := by exact continuous_const
  have hle : nhdsWithin (0:ℝ) (Set.Iio (0:ℝ)) ≤ nhds 0 := by exact nhdsWithin_le_nhds
  have hnhdswithn := (hcont.tendsto 0).mono_left hle
  apply hnhdswithn.congr'
  filter_upwards [self_mem_nhdsWithin] with n hn
  simp at hn
  rw [abs_of_neg hn]
  grind

example : (nhdsWithin 0 (.Iio 0)).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0)) (nhds (-1)) := by
  exact abs_from_left

lemma abs_at_zero : ¬ ∃ L, (nhdsWithin 0 (.univ \ {0})).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
   (nhds L) := by
  push_neg
  intro L hL
  have hleft : nhdsWithin (0:ℝ) (Set.Iio (0:ℝ)) ≤ nhdsWithin (0:ℝ) (Set.univ \ {0}) := by
    apply nhdsWithin_mono 0
    intro x hx; simp at hx ⊢
    linarith
  have hright : nhdsWithin (0:ℝ) (Set.Ioi (0:ℝ)) ≤ nhdsWithin (0:ℝ) (Set.univ \ {0}) := by
    apply nhdsWithin_mono 0
    intro x hx; simp at hx ⊢
    linarith
  have hliml := hL.mono_left hleft
  have hlimr := hL.mono_left hright
  have hl := abs_from_left
  have hr := abs_from_right
  have hleftlim := tendsto_nhds_unique hl hliml
  have hrightlim := tendsto_nhds_unique hr hlimr
  linarith


example : ¬ ∃ L, (nhdsWithin 0 (.univ \ {0})).Tendsto (fun x ↦ (f_10_1_6 x - f_10_1_6 0) / (x - 0))
   (nhds L) := by
  exact abs_at_zero

example : ¬ DifferentiableWithinAt ℝ f_10_1_6 (.univ) 0 := by
  rw [DifferentiableWithinAt.iff]
  simp_rw [HasDerivWithinAt.iff]
  convert abs_at_zero

lemma abs_differentiablewithinat_from_right : DifferentiableWithinAt ℝ f_10_1_6 (.Ioi 0) 0 := by
  rw [DifferentiableWithinAt.iff]
  use 1
  rw [HasDerivWithinAt.iff]
  have : Set.Ioi (0:ℝ) \ {0} = Set.Ioi (0:ℝ) := by
    simp
  simp_rw [this]
  apply abs_from_right.congr'
  filter_upwards [self_mem_nhdsWithin] with n hn
  simp at ⊢

example : DifferentiableWithinAt ℝ f_10_1_6 (.Ioi 0) 0 := by
  exact abs_differentiablewithinat_from_right

example : derivWithin f_10_1_6 (.Ioi 0) 0 = 1 := by
  have hid : HasDerivWithinAt (fun (x:ℝ) ↦ (x:ℝ)) 1 (Set.Ioi 0) 0 := by
    apply hasDerivWithinAt_id
  have heq : f_10_1_6 =ᶠ[nhdsWithin 0 (Set.Ioi (0:ℝ))] (fun (x:ℝ) ↦ (x:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with n hn
    simp at hn
    unfold f_10_1_6
    rw [abs_of_pos hn]
  have hderiv : HasDerivWithinAt f_10_1_6 1 (Set.Ioi 0) 0 := by
    apply hid.congr_of_eventuallyEq heq
    simp
  apply hderiv.derivWithin
  exact uniqueDiffWithinAt_Ioi 0

example : DifferentiableWithinAt ℝ f_10_1_6 (.Iio 0) 0 := by
  have hid : HasDerivWithinAt (fun (x:ℝ) => (-x:ℝ)) (-1) (.Iio 0) 0 := by
    exact (hasDerivWithinAt_id 0 _).neg
  have heq : f_10_1_6 =ᶠ[nhdsWithin (0:ℝ) (.Iio 0)] (fun (x:ℝ) => (-x:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with n hn
    simp at hn; unfold f_10_1_6
    rw [abs_of_neg hn]
  have hderiv : HasDerivWithinAt f_10_1_6 (-1) (.Iio 0) 0 := by
    apply hid.congr_of_eventuallyEq heq
    simp
  exact DifferentiableWithinAt.of_hasDeriv hderiv


example : derivWithin f_10_1_6 (.Iio 0) 0 = -1 := by
  have hid : HasDerivWithinAt (fun (x:ℝ) => (-x:ℝ)) (-1) (.Iio 0) 0 := by
    exact (hasDerivWithinAt_id 0 _).neg
  have heq : f_10_1_6 =ᶠ[nhdsWithin (0:ℝ) (.Iio 0)] (fun (x:ℝ) => (-x:ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with n hn
    simp at hn; unfold f_10_1_6
    rw [abs_of_neg hn]
  have hderiv : HasDerivWithinAt f_10_1_6 (-1) (.Iio 0) 0 := by
    apply hid.congr_of_eventuallyEq heq
    simp
  apply hderiv.derivWithin
  exact uniqueDiffWithinAt_Iio 0

/-- Proposition 10.1.7 (Newton's approximation) / Exercise 10.1.2 -/
theorem _root_.HasDerivWithinAt.iff_approx_linear (X: Set ℝ) (x₀ :ℝ) (f: ℝ → ℝ) (L:ℝ) :
  HasDerivWithinAt f L X x₀ ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, |x - x₀| < δ → |f x - f x₀ - L * (x - x₀)| ≤ ε * |x - x₀| := by
  rw [HasDerivWithinAt.iff]
  simp_rw [Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]
  constructor
  . intro h ε hε
    choose δ hδpos hδ using h (ε/2) (by positivity)
    use δ; constructor
    . exact hδpos
    . intro x hx hxdist
      by_cases h₀ : x = x₀
      . subst h₀; simp
      . have h' : x ∈ X \ {x₀} := by tauto
        have :=  hδ h' hxdist
        rw [div_sub' (sub_ne_zero_of_ne h₀), mul_comm _ L, abs_div] at this
        rw [← div_le_iff₀ (abs_sub_pos.mpr h₀)]
        nlinarith
  . intro h ε hε
    choose δ hδpos hδ using h (ε/2) (by positivity)
    use δ; constructor
    . exact hδpos
    . intro x hx hdist
      specialize hδ x hx.1 hdist
      rw [div_sub' (sub_ne_zero_of_ne hx.2), mul_comm _ L, abs_div]
      rw [← div_le_iff₀ (abs_sub_pos.mpr hx.2)] at hδ
      nlinarith

/-- Proposition 10.1.10 / Exercise 10.1.3 -/
theorem _root_.ContinuousWithinAt.of_differentiableWithinAt {X: Set ℝ} {x₀ : ℝ} {f: ℝ → ℝ}
  (h: DifferentiableWithinAt ℝ f X x₀) :
  ContinuousWithinAt f X x₀ := by
  simp_rw [DifferentiableWithinAt.iff, HasDerivWithinAt.iff] at h
  choose L hL using h
  rw [Metric.tendsto_nhdsWithin_nhds] at hL
  rw [Metric.continuousWithinAt_iff]
  simp_rw [Real.dist_eq] at hL ⊢
  intro ε hε
  choose δ₁ hδpos₁ hδ₁ using hL 1 (by norm_num)
  set δ := min δ₁ (ε / (|L| + 1))
  have hδpos : δ > 0 := by
    unfold δ
    positivity
  use δ; constructor
  . exact hδpos
  . intro x hx hxdist
    by_cases h₀ : x = x₀
    . subst h₀; simp; exact hε
    . have h' : x ∈ X \ {x₀} := by tauto
      have hdistpos : 0 < |x - x₀| := by
        simp
        intro h
        have heq : x = x₀ := by linarith
        exact h₀ heq
      have hltδ₁ : |x - x₀| < δ₁ := by
        unfold δ at hxdist
        simp at hxdist
        tauto
      specialize hδ₁ h' hltδ₁
      set q := (f x - f x₀)/(x - x₀)
      have hq : |q| < 1 + |L| := by
        calc _ = |(q-L) + L| := by ring_nf
             _ ≤ |q-L| + |L| := by apply abs_add_le
             _ < 1 + |L|     := by linarith
      have hsplit : |f x - f x₀| = |q| * |x - x₀| := by
        unfold q
        rw [abs_div]
        rw [div_mul_cancel₀]
        linarith
      rw [hsplit]
      calc |q| * |x - x₀| < (1 + |L|) * |x - x₀|         := by gcongr
                        _ < (1 + |L|) * (ε / (|L| + 1))  := by
                                                            gcongr
                                                            unfold δ at hxdist
                                                            simp at hxdist
                                                            exact hxdist.2
                        _ = ε                            := by field_simp; linarith


/-Definition 10.1.11 (Differentiability on a domain). -/
#check DifferentiableOn.eq_1

/-- Corollary 10.1.12 -/
theorem _root_.ContinuousOn.of_differentiableOn {X: Set ℝ} {f: ℝ → ℝ}
  (h: DifferentiableOn ℝ f X) :
  ContinuousOn f X := by
  solve_by_elim [ContinuousWithinAt.of_differentiableWithinAt]

/-- Theorem 10.1.13 (a) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_const (X: Set ℝ) (x₀ : ℝ) (c:ℝ) :
  HasDerivWithinAt (fun x ↦ c) 0 X x₀ := by
    rw [HasDerivWithinAt.iff]
    simp
    have httnhds : Filter.Tendsto (fun (x:ℝ) ↦ (0:ℝ)) (nhdsWithin x₀ X) (nhds 0) := by
      exact tendsto_const_nhds
    refine httnhds.mono_left ?_
    refine nhdsWithin_mono x₀ ?_
    simp

/-- Theorem 10.1.13 (b) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_id (X: Set ℝ) (x₀ : ℝ) :
  HasDerivWithinAt (fun x ↦ x) 1 X x₀ := by
  rw [HasDerivWithinAt.iff]
  have htt : Filter.Tendsto (fun (x:ℝ) ↦ (1:ℝ)) (nhdsWithin x₀ X) (nhds 1) := by
    exact tendsto_const_nhds
  have htt : Filter.Tendsto (fun (x:ℝ) ↦ (1:ℝ)) (nhdsWithin x₀ (X \ {x₀})) (nhds 1) := by
    apply htt.mono_left
    apply nhdsWithin_mono x₀
    simp
  have heventually : (fun (x:ℝ) ↦ (1:ℝ)) =ᶠ[(nhdsWithin x₀ (X \ {x₀}))] (fun x ↦ (x - x₀) / (x - x₀)) := by
    filter_upwards [self_mem_nhdsWithin] with n hn; simp at hn
    rw [div_self (by grind)]
  exact htt.congr' heventually


/-- Theorem 10.1.13 (c) (Sum rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_add {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f + g) (f'x₀ + g'x₀) X x₀ := by
  rw [HasDerivWithinAt.iff] at hg hf ⊢
  convert hg.add hf using 1
  . simp;
    ext x
    ring_nf
  . simp; linarith


/-- Theorem 10.1.13 (d) (Product rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_mul {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f * g) (f'x₀ * (g x₀) + (f x₀) * g'x₀) X x₀ := by
  -- need continuity of f in order to establish that fx → fx₀ as x → x₀
  have hfcont : ContinuousWithinAt f X x₀ := by
    suffices DifferentiableWithinAt ℝ f X x₀ by
      exact ContinuousWithinAt.of_differentiableWithinAt this
    apply _root_.DifferentiableWithinAt.of_hasDeriv hf
  rw [HasDerivWithinAt.iff] at hg hf ⊢
  simp
  have hmiddle : (fun (x:ℝ) => f x * g x - f x₀ * g x₀) = fun (x:ℝ) => (f x - f x₀) * g x₀ + f x * (g x - g x₀) := by
    funext x
    calc _ = f x * g x - f x * g x₀ + (f x * g x₀ - f x₀ * g x₀) := by ring_nf
         _ = f x * (g x - g x₀) + (f x * g x₀ - f x₀ * g x₀)     := by congr; rw [← mul_sub]
         _ = f x * (g x - g x₀) + (f x - f x₀) * g x₀            := by congr; rw [← sub_mul]
         _ = (f x - f x₀) * g x₀ + f x * (g x - g x₀)            := by rw [add_comm]
  have hgtt₀ : Filter.Tendsto (fun x => g x₀) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)) := by
    exact tendsto_const_nhds
  have hftt₀ : Filter.Tendsto f (nhdsWithin x₀ (X \ {x₀})) (nhds (f x₀)) := by
    apply hfcont.tendsto.mono_left
    apply nhdsWithin_mono x₀
    simp
  have hfg₀ := hf.mul hgtt₀
  have hf₀g := hftt₀.mul hg
  have hproduct := hfg₀.add hf₀g
  apply hproduct.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp at hx
  have hneq : x ≠ x₀ := by tauto
  have hnonzero : x - x₀ ≠ 0 := by exact sub_ne_zero_of_ne hneq
  field_simp
  have hfun := congrFun hmiddle x; simp at hfun
  exact hfun.symm


/-- Theorem 10.1.13 (e) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_smul {X: Set ℝ} {x₀ f'x₀: ℝ} (c:ℝ)
  {f: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) :
  HasDerivWithinAt (c • f) (c * f'x₀) X x₀ := by
  rw [HasDerivWithinAt.iff] at hf ⊢
  convert hf.const_smul c using 1
  funext x
  simp
  rw [← mul_sub, mul_div_assoc]

/-- Theorem 10.1.13 (f) (Difference rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_sub {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f - g) (f'x₀ - g'x₀) X x₀ := by
  rw [HasDerivWithinAt.iff] at hf hg ⊢
  convert hf.sub hg using 1
  funext x
  simp
  rw [← sub_div]
  congr 1
  ring_nf

/-- Theorem 10.1.13 (g) (Differential calculus) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_inv {X: Set ℝ} {x₀ g'x₀: ℝ}
  {g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (1/g) (-g'x₀ / (g x₀)^2) X x₀ := by
  have hgcont : ContinuousWithinAt g X x₀ := by
    suffices DifferentiableWithinAt ℝ g X x₀ by
      exact ContinuousWithinAt.of_differentiableWithinAt this
    apply _root_.DifferentiableWithinAt.of_hasDeriv hg
  rw [HasDerivWithinAt.iff] at hg ⊢
  have heventuallynonzero : ∀ᶠ x in nhdsWithin x₀ (X \ {x₀}), g x ≠ 0 := by
    refine Filter.Tendsto.eventually_ne ?_ hgx₀
    apply hgcont.tendsto.mono_left
    refine nhdsWithin_mono x₀ ?_
    simp
  have hgtt₀' : Filter.Tendsto (fun x => (g x₀)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)⁻¹) := by
    exact tendsto_const_nhds
  have hgtt' : Filter.Tendsto (fun x ↦ (g x)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)⁻¹) := by
    apply (hgcont.tendsto.inv₀ hgx₀).mono_left
    apply nhdsWithin_mono x₀
    simp
  have hden : Filter.Tendsto (fun x ↦ (g x)⁻¹ * (g x₀)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (1 / (g x₀)^2)) := by
    convert hgtt'.mul hgtt₀' using 1
    field_simp
  have hexp := hg.neg.mul hden
  simp only [mul_one_div] at hexp
  apply hexp.congr'
  filter_upwards [heventuallynonzero, self_mem_nhdsWithin] with x hxnezero hmem
  have hnonzero : x - x₀ ≠ 0 := by exact sub_ne_zero_of_ne hmem.2
  simp
  field_simp
  linarith

/-- Theorem 10.1.13 (h) (Quotient rule) / Exercise 10.1.4 -/
theorem _root_.HasDerivWithinAt.of_div {X: Set ℝ} {x₀ f'x₀ g'x₀: ℝ}
  {f g: ℝ → ℝ} (hgx₀ : g x₀ ≠ 0) (hf: HasDerivWithinAt f f'x₀ X x₀)
  (hg: HasDerivWithinAt g g'x₀ X x₀) :
  HasDerivWithinAt (f / g) ((f'x₀ * (g x₀) - (f x₀) * g'x₀) / (g x₀)^2) X x₀ := by
  have hfcont : ContinuousWithinAt f X x₀ := by
    suffices DifferentiableWithinAt ℝ f X x₀ by
      exact ContinuousWithinAt.of_differentiableWithinAt this
    apply _root_.DifferentiableWithinAt.of_hasDeriv hf
  have hgcont : ContinuousWithinAt g X x₀ := by
    suffices DifferentiableWithinAt ℝ g X x₀ by
      exact ContinuousWithinAt.of_differentiableWithinAt this
    apply _root_.DifferentiableWithinAt.of_hasDeriv hg
  rw [HasDerivWithinAt.iff] at hf hg ⊢
  simp
  have hgevnonzero : ∀ᶠ (x:ℝ) in nhdsWithin x₀ (X \ {x₀}), g x ≠ 0 := by
    refine Filter.Tendsto.eventually_ne ?_ hgx₀
    apply hgcont.tendsto.mono_left
    apply nhdsWithin_mono x₀
    simp
  have hgttinv₀ : Filter.Tendsto (fun x => (g x₀)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)⁻¹) := by
    exact tendsto_const_nhds
  have hgttinv : Filter.Tendsto (fun x ↦ (g x)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)⁻¹) := by
    apply (hgcont.tendsto.inv₀ hgx₀).mono_left
    apply nhdsWithin_mono x₀
    simp
  have hden : Filter.Tendsto (fun x ↦ (g x)⁻¹ * (g x₀)⁻¹) (nhdsWithin x₀ (X \ {x₀})) (nhds (1 / (g x₀)^2)) := by
    convert hgttinv.mul hgttinv₀ using 1
    field_simp
  have hf₀ :  Filter.Tendsto (fun x ↦ f x₀) (nhdsWithin x₀ (X \ {x₀})) (nhds (f x₀)) := by
    exact tendsto_const_nhds
  have hg₀  : Filter.Tendsto (fun x ↦ g x₀) (nhdsWithin x₀ (X \ {x₀})) (nhds (g x₀)) := by
    exact tendsto_const_nhds
  have hnum := (hf.mul hg₀).sub (hf₀.mul hg)
  have hexp := hnum.mul hden
  simp only [mul_one_div] at hexp
  apply hexp.congr'
  filter_upwards [hgevnonzero, self_mem_nhdsWithin] with x hx hmem
  have hneq : x - x₀ ≠ 0 := by exact sub_ne_zero_of_ne hmem.2
  field_simp
  ring_nf

example (x₀:ℝ) (hx₀: x₀ ≠ 1): HasDerivWithinAt (fun x ↦ (x-2)/(x-1)) (1 /(x₀-1)^2) (.univ \ {1}) x₀ := by
  have hden : HasDerivWithinAt (fun (x:ℝ) => (x-1)) 1 (.univ \ {1}) x₀ := by
    have hid := hasDerivAt_id x₀
    have hminus1 := (hid.sub_const) 1
    exact hminus1.hasDerivWithinAt
  have hnum : HasDerivWithinAt (fun (x:ℝ) => (x-2)) 1 (.univ \ {1}) x₀ := by
    have hid := hasDerivAt_id x₀
    have hminus1 := (hid.sub_const) 2
    exact hminus1.hasDerivWithinAt
  have hgx₀ : (fun (x:ℝ) => (x - 1)) x₀ ≠ 0 := by
    simp
    intro hx
    contrapose! hx₀
    linarith
  have hquotient := _root_.HasDerivWithinAt.of_div (f := fun x => x - 2) (g := fun x => x - 1) hgx₀ hnum hden
  simp at hquotient
  convert hquotient using 1
  field_simp
  linarith

/-- Theorem 10.1.15 (Chain rule) / Exercise 10.1.7 -/
theorem _root_.HasDerivWithinAt.of_comp {X Y: Set ℝ} {x₀ y₀ f'x₀ g'y₀: ℝ}
  {f g: ℝ → ℝ} (hfx₀: f x₀ = y₀) (hfX : ∀ x ∈ X, f x ∈ Y)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  HasDerivWithinAt (g ∘ f) (g'y₀ * f'x₀) X x₀ := by
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hf hg ⊢
  intro ε hε
  choose δ₁ hδpos₁ hδ₁ using hg (ε / (2 * (|f'x₀| + 1))) (by positivity)
  choose δ₂ hδpos₂ hδ₂ using hf (min 1 (ε / (2 * (|g'y₀| + 1)))) (by positivity)
  use min δ₂  (δ₁ / (|f'x₀| + 1))
  constructor
  . positivity
  . intro x hx hxdist
    simp at hxdist; obtain ⟨hxdistl, hxdistr⟩ := hxdist
    specialize hδ₁ (f x) (hfX x hx) (by
      rw [← hfx₀]
      specialize hδ₂ x hx hxdistl
      calc _ = |f x - f x₀ - f'x₀ * (x - x₀) +  f'x₀ * (x - x₀)|  := by ring_nf
           _ ≤ |f x - f x₀ - f'x₀ * (x - x₀)| + |f'x₀ * (x - x₀)| := by apply abs_add_le
           _ ≤ min 1 (ε / (2 * (|g'y₀| + 1))) * |x - x₀| + |f'x₀ * (x - x₀)| := by gcongr
           _ ≤ 1 * |x - x₀| + |f'x₀ * (x - x₀)|                   := by gcongr; simp
           _ = 1 * |x - x₀| + (|f'x₀| * |(x - x₀)|)               := by congr 1; rw [abs_mul]
           _ = (1 + |f'x₀|) * |x - x₀|                            := by ring_nf
           _ < δ₁                                                 := by field_simp at hxdistr; linarith
    )
    subst hfx₀
    have hkey : (g ∘ f) x - (g ∘ f) x₀ - g'y₀ * f'x₀ * (x - x₀)
      = g'y₀ * (f x - f x₀ - f'x₀ * (x - x₀))
        + (g (f x) - g (f x₀) - g'y₀ * (f x - f x₀)) := by
      simp; ring_nf
    rw [hkey]
    have hfbound : |f x - f x₀| / (|f'x₀| + 1) ≤ |x - x₀| := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < |f'x₀| + 1)]
      calc |f x - f x₀|
                = |(f x - f x₀ - f'x₀ * (x - x₀)) + f'x₀ * (x - x₀)| := by rw [sub_add_cancel]
              _ ≤ |f x - f x₀ - f'x₀ * (x - x₀)| + |f'x₀ * (x - x₀)| := by apply abs_add_le
              _ ≤ 1 * |x - x₀| + |f'x₀| * |x - x₀| := by
                    gcongr
                    · exact le_trans (hδ₂ x hx hxdistl) (by gcongr; exact min_le_left _ _)
                    · rw [abs_mul]
              _ = |x - x₀| * (|f'x₀| + 1) := by ring
    calc _ ≤ |g'y₀ * (f x - f x₀ - f'x₀ * (x - x₀))| + |(g (f x) - g (f x₀) - g'y₀ * (f x - f x₀))| := by apply abs_add_le
         _ ≤ ε / 2 * |x - x₀| + (ε / 2 * |x - x₀|) := by
          gcongr
          . rw [abs_mul]
            specialize hδ₂ x hx (by linarith)
            calc _ ≤ |g'y₀| * (min 1 (ε / (2 * (|g'y₀| + 1))) * |x - x₀|)   := by gcongr
                 _ ≤ |g'y₀| * ((ε / (2 * (|g'y₀| + 1))) * |x - x₀|)         := by gcongr; simp
                 _ = (ε / 2 * |x - x₀|) * (|g'y₀| / (|g'y₀| + 1))           := by field_simp
                 _ ≤ (ε / 2 * |x - x₀|) * 1                                 := by gcongr; field_simp; linarith
                 _ = (ε / 2 * |x - x₀|)                                     := by simp
          . calc _ ≤ ε / (2 * (|f'x₀| + 1)) * |f x - f x₀|                  := by exact hδ₁
                 _ = ε / 2 * (|f x - f x₀| /  (|f'x₀| + 1))                 := by field_simp
                 _ ≤ ε / 2 * (|x - x₀|)                                     := by gcongr
         _ = ε * |x - x₀|                        := by ring_nf


/-- Exercise 10.1.5 -/
theorem _root_.HasDerivWithinAt.of_pow (n:ℕ) (x₀:ℝ) : HasDerivWithinAt (fun x ↦ x^n)
(n * x₀^((n:ℤ)-1)) .univ x₀ := by
induction' n with k ih
. simpa using hasDerivWithinAt_const x₀ .univ 1
. convert ih.mul (hasDerivWithinAt_id x₀ .univ) using 1
  simp
  cases k with
  | zero => simp
  | succ m =>
    simp
    grind

/-- Exercise 10.1.6 -/
theorem _root_.HasDerivWithinAt.of_zpow (n:ℤ) (x₀:ℝ) (hx₀: x₀ ≠ 0) :
  HasDerivWithinAt (fun x ↦ x^n) (n * x₀^(n-1)) (.univ \ {0}) x₀ := by
  induction n using Int.negInduction with
  | nat n =>
      have := _root_.HasDerivWithinAt.of_pow n x₀
      apply HasDerivWithinAt.mono this
      simp
  | neg ih n =>
      specialize ih n
      have := _root_.HasDerivWithinAt.of_inv (hgx₀:=?nonzero) ih
      convert this using 1
      . funext x
        simp
      . simp
        field_simp
        ring_nf
        conv_lhs =>
          rw [mul_assoc]
          rw [← zpow_natCast]
          arg 1
          arg 2
          rw [← zpow_add₀ hx₀]
        push_cast
        ring_nf
      . intro h
        have : x₀ = 0 := by exact eq_zero_of_pow_eq_zero h
        exact hx₀ this



end Chapter10
