import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.2: Local maxima, local minima, and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Relation between local extrema and derivatives.
- Rolle's theorem.
- mean value theorem.

-/

open Chapter9
namespace Chapter10

/-- Definition 10.2.1 (Local maxima and minima).  Here we use Mathlib's {name}`IsLocalMaxOn` type. -/
theorem IsLocalMaxOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMaxOn f X x₀ ↔
  ∃ δ > 0, IsMaxOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMaxOn_iff, IsLocalMaxOn, IsMaxFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

theorem IsLocalMinOn.iff (X:Set ℝ) (f:ℝ → ℝ) (x₀:ℝ) :
  IsLocalMinOn f X x₀ ↔
  ∃ δ > 0, IsMinOn f (X ∩ .Ioo (x₀ - δ) (x₀ + δ)) x₀ := by
  simp [isMinOn_iff, IsLocalMinOn, IsMinFilter, nhdsWithin.eq_1, Filter.eventually_inf_principal,
        Metric.eventually_nhds_iff, Real.dist_eq, abs_sub_lt_iff]
  peel 3; constructor <;> intro h _ _ _ <;> apply h <;> grind

/-- Example 10.2.3 -/
abbrev f_10_2_3 : ℝ → ℝ := fun x ↦ x^2 - x^4

example : ¬ IsMinOn f_10_2_3 .univ 0 := by
  intro hmin
  specialize hmin (show 100 ∈ Set.univ by tauto)
  unfold f_10_2_3 at hmin
  simp at hmin
  norm_num at hmin



example : IsMinOn f_10_2_3 (.Ioo (-1) 1) 0 := by
  intro x hx
  unfold f_10_2_3
  simp at hx ⊢
  rw [show 4 = 2 * 2 by linarith, pow_mul]
  suffices x ^ 2 < 1 by nlinarith
  nlinarith

example : IsLocalMinOn f_10_2_3 .univ 0 := by
  rw [IsLocalMinOn.iff]
  use 1; simp
  intro x hx
  unfold f_10_2_3
  simp at hx ⊢
  rw [show 4 = 2 * 2 by linarith, pow_mul]
  suffices x ^ 2 < 1 by nlinarith
  nlinarith


/-- Example 10.2.4 -/
example : ¬ ∃ x, IsMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  intro h
  choose x hx using h
  set y := ⌈x⌉ + 1
  have hy : (y:ℝ) ∈ ((↑· : ℤ → ℝ) '' Set.univ) := by
    use y; simp
  have ha:= hx hy
  simp at ha
  have hb : ⌈x⌉ < y := by unfold y; exact Int.lt_succ ⌈x⌉
  have hc : x ≤ ⌈x⌉ := by exact Int.le_ceil x
  rify at hb hc
  linarith


example : ¬ ∃ x, IsMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) x := by
  intro h
  choose x hx using h
  set y := ⌊x⌋ - 1
  have hy : (y:ℝ) ∈ ((↑· : ℤ → ℝ) '' Set.univ) := by
    use y; simp
  have ha:= hx hy
  simp at ha
  have hb : y < ⌊x⌋ := by unfold y; exact sub_one_lt ⌊x⌋
  have hc : ⌊x⌋ ≤ x := by exact Int.floor_le x
  rify at hb hc
  linarith

example (n:ℤ) : IsLocalMaxOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  rw [IsLocalMaxOn.iff]
  use 0.5; constructor
  . simp
    norm_num
  . intro x hx
    simp at hx ⊢
    obtain ⟨hex, hl, hr⟩ := hx
    choose y hy using hex
    subst hy
    by_contra! h'
    simp at h'
    have : (n+1) ≤ y := by omega
    rify at this
    linarith


example (n:ℤ) : IsLocalMinOn (· : ℝ → ℝ)  ((↑· : ℤ → ℝ) '' .univ) n := by
  rw [IsLocalMinOn.iff]
  use 0.5; constructor
  . simp
    norm_num
  . intro x hx
    simp at hx ⊢
    obtain ⟨hex, hl, hr⟩ := hx
    choose y hy using hex
    subst hy
    by_contra! h'
    simp at h'
    have : (n-1) ≥ y := by omega
    rify at this
    linarith

/-- Remark 10.2.5 -/
theorem IsLocalMaxOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMaxOn f X x₀) : IsLocalMaxOn f Y x₀ := by
  rw [IsLocalMaxOn.iff] at h ⊢
  choose δ hδpos hδ using h
  use δ; constructor
  . exact hδpos
  . intro x hx
    have hx' : x ∈ X ∩ Set.Ioo (x₀ - δ) (x₀ + δ) := by
      constructor
      . apply hXY; exact hx.1
      . exact hx.2
    exact hδ hx'

theorem IsLocalMinOn.of_restrict {X Y:Set ℝ} (hXY: Y ⊆ X) (f:ℝ → ℝ) (x₀:ℝ)
  (h: IsLocalMinOn f X x₀) : IsLocalMinOn f Y x₀ := by
  rw [IsLocalMinOn.iff] at h ⊢
  choose δ hδpos hδ using h
  use δ; constructor
  . exact hδpos
  . intro x hx
    have hx' : x ∈ X ∩ Set.Ioo (x₀ - δ) (x₀ + δ) := by
      constructor
      . apply hXY; exact hx.1
      . exact hx.2
    exact hδ hx'

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMaxOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMaxOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hderiv
  rw [IsLocalMaxOn.iff] at h
  choose δ₀ hδpos₀ hmax using h
  rw [isMaxOn_iff] at hmax
  obtain ⟨ha, hb⟩ := hx₀
  by_contra! h'
  rcases h'.lt_or_gt with hneg | hpos
  . choose δ₁ hδpos₁ hδ₁ using hderiv (-L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (x₀ - a))
    set x := x₀ - δ/2
    have hxab : x ∈ Set.Ioo a b := by unfold x; grind
    have hxδ₀ : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hxδ₁ : |x - x₀| < δ₁ := by rw [abs_lt]; grind
    have hxneg : x - x₀ < 0 := by simp; grind
    specialize hδ₁ x hxab hxδ₁
    specialize hmax x (by exact ⟨hxab, hxδ₀⟩)
    rw [abs_of_neg hxneg] at hδ₁
    rw [abs_le] at hδ₁
    simp at hδ₁
    obtain ⟨hl, hr⟩ := hδ₁
    replace hmax : f x - f x₀ ≤ 0 := by linarith
    have hr' : f x - f x₀ ≤ L / 2 * (x₀ - x) := by linarith
    have : 0 < L / 2 * (x₀ - x) := by nlinarith
    nlinarith
  . choose δ₁ hδpos₁ hδ₁ using hderiv (L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (b - x₀))
    set x := x₀ + δ/2
    have hxab : x ∈ Set.Ioo a b := by unfold x; grind
    have hxδ₀ : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hxδ₁ : |x - x₀| < δ₁ := by rw [abs_lt]; grind
    have hxpos : 0 < x - x₀ := by simp; grind
    specialize hδ₁ x hxab hxδ₁
    specialize hmax x (by exact ⟨hxab, hxδ₀⟩)
    rw [abs_of_pos hxpos] at hδ₁
    rw [abs_le] at hδ₁
    obtain ⟨hl, hr⟩ := hδ₁
    replace hmax : f x - f x₀ ≤ 0 := by linarith
    have hl' : L / 2 * (x₀ - x) ≤ f x - f x₀ := by linarith
    have : 0 < L / 2 * (x₀ - x) := by nlinarith
    nlinarith

/-- Proposition 10.2.6 (Local extrema are stationary) / Exercise 10.2.1 -/
theorem IsLocalMinOn.deriv_eq_zero {a b:ℝ} {f:ℝ → ℝ} {x₀:ℝ}
  (hx₀: x₀ ∈ Set.Ioo a b) (h: IsLocalMinOn f (.Ioo a b) x₀) {L:ℝ}
  (hderiv: HasDerivWithinAt f L (.Ioo a b) x₀) : L = 0 := by
  rw [_root_.HasDerivWithinAt.iff_approx_linear] at hderiv
  rw [IsLocalMinOn.iff] at h
  choose δ₀ hδpos₀ hmax using h
  rw [isMinOn_iff] at hmax
  obtain ⟨ha, hb⟩ := hx₀
  by_contra! h'
  rcases h'.lt_or_gt with hneg | hpos
  . choose δ₁ hδpos₁ hδ₁ using hderiv (-L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (b - x₀))
    set x := x₀ + δ/2
    have hxab : x ∈ Set.Ioo a b := by unfold x; grind
    have hxδ₀ : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hxδ₁ : |x - x₀| < δ₁ := by rw [abs_lt]; grind
    have hxpos : x - x₀ > 0 := by simp; grind
    specialize hδ₁ x hxab hxδ₁
    specialize hmax x (by exact ⟨hxab, hxδ₀⟩)
    rw [abs_of_pos hxpos] at hδ₁
    rw [abs_le] at hδ₁
    simp at hδ₁
    obtain ⟨hl, hr⟩ := hδ₁
    replace hmax : f x₀ - f x ≤ 0 := by linarith
    have hr' : f x₀ - f x ≤ L / 2 * (x₀ - x) := by linarith
    have : L / 2 * (x₀ - x) < 0 := by nlinarith
    nlinarith
  . choose δ₁ hδpos₁ hδ₁ using hderiv (L/2) (by linarith)
    set δ := min δ₀ (min δ₁ (x₀ - a))
    set x := x₀ - δ/2
    have hxab : x ∈ Set.Ioo a b := by unfold x; grind
    have hxδ₀ : x ∈ Set.Ioo (x₀ - δ₀) (x₀ + δ₀) := by grind
    have hxδ₁ : |x - x₀| < δ₁ := by rw [abs_lt]; grind
    have hxneg : x - x₀ < 0 := by simp; grind
    specialize hδ₁ x hxab hxδ₁
    specialize hmax x (by exact ⟨hxab, hxδ₀⟩)
    rw [abs_of_neg hxneg] at hδ₁
    rw [abs_le] at hδ₁
    simp at hδ₁
    obtain ⟨hl, hr⟩ := hδ₁
    replace hmax : f x₀ - f x ≤ 0 := by linarith
    have hr' : f x₀ - f x ≤ L / 2 * (x₀ - x) := by linarith
    have : L / 2 * (x₀ - x) < 0 := by nlinarith
    nlinarith

theorem IsMaxOn.deriv_eq_zero_counter : ∃ (a b:ℝ) (f:ℝ → ℝ)
  (x₀:ℝ) (hx₀: x₀ ∈ Set.Icc a b) (h: IsMaxOn f (.Icc a b) x₀) (L:ℝ)
  (hderiv: HasDerivWithinAt f L (.Icc a b) x₀), L ≠ 0 := by
  use -1, 1, fun x => x ^ 3, 1, by simp
  use (
    by
      intro x hx
      simp at hx ⊢
      have : x ^ 2 ≤ 1 := by nlinarith
      nlinarith
  )
  use 3; simp
  simpa using (hasDerivAt_pow 3 (1 : ℝ)).hasDerivWithinAt (s := Set.Icc (-1) 1)


/-- Theorem 10.2.7 (Rolle's theorem) / Exercise 10.2.4 -/
theorem _root_.HasDerivWithinAt.exist_zero {a b:ℝ} (hab: a < b) {g:ℝ → ℝ}
  (hcont: ContinuousOn g (.Icc a b)) (hderiv: DifferentiableOn ℝ g (.Ioo a b))
  (hgab: g a = g b) : ∃ x ∈ Set.Ioo a b, HasDerivWithinAt g 0 (.Ioo a b) x := by
  choose m hm hmin using IsMinOn.of_continuous_on_compact hab hcont
  choose M hM hmax using IsMaxOn.of_continuous_on_compact hab hcont
  have hminmax : g m ≤ g M := by
    specialize hmin hM
    simpa using hmin
  rcases hminmax.eq_or_lt with heq | hlt
  . -- constant
    have hconst : ∀ p ∈ Set.Icc a b, g p = g M := by
      intro p hp
      by_contra! hp'
      rcases hp'.lt_or_gt with hlt | hgt
      . specialize hmin hp; simp at hmin
        linarith
      . specialize hmax hp; simp at hmax
        linarith
    use (a + b) / 2; constructor
    . grind
    . have hderivwithin : HasDerivWithinAt (fun _ => g M) 0 (Set.Ioo a b) ((a + b) / 2) := by
        exact HasDerivWithinAt.of_const (Set.Ioo a b) ((a + b) / 2) (g M)
      apply hderivwithin.congr
      . intro x₀ hx₀
        exact hconst x₀ (by grind)
      . apply hconst; grind
  . have h : ¬ ((g a = g m) ∧ (g a = g M)) := by
      intro h
      have : g m = g M := by linarith
      linarith
    rw [not_and_or] at h
    rcases h with hgm | hgM
    . have hma : m ≠ a := by
        intro h
        apply hgm
        rw [h]
      have hmb : m ≠ b := by
        intro h
        apply hgm
        rw [h, hgab]
      have hmab : m ∈ Set.Ioo a b := by grind
      use m
      constructor
      . exact hmab
      . have hlocalmin : IsLocalMinOn g (.Ioo a b) m := by
          rw [IsLocalMinOn.iff]
          set δ := min (m - a) (b - m)
          use δ / 2
          constructor
          . simp; grind
          . intro x₀ hx₀
            apply hmin
            grind
        have hderiv' : DifferentiableWithinAt ℝ g (Set.Ioo a b) m := by
          apply DifferentiableWithinAt.mono (hderiv _ hmab)
          simp
        rw [_root_.DifferentiableWithinAt.iff] at hderiv'
        choose L hL using hderiv'
        have := IsLocalMinOn.deriv_eq_zero (hx₀ := hmab) hlocalmin hL
        subst this; exact hL
    . have hMa : M ≠ a := by
        intro h
        apply hgM
        rw [h]
      have hMb : M ≠ b := by
        intro h
        apply hgM
        rw [h, hgab]
      have hMab : M ∈ Set.Ioo a b := by grind
      use M
      constructor
      . exact hMab
      . have hlocalmax : IsLocalMaxOn g (.Ioo a b) M := by
            rw [IsLocalMaxOn.iff]
            set δ := min (M - a) (b - M)
            use δ / 2
            constructor
            . simp; grind
            . intro x₀ hx₀
              apply hmax
              grind
        have hderiv' : DifferentiableWithinAt ℝ g (Set.Ioo a b) M := by
          apply DifferentiableWithinAt.mono (hderiv _ hMab)
          simp
        rw [_root_.DifferentiableWithinAt.iff] at hderiv'
        choose L hL using hderiv'
        have := IsLocalMaxOn.deriv_eq_zero (hx₀ := hMab) hlocalmax hL
        subst this; exact hL



/-- Corollary 10.2.9 (Mean value theorem ) / Exercise 10.2.5 -/
theorem _root_.HasDerivWithinAt.mean_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) (hderiv: DifferentiableOn ℝ f (.Ioo a b)) :
  ∃ x ∈ Set.Ioo a b, HasDerivWithinAt f ((f b - f a) / (b - a)) (.Ioo a b) x := by
  set C := (f b - f a) / (b - a)
  set g := fun x => f x - (C * x)
  have hgab : g a = g b := by
    unfold g C
    have hba : b - a > 0 := by linarith
    field_simp
    ring_nf
  have hgcont : ContinuousOn g (.Icc a b) := by
    have hCcont : ContinuousOn (fun x => C * x) (.Icc a b) := by
      exact continuousOn_id.const_mul C
    exact hcont.sub hCcont
  have hgderiv : DifferentiableOn ℝ g (.Ioo a b) := by
    have hCdiffable : DifferentiableOn ℝ (fun x => C * x) (.Ioo a b) := by
      exact differentiableOn_id.const_mul C
    exact hderiv.sub hCdiffable
  have hrolle := _root_.HasDerivWithinAt.exist_zero hab hgcont hgderiv hgab
  choose x hxab hx using hrolle
  use x; constructor
  . exact hxab
  . unfold g at hx
    have hC : HasDerivWithinAt (fun x ↦ C * x) C (Set.Ioo a b) x := by
      simpa using (hasDerivWithinAt_id x _).const_mul C
    convert hx.add hC using 1
    . funext x; simp
    . simp

/-- Exercise 10.2.2 -/
example : ∃ f:ℝ → ℝ, ContinuousOn f (.Icc (-1) 1) ∧
  IsMaxOn f (.Icc (-1) 1) 0 ∧ ¬ DifferentiableWithinAt ℝ f (.Icc (-1) 1) 0 := by
  use -abs; refine ⟨?_, ?_, ?_⟩
  . exact continuousOn_id.abs.neg
  . intro x hx
    simp at hx ⊢
  . intro hdiff
    have hL := hdiff.hasDerivWithinAt
    set L := derivWithin (-abs:ℝ → ℝ) (Set.Icc (-1) 1) 0 with hLdef
    have hleft : L = 1 := by
      have hl : HasDerivWithinAt (-abs:ℝ → ℝ) L (Set.Icc (-1) 0) 0 := by
        apply hL.mono
        grind
      have h1 : HasDerivWithinAt (-abs:ℝ → ℝ) 1 (Set.Icc (-1) 0) 0 := by
        apply (hasDerivWithinAt_id 0 _).congr
        . intro x hx; simp at hx ⊢
          rw [abs_of_nonpos hx.2]; simp
        . simp
      have hu : UniqueDiffWithinAt ℝ (Set.Icc (-1:ℝ) 0) 0 := by
        apply uniqueDiffOn_Icc
        . linarith
        . simp
      exact hu.eq_deriv _ hl h1
    have hright : L = -1 := by
      have hl : HasDerivWithinAt (-abs:ℝ → ℝ) L (Set.Icc 0 1) 0 := by
        apply hL.mono
        grind
      have h1 : HasDerivWithinAt (-abs:ℝ → ℝ) (-1) (Set.Icc 0 1) 0 := by
        apply (hasDerivWithinAt_id 0 _).neg.congr
        . intro x hx; simp at hx ⊢
          exact hx.1
        . simp
      have hu : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) 0 := by
        apply uniqueDiffOn_Icc
        . linarith
        . simp
      exact hu.eq_deriv _ hl h1
    linarith

/-- Exercise 10.2.3 -/
example : ∃ f:ℝ → ℝ, DifferentiableOn ℝ f (.Icc (-1) 1) ∧
  HasDerivWithinAt f 0 (.Ioo (-1) 1) 0 ∧
  ¬ IsLocalMaxOn f (.Icc (-1) 1) 0 ∧ ¬ IsLocalMinOn f (.Icc (-1) 1) 0 := by
  use fun x => x ^ 3; refine ⟨?_, ?_, ?_, ?_⟩
  . simpa using differentiableOn_id.pow 3
  . have h := (hasDerivWithinAt_id (0 : ℝ) (Set.Ioo (-1) 1)).pow 3
    convert h using 1
    simp
  . intro hmax
    rw [IsLocalMaxOn.iff] at hmax
    choose δ hδpos hδ using hmax
    set δ' := min δ 1 with hδdef'
    simp at hδdef'
    have hδpos' : δ' > 0 := by positivity
    have hpos : (δ' / 2) ^ 3 > 0 := by positivity
    have : δ'/2 ∈ (Set.Icc (-1) 1 ∩ Set.Ioo (0 - δ) (0 + δ)) := by
      grind
    specialize hδ this
    simp at hδ
    linarith
  . intro hmin
    rw [IsLocalMinOn.iff] at hmin
    choose δ hδpos hδ using hmin
    set δ' := min δ 1 with hδdef'
    simp at hδdef'
    have hδpos' : δ' > 0 := by positivity
    have hpos : (δ' / 2) ^ 3 > 0 := by positivity
    have : -δ'/2 ∈ (Set.Icc (-1) 1 ∩ Set.Ioo (0 - δ) (0 + δ)) := by
      grind
    specialize hδ this
    simp at hδ
    linarith

/-- Exercise 10.2.6 -/
theorem lipschitz_bound {M a b:ℝ} (hM: M > 0) (hab: a < b) {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b))
  (hderiv: DifferentiableOn ℝ f (.Ioo a b))
  (hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M)
  {x y:ℝ} (hx: x ∈ Set.Ioo a b) (hy: y ∈ Set.Ioo a b) :
  |f x - f y| ≤ M * |x - y| := by
  wlog hxy : x < y with hlog
  . push_neg at hxy
    rcases hxy.eq_or_lt with heq | hlt
    . subst heq; simp
    . -- swapping the x and ys doesn't matter due to absolute sign
      specialize hlog hM hab hcont hderiv hlip hy hx hlt
      conv_lhs at hlog  => rw [abs_sub_comm]
      conv_rhs at hlog  => rw [abs_sub_comm]
      exact hlog
  have hxyIcc : Set.Icc x y ⊆ Set.Ioo a b := by
    intro p hp
    simp at hp hx hy ⊢
    constructor <;> linarith
  have hxyIoo : Set.Ioo x y ⊆ Set.Ioo a b := by
    have : Set.Ioo x y ⊆ Set.Icc x y := by exact Set.Ioo_subset_Icc_self
    exact this.trans hxyIcc
  have hxycont : ContinuousOn f (Set.Icc x y) := by
    apply hcont.mono
    apply hxyIcc.trans
    exact Set.Ioo_subset_Icc_self
  have hxyderiv : DifferentiableOn ℝ f (.Ioo x y) := by
    apply hderiv.mono
    apply hxyIoo.trans
    rfl
  choose p hpxy hdwithinxyatp using _root_.HasDerivWithinAt.mean_value hxy hxycont hxyderiv
  have hderivatp := hdwithinxyatp.hasDerivAt (by exact Ioo_mem_nhds hpxy.1 hpxy.2)
  have hpab : p ∈ Set.Ioo a b := by
    simp at hpxy hx hy ⊢
    constructor <;> linarith
  have hderivatp' : HasDerivAt f (derivWithin f (Set.Ioo a b) p) p:= by
    have hdwithinabatp := (hderiv p hpab).hasDerivWithinAt
    exact hdwithinabatp.hasDerivAt (by exact Ioo_mem_nhds hpab.1 hpab.2)
  have hΔ : (f y - f x) / (y - x) = derivWithin f (Set.Ioo a b) p := by
    exact hderivatp.unique hderivatp'
  specialize hlip p hpab
  rw [← hΔ] at hlip
  rw [abs_div] at hlip; field_simp at hlip
  have : |y - x| > 0 := by simp; linarith
  observe : |y - x| ≠ 0
  field_simp at hlip
  conv_lhs at hlip => rw [abs_sub_comm]
  conv_rhs at hlip => rw [abs_sub_comm, mul_comm]
  exact hlip

/-- Exercise 10.2.7 -/
theorem _root_.UniformContinuousOn.of_lipschitz {f:ℝ → ℝ}
  (hcont: ContinuousOn f .univ)
  (hderiv: DifferentiableOn ℝ f .univ)
  (hlip: BddOn (deriv f) .univ) :
  UniformContinuousOn f (.univ) := by
  choose M hM using hlip
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.dist_eq]
  intro ε hε
  have hMnonneg : 0 ≤ M := by
    by_contra! h'
    specialize hM 0 (by tauto)
    have : |deriv f 0| ≥ 0 := by apply abs_nonneg
    linarith
  rcases hMnonneg.eq_or_lt with heq | hlt
  . use 10000000000000000000000000; constructor
    . simp
    . intro x hx y hy hxy
      suffices f x = f y by
        rw [this]
        simp; linarith
      apply is_const_of_deriv_eq_zero
      . exact differentiableOn_univ.mp hderiv
      . intro p
        specialize hM p (by tauto)
        rwa [← heq, abs_nonpos_iff] at hM
  . use ε / M; constructor
    . positivity
    . intro x hx y hy hxy
      wlog hxlty : x < y with hlog
      . push_neg at hxlty
        rcases hxlty.eq_or_lt with hxyeq | hxylt
        . subst hxyeq; simp; linarith
        . specialize hlog hcont hderiv M hM ε hε hMnonneg hlt y hy x hx (by rwa [abs_sub_comm]) hxylt
          rwa [abs_sub_comm]
      have hεM : (ε/M) > 0 := by positivity
      set a := x - (ε/M)
      set b := y + (ε/M)
      have hab : a < b := by linarith
      have hlip: ∀ x ∈ Set.Ioo a b, |derivWithin f (.Ioo a b) x| ≤ M := by
        intro p hp
        have hdiffuniv := differentiableOn_univ.mp hderiv
        have hdiffwithinat : DifferentiableWithinAt ℝ f (Set.Ioo a b) p := by
          apply (hdiffuniv p).differentiableWithinAt
        have hdiffatp := hdiffuniv p
        have hunique := uniqueDiffOn_Ioo a b p hp
        have heq := hdiffatp.derivWithin hunique
        specialize hM p (by tauto)
        rwa [heq]
      have hxab : x ∈ Set.Ioo a b := by
        unfold a b; simp; constructor <;> linarith
      have hyab : y ∈ Set.Ioo a b := by
        unfold a b; simp; constructor <;> linarith
      have hdist : |x - y| ≤ ε / M := by
        unfold a b at hxab hyab
        simp at hxab hyab
        rw [abs_le]; constructor <;> grind
      have hlipbound := lipschitz_bound (f:=f) (M:=M) (a:=a) (b:=b) hlt hab
        (by apply hcont.mono; tauto)  -- it's continuous everywhere, so it's continuous here
        (by apply hderiv.mono; tauto)  -- it's differentiable everywhere, so it's differentiable here
        (by exact hlip)
        (x:=x) (y:=y) hxab hyab
      calc _ ≤ M * |x - y| := by exact hlipbound
           _ ≤ M * (ε / M) := by gcongr
           _ = ε           := by field_simp


end Chapter10
