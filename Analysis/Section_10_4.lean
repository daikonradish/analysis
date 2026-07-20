import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_10_1

/-!
# Analysis I, Section 10.4: Inverse functions and derivatives

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The inverse function theorem.

-/

open Chapter9
namespace Chapter10

/-- Lemma 10.4.1 -/
theorem _root_.HasDerivWithinAt.of_inverse {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ * f'x₀ = 1 := by
  -- This proof is written to follow the structure of the original text.
  have h1 : HasDerivWithinAt id (g'y₀ * f'x₀) X x₀ := by
    apply (hf.of_comp hfx₀ hfXY _).congr _ (hgf _ hx₀).symm <;> grind
  observe h2 : HasDerivWithinAt id 1 X x₀
  solve_by_elim [derivative_unique]

theorem _root_.HasDerivWithinAt.of_inverse' {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀ f'x₀ g'y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: HasDerivWithinAt g g'y₀ Y y₀) :
  g'y₀ = 1/f'x₀ :=
    eq_one_div_of_mul_eq_one_left (hf.of_inverse hfXY hgf hx₀ hfx₀ hcluster hg)

theorem _root_.HasDerivWithinAt.of_inverse_of_zero_deriv {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgf: ∀ x ∈ X, g (f x) = x)
  {x₀ y₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀)
  (hcluster: ClusterPt x₀ (.principal (X \ {x₀})))
  (hf: HasDerivWithinAt f 0 X x₀) :
  ¬ DifferentiableWithinAt ℝ g Y y₀ := by
  by_contra this; rw [DifferentiableWithinAt.iff] at this; choose _ hg using this
  apply hf.of_inverse at hg <;> grind

example : ¬ DifferentiableWithinAt ℝ (fun x:ℝ ↦ x^(1/3:ℝ)) (.Ici 0) 0 := by
  apply _root_.HasDerivWithinAt.of_inverse_of_zero_deriv (x₀:=0) (X:=(.Ici 0)) (f:=fun x:ℝ => x^3) (g:=fun x:ℝ ↦ x^(1/3:ℝ))
  . simp
  . simp
  . simp_rw [← mem_closure_iff_clusterPt, Metric.mem_closure_iff, Real.dist_eq]
    intro x hx
    have : Set.Ici (0:ℝ) \ {0} = Set.Iio 0 := by sorry
    rw [this]
    simp
    use -x / 2; constructor
    . linarith
    . rw [neg_div, abs_neg, abs_div, abs_of_pos hx]
      norm_num; exact hx
  . simpa using (hasDerivAt_pow 3 (0 : ℝ)).hasDerivWithinAt
  . intro x hx
    simp at hx ⊢
    rw [show 3 = 2 + 1 by linarith]
    rw [pow_add]; simp
    observe : x ^ 2 ≥ 0
    nlinarith
  . intro x hx
    simp
    rw [← Real.rpow_natCast x 3]
    rw [← Real.rpow_mul (by exact hx)]
    simp


/-- Theorem 10.4.2 (Inverse function theorem) -/
theorem inverse_function_theorem {X Y: Set ℝ} {f: ℝ → ℝ} {g:ℝ → ℝ}
  (hfXY: ∀ x ∈ X, f x ∈ Y) (hgYX: ∀ y ∈ Y, g y ∈ X)
  (hgf: ∀ x ∈ X, g (f x) = x) (hfg: ∀ y ∈ Y, f (g y) = y)
  {x₀ y₀ f'x₀: ℝ} (hx₀: x₀ ∈ X) (hfx₀: f x₀ = y₀) (hne : f'x₀ ≠ 0)
  (hf: HasDerivWithinAt f f'x₀ X x₀) (hg: ContinuousWithinAt g Y y₀) :
    HasDerivWithinAt g (1/f'x₀) Y y₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _]
    intro y hy hconv
    set x : ℕ → ℝ := fun n ↦ g (y n)
    have hy' : ∀ n, y n ∈ Y := by aesop
    have hy₀: y₀ ∈ Y := by aesop
    have hx : ∀ n, x n ∈ X \ {x₀}:= by
      intro n
      unfold x
      by_contra! h'; simp at h'
      have hyn : y n ∈ Y := by exact hy' n
      specialize h' (by exact hgYX _ hyn)
      have hg' := congrArg f h'
      have := hfg (y n) (by exact (hy n).1)
      rw [this, hfx₀] at hg'
      specialize hy n
      exact hy.2 hg'
    replace hconv := hconv.comp_of_continuous hg hy'
    have hgy₀ : g y₀ = x₀ := by aesop
    rw [HasDerivWithinAt.iff, ←Convergesto.iff, Convergesto.iff_conv _ _] at hf
    convert (hf _ hx _).inv₀ _ using 2 with n <;> grind

/-- Exercise 10.4.1(a) -/
example {n:ℕ} : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (.Ioi 0) := by
  exact Continuous.exp' _

theorem hasDerivWithinAt_of_rpow_one_div_natCast {n:ℕ} {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (.Ioi 0) x := by
  by_cases! hn : n = 0
  . subst hn
    simp
    apply hasDerivWithinAt_const
  replace hn : n > 0 := by omega
  have hxge0 : x ≥ 0 := by simp at hx; linarith
  set x₀ := x^(1/n:ℝ)
  convert inverse_function_theorem
    (X:=(.Ioi 0)) (Y:=(.Ioi 0))
    (f:=fun x:ℝ => Real.rpow x (n:ℝ)) (g:=fun x:ℝ ↦ x^(1/n:ℝ))
    (x₀:=x₀) (y₀:=x)
    (f'x₀:=(n:ℝ)*x₀^((n-1):ℝ))
    (hfXY:=?rangeDomain)
    (hgYX:=?domainRange)
    (hgf:=?inverseAgree)
    (hfg:=?agreeInverse)
    (hx₀:=?inRange)
    (hfx₀:=?inDomain)
    (hne:=?nonZero)
    (hf:=?diff)
    (hg:=?cont) using 1
  · unfold x₀
    field_simp
    rw [← Real.rpow_mul hxge0, one_div, ← Real.rpow_neg hxge0]
    congr; ring_nf
  . intro p hp; simp at hp ⊢
    exact pow_pos hp n
  . intro p hp; simp at hp ⊢
    exact Real.rpow_pos_of_pos hp _
  . intro p hp; simp at hp ⊢
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    conv_rhs => rw [show p = p ^ (1:ℝ) by simp]
    congr; field_simp
  . intro p hp; simp at hp ⊢
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    conv_rhs => rw [show p = p ^ (1:ℝ) by simp]
    congr; field_simp
  . simp; unfold x₀
    exact Real.rpow_pos_of_pos hx _
  . unfold x₀; simp
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    conv_rhs => rw [show x = x ^ (1:ℝ) by simp]
    congr; field_simp
  . suffices x₀ ^ (n - 1:ℝ) > 0 by
      by_contra! h'
      rify at hn
      nlinarith
    unfold x₀
    rw [← Real.rpow_mul (by linarith)]
    exact Real.rpow_pos_of_pos hx _
  . convert  (hasDerivAt_pow n x₀).hasDerivWithinAt using 1
    . simp
    . simp; left
      conv_rhs => rw [← Real.rpow_natCast]
      congr
      exact (Nat.cast_pred hn).symm
  . have hcont : ContinuousOn (fun x:ℝ ↦ x^(1/n:ℝ)) (.Ioi 0) := by
      exact Continuous.exp' _
    exact hcont x hx

/-- Exercise 10.4.1(b) -/
example {n:ℕ} {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^(1/n:ℝ))
  ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) (.Ioi 0) x := by
  exact hasDerivWithinAt_of_rpow_one_div_natCast hx

theorem hasDerivWithinAt_of_rpow_ratCast (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ioi 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (.Ioi 0) x := by
  have hx0 : x > 0 := by simp at hx; linarith
  set m := q.num
  set n := q.den
  have hn0 : n ≠ 0 := by exact q.den_nz
  have hn0' : n > 0 := by omega
  have hmnq :  (m:ℝ) * (n:ℝ)⁻¹ = q := by
    conv_rhs => rw [← Rat.num_div_den q]
    unfold m n
    push_cast
    field_simp
  set y₀ := x^ (1/n:ℝ)
  have hy₀pos : y₀ > 0 := by
    unfold y₀
    exact Real.rpow_pos_of_pos hx _
  have hchainrule := _root_.HasDerivWithinAt.of_comp
    (X:=Set.Ioi 0) (Y:=Set.Ioi 0)
    (f:=fun x=>x^ (1/n:ℝ)) (g:=fun x => x ^ m)
    (x₀:=x) (y₀:=y₀)
    (f'x₀:=((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1))) (g'y₀:= m * y₀ ^ (m-1))
    (hfx₀:=?pointwise) (hfX:=?rangeDomain)
    (hf:=?fDeriv) (hg:=?gDeriv)
  have hidentity : (q:ℝ) * x ^ ((q:ℝ)-1) = (m:ℝ) * y₀ ^ (m - 1) * ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) := by
    conv_rhs =>
      rw [show (m:ℝ) * y₀ ^ (m - 1) * ((n:ℝ)⁻¹ * x^((n:ℝ)⁻¹-1)) = (m:ℝ) * (n:ℝ)⁻¹ * y₀ ^ (m - 1) * x^((n:ℝ)⁻¹-1) by ring_nf]
      rw [show (m:ℝ) * (n:ℝ)⁻¹ = q by exact hmnq]
      unfold y₀
      rw [mul_assoc]
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    congr
    conv_rhs =>
      rw [show (((m-1):ℤ):ℝ) = (m:ℝ) - (1:ℝ) by simp]
      rw [mul_sub]
      simp
      rw [mul_comm, hmnq]
  rw [← hidentity] at hchainrule
  refine hchainrule.congr ?_ ?_
  . intro p hp; simp at hp ⊢
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by linarith)]
    conv_rhs => rw [mul_comm, hmnq]
  . simp
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by linarith)]
    conv_rhs => rw [mul_comm, hmnq]
  . unfold y₀; simp
  . intro p hp; simp
    exact Real.rpow_pos_of_pos hp _
  . apply hasDerivWithinAt_of_rpow_one_div_natCast hx
  . exact (hasDerivAt_zpow m y₀ (by left; linarith)).hasDerivWithinAt

/-- Exercise 10.4.2(a) -/
example (q:ℚ) {x:ℝ} (hx: x ∈ Set.Ioi 0) :
  HasDerivWithinAt (fun x:ℝ ↦ x^(q:ℝ)) (q * x^(q-1:ℝ)) (.Ioi 0) x := by
  exact hasDerivWithinAt_of_rpow_ratCast q hx

lemma tendsto_nhdsWithin_nhds_of_rpow_ratCast (q:ℚ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1)) (nhds q) := by
  have := hasDerivWithinAt_of_rpow_ratCast (q:=q) (x:=1) (hx:=by norm_num)
  rw [HasDerivWithinAt.iff] at this
  simpa using this

/-- Exercise 10.4.2(b) -/
example (q:ℚ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^(q:ℝ)-1)/(x-1)) (nhds q) := by
  exact tendsto_nhdsWithin_nhds_of_rpow_ratCast q


lemma tendsto_nhdsWithin_nhds_of_rpow (α:ℝ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1)) (nhds α) := by
  rw [Real.one_rpow]
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  intro ε hε
  choose a ha hpa using exists_rat_btwn (x:=α-(ε/2)) (y:=α) (by linarith)
  choose b hb hpb using exists_rat_btwn (x:=α) (y:=α+(ε/2)) (by linarith)
  have hqa := tendsto_nhdsWithin_nhds_of_rpow_ratCast a
  have hqb := tendsto_nhdsWithin_nhds_of_rpow_ratCast b
  simp_rw [Metric.tendsto_nhds, Real.dist_eq] at hqa hqb
  specialize hqa (ε/2) (by positivity)
  specialize hqb (ε/2) (by positivity)
  filter_upwards [hqa, hqb, self_mem_nhdsWithin] with p hneara hnearb hmem
  simp at hmem; obtain ⟨hppos, hpnonzero⟩ := hmem; push_neg at hpnonzero
  rw [abs_lt] at hneara hnearb ⊢
  rcases hpnonzero.lt_or_gt with hplt1 | hgt1
  . have hpsub1 : p - 1 < 0 := by linarith
    constructor
    . have hpow : p ^ α < p ^ (a:ℝ) := by exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one hppos hplt1).mpr hpa
      have hpowsub1 : p ^ α - 1 < p ^ (a:ℝ) - 1 := by linarith
      have hover := (div_lt_div_right_of_neg (c:=(p-1)) hpsub1).mpr hpowsub1
      linarith
    · have hpow : p ^ (b:ℝ) <  p ^ α := by exact (Real.rpow_lt_rpow_left_iff_of_base_lt_one hppos hplt1).mpr hb
      have hpowsub1 : p ^ (b:ℝ) - 1 <  p ^ α - 1 := by linarith
      have hover := (div_lt_div_right_of_neg (c:=(p-1)) hpsub1).mpr hpowsub1
      linarith
  · constructor
    . have hpow : p ^ (a:ℝ) < p ^ α := by exact (Real.rpow_lt_rpow_left_iff hgt1).mpr hpa
      have hpowsub1 :p ^ (a:ℝ) - 1 < p ^ α -1 := by linarith
      have hover := div_lt_div_of_pos_right (c:=p-1) (h:=hpowsub1) (hc:=by linarith)
      linarith
    · have hpow : p ^ α < p ^ (b:ℝ) := by exact (Real.rpow_lt_rpow_left_iff hgt1).mpr hb
      have hpowsub1 : p ^ α - 1 < p ^ (b:ℝ) - 1 := by linarith
      have hover := div_lt_div_of_pos_right (c:=p-1) (h:=hpowsub1) (hc:=by linarith)
      linarith

/-- Exercise 10.4.3(a) -/
example (α:ℝ) : (nhdsWithin 1 (.Ioi 0 \ {1})).Tendsto (fun x:ℝ ↦ (x^α-1^α)/(x-1)) (nhds α) := by
  apply tendsto_nhdsWithin_nhds_of_rpow


/-- Exercise 10.4.3(b) -/
example (α:ℝ) {x:ℝ} (hx: x ∈ Set.Ioi 0) : HasDerivWithinAt (fun x:ℝ ↦ x^α) (α * x^(α-1)) (.Ioi 0) x := by
  rw [HasDerivWithinAt.iff]
  have hrpow := tendsto_nhdsWithin_nhds_of_rpow α
  have hg : Filter.Tendsto (fun x₁ => x₁ / x) (nhdsWithin x (Set.Ioi 0 \ {x})) (nhdsWithin 1 (Set.Ioi 0 \ {1})) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    . have hdiv : Filter.Tendsto (fun x₁ => x₁ / x) (nhds x) (nhds 1) := by
        have hcont : Continuous (fun (x:ℝ) => x) := by exact continuous_id'
        have htt := (hcont.div_const x).tendsto
        specialize htt x
        convert htt using 1
        simp at hx ⊢; field_simp
      exact tendsto_nhdsWithin_of_tendsto_nhds hdiv
    . filter_upwards [self_mem_nhdsWithin]
      intro a ha; simp at ha hx ⊢
      constructor
      . exact div_pos ha.1 hx
      . intro hax; field_simp at hax
        exact ha.2 hax
  have hcomp := hrpow.comp hg
  have hconstmul := hcomp.const_mul (x ^ (α - 1))
  refine (hconstmul.congr' ?_).mono_right ?_
  . filter_upwards [self_mem_nhdsWithin] with p hp
    simp at hp; obtain ⟨hppos, hpnx⟩ := hp
    have hpα : p ^ α > 0 := by positivity
    have hxα : x ^ α > 0 := by simp at hx; positivity
    have hpx : p - x ≠ 0 := by exact sub_ne_zero_of_ne hpnx
    simp
    conv_lhs =>
      rw [mul_div, mul_sub, mul_one, Real.rpow_sub (by exact hx)]
      simp
    nth_rewrite 2 [show x ^ α / x = (x ^ α / x) * 1 by simp]
    conv_lhs => rw [← mul_sub, Real.div_rpow (by linarith) (by simp at hx; linarith), mul_sub]
    field_simp
    grind
  · conv_lhs => rw [mul_comm]

end Chapter10
