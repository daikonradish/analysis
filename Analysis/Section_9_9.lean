import Mathlib.Tactic
import Analysis.Section_6_1
import Mathlib.Data.Nat.Nth
import Analysis.Section_9_6
/-!
# Analysis I, Section 9.9: Uniform continuity

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- API for Mathlib's {name}`UniformContinuousOn`.
- Continuous functions on compact intervals are uniformly continuous.

-/

open Chapter6 Filter

namespace Chapter9

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  apply ContinuousOn.div
  . exact continuousOn_const
  . exact continuousOn_id
  . intro x hx; simp at hx; linarith

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 2) := by
  intro hbdd
  choose B hB using hbdd
  by_cases! hB0 : B < 1
  . specialize hB 1 (by simp)
    simp at hB
    linarith
  . specialize hB (1/(2*B)) (by simp; exact ⟨by positivity, by field_simp; linarith⟩)
    simp at hB
    rw [abs_of_pos (by linarith)] at hB
    linarith


/-- Example 9.9.1 -/
example (x : ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 1/11
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets f ε x₀ δ
  intro hxδ
  unfold x₀ δ at hxδ
  unfold f x₀ ε
  rw [abs_le] at hxδ ⊢
  obtain ⟨hl, hr⟩ := hxδ
  have hl' : 10 / 11 ≤ x := by linarith
  have hr' : x ≤ 12 / 11 := by linarith
  constructor
  . suffices 0.9 ≤ 1/x by linarith
    field_simp; linarith
  . suffices 1/x ≤ 1.1 by linarith
    field_simp; linarith


example (x:ℝ) :
  let f : ℝ → ℝ := fun x ↦ 1/x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 0.1
  let δ : ℝ := 1/1010
  |x-x₀| ≤ δ → |f x - f x₀| ≤ ε := by
  extract_lets -merge f ε x₀ δ -- need the `-merge` flag due to the collision of `ε` and `x₀`
  intro hd
  unfold x₀ δ ε f at *
  rw [abs_le] at hd; obtain ⟨hd1, hd2⟩ := hd
  replace hd1 : -(1 / 1010) + 0.1 ≤ x := by linarith
  replace hd2 : x ≤ 1 / 1010 + 0.1    := by linarith
  norm_num at hd1 hd2
  field_simp
  rw [abs_div]
  field_simp
  conv_rhs => rw [abs_of_pos (by positivity)]
  ring_nf
  rw [abs_le]
  constructor <;> linarith

example (x:ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let x₀ : ℝ := 1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε x₀ δ
  intro hd
  unfold x₀ δ ε g at *
  simp
  rw [abs_le] at hd ⊢
  constructor <;> linarith

example (x₀ x : ℝ) :
  let g : ℝ → ℝ := fun x ↦ 2*x
  let ε : ℝ := 0.1
  let δ : ℝ := 0.05
  |x-x₀| ≤ δ → |g x - g x₀| ≤ ε := by
  extract_lets g ε δ
  intro hd
  unfold δ ε g at *
  rw [abs_le] at hd ⊢
  constructor <;> linarith

/-- Definition 9.9.2.  Here we use the Mathlib term {name}`UniformContinuousOn` -/
theorem UniformContinuousOn.iff (f: ℝ → ℝ) (X:Set ℝ) : UniformContinuousOn f X  ↔
  ∀ ε > (0:ℝ), ∃ δ > (0:ℝ), ∀ x₀ ∈ X, ∀ x ∈ X, δ.Close x x₀ → ε.Close (f x) (f x₀) := by
  simp_rw [Metric.uniformContinuousOn_iff_le, Real.Close]
  grind

theorem ContinuousOn.ofUniformContinuousOn {X:Set ℝ} (f: ℝ → ℝ) (hf: UniformContinuousOn f X) :
  ContinuousOn f X := by
  rw [UniformContinuousOn.iff] at hf
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  choose δ hδpos hδ using hf (ε/2) (by positivity)
  simp [Real.Close, Real.dist_eq] at hδ ⊢
  use δ; constructor
  . exact hδpos
  . intro x hx hxdist
    specialize hδ x hx b hb (by grind)
    grind

example : ¬ UniformContinuousOn (fun x:ℝ ↦ 1/x) (Set.Ioo 0 2) := by
  intro hucont
  rw [UniformContinuousOn.iff] at hucont
  choose δ hδpos hδ using hucont (1/10) (by positivity)
  contrapose! hδ
  use min δ (1/10); constructor
  . constructor
    . positivity
    . simp; norm_num
  use (min δ (1/10))/2; constructor
  . constructor
    . positivity
    . field_simp; norm_num
  . simp_rw [Real.Close, Real.dist_eq]; constructor
    . rw [abs_sub_comm, abs_of_pos]
      . simp; left; positivity
      . simp; constructor
        . field_simp; apply min_lt_of_left_lt; linarith
        . field_simp; suffices min δ (1 / 10) < (2/10) by linarith
          apply min_lt_of_right_lt; linarith
    field_simp; norm_num; field_simp
    rw [abs_of_pos]
    . apply min_lt_of_right_lt; linarith
    . positivity

end Chapter9

/--
Definition 9.9.5.  This is similar but not identical to {name}`Real.CloseSeq` from
Section 6.1.
-/
abbrev Real.CloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  (a.m = b.m) ∧ ∀ n ≥ a.m, ε.Close (a n) (b n)

abbrev Real.EventuallyCloseSeqs (ε:ℝ) (a b: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeqs (a.from N) (b.from N)

abbrev Chapter6.Sequence.equiv (a b: Sequence) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyCloseSeqs a b

/-- Remark 9.9.6 -/
theorem Chapter6.Sequence.equiv_iff_rat (a b: Sequence) :
  a.equiv b ↔ ∀ ε > (0:ℚ), (ε:ℝ).EventuallyCloseSeqs a b := by
  constructor
  . intro haeqb ε hε
    exact haeqb ε (by positivity)
  . intro hevclose ε hε
    choose q hql hqr using exists_rat_btwn hε
    have := hevclose q (by exact_mod_cast hql)
    suffices q < ε by grind
    exact hqr

/-- Lemma 9.9.7 / Exercise 9.9.1 -/
theorem Chapter6.Sequence.equiv_iff (a b: Sequence) :
  a.equiv b ↔ atTop.Tendsto (fun n ↦ a n - b n) (nhds 0) := by
  rw [Metric.tendsto_atTop]
  unfold equiv
  constructor
  . intro hevclose ε hε
    choose N hNam hN using hevclose (ε/2) (by positivity)
    use max 0 N
    intro n hn; simp at hn
    lift n to ℕ using by omega
    have hεcl := hN.2 n (by grind)
    rw [Sequence.from_eval _ (by exact hn.2), Sequence.from_eval _ (by exact hn.2)] at hεcl
    rw [Real.Close] at hεcl
    rw [Real.dist_eq] at hεcl ⊢
    simp; linarith
  . intro htt ε hε
    choose N hN using htt ε hε
    use max N (max a.m b.m); constructor
    . simp
    . unfold Real.CloseSeqs; constructor
      . simp
      . intro n hn
        unfold Real.Close
        rw [Sequence.from_eval _ (by exact le_of_max_le_right hn), Sequence.from_eval _ (by exact le_of_max_le_right hn)]
        specialize hN n (by simp at hn; exact hn.1)
        rw [Real.dist_eq] at hN ⊢
        simp at hN; linarith

namespace Chapter9


/-- Proposition 9.9.8 / Exercise 9.9.2 -/
theorem UniformContinuousOn.iff_preserves_equiv {X:Set ℝ} (f: ℝ → ℝ) :
  UniformContinuousOn f X ↔
  ∀ x y: ℕ → ℝ, (∀ n, x n ∈ X) → (∀ n, y n ∈ X) →
  (x:Sequence).equiv (y:Sequence) →
  (f ∘ x:Sequence).equiv (f ∘ y:Sequence) := by
  constructor
  . intro hucont φ τ hφX hτX hφτ ε hε
    rw [UniformContinuousOn.iff] at hucont
    unfold Real.EventuallyCloseSeqs Real.CloseSeqs
    choose δ hδpos hδ using hucont ε hε
    choose N hNam hN using hφτ δ hδpos
    use max 0 N; refine ⟨?_, ?_, ?_⟩
    . grind
    . grind
    . intro n hn; simp at hn
      rw [Sequence.from_eval _ (by simp; tauto), Sequence.from_eval _ (by simp; tauto)]
      unfold Real.CloseSeqs at hN
      have hδclose := hN.2 n (by simp; exact hn)
      rw [Sequence.from_eval _ (by tauto), Sequence.from_eval _ (by tauto)] at hδclose
      simp at hδclose; rw [if_pos (by tauto), if_pos (by tauto), dist_comm] at hδclose
      specialize hδ _ (hφX n.toNat) _ (hτX n.toNat) (by simp; tauto); simp at hδ
      simp; rwa [if_pos (by tauto), if_pos (by tauto), dist_comm]
  . intro hequiv
    rw [UniformContinuousOn.iff]
    intro ε hε
    contrapose! hequiv
    choose φ hφX τ hτX hδclose hεfar using (fun (n:ℕ) => hequiv (1/((n:ℝ)+1)) (by positivity))
    use φ, τ; refine ⟨?_, ?_, ?_, ?_⟩
    . exact hφX
    . exact hτX
    . intro ε' hε'
      unfold Real.EventuallyCloseSeqs Real.CloseSeqs
      choose N hN using exists_nat_one_div_lt hε'; simp at hN
      use max 0 N; simp
      intro n hn
      lift n to ℕ using by omega
      simp; rw [if_pos (by exact_mod_cast hn), if_pos (by exact_mod_cast hn)]
      specialize hδclose n; simp at hδclose
      rw [Real.dist_eq] at hδclose ⊢
      rw [abs_sub_comm]
      suffices ((n:ℝ) + 1)⁻¹ ≤ ((N:ℝ) + 1)⁻¹ by linarith
      field_simp; simp; exact_mod_cast hn
    . intro hf
      choose N hNam hN using hf ε hε; simp at hNam
      unfold Real.CloseSeqs Real.Close at hN
      obtain ⟨hNfrom, hNε⟩ := hN
      specialize hNε N (by simp; exact hNam)
      rw [Sequence.from_eval _ (by rfl), Sequence.from_eval _ (by rfl)] at hNε
      simp at hNε; rw [if_pos (by exact hNam), if_pos (by exact hNam)] at hNε
      specialize hεfar (N.toNat)
      rw [Real.dist_eq] at hεfar hNε
      rw [abs_sub_comm] at hεfar
      linarith

/-- Remark 9.9.9 -/
theorem Chapter6.Sequence.equiv_const (x₀: ℝ) (x:ℕ → ℝ) : atTop.Tendsto x (nhds x₀) ↔
  (x:Sequence).equiv (fun n:ℕ ↦ x₀:Sequence) := by
  constructor
  . intro htt
    rw [Metric.tendsto_atTop] at htt
    intro ε hε
    choose N hN using htt ε (by positivity)
    unfold Real.EventuallyCloseSeqs Real.CloseSeqs Real.Close
    use max 0 N; simp
    intro n hn
    lift n to ℕ using by omega
    simp at hn ⊢
    simp [hn]
    specialize hN n hn
    rw [Real.dist_eq] at hN ⊢
    linarith
  . intro hequiv
    rw [Metric.tendsto_atTop]
    intro ε hε
    choose N hNam hN using hequiv (ε/2) (by positivity)
    use N.toNat
    intro n hn
    unfold Real.CloseSeqs Real.Close at hN
    have hdist := hN.2 n (by simp; exact Int.toNat_le.mp hn)
    simp at hdist
    simp [Int.toNat_le.mp hn] at hdist
    rw [Real.dist_eq] at hdist ⊢
    linarith

/-- Example 9.9.10 -/
noncomputable abbrev f_9_9_10 : ℝ → ℝ := fun x ↦ 1/x

example : (fun n:ℕ ↦ 1/(n+1:ℝ):Sequence).equiv (fun n:ℕ ↦ 1/(2*(n+1):ℝ):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff]; simp
  have hg : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹ * 2⁻¹) atTop (nhds 0) := by
    have hden : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)) atTop atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop
    convert hden.inv_tendsto_atTop.mul_const 2⁻¹
    simp
  have htoNat : Tendsto Int.toNat atTop atTop := by
    apply Monotone.tendsto_atTop_atTop
    . intro a b hab
      exact Int.toNat_le_toNat hab
    . intro a
      use a; simp
  apply (hg.comp htoNat).congr'
  filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
  lift n to ℕ using by omega
  simp; linarith

example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  constructor
  . positivity
  . field_simp; linarith

example (n:ℕ) : 1/(2*(n+1):ℝ) ∈ Set.Ioo 0 2 := by
  constructor
  . positivity
  . field_simp; linarith

example : ¬ (fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ)):Sequence).equiv (fun n:ℕ ↦ f_9_9_10 (1/(2*(n+1):ℝ)):Sequence) := by
  intro hequiv
  rw [Chapter6.Sequence.equiv_iff] at hequiv
  simp at hequiv
  rw [Metric.tendsto_atTop] at hequiv
  choose N₁ hN₁ using hequiv 1 (by positivity)
  specialize hN₁ (max 100 N₁) (by simp)
  rw [if_pos (by simp), if_pos (by simp)] at hN₁
  simp at hN₁
  rw [two_mul] at hN₁
  ring_nf at hN₁
  rw [sub_eq_add_neg, ← neg_add, neg_eq_neg_one_mul, abs_mul] at hN₁
  simp at hN₁
  rw [abs_of_pos (by positivity)] at hN₁
  linarith


example : ¬ UniformContinuousOn f_9_9_10 (.Ioo 0 2) := by
  unfold f_9_9_10
  intro hucont
  rw [UniformContinuousOn.iff] at hucont
  choose δ hδpos hδ using hucont (1/10) (by positivity)
  contrapose! hδ
  use min δ (1/10); constructor
  . constructor
    . positivity
    . simp; norm_num
  use (min δ (1/10))/2; constructor
  . constructor
    . positivity
    . field_simp; norm_num
  . simp_rw [Real.Close, Real.dist_eq]; constructor
    . rw [abs_sub_comm, abs_of_pos]
      . simp; left; positivity
      . simp; constructor
        . field_simp; apply min_lt_of_left_lt; linarith
        . field_simp; suffices min δ (1 / 10) < (2/10) by linarith
          apply min_lt_of_right_lt; linarith
    field_simp; norm_num; field_simp
    rw [abs_of_pos]
    . apply min_lt_of_right_lt; linarith
    . positivity


/-- Example 9.9.11 -/
abbrev f_9_9_11 : ℝ → ℝ := fun x ↦ x^2

example : ((fun n:ℕ ↦ (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ (n+1)+1/(n+1:ℝ)):Sequence) := by
  rw [Chapter6.Sequence.equiv_iff]
  simp
  have htt0 : Filter.Tendsto (fun (n:ℕ) => (1/(n+1:ℝ))) atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have htt0' : Filter.Tendsto (fun (n:ℕ) => -(1/(n+1:ℝ))) atTop (nhds 0) := by
    have := htt0.neg
    rwa [neg_zero] at this
  have htoNat : Tendsto Int.toNat atTop atTop := by
    apply Monotone.tendsto_atTop_atTop
    . intro a b hab
      exact Int.toNat_le_toNat hab
    . intro a
      use a; simp
  apply (htt0'.comp htoNat).congr'
  filter_upwards [eventually_ge_atTop (0:ℤ)] with n hn
  simp [hn]

example : ¬ ((fun n:ℕ ↦ f_9_9_11 (n+1:ℝ)):Sequence).equiv ((fun n:ℕ ↦ f_9_9_11 ((n+1)+1/(n+1:ℝ))):Sequence) := by
  intro hequiv
  rw [Chapter6.Sequence.equiv_iff] at hequiv
  unfold f_9_9_11 at hequiv
  simp at hequiv
  rw [Metric.tendsto_atTop] at hequiv
  specialize hequiv 1 (by positivity)
  choose N hN using hequiv
  set n := max 100 N
  specialize hN n  (by unfold n; simp)
  rw [if_pos (by unfold n; simp), if_pos (by unfold n; simp)] at hN
  set x := ((n.toNat):ℝ) + 1
  nth_rw 2 [add_sq] at hN
  ring_nf at hN
  field_simp at hN
  rw [Real.dist_eq] at hN
  simp at hN
  rw [abs_div] at hN
  rw [div_lt_iff₀ (by positivity)] at hN
  rw [sub_eq_add_neg, ← neg_add, neg_eq_neg_one_mul, abs_mul] at hN
  simp at hN
  rw [abs_of_pos (by positivity)] at hN
  have : x ^ 2 < -1 := by linarith
  exact absurd this (by nlinarith [sq_nonneg x])

example : ¬ UniformContinuousOn f_9_9_11 .univ := by
  unfold f_9_9_11
  intro hucont
  rw [UniformContinuousOn.iff] at hucont
  choose δ hδpos hδ using hucont 1 (by positivity)
  unfold Real.Close at hδ
  simp_rw [Real.dist_eq] at hδ
  specialize hδ (1/δ) (by tauto) (1/δ + δ/2) (by tauto) (by simp; rw [abs_of_pos (by positivity)]; linarith)
  rw [sq_sub_sq] at hδ; ring_nf at hδ
  rw [mul_inv_cancel₀ (by linarith)] at hδ
  have f1 : |1 + δ ^ 2 * (1 / 4)| ≤ |1| + |δ ^ 2 * (1 / 4)| := by apply abs_add_le
  simp at f1
  have f2 : |1 + δ ^ 2 * (1 / 4)| > 0 := by positivity
  have f3 : δ ^ 2 * (1 / 4) > 0 := by positivity
  grind

/-- Proposition 9.9.12 / Exercise 9.9.3  -/
theorem UniformContinuousOn.ofCauchy  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x: ℕ → ℝ} (hx: (x:Sequence).IsCauchy) (hmem : ∀ n, x n ∈ X) :
  (f ∘ x:Sequence).IsCauchy := by
  rw [UniformContinuousOn.iff] at hf
  intro ε hε
  choose δ hδpos hδ  using hf (ε/2) (by positivity)
  choose N hN using hx δ hδpos
  use max 0 N; simp
  intro n hn m hm
  simp at hn hm
  have hδdist := hN.2 n (by simp; exact hn) m (by simp; exact hm)
  simp at hδdist; rw [dist_comm] at hδdist
  simp
  rw [if_pos hn, if_pos hn.1, if_pos hm, if_pos hm.1] at hδdist ⊢
  specialize hδ (x n.toNat) (hmem _) (x m.toNat) (hmem _) (by simp; exact hδdist)
  simp at hδ; rw [dist_comm] at hδ
  rw [Real.dist_eq] at hδ ⊢
  linarith


/-- Example 9.9.13 -/
example : ((fun n:ℕ ↦ 1/(n+1:ℝ)):Sequence).IsCauchy := by
  intro ε hε
  have htt0 : Filter.Tendsto (fun (n:ℕ) => (1/(n+1:ℝ))) atTop (nhds 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Metric.tendsto_atTop] at htt0
  choose N hN using htt0 (ε / 4) (by positivity)
  use N; simp
  intro n hn m hm; simp at hn hm
  lift n to ℕ using by omega
  lift m to ℕ using by omega
  simp at hn hm
  simp; rw [if_pos hn, if_pos hm]
  have hmm := hN m hm
  have hnn := hN n hn
  rw [Real.dist_eq] at hmm hnn ⊢
  simp at hmm hnn
  calc _ ≤ |((n:ℝ) + 1)⁻¹ + -((m:ℝ) + 1)⁻¹|   := by rw [sub_eq_add_neg]
       _ ≤ |((n:ℝ) + 1)⁻¹| + |-((m:ℝ) + 1)⁻¹| := by apply abs_add_le
       _ = |((n:ℝ) + 1)⁻¹| + |((m:ℝ) + 1)⁻¹|  := by congr 1; rw [abs_neg]
       _ ≤ ε / 2 + ε / 2                      := by gcongr <;> grind
       _ = ε                                  := by linarith


example (n:ℕ) : 1/(n+1:ℝ) ∈ Set.Ioo 0 2 := by
  constructor
  . positivity
  . field_simp
    linarith

example : ¬ ((fun n:ℕ ↦ f_9_9_10 (1/(n+1:ℝ))):Sequence).IsCauchy := by
  unfold f_9_9_10
  intro h
  simp at h
  choose N hNam hN using  h (1/2) (by positivity)
  set N' := max 0 N with hNdef'
  specialize hN N' (by unfold N'; simp) (N'+1) (by unfold N'; simp)
  simp at hN
  rw [if_pos (by unfold N'; simp), if_pos (by unfold N'; simp)] at hN
  rw [if_pos (by unfold N'; grind), if_pos (by unfold N'; grind)] at hN
  rw [Real.dist_eq] at hN
  simp at hN
  rw [Int.toNat_add (by unfold N'; simp) (by linarith)] at hN
  simp at hN
  linarith

example : ¬ UniformContinuousOn f_9_9_10 (Set.Ioo 0 2) := by
  unfold f_9_9_10
  intro hucont
  rw [UniformContinuousOn.iff] at hucont
  choose δ hδpos hδ using hucont (1/10) (by positivity)
  contrapose! hδ
  use min δ (1/10); constructor
  . constructor
    . positivity
    . simp; norm_num
  use (min δ (1/10))/2; constructor
  . constructor
    . positivity
    . field_simp; norm_num
  . simp_rw [Real.Close, Real.dist_eq]; constructor
    . rw [abs_sub_comm, abs_of_pos]
      . simp; left; positivity
      . simp; constructor
        . field_simp; apply min_lt_of_left_lt; linarith
        . field_simp; suffices min δ (1 / 10) < (2/10) by linarith
          apply min_lt_of_right_lt; linarith
    field_simp; norm_num; field_simp
    rw [abs_of_pos]
    . apply min_lt_of_right_lt; linarith
    . positivity

/-- Corollary 9.9.14 / Exercise 9.9.4 -/
theorem UniformContinuousOn.limit_at_adherent  {X:Set ℝ} (f: ℝ → ℝ)
  (hf: UniformContinuousOn f X) {x₀:ℝ} (hx₀: AdherentPt x₀ X) :
  ∃ L:ℝ, (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  rw [limit_of_AdherentPt] at hx₀
  choose g hgX htt using hx₀
  have hgcauch : (g:Sequence).IsCauchy := by
    apply (Sequence.Cauchy_iff_convergent _).mpr
    use x₀
    intro ε hε
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at htt
    choose N hN using htt (ε / 2) (by positivity)
    use max 0 N
    simp
    unfold Real.CloseSeq Real.Close
    intro n hn; simp at hn; lift n to ℕ using by omega
    simp at hn ⊢
    rw [if_pos (by omega), Real.dist_eq]
    specialize hN n hn
    linarith
  have hfgcauch := UniformContinuousOn.ofCauchy f hf hgcauch hgX
  have hfgconv := (Sequence.Cauchy_iff_convergent _).mp hfgcauch
  choose L hL using hfgconv
  have httL : Filter.Tendsto (f ∘ g) atTop (nhds L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    choose N hNam hN using hL (ε/2) (by positivity)
    simp at hNam
    lift N to ℕ using by omega
    use N
    intro n hn
    specialize hN n (by simp; exact hn)
    simp [hn] at hN
    rw [Real.dist_eq] at hN ⊢
    simp; linarith
  use L
  apply Filter.tendsto_of_seq_tendsto
  intro φ hφ
  rw [tendsto_nhdsWithin_iff] at hφ
  obtain ⟨hφ, hfilterup⟩ := hφ
  have hgφ : Tendsto (g - φ) atTop (nhds 0) := by
    have := htt.sub hφ
    simp at this
    convert this using 1
  have hfdiff : Tendsto (fun n => f (g n) - f (φ n)) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    rw [UniformContinuousOn.iff] at hf
    intro ε hε
    simp
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at hgφ
    simp at hgφ
    choose δ hδpos hδ using hf (ε/2) (by positivity)
    choose N₁ hN₁ using hgφ δ hδpos
    choose N₂ hN₂ using Filter.eventually_atTop.mp hfilterup
    use max N₁ N₂
    intro n hn; simp at hn
    specialize hN₁ n (by tauto); rw [abs_sub_comm] at hN₁
    specialize hN₂ n (by tauto)
    specialize hδ (g n) (hgX _) (φ n) hN₂ (by simp; rw [Real.dist_eq]; linarith)
    unfold Real.Close at hδ; rw [Real.dist_eq] at hδ; rw [abs_sub_comm]
    linarith
  have := httL.sub hfdiff
  simp at this
  simpa using this


/-- Proposition 9.9.15 / Exercise 9.9.5 -/
theorem UniformContinuousOn.of_bounded {E X:Set ℝ} {f: ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hEX: E ⊆ X) (hE: Bornology.IsBounded E) :
  Bornology.IsBounded (f '' E) := by
  rw [← BddOn.iff']
  by_contra! hunbound
  choose φ hφE hφbig using (fun (n:ℕ) => hunbound n)
  have hclosed : IsClosed (closure E) := by exact isClosed_closure
  have hclosedbdd : Bornology.IsBounded (closure E) := by
    exact hE.closure
  have hxclE : ∀ (n:ℕ), φ n ∈ closure E := by
    intro n
    specialize hφE n
    suffices E ⊆ closure E by exact this hφE
    exact subset_closure E
  choose τ hτ L hLcLE hφτL using (Heine_Borel (closure E)).mp ⟨hclosed, hclosedbdd⟩ φ hxclE
  have had : AdherentPt L X := by
    rw [← closure_def']
    apply closure_mono hEX
    exact hLcLE
  choose M hM using UniformContinuousOn.limit_at_adherent f hf had
  have hφτX : ∀ (n:ℕ), φ (τ n) ∈ X := by
    intro n
    apply hEX
    exact hφE (τ n)
  have hφτM : Tendsto (f ∘ φ ∘ τ) atTop (nhds M) := by
    apply hM.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    . exact hφτL
    . filter_upwards [eventually_ge_atTop 0] with n hn
      exact hφτX n
  have hτφTop : Tendsto |f ∘ φ ∘ τ| atTop atTop := by
    refine tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
    intro n
    simp
    specialize hφbig (τ n)
    suffices n ≤ τ n by rify at this; linarith
    simpa using hτ.id_le n
  apply not_tendsto_nhds_of_tendsto_atTop hτφTop |M|
  exact hφτM.abs


/-- Theorem 9.9.16 -/
theorem UniformContinuousOn.of_continuousOn {a b:ℝ} {f:ℝ → ℝ}
  (hcont: ContinuousOn f (.Icc a b)) :
  UniformContinuousOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra h; rw [iff_preserves_equiv] at h
  simp [-Set.mem_Icc] at h
  choose x hx y hy hequiv ε hε h using h
  set E : Set ℕ := {n | ¬ ε.Close (f (x n)) (f (y n)) }
  have hE : Infinite E := by
    rw [←not_finite_iff_infinite]
    by_contra! this
    replace : ε.EventuallyCloseSeqs (fun n ↦ f (x n):Sequence) (fun n ↦ f (y n):Sequence) := by
      have hfin := this
      unfold Real.EventuallyCloseSeqs Real.CloseSeqs Real.Close
      by_cases! hEempty : E.Nonempty
      . have hfin' : E.Finite := by exact Set.finite_coe_iff.mp hfin
        set S := hfin'.toFinset
        have hSnonempty : S.Nonempty := by exact (Set.Finite.toFinset_nonempty hfin').mpr hEempty
        set M := S.max' hSnonempty
        use (M+1); simp; constructor
        . linarith
        · intro n hn hnM; simp [hn, hnM]
          have hnotS : n.toNat ∉ S := by
            intro hS
            have := S.le_max' n.toNat hS
            unfold M at hnM
            grind
          have hnotE : n.toNat ∉ E := by
            unfold S at hnotS
            intro hE
            have := (Set.Finite.mem_toFinset hfin').mpr hE
            exact hnotS this
          unfold E at hnotE
          simpa using hnotE
      . use 0; simp
        intro n hn; simp [hn]
        lift n to ℕ using by omega
        have hεclose : ε.Close (f (x n)) (f (y n)) := by
          by_contra h'
          have hE' : E.Nonempty := by
            use n; unfold E; exact h'
          rw [hEempty] at hE'
          simp at hE'
        simp; exact hεclose
    choose N hNam hN using this
    simp at hNam
    unfold Real.CloseSeqs Real.Close at hN
    simp at hN
    choose N' hNam' hNN' hN' using h N hNam
    simp [hNN', hNam'] at hN'
    specialize hN N' hNam' hNN'
    simp [hNam', hNN'] at hN
    rw [Real.dist_eq] at hN' hN
    linarith
  observe : Countable E
  set n : ℕ → ℕ := Nat.nth E
  rw [Set.infinite_coe_iff] at hE
  have hmono : StrictMono n := by apply_rules [Nat.nth_strictMono]
  have hmem (j:ℕ) : n j ∈ E := j.nth_mem_of_infinite hE
  have hsep (j:ℕ) : |f (x (n j)) - f (y (n j))| > ε := by
    specialize hmem j
    simpa [E, Real.Close, Real.dist_eq] using hmem
  observe hxmem : ∀ j, x (n j) ∈ Set.Icc a b
  observe hymem : ∀ j, y (n j) ∈ Set.Icc a b
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ j, hj, ⟨ L, hL, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨ hclosed, hbounded ⟩ _ hxmem
  replace hcont := ContinuousOn.continuousWithinAt hcont hL
  have hconv' := hconv.comp_of_continuous hcont (fun k ↦ hxmem (j k))
  rw [Sequence.equiv_iff] at hequiv
  replace hequiv : atTop.Tendsto (fun k ↦ x (n (j k)) - y (n (j k))) (nhds 0) := by
    observe hj' : atTop.Tendsto j .atTop
    observe hn' : atTop.Tendsto n .atTop
    observe hcoe : atTop.Tendsto (fun n:ℕ ↦ (n:ℤ)) .atTop
    exact hequiv.comp (hcoe.comp (hn'.comp hj'))
  have hyconv : atTop.Tendsto (fun k ↦ y (n (j k))) (nhds L) := by
    convert hconv.sub hequiv with k
    . abel
    simp
  replace hyconv := hyconv.comp_of_continuous hcont (fun k ↦ hymem (j k))
  have : atTop.Tendsto (fun k ↦ f (x (n (j k))) - f (y (n (j k)))) (nhds 0) := by
    convert hconv'.sub hyconv; simp
  rw [Metric.tendsto_atTop] at this
  choose N hN using this ε hε
  specialize hsep (j N)
  specialize hN N (by rfl); simp at hN
  linarith


/-- Exercise 9.9.6 -/
theorem UniformContinuousOn.comp {X Y: Set ℝ} {f g:ℝ → ℝ}
  (hf: UniformContinuousOn f X) (hg: UniformContinuousOn g Y)
  (hrange: f '' X ⊆ Y) : UniformContinuousOn (g ∘ f) X := by
  rw [UniformContinuousOn.iff] at hf hg ⊢
  intro ε hε
  choose δ₁ hδpos₁ hδ₁ using hg ε hε
  choose δ₂ hδpos₂ hδ₂ using hf δ₁ hδpos₁
  use δ₂; constructor
  . exact hδpos₂
  . intro x hx y hy hxy
    specialize hδ₂ x hx y hy hxy
    exact hδ₁ (f x) (by apply hrange; use x) (f y) (by apply hrange; use y) hδ₂


end Chapter9
