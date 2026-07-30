import Mathlib.Tactic
import Mathlib.Topology.ContinuousOn
import Analysis.Section_7_3
import Analysis.Section_9_4
import Analysis.Section_9_8
import Analysis.Section_10_1
import Analysis.Section_10_2
import Analysis.Section_11_6
import Analysis.Section_11_8


/-!
# Analysis I, Section 11.9: The two fundamental theorems of calculus

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- The fundamental theorems of calculus.
-/

namespace Chapter11
open Chapter9 Chapter10 BoundedInterval

/-- Theorem 11.9.1 (First Fundamental Theorem of Calculus). -/
theorem cts_of_integ {a b:ℝ} {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  ContinuousOn (fun x => integ f (Icc a x)) (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  set F : ℝ → ℝ := fun x => integ f (Icc a x)
  choose M hM using hf.1
  have {x y:ℝ} (hxy: x < y) (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) : |F y - F x| ≤ M * (y - x) := by
    simp at hx hy
    have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx.1 (le_of_lt hxy))).2
    simp [F, this.2, abs_le']
    constructor
    . convert this.1.mono (g := fun _ ↦ M) (IntegrableOn.const _ _).1 _
      . simp [IntegrableOn.const, le_of_lt hxy]
      intro z hz
      specialize hM z ?_
      . simp at *; grind
      grind [abs_le']
    rw [neg_le]
    convert (IntegrableOn.const _ _).1.mono (f := fun _ ↦ -M) this.1 _
    . simp [IntegrableOn.const, le_of_lt hxy]
    intro z hz
    specialize hM z ?_
    . simp at *; grind
    grind [abs_le']
  replace {x y:ℝ} (hx: x ∈ Set.Icc a b) (hy: y ∈ Set.Icc a b) :
    |F y - F x| ≤ M * |x-y| := by
    obtain h | rfl | h := lt_trichotomy x y
    . simp [abs_of_neg (show x-y < 0 by linarith), this h hx hy]
    . simp
    . simp [abs_of_pos (show 0 < x-y by linarith), abs_sub_comm, this h hy hx]
  replace : UniformContinuousOn F (.Icc a b) := by
    simp [Metric.uniformContinuousOn_iff, Real.dist_eq, -Set.mem_Icc]
    intro ε hε
    use (ε/(max M 1)), (by positivity)
    intro x hx y hy hxy
    calc
      _ = |F y - F x| := by rw [abs_sub_comm]
      _ ≤ M * |x-y| := this hx hy
      _ ≤ (max M 1) * |x-y| := by gcongr; apply le_max_left
      _ < (max M 1) * (ε / (max M 1)) := by gcongr
      _ = _ := by field_simp
  exact ContinuousOn.ofUniformContinuousOn F this

theorem deriv_of_integ {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: IntegrableOn f (Icc a b))
  {x₀:ℝ} (hx₀ : x₀ ∈ Set.Icc a b) (hcts: ContinuousWithinAt f (Icc a b) x₀) :
  HasDerivWithinAt (fun x => integ f (Icc a x)) (f x₀) (.Icc a b) x₀ := by
  -- This proof is written to follow the structure of the original text.
  rw [HasDerivWithinAt.iff_approx_linear]
  simp [(ContinuousWithinAt.tfae _ f x₀).out 0 2] at hcts
  peel hcts with ε hε δ hδ hconv; intro y hy hyδ
  obtain hx₀y | rfl | hx₀y := lt_trichotomy x₀ y
  . have := ((hf.join (join_Icc_Ioc hy.1 hy.2)).1.join (join_Icc_Ioc hx₀.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_pos (show 0 < y - x₀ by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y] at h1 h2
      split_ands
      . convert h1 using 1;
        ring
      . simp [←sub_nonneg] at *; convert h2 using 1; ring
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith
  . simp
  . --- visually, looks something like that
    --- [a                                       y                   x₀]
    --- IntegrableOn f (Ioc y x₀) ∧ integ f (Icc a x₀) = integ f (Icc a y) + integ f (Ioc y x₀)
    have := ((hf.join (join_Icc_Ioc hx₀.1 hx₀.2)).1.join (join_Icc_Ioc hy.1 (le_of_lt hx₀y))).2
    simp [this.2, abs_le', abs_of_neg (show y - x₀ < 0 by linarith)]
    have h1 := this.1.mono (g := fun _ ↦ f x₀ + ε) (IntegrableOn.const _ _).1 ?_
    have h2 := (IntegrableOn.const _ _).1.mono (f := fun _ ↦ f x₀ - ε) this.1 ?_
    . simp [IntegrableOn.const, le_of_lt hx₀y, BoundedInterval.a, BoundedInterval.b] at h1 h2
      split_ands
      . rw [neg_le]
        convert h2 using 1
        ring
      . simp [←sub_nonneg] at *; convert h1 using 1; ring
    all_goals intro z hz; simp [abs_lt] at *; specialize hconv z ?_ ?_ ?_ ?_ <;> linarith



/-- Example 11.9.2 -/
theorem IntegrableOn.of_f_9_8_5 : IntegrableOn f_9_8_5 (Icc 0 1) :=
  integ_of_monotone (StrictMonoOn.of_f_9_8_5.mono (by simp)).monotoneOn

noncomputable abbrev F_11_9_2 := fun x ↦ integ f_9_8_5 (Icc 0 x)

theorem ContinuousOn.of_F_11_9_2 : ContinuousOn F_11_9_2 (.Icc 0 1) := cts_of_integ IntegrableOn.of_f_9_8_5

theorem DifferentiableOn.of_F_11_9_2 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) (hx': x ∈ Set.Icc 0 1) :
  DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) x := by
  have := deriv_of_integ (show 0 < 1 by norm_num) .of_f_9_8_5 hx' (ContinuousAt.of_f_9_8_5 hx).continuousWithinAt
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt] at this
  exact ⟨_, this⟩

open Classical in
/-- Exercise 11.9.1 -/
theorem DifferentiableOn.of_F_11_9_2' {q:ℚ} (hq: (q:ℝ) ∈ Set.Ioo 0 1) : ¬ DifferentiableWithinAt ℝ F_11_9_2 (.Icc 0 1) q := by
  intro hdiff
  have hD := hdiff.hasDerivWithinAt
  have ⟨hq0, hq1⟩ := hq
  set c : ℝ := f_9_8_5 q
  set D : ℝ := derivWithin F_11_9_2 (Set.Icc 0 1) q
  have hgpos : 0 < g_9_8_5 q := by exact pos_of_g_9_8_5
  have hint {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) : IntegrableOn f_9_8_5 (Icc u v) := by
    apply IntegrableOn.of_f_9_8_5.mono'
    rw [BoundedInterval.subset_iff]
    simp; exact Set.Icc_subset_Icc hu hv
  have hint'  {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) : IntegrableOn f_9_8_5 (Ioc u v) := by
    apply IntegrableOn.of_f_9_8_5.mono' ?_
    rw [BoundedInterval.subset_iff]
    simp; grind
  have hadd {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v) : F_11_9_2 v - F_11_9_2 u = integ f_9_8_5 (Ioc u v) := by
    have hjoin := (BoundedInterval.join_Icc_Ioc hu huv)
    have hint0 : IntegrableOn f_9_8_5 (Icc 0 v) := by
      exact hint (u:=0) (v:=v) (by rfl) (by linarith)
    have ⟨_, _, h⟩ := hint0.join hjoin
    unfold F_11_9_2
    linarith
  have hleft {l : ℝ} (h : l ≤ q) : f_9_8_5 l ≤ c := by
    unfold c
    rcases h.eq_or_lt with rfl | hlt
    . rfl
    have hl : l ∈ Set.univ := by tauto
    have hq : (q:ℝ) ∈ Set.univ := by tauto
    linarith [StrictMonoOn.of_f_9_8_5 hl hq hlt]
  have hright {z : ℝ} (h : q < z) : c + g_9_8_5 q ≤ f_9_8_5 z := by
    have hg0 : ∀ r : ℚ, 0 ≤ g_9_8_5 r := by
      intro r
      exact nonneg_of_g_9_8_5
    have hsum : Summable g_9_8_5 := by
      exact summable_of_g_9_8_5
    set S : Set ℚ := {r : ℚ | (r:ℝ) < (q:ℝ)} with hSdef
    set T : Set ℚ := {r : ℚ | (r:ℝ) < z} with hTdef
    have hqS  : q ∉ S := by simp [hSdef]
    have hdisj : Disjoint S ({q} : Set ℚ) := by
      simpa [Set.disjoint_singleton_right] using hqS
    have hST  : S ∪ {q} ⊆ T := by
      rintro r (hr | rfl)
      · unfold T
        unfold S at hr; simp at hr ⊢
        rify at hr
        linarith
      · unfold T; exact h
    have hSsum := hsum.indicator S
    have hqsum := hsum.indicator ({q} : Set ℚ)
    have hUsum := hsum.indicator (S ∪ {q})
    have hTsum := hsum.indicator T
    have hfz : f_9_8_5 z = ∑' r, T.indicator g_9_8_5 r := tsum_subtype T g_9_8_5
    have hcq : c = ∑' r, S.indicator g_9_8_5 r := by
      unfold c
      exact tsum_subtype S g_9_8_5
    have hgq : g_9_8_5 q = ∑' r, ({q} : Set ℚ).indicator g_9_8_5 r := by
      rw [tsum_eq_single q (by intro b hb; apply Set.indicator_of_notMem; simpa using hb)]
      simp
    have hsplit : c + g_9_8_5 q = ∑' r, (S ∪ {q}).indicator g_9_8_5 r := by
      rw [hcq, hgq, ← Summable.tsum_add hSsum hqsum, Set.indicator_union_of_disjoint hdisj]
    rw [hsplit, hfz]
    apply Summable.tsum_le_tsum
    . intro p
      exact Set.indicator_le_indicator_apply_of_subset hST (hg0 p)
    . exact Summable.indicator hsum (S ∪ {q})
    . exact Summable.indicator hsum T
  have hsloper {x : ℝ} (h : q < x) (h1 : x ≤ 1) : c + g_9_8_5 q ≤ slope F_11_9_2 q x := by
    have hif := hint' (u:=q) (v:=x) (by linarith) (by linarith)
    have hcon := IntegrableOn.const (c + g_9_8_5 q) (Ioc q x)
    have hmaj : MajorizesOn f_9_8_5 (fun x => c + g_9_8_5 q) (Ioc q x) := by
      intro p hp; simp at hp
      dsimp; apply hright
      linarith
    have hle := IntegrableOn.mono hcon.1 hif hmaj
    rw [hcon.2] at hle
    rw [show |Ioc q x|ₗ = x - q by simp only [length, BoundedInterval.a, BoundedInterval.b]; simp; linarith] at hle
    have hFsub : F_11_9_2 x - F_11_9_2 q = integ f_9_8_5 (Ioc q x) := by
      exact hadd (u:=q) (v:=x) (by linarith) (by linarith) (by linarith)
    rw [slope_def_field, hFsub, le_div_iff₀ (by linarith)]
    field_simp
    linarith
  have hslopel {x:ℝ} (h0 : 0 ≤ x) (h : x < q) : slope F_11_9_2 (q:ℝ) x ≤ c := by
    have hif := hint' (u:=x) (v:=q) (by linarith) (by linarith)
    have hcon := IntegrableOn.const c (Ioc x q)
    have hmin : MajorizesOn (fun _ ↦ c) f_9_8_5 (Ioc x (q:ℝ)) := by
      intro z hz; simp at hz
      dsimp; apply hleft
      linarith
    have hle := IntegrableOn.mono hif hcon.1 hmin
    rw [hcon.2] at hle
    rw [show |Ioc x q|ₗ = q - x by simp only [length, BoundedInterval.a, BoundedInterval.b]; simp; linarith] at hle
    have hFsub : F_11_9_2 q - F_11_9_2 x = integ f_9_8_5 (Ioc x q) := by
      exact hadd (u:=x) (v:=q) (by linarith) (by linarith) (by linarith)
    rw [slope_def_field, div_le_iff_of_neg (by linarith)]
    field_simp
    linarith
  rw [hasDerivWithinAt_iff_tendsto_slope] at hD
  have hDR : c + g_9_8_5 q ≤ D := by
    have hmem : (Set.Icc (0:ℝ) 1 \ {(q:ℝ)}) ∈ nhdsWithin (q:ℝ) (Set.Ioi (q:ℝ)) := by
      apply mem_nhdsWithin.mpr
      use Set.Iio 1
      refine ⟨isOpen_Iio, hq1, ?_⟩
      rintro x ⟨hx, hx'⟩
      simp at hx hx' ⊢
      grind
    have htend : Filter.Tendsto (slope F_11_9_2 (q:ℝ)) (nhdsWithin (q:ℝ) (Set.Ioi (q:ℝ))) (nhds D) := by
      apply hD.mono_left
      exact nhdsWithin_le_iff.mpr hmem
    apply ge_of_tendsto htend
    filter_upwards [Ioo_mem_nhdsGT hq1] with a ha; simp at ha
    apply hsloper <;> linarith
  have hDL : D ≤ c := by
    have hmem : (Set.Icc (0:ℝ) 1 \ {(q:ℝ)}) ∈ nhdsWithin (q:ℝ) (Set.Iio (q:ℝ)) := by
      apply mem_nhdsWithin.mpr
      use Set.Ioi 0
      refine ⟨isOpen_Ioi, hq0, ?_⟩
      rintro x ⟨hx, hx'⟩
      simp at hx hx' ⊢
      grind
    have htend : Filter.Tendsto (slope F_11_9_2 (q:ℝ)) (nhdsWithin (q:ℝ) (Set.Iio (q:ℝ))) (nhds D) := by
      apply hD.mono_left
      exact nhdsWithin_le_iff.mpr hmem
    apply le_of_tendsto htend
    filter_upwards [Ioo_mem_nhdsLT hq0] with a ha; simp at ha
    apply hslopel <;> linarith
  linarith

/-- Definition 11.9.3.  We drop the requirement that x be a limit point as this makes
    the Lean arguments slightly cleaner -/
abbrev AntiderivOn (F f: ℝ → ℝ) (I: BoundedInterval) :=
  DifferentiableOn ℝ F I ∧ ∀ x ∈ I, HasDerivWithinAt F (f x) I x

theorem AntiderivOn.mono {F f: ℝ → ℝ} {I J: BoundedInterval}
  (h: AntiderivOn F f I) (hIJ: J ⊆ I) : AntiderivOn F f J :=
  ⟨ h.1.mono hIJ, by intro x hx; rw [subset_iff] at hIJ; exact (h.2 x (hIJ hx)).mono hIJ ⟩

/-- Theorem 11.9.4 (Second Fundamental Theorem of Calculus) -/
theorem integ_eq_antideriv_sub {a b:ℝ} (h:a ≤ b) {f F: ℝ → ℝ}
  (hf: IntegrableOn f (Icc a b)) (hF: AntiderivOn F f (Icc a b)) :
  integ f (Icc a b) = F b - F a := by
  -- This proof is written to follow the structure of the original text.
  obtain h | h := lt_or_eq_of_le h
  . have hF_cts : ContinuousOn F (.Icc a b) := by
      intro x hx; exact ContinuousWithinAt.of_differentiableWithinAt (hF.1 x hx)
    -- for technical reasons we need to extend F by constant outside of Icc a b
    let F' : ℝ → ℝ := fun x ↦ F (max (min x b) a)

    have hFF' {x:ℝ} (hx: x ∈ Set.Icc a b) : F' x = F x := by simp_all [F']

    have hF'_cts : ContinuousOn F' (Ioo (a-1) (b+1)) := by
      convert (hF_cts.comp_continuous (f := fun x ↦ max (min x b) a) (by fun_prop) ?_).continuousOn using 1
      intros; simp [le_of_lt h]

    have hupper (P: Partition (Icc a b)) : upper_riemann_sum f P ≥ F b - F a := by
      have := P.sum_of_α_length F'
      calc
        _ ≥ ∑ J ∈ P.intervals, F'[J]ₗ := by
          apply Finset.sum_le_sum
          intro J hJ; by_cases hJ_empty : (J:Set ℝ) = ∅
          . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
          obtain hJab | hJab := le_or_gt J.b J.a
          . push_neg at hJ_empty; choose x hx using hJ_empty
            cases J with
            | Ioo _ _ => simp at hx; linarith
            | Ioc _ _ => simp at hx; linarith
            | Ico _ _ => simp at hx; linarith
            | Icc c d =>
              simp at hx
              simp [show c = d by linarith]
              have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
                apply P.contains at hJ
                simp [subset_iff] at hJ
                rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
                apply Ioo_mem_nhds <;> linarith
              rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
          set c := J.a
          set d := J.b
          apply P.contains at hJ
          have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
          apply ((Ioo_subset J).trans hJ).trans at hJ'
          simp [subset_iff] at hJ'
          rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
          have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
          apply hJ.trans at hJ''
          rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
          have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
          . choose e he hmean using this
            have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
              apply (Ioo_subset J).trans at hJ
              simp [subset_iff] at hJ
              apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
              all_goals grind
            replace := derivative_unique ?_ this hmean
            . calc
                _ = F' d - F' c := rfl
                _ = (d - c) * f e := by
                  rw [this]; have : d-c > 0 := by linarith
                  field_simp
                _ = f e * |J|ₗ := by simp [mul_comm, length]; left; rw [max_eq_left (by linarith)]
                _ ≤ _ := by
                  gcongr; apply le_csSup
                  . rw [bddAbove_def]
                    choose M hM using hf.1; use M
                    simp [abs_le', -Set.mem_Icc] at hM ⊢
                    intro x hx; rw [subset_iff] at hJ; specialize hM x (hJ hx); tauto
                  simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
            rw [←mem_closure_iff_clusterPt]
            apply closure_mono (s := .Ioo e d)
            . intro _ _; simp at *; refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> linarith
            simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
          . simp; rw [Set.Icc_subset_Ioo_iff (le_of_lt hJab)]; grind
          apply (Ioo_subset J).trans at hJ
          apply (hF.1.mono _).congr
          . intro x hx
            have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
            grind
          grind [subset_iff]
        _ = F'[Icc a b]ₗ := P.sum_of_α_length F'
        _ = F' b - F' a := by
          apply α_length_of_cts _ _ _ _ hF'_cts <;> try linarith
          intro _ _; simp [mem_iff] at *; grind
        _ = _ := by congr 1 <;> apply hFF' <;> grind
    have hlower (P: Partition (Icc a b)) : lower_riemann_sum f P ≤ F b - F a := by
      have h1 := P.sum_of_α_length F'
      have h2 : F'[Icc a b]ₗ = F' b - F' a := by
        apply α_length_of_cts (hα:=hF'_cts) <;> try linarith
        simp [BoundedInterval.subset_iff]; grind
      rw [h2, hFF' (x:=a) (by simp_all), hFF' (x:=b) (by simp_all)] at h1
      rw [← h1]
      unfold lower_riemann_sum
      apply Finset.sum_le_sum
      intro J hJ
      by_cases hJ_empty : (J:Set ℝ) = ∅
      . simp [α_length_of_empty _ hJ_empty, length_of_empty hJ_empty]
      obtain hJab | hJab := le_or_gt J.b J.a
      . push_neg at hJ_empty; choose x hx using hJ_empty
        cases J with
        | Ioo _ _ => simp at hx; linarith
        | Ioc _ _ => simp at hx; linarith
        | Ico _ _ => simp at hx; linarith
        | Icc c d =>
          simp at hx
          simp [show c = d by linarith]
          have hnhds: (Ioo (a-1) (b+1):Set ℝ) ∈ nhds d := by
            apply P.contains at hJ
            simp [subset_iff] at hJ
            rw [Set.Icc_subset_Icc_iff (by linarith)] at hJ
            apply Ioo_mem_nhds <;> linarith
          rw [α_length_of_pt, jump_of_continuous hnhds (hF'_cts _ (mem_of_mem_nhds hnhds))]
      set c := J.a
      set d := J.b
      apply P.contains at hJ
      have hJ' : Icc a b ⊆ Ioo (a-1/2) (b+1/2) := by apply Set.Icc_subset_Ioo <;> linarith
      apply ((Ioo_subset J).trans hJ).trans at hJ'
      simp [subset_iff] at hJ'
      rw [Set.Ioo_subset_Ioo_iff hJab] at hJ'
      have hJ'' : Icc a b ⊆ Ioo (a-1) (b+1) := by apply Set.Icc_subset_Ioo <;> linarith
      apply hJ.trans at hJ''
      rw [α_length_of_cts _ (le_of_lt hJab) _ hJ'' hF'_cts] <;> try linarith
      have := HasDerivWithinAt.mean_value hJab (hF'_cts.mono ?_) ?_
      . choose e he hmean using this
        have : HasDerivWithinAt F' (f e) (.Ioo c d) e := by
          apply (Ioo_subset J).trans at hJ
          simp [subset_iff] at hJ
          apply ((hF.2 e (hJ he)).mono hJ).congr (f := F)
          all_goals grind
        replace := derivative_unique ?_ this hmean
        . have hdc : 0 < d - c := by linarith
          field_simp at this
          conv_rhs at this => unfold c d
          rw [← this]
          rw [show d - c = J.length by unfold length d c; simp; linarith]
          gcongr
          apply csInf_le
          . choose M hM using hf.1; use -M
            intro x hx; choose y hy hyfx using hx; subst hyfx
            specialize hM y (by apply hJ; exact hy); grind
          . simp; use e; simp; exact ((subset_iff _ _).mp (Ioo_subset J)) he
        . rw [←mem_closure_iff_clusterPt]
          apply closure_mono (s := .Ioo e d)
          . grind
          . simp at he; rw [closure_Ioo (by linarith)]; simp; linarith
      . simp; grind
      apply (Ioo_subset J).trans at hJ
      apply (hF.1.mono _).congr
      . intro x hx
        have : x ∈ Set.Icc a b := by specialize hJ _ hx; simpa using hJ
        grind
      simp; unfold c d; exact hJ
    replace hupper : upper_integral f (Icc a b) ≥ F b - F a := by
      rw [upper_integ_eq_inf_upper_sum hf.1]; apply le_csInf <;> simp [Set.range_nonempty]
      grind
    replace hlower : lower_integral f (Icc a b) ≤ F b - F a := by
      rw [lower_integ_eq_sup_lower_sum hf.1]; apply csSup_le <;> simp [Set.range_nonempty]
      grind
    linarith [hf.2]
  simp [h]; exact (integ_on_subsingleton (by simp [length])).2


open Real

noncomputable abbrev F_11_9 : ℝ → ℝ := fun x ↦ if x = 0 then 0 else x^2 * sin (1 / x^3)

lemma differentiable_of_F_11_9 : Differentiable ℝ F_11_9 := by
  intro x
  by_cases! h0 : x ≠ 0
  . unfold F_11_9
    have hsq : DifferentiableAt ℝ (fun (x:ℝ) => x^2) x := by fun_prop
    have hcu : DifferentiableAt ℝ (fun (x:ℝ) => x^3) x := by fun_prop
    have hsi : DifferentiableAt ℝ (fun (x:ℝ) => sin x) x := by fun_prop
    have := hsq.mul (hcu.inv (by grind)).sin; simp at this
    apply this.congr_of_eventuallyEq
    filter_upwards [compl_singleton_mem_nhds h0] with a ha
    simp at ha; simp [ha]
  subst h0
  suffices HasDerivAt F_11_9 0 0 by exact HasFDerivAt.differentiableAt this
  rw [hasDerivAt_iff_tendsto_slope]
  have heveq : Filter.EventuallyEq (nhdsWithin 0 {0}ᶜ) (slope F_11_9 0) (fun y ↦ y * Real.sin (1 / y ^ 3)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha; simp at ha
    unfold F_11_9
    simp [slope_def_field, ha]
    field_simp
  have htt : Filter.Tendsto (fun y ↦ y * sin (1 / y ^ 3)) (nhds 0) (nhds 0) := by
    apply squeeze_zero_norm (t₀:=nhds 0) (a:=fun y => |y|)
    . intro x
      rw [norm_eq_abs, abs_mul]
      suffices |sin (1 / x ^ 3)| ≤ 1 by nlinarith [abs_nonneg x]
      apply abs_sin_le_one
    . exact Continuous.tendsto' (by fun_prop) 0 0 (by simp)
  replace htt : Filter.Tendsto (fun y ↦ y * sin (1 / y ^ 3)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    apply htt.mono_left
    exact nhdsWithin_le_nhds
  apply htt.congr'
  exact heveq.symm

example : Differentiable ℝ F_11_9 := by
  exact differentiable_of_F_11_9

example : ¬ BddOn (deriv F_11_9) (.Icc (-1) 1) := by
  intro hbd
  have hderiv {x :ℝ} (h : x ≠ 0) : HasDerivAt F_11_9 ((2 * x) * sin ((x^3)⁻¹) + x^2 * (cos ((x^3)⁻¹) * (-(3*x^2) / (x^3)^2))) x := by
    have hcube := hasDerivAt_pow 3 x; simp at hcube
    have hsq := hasDerivAt_pow 2 x; simp at hsq
    have hinv := hcube.inv (by grind); simp at hinv
    have hsin := hinv.sin
    have hmul := hsq.mul hsin
    apply hmul.congr_of_eventuallyEq
    filter_upwards [compl_singleton_mem_nhds h] with a ha; simp at ha
    unfold F_11_9; simp [ha]
  choose B hB using hbd
  choose N hN using exists_nat_gt ((max 1 ((B/3)^((3:ℝ)/2)))/(2*π))
  field_simp at hN
  set a : ℝ := 2 * π * N with ha_def
  have ha1 : 1 < a := by grind
  have ha  : 0 < a := by linarith
  have hBnonneg : 0 ≤ B := by
    specialize hB 1 (by simp)
    have : 0 ≤ |deriv F_11_9 1| := by apply abs_nonneg
    linarith
  set x : ℝ := a ^ (-(1:ℝ)/3) with hx_def
  have hxpos : 0 < x := by positivity
  have hsqpos : 0 ≤ x^2 := by positivity
  have hxne :  x ≠ 0 := by linarith
  have hxle1 : x ≤ 1 := by
    unfold x
    apply rpow_le_one_of_one_le_of_nonpos
    . linarith
    . norm_num
  have hx3 : x ^ 3 = a⁻¹ := by
    unfold x
    rw [← Real.rpow_natCast, ← rpow_mul (by linarith)]
    simp
    exact rpow_neg_one a
  have hinv3 : (x ^ 3)⁻¹ = a := by
    rw [hx3]
    apply inv_inv
  have hsin : sin (x ^ 3)⁻¹ = 0 := by
    rw [hinv3]; unfold a
    refine sin_eq_zero_iff.mpr ?_
    use 2 * N; push_cast; ring
  have hcos : cos (x ^ 3)⁻¹ = 1 := by
    rw [hinv3]; unfold a
    refine (cos_eq_one_iff _).mpr ?_
    use N; push_cast; ring
  have hderiveq : deriv F_11_9 x = -3 / x^2 := by
    rw [(hderiv hxne).deriv, hsin, hcos]
    field_simp
    simp
  specialize hB x (by constructor <;> linarith)
  rw [hderiveq] at hB
  rw [abs_of_neg (by field_simp; simp), neg_div, neg_neg] at hB
  have hxinv' : (x^2)⁻¹ = a^((2:ℝ)/3) := by
    unfold x
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    simp
    rw [show -(1:ℝ) / 3 * 2 = - 2 / 3 by field_simp]
    field_simp
    rw [← Real.rpow_add]; simp; linarith
  have hgt : B < 3 / x^2 := by
    have hmono : B/3 < a ^ ((2:ℝ)/3) := by
      have hpow : ((B/3) ^ ((3:ℝ)/2)) ^ ((2:ℝ)/3) = B/3 := by
        rw [← Real.rpow_mul (by positivity)]; norm_num
      rw [← hpow]
      apply Real.rpow_lt_rpow (y:=a) (z:=((2:ℝ)/3))
      . positivity
      . grind
      . norm_num
    field_simp at hmono hxinv' ⊢
    nlinarith
  linarith


example : AntiderivOn F_11_9 (deriv F_11_9) (Icc (-1) 1) := by
  refine ⟨differentiable_of_F_11_9.differentiableOn, ?_⟩
  intro x hx
  exact (differentiable_of_F_11_9 x).hasDerivAt.hasDerivWithinAt


/-- Lemma 11.9.5 / Exercise 11.9.2 -/
theorem antideriv_eq_antideriv_add_const {I:BoundedInterval} {f F G : ℝ → ℝ}
  (hfF: AntiderivOn F f I) (hfG: AntiderivOn G f I) :
   ∃ C, ∀ x ∈ (I:Set ℝ), F x = G x + C := by
  have ⟨hF, hFanti⟩ := hfF
  have ⟨hG, hGanti⟩ := hfG
  by_cases h : Subsingleton (I:Set ℝ)
  . -- handle the trivial cases first, so we can apply Tao's statement of MVT to
    -- a non-empty interval.
    simp at h
    rcases Set.Subsingleton.eq_empty_or_singleton h with hempty | hsingleton
    . use 1234091019283749234; intro x hx; rw [hempty] at hx; simp at hx
    . choose p hp using hsingleton
      use F p - G p
      rw [hp]
      intro x hx; simp at hx; subst hx
      simp
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have key {x y :ℝ} (hxI : x ∈ I) (hyI : y ∈ I) : (F - G) x = (F - G) y := by
    wlog hxy : x < y generalizing x y
    . push_neg at hxy
      rcases hxy.eq_or_lt with rfl | hlt
      . rfl
      exact (this (x:=y) (y:=x) hyI hxI hlt).symm
    have hdiff := hF.sub hG
    have hcont := hdiff.continuousOn
    rw [BoundedInterval.mem_iff] at hxI hyI
    have hIoo : Set.Ioo x y ⊆ I := by
      match I with
      | Ioo a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Ico a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Ioc a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Icc a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
    have hIcc : Set.Icc x y ⊆ I := by
      match I with
      | Ioo a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Ico a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Ioc a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
      | Icc a b =>
        intro p hp
        simp at hp hxI hyI ⊢
        constructor <;> linarith
    have hdiff' : DifferentiableOn ℝ (F - G) (Set.Ioo x y) := by
      apply hdiff.mono
      exact hIoo
    have hcont' : ContinuousOn (F - G) (Set.Icc x y) := by
      apply hcont.mono
      exact hIcc
    choose k hkmem hkderiv using
      _root_.HasDerivWithinAt.mean_value
        (a:=x) (b:=y) (by linarith)
        (f:=F-G) (hcont:=hcont') (hderiv:=hdiff')
    rw [← slope_def_field] at hkderiv
    have hkI : k ∈ I := by
      apply hIoo
      simp at hkmem ⊢
      constructor <;> linarith
    specialize hFanti k hkI
    specialize hGanti k hkI
    have hsub := hFanti.sub hGanti; simp at hsub
    have hsub' : HasDerivWithinAt (F - G) 0 (Set.Ioo x y) k := by
      apply hsub.mono
      exact hIoo
    have heq := UniqueDiffWithinAt.eq_deriv (h:=hsub') (h₁:=hkderiv) (H:=by exact uniqueDiffWithinAt_Ioo hkmem)
    rw [slope_def_field] at heq
    have hxypos : y - x > 0 := by linarith
    field_simp at heq; simp at heq
    simp; linarith
  choose p hp1 hp2 using exists_between h
  have hpI : p ∈ I := by
    apply I.Ioo_subset
    constructor <;> linarith
  have hconst : ∀ x ∈ I, (F - G) x = (F - G) p := by
    intro x hxI
    exact key hxI hpI
  simp at hconst
  use F p - G p
  intro x hx
  specialize hconst x hx
  linarith




/-- Exercise 11.9.3 -/
example {a b x₀:ℝ} (hab: a < b) (hx₀: x₀ ∈ Ioo a b) {f: ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  DifferentiableWithinAt ℝ (fun x => integ f (Icc a x)) (Icc a b) x₀ ↔
  ContinuousWithinAt f (Icc a b) x₀ := by
  have hint : IntegrableOn f (Icc a b) := by
      exact integ_of_monotone hf
  refine ⟨?_, ?_⟩; swap
  . intro hcont
    have hx₀' : x₀ ∈ Icc a b := by
      simp [BoundedInterval.mem_iff] at hx₀ ⊢
      constructor <;> linarith
    have := deriv_of_integ (hab:=hab) (hf:=hint) (hcts:=hcont) (hx₀:=hx₀')
    exact DifferentiableWithinAt.of_hasDeriv this
  -- we first have to extend MonotoneOn the interval to Monotone on the entire line,
  -- so we can apply the theorems elsewhere in the text.
  set f' := fun x => if x < a then f a else if b < x then f b else f x
  have hf' : Monotone f' := by
    intro x y hxy; unfold f'
    split_ifs <;> try linarith
    all_goals
    . apply hf <;> try simp_all; try linarith
  have heqon : Set.EqOn f f' (Icc a b) := by
    intro x hx
    simp at hx
    unfold f'
    rw [if_neg (by linarith), if_neg (by linarith)]
  have hright : right_lim f x₀ = right_lim f' x₀ := by
    unfold right_lim
    have hev : f =ᶠ[nhdsWithin x₀ (Set.Ioi x₀)] f' := by
      rw [BoundedInterval.mem_iff] at hx₀; simp at hx₀
      filter_upwards [Ioo_mem_nhdsGT hx₀.2] with p hp; simp at hp
      unfold f'
      rw [if_neg (by linarith), if_neg (by linarith)]
    rw [Filter.map_congr hev]
  have hleft : left_lim f x₀ = left_lim f' x₀ := by
    unfold left_lim
    have hev : f =ᶠ[nhdsWithin x₀ (Set.Iio x₀)] f' := by
      rw [BoundedInterval.mem_iff] at hx₀; simp at hx₀
      filter_upwards [Ioo_mem_nhdsLT hx₀.1] with p hp; simp at hp
      unfold f'
      rw [if_neg (by linarith), if_neg (by linarith)]
    rw [Filter.map_congr hev]
  have hright' : right_lim f' x₀ = Function.rightLim f' x₀ := by
    have htends := right_lim_of_monotone x₀ hf'
    rw [Convergesto.iff] at htends
    rw [right_lim_of_monotone' x₀ hf']
    symm
    exact rightLim_eq_of_tendsto (Filter.NeBot.ne') htends
  have hleft' : left_lim f' x₀ = Function.leftLim f' x₀ := by
    have htends := left_lim_of_monotone x₀ hf'
    rw [Convergesto.iff] at htends
    rw [left_lim_of_monotone' x₀ hf']
    symm
    exact leftLim_eq_of_tendsto (Filter.NeBot.ne') htends
  intro hdiff
  by_contra! hcont
  have hlim : left_lim f x₀ < right_lim f x₀ := by
    by_contra! h'
    rcases h'.eq_or_lt with heq | hlt
    . -- then f isn't discontinuous
      rw [hleft, hright, hleft', hright'] at heq
      have hcont' : ContinuousAt f' x₀ := by
        apply hf'.continuousAt_iff_leftLim_eq_rightLim.mpr
        exact heq.symm
      apply hcont
      apply hcont'.continuousWithinAt.congr
      . apply heqon
      . apply heqon
        rw [BoundedInterval.mem_iff] at hx₀
        simp at hx₀ ⊢
        constructor <;> linarith
    . contrapose! hlt
      rw [hleft, hright]
      have := jump_of_monotone x₀ hf'
      unfold jump at this
      linarith
  have hderiv := hdiff.hasDerivWithinAt
  have hderivslope := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  simp at hderivslope
  set D := derivWithin (fun x ↦ integ f (Icc a x)) (Icc a b) x₀
  have hx₀' := (BoundedInterval.mem_iff _ _).mp hx₀; simp at hx₀'
  obtain ⟨hax₀, hx₀b⟩ := hx₀'
  have hIoc {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) : IntegrableOn f (Ioc u v) := by
    apply hint.mono'
    rw [BoundedInterval.subset_iff]; simp
    intro x hx; simp at hx ⊢; constructor <;> linarith
  have hIoo {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) : IntegrableOn f (Ioo u v) := by
    apply hint.mono'
    rw [BoundedInterval.subset_iff]; simp
    intro x hx; simp at hx ⊢; constructor <;> linarith
  have hadd {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) (huv : u ≤ v) : integ f (Icc a v) - integ f (Icc a u) = integ f (Ioc u v) := by
    have hjoin := BoundedInterval.join_Icc_Ioc hu huv
    have hintav : IntegrableOn f (Icc a v) := by
      apply hint.mono'
      rw [BoundedInterval.subset_iff]; simp
      intro x hx; simp at hx ⊢; constructor <;> linarith
    obtain ⟨_, _, heq⟩ := hintav.join hjoin
    linarith
  have hfr {z : ℝ} (hz : x₀ < z) (hzb : z ≤ b) : right_lim f x₀ ≤ f z := by
    rw [hright, hright']
    rw [show f z = f' z by apply heqon; simp; constructor <;> linarith]
    apply hf'.rightLim_le
    exact hz
  have hfl {z : ℝ} (haz : a ≤ z) (hz : z < x₀) : f z ≤ left_lim f x₀ := by
    rw [hleft, hleft']
    rw [show f z = f' z by apply heqon; simp; constructor <;> linarith]
    apply hf'.le_leftLim
    exact hz
  have hsloper {z : ℝ} (hz : x₀ < z) (hzb : z ≤ b) : right_lim f x₀ ≤ slope (fun p => integ f (Icc a p)) x₀ z := by
    observe : z - x₀ > 0
    have hmaj : MajorizesOn f (fun _ => right_lim f x₀) (Ioc x₀ z) := by
      intro ℓ hℓ; simp at hℓ ⊢
      apply hfr; all_goals linarith
    have hle : integ (fun x ↦ right_lim f x₀) (Ioc x₀ z) ≤ integ f (Ioc x₀ z) := by
      apply IntegrableOn.mono
      . exact (IntegrableOn.const _ _).1
      . exact hIoc (u:=x₀) (v:=z) (by linarith) (by linarith)
      . exact hmaj
    rw [
      (IntegrableOn.const (right_lim f x₀) (Ioc x₀ z)).2,
      show (Ioc x₀ z).length = z - x₀ by unfold length; simp [BoundedInterval.a, BoundedInterval.b]; linarith,
      ← hadd (by linarith) (by linarith) (by linarith)
    ] at hle
    rw [slope_def_field]
    field_simp; exact hle
  have hslopel {z : ℝ} (haz : a ≤ z) (hz : z < x₀) : slope (fun p => integ f (Icc a p)) x₀ z ≤ left_lim f x₀ := by
    observe : x₀ - z > 0
    have hmaj : MajorizesOn (fun _ => left_lim f x₀) f (Ioo z x₀) := by
      intro ℓ hℓ; simp at hℓ ⊢
      apply hfl; all_goals linarith
    have hle : integ f (Ioo z x₀) ≤ integ (fun x ↦ left_lim f x₀) (Ioo z x₀) := by
      apply IntegrableOn.mono
      . exact hIoo (u:=z) (v:=x₀) (by linarith) (by linarith)
      . exact (IntegrableOn.const _ _).1
      . exact hmaj
    have heq : integ f (Ioo z x₀) = integ f (Ioc z x₀) := by
      apply IntegrableOn.eq
      . rw [BoundedInterval.subset_iff]; simp; intro q hq; simp at hq ⊢; constructor <;> linarith
      . simp_all
      . simp_all
      . exact hIoc (u:=z) (v:=x₀) (by linarith) (by linarith)
    rw [
      heq,
      (IntegrableOn.const (left_lim f x₀) (Ioo z x₀)).2,
      show (Ioo z x₀).length = x₀ - z by unfold length; simp [BoundedInterval.a, BoundedInterval.b]; linarith,
      ← hadd (by linarith) (by linarith) (by linarith)
    ] at hle
    rw [slope_def_field]
    field_simp
    rw [show z - x₀ = -1 * (x₀ - z) by linarith]
    field_simp
    conv_lhs => simp
    conv_rhs => rw [mul_comm]
    exact hle
  have hDR : right_lim f x₀ ≤ D := by
    have hmem : (Set.Icc a b \ {x₀}) ∈ (nhdsWithin x₀ (Set.Ioi x₀)) := by
      apply mem_nhdsWithin.mpr; use Set.Iio b; refine ⟨isOpen_Iio, hx₀b, ?_⟩
      intro x hx
      simp at hx ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩; all_goals linarith
    apply ge_of_tendsto (hderivslope.mono_left (nhdsWithin_le_iff.mpr hmem))
    filter_upwards [Ioo_mem_nhdsGT hx₀b] with p hp; simp at hp
    exact hsloper hp.1 (by linarith)
  have hDl : D ≤ left_lim f x₀ := by
    have hmem : (Set.Icc a b \ {x₀}) ∈ (nhdsWithin x₀ (Set.Iio x₀)) := by
      apply mem_nhdsWithin.mpr; use Set.Ioi a; refine ⟨isOpen_Ioi, hax₀, ?_⟩
      intro x hx
      simp at hx ⊢
      refine ⟨⟨?_, ?_⟩, ?_⟩; all_goals linarith
    apply le_of_tendsto (hderivslope.mono_left (nhdsWithin_le_iff.mpr hmem))
    filter_upwards [Ioo_mem_nhdsLT hax₀] with p hp; simp at hp
    exact hslopel (by linarith) hp.2
  linarith


end Chapter11

#check Chapter11.summable_iff_integ_of_antitone

theorem Chapter7.Series.qseries_partial (p : ℝ) (N : ℕ) :
  (mk' (m := 1) (fun n ↦ 1 / (n:ℝ) ^ p) : Series).partial (N : ℤ)
      = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ p := by
  simp only [Series.partial]
  set e : ℕ ↪ ℤ := ⟨fun n ↦ (n : ℤ) + 1, fun a b h ↦ by simpa using h⟩ with he
  have hset : Finset.Icc (1:ℤ) N = (Finset.range N).map e := by
    ext x
    simp; constructor
    . intro ⟨h1, h2⟩
      use (x-1).toNat; refine ⟨by omega, ?_⟩
      unfold e; simp; grind
    . intro h; choose n h1 h2 using h
      unfold e at h2; simp at h2
      constructor <;> omega
  rw [hset, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  simp; rw [if_pos (by unfold e; simp)]
  unfold e; simp

theorem tendsto_int_iff_nat (a : ℤ → ℝ) (L : ℝ) :
    Filter.atTop.Tendsto a (nhds L) ↔ Filter.atTop.Tendsto (fun n : ℕ ↦ a n) (nhds L) := by
  convert Filter.tendsto_map'_iff (g := fun n:ℕ => (n:ℤ))
  symm
  exact Nat.map_cast_int_atTop

theorem Chapter7.Series.qseries_convergesTo_iff_hasSum (p : ℝ) (L : ℝ) :
    (mk' (m := 1) (fun n ↦ 1 / (n:ℝ) ^ p) : Series).convergesTo L
      ↔ HasSum (fun n : ℕ ↦ 1 / ((n:ℝ) + 1) ^ p) L := by
  have hg0 : ∀ n : ℕ, 0 ≤ 1 / ((n:ℝ) + 1) ^ p := by
    intro n
    positivity
  conv_rhs =>
    rw [hasSum_iff_tendsto_nat_of_nonneg hg0]
  conv_lhs =>
    unfold Series.convergesTo
    rw [tendsto_int_iff_nat]
  apply Filter.tendsto_congr
  intro n
  exact Chapter7.Series.qseries_partial p n

theorem Chapter7.Series.qseries_converges_iff_summable (p : ℝ) :
    (mk' (m := 1) (fun n ↦ 1 / (n:ℝ) ^ p) : Series).converges
      ↔ Summable (fun n : ℕ ↦ 1 / ((n:ℝ) + 1) ^ p) := by
  apply exists_congr
  intro L
  exact qseries_convergesTo_iff_hasSum p L


/-- Exercise 11.6.5, moved to Section 11.9 -/
theorem Chapter7.Series.converges_qseries' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).converges ↔ (p>1) := by
  by_cases! hp : p ≤ 0
  . -- first prove that p has to be greater than zero, otherwise there's nothing to prove
    constructor
    . intro hconv; exfalso
      have hdecay := Series.decay_of_converges hconv
      choose N hN using Metric.tendsto_atTop.mp hdecay 1 (by positivity)
      simp at hN
      specialize hN (max 1 N) (by simp)
      rw [if_pos (by simp), abs_of_pos (by positivity)] at hN
      field_simp at hN
      have h1 : (1:ℝ) ≤ max 1 N := by simp
      set d := max 1 N
      have := Real.rpow_le_one_of_one_le_of_nonpos h1 hp
      linarith
    . intro hp1; exfalso; linarith
  . rw [Chapter7.Series.qseries_converges_iff_summable]
    set f : ℝ → ℝ := fun x => 1 / (x+1)^p
    have hnon : ∀ x ≥ 0, f x ≥ 0 := by
      intro x hx
      unfold f; simp; positivity
    have hanti : AntitoneOn f (Set.Ici 0) := by
      intro x hx y hy hxy
      unfold f
      apply one_div_le_one_div_of_le
      . simp at hx
        positivity
      . gcongr
        simp at hx; linarith
    -- apply integral test
    rw [Chapter11.summable_iff_integ_of_antitone hnon hanti]
    have heval : p ≠ 1 → ∀ N ≥ (0:ℝ), Chapter11.integ f (Chapter11.BoundedInterval.Icc 0 N) = ((N + 1) ^ (1 - p) - 1) / (1 - p) := by
      intro hp1 N hN
      set F : ℝ → ℝ := fun x ↦ (x + 1) ^ (1 - p) / (1 - p)
      have hderiv : ∀ x ∈ Set.Icc (0:ℝ) N, HasDerivWithinAt F (f x) (Set.Icc 0 N) x := by
        intro x hx
        have h1  : HasDerivAt (fun x:ℝ ↦ x + 1) 1 x := by
          apply (hasDerivAt_id x).add_const
        have h2 := (h1.rpow_const (p:=(1-p)) (by left; grind)).div_const (1-p)
        convert h2.hasDerivWithinAt using 1
        unfold f
        observe : 1 - p ≠ 0
        field_simp
        ring_nf
        rw [Real.rpow_neg]
        simp at hx; linarith
      have hint : Chapter11.IntegrableOn f (Chapter11.BoundedInterval.Icc 0 N) := by
        apply Chapter11.integ_of_antitone
        intro x hx y hy hxy; simp at hx hy
        apply hanti
        . simp at hx ⊢; linarith
        . simp at hy ⊢; linarith
        . exact hxy
      have hantideriv : Chapter11.AntiderivOn F f (Chapter11.BoundedInterval.Icc 0 N) := by
        constructor
        . intro x hx
          specialize hderiv x hx
          exact DifferentiableWithinAt.of_hasDeriv hderiv
        . intro x hx
          exact hderiv x hx
      rw [Chapter11.integ_eq_antideriv_sub hN hint hantideriv]
      unfold F
      observe : 1 - p ≠ 0
      field_simp
      simp
    constructor
    . intro h
      choose M hM using h
      by_contra! h
      rcases h.eq_or_lt with heq | hlt
      . subst heq
        -- heval becomes useless here, so let's get rid of it
        clear heval h
        have heval' : ∀ N ≥ 0, Chapter11.integ f (Chapter11.BoundedInterval.Icc 0 N) = Real.log (N + 1) := by
          intro N hN
          set F : ℝ → ℝ := fun x => Real.log (x + 1)
          have hderiv : ∀ x ∈ Set.Icc (0:ℝ) N, HasDerivWithinAt F (f x) (Set.Icc 0 N) x := by
            intro x hx
            have h1 : HasDerivAt (fun x:ℝ ↦ x + 1) 1 x := (hasDerivAt_id x).add_const 1
            have h2 : HasDerivAt F (1 / (x + 1)) x := by
              simpa using h1.log (by grind)
            convert h2.hasDerivWithinAt using 1
            unfold f
            simp
          have hint : Chapter11.IntegrableOn f (Chapter11.BoundedInterval.Icc 0 N) := by
            apply Chapter11.integ_of_antitone
            intro x hx y hy hxy
            apply hanti
            . simp at hx ⊢; linarith
            . simp at hy ⊢; linarith
            . exact hxy
          have hantideriv : Chapter11.AntiderivOn F f (Chapter11.BoundedInterval.Icc 0 N) := by
            constructor
            . intro x hx
              specialize hderiv x hx
              exact DifferentiableWithinAt.of_hasDeriv hderiv
            . intro x hx
              exact hderiv x hx
          rw [Chapter11.integ_eq_antideriv_sub hN hint hantideriv]
          unfold F; simp
        have htend : Filter.Tendsto (fun N:ℝ => Chapter11.integ f (Chapter11.BoundedInterval.Icc 0 N)) Filter.atTop Filter.atTop := by
          refine (Real.tendsto_log_atTop.comp (Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id)).congr' ?_
          filter_upwards [Filter.eventually_ge_atTop 0] with n hn
          simp; rw [heval' n hn]
        have := htend.eventually_gt_atTop M; rw [Filter.eventually_atTop] at this
        choose a ha using this
        choose a' ha' using exists_nat_gt a
        specialize ha a' (by linarith)
        specialize hM a' (by linarith)
        linarith
      . have htend : Filter.Tendsto (fun N:ℝ => Chapter11.integ f (Chapter11.BoundedInterval.Icc 0 N)) Filter.atTop Filter.atTop := by
          have hcf : Filter.Tendsto (fun N:ℝ => ((N + 1) ^ (1 - p) + (-1)) / (1 - p)) Filter.atTop Filter.atTop := by
            apply Filter.Tendsto.atTop_div_const (by linarith)
            apply Filter.tendsto_atTop_add_const_right
            apply (tendsto_rpow_atTop (y:=1-p) (by linarith)).comp
            apply Filter.tendsto_atTop_add_const_right
            exact Filter.tendsto_id
          apply hcf.congr'
          filter_upwards [Filter.eventually_ge_atTop 0] with n hn
          rw [heval (by linarith) (N:=n) (by linarith)]
          observe : 1 - p > 0
          field_simp
          linarith
        have := htend.eventually_gt_atTop M; rw [Filter.eventually_atTop] at this
        choose a ha using this
        choose a' ha' using exists_nat_gt a
        specialize ha a' (by linarith)
        specialize hM a' (by linarith)
        linarith
    . intro hp1
      observe : p ≠ 1
      use 1 / (p-1)
      intro N hN
      rw [heval (by linarith) N hN]
      rw [show 1 - p = -1 * (p - 1) by linarith]
      observe : p - 1 > 0
      field_simp
      simp
      positivity


theorem Chapter7.Series.converges_qseries'' (p:ℝ) : (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ p : Series).absConverges ↔ (p>1) := by
  have hpartial : (mk' (m := 1) fun n => 1/(n:ℝ)^p).abs.partial = (mk' (m := 1) fun n => 1/(n:ℝ)^p).partial := by
    ext N
    unfold Series.partial
    simp; apply Finset.sum_congr rfl
    intro x hx; simp at hx
    rw [if_pos hx.1, if_pos hx.1]
    simp; refine Real.rpow_nonneg ?_ p
    rify at hx; linarith
  have hiff : (mk' (m := 1) fun n => 1/(n:ℝ)^p).absConverges ↔ (mk' (m := 1) fun n => 1/(n:ℝ)^p).converges := by
    unfold Series.absConverges Series.converges Series.convergesTo
    rw [hpartial]
  rw [hiff]
  exact converges_qseries' p
