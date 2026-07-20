import Mathlib.Tactic
import Analysis.Section_9_9
import Analysis.Section_11_4

/-!
# Analysis I, Section 11.5: Riemann integrability of continuous functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of uniformly continuous functions.
- Riemann integrability of bounded continuous functions.

-/

namespace Chapter11
open BoundedInterval
open Chapter9

lemma BoundedInterval.exists_join_of_btwn {c : ℝ} {I : BoundedInterval} (ha : I.a < c) (hb : c < I.b) :
  ∃ L R : BoundedInterval, I.joins L R ∧ L.a = I.a ∧ L.b = c ∧ R.a = c ∧ R.b = I.b := by
  match I with
  | Ioo x y =>
    use Ioc x c, Ioo c y; simp_all
    change x < c at ha
    exact join_Ioc_Ioo (by linarith) hb
  | Ico x y =>
    use Icc x c, Ioo c y; simp_all
    change x < c at ha
    exact join_Icc_Ioo (by linarith) hb
  | Ioc x y =>
    use Ioc x c, Ioc c y; simp_all
    change x < c at ha
    change c < y at hb
    exact join_Ioc_Ioc (by linarith) (by linarith)
  | Icc x y =>
    use Icc x c, Ioc c y; simp_all
    change x < c at ha
    change c < y at hb
    exact join_Icc_Ioc (by linarith) (by linarith)

lemma BoundedInterval.exists_evenly_spaced_split {N : ℕ} {I : BoundedInterval} (hN : 1 ≤ N) (h : I.a < I.b) :
  ∃ P : Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = |I|ₗ / (N:ℝ) := by
  induction N, hN using Nat.le_induction generalizing I with
  | base =>
    use ⊥; constructor
    . simp
    . rw [BoundedInterval.intervals_of_bot]
      intro J hJ; simp at hJ
      field_simp; rw [hJ]
      grind
  | succ n hn ih =>
    set Δ : ℝ := |I|ₗ / ((n:ℝ)+1)
    set c : ℝ := I.a + Δ
    have ha : I.a < c := by
      suffices 0 < Δ by linarith
      unfold Δ
      field_simp; simp; exact h
    have hb: c < I.b := by
      unfold c
      suffices Δ < I.b - I.a by linarith
      unfold Δ
      field_simp
      rw [show I.length = I.b - I.a by grind]
      conv_lhs => rw [show I.b - I.a = (1:ℝ) * (I.b - I.a) by simp]
      gcongr
      . linarith
      . rify at hn; linarith
    choose L R hILR h1 h2 h3 h4 using BoundedInterval.exists_join_of_btwn ha hb
    have hR : R.a < R.b := by
      rw [h3, h4]; exact hb
    choose P hPcard hPintervallength using ih hR
    have hRlen : R.length = n * (I.length / (n+1)) := by
      conv_lhs => unfold length
      rw [max_eq_left (by linarith)]
      rw [h3, h4]
      unfold c Δ
      conv_lhs =>
        rw [sub_eq_add_neg, neg_add, ← add_assoc, ← sub_eq_add_neg, ← sub_eq_add_neg]
        rw [show I.b - I.a = I.length by simp; linarith]
      field_simp; simp
    rw [hRlen] at hPintervallength
    rw [show (n:ℝ) * (I.length / ((n:ℝ) + 1)) / (n:ℝ) = (I.length / ((n:ℝ) + 1)) by field_simp] at hPintervallength
    set Q : Partition I := {
      intervals := insert L P.intervals
      exists_unique := by
        intro x hx; rw [BoundedInterval.mem_iff] at hx
        obtain ⟨hdisj, hunion, hlen⟩ := hILR
        rw [hunion] at hx
        rcases hx with hL | hR
        . use L; simp; constructor
          . exact hL
          . intro L' hL' hxL'
            contrapose! hdisj
            use x; constructor
            . exact hL
            . apply P.contains L' hL'
              exact hxL'
        . choose J hJ hJuniq using P.exists_unique x hR
          simp at hJ hJuniq
          use J; simp; constructor
          . exact ⟨by right; exact hJ.1, hJ.2⟩
          . constructor
            . intro hxL
              contrapose! hdisj
              use x; exact ⟨hxL, hR⟩
            . exact hJuniq
      contains := by
        intro J hJ; simp at hJ
        obtain ⟨hdisj, hunion, hlen⟩ := hILR
        rcases hJ with hL | hR
        . rw [hL, BoundedInterval.subset_iff, hunion]
          simp
        . rw [BoundedInterval.subset_iff, hunion]
          have hJR := (P.contains J hR)
          rw [BoundedInterval.subset_iff] at hJR
          exact Set.subset_union_of_subset_right hJR _
    }
    use Q; constructor
    . change (insert L P.intervals).card = n + 1
      rw [Finset.card_insert_of_notMem ?_]
      . rw [hPcard]
      . obtain ⟨hdisj, hunion, hlen⟩ := hILR
        intro h'
        have hLR := P.contains L h'
        rw [BoundedInterval.subset_iff] at hLR
        have := Set.inter_eq_left.mpr hLR
        rw [this] at hdisj
        contrapose! hdisj
        have hsub := BoundedInterval.Ioo_subset L
        rw [BoundedInterval.subset_iff] at hsub
        simp at hsub
        refine (Set.nonempty_Ioo.mpr ?_).mono hsub
        linarith
    . intro J hJ
      change J ∈ insert L P.intervals at hJ
      simp at hJ
      rcases hJ with hL | hR
      . subst hL
        unfold length
        rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        rw [h1, h2]
        unfold c
        simp; unfold Δ
        field_simp
        rw [show I.length = I.b - I.a by simp; linarith]
      . have :=  hPintervallength J hR
        field_simp at this ⊢
        simpa using this



/-- Theorem 11.5.1 -/
theorem integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I) :
  IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨ hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1.2
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ ε * (b-a) := by
    rw [UniformContinuousOn.iff] at hf
    choose δ hδ hf using hf ε hε; simp [Real.Close, Real.dist_eq] at hf
    choose N hN using exists_nat_gt ((b-a)/δ)
    have hNpos : 0 < N := by
      have : 0 < (b-a)/δ := by positivity
      rify; order
    have hN' : (b-a)/N < δ := by rwa [div_lt_comm₀] <;> positivity
    have : ∃ P: Partition I, P.intervals.card = N ∧ ∀ J ∈ P.intervals, |J|ₗ = (b-a) / N := by
      choose P hPcard hPlen using BoundedInterval.exists_evenly_spaced_split (N:=N) (I:=I) (by omega) (by linarith)
      use P; constructor
      . exact hPcard
      . intro J hJ; specialize hPlen J hJ
        rw [hPlen]; field_simp
        unfold length
        rw [max_eq_left (by linarith)]
    choose P hcard hlength using this
    calc
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * |J|ₗ := by
        have h1 := upper_integ_le_upper_sum hfbound P
        have h2 := lower_integ_ge_lower_sum hfbound P
        simp [sub_mul, upper_riemann_sum, lower_riemann_sum] at *
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε * |J|ₗ := by
        apply Finset.sum_le_sum; intro J hJ; gcongr
        have {x y:ℝ} (hx: x ∈ J) (hy: y ∈ J) : f x ≤ f y + ε := by
          have : J ⊆ I := P.contains _ hJ
          have : |f x - f y| ≤ ε := by
            apply hf y _ x _ _ <;> try solve_by_elim
            apply (BoundedInterval.dist_le_length hx hy).trans; grind
          grind [abs_le']
        have hJnon : (f '' J).Nonempty := by
          simp; by_contra! h
          replace h : Subsingleton (J:Set ℝ) := by simp [h]
          simp only [length_of_subsingleton, hlength J hJ] at h
          linarith [show 0 < (b-a) / N by positivity]
        replace (y:ℝ) (hy:y ∈ J) : sSup (f '' J) ≤ f y + ε := by
          apply csSup_le hJnon; rintro _ ⟨z, hz, rfl⟩; exact this hz hy
        replace : sSup (f '' J) - ε ≤ sInf (f '' J) := by
          apply le_csInf hJnon; grind [mem_iff]
        linarith
      _ = ∑ J ∈ P.intervals, ε * (b-a)/N := by grind [Finset.sum_congr]
      _ = _ := by simp [hcard]; field_simp
  have lower_le_upper : 0 ≤ upper_integral f I - lower_integral f I := by linarith [lower_integral_le_upper hfbound]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  . set ε := (upper_integral f I - lower_integral f I)/(2*(b-a))
    replace : upper_integral f I - lower_integral f I ≤ (upper_integral f I - lower_integral f I)/2 := by
      convert this ε (by positivity) using 1; grind
    linarith
  linarith

/-- Corollary 11.5.2 -/
theorem integ_of_cts {a b:ℝ} {f:ℝ → ℝ} (hf: ContinuousOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := integ_of_uniform_cts (UniformContinuousOn.of_continuousOn hf)

example : ContinuousOn (fun x:ℝ ↦ 1/x) (Ioc 0 1) := by
  simp only [set_Ioc]
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx
  simp at hx ⊢
  linarith


example : ¬ IntegrableOn (fun x:ℝ ↦ 1/x) (Icc 0 1) := by
  intro ⟨hbdd, _⟩
  choose B hB using hbdd
  simp at hB
  by_cases! h : B ≤ 0
  . specialize hB (1/2) (by norm_num) (by norm_num)
    simp at hB
    linarith
  . by_cases! h' : 1 ≤ B
    . specialize hB ((B+1)⁻¹) (by positivity) (by field_simp; linarith)
      simp at hB
      rw [abs_of_pos (by linarith)] at hB
      linarith
    . specialize hB (B / 2) (by linarith) (by linarith)
      rw [abs_of_nonneg (by linarith)] at hB
      field_simp at hB
      nlinarith

open PiecewiseConstantOn ConstantOn in
set_option maxHeartbeats 300000 in
/-- Proposition 11.5.3-/
theorem integ_of_bdd_cts {I: BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: ContinuousOn f I) : IntegrableOn f I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hsing : |I|ₗ = 0
  . exact (integ_on_subsingleton hsing).1
  have hI : (I:Set ℝ).Nonempty := by by_contra!; rw [←BoundedInterval.length_of_subsingleton] at hsing; simp_all
  simp at hsing
  set a := I.a
  set b := I.b
  have lower_le_upper := lower_integral_le_upper hbound
  have ⟨ M, hM ⟩ := hbound
  have hMpos : 0 ≤ M := (abs_nonneg _).trans (hM hI.some hI.some_mem)
  have (ε:ℝ) (hε: ε > 0) : upper_integral f I - lower_integral f I ≤ (4*M+2) * ε := by
    wlog hε' : ε < (b-a)/2
    . specialize this _ _ _ _ _ _ hM _ ((b-a)/3) _ _
        <;> first | assumption | linarith | apply this.trans; gcongr; linarith
    set I' := Icc (a+ε) (b-ε)
    set Ileft : BoundedInterval := match I with
    | Icc _ _ => Ico a (a + ε)
    | Ico _ _ => Ico a (a + ε)
    | Ioc _ _ => Ioo a (a + ε)
    | Ioo _ _ => Ioo a (a + ε)
    set Iright : BoundedInterval := match I with
    | Icc _ _ => Ioc (b - ε) b
    | Ico _ _ => Ioo (b - ε) b
    | Ioc _ _ => Ioc (b - ε) b
    | Ioo _ _ => Ioo (b - ε) b
    set Ileft' : BoundedInterval := match I with
    | Icc _ _ => Icc a (b - ε)
    | Ico _ _ => Icc a (b - ε)
    | Ioc _ _ => Ioc a (b - ε)
    | Ioo _ _ => Ioc a (b - ε)
    have Ileftlen : |Ileft|ₗ = ε := by cases I <;> simp [Ileft, length, le_of_lt hε]
    have Irightlen : |Iright|ₗ = ε := by cases I <;> simp [Iright, length, le_of_lt hε]
    have hjoin1 : Ileft'.joins Ileft I' := by
      cases I
      case Icc _ _ => apply join_Ico_Icc <;> linarith
      case Ico _ _ => apply join_Ico_Icc <;> linarith
      case Ioc _ _ => apply join_Ioo_Icc <;> linarith
      case Ioo _ _ => apply join_Ioo_Icc <;> linarith
    have hjoin2: I.joins Ileft' Iright := by
      cases I
      case Icc _ _ => apply join_Icc_Ioc <;> linarith
      case Ico _ _ => apply join_Icc_Ioo <;> linarith
      case Ioc _ _ => apply join_Ioc_Ioc <;> linarith
      case Ioo _ _ => apply join_Ioc_Ioo <;> linarith
    have hf' : IntegrableOn f I' := by
      apply integ_of_cts $ ContinuousOn.mono hf $ subset_trans _ $ (subset_iff _ _).mp $ Ioo_subset I
      intro _; simp; grind
    choose h hhmin hhconst hhint using lt_of_gt_upper_integral hf'.1 (show upper_integral f I' < integ f I' + ε by linarith [hf'.2])
    classical
    set h' : ℝ → ℝ := fun x ↦ if x ∈ I' then h x else M
    have h'const_left (x:ℝ) (hx: x ∈ Ileft) : h' x = M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [h',mem_iff]
    have h'const_right (x:ℝ) (hx: x ∈ Iright) : h' x = M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [h',mem_iff]
    have h'const : PiecewiseConstantOn h' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, ConstantOn.of_const]
      . apply hhconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, ConstantOn.of_const]
    have h'maj : MajorizesOn h' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [h', hxI']; solve_by_elim; grind [abs_le']
    observe h'maj : upper_integral f I ≤ h'const.integ'
    have h'integ1 := h'const.integ_of_join hjoin2
    have h'integ2 := ((of_join hjoin2 _).mp h'const).1.integ_of_join hjoin1
    have h'integ3 : PiecewiseConstantOn.integ h' Ileft = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_left, integ_const, Ileftlen]
    have h'integ4 : PiecewiseConstantOn.integ h' Iright = M * ε := by
      rw [PiecewiseConstantOn.integ_congr h'const_right, integ_const, Irightlen]
    have h'integ5 : PiecewiseConstantOn.integ h' I' = PiecewiseConstantOn.integ h I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    choose g hgmin hgconst hgint using gt_of_lt_lower_integral hf'.1 (show integ f I' - ε < lower_integral f I' by linarith [hf'.2])
    set g' : ℝ → ℝ := fun x ↦ if x ∈ I' then g x else -M
    have g'const_left (x:ℝ) (hx: x ∈ Ileft) : g' x = -M := by
      replace hjoin1 := Set.eq_empty_iff_forall_notMem.mp hjoin1.1 x
      simp_all [g', mem_iff]
    have g'const_right (x:ℝ) (hx: x ∈ Iright) : g' x = -M := by
      replace hjoin2 := Set.eq_empty_iff_forall_notMem.mp hjoin2.1 x
      replace hjoin1 := congrArg (x ∈ ·) hjoin1.2.1
      simp_all [g', mem_iff]
    have g'const : PiecewiseConstantOn g' I := by
      rw [of_join hjoin2, of_join hjoin1]; split_ands
      . apply_rules [piecewiseConstantOn, ConstantOn.of_const]
      . apply hgconst.congr'; grind [mem_iff]
      apply_rules [piecewiseConstantOn, ConstantOn.of_const]
    have g'maj : MinorizesOn g' f I := by
      intro x _; by_cases hxI': x ∈ I' <;> simp [g', hxI']; solve_by_elim; grind [abs_le']
    observe g'maj : g'const.integ' ≤ lower_integral f I
    have g'integ1 := g'const.integ_of_join hjoin2
    have g'integ2 := ((of_join hjoin2 _).mp g'const).1.integ_of_join hjoin1
    have g'integ3 : PiecewiseConstantOn.integ g' Ileft = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_left, integ_const, Ileftlen]
    have g'integ4 : PiecewiseConstantOn.integ g' Iright = -M * ε := by
      rw [PiecewiseConstantOn.integ_congr g'const_right, integ_const, Irightlen]
    have g'integ5 : PiecewiseConstantOn.integ g' I' = PiecewiseConstantOn.integ g I' := by
      apply PiecewiseConstantOn.integ_congr; grind [mem_iff]
    grind
  exact ⟨ hbound, by linarith [nonneg_of_le_const_mul_eps this] ⟩

/-- Definition 11.5.4 -/
abbrev PiecewiseContinuousOn (f:ℝ → ℝ) (I:BoundedInterval) : Prop :=
  ∃ P: Partition I, ∀ J ∈ P.intervals, ContinuousOn f J

/-- Example 11.5.5 -/
noncomputable abbrev f_11_5_5 : ℝ → ℝ := fun x ↦
  if x < 2 then x^2
  else if x = 2 then 7
  else x^3

example : ¬ ContinuousOn f_11_5_5 (Icc 1 3) := by
  intro h
  specialize h 2 (by simp; norm_num)
  simp at h
  have htt := h.tendsto
  rw [show f_11_5_5 2 = 7 by unfold f_11_5_5; simp] at htt
  have hright : Filter.Tendsto f_11_5_5 (nhdsWithin 2 (Set.Ico 1 2)) (nhds 7) := by
    apply htt.mono_left
    apply nhdsWithin_mono 2
    intro x hx; simp at hx ⊢
    constructor <;> linarith
  have hleft : Filter.Tendsto f_11_5_5 (nhdsWithin 2 (Set.Ico 1 2)) (nhds 4) := by
    unfold f_11_5_5
    have hsq : Filter.Tendsto (fun (x:ℝ) => x ^ 2) (nhdsWithin 2 (Set.Ico 1 2)) (nhds 4) := by
      have hsq' : Filter.Tendsto (fun (x:ℝ) => x ^ 2) (nhds 2) (nhds 4) := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num]
        exact (continuous_pow 2).tendsto (2:ℝ)
      exact hsq'.mono_left nhdsWithin_le_nhds
    apply hsq.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp at hx ⊢
    intro h
    exfalso; linarith
  haveI hnebot : (nhdsWithin (2:ℝ) (Set.Ico 1 2)).NeBot := by
    apply right_nhdsWithin_Ico_neBot
    linarith
  have := tendsto_nhds_unique hleft hright
  simp at this


lemma f_11_5_5_Ico12 : ContinuousOn f_11_5_5 (Ico 1 2) := by
  simp
  have hcont : ContinuousOn (fun (x:ℝ) => x ^ 2)  (Set.Ico 1 2) := by
    exact continuousOn_pow 2
  apply hcont.congr
  intro x hx
  unfold f_11_5_5; simp at hx ⊢
  intro h; exfalso; linarith


lemma f_11_5_5_Icc22 : ContinuousOn f_11_5_5 (Icc 2 2) := by
  simp only [set_Icc, Set.Icc_self]
  apply continuousOn_singleton


lemma  f_11_5_5_Ioc23 : ContinuousOn f_11_5_5 (Ioc 2 3) := by
  simp
  have hcont : ContinuousOn (fun (x:ℝ) => x ^ 3)  (Set.Ioc 2 3) := by
    exact continuousOn_pow 3
  apply hcont.congr
  intro x hx
  unfold f_11_5_5; simp at hx ⊢
  rw [if_neg (by linarith), if_neg (by linarith)]

example : ContinuousOn f_11_5_5 (Ico 1 2) := by
  exact f_11_5_5_Ico12

example : ContinuousOn f_11_5_5 (Icc 2 2) := by
  exact f_11_5_5_Icc22


example : ContinuousOn f_11_5_5 (Ioc 2 3) := by
  exact f_11_5_5_Ioc23

example : PiecewiseContinuousOn f_11_5_5 (Icc 1 3) := by
  -- example : ∃ P:Partition (Icc 1 8),
  -- P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8, ∅} := by
  -- set P1 : Partition (Icc 1 1) := ⊥
  -- set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  -- set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  -- set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  --set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )

  have : ∃ P:Partition (Icc 1 3), P.intervals = {Ico 1 2, Icc 2 2, Ioc 2 3} := by
    set P1 : Partition (Ico 1 2) := ⊥
    set P2 : Partition (Icc 1 2) := P1.join (⊥:Partition (Icc 2 2)) (join_Ico_Icc (by norm_num) (by norm_num))
    set P3 : Partition (Icc 1 3) := P2.join (⊥:Partition (Ioc 2 3)) (join_Icc_Ioc (by norm_num) (by norm_num))
    use P3; aesop
  choose P hP using this
  use P; rw [hP]
  intro J hJ; simp at hJ
  rcases hJ with rfl | rfl | rfl
  . exact f_11_5_5_Ico12
  . exact f_11_5_5_Icc22
  . exact f_11_5_5_Ioc23


open Classical in
/-- Proposition 11.5.6 / Exercise 11.5.1 -/
theorem integ_of_bdd_piecewise_cts {I: BoundedInterval} {f:ℝ → ℝ}
  (hbound: BddOn f I) (hf: PiecewiseContinuousOn f I) : IntegrableOn f I := by
  choose P hP using hf
  set g : BoundedInterval → ℝ → ℝ := fun J x => if x ∈ J then f x else 0
  set γ : ℝ → ℝ := fun x => if h : x ∈ I then g (P.exists_unique x h).choose x else 0
  have heq : ∀ x ∈ I, f x = γ x := by
    intro x hx
    unfold γ
    rw [dif_pos hx]
    unfold g
    have := (P.exists_unique x hx).choose_spec
    rw [if_pos this.1.2]
  have hg : ∀ x ∈ I, γ x = ∑ J ∈ P.intervals, g J x := by
    intro x hx
    have hspec := (P.exists_unique x hx).choose_spec
    rw [Finset.sum_eq_single (P.exists_unique x hx).choose]
    . unfold γ; rw [dif_pos hx]
    . intro J hJ hJ'
      grind
    . intro h'
      grind
  have hfJ : ∀ J ∈ P.intervals, IntegrableOn f J := by
    intro J hJ
    have hboundJ : BddOn f J := by
      apply BddOn.mono hbound
      exact P.contains J hJ
    exact integ_of_bdd_cts hboundJ (hP J hJ)
  have hgJ : ∀ J ∈ P.intervals, IntegrableOn (g J) I := by
    intro J hJ
    apply IntegrableOn.of_extend
    . exact P.contains J hJ
    . exact hfJ J hJ
  have key : ∀ S : Finset BoundedInterval, (∀ J ∈ S, IntegrableOn (g J) I) → IntegrableOn (fun x => ∑ J ∈ S, g J x) I := by
    intro S
    induction S using Finset.induction with
    | empty =>
      simp; apply integ_of_bdd_cts
      . use 0; simp
      . exact continuousOn_const
    | insert J S hJS ih =>
      intro hmem; simp at hmem
      obtain ⟨hJ, hS⟩ := hmem
      specialize ih hS
      simp_rw [Finset.sum_insert hJS]
      exact (IntegrableOn.add hJ ih).1
  have := key P.intervals hgJ
  apply IntegrableOn.congr (hf:=this)
  intro x hx
  simp
  specialize hg x hx
  specialize heq x hx
  rw [← hg, heq]

/-- Exercise 11.5.2 -/
theorem integ_zero {a b:ℝ} (hab: a < b) (f: ℝ → ℝ) (hf: ContinuousOn f (Icc a b))
  (hnonneg: MajorizesOn f (fun _ ↦ 0) (Icc a b)) (hinteg : integ f (Icc a b) = 0) :
  ∀ x ∈ Icc a b, f x = 0 := by
    by_contra! h
    have hbdd := BddOn.of_continuous_on_compact hab hf
    choose x hx hfx0 using h
    --rw [BoundedInterval.mem_iff] at hx; simp at hx
    have hfxpos : 0 < f x := by
      specialize hnonneg x hx
      simp at hnonneg
      grind
    have hcontwithin := hf x hx
    rw [Metric.continuousWithinAt_iff] at hcontwithin
    choose δ hδpos hδ using hcontwithin (f x / 2) (by positivity)
    simp_rw [Real.dist_eq] at hδ
    set l := max a (x - δ/2)
    set r := min b (x + δ/2)
    have hx' := (BoundedInterval.mem_iff _ _).mp hx
    simp at hx'
    -- want : a ≤ l ≤ x ≤ r ≤ b, and l < r so we can have an interval with enough room.
    have hal : a ≤ l := by unfold l; apply le_max_left
    have hrb : r ≤ b := by unfold r; apply min_le_left
    have hlx : l ≤ x := by unfold l; apply max_le; linarith; linarith
    have hxr : x ≤ r := by unfold r; apply le_min; linarith; linarith
    have hlr : l < r := by unfold l r; grind
    have hintegrable := integ_of_cts hf
    -- okay, now split as such :
    -- [a, l), [l, r], (r, b]
    -- first, split intp [a, l) and [l, r]
    have hjoin1 := join_Ico_Icc (a:=a) (b:=l) (c:=b) (by linarith) (by linarith)
    have hstep1 := IntegrableOn.join hjoin1 hintegrable
    have hjoin2 := join_Icc_Ioc (a:=l) (b:=r) (c:=b) (by linarith) (by linarith)
    have hstep2 := IntegrableOn.join hjoin2 hstep1.2.1
    have heq1 := hstep1.2.2 -- [a b] = [a l) + [l b]
    have heq2 := hstep2.2.2 -- [l b] = [l r] + (r b]
    rw [heq2, hinteg] at heq1 -- [a b] = [a l) + [l b] + (r b] = 0
    -- this is so >.<
    have hintegal : 0 ≤ integ f (Ico a l)  := by
      have hsub : Ico a l ⊆ Icc a b := by
        simp [BoundedInterval.subset_iff]
        intro x hx; simp at hx ⊢
        constructor <;> linarith
      apply IntegrableOn.nonneg
      . exact hintegrable.mono' hsub
      . intro x hx
        simpa using hnonneg x (by apply hsub; exact hx)
    have hintegrb : 0 ≤ integ f (Ioc r b) := by
      have hsub : Ioc r b ⊆ Icc a b := by
        simp [BoundedInterval.subset_iff]
        intro x hx; simp at hx ⊢
        constructor <;> linarith
      apply IntegrableOn.nonneg
      . exact hintegrable.mono' hsub
      . intro x hx
        simpa using hnonneg x (by apply hsub; exact hx)
    suffices 0 < integ f (Icc l r) by linarith
    unfold integ
    have hbdd' : BddOn f (Icc l r) := by
      apply hbdd.mono; simp
      grind
    have hlower := lower_integ_ge_lower_sum (f:=f) (I:=Icc l r) (P:=⊥) hbdd'
    have hlower' := lower_integral_le_upper hbdd'
    suffices 0 < lower_riemann_sum f (⊥ : Partition (Icc l r)) by linarith
    unfold lower_riemann_sum
    rw [Partition.intervals_of_bot]
    simp
    have hlen : (Icc l r).length = r - l := by
      unfold length
      simp [BoundedInterval.a, BoundedInterval.b]
      linarith
    rw [hlen]
    suffices 0 < sInf (f '' Set.Icc l r) by nlinarith
    have key : ∀ p ∈ Set.Icc l r, f p > (f x) / 2 := by
      intro p hp
      have : p ∈ Set.Icc a b := by grind
      specialize hδ this (by grind)
      rw [abs_lt] at hδ
      simp at hδ
      linarith
    have hinf : f x / 2 ≤ sInf (f '' Set.Icc l r) := by
      apply le_csInf
      . simp; linarith
      . intro b hb
        choose a ha using hb
        simp at ha
        specialize key a ⟨ha.1.1, ha.1.2⟩
        rw [← ha.2]
        linarith
    linarith


end Chapter11
