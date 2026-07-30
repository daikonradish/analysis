import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_10_3
import Analysis.Section_11_9


/-!
# Analysis I, Section 11.10: Consequences of the fundamental theorems

I have attempted to make the translation as faithful a paraphrasing as possible of the
original text. When there is a choice between a more idiomatic Lean solution and a
more faithful translation, I have generally chosen the latter. In particular, there will
be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I
have consciously avoided doing so.

Main constructions and results of this section:
- Integration by parts

-/

namespace Chapter11

open BoundedInterval Chapter9 Chapter10

/-- Proposition 11.10.1 (Integration by parts formula) / Exercise 11.10.1 -/
theorem integ_of_mul_deriv {a b:ℝ} (hab: a ≤ b) {F G: ℝ → ℝ}
  (hF: DifferentiableOn ℝ F (Icc a b)) (hG : DifferentiableOn ℝ G (Icc a b))
  (hF': IntegrableOn (derivWithin F (Icc a b)) (Icc a b))
  (hG': IntegrableOn (derivWithin G (Icc a b)) (Icc a b)) :
  integ (F * derivWithin G (Icc a b)) (Icc a b) = F b * G b - F a * G a -
    integ (G * derivWithin F (Icc a b)) (Icc a b) := by
    rcases hab.eq_or_lt with heq | hlt
    . subst heq
      simp at *
      have hI : (Icc a a).length = 0 := by unfold length; simp
      rw [(integ_on_subsingleton hI).2, (integ_on_subsingleton hI).2]
      simp
    set F' := derivWithin F (Icc a b) with hF'def
    set G' := derivWithin G (Icc a b) with hG'def
    have key : AntiderivOn (F * G) (F * G' + F' * G) (Icc a b) := by
      constructor
      . exact hF.mul hG
      . intro x hx
        have hF'deriv := (hF x hx).hasDerivWithinAt; rw [← hF'def] at hF'deriv
        have hG'deriv := (hG x hx).hasDerivWithinAt; rw [← hG'def] at hG'deriv
        convert _root_.HasDerivWithinAt.of_mul hF'deriv hG'deriv using 1
        simp; ring_nf
    have hFinteg := integ_of_cts hF.continuousOn
    have hGinteg := integ_of_cts hG.continuousOn
    have hFG' := integ_of_mul hFinteg hG'
    have hF'G := integ_of_mul hF' hGinteg
    have hsum : IntegrableOn (F * G' + F' * G) (Icc a b) := by
      convert (IntegrableOn.add hFG' hF'G).1 using 1
    have := integ_eq_antideriv_sub (by linarith) hsum key
    rw [(IntegrableOn.add hFG' hF'G).2] at this
    replace this : integ (F * G') (Icc a b)  = (F * G) b - (F * G) a - integ (F' * G) (Icc a b):= by linarith
    rw [this]
    conv_rhs => rw [
      show F b * G b - F a * G a - integ (G * F') (Icc a b) = (F b * G b) - (F a * G a) - integ (G * F') (Icc a b) by linarith
    ]
    congr 1
    congr 1
    rw [mul_comm]


/-- Theorem 11.10.2.  Need to add continuity of α due to our conventions on {name}`α_length` -/
theorem PiecewiseConstantOn.RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} {α f:ℝ → ℝ}
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: PiecewiseConstantOn f (Icc a b)) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  Chapter11.integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hf_integ: IntegrableOn f (Icc a b) := (integ_of_piecewise_const hf).1
  observe hfα'_integ: IntegrableOn (f * α') (Icc a b)
  refine ⟨ hfα'_integ, ?_ ⟩
  choose P hP using hf
  rw [PiecewiseConstantOn.RS_integ_def hP α, hfα'_integ.split P]
  apply Finset.sum_congr rfl; intro J hJ
  calc
    _ = Chapter11.integ ((constant_value_on f (J:Set ℝ)) • α') J := by
      apply Chapter11.integ_congr; intro x hx
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; congr
      exact (hP J hJ).eq hx
    _ = constant_value_on f (J:Set ℝ) * Chapter11.integ α' J := ((hα'.mono' (P.contains _ hJ)).smul _).2
    _ = _ := by
      congr
      have hJsub (hJab : J.a ≤ J.b) : J ⊆ Ioo (J.a - 1) (J.b + 1) :=
        (subset_Icc J).trans (by simp [subset_iff, Set.Icc_subset_Ioo_iff hJab])
      obtain hJab | hJab := le_iff_eq_or_lt.mp (length_nonneg J)
      . rw [(integ_on_subsingleton hJab.symm).2]
        simp [le_iff_lt_or_eq] at hJab; obtain hJab | hJab := hJab
        . rw [α_length_of_empty _ (empty_of_lt hJab)]
        rw [α_length_of_cts _ _ _ (hJsub _) hαcont.continuousOn] <;> grind
      simp [length] at hJab
      rw [α_length_of_cts ?_ ?_ ?_ (hJsub ?_) hαcont.continuousOn ]
      . have : Icc J.a J.b ⊆ Icc a b := by
          have := closure_mono $ (subset_iff _ _).mp $ (Ioo_subset J).trans $ P.contains _ hJ
          simpa [closure_Ioo (show J.a ≠ J.b by linarith), subset_iff] using this
        calc
          _ = Chapter11.integ α' (Icc J.a J.b) := (hα'.mono' this).eq (subset_Icc J) rfl rfl
          _ = _ := by
            convert integ_eq_antideriv_sub (by order) (hα'.mono' this) _
            apply AntiderivOn.mono ⟨ hα_diff, _ ⟩ this
            intros; solve_by_elim [DifferentiableWithinAt.hasDerivWithinAt]
      all_goals linarith

lemma lower_integral_mono {f g : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) (hg : BddOn g I) (hpq : MinorizesOn f g I) :
  lower_integral f I ≤ lower_integral g I := by
  apply csSup_le (integral_bound_lower_nonempty hf)
  intro b hb; simp at hb
  obtain ⟨𝒻, ⟨hminor𝒻, hpwconst𝒻⟩, rfl⟩ := hb
  apply le_csSup (integral_bound_above hg)
  simp; use 𝒻; refine ⟨⟨?_, hpwconst𝒻 ⟩, rfl⟩
  intro x hx
  specialize hpq x hx
  specialize hminor𝒻 x hx
  linarith

lemma upper_integral_mono {f g : ℝ → ℝ} {I : BoundedInterval} (hf : BddOn f I) (hg : BddOn g I) (hpq : MajorizesOn g f I) :
  upper_integral f I ≤ upper_integral g I := by
  apply le_csInf (integral_bound_upper_nonempty hg)
  intro b hb; simp at hb
  obtain ⟨𝒻, ⟨hmajor𝒻, hpwconst𝒻⟩, rfl⟩ := hb
  apply csInf_le (integral_bound_below hf)
  simp; use 𝒻; refine ⟨⟨?_, hpwconst𝒻 ⟩, rfl⟩
  intro x hx
  specialize hpq x hx
  specialize hmajor𝒻 x hx
  linarith



/-- Corollary 11.10.3 -/
theorem RS_integ_eq_integ_of_mul_deriv
  {a b:ℝ} (hab: a < b) {α f:ℝ → ℝ} (hα: Monotone α)
  (hα_diff: DifferentiableOn ℝ α (Icc a b)) (hαcont: Continuous α)
  (hα': IntegrableOn (derivWithin α (Icc a b)) (Icc a b))
  (hf: RS_IntegrableOn f (Icc a b) α) :
  IntegrableOn (f * derivWithin α (Icc a b)) (Icc a b) ∧
  integ (f * derivWithin α (Icc a b)) (Icc a b) = RS_integ f (Icc a b) α := by
  -- This proof is adapted from the structure of the original text.
  set α' := derivWithin α (Icc a b)
  have hfα'_bound: BddOn (f * α') (Icc a b) := by
    have ⟨ M, hM ⟩ := hf.1; have ⟨ N, hN ⟩ := hα'.1
    use M * N; intro x hx; specialize hM _ hx; specialize hN _ hx
    simp [abs_mul]; gcongr; linarith [abs_nonneg (f x)]
  have hα'_nonneg : MajorizesOn α' 0 (Icc a b) := by
    intro x hx
    convert ge_iff_le.mp (derivative_of_monotone _ _ hα (hα_diff x hx))
    rw [←mem_closure_iff_clusterPt]
    simp at hx
    obtain h | h := le_iff_lt_or_eq.mp hx.1
    . apply closure_mono (s := .Ico a x) _
      . simp [closure_Ico (show a ≠ x by linarith), hx.1]
      intro _ _; simp_all; grind
    apply closure_mono (s := .Ioc x b) _
    . simp [closure_Ioc (show x ≠ b by linarith), hx.2]
    intro _ _; simp_all
  have h0 := hf.2
  have h1 : RS_integ f (Icc a b) α ≤ lower_integral (f * α') (Icc a b) := by
    apply le_of_forall_sub_le; intro ε hε
    have ⟨ h, hhminor, hhconst, hh ⟩ :=
      gt_of_lt_lower_RS_integral hf.1 hα (show RS_integ f (Icc a b) α - ε < lower_RS_integral f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    replace : lower_integral (h * α') (Icc a b) = integ (h * α') (Icc a b) := this.1.2
    have why : lower_integral (h * α') (Icc a b) ≤ lower_integral (f * α') (Icc a b) := by
      apply lower_integral_mono
      . apply BddOn.mul
        . exact (integ_of_piecewise_const hhconst).1.1
        . exact hα'.1
      . exact hfα'_bound
      . intro x hx
        specialize hhminor x hx
        specialize hα'_nonneg x hx
        simp at hα'_nonneg ⊢
        nlinarith
    linarith
  have h2 : upper_integral (f * α') (Icc a b) ≤ RS_integ f (Icc a b) α := by
    apply le_of_forall_pos_le_add; intro ε hε
    have ⟨ h, hhmajor, hhconst, hh ⟩ :=
      lt_of_gt_upper_RS_integral hf.1 hα (show upper_RS_integral f (Icc a b) α + ε > RS_integ f (Icc a b) α by linarith)
    have := hhconst.RS_integ_eq_integ_of_mul_deriv hα_diff hαcont hα'
    rw [←this.2] at hh
    have why : upper_integral (f * α') (Icc a b) ≤ upper_integral (h * α') (Icc a b) := by
      apply upper_integral_mono
      . exact hfα'_bound
      . apply BddOn.mul
        . exact (integ_of_piecewise_const hhconst).1.1
        . exact hα'.1
      . intro x hx
        specialize hhmajor x hx
        specialize hα'_nonneg x hx
        simp at hα'_nonneg ⊢
        nlinarith
    linarith
  have h3 : lower_integral (f * α') (Icc a b) ≤
    upper_integral (f * α') (Icc a b) := lower_integral_le_upper hfα'_bound
  refine ⟨ ⟨ hfα'_bound, ?_ ⟩, ?_ ⟩ <;> linarith

lemma BoundedInterval.a_inf {I : BoundedInterval} (h : I.a < I.b) : I.a = sInf (I : Set ℝ) := by
  match I with
  | Ioo a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.a]; symm; exact csInf_Ioo h
  | Ico a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.a]; symm; exact csInf_Ico h
  | Ioc a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.a]; symm; exact csInf_Ioc h
  | Icc a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.a]; symm; exact csInf_Icc (by linarith)

lemma BoundedInterval.b_sup {I : BoundedInterval} (h : I.a < I.b) : I.b = sSup (I : Set ℝ) := by
  match I with
  | Ioo a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.b]; symm; exact csSup_Ioo h
  | Ico a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.b]; symm; exact csSup_Ico h
  | Ioc a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.b]; symm; exact csSup_Ioc h
  | Icc a b =>
    simp [BoundedInterval.a, BoundedInterval.b] at h
    simp [BoundedInterval.b]; symm; exact csSup_Icc (by linarith)


/-- Lemma 11.10.5 / Exercise 11.10.2-/
theorem PiecewiseConstantOn.RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f:ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: PiecewiseConstantOn f (Icc (φ a) (φ b))) :
  PiecewiseConstantOn (f ∘ φ) (Icc a b) ∧ RS_integ (f ∘ φ) (Icc a b) φ =
    integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  choose P' hf using hf
  set P := P'.remove_empty
  have hPnonempty (J : P.intervals) : (J:Set ℝ).Nonempty := by
    have := J.property
    unfold P at this
    simp only [Finset.mem_filter] at this
    exact this.2
  replace hf : PiecewiseConstantWith f P := by
    intro J hJ; simp [P, (· ∈ ·)] at hJ; exact hf J hJ.1
  rw [integ_def hf]
  unfold PiecewiseConstantWith.integ
  set φ_inv : P.intervals → Set ℝ := fun J ↦ { x:ℝ | x ∈ Set.Icc a b ∧ φ x ∈ (J:Set ℝ) }
  have hφ_inv_bounded (J: P.intervals) : Bornology.IsBounded (φ_inv J) := by
    apply Bornology.IsBounded.subset (Icc_bounded a b); intro _; aesop
  have hφ_inv_connected (J : P.intervals) : (φ_inv J).OrdConnected := by
    have : (J : Set ℝ).OrdConnected := by
      match J with
      | ⟨Ico a b, h⟩ => simp; exact Set.ordConnected_Ico
      | ⟨Ioc a b, h⟩ => simp; exact Set.ordConnected_Ioc
      | ⟨Icc a b, h⟩ => simp; exact Set.ordConnected_Icc
      | ⟨Ioo a b, h⟩ => simp; exact Set.ordConnected_Ioo
    unfold φ_inv
    have hIcc : (Set.Icc a b).OrdConnected := by exact Set.ordConnected_Icc
    convert Set.OrdConnected.inter hIcc (this.preimage_mono hφ_mono) using 1
  set φ_inv' : P.intervals → BoundedInterval := fun J ↦ ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose
  have hφ_inv' (J:P.intervals) : φ_inv J = φ_inv' J :=
    ((BoundedInterval.ordConnected_iff _).mp ⟨ hφ_inv_bounded J, hφ_inv_connected J ⟩).choose_spec
  have hφ_inv_nonempty (J:P.intervals) : (φ_inv J).Nonempty := by
    obtain ⟨y, hy⟩ := hPnonempty J
    have hivt := intermediate_value_Icc (a:=a) (b:=b) (by linarith) hφ_cont.continuousOn
    have hsub := P.contains _ J.property
    rw [BoundedInterval.subset_iff] at hsub
    have hmem := hsub hy
    have : y ∈  φ '' Set.Icc a b := by
      apply hivt
      exact hmem
    obtain ⟨x, hx, rfl⟩ := this
    use x
    unfold φ_inv
    exact ⟨hx, hy⟩
  have hφ_inv_const {J:P.intervals} : ConstantOn (f ∘ φ) (φ_inv' J) ∧ constant_value_on (f ∘ φ) (φ_inv' J) = constant_value_on f J := by
    have hmem : ∀ x ∈ (φ_inv' J : Set ℝ), φ x ∈ (J : Set ℝ) := by
      intro x hx
      rw [← hφ_inv' J] at hx
      unfold φ_inv at hx
      exact hx.2
    have hconst' := hf J J.property
    have hconst : ConstantOn (f ∘ φ) (φ_inv' J) := by
      use constant_value_on f J
      intro ⟨x, hx⟩
      simp
      apply ConstantOn.eq
      . exact hf J J.property
      . exact hmem x hx
    refine ⟨hconst, ?_⟩
    choose a ha using hφ_inv_nonempty J
    rw [hφ_inv' J] at ha
    rw [
      ← ConstantOn.eq hconst ha,
      ← ConstantOn.eq hconst' (hmem a ha)
    ]
    simp
  have key (J : P.intervals) (y : ℝ) : y ∈ (φ_inv' J : Set ℝ) ↔ y ∈ Set.Icc a b ∧ φ y ∈ (J:Set ℝ) := by
    rw [← hφ_inv']
    unfold φ_inv
    rfl
  have key_contains {K: BoundedInterval} (hK : K ∈ Finset.image φ_inv' .univ) : K ⊆ Icc a b := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK
    obtain ⟨J, rfl⟩ := hK
    rw [BoundedInterval.subset_iff]
    simp
    intro x hx
    exact ((key J x).mp hx).1
  have key_unique {x:ℝ} (h : x ∈ Icc a b) : ∃! K, K ∈ Finset.image φ_inv' .univ ∧ x ∈ K := by
    have h' := (BoundedInterval.mem_iff _ _).mp h
    simp at h'
    have hφx : φ x ∈ Icc (φ a) (φ b) := by
      rw [BoundedInterval.mem_iff]; simp
      constructor
      all_goals apply hφ_mono; linarith
    choose J hJ hJuniq using P.exists_unique (φ x) hφx
    set J' := φ_inv' ⟨J, hJ.1⟩
    use J'; refine ⟨⟨?_, ?_⟩, ?_⟩
    . simp; use J, hJ.1
    . refine (key ⟨J, hJ.1⟩ x).mpr ⟨?_, hJ.2⟩
      simp; exact h'
    . intro L ⟨hL, hLmem⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hL
      obtain ⟨L', rfl⟩ := hL
      have : L' = ⟨J, hJ.1⟩ := by
        apply Subtype.ext
        simp at hJuniq ⊢
        have : φ x ∈ (L':Set ℝ) := by
          refine ((key L' x).mp ?_).2
          exact hLmem
        exact hJuniq _ L'.property this
      rw [this]
  set Q : Partition (Icc a b) := {
    intervals := .image φ_inv' .univ
    exists_unique := by
      intro x hx
      exact key_unique hx
    contains := by
      intro K hK
      exact key_contains hK
  }
  have hfφ_piecewise : PiecewiseConstantWith (f ∘ φ) Q := by
    intro K hK
    unfold Q at hK
    change K ∈ Finset.image φ_inv' Finset.univ at hK
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK
    choose A hA using hK
    convert (hφ_inv_const (J:=A)).1
    exact hA.symm
  have hfφ_piecewise' : PiecewiseConstantOn (f ∘ φ) (Icc a b) := ⟨ Q, hfφ_piecewise ⟩
  refine ⟨ hfφ_piecewise' , ?_ ⟩
  rw [RS_integ_def hfφ_piecewise]
  unfold PiecewiseConstantWith.RS_integ
  rw [Finset.sum_image, ←Finset.sum_coe_sort (s := P.intervals)]
  . apply Finset.sum_congr rfl
    intro J _
    congr 1
    . exact hφ_inv_const.2
    have hne : ((φ_inv' J): Set ℝ).Nonempty := by
      have := hφ_inv_nonempty J
      rwa [← hφ_inv' J]
    rcases hne.exists_eq_singleton_or_nontrivial with ⟨p, hsingle⟩ | hnt
    . have hjump : jump φ p = 0 := by
        apply jump_of_continuous (X:=Ioo (p-1) (p+1))
        . simp; apply Ioo_mem_nhds; all_goals linarith
        . exact Continuous.continuousWithinAt hφ_cont
      rw [BoundedInterval.singleton_Icc hsingle, α_length_of_pt, hjump]
      symm; apply BoundedInterval.length_of_subsingleton.mp
      simp
      specialize hφ_inv' J; rw [← hφ_inv'] at hsingle
      unfold φ_inv at hsingle; simp at hsingle
      intro x₁ hx₁ x₂ hx₂
      have hJsub : (J:Set ℝ) ⊆ Set.Icc (φ a) (φ b) := by
        exact P.contains J J.property
      have hivt := intermediate_value_Icc (a:=a) (b:=b) (f:=φ) (by linarith) (Continuous.continuousOn hφ_cont)
      have hx₁' : x₁ ∈ φ '' Set.Icc a b := by
        apply hivt
        apply hJsub
        exact hx₁
      have hx₂' : x₂ ∈ φ '' Set.Icc a b := by
        apply hivt
        apply hJsub
        exact hx₂
      choose y₁ hy₁ hφy₁ using hx₁'
      choose y₂ hy₂ hφy₂ using hx₂'
      have hsingley₁ : y₁ ∈ {x | (a ≤ x ∧ x ≤ b) ∧ φ x ∈ (J:Set ℝ)} := by
        constructor
        . simpa using hy₁
        . rw [hφy₁]; exact hx₁
      have hsingley₂ : y₂ ∈ {x | (a ≤ x ∧ x ≤ b) ∧ φ x ∈ (J:Set ℝ)} := by
        constructor
        . simpa using hy₂
        . rw [hφy₂]; exact hx₂
      simp [hsingle] at hsingley₁ hsingley₂
      rw [← hφy₁, ← hφy₂, hsingley₁, hsingley₂]
    set J' := φ_inv' J
    have haa : J'.a < J'.b := by
      choose x hx y hy hxy using hnt
      have hIoo := BoundedInterval.subset_Icc J'
      have hx' : x ∈ Icc J'.a J'.b := by apply hIoo; exact hx
      have hy' : y ∈ Icc J'.a J'.b := by apply hIoo; exact hy
      simp [BoundedInterval.mem_iff] at hx' hy'
      rcases hxy.lt_or_gt; all_goals linarith
    rw [α_length_of_cts (a:=J'.a-1) (b:=J'.b+1) (haa:=by linarith) (hab:=by linarith) (hbb:=by linarith) (hα:=Continuous.continuousOn hφ_cont)]
    . have hJab : J.val.a ≤ J.val.b := by
        choose x₁ hx₁ x₂ hx₂ hx using hnt
        have ⟨hk₁, hmem₁⟩  := (key J x₁).mp hx₁
        by_contra! h
        have hempty := BoundedInterval.empty_of_lt h
        have hnon : (J:Set ℝ) ≠ ∅ := by
          push_neg; use φ x₁
        exact hnon hempty
      simp [length, show 0 ≤ J.val.b - J.val.a by linarith]
      rcases hJab.eq_or_lt with heq | hlt
      . rw [heq]; simp
        have hclosed : IsClosed (φ ⁻¹' {J.val.a}) := isClosed_singleton.preimage hφ_cont
        have hIoo : Set.Ioo J'.a J'.b ⊆ φ ⁻¹' {J.val.a} := by
          intro z hz
          replace hz : z ∈ J' := by
            apply BoundedInterval.Ioo_subset
            exact hz
          unfold J' at hz
          have ⟨hkeyab, hkey⟩ := (key J z).mp hz
          have : φ z ∈ Icc J.val.a J.val.b := by
            apply BoundedInterval.subset_Icc J.val
            exact hkey
          rw [BoundedInterval.mem_iff] at this
          simp at this
          simp; linarith
        have hIcc : Set.Icc J'.a J'.b ⊆ φ ⁻¹' {J.val.a} := by
          rw [← closure_Ioo (by linarith)]
          exact (IsClosed.closure_subset_iff hclosed).mpr hIoo
        have hl : J'.a ∈ Set.Icc J'.a J'.b := by simp; linarith
        have hr : J'.b ∈ Set.Icc J'.a J'.b := by simp; linarith
        have ha := hIcc hl
        have hb := hIcc hr
        simp at ha hb; linarith
      have hnon : (J : Set ℝ).Nonempty := by
        by_contra! h
        have := BoundedInterval.length_of_empty h
        suffices J.val.length > 0 by linarith
        unfold length; simp; exact hlt
      have hivt := intermediate_value_Icc (f:=φ) (a:=a) (b:=b) (by linarith) (Continuous.continuousOn hφ_cont)
      congr 1
      . rw [BoundedInterval.b_sup (I:=J') (by linarith), BoundedInterval.b_sup (I:=J) (by linarith)]
        apply le_antisymm
        . have hclosed : IsClosed (φ ⁻¹' (Set.Iic (sSup (J:Set ℝ)))) := isClosed_Iic.preimage hφ_cont
          have hIoo : Set.Ioo J'.a J'.b ⊆ φ⁻¹' Set.Iic (sSup (J:Set ℝ)) := by
            intro z hz
            replace hz : z ∈ J' := by
              apply BoundedInterval.Ioo_subset
              exact hz
            unfold J' at hz
            have ⟨hkeyab, hkey⟩ := (key J z).mp hz
            have : φ z ∈ Icc J.val.a J.val.b := by
              apply BoundedInterval.subset_Icc J.val
              exact hkey
            rw [BoundedInterval.mem_iff] at this
            simp at this
            simp; apply le_csSup
            . use J.val.b; intro p hp
              have := BoundedInterval.subset_Icc J
              rw [BoundedInterval.subset_iff] at this; simp at this
              specialize this hp; simp at this; linarith
            . exact hkey
          have hIcc : Set.Icc J'.a J'.b ⊆ φ⁻¹' Set.Iic (sSup (J:Set ℝ)) := by
            rw [← closure_Ioo (by linarith)]
            exact (IsClosed.closure_subset_iff hclosed).mpr hIoo
          apply hIcc
          rw [← BoundedInterval.b_sup (I:=J') (by linarith)]
          simp; linarith
        . apply csSup_le hnon
          intro j hj
          unfold J'; rw [← hφ_inv' J]; unfold φ_inv
          have hjIcc : j ∈ Set.Icc (φ a) (φ b) := by
            apply P.contains J.val J.property; exact hj
          have hj' := hivt hjIcc
          obtain ⟨μ, hμ, rfl⟩ := hj'
          apply hφ_mono
          apply le_csSup
          . use b; intro p hp; simp at hp; linarith
          . exact ⟨hμ, hj⟩
      . rw [BoundedInterval.a_inf (I:=J') (by linarith), BoundedInterval.a_inf (I:=J) (by linarith)]
        apply le_antisymm
        . apply le_csInf hnon
          intro j hj
          unfold J'; rw [← hφ_inv' J]; unfold φ_inv
          have hjIcc : j ∈ Set.Icc (φ a) (φ b) := by
            apply P.contains J.val J.property; exact hj
          have hj' := hivt hjIcc
          obtain ⟨μ, hμ, rfl⟩ := hj'
          apply hφ_mono
          apply csInf_le
          . use a; intro p hp; simp at hp; linarith
          . exact ⟨hμ, hj⟩
        . have hclosed : IsClosed (φ ⁻¹' (Set.Ici (sInf (J:Set ℝ)))) := isClosed_Ici.preimage hφ_cont
          have hIoo : Set.Ioo J'.a J'.b ⊆ φ⁻¹' Set.Ici (sInf (J:Set ℝ)) := by
            intro p hp
            replace hp : p ∈ J' := by
              apply BoundedInterval.Ioo_subset J'; exact hp
            unfold J' at hp
            have ⟨hkeyab, hkey⟩ := (key J p).mp hp
            simp; apply csInf_le
            . use J.val.a
              intro q hq
              have := BoundedInterval.subset_Icc J
              rw [BoundedInterval.subset_iff] at this; simp at this
              specialize this hq; simp at this; linarith
            . exact hkey
          have hIcc : Set.Icc J'.a J'.b ⊆ φ⁻¹' Set.Ici (sInf (J:Set ℝ)) := by
            rw [← closure_Ioo (by linarith)]
            exact (IsClosed.closure_subset_iff hclosed).mpr hIoo
          apply hIcc
          rw [← BoundedInterval.a_inf (I:=J') (by linarith)]
          simp; linarith
    . intro x hx
      have hxIcc := BoundedInterval.subset_Icc J' x hx
      simp [BoundedInterval.mem_iff] at hxIcc ⊢
      constructor <;> linarith
  intro J _ K _ hJK
  set x := (hφ_inv_nonempty J).some
  have h1 : x ∈ φ_inv J := (hφ_inv_nonempty J).some_mem
  have h2 : x ∈ φ_inv K := by rwa [hφ_inv' J, hJK, ←hφ_inv' K] at h1
  simp [φ_inv] at h1 h2
  have h3 : φ x ∈ Icc (φ a) (φ b) := by
    have := P.contains _ J.property
    simp only [subset_iff, mem_iff] at this ⊢
    exact this h1.2
  ext; apply (P.exists_unique _ h3).unique <;> simp [J.property, K.property, mem_iff, h1, h2]

/-- Proposition 11.10.6 (Change of variables formula II). -/
theorem RS_integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ) (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  RS_IntegrableOn (f ∘ φ) (Icc a b) φ ∧
  RS_integ (f ∘ φ) (Icc a b) φ = integ f (Icc (φ a) (φ b)) := by
  -- This proof is adapted from the structure of the original text.
  have hf_bdd := hf.1
  have hfφ_bdd : BddOn (f ∘ φ) (Icc a b) := by
    choose M hM using hf_bdd
    use M
    intro x hx
    have : φ x ∈ Set.Icc (φ a) (φ b) := by
      simp at hx ⊢
      constructor; all_goals apply hφ_mono; linarith
    simpa using hM (φ x) this
  have heq : lower_integral f (Icc (φ a) (φ b)) = upper_integral f (Icc (φ a) (φ b)) := hf.2
  have hupper : upper_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_integral f (Icc (φ a) (φ b)) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose f_up hf_upmajor hf_upconst hf_up using lt_of_gt_upper_integral hf.1 (show upper_integral f (Icc (φ a) (φ b)) + ε > integ f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_upconst
    rw [←hpc.2] at hf_up
    have : MajorizesOn (f_up ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_upmajor; aesop
    linarith [upper_RS_integral_le_integ hfφ_bdd this hpc.1 hφ_mono]
  have hlower : lower_integral f (Icc (φ a) (φ b)) ≤ lower_RS_integral (f ∘ φ) (Icc a b) φ := by
    apply le_of_forall_sub_le
    intro ε hε
    choose f_low hf_lowminor hf_lowconst hf_low using gt_of_lt_lower_integral hf.1 (show lower_integral f (Icc (φ a) (φ b)) - ε < lower_integral f (Icc (φ a) (φ b)) by grind)
    have hpc := PiecewiseConstantOn.RS_integ_of_comp hab hφ_cont hφ_mono hf_lowconst
    rw [←hpc.2] at hf_low
    have : MinorizesOn (f_low ∘ φ) (f ∘ φ) (Icc a b) := by intro _ _; simp at *; apply hf_lowminor; aesop
    linarith [integ_le_lower_RS_integral hfφ_bdd this hpc.1 hφ_mono]
  have hle : lower_RS_integral (f ∘ φ) (Icc a b) φ ≤ upper_RS_integral (f ∘ φ) (Icc a b) φ :=
    lower_RS_integral_le_upper hfφ_bdd hφ_mono
  refine ⟨ ⟨ hfφ_bdd, ?_ ⟩, ?_ ⟩ <;> linarith

/-- Proposition 11.10.7 (Change of variables formula III). -/
theorem integ_of_comp {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_mono: Monotone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ a) (φ b))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    integ f (Icc (φ a) (φ b)) := by
 have h1 := RS_integ_of_comp hab hφ_cont hφ_mono hf
 have h2 := RS_integ_eq_integ_of_mul_deriv hab hφ_mono hφ_diff hφ_cont hφ' h1.1
 refine ⟨ h2.1, by aesop ⟩

def BoundedInterval.neg : BoundedInterval → BoundedInterval
  | .Icc a b => .Icc (-b) (-a)
  | .Ico a b => .Ioc (-b) (-a)
  | .Ioc a b => .Ico (-b) (-a)
  | .Ioo a b => .Ioo (-b) (-a)

lemma BoundedInterval.Icc_neg {a b : ℝ} : (Icc a b).neg = Icc (-b) (-a) := by
  unfold neg; simp

lemma BoundedInterval.Ico_neg {a b : ℝ} : (Ico a b).neg = Ioc (-b) (-a) := by
  unfold neg; simp

lemma BoundedInterval.Ioc_neg {a b : ℝ} : (Ioc a b).neg = Ico (-b) (-a) := by
  unfold neg; simp

lemma BoundedInterval.Ioo_neg {a b : ℝ} : (Ioo a b).neg = Ioo (-b) (-a) := by
  unfold neg; simp

theorem BoundedInterval.coe_neg (J : BoundedInterval) :
  J.neg = Neg.neg '' (J : Set ℝ) := by
  match J with
  | .Icc a b =>
    rw [BoundedInterval.Icc_neg]; simp
  | .Ico a b =>
    rw [BoundedInterval.Ico_neg]; simp
  | .Ioc a b =>
    rw [BoundedInterval.Ioc_neg]; simp
  | .Ioo a b =>
    rw [BoundedInterval.Ioo_neg]; simp

theorem BoundedInterval.length_neg (J : BoundedInterval) : J.neg.length = J.length := by
  cases J <;> simp only [BoundedInterval.neg, BoundedInterval.length, neg_sub_neg]

theorem BoundedInterval.neg_neg (J : BoundedInterval) : J.neg.neg = J := by
  cases J <;> simp [BoundedInterval.neg, _root_.neg_neg]

noncomputable def Partition.neg {I : BoundedInterval} (P : Partition I) : Partition I.neg where
  intervals := P.intervals.image BoundedInterval.neg
  exists_unique := by
    intro x hx
    replace hx : x ∈ ((I.neg) : Set ℝ) := hx
    have hx' : (-x) ∈ (I:Set ℝ) := by
      rw [BoundedInterval.coe_neg] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp; exact hy
    obtain ⟨J, ⟨hJ, hJ'⟩, hJuniq⟩ := P.exists_unique (-x) hx'
    use J.neg; simp; refine ⟨⟨?_, ?_⟩, ?_⟩
    . use J
    . show x ∈ ((J.neg) : Set ℝ)
      rw [BoundedInterval.coe_neg]
      simp; exact hJ'
    . intro L hL hxL
      have hxL' : -x ∈ L := by
        replace hxL : x ∈ ((L.neg) : Set ℝ) := hxL
        rw [BoundedInterval.coe_neg] at hxL
        obtain ⟨y, hy, rfl⟩ := hxL
        simp; exact hy
      specialize hJuniq L ⟨hL, hxL'⟩
      rw [hJuniq]
  contains := by
    intro J hJ; simp at hJ
    choose J' hJ' hJJ' using hJ
    rw [← hJJ']
    have hsub := P.contains J' hJ'
    rw [BoundedInterval.subset_iff] at hsub ⊢
    rw [BoundedInterval.coe_neg, BoundedInterval.coe_neg]
    exact Set.image_mono hsub

lemma PiecewiseConstantOn.negative_interval {φ : ℝ → ℝ} {a b : ℝ} (P : Partition (Icc a b)) (h : PiecewiseConstantWith φ P) :
  PiecewiseConstantOn (fun x ↦ φ (-x)) (Icc (-b) (-a)) := by
  use P.neg
  intro J' hJ'
  change J' ∈ P.intervals.image BoundedInterval.neg at hJ'
  simp at hJ'
  choose J hJ hJneg using hJ'
  by_cases! h' : (J':Set ℝ).Nonempty
  . choose p hp using h'
    have hp' : - p ∈ J := by
      rw [← hJneg] at hp
      change p ∈ ((J.neg) : Set ℝ) at hp
      rw [BoundedInterval.coe_neg] at hp
      simp at hp; exact hp
    apply ConstantOn.of_const (c:=φ (-p))
    intro z hz
    have hz' : -z ∈ J := by
      rw [← hJneg] at hz
      change z ∈ ((J.neg) : Set ℝ) at hz
      rw [BoundedInterval.coe_neg] at hz
      simp at hz; exact hz
    have hconst := h J hJ
    linarith [hconst.eq hz', hconst.eq hp']
  . use 12992387498237038109283; intro ⟨x, hmem⟩; rw [h'] at hmem; simp at hmem

lemma PiecewiseConstantOn.integ_negative_interval {φ : ℝ → ℝ} {a b : ℝ} (h : PiecewiseConstantOn φ (Icc a b)) :
    PiecewiseConstantOn.integ (fun x ↦ φ (-x)) (Icc (-b) (-a)) = PiecewiseConstantOn.integ φ (Icc a b) := by
  have ⟨P, hP⟩ := h
  set P' : Partition (Icc (-b) (-a)) := P.neg
  have hP' : PiecewiseConstantWith (fun x ↦ φ (-x)) P' := by
    intro J' hJ'
    change J' ∈ P.intervals.image BoundedInterval.neg at hJ'
    simp at hJ'
    choose J hJ hJneg using hJ'
    by_cases! h' : (J':Set ℝ).Nonempty
    . choose p hp using h'
      have hp' : - p ∈ J := by
        rw [← hJneg] at hp
        change p ∈ ((J.neg) : Set ℝ) at hp
        rw [BoundedInterval.coe_neg] at hp
        simp at hp; exact hp
      apply ConstantOn.of_const (c:=φ (-p))
      intro z hz
      have hz' : -z ∈ J := by
        rw [← hJneg] at hz
        change z ∈ ((J.neg) : Set ℝ) at hz
        rw [BoundedInterval.coe_neg] at hz
        simp at hz; exact hz
      have hconst := hP J hJ
      linarith [hconst.eq hz', hconst.eq hp']
    . use 12992387498237038109283; intro ⟨x, hmem⟩; rw [h'] at hmem; simp at hmem
  rw [PiecewiseConstantOn.integ_def hP', PiecewiseConstantOn.integ_def hP]
  simp only [PiecewiseConstantWith.integ]
  rw [show P'.intervals = P.intervals.image BoundedInterval.neg by rfl]
  rw [Finset.sum_image]
  . apply Finset.sum_congr rfl
    intro J hJ
    rw [BoundedInterval.length_neg]
    by_cases! hemp : (J : Set ℝ) = ∅
    . have hemp' : (J.neg : Set ℝ) = ∅ := by
        rw [BoundedInterval.coe_neg, hemp]
        simp
      rw [hemp', hemp]
      congr 1
      exact constant_value_on_congr (by intro x hx; simp at hx)
    . have hconst := hP J hJ
      have ⟨p, hp⟩ := hemp
      have hnegp : -p ∈ (↑J.neg : Set ℝ) := by
        rw [BoundedInterval.coe_neg]; exact ⟨p, hp, rfl⟩
      have hcn : ConstantOn (fun x ↦ φ (-x)) J.neg := by
        apply ConstantOn.of_const (c := φ p)
        intro y hy
        rw [BoundedInterval.coe_neg] at hy
        obtain ⟨z, hz, rfl⟩ := hy               -- y = -z, z ∈ ↑J
        simp
        have hconst := hP J hJ
        linarith [hconst.eq hp, hconst.eq hz]
      congr 1
      rw [← hcn.eq hnegp, ← hconst.eq hp]
      simp
  . intro J hJ K hK hJK
    rw [← BoundedInterval.neg_neg J, ← BoundedInterval.neg_neg K, hJK]


/-- Exercise 11.10.3-/
lemma IntegrableOn.of_neg {a b:ℝ} (hab: a < b) {f: ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
  integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = integ f (Icc a b) := by
  have hint : IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) := by
    constructor
    . choose M hM using hf.1
      use M
      intro p hp
      simp at hp
      simpa using hM (-p) (by simp; constructor <;> linarith)
    . have hagree := hf.2
      have hlo : lower_integral (fun x ↦ f (-x)) (Icc (-b) (-a)) = lower_integral f (Icc a b) := by
        unfold lower_integral
        congr 1
        ext x; constructor
        . intro h; simp at h
          obtain ⟨φ, ⟨hminorφ, hpwconstφ⟩, hintegφ⟩ := h
          simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
          . intro p hp
            have hp' : -p ∈ (Icc (-b) (-a)) := by
              rw [BoundedInterval.mem_iff]
              simp at hp ⊢
              constructor <;> linarith
            specialize hminorφ (-p) hp'
            simp at hminorφ ⊢; linarith
          . choose P hP using hpwconstφ
            simpa using PiecewiseConstantOn.negative_interval P hP
          . have ⟨P, hP⟩ := hpwconstφ
            rw [← hintegφ]
            simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ
        . intro h; simp at h
          obtain ⟨φ, ⟨hminorφ, hpwconstφ⟩, hintegφ⟩ := h
          simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
          . intro p hp
            have hp' : -p ∈ (Icc a b) := by
              rw [BoundedInterval.mem_iff]
              simp at hp ⊢
              constructor <;> linarith
            specialize hminorφ (-p) hp'
            simp at hminorφ ⊢; linarith
          . choose P hP using hpwconstφ
            simpa using PiecewiseConstantOn.negative_interval P hP
          . have ⟨P, hP⟩ := hpwconstφ
            rw [← hintegφ]
            simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ
      have hup : upper_integral (fun x ↦ f (-x)) (Icc (-b) (-a)) = upper_integral f (Icc a b) := by
        unfold upper_integral
        congr 1
        ext x; constructor
        . intro h; simp at h
          obtain ⟨φ, ⟨hmajorφ, hpwconstφ⟩, hintegφ⟩ := h
          simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
          . intro p hp
            have hp' : -p ∈ (Icc (-b) (-a)) := by
              rw [BoundedInterval.mem_iff]
              simp at hp ⊢
              constructor <;> linarith
            specialize hmajorφ (-p) hp'
            simp at hmajorφ ⊢; linarith
          . choose P hP using hpwconstφ
            simpa using PiecewiseConstantOn.negative_interval P hP
          . have ⟨P, hP⟩ := hpwconstφ
            rw [← hintegφ]
            simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ
        . intro h; simp at h
          obtain ⟨φ, ⟨hmajorφ, hpwconstφ⟩, hintegφ⟩ := h
          simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
          . intro p hp
            have hp' : -p ∈ (Icc a b) := by
              rw [BoundedInterval.mem_iff]
              simp at hp ⊢
              constructor <;> linarith
            specialize hmajorφ (-p) hp'
            simp at hmajorφ ⊢; linarith
          . choose P hP using hpwconstφ
            simpa using PiecewiseConstantOn.negative_interval P hP
          . have ⟨P, hP⟩ := hpwconstφ
            rw [← hintegφ]
            simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ
      linarith
  refine ⟨hint, ?_⟩
  unfold integ upper_integral
  congr 1
  ext x; constructor
  . intro h; simp at h
    obtain ⟨φ, ⟨hminorφ, hpwconstφ⟩, hintegφ⟩ := h
    simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro p hp
      have hp' : -p ∈ (Icc (-b) (-a)) := by
        rw [BoundedInterval.mem_iff]
        simp at hp ⊢
        constructor <;> linarith
      specialize hminorφ (-p) hp'
      simp at hminorφ ⊢; linarith
    . choose P hP using hpwconstφ
      simpa using PiecewiseConstantOn.negative_interval P hP
    . have ⟨P, hP⟩ := hpwconstφ
      rw [← hintegφ]
      simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ
  . intro h; simp at h
    obtain ⟨φ, ⟨hminorφ, hpwconstφ⟩, hintegφ⟩ := h
    simp; use fun x => φ (-x); refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro p hp
      have hp' : -p ∈ (Icc a b) := by
        rw [BoundedInterval.mem_iff]
        simp at hp ⊢
        constructor <;> linarith
      specialize hminorφ (-p) hp'
      simp at hminorφ ⊢; linarith
    . choose P hP using hpwconstφ
      simpa using PiecewiseConstantOn.negative_interval P hP
    . have ⟨P, hP⟩ := hpwconstφ
      rw [← hintegφ]
      simpa using PiecewiseConstantOn.integ_negative_interval hpwconstφ

example {a b:ℝ} (hab: a < b) {f: ℝ → ℝ} (hf: IntegrableOn f (Icc a b)) :
  IntegrableOn (fun x ↦ f (-x)) (Icc (-b) (-a)) ∧
  integ (fun x ↦ f (-x)) (Icc (-b) (-a)) = integ f (Icc a b) := by
  apply IntegrableOn.of_neg; all_goals assumption

/- Exercise 11.10.4: state and prove a version of `integ_of_comp` in which `φ` is `Antitone` rather than `Monotone`. -/
-- Proposition 11.10.7 (Change of variables formula III). -/

theorem integ_of_comp' {a b:ℝ} (hab: a < b) {φ f: ℝ → ℝ}
  (hφ_diff: DifferentiableOn ℝ φ (Icc a b))
  (hφ_cont: Continuous φ) (hφ_anti: Antitone φ)
  (hφ': IntegrableOn (derivWithin φ (Icc a b)) (Icc a b))
  (hf: IntegrableOn f (Icc (φ b) (φ a))) :
  IntegrableOn (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) ∧
  integ (f ∘ φ * derivWithin φ (Icc a b)) (Icc a b) =
    - integ f (Icc (φ b) (φ a)) := by
  set ψ : ℝ → ℝ := fun x => φ (-x)
  have hmaps : Set.MapsTo (fun x => -x) ((Icc (-b) (-a)) : Set ℝ) ((Icc a b) : Set ℝ) := by
      intro x hx
      simp at hx ⊢
      constructor <;> linarith
  have hψ_mono : Monotone ψ := by
    intro x y hxy
    unfold ψ
    apply hφ_anti
    linarith
  have ha : ψ (-a) = φ a := by
    unfold ψ; simp
  have hb : ψ (-b) = φ b := by
    unfold ψ; simp
  have hψ_diff : DifferentiableOn ℝ ψ ↑(Icc (-b) (-a)) := by
    exact hφ_diff.comp (differentiable_id.neg).differentiableOn hmaps
  have hψ_cont : Continuous ψ := by
    unfold ψ
    apply Continuous.comp
    . exact hφ_cont
    . exact continuous_neg
  have hset : Set.EqOn (fun y ↦ -derivWithin φ ((Icc a b)) (-y)) (derivWithin ψ (Icc (-b) (-a))) (Icc (-b) (-a)) := by
    intro x hx
    have hxmem' :  - x ∈ Set.Icc a b := by
      simp at hx ⊢; constructor <;> linarith
    have hneg : HasDerivWithinAt (fun y : ℝ => -y) (-1) (Set.Icc (-b) (-a)) x := by
      exact hasDerivWithinAt_neg x _
    have hφd : HasDerivWithinAt φ (derivWithin φ (Set.Icc a b) (-x)) (Set.Icc a b) (-x) := by
      exact (hφ_diff (-x) hxmem').hasDerivWithinAt
    have hcomp : HasDerivWithinAt ψ (derivWithin φ (Set.Icc a b) (-x) * -1) (Set.Icc (-b) (-a)) x := by
      apply hφd.comp x
      . exact hneg
      . exact hmaps
    have huniq : UniqueDiffWithinAt ℝ (Set.Icc (-b) (-a)) x := uniqueDiffOn_Icc (by linarith) x hx
    simp
    rw [hcomp.derivWithin huniq]
    simp
  have hψ' : IntegrableOn (derivWithin ψ (Icc (-b) (-a))) (Icc (-b) (-a)) := by
    apply IntegrableOn.congr (I:=Icc (-b) (-a)) (f:=fun y => -(derivWithin φ (Icc a b) (-y))) (g:=derivWithin ψ (Icc (-b) (-a)))
    . have := IntegrableOn.of_neg hab hφ'
      convert (this.1).neg.1  using 1
    . exact hset
  have hf' : IntegrableOn f (Icc (ψ (-b)) (ψ (-a))) := by
    rwa [ha, hb]
  have hψ_cov := integ_of_comp (φ:=ψ) (f:=f) (a:=-b) (b:=-a) (hab:=by linarith) (hφ_diff:=hψ_diff) (hφ_cont:=hψ_cont) (hφ_mono:=hψ_mono) (hφ':=hψ') (hf:=hf')
  have ⟨h1, h2⟩ := (IntegrableOn.of_neg (by linarith) (hψ_cov.1).neg.1)
  constructor
  . simp at h1
    apply h1.congr
    intro x hx
    simp
    have hx' : - x ∈ Set.Icc (-b) (-a) := by
      simp at hx ⊢; constructor <;> linarith
    rw [show ψ (-x) = φ x by unfold ψ; simp]
    unfold ψ
    conv_lhs =>
      rw [← neg_mul, show -f (φ x) = f (φ x) * (-1) by linarith, mul_assoc, neg_mul, one_mul]
    congr 1
    -- derivWithin (fun x ↦ φ (-x)) (Set.Icc (-b) (-a)) (-x) = derivWithin φ (Set.Icc a b) x
    specialize hset hx'
    simp at hset ⊢
    linarith
  . simp at h2
    rw [← ha, ← hb] at *
    rw [← hψ_cov.2, ← (IntegrableOn.neg hψ_cov.1).2]
    simp; rw [← h2]
    apply integ_congr
    simp
    intro x hx
    have hx' : - x ∈ Set.Icc (-b) (-a) := by
      simp at hx ⊢; constructor <;> linarith
    specialize hset hx'; simp at hset ⊢
    rw [← hset]
    simp
    unfold ψ; simp


end Chapter11
