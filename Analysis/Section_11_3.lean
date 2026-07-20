import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_2

/-!
# Analysis I, Section 11.3: Upper and lower Riemann integrals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The upper and lower Riemann integral; the Riemann integral.
- Upper and lower Riemann sums.

-/

namespace Chapter11
open BoundedInterval Chapter9

/-- Definition 11.3.1 (Majorization of functions) -/
abbrev MajorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), f x ≤ g x

abbrev MinorizesOn (g f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∀ x ∈ (I:Set ℝ), g x ≤ f x

theorem MinorizesOn.iff (g f:ℝ → ℝ) (I: BoundedInterval) : MinorizesOn g f I ↔ MajorizesOn f g I := by rfl

/-- Definition 11.3.2 (Upper and lower Riemann integrals ). -/
noncomputable abbrev upper_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sInf ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_integral (f:ℝ → ℝ) (I: BoundedInterval) : ℝ :=
  sSup ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

theorem upper_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  upper_integral f I = upper_integral g I := by
  simp [upper_integral]; congr! 2; ext; simp; grind

theorem lower_integral_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  lower_integral f I = lower_integral g I := by
  simp [lower_integral]; congr! 2; ext; simp; grind

lemma integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ M , ⟨ ⟨ _, _ ⟩, PiecewiseConstantOn.integ_const _ _ ⟩ ⟩
  . grind [abs_le']
  apply (ConstantOn.of_const (c := M) _).piecewiseConstantOn; simp

lemma integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) : -M * |I|ₗ ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp
  refine' ⟨ fun _ ↦ -M , ⟨ ⟨ _, _ ⟩, by convert PiecewiseConstantOn.integ_const _ _ using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn

lemma integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_upper_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) : ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty :=
  ⟨ _, integral_bound_lower_of_bounded h.choose_spec ⟩

lemma integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  (ha: a ∈ (PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    obtain ⟨ g, ⟨ ⟨ hmaj, hgp⟩, rfl ⟩ ⟩ := ha
    obtain ⟨ h, ⟨ ⟨ hmin, hhp⟩, rfl ⟩ ⟩ := hb
    apply hhp.integ_mono _ hgp; intro x hx; linarith [hmin _ hx, hmaj _ hx]

lemma integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddBelow ((PiecewiseConstantOn.integ · I) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (integral_bound_lower_nonempty h).some
    intro a ha; exact integral_bound_lower_le_upper ha (integral_bound_lower_nonempty h).some_mem

lemma integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  BddAbove ((PiecewiseConstantOn.integ · I) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (integral_bound_upper_nonempty h).some
    intro b hb; exact integral_bound_lower_le_upper (integral_bound_upper_nonempty h).some_mem hb

/-- Lemma 11.3.3.  The proof has been reorganized somewhat from the textbook. -/
lemma le_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  -M * |I|ₗ ≤ lower_integral f I :=
  le_csSup (integral_bound_above (BddOn.of_bounded h)) (integral_bound_lower_of_bounded h)

lemma lower_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I) :
  lower_integral f I ≤ upper_integral f I := by
  apply csSup_le (integral_bound_lower_nonempty h)
  intros
  apply le_csInf (integral_bound_upper_nonempty h)
  intros
  solve_by_elim [integral_bound_lower_le_upper]

lemma upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) :
  upper_integral f I ≤ M * |I|ₗ :=
  csInf_le (integral_bound_below (BddOn.of_bounded h)) (integral_bound_upper_of_bounded h)

lemma upper_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I) :
  upper_integral f I ≤ hg.integ' := by
  apply csInf_le (integral_bound_below hf) _
  use g; simpa [hg]

lemma integ_le_lower_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I) :
  hg.integ' ≤ lower_integral f I := by
  apply le_csSup (integral_bound_above hf) _
  use h; simpa [hg]

lemma lt_of_gt_upper_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: upper_integral f I < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.integ g I < X := by
  choose Y hY hYX using exists_lt_of_csInf_lt (integral_bound_upper_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

lemma gt_of_lt_lower_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {X:ℝ} (hX: X < lower_integral f I) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.integ h I := by
  choose Y hY hYX using exists_lt_of_lt_csSup (integral_bound_lower_nonempty hf) hX
  simp at hY; peel hY; simp_all; tauto

/-- Definition 11.3.4 (Riemann integral)
As we permit junk values, the simplest definition for the Riemann integral is the upper integral.-/
noncomputable abbrev integ (f:ℝ → ℝ) (I: BoundedInterval) : ℝ := upper_integral f I

theorem integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) :
  integ f I = integ g I := upper_integral_congr h

noncomputable abbrev IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop :=
  BddOn f I ∧ lower_integral f I = upper_integral f I

theorem IntegrableOn.congr {f g:ℝ → ℝ} {I: BoundedInterval} (h: Set.EqOn f g I) (hf : IntegrableOn f I) : IntegrableOn g I := by
  have ⟨hfbd, hagree⟩ := hf
  have hgbd : BddOn g I := by
    choose B hB using hfbd
    use B
    intro x hx
    specialize hB x hx
    specialize h hx
    rwa [← h]
  refine ⟨hgbd, ?_⟩



  sorry

/-- Lemma 11.3.7 / Exercise 11.3.3 -/
theorem integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) :
  IntegrableOn f I ∧ integ f I = hf.integ' := by
  have hbdd : BddOn f I := by
    choose P hP using hf
    use ∑ J ∈ P.intervals, |constant_value_on f J|
    intro x hx
    choose J hJ hJuniq using P.exists_unique x hx
    have hfxconst : f x = constant_value_on f J := by
      apply ConstantOn.eq
      . exact hP J hJ.1
      . exact hJ.2
    rw [hfxconst]
    apply Finset.single_le_sum (f:=fun K:BoundedInterval => |constant_value_on f K|) (by simp)
    exact hJ.1
  have hmajff : MajorizesOn f f I := by unfold MajorizesOn; simp
  have hminff : MinorizesOn f f I := by unfold MinorizesOn; simp
  have h1 := upper_integral_le_integ hbdd hmajff hf
  have h2 := integ_le_lower_integral hbdd hminff hf
  have h3 := lower_integral_le_upper hbdd
  refine ⟨⟨hbdd, ?_⟩, ?_⟩
  . linarith
  . rw [integ]
    linarith


/-- Remark 11.3.8 -/
theorem integ_on_subsingleton {f:ℝ → ℝ} {I: BoundedInterval} (hI: |I|ₗ = 0) :
  IntegrableOn f I ∧ integ f I = 0 := by
  observe : Subsingleton I.toSet
  observe hconst : ConstantOn f I
  convert integ_of_piecewise_const hconst.piecewiseConstantOn
  simp [PiecewiseConstantOn.integ_const' hconst, hI]

/-- Definition 11.3.9 (Riemann sums).  The restriction to positive length J is not needed thanks to various junk value conventions. -/
noncomputable abbrev upper_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ

noncomputable abbrev lower_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ

/-- Lemma 11.3.11 / Exercise 11.3.4 -/
theorem upper_riemann_sum_le {f g: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hgf: MajorizesOn g f I) (hg: PiecewiseConstantWith g P) :
  upper_riemann_sum f P ≤ integ g I := by
  have hgpiecewiseon: PiecewiseConstantOn g I := by
    use P
  obtain ⟨hintegrableon, heq⟩ := integ_of_piecewise_const hgpiecewiseon
  have hdef := PiecewiseConstantOn.integ_def hg
  simp only [PiecewiseConstantOn.integ'] at heq
  rw [hdef] at heq
  rw [heq]
  simp only [upper_riemann_sum, PiecewiseConstantWith.integ]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hemp : (J:Set ℝ).Nonempty
  . have := BoundedInterval.length_nonneg J
    suffices sSup (f '' J) ≤ constant_value_on g J by nlinarith
    apply csSup_le
    . simp; exact hemp
    . intro b hb; simp at hb
      choose b' hb' using hb
      rw [← hb'.2]
      have : constant_value_on g J = g b' := by
        symm
        have hconst := hg J hJ
        apply ConstantOn.eq hconst
        exact hb'.1
      rw [this]
      apply hgf
      apply P.contains J hJ
      exact hb'.1
  . simp [BoundedInterval.length_of_empty hemp]


theorem lower_riemann_sum_ge {f h: ℝ → ℝ} {I:BoundedInterval} (P: Partition I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantWith h P) :
  integ h I ≤ lower_riemann_sum f P := by
  have hpiecewiseon : PiecewiseConstantOn h I := by
    use P
  obtain ⟨hintegrable, heq⟩ := integ_of_piecewise_const hpiecewiseon
  have hdef := PiecewiseConstantOn.integ_def hg
  simp only [PiecewiseConstantOn.integ'] at heq
  rw [hdef] at heq
  rw [heq]
  simp only [lower_riemann_sum, PiecewiseConstantWith.integ]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hemp : (J:Set ℝ).Nonempty
  . have := BoundedInterval.length_nonneg J
    suffices constant_value_on h J ≤ sInf (f '' J) by nlinarith
    apply le_csInf
    . simp; exact hemp
    . intro b hb
      choose b' hb' using hb
      rw [← hb'.2]
      have : constant_value_on h J = h b' := by
        symm
        have hconst := hg J hJ
        apply ConstantOn.eq hconst
        exact hb'.1
      rw [this]
      apply hfh
      apply P.contains J hJ
      exact hb'.1
  . simp [BoundedInterval.length_of_empty hemp]

/-- Proposition 11.3.12 / Exercise 11.3.5 -/
theorem upper_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): upper_integral f I ≤ upper_riemann_sum f P := by
  classical
  set g : ℝ → ℝ := fun (x:ℝ) => if h : ∃ J ∈ P.intervals, x ∈ J then sSup (f '' (h.choose) : Set ℝ) else 0
  have hg_eq {x:ℝ} {J:BoundedInterval} (hJ : J ∈ P.intervals) (hxJ : x ∈ J) : g x = sSup (f '' J) := by
    have hchoice : ∃ J ∈ P.intervals, x ∈ J := by use J
    obtain ⟨hspec1, hspec2⟩ := hchoice.choose_spec
    have hchose : hchoice.choose = J := by
      obtain ⟨J', ⟨hJmem, hJ'⟩, hJ'uniq⟩ := P.exists_unique x (by apply P.contains J hJ; exact hxJ)
      simp at hJ'uniq
      have h1 := hJ'uniq hchoice.choose hspec1 hspec2
      have h2 := hJ'uniq J hJ hxJ
      rw [h1, h2]
    unfold g; rw [dif_pos hchoice, hchose]
  have hf_bddabove {J : BoundedInterval} (hJ : J ∈ P.intervals) :  BddAbove (f '' J) := by
    choose B hB using hf
    use B; intro y hy
    choose x hxJ hfxy using hy
    specialize hB x (by apply P.contains J hJ; exact hxJ)
    grind
  apply csInf_le
  . exact integral_bound_below hf
  . simp
    have hpconstwith : PiecewiseConstantWith g P := by
      intro J hJ
      apply ConstantOn.of_const (c:=sSup (f '' J))
      intro x hx
      exact hg_eq hJ hx
    use g; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx
      obtain ⟨J, ⟨hJP, hxJ⟩, _⟩ := P.exists_unique x hx
      rw [hg_eq hJP hxJ]; apply le_csSup
      . exact hf_bddabove hJP
      . tauto
    . use P
    · rw [PiecewiseConstantOn.integ_def hpconstwith]
      simp only [PiecewiseConstantWith.integ]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J:Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on g J = sSup (f '' J) by nlinarith
        apply ConstantOn.const_eq hemp
        intro x hx
        exact hg_eq hJ hx
      . simp [BoundedInterval.length_of_empty hemp]


theorem upper_integ_eq_inf_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  upper_integral f I = sInf (.range (fun P : Partition I ↦ upper_riemann_sum f P)) := by
  apply le_antisymm
  . apply le_csInf
    . use sSup (f '' I)  * |I|ₗ
      simp; use ⊥; unfold upper_riemann_sum
      have : (⊥: Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl
      simp [this]
    . intro P hP; simp at hP
      choose S hS using hP
      rw [← hS]
      exact upper_integ_le_upper_sum hf S
  . unfold upper_riemann_sum
    apply le_csInf
    . use sSup (f '' I)  * |I|ₗ
      simp
      set g := fun _ => sSup (f '' I)
      use g; refine ⟨⟨?majorizes, ?piecewiseon⟩, ?piecewisewith⟩
      · intro x hx
        unfold g
        apply le_csSup
        . choose B hB using hf
          use B; intro y hy
          choose x hxI hfxy using hy
          rw [← hfxy]
          specialize hB x hxI
          grind
        . use x
      . apply ConstantOn.piecewiseConstantOn
        apply ConstantOn.of_const'
      . have hpwconstwith: PiecewiseConstantWith g (⊥:Partition I) := by
          intro J hJ
          rw [BoundedInterval.intervals_of_bot'] at hJ; subst hJ
          apply ConstantOn.of_const'
        simp only [PiecewiseConstantOn.integ_def hpwconstwith, PiecewiseConstantWith.integ]
        have hint : (⊥:Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl
        simp only [hint, Finset.sum_singleton]
        by_cases! hemp : (I:Set ℝ).Nonempty
        . have hconstval := ConstantOn.const_eq (f:=g) (c:=sSup (f '' I)) hemp (by unfold g; tauto)
          rw [hconstval]
        . simp [BoundedInterval.length_of_empty hemp]
    . intro b hb
      choose g hg using hb
      simp at hg; obtain ⟨⟨hmajorize, hpwconston⟩, hginteg⟩ := hg
      have ⟨hgintegrable, hginteg'⟩ := integ_of_piecewise_const hpwconston
      simp only [PiecewiseConstantOn.integ'] at hginteg'
      choose P hP using hpwconston
      have hupperleb : upper_riemann_sum f P ≤ b := by
        rw [← hginteg, ← hginteg']
        exact upper_riemann_sum_le P hmajorize hP
      suffices sInf (Set.range fun (P:Partition I) ↦ ∑ J ∈ P.intervals, sSup (f '' J) * J.length) ≤ upper_riemann_sum f P by linarith
      apply csInf_le
      . use upper_integral f I
        intro x hx; simp at hx
        choose Q hQ using hx
        rw [← hQ]
        exact upper_integ_le_upper_sum hf Q
      . simp

theorem lower_integ_ge_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
  (P: Partition I): lower_riemann_sum f P ≤ lower_integral f I := by
  classical
  set g : ℝ → ℝ := fun (x:ℝ) => if h : ∃ J ∈ P.intervals, x ∈ J then sInf (f '' (h.choose) : Set ℝ) else 0
  have hg_eq {x:ℝ} {J:BoundedInterval} (hJ : J ∈ P.intervals) (hxJ : x ∈ J) : g x = sInf (f '' J) := by
    have hchoice : ∃ J ∈ P.intervals, x ∈ J := by use J
    obtain ⟨hspec1, hspec2⟩ := hchoice.choose_spec
    have hchose : hchoice.choose = J := by
      obtain ⟨J', ⟨hJmem, hJ'⟩, hJ'uniq⟩ := P.exists_unique x (by apply P.contains J hJ; exact hxJ)
      simp at hJ'uniq
      have h1 := hJ'uniq hchoice.choose hspec1 hspec2
      have h2 := hJ'uniq J hJ hxJ
      rw [h1, h2]
    unfold g; rw [dif_pos hchoice, hchose]
  have hf_bddbelow {J : BoundedInterval} (hJ : J ∈ P.intervals) :  BddBelow (f '' J) := by
    choose B hB using hf
    use -B; intro y hy
    choose x hxJ hfxy using hy
    specialize hB x (by apply P.contains J hJ; exact hxJ)
    grind
  apply le_csSup
  . exact integral_bound_above hf
  . simp
    have hpconstwith : PiecewiseConstantWith g P := by
      intro J hJ
      apply ConstantOn.of_const (c:=sInf (f '' J))
      intro x hx
      exact hg_eq hJ hx
    use g; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx
      obtain ⟨J, ⟨hJP, hxJ⟩, _⟩ := P.exists_unique x hx
      rw [hg_eq hJP hxJ]; apply csInf_le
      . exact hf_bddbelow hJP
      . tauto
    . use P
    . rw [PiecewiseConstantOn.integ_def hpconstwith]
      simp only [PiecewiseConstantWith.integ]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J:Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on g J = sInf (f '' J) by nlinarith
        apply ConstantOn.const_eq hemp
        intro x hx
        exact hg_eq hJ hx
      . simp [BoundedInterval.length_of_empty hemp]

theorem lower_integ_eq_sup_lower_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I) :
  lower_integral f I = sSup (.range (fun P : Partition I ↦ lower_riemann_sum f P)) := by
  apply le_antisymm
  . unfold lower_riemann_sum
    apply csSup_le
    . use sInf (f '' I) * |I|ₗ
      simp
      set g := fun _ => sInf (f '' I)
      use g; refine ⟨⟨?minorizes, ?piecewiseon⟩, ?piecewisewith⟩
      · intro x hx
        unfold g
        apply csInf_le
        . choose B hB using hf
          use -B; intro y hy
          choose x hxI hfxy using hy
          rw [← hfxy]
          specialize hB x hxI
          grind
        . use x
      . apply ConstantOn.piecewiseConstantOn
        apply ConstantOn.of_const'
      . have hpwconstwith: PiecewiseConstantWith g (⊥:Partition I) := by
          intro J hJ
          rw [BoundedInterval.intervals_of_bot'] at hJ; subst hJ
          apply ConstantOn.of_const'
        simp only [PiecewiseConstantOn.integ_def hpwconstwith, PiecewiseConstantWith.integ]
        have hint : (⊥:Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl
        simp only [hint, Finset.sum_singleton]
        by_cases! hemp : (I:Set ℝ).Nonempty
        . have hconstval := ConstantOn.const_eq (f:=g) (c:=sInf (f '' I)) hemp (by unfold g; tauto)
          rw [hconstval]
        . simp [BoundedInterval.length_of_empty hemp]
    . intro b hb
      choose g hg using hb
      simp at hg; obtain ⟨⟨hminorize, hpwconston⟩, hginteg⟩ := hg
      have ⟨hgintegrable, hginteg'⟩ := integ_of_piecewise_const hpwconston
      simp only [PiecewiseConstantOn.integ'] at hginteg'
      choose P hP using hpwconston
      have hblelower : b ≤ lower_riemann_sum f P := by
         rw [← hginteg, ← hginteg']
         exact lower_riemann_sum_ge P hminorize hP
      suffices lower_riemann_sum f P ≤ sSup (Set.range fun (P:Partition I) ↦ ∑ J ∈ P.intervals, sInf (f '' ↑J) * J.length) by linarith
      apply le_csSup
      . use lower_integral f I
        intro x hx
        choose P hP using hx
        simp at hP; rw [← hP]
        exact lower_integ_ge_lower_sum hf P
      . simp
  . apply csSup_le
    . use sInf (f '' I) * |I|ₗ
      simp; use ⊥
      unfold lower_riemann_sum
      have hint : (⊥:Partition I).intervals = {I} := by rfl
      simp [hint]
    . intro S hS; simp at hS; choose P hP using hS
      rw [← hP]
      exact lower_integ_ge_lower_sum hf P

/-- Exercise 11.3.1 -/
theorem MajorizesOn.trans {f g h: ℝ → ℝ} {I: BoundedInterval}
  (hfg: MajorizesOn f g I) (hgh: MajorizesOn g h I) : MajorizesOn f h I := by
  intro x hx
  specialize hgh x hx
  specialize hfg x hx
  linarith


/-- Exercise 11.3.1 -/
theorem MajorizesOn.anti_symm {f g: ℝ → ℝ} {I: BoundedInterval}:
  (∀ x ∈ (I:Set ℝ), f x = g x) ↔ MajorizesOn f g I ∧ MajorizesOn g f I := by
  constructor
  . intro heq; constructor <;>
    . intro x hx; specialize heq x hx; linarith
  . rintro ⟨hf, hg⟩
    intro x hx
    specialize hg x hx
    specialize hf x hx
    linarith

/-- Exercise 11.3.2 -/
def MajorizesOn.of_add : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f+h) (g+h) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  intro f g h I hf x hx
  simp
  exact hf x hx



def MajorizesOn.of_mul : Decidable ( ∀ (f g h:ℝ → ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (f*h) (g*h) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  use fun x => 2 * x
  use fun x => x
  use fun x => - x
  use Ioo 0 1
  constructor
  . intro x hx; simp at hx ⊢
    linarith
  . intro h
    specialize h (0.5) (by simp; norm_num)
    simp at h
    norm_num at h

def MajorizesOn.of_smul : Decidable ( ∀ (f g:ℝ → ℝ) (c:ℝ) (I:BoundedInterval) (hfg: MajorizesOn f g I),
 MajorizesOn (c • f) (c • g) I) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse; push_neg
  use fun x => 2 * x
  use fun x => x
  use -1
  use Ioo 0 1
  constructor
  . intro x hx; simp at hx ⊢
    linarith
  . intro h
    specialize h (0.5) (by simp; norm_num)
    simp at h
    norm_num at h


end Chapter11
