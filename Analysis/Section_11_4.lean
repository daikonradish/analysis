import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_11_3

/-!
# Analysis I, Section 11.4: Basic properties of the Riemann integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Basic properties of the Riemann integral.

-/

namespace Chapter11
open Chapter9


lemma PiecewiseConstantOn.of_const (c:ℝ) (I: BoundedInterval) :
    PiecewiseConstantOn (fun _ ↦ c) I :=
  (ConstantOn.of_const' c _).piecewiseConstantOn

lemma PiecewiseConstantWith.of_const_bot (c:ℝ) (I: BoundedInterval) :
    PiecewiseConstantWith (fun _ ↦ c) (⊥ : Partition I) := by
  intro J hJ; change J ∈ ({I}:Finset BoundedInterval) at hJ
  simp at hJ; subst hJ
  exact ConstantOn.of_const' c J

lemma PiecewiseConstantWith.add {I : BoundedInterval} {f g : ℝ → ℝ} {P : Partition I} (hf : PiecewiseConstantWith f P) (hg : PiecewiseConstantWith g P) :
  PiecewiseConstantWith (f + g) P := by
  intro J hJ;
  choose c₁ hc₁ using hf J hJ
  choose c₂ hc₂ using hg J hJ
  apply ConstantOn.of_const (c:=c₁+c₂)
  intro x hx; simp at hc₁ hc₂ ⊢
  specialize hc₁ x hx
  specialize hc₂ x hx
  linarith

lemma PiecewiseConstantWith.smul {I : BoundedInterval} {c : ℝ} {f : ℝ → ℝ} {P : Partition I} (hf : PiecewiseConstantWith f P) :
  PiecewiseConstantWith (c • f) P := by
  intro J hJ
  choose b hb using hf J hJ
  apply ConstantOn.of_const (c:=(c * b))
  intro x hx; simp at hb hx ⊢
  left; exact hb x hx


lemma constant_value_on_of_add {f g : ℝ → ℝ} {I J:BoundedInterval} {P:Partition I}
  (h : J ∈ P.intervals) (hnon : (J: Set ℝ).Nonempty) (hf : PiecewiseConstantWith f P) (hg : PiecewiseConstantWith g P):
  constant_value_on (f + g) J = constant_value_on f J + constant_value_on g J := by
  have ⟨x, hx⟩ := hnon
  rw [ConstantOn.const_eq (c:=(f + g) x) hnon ?_]
  rw [ConstantOn.const_eq (c:=f x) hnon ?_]
  rw [ConstantOn.const_eq (c:=g x) hnon ?_]
  simp
  . choose c hc using hg J h
    simp at hc
    intro x' hx'
    rw [hc x hx, hc x' hx']
  . choose c hc using hf J h
    simp at hc
    intro x' hx'
    rw [hc x hx, hc x' hx']
  · choose c₁ hc₁ using hf J h
    choose c₂ hc₂ using hg J h
    simp at hc₁ hc₂ ⊢
    intro x' hx'
    rw [hc₁ x hx, hc₁ x' hx', hc₂ x hx, hc₂ x' hx']

lemma constant_value_on_of_smul {k : ℝ} {f : ℝ → ℝ} {I J:BoundedInterval} {P:Partition I}
  (h : J ∈ P.intervals) (hnon : (J: Set ℝ).Nonempty) (hf : PiecewiseConstantWith f P) :
  constant_value_on (k • f) J = k * constant_value_on f J  := by
  have ⟨x, hx⟩ := hnon
  rw [ConstantOn.const_eq (c:=(k • f) x) hnon ?_]
  rw [ConstantOn.const_eq (c:=f x) hnon ?_]
  simp
  . choose c hc using hf J h
    simp at hc
    intro x' hx'
    rw [hc x hx, hc x' hx']
  · choose c hc using hf J h
    simp at hc ⊢
    intro x' hx'
    rw [hc x hx, hc x' hx']
    left; rfl

lemma upper_integral_add_le_add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  upper_integral (f + g) I ≤ upper_integral f I + upper_integral g I := by
  obtain ⟨hfbdd, hfagree⟩ := hf
  obtain ⟨hgbdd, hgagree⟩ := hg
  have haddbdd : BddOn (f + g) I := by exact BddOn.add _ _ _ hfbdd hgbdd
  suffices upper_integral (f + g) I - upper_integral g I ≤ upper_integral f I by linarith
  conv_rhs => unfold upper_integral
  apply le_csInf (integral_bound_upper_nonempty hfbdd)
  intro b hb; simp at hb
  obtain ⟨φ, ⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hb
  suffices upper_integral (f + g) I - b ≤ upper_integral g I by linarith
  conv_rhs => unfold upper_integral
  apply le_csInf (integral_bound_upper_nonempty hgbdd)
  intro c hc; simp at hc
  obtain ⟨γ, ⟨hmajorγ, hpwconstonγ⟩, hintegγ⟩ := hc
  suffices upper_integral (f + g) I ≤ b + c by linarith
  choose P₁ hP₁ using hpwconstonφ
  choose P₂ hP₂ using hpwconstonγ
  have ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
  set P := P₁ ⊔ P₂
  have hPφ : PiecewiseConstantWith φ P := by exact hP₁.mono h₁
  have hPγ : PiecewiseConstantWith γ P := by exact hP₂.mono h₂
  have hintegdefφ := PiecewiseConstantOn.integ_def hPφ
  have hintegdefγ := PiecewiseConstantOn.integ_def hPγ
  rw [← hintegφ, ← hintegγ, hintegdefφ, hintegdefγ]
  have hmajorφγ : MajorizesOn (φ + γ) (f + g) I := by
    intro x hx
    specialize hmajorφ x hx
    specialize hmajorγ x hx
    simp; linarith
  have hpwconstantwithφγ : PiecewiseConstantWith (φ + γ) P := by exact PiecewiseConstantWith.add hPφ hPγ
  have hpwconstantonφγ : PiecewiseConstantOn (φ + γ) I := by use P
  have hinequality : upper_integral (f + g) I ≤ hpwconstantonφγ.integ' := by
     exact upper_integral_le_integ haddbdd hmajorφγ hpwconstantonφγ
  suffices hpwconstantonφγ.integ' ≤ PiecewiseConstantWith.integ φ P + PiecewiseConstantWith.integ γ P by linarith
  simp only [PiecewiseConstantOn.integ']
  rw [PiecewiseConstantOn.integ_def hpwconstantwithφγ]
  simp only [PiecewiseConstantWith.integ]
  simp_rw [← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hemp : (J:Set ℝ).Nonempty
  . have := BoundedInterval.length_nonneg J
    suffices constant_value_on (φ + γ) J = constant_value_on φ J + constant_value_on γ J by nlinarith
    exact constant_value_on_of_add hJ hemp hPφ hPγ
  . simp [BoundedInterval.length_of_empty hemp]

lemma lower_integral_add_le_add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  lower_integral f I + lower_integral g I ≤ lower_integral (f + g) I := by
  obtain ⟨hfbdd, hfagree⟩ := hf
  obtain ⟨hgbdd, hgagree⟩ := hg
  have haddbdd : BddOn (f + g) I := by exact BddOn.add _ _ _ hfbdd hgbdd
  suffices lower_integral f I ≤ lower_integral (f + g) I - lower_integral g I by linarith
  conv_lhs => unfold lower_integral
  apply csSup_le (integral_bound_lower_nonempty hfbdd)
  intro b hb; simp at hb
  obtain ⟨φ, ⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hb
  suffices lower_integral g I ≤ lower_integral (f + g) I - b by linarith
  conv_lhs => unfold lower_integral
  apply csSup_le (integral_bound_lower_nonempty hgbdd)
  intro c hc; simp at hc
  obtain ⟨γ, ⟨hminorγ, hpwconstonγ⟩, hintegγ⟩ := hc
  suffices b + c ≤  lower_integral (f + g) I  by linarith
  choose P₁ hP₁ using hpwconstonφ
  choose P₂ hP₂ using hpwconstonγ
  have ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
  set P := P₁ ⊔ P₂
  have hPφ : PiecewiseConstantWith φ P := by exact PiecewiseConstantWith.mono h₁ hP₁
  have hPγ : PiecewiseConstantWith γ P := by exact PiecewiseConstantWith.mono h₂ hP₂
  rw [← hintegφ, ← hintegγ, PiecewiseConstantOn.integ_def hPφ, PiecewiseConstantOn.integ_def hPγ]
  have hminorφγ : MinorizesOn (φ + γ) (f + g) I := by
    intro x hx
    specialize hminorφ x hx
    specialize hminorγ x hx
    simp; linarith
  have hpwconstantwithφγ : PiecewiseConstantWith (φ + γ) P := by exact PiecewiseConstantWith.add hPφ hPγ
  have hpwconstantonφγ : PiecewiseConstantOn (φ + γ) I := by use P
  have hinequality : hpwconstantonφγ.integ' ≤ lower_integral (f + g) I := by
    exact integ_le_lower_integral haddbdd hminorφγ hpwconstantonφγ
  suffices PiecewiseConstantWith.integ φ P + PiecewiseConstantWith.integ γ P ≤ hpwconstantonφγ.integ' by linarith
  simp only [PiecewiseConstantOn.integ']
  rw [PiecewiseConstantOn.integ_def hpwconstantwithφγ]
  simp only [PiecewiseConstantWith.integ]
  simp_rw [← Finset.sum_add_distrib, ← add_mul]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hemp : (J : Set ℝ).Nonempty
  . have := BoundedInterval.length_nonneg J
    suffices constant_value_on (φ + γ) J = constant_value_on φ J + constant_value_on γ J by nlinarith
    exact constant_value_on_of_add hJ hemp hPφ hPγ
  . simp [BoundedInterval.length_of_empty hemp]

lemma upper_integral_smul_le_smul_zero {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hc : c = 0):
  upper_integral (c • f) I ≤ c * (lower_integral f I) := by
  subst hc; simp
  have h := upper_integral_le (f:=(0:ℝ → ℝ)) (I:=I) (M:=0) (by simp_all)
  simpa using h

lemma upper_integral_smul_le_smul_pos {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) (hc : 0 < c):
  upper_integral (c • f) I ≤ c * (lower_integral f I) := by
  have ⟨hfbdd, hfagree⟩ := hf
  suffices (1/c) * upper_integral (c • f) I ≤ upper_integral f I by
    field_simp at this
    rwa [hfagree]
  conv_rhs => unfold upper_integral
  apply le_csInf (by exact integral_bound_upper_nonempty hfbdd)
  intro b hb
  choose φ hφ using hb
  simp at hφ; obtain ⟨⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  field_simp
  conv_lhs => unfold upper_integral
  apply csInf_le
  . apply integral_bound_below
    exact BddOn.of_smul hfbdd
  . simp
    use c • φ; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx
      simp; gcongr
      exact hmajorφ x hx
    . exact PiecewiseConstantOn.smul c hpwconstonφ
    . have ⟨P₁, hP₁⟩ := hpwconstonφ
      choose P₂ hP₂ using PiecewiseConstantOn.smul c hpwconstonφ
      obtain ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
      set P := P₁ ⊔ P₂
      have hPφ : PiecewiseConstantWith φ P := by exact PiecewiseConstantWith.mono h₁ hP₁
      have hPcφ : PiecewiseConstantWith (c • φ) P := by exact PiecewiseConstantWith.mono h₂ hP₂
      rw [← hintegφ, PiecewiseConstantOn.integ_def hPφ, PiecewiseConstantOn.integ_def hPcφ]
      simp only [PiecewiseConstantWith.integ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J : Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on (c • φ) J  = c * (constant_value_on φ J) by nlinarith
        exact constant_value_on_of_smul hJ hemp hPφ
      . simp [BoundedInterval.length_of_empty hemp]

lemma upper_integral_smul_le_smul_neg {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) (hc : c < 0):
  upper_integral (c • f) I ≤ c * (lower_integral f I) := by
  have ⟨hfbdd, hfagree⟩ := hf
  suffices lower_integral f I ≤ (upper_integral (c • f) I) / c by
    rw [le_div_iff_of_neg hc] at this
    linarith
  conv_lhs => unfold lower_integral
  apply csSup_le (integral_bound_lower_nonempty hfbdd)
  intro b hb; choose φ hφ using hb
  simp at hφ; obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  suffices upper_integral (c • f) I ≤ c * b by
    rw [le_div_iff_of_neg hc]
    linarith
  conv_lhs => unfold upper_integral
  apply csInf_le
  . apply integral_bound_below
    exact BddOn.of_smul hfbdd
  . simp
    use c • φ; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx; simp
      specialize hminorφ x hx
      nlinarith
    . exact PiecewiseConstantOn.smul c hpwconstonφ
    . have ⟨P₁, hP₁⟩ := hpwconstonφ
      choose P₂ hP₂ using PiecewiseConstantOn.smul c hpwconstonφ
      obtain ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
      set P := P₁ ⊔ P₂
      have hPφ : PiecewiseConstantWith φ P := by exact PiecewiseConstantWith.mono h₁ hP₁
      have hPcφ : PiecewiseConstantWith (c • φ) P := by exact PiecewiseConstantWith.mono h₂ hP₂
      rw [← hintegφ, PiecewiseConstantOn.integ_def hPφ, PiecewiseConstantOn.integ_def hPcφ]
      simp only [PiecewiseConstantWith.integ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J : Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on (c • φ) J  = c * (constant_value_on φ J) by nlinarith
        exact constant_value_on_of_smul hJ hemp hPφ
      . simp [BoundedInterval.length_of_empty hemp]

lemma upper_integral_smul_le_smul {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) :
  upper_integral (c • f) I ≤ c * (lower_integral f I) := by
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  . exact upper_integral_smul_le_smul_neg hf hlt
  . exact upper_integral_smul_le_smul_zero heq
  . exact upper_integral_smul_le_smul_pos hf hgt

lemma lower_integral_smul_le_smul_zero {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hc : c = 0):
  c * (lower_integral f I) ≤ lower_integral (c • f) I := by
  subst hc; simp
  have h := le_lower_integral (f := (0:ℝ → ℝ)) (I:=I) (M := 0) (by simp_all)
  simpa using h

lemma lower_integral_smul_le_smul_pos {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) (hc : 0 < c) :
  c * (lower_integral f I) ≤ lower_integral (c • f) I := by
  obtain ⟨hfbdd, hfagree⟩ := hf
  suffices lower_integral f I ≤ (1/c) * lower_integral (c • f) I by
    field_simp at this
    nlinarith
  conv_lhs => unfold lower_integral
  apply csSup_le (integral_bound_lower_nonempty hfbdd)
  intro b hb; simp at hb
  choose φ hφ using hb
  obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  suffices b * c ≤ lower_integral (c • f) I by field_simp; exact this
  conv_rhs => unfold lower_integral
  apply le_csSup
  . apply integral_bound_above
    exact BddOn.of_smul hfbdd
  . simp
    use c • φ; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx; simp
      gcongr
      exact hminorφ x hx
    . exact PiecewiseConstantOn.smul c hpwconstonφ
    . have ⟨P₁, hP₁⟩ := hpwconstonφ
      choose P₂ hP₂ using PiecewiseConstantOn.smul c hpwconstonφ
      have ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
      set P := P₁ ⊔ P₂
      have hPφ : PiecewiseConstantWith φ P := by exact PiecewiseConstantWith.mono h₁ hP₁
      have hPcφ : PiecewiseConstantWith (c • φ) P := by exact PiecewiseConstantWith.mono h₂ hP₂
      rw [← hintegφ, PiecewiseConstantOn.integ_def hPφ, PiecewiseConstantOn.integ_def hPcφ]
      simp only [PiecewiseConstantWith.integ]
      rw [mul_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J : Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on (c • φ) J  = c * (constant_value_on φ J) by nlinarith
        exact constant_value_on_of_smul hJ hemp hPφ
      . simp [BoundedInterval.length_of_empty hemp]

lemma lower_integral_smul_le_smul_neg {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) (hc : c < 0) :
  c * (lower_integral f I) ≤ lower_integral (c • f) I := by
  obtain ⟨hfbdd, hfagree⟩ := hf
  suffices (lower_integral (c • f) I) / c ≤ upper_integral f I by
    rw [div_le_iff_of_neg hc] at this
    nlinarith
  conv_rhs => unfold upper_integral
  apply le_csInf (integral_bound_upper_nonempty hfbdd)
  intro b hb
  simp at hb
  choose φ hφ using hb
  obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  suffices b * c ≤ lower_integral (c • f) I by
    rwa [div_le_iff_of_neg hc]
  conv_rhs => unfold lower_integral
  apply le_csSup
  . apply integral_bound_above
    exact BddOn.of_smul hfbdd
  . simp
    use c • φ; refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx; simp
      specialize hminorφ x hx
      nlinarith
    . exact PiecewiseConstantOn.smul c hpwconstonφ
    . have ⟨P₁, hP₁⟩ := hpwconstonφ
      choose P₂ hP₂ using PiecewiseConstantOn.smul c hpwconstonφ
      obtain ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
      set P := P₁ ⊔ P₂
      have hPφ : PiecewiseConstantWith φ P := by exact PiecewiseConstantWith.mono h₁ hP₁
      have hPcφ : PiecewiseConstantWith (c • φ) P := by exact PiecewiseConstantWith.mono h₂ hP₂
      rw [← hintegφ, PiecewiseConstantOn.integ_def hPφ, PiecewiseConstantOn.integ_def hPcφ]
      simp only [PiecewiseConstantWith.integ]
      rw [mul_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J : Set ℝ).Nonempty
      . have := BoundedInterval.length_nonneg J
        suffices constant_value_on (c • φ) J  = c * (constant_value_on φ J) by nlinarith
        exact constant_value_on_of_smul hJ hemp hPφ
      . simp [BoundedInterval.length_of_empty hemp]

lemma lower_integral_smul_le_smul {I: BoundedInterval} {c: ℝ} {f : ℝ → ℝ} (hf: IntegrableOn f I) :
  c * (lower_integral f I) ≤ lower_integral (c • f) I := by
  rcases lt_trichotomy c 0 with hlt | heq | hgt
  . exact lower_integral_smul_le_smul_neg hf hlt
  . exact lower_integral_smul_le_smul_zero heq
  . exact lower_integral_smul_le_smul_pos hf hgt


/-- Theorem 11.4.1(a) / Exercise 11.4.1 -/
theorem IntegrableOn.add {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f + g) I ∧ integ (f + g) I = integ f I + integ g I := by
  have ⟨hfbdd, hfagree⟩ := hf
  have ⟨hgbdd, hgagree⟩ := hg
  have haddbdd : BddOn (f + g) I := by exact BddOn.add _ _ _ hfbdd hgbdd
  have hintegrable : IntegrableOn (f + g) I := by
    refine ⟨haddbdd, ?_⟩
    apply le_antisymm (lower_integral_le_upper haddbdd)
    calc _ ≤ upper_integral f I + upper_integral g I := by exact upper_integral_add_le_add hf hg
         _ = lower_integral f I + lower_integral g I := by linarith
         _ ≤ lower_integral (f + g) I                := by exact lower_integral_add_le_add hf hg
  refine ⟨hintegrable, ?_⟩
  obtain ⟨_, hagree⟩ := hintegrable
  unfold integ
  apply le_antisymm
  . exact upper_integral_add_le_add hf hg
  . calc _ = lower_integral f I + lower_integral g I := by linarith
         _ ≤ lower_integral (f + g) I                := by exact lower_integral_add_le_add hf hg
         _ = upper_integral (f + g) I                := by linarith


/-- Theorem 11.4.1(b) / Exercise 11.4.1 -/
theorem IntegrableOn.smul {I: BoundedInterval} (c:ℝ) {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (c • f) I ∧ integ (c • f) I = c * integ f I := by
  have ⟨hfbdd, hfagree⟩ := hf
  have hsmulbdd : BddOn (c • f) I := by
    choose B hB using hfbdd
    use |c| * B
    intro x hx; simp
    specialize hB x hx
    gcongr
  have hintegrable : IntegrableOn (c • f) I := by
    constructor
    . exact hsmulbdd
    . apply le_antisymm (lower_integral_le_upper hsmulbdd)
      calc _ ≤ c * (lower_integral f I) := by exact upper_integral_smul_le_smul hf
         _ ≤ lower_integral (c • f) I := by exact lower_integral_smul_le_smul hf
  refine ⟨hintegrable, ?_⟩
  have ⟨hbdd, hagree⟩ := hintegrable
  unfold integ
  apply le_antisymm
  . rw [← hfagree]
    exact upper_integral_smul_le_smul hf
  . rw [← hfagree, ← hagree]
    exact lower_integral_smul_le_smul hf


theorem IntegrableOn.neg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (-f) I ∧ integ (-f) I = -integ f I := by have := IntegrableOn.smul (-1) hf; aesop

/-- Theorem 11.4.1(c) / Exercise 11.4.1 -/
theorem IntegrableOn.sub {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f - g) I ∧ integ (f - g) I = integ f I - integ g I := by
  have hfg : f - g = f + (-g) := by
    funext x; simp; linarith
  rw [hfg]
  obtain ⟨hg', hginteg'⟩ := IntegrableOn.neg hg
  obtain ⟨hfsubg, hfsubginteg⟩ := IntegrableOn.add hf hg'
  constructor
  . exact hfsubg
  . rwa [hginteg'] at hfsubginteg


/-- Theorem 11.4.1(d) / Exercise 11.4.1 -/
theorem IntegrableOn.nonneg {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) (hf_nonneg: ∀ x ∈ I, 0 ≤ f x) :
  0 ≤ integ f I := by
  have ⟨hfbdd, hfagree⟩ := hf
  unfold integ
  rw [← hfagree]
  unfold lower_integral
  apply le_csSup (integral_bound_above hfbdd)
  simp
  use 0; refine ⟨⟨?_, ?_⟩, ?_⟩
  . intro x hx
    simp; exact hf_nonneg x hx
  . use ⊥
    intro J hJ
    apply ConstantOn.of_const'
  . intro P hP
    simp only [PiecewiseConstantWith.integ]
    apply Finset.sum_eq_zero
    intro I hI
    by_cases! hemp : (I : Set ℝ).Nonempty
    . have : constant_value_on 0 I = 0 := by
        exact ConstantOn.const_eq hemp (by simp_all)
      rw [this]; simp
    . simp [BoundedInterval.length_of_empty hemp]


/-- Theorem 11.4.1(e) / Exercise 11.4.1 -/
theorem IntegrableOn.mono {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (h: MajorizesOn g f I) :
  integ f I ≤ integ g I := by
  have ⟨hfbdd, hfagree⟩ := hf
  have ⟨hgbdd, hgagree⟩ := hg
  unfold integ upper_integral
  apply csInf_le_csInf (integral_bound_below hfbdd) (integral_bound_upper_nonempty hgbdd)
  intro x hx
  choose φ hφ using hx
  simp at hφ ⊢; obtain ⟨⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  use φ; refine ⟨⟨?_, ?_⟩, ?_⟩
  . intro x hx
    specialize h x hx
    specialize hmajorφ x hx
    linarith
  . exact hpwconstonφ
  . exact hintegφ



/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const (c:ℝ) (I: BoundedInterval) :
  IntegrableOn (fun _ ↦ c) I ∧ integ (fun _ ↦ c) I = c * |I|ₗ := by
  have hpw : PiecewiseConstantOn (fun _ => c) I := by
    exact PiecewiseConstantOn.of_const c I
  have ⟨hintegrable, hinteg⟩ := integ_of_piecewise_const hpw
  refine ⟨hintegrable, ?_⟩
  simp only [PiecewiseConstantOn.integ'] at hinteg
  have hpwith : PiecewiseConstantWith (fun x ↦ c) (⊥:Partition I) := by
    intro J hJ
    rw [BoundedInterval.intervals_of_bot'] at hJ
    subst hJ
    exact ConstantOn.of_const' c J
  rw [hinteg, PiecewiseConstantOn.integ_def hpwith]
  simp only [PiecewiseConstantWith.integ]
  rw [BoundedInterval.intervals_of_bot]
  simp only [Finset.sum_singleton]
  by_cases! hemp : (I : Set ℝ).Nonempty
  . have := BoundedInterval.length_nonneg I
    congr
    apply ConstantOn.const_eq hemp
    simp_all
  . simp [BoundedInterval.length_of_empty hemp]



/-- Theorem 11.4.1(f) / Exercise 11.4.1 -/
theorem IntegrableOn.const' {I: BoundedInterval} {f:ℝ → ℝ} (hf: ConstantOn f I) :
  IntegrableOn f I ∧ integ f I = (constant_value_on f I) * |I|ₗ := by
  have hpw : PiecewiseConstantOn f I := by exact ConstantOn.piecewiseConstantOn hf
  have ⟨hintegrable, hinteg⟩ := integ_of_piecewise_const hpw
  refine ⟨hintegrable, ?_⟩
  simp only [PiecewiseConstantOn.integ'] at hinteg
  have hpwith : PiecewiseConstantWith f (⊥:Partition I) := by
    intro J hJ
    rw [BoundedInterval.intervals_of_bot'] at hJ
    subst hJ
    exact hf
  rw [hinteg, PiecewiseConstantOn.integ_def hpwith]
  simp only [PiecewiseConstantWith.integ]
  rw [BoundedInterval.intervals_of_bot]
  simp only [Finset.sum_singleton]

open Classical in
lemma BddOn.of_extend  {I J: BoundedInterval}
  {f: ℝ → ℝ} (h: BddOn f I) : BddOn (fun x ↦ if x ∈ I then f x else 0) J := by
  choose B hB using h
  use max 0 B; intro x hx
  simp
  by_cases! hxI : x ∈ I
  . simp [hxI]; right; exact hB x hxI
  . simp [hxI]

open Classical in
theorem lower_integral_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  lower_integral f I ≤ lower_integral (fun x ↦ if x ∈ I then f x else 0) J := by
  have ⟨hfbdd, hagree⟩ := h
  apply csSup_le (integral_bound_lower_nonempty hfbdd)
  intro b hb; simp at hb
  choose φ hφ using hb
  obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  apply le_csSup (integral_bound_above (BddOn.of_extend hfbdd))
  simp
  use fun x => if x ∈ I then φ x else 0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  . intro x hx; simp
    split_ifs with h
    . exact hminorφ x h
    . rfl
  . exact PiecewiseConstantOn.of_extend hIJ hpwconstonφ
  . rw [← hintegφ]
    exact PiecewiseConstantOn.integ_of_extend hIJ hpwconstonφ

open Classical in
theorem upper_integral_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  upper_integral (fun x ↦ if x ∈ I then f x else 0) J ≤ upper_integral f I := by
  have ⟨hfbdd, hagree⟩ := h
  apply le_csInf (integral_bound_upper_nonempty hfbdd)
  intro b hb; simp at hb
  choose φ hφ using hb
  obtain ⟨⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
  apply csInf_le (integral_bound_below (BddOn.of_extend hfbdd))
  simp
  use fun x => if x ∈ I then φ x else 0
  refine ⟨⟨?_, ?_⟩, ?_⟩
  . intro x hx; simp
    split_ifs with h
    . exact hmajorφ x h
    . rfl
  . exact PiecewiseConstantOn.of_extend hIJ hpwconstonφ
  . rw [← hintegφ]
    exact PiecewiseConstantOn.integ_of_extend hIJ hpwconstonφ

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  IntegrableOn (fun x ↦ if x ∈ I then f x else 0) J := by
  have ⟨hfbdd, hagree⟩ := h
  set g := (fun x ↦ if x ∈ I then f x else 0)
  have hgbdd : BddOn g J := by
    exact BddOn.of_extend hfbdd
  refine ⟨hgbdd, ?_⟩
  apply le_antisymm (lower_integral_le_upper hgbdd)
  calc upper_integral g J  ≤ upper_integral f I := by simpa using upper_integral_of_extend hIJ h
                         _ = lower_integral f I := by linarith
                         _ ≤ lower_integral g J := by simpa using lower_integral_of_extend hIJ h

open Classical in
/-- Theorem 11.4.1 (g)  / Exercise 11.4.1 -/
theorem IntegrableOn.of_extend' {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: IntegrableOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  have ⟨hfbdd, hfagree⟩ := h
  obtain ⟨hbdd, hagree⟩ := IntegrableOn.of_extend hIJ h
  unfold integ
  have hlower := lower_integral_of_extend hIJ h
  have hupper := upper_integral_of_extend hIJ h
  linarith



open Classical in
lemma lower_integral_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) : lower_integral f I + lower_integral f J = lower_integral f K := by
  have ⟨hfbdd, hfagree⟩ := h
  have ⟨hinter, hunion, hlength⟩ := hIJK
  have hIK : (I:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  have hJK : (J:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  apply le_antisymm
  . suffices lower_integral f I ≤ lower_integral f K - lower_integral f J by linarith
    apply csSup_le (integral_bound_lower_nonempty (BddOn.mono hfbdd hIK))
    intro b hb; simp at hb
    choose φ hφ using hb; obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
    suffices lower_integral f J ≤ lower_integral f K - b by linarith
    apply csSup_le (integral_bound_lower_nonempty (BddOn.mono hfbdd hJK))
    intro c hc; simp at hc
    choose γ hγ using hc; obtain ⟨⟨hminorγ, hpwconstonγ⟩, hintegγ⟩ := hγ
    suffices b + c ≤ lower_integral f K by linarith
    apply le_csSup (integral_bound_above hfbdd)
    simp
    use fun x => if x ∈ I then φ x else γ x
    choose P hP using hpwconstonφ
    choose Q hQ using hpwconstonγ
    have hPQ : PiecewiseConstantWith (fun x ↦ if x ∈ I then φ x else γ x) (P.join Q hIJK) := by
      intro ℓ hℓ
      change ℓ ∈ P.intervals ∪ Q.intervals at hℓ; simp at hℓ
      by_cases! hemp : (ℓ:Set ℝ).Nonempty
      . rcases hℓ with hPint | hQint
        . have ⟨x, hx⟩ := hemp
          use φ x; simp
          intro x' hx'
          have hxI : x ∈ I := by
            apply P.contains ℓ hPint
            exact hx
          have hx'I : x' ∈ I := by
            apply P.contains ℓ hPint
            exact hx'
          simp [hx'I]
          specialize hP ℓ hPint
          have h1 := ConstantOn.eq hP hx
          have h2 := ConstantOn.eq hP hx'
          linarith
        . have ⟨x, hx⟩ := hemp
          use γ x; simp
          intro x' hx'
          have hxJ : x ∈ J := by
            apply Q.contains ℓ hQint
            exact hx
          have hx'J : x' ∈ J := by
            apply Q.contains ℓ hQint
            exact hx'
          have hxnI : ¬(x' ∈ I) := by
            intro h'
            refine absurd hinter ?_
            push_neg
            use x'; exact ⟨h', hx'J⟩
          simp [hxnI]
          specialize hQ ℓ hQint
          have h1 := ConstantOn.eq hQ hx
          have h2 := ConstantOn.eq hQ hx'
          linarith
      . have : Subsingleton (ℓ:Set ℝ) := by
          apply (Set.subsingleton_coe _).mpr
          rw [hemp]; exact Set.subsingleton_empty
        exact ConstantOn.of_subsingleton
    refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx; simp
      split_ifs with h
      . apply hminorφ; exact h
      . apply hminorγ
        rw [hunion] at hx
        rw [BoundedInterval.mem_iff] at h
        exact hx.resolve_left h
    .  use P.join Q hIJK
    . rw [← hintegφ, ← hintegγ]
      rw [PiecewiseConstantOn.integ_def hP, PiecewiseConstantOn.integ_def hQ, PiecewiseConstantOn.integ_def hPQ]
      simp only [PiecewiseConstantWith.integ]
      set F : BoundedInterval → ℝ := fun L => (constant_value_on (fun x => if x ∈ I then φ x else γ x) L) * L.length
      have hQandP : ∑ J ∈ P.intervals ∩ Q.intervals, F J = 0 := by
        apply Finset.sum_eq_zero
        intro L hL
        unfold F
        simp at hL
        suffices (L:Set ℝ) = ∅ by
          simp [BoundedInterval.length_of_empty this]
        have hinI : L ⊆ I := by exact P.contains L hL.1
        have hinJ : L ⊆ J := by exact Q.contains L hL.2
        rw [BoundedInterval.subset_iff] at hinI hinJ
        have : (L:Set ℝ) ⊆ (I:Set ℝ) ∩ (J:Set ℝ) := by
          intro x hL; exact ⟨hinI hL, hinJ hL⟩
        rw [hinter] at this
        simpa using this
      have key :  ∑ J ∈ P.intervals ∪ Q.intervals, F J = ∑ J ∈ P.intervals, F J + ∑ J ∈ Q.intervals, F J := by
        have h := Finset.sum_union_inter (s₁:=P.intervals) (s₂:= Q.intervals) (f := F)
        rwa [hQandP, add_zero] at h
      rw [key]
      congr 1
      . apply Finset.sum_congr rfl
        intro L hL; unfold F
        by_cases! hemp : (L:Set ℝ).Nonempty
        . congr 1; apply constant_value_on_congr
          intro x hx
          have hxI : x ∈ I := by
            apply P.contains L hL
            exact hx
          simp [hxI]
        . simp [BoundedInterval.length_of_empty hemp]
      . apply Finset.sum_congr rfl
        intro L hL; unfold F
        by_cases! hemp : (L:Set ℝ).Nonempty
        . congr 1; apply constant_value_on_congr
          intro x hx
          have hxI : ¬ (x ∈ I) := by
            contrapose! hinter
            use x; exact ⟨hinter, Q.contains L hL x hx⟩
          simp [hxI]
        . simp [BoundedInterval.length_of_empty hemp]
  . apply csSup_le (integral_bound_lower_nonempty hfbdd)
    intro b hb; simp at hb
    choose φ hφ using hb; obtain ⟨⟨hminorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
    obtain ⟨hpI, hpJ⟩ := (PiecewiseConstantOn.of_join hIJK _).mp hpwconstonφ
    rw [← hintegφ, PiecewiseConstantOn.integ_of_join hIJK hpwconstonφ]
    gcongr
    . apply integ_le_lower_integral (hg:=hpI) (hf:=BddOn.mono hfbdd hIK)
      intro x hx
      apply hminorφ
      apply hIK
      exact hx
    . apply integ_le_lower_integral (hg:=hpJ) (hf:=BddOn.mono hfbdd hJK)
      intro x hx
      apply hminorφ
      apply hJK
      exact hx

open Classical in
lemma upper_integral_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) : upper_integral f I + upper_integral f J = upper_integral f K := by
  have ⟨hfbdd, hfagree⟩ := h
  have ⟨hinter, hunion, hlength⟩ := hIJK
  have hIK : (I:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  have hJK : (J:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  apply le_antisymm
  . apply le_csInf (integral_bound_upper_nonempty hfbdd)
    intro b hb; simp at hb
    choose φ hφ using hb; obtain ⟨⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
    obtain ⟨hpI, hpJ⟩ := (PiecewiseConstantOn.of_join hIJK _).mp hpwconstonφ
    rw [← hintegφ, PiecewiseConstantOn.integ_of_join hIJK hpwconstonφ]
    gcongr
    . apply upper_integral_le_integ (hf:=BddOn.mono hfbdd hIK) (hg:=hpI)
      intro x hx
      apply hmajorφ
      apply hIK
      exact hx
    . apply upper_integral_le_integ (hf:=BddOn.mono hfbdd hJK) (hg:=hpJ)
      intro x hx
      apply hmajorφ
      apply hJK
      exact hx
  . suffices upper_integral f K - upper_integral f J ≤ upper_integral f I by linarith
    apply le_csInf (integral_bound_upper_nonempty (BddOn.mono hfbdd hIK))
    intro b hb; simp at hb
    choose φ hφ using hb; obtain ⟨⟨hmajorφ, hpwconstonφ⟩, hintegφ⟩ := hφ
    suffices upper_integral f K - b ≤ upper_integral f J by linarith
    apply le_csInf (integral_bound_upper_nonempty (BddOn.mono hfbdd hJK))
    intro c hc; simp at hc
    choose γ hγ using hc; obtain ⟨⟨hmajorγ, hpwconstonγ⟩, hintegγ⟩ := hγ
    suffices upper_integral f K ≤ b + c by linarith
    apply csInf_le (integral_bound_below hfbdd)
    simp
    use fun x => if x ∈ I then φ x else γ x
    choose P hP using hpwconstonφ
    choose Q hQ using hpwconstonγ
    have hPQ : PiecewiseConstantWith (fun x ↦ if x ∈ I then φ x else γ x) (P.join Q hIJK) := by
      intro ℓ hℓ
      change ℓ ∈ P.intervals ∪ Q.intervals at hℓ; simp at hℓ
      by_cases! hemp : (ℓ:Set ℝ).Nonempty
      . rcases hℓ with hPint | hQint
        . have ⟨x, hx⟩ := hemp
          use φ x; simp
          intro x' hx'
          have hxI : x ∈ I := by
            apply P.contains ℓ hPint
            exact hx
          have hx'I : x' ∈ I := by
            apply P.contains ℓ hPint
            exact hx'
          simp [hx'I]
          specialize hP ℓ hPint
          have h1 := ConstantOn.eq hP hx
          have h2 := ConstantOn.eq hP hx'
          linarith
        . have ⟨x, hx⟩ := hemp
          use γ x; simp
          intro x' hx'
          have hxJ : x ∈ J := by
            apply Q.contains ℓ hQint
            exact hx
          have hx'J : x' ∈ J := by
            apply Q.contains ℓ hQint
            exact hx'
          have hxnI : ¬(x' ∈ I) := by
            intro h'
            refine absurd hinter ?_
            push_neg
            use x'; exact ⟨h', hx'J⟩
          simp [hxnI]
          specialize hQ ℓ hQint
          have h1 := ConstantOn.eq hQ hx
          have h2 := ConstantOn.eq hQ hx'
          linarith
      . have : Subsingleton (ℓ:Set ℝ) := by
          apply (Set.subsingleton_coe _).mpr
          rw [hemp]; exact Set.subsingleton_empty
        exact ConstantOn.of_subsingleton
    refine ⟨⟨?_, ?_⟩, ?_⟩
    . intro x hx; simp
      split_ifs with h
      . apply hmajorφ; exact h
      . apply hmajorγ
        rw [hunion] at hx
        rw [BoundedInterval.mem_iff] at h
        exact hx.resolve_left h
    .  use P.join Q hIJK
    . rw [← hintegφ, ← hintegγ]
      rw [PiecewiseConstantOn.integ_def hP, PiecewiseConstantOn.integ_def hQ, PiecewiseConstantOn.integ_def hPQ]
      simp only [PiecewiseConstantWith.integ]
      set F : BoundedInterval → ℝ := fun L => (constant_value_on (fun x => if x ∈ I then φ x else γ x) L) * L.length
      have hQandP : ∑ J ∈ P.intervals ∩ Q.intervals, F J = 0 := by
        apply Finset.sum_eq_zero
        intro L hL
        unfold F
        simp at hL
        suffices (L:Set ℝ) = ∅ by
          simp [BoundedInterval.length_of_empty this]
        have hinI : L ⊆ I := by exact P.contains L hL.1
        have hinJ : L ⊆ J := by exact Q.contains L hL.2
        rw [BoundedInterval.subset_iff] at hinI hinJ
        have : (L:Set ℝ) ⊆ (I:Set ℝ) ∩ (J:Set ℝ) := by
          intro x hL; exact ⟨hinI hL, hinJ hL⟩
        rw [hinter] at this
        simpa using this
      have key :  ∑ J ∈ P.intervals ∪ Q.intervals, F J = ∑ J ∈ P.intervals, F J + ∑ J ∈ Q.intervals, F J := by
        have h := Finset.sum_union_inter (s₁:=P.intervals) (s₂:= Q.intervals) (f := F)
        rwa [hQandP, add_zero] at h
      rw [key]
      congr 1
      . apply Finset.sum_congr rfl
        intro L hL; unfold F
        by_cases! hemp : (L:Set ℝ).Nonempty
        . congr 1; apply constant_value_on_congr
          intro x hx
          have hxI : x ∈ I := by
            apply P.contains L hL
            exact hx
          simp [hxI]
        . simp [BoundedInterval.length_of_empty hemp]
      . apply Finset.sum_congr rfl
        intro L hL; unfold F
        by_cases! hemp : (L:Set ℝ).Nonempty
        . congr 1; apply constant_value_on_congr
          intro x hx
          have hxI : ¬ (x ∈ I) := by
            contrapose! hinter
            use x; exact ⟨hinter, Q.contains L hL x hx⟩
          simp [hxI]
        . simp [BoundedInterval.length_of_empty hemp]


/-- Theorem 11.4.1 (h) (Laws of integration) / Exercise 11.4.1 -/
theorem IntegrableOn.join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: IntegrableOn f K) :
  IntegrableOn f I ∧ IntegrableOn f J ∧ integ f K = integ f I + integ f J := by
  have ⟨hfbdd, hfagree⟩ := h
  have ⟨hinter, hunion, hlength⟩ := hIJK
  have hIK : (I:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  have hJK : (J:Set ℝ) ⊆ (K:Set ℝ) := by
    rw [hunion]; simp
  have hlower : lower_integral f I + lower_integral f J = lower_integral f K := by exact lower_integral_of_join hIJK h
  have hupper : upper_integral f I + upper_integral f J = upper_integral f K := by exact upper_integral_of_join hIJK h
  have hlowerfI : lower_integral f I ≤ upper_integral f I := by
    exact lower_integral_le_upper (BddOn.mono hfbdd hIK)
  have hlowerfJ : lower_integral f J ≤ upper_integral f J := by
    exact lower_integral_le_upper (BddOn.mono hfbdd hJK)
  refine ⟨?_, ?_, ?_⟩
  . refine ⟨BddOn.mono hfbdd hIK  , ?_⟩
    apply le_antisymm hlowerfI
    linarith
  . refine ⟨BddOn.mono hfbdd hJK  , ?_⟩
    apply le_antisymm hlowerfJ
    linarith
  . unfold integ
    linarith

lemma BoundedInterval.exists_join {I J : BoundedInterval} (hJI : J ⊆ I)
    (hJ : (J:Set ℝ).Nonempty) :
    ∃ L M R : BoundedInterval, I.joins L M ∧ M.joins J R := by
    match I, J with
  | Ioo a b, Ioo c d =>
    rw [subset_iff] at hJI; simp only [set_Ioo] at hJI hJ
    have hcd := Set.nonempty_Ioo.mp hJ
    obtain ⟨hac, hdb⟩ := (Set.Ioo_subset_Ioo_iff hcd).mp hJI
    exact ⟨Ioc a c, Ioo c b, Ico d b,
      join_Ioc_Ioo hac (by linarith), join_Ioo_Ico hcd hdb⟩
  | Ioo a b, Ico c d =>
    rw [subset_iff] at hJI; simp only [set_Ioo, set_Ico] at hJI hJ
    have hcd : c < d := Set.nonempty_Ico.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Ioo.mp (hJI (Set.mem_Ico.mpr ⟨le_refl c, hcd⟩))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      exact absurd (Set.mem_Ioo.mp (hJI (Set.mem_Ico.mpr ⟨le_of_lt hcb, h⟩))).2 (lt_irrefl b)
    exact ⟨Ioo a c, Ico c b, Ico d b,
      join_Ioo_Ico hac (by linarith), join_Ico_Ico (by linarith) hdb⟩
  | Ioo a b, Ioc c d =>
    rw [subset_iff] at hJI; simp only [set_Ioo, set_Ioc] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioc.mp hJ
    obtain ⟨had, hdb⟩ := Set.mem_Ioo.mp (hJI (Set.mem_Ioc.mpr ⟨hcd, le_refl d⟩))
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      exact absurd (Set.mem_Ioo.mp (hJI (Set.mem_Ioc.mpr ⟨lt_min h hcd, min_le_right a d⟩))).1
        (not_lt.mpr (min_le_left a d))
    exact ⟨Ioc a c, Ioo c b, Ioo d b,
      join_Ioc_Ioo hac (by linarith), join_Ioc_Ioo (by linarith) hdb⟩
  | Ioo a b, Icc c d =>
    rw [subset_iff] at hJI; simp only [set_Ioo, set_Icc] at hJI hJ
    have hcd : c ≤ d := Set.nonempty_Icc.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Ioo.mp (hJI (Set.mem_Icc.mpr ⟨le_refl c, hcd⟩))
    obtain ⟨had, hdb⟩ := Set.mem_Ioo.mp (hJI (Set.mem_Icc.mpr ⟨hcd, le_refl d⟩))
    exact ⟨Ioo a c, Ico c b, Ioo d b,
      join_Ioo_Ico hac (by linarith), join_Icc_Ioo hcd hdb⟩
  | Ico a b, Ioo c d =>
    rw [subset_iff] at hJI; simp only [set_Ico, set_Ioo] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioo.mp hJ
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      obtain ⟨x, hcx, hxm⟩ := exists_between (lt_min h hcd)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨hcx, lt_of_lt_of_le hxm (min_le_right a d)⟩
      exact absurd (Set.mem_Ico.mp (hJI hx)).1
        (not_le.mpr (lt_of_lt_of_le hxm (min_le_left a d)))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      obtain ⟨x, hmx, hxd⟩ := exists_between (max_lt hcd h)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left c b) hmx, hxd⟩
      exact absurd (Set.mem_Ico.mp (hJI hx)).2
        (not_lt.mpr (le_of_lt (lt_of_le_of_lt (le_max_right c b) hmx)))
    exact ⟨Icc a c, Ioo c b, Ico d b,
      join_Icc_Ioo hac (by linarith), join_Ioo_Ico hcd hdb⟩
  | Ico a b, Ico c d =>
    rw [subset_iff] at hJI; simp only [set_Ico] at hJI hJ
    have hcd := Set.nonempty_Ico.mp hJ
    obtain ⟨hac, hdb⟩ := (Set.Ico_subset_Ico_iff hcd).mp hJI
    exact ⟨Ico a c, Ico c b, Ico d b, join_Ico_Ico hac (by linarith), join_Ico_Ico (by linarith) hdb⟩
  | Ico a b, Ioc c d =>
    rw [subset_iff] at hJI; simp only [set_Ico, set_Ioc] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioc.mp hJ
    obtain ⟨had, hdb⟩ := Set.mem_Ico.mp (hJI (Set.mem_Ioc.mpr ⟨hcd, le_refl d⟩))
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      obtain ⟨x, hcx, hxm⟩ := exists_between (lt_min h hcd)
      have hx : x ∈ Set.Ioc c d :=
        Set.mem_Ioc.mpr ⟨hcx, le_of_lt (lt_of_lt_of_le hxm (min_le_right a d))⟩
      exact absurd (Set.mem_Ico.mp (hJI hx)).1
        (not_le.mpr (lt_of_lt_of_le hxm (min_le_left a d)))
    exact ⟨Icc a c, Ioo c b, Ioo d b,
      join_Icc_Ioo hac (by linarith), join_Ioc_Ioo (by linarith) hdb⟩
  | Ico a b, Icc c d =>
    rw [subset_iff] at hJI; simp only [set_Ico, set_Icc] at hJI hJ
    have hcd : c ≤ d := Set.nonempty_Icc.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Ico.mp (hJI (Set.mem_Icc.mpr ⟨le_refl c, hcd⟩))
    obtain ⟨had, hdb⟩ := Set.mem_Ico.mp (hJI (Set.mem_Icc.mpr ⟨hcd, le_refl d⟩))
    exact ⟨Ico a c, Ico c b, Ioo d b,
      join_Ico_Ico hac (by linarith), join_Icc_Ioo hcd hdb⟩
  | Ioc a b, Ioo c d =>
    rw [subset_iff] at hJI; simp only [set_Ioc, set_Ioo] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioo.mp hJ
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      obtain ⟨x, hcx, hxm⟩ := exists_between (lt_min h hcd)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨hcx, lt_of_lt_of_le hxm (min_le_right a d)⟩
      exact absurd (Set.mem_Ioc.mp (hJI hx)).1
        (not_lt.mpr (le_of_lt (lt_of_lt_of_le hxm (min_le_left a d))))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      obtain ⟨x, hmx, hxd⟩ := exists_between (max_lt hcd h)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left c b) hmx, hxd⟩
      exact absurd (Set.mem_Ioc.mp (hJI hx)).2
        (not_le.mpr (lt_of_le_of_lt (le_max_right c b) hmx))
    exact ⟨Ioc a c, Ioc c b, Icc d b,
      join_Ioc_Ioc hac (by linarith), join_Ioo_Icc hcd hdb⟩
  | Ioc a b, Ico c d =>
    rw [subset_iff] at hJI; simp only [set_Ioc, set_Ico] at hJI hJ
    have hcd : c < d := Set.nonempty_Ico.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Ioc.mp (hJI (Set.mem_Ico.mpr ⟨le_refl c, hcd⟩))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      obtain ⟨x, hmx, hxd⟩ := exists_between (max_lt hcd h)
      have hx : x ∈ Set.Ico c d :=
        Set.mem_Ico.mpr ⟨le_of_lt (lt_of_le_of_lt (le_max_left c b) hmx), hxd⟩
      exact absurd (Set.mem_Ioc.mp (hJI hx)).2
        (not_le.mpr (lt_of_le_of_lt (le_max_right c b) hmx))
    exact ⟨Ioo a c, Icc c b, Icc d b,
      join_Ioo_Icc hac hcb, join_Ico_Icc (by linarith) hdb⟩
  | Ioc a b, Ioc c d =>
    rw [subset_iff] at hJI; simp only [set_Ioc] at hJI hJ
    have hcd := Set.nonempty_Ioc.mp hJ
    obtain ⟨hdb, hac⟩ := (Set.Ioc_subset_Ioc_iff hcd).mp hJI
    exact ⟨Ioc a c, Ioc c b, Ioc d b, join_Ioc_Ioc hac (by linarith), join_Ioc_Ioc (by linarith) hdb⟩
  | Ioc a b, Icc c d =>
    rw [subset_iff] at hJI; simp only [set_Ioc, set_Icc] at hJI hJ
    have hcd : c ≤ d := Set.nonempty_Icc.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Ioc.mp (hJI (Set.mem_Icc.mpr ⟨le_refl c, hcd⟩))
    obtain ⟨had, hdb⟩ := Set.mem_Ioc.mp (hJI (Set.mem_Icc.mpr ⟨hcd, le_refl d⟩))
    exact ⟨Ioo a c, Icc c b, Ioc d b,
      join_Ioo_Icc hac hcb, join_Icc_Ioc hcd hdb⟩
  | Icc a b, Ioo c d =>
    rw [subset_iff] at hJI; simp only [set_Icc, set_Ioo] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioo.mp hJ
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      obtain ⟨x, hcx, hxm⟩ := exists_between (lt_min h hcd)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨hcx, lt_of_lt_of_le hxm (min_le_right a d)⟩
      exact absurd (Set.mem_Icc.mp (hJI hx)).1
        (not_le.mpr (lt_of_lt_of_le hxm (min_le_left a d)))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      obtain ⟨x, hmx, hxd⟩ := exists_between (max_lt hcd h)
      have hx : x ∈ Set.Ioo c d :=
        Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left c b) hmx, hxd⟩
      exact absurd (Set.mem_Icc.mp (hJI hx)).2
        (not_le.mpr (lt_of_le_of_lt (le_max_right c b) hmx))
    exact ⟨Icc a c, Ioc c b, Icc d b,
      join_Icc_Ioc hac (by linarith), join_Ioo_Icc hcd hdb⟩
  | Icc a b, Ico c d =>
    rw [subset_iff] at hJI; simp only [set_Icc, set_Ico] at hJI hJ
    have hcd : c < d := Set.nonempty_Ico.mp hJ
    obtain ⟨hac, hcb⟩ := Set.mem_Icc.mp (hJI (Set.mem_Ico.mpr ⟨le_refl c, hcd⟩))
    have hdb : d ≤ b := by
      by_contra h; push_neg at h
      obtain ⟨x, hmx, hxd⟩ := exists_between (max_lt hcd h)
      have hx : x ∈ Set.Ico c d :=
        Set.mem_Ico.mpr ⟨le_of_lt (lt_of_le_of_lt (le_max_left c b) hmx), hxd⟩
      exact absurd (Set.mem_Icc.mp (hJI hx)).2
        (not_le.mpr (lt_of_le_of_lt (le_max_right c b) hmx))
    exact ⟨Ico a c, Icc c b, Icc d b,
      join_Ico_Icc hac hcb, join_Ico_Icc (by linarith) hdb⟩
  | Icc a b, Ioc c d =>
    rw [subset_iff] at hJI; simp only [set_Icc, set_Ioc] at hJI hJ
    have hcd : c < d := Set.nonempty_Ioc.mp hJ
    obtain ⟨had, hdb⟩ := Set.mem_Icc.mp (hJI (Set.mem_Ioc.mpr ⟨hcd, le_refl d⟩))
    have hac : a ≤ c := by
      by_contra h; push_neg at h
      obtain ⟨x, hcx, hxm⟩ := exists_between (lt_min h hcd)
      have hx : x ∈ Set.Ioc c d :=
        Set.mem_Ioc.mpr ⟨hcx, le_of_lt (lt_of_lt_of_le hxm (min_le_right a d))⟩
      exact absurd (Set.mem_Icc.mp (hJI hx)).1
        (not_le.mpr (lt_of_lt_of_le hxm (min_le_left a d)))
    exact ⟨Icc a c, Ioc c b, Ioc d b,
      join_Icc_Ioc hac (by linarith), join_Ioc_Ioc (by linarith) hdb⟩
  | Icc a b, Icc c d =>
    rw [subset_iff] at hJI; simp only [set_Icc] at hJI hJ
    have hcd := Set.nonempty_Icc.mp hJ
    obtain ⟨hac, hdb⟩ := (Set.Icc_subset_Icc_iff hcd).mp hJI
    exact ⟨Ico a c, Icc c b, Ioc d b, join_Ico_Icc hac (by linarith), join_Icc_Ioc hcd hdb⟩


/-- A variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.mono' {I J: BoundedInterval} (hIJ: J ⊆ I)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : IntegrableOn f J := by
  by_cases! hJ : (J:Set ℝ).Nonempty
  . obtain ⟨L, M, R, hILM, hMJR⟩ := BoundedInterval.exists_join hIJ hJ
    have hstep1 := IntegrableOn.join hILM h
    have hstep2 := IntegrableOn.join hMJR hstep1.2.1
    exact hstep2.1
  . exact (integ_on_subsingleton (f:=f) (BoundedInterval.length_of_empty hJ)).1


lemma BoundedInterval.exists_joins_of_subsingleton (I : BoundedInterval) :
  ∃ L M R : BoundedInterval, I.joins L M ∧ M.joins (Ioo I.a I.b) R ∧ (L:Set ℝ).Subsingleton ∧ (R:Set ℝ).Subsingleton := by
  by_cases! hab : I.a < I.b
  . have hsub := BoundedInterval.Ioo_subset I
    have hemp : (Ioo I.a I.b: Set ℝ).Nonempty := by
      simp; exact hab
    obtain ⟨L, M, R, hILM, hMJR⟩ := BoundedInterval.exists_join hsub hemp
    use L, M, R;
    have ⟨hLMempty, hLMunion, hLMlength⟩ := hILM
    have ⟨hJRempty, hJRunion, hJRlength⟩ := hMJR
    have hLR : L.length + R.length = 0 := by
      rw [hJRlength] at hLMlength
      rw [show (Ioo I.a I.b).length = I.b - I.a by grind] at hLMlength
      linarith
    have hL := BoundedInterval.length_nonneg L
    have hR := BoundedInterval.length_nonneg R
    refine ⟨hILM, hMJR, ?_, ?_⟩
    . suffices L.length = 0 by
        have hlen := (BoundedInterval.length_of_subsingleton (I:=L)).mpr this
        exact (Set.subsingleton_coe _).mp hlen
      linarith
    . suffices R.length = 0 by
        have hlen := (BoundedInterval.length_of_subsingleton (I:=R)).mpr this
        exact (Set.subsingleton_coe _).mp hlen
      linarith
  . use I, ∅, ∅; refine ⟨?_, ?_, ?_, ?_⟩
    . refine ⟨by simp, by simp, ?_⟩
      change I.length = I.length + (Ioo 0 0).length
      simp
    . refine ⟨by simp, ?_, ?_⟩
      . simp; symm
        exact Set.Ioo_eq_empty_of_le hab
      . change (Ioo 0 0).length = (Ioo I.a I.b).length + (Ioo 0 0).length
        simp; change I.b ≤ I.a; exact hab
    . have hsub := I.subset_Icc; rw [BoundedInterval.subset_iff] at hsub
      intro x hx y hy
      have hx' := hsub hx
      have hy' := hsub hy
      simp only [set_Icc, Set.mem_Icc] at hx' hy'
      linarith
    . simp

/-- A further variant of Theorem 11.4.1(h) that will be useful in later sections. -/
theorem IntegrableOn.eq {I J: BoundedInterval} (hIJ: J ⊆ I)
  (ha: J.a = I.a) (hb: J.b = I.b)
  {f: ℝ → ℝ} (h: IntegrableOn f I) : integ f J = integ f I := by
  by_cases! hab : I.b ≤ I.a
  . have hlenI : I.length = 0 := by
      apply (BoundedInterval.length_of_subsingleton (I:=I)).mp
      simpa using Boundedinterval.subsingleton_of_le hab
    have hlenJ : J.length = 0 := by
      have hab' : J.b ≤ J.a := by linarith
      apply (BoundedInterval.length_of_subsingleton (I:=J)).mp
      simpa using Boundedinterval.subsingleton_of_le hab'
    have hintegI := (integ_on_subsingleton (f:=f) hlenI).2
    have hintegJ := (integ_on_subsingleton (f:=f) hlenJ).2
    rw [hintegI, hintegJ]
  . have hintegI : integ f I = integ f (BoundedInterval.Ioo I.a I.b) := by
      obtain ⟨L, M, R, hILM, hMJR, hLsingle, hRsingle⟩ := BoundedInterval.exists_joins_of_subsingleton I
      have ⟨hintegrableL, hintegrableM, heqI⟩  := IntegrableOn.join hILM h
      have ⟨hintegrableIoo, hintegrableR, heqI'⟩  := IntegrableOn.join hMJR hintegrableM
      have hlenL : L.length = 0 := by
        apply (BoundedInterval.length_of_subsingleton (I:=L)).mp
        simpa using hLsingle
      have hlenR : R.length = 0 := by
        apply (BoundedInterval.length_of_subsingleton (I:=R)).mp
        simpa using hRsingle
      rw [heqI', (integ_on_subsingleton hlenL).2, (integ_on_subsingleton hlenR).2] at heqI
      simpa using heqI
    have hintegJ : integ f J = integ f (BoundedInterval.Ioo J.a J.b) := by
      have h' : IntegrableOn f J := by exact mono' hIJ h
      obtain ⟨L, M, R, hILM, hMJR, hLsingle, hRsingle⟩ := BoundedInterval.exists_joins_of_subsingleton J
      have ⟨hintegrableL, hintegrableM, heqI⟩  := IntegrableOn.join hILM h'
      have ⟨hintegrableIoo, hintegrableR, heqI'⟩  := IntegrableOn.join hMJR hintegrableM
      have hlenL : L.length = 0 := by
        apply (BoundedInterval.length_of_subsingleton (I:=L)).mp
        simpa using hLsingle
      have hlenR : R.length = 0 := by
        apply (BoundedInterval.length_of_subsingleton (I:=R)).mp
        simpa using hRsingle
      rw [heqI', (integ_on_subsingleton hlenL).2, (integ_on_subsingleton hlenR).2] at heqI
      simpa using heqI
    rw [hintegI, hintegJ, ha, hb]

/-- A handy little lemma for "epsilon of room" type arguments -/
lemma nonneg_of_le_const_mul_eps {x C:ℝ} (h: ∀ ε>0, x ≤ C * ε) : x ≤ 0 := by
  by_cases hC: C > 0
  . by_contra!
    specialize h (x/(2*C)) (by positivity); convert_to x ≤ x/2 at h; grind
    linarith
  specialize h 1 ?_ <;> grind

/-- Theorem 11.4.3 (Max and min preserve integrability). -/
theorem IntegrableOn.max {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊔ g) I  := by
  -- This proof is written to follow the structure of the original text.
  unfold IntegrableOn at hf hg
  have hmax_bound : BddOn (f ⊔ g) I := by
    choose M hM using hf.1; choose M' hM' using hg.1
    use M ⊔ M'; peel hM with x hx hM; specialize hM' _ hx
    simp only [Pi.sup_apply]
    exact abs_max_le_max_abs_abs.trans (sup_le_sup hM hM')
  have lower_le_upper : 0 ≤ upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I := by linarith [lower_integral_le_upper hmax_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f ⊔ g) I - lower_integral (f ⊔ g) I ≤ 4*ε := by
    choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I
    by grind)
    choose g' hg'min hg'const hg'int using gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by grind)
    choose f'' hf''max hf''const hf''int using lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε by grind)
    choose g'' hg''max hg''const hg''int using lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by grind)
    set h := (f'' - f') + (g'' - g')
    have hf'_integ := integ_of_piecewise_const hf'const
    have hg'_integ := integ_of_piecewise_const hg'const
    have hf''_integ := integ_of_piecewise_const hf''const
    have hg''_integ := integ_of_piecewise_const hg''const
    have hf''f'_integ := hf''_integ.1.sub hf'_integ.1
    have hg''g'_integ := hg''_integ.1.sub hg'_integ.1
    have hh_IntegrableOn.eq := hf''f'_integ.1.add hg''g'_integ.1
    have hinteg_le : integ h I ≤ 4 * ε := by linarith
    have hf''g''_const := hf''const.max hg''const
    have hf''g''_maj : MajorizesOn (f'' ⊔ g'') (f ⊔ g) I := by
      intro x hx
      specialize hf''max x hx
      specialize hg''max x hx
      by_cases! hfxgx : f x ≤ g x
      . have : (f ⊔ g) x = g x := by
          simp; exact hfxgx
        rw [this]
        simp; right; exact hg''max
      . have : (f ⊔ g) x = f x := by
          simp; linarith
        rw [this]
        simp; left; exact hf''max
    have hf'g'_const := hf'const.max hg'const
    have hf'g'_maj : MinorizesOn (f' ⊔ g') (f ⊔ g) I := by
      intro x hx
      specialize hf'min x hx
      specialize hg'min x hx
      by_cases! hfxgx : f' x ≤ g' x
      . have : (f' ⊔ g') x = g' x := by
          simp; exact hfxgx
        rw [this]
        simp; right; exact hg'min
      . have : (f' ⊔ g') x = f' x := by
          simp; linarith
        rw [this]
        simp; left; exact hf'min
    have hff'g''_ge := upper_integral_le_integ hmax_bound hf''g''_maj hf''g''_const
    have hf'g'_le := integ_le_lower_integral hmax_bound hf'g'_maj hf'g'_const
    have : MinorizesOn (f'' ⊔ g'') (f' ⊔ g' + h) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx; specialize hf''max _ hx; specialize hg''max _ hx
      simp [h]; split_ands <;> linarith [le_max_left (f' x) (g' x), le_max_right (f' x) (g' x)]
    have hf'g'_integ := integ_of_piecewise_const hf'g'_const
    have hf''g''_integ := integ_of_piecewise_const hf''g''_const
    have hf'g'h_integ := hf'g'_integ.1.add hh_IntegrableOn.eq.1
    rw [MinorizesOn.iff] at this
    linarith [hf''g''_integ.1.mono hf'g'h_integ.1 this]
  exact ⟨ hmax_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩



/-- Theorem 11.4.5 / Exercise 11.4.3.  The objective here is to create a shorter proof than the one above.-/
theorem IntegrableOn.min {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f ⊓ g) I  := by
  have hfeq : (f ⊓ g) = f + g - (f ⊔ g) := by
    ext x
    simp; grind
  rw [hfeq]
  have hadd := (IntegrableOn.add hf hg).1
  have hmax := IntegrableOn.max hf hg
  exact (IntegrableOn.sub hadd hmax).1


/-- Corollary 11.4.4 -/
theorem IntegrableOn.abs {I: BoundedInterval} {f:ℝ → ℝ} (hf: IntegrableOn f I) :
  IntegrableOn (abs f) I := by
  have := (IntegrableOn.const 0 I).1
  convert ((hf.max this).sub (hf.min this)).1 using 1
  ext x; obtain h | h := (show f x ≤ 0 ∨ f x ≥ 0 by grind) <;> simp [h]

/-- Theorem 11.4.5 (Products preserve Riemann integrability).
It is convenient to first establish the non-negative case.-/
theorem integ_of_mul_nonneg {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I)
  (hf_nonneg: MajorizesOn f 0 I) (hg_nonneg: MajorizesOn g 0 I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  by_cases hI : (I:Set ℝ).Nonempty
  swap
  . apply (integ_on_subsingleton _).1
    rw [←BoundedInterval.length_of_subsingleton]
    simp_all [Set.not_nonempty_iff_eq_empty]
  unfold IntegrableOn at hf hg
  choose M₁ hM₁ using hf.1
  choose M₂ hM₂ using hg.1
  have hM₁pos : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ hI.some hI.some_mem)
  have hM₂pos : 0 ≤ M₂ := (abs_nonneg _).trans (hM₂ hI.some hI.some_mem)
  have hmul_bound : BddOn (f * g) I := by
    use M₁ * M₂; peel hM₁ with x hx hM₁; specialize hM₂ _ hx
    simp [abs_mul]; apply mul_le_mul hM₁ hM₂ <;> positivity
  have lower_le_upper : 0 ≤ upper_integral (f * g) I - lower_integral (f * g) I := by
    linarith [lower_integral_le_upper hmul_bound]
  have (ε:ℝ) (hε: 0 < ε) : upper_integral (f * g) I - lower_integral (f * g) I ≤ 2*(M₁+M₂)*ε := by
    have : ∃ f', MinorizesOn f' f I ∧ PiecewiseConstantOn f' I ∧ integ f I - ε < PiecewiseConstantOn.integ f' I ∧ MajorizesOn f' 0 I := by
      choose f' hf'min hf'const hf'int using gt_of_lt_lower_integral hf.1 (show integ f I - ε < lower_integral f I by linarith)
      use max f' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hf_nonneg with x hx _; specialize hf'min _ hx; aesop
      . exact hf'const.max hzero
      . apply lt_of_lt_of_le hf'int (hf'const.integ_mono _ (hf'const.max hzero)); simp
      intro _; simp
    choose f' hf'min hf'const hf'int hf'_nonneg using this
    have : ∃ g', MinorizesOn g' g I ∧ PiecewiseConstantOn g' I ∧ integ g I - ε < PiecewiseConstantOn.integ g' I ∧ MajorizesOn g' 0 I := by
      obtain ⟨ g', hg'min, hg'const, hg'int ⟩ := gt_of_lt_lower_integral hg.1 (show integ g I - ε < lower_integral g I by linarith)
      use max g' 0
      have hzero := (ConstantOn.of_const' 0 I).piecewiseConstantOn
      split_ands
      . peel hg_nonneg with x hx _; specialize hg'min _ hx; aesop
      . exact hg'const.max hzero
      . apply lt_of_lt_of_le hg'int (hg'const.integ_mono _ (hg'const.max hzero)); simp
      intro _; simp
    choose g' hg'min hg'const hg'int hg'_nonneg using this
    have : ∃ f'', MajorizesOn f'' f I ∧ PiecewiseConstantOn f'' I ∧ PiecewiseConstantOn.integ f'' I < integ f I + ε ∧ MinorizesOn f'' (fun _ ↦ M₁) I := by
      obtain ⟨ f'', hf''maj, hf''const, hf''int ⟩ := lt_of_gt_upper_integral hf.1 (show upper_integral f I < integ f I + ε  by linarith)
      use min f'' (fun _ ↦ M₁)
      have hM₁_piece := (ConstantOn.of_const' M₁ I).piecewiseConstantOn
      split_ands
      . peel hM₁ with x hx hM₁; rw [abs_le'] at hM₁
        simp [hf''maj _ hx, hM₁.1]
      . exact hf''const.min hM₁_piece
      . apply lt_of_le_of_lt ((hf''const.min hM₁_piece).integ_mono _ hf''const) hf''int
        simp
      intro _; simp
    choose f'' hf''maj hf''const hf''int hf''bound using this
    have : ∃ g'', MajorizesOn g'' g I ∧ PiecewiseConstantOn g'' I ∧ PiecewiseConstantOn.integ g'' I < integ g I + ε ∧ MinorizesOn g'' (fun _ ↦ M₂) I := by
      obtain ⟨ g'', hg''maj, hg''const, hg''int ⟩ := lt_of_gt_upper_integral hg.1 (show upper_integral g I < integ g I + ε by linarith)
      use min g'' (fun _ ↦ M₂)
      have hM₂_piece := (ConstantOn.of_const' M₂ I).piecewiseConstantOn
      split_ands
      . peel hM₂ with x hx hM₂; rw [abs_le'] at hM₂
        simp [hg''maj _ hx, hM₂.1]
      . exact hg''const.min hM₂_piece
      . apply lt_of_le_of_lt ((hg''const.min hM₂_piece).integ_mono _ hg''const) hg''int
        simp
      intro _ _; simp
    choose g'' hg''maj hg''const hg''int hg''bound using this
    have hf'g'_const := hf'const.mul hg'const
    have hf'g'_maj : MinorizesOn (f' * g') (f * g) I := by
      peel hf'min with x hx hf'min; specialize hg'min _ hx;
      specialize hf'_nonneg _ hx; specialize hg'_nonneg _ hx
      simp at *; apply mul_le_mul hf'min hg'min <;> grind
    have hf''g''_const := hf''const.mul hg''const
    have hf''g''_maj : MajorizesOn (f'' * g'') (f * g) I := by
      peel hf''maj with x hx hf''maj; specialize hg''maj _ hx
      specialize hg_nonneg _ hx; specialize hf_nonneg _ hx
      simp at *; apply mul_le_mul hf''maj hg''maj <;> grind
    have hupper_le := upper_integral_le_integ hmul_bound hf''g''_maj hf''g''_const
    have hlower_ge := integ_le_lower_integral hmul_bound hf'g'_maj hf'g'_const
    have hh_const := hf''g''_const.sub hf'g'_const
    have hh_integ := hf''g''_const.integ_sub hf'g'_const
    have hhmin : MinorizesOn (f'' * g'' - f' * g') (M₁ • (g''-g') + M₂ • (f''-f')) I := by
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        _ = (f'' x) * (g'' x - g' x) + (g' x) * (f'' x - f' x) := by ring
        _ ≤ _ := by gcongr <;> grind
    have hg''g'_const := hg''const.sub hg'const
    have hg''g'_integ := hg''const.integ_sub hg'const
    have hM₁g''g'_const := hg''g'_const.smul M₁
    have hM₁g''g_integ := hg''g'_const.integ_smul M₁
    have hf''f'_const := hf''const.sub hf'const
    have hf''f_integ := hf''const.integ_sub hf'const
    have hM₂f''f'_const := hf''f'_const.smul M₂
    have hM₂f''f_integ := hf''f'_const.integ_smul M₂
    have hsum_const := hM₁g''g'_const.add hM₂f''f'_const
    have hsum_integ := hM₁g''g'_const.integ_add hM₂f''f'_const
    have hsum_bound := hh_const.integ_mono hhmin hsum_const
    calc
      _ ≤ M₁ * PiecewiseConstantOn.integ (g'' - g') I + M₂ * PiecewiseConstantOn.integ (f'' - f') I := by linarith
      _ ≤ M₁ * (2*ε) + M₂ * (2*ε) := by gcongr <;> linarith
      _ = _ := by ring
  exact ⟨ hmul_bound, by linarith [nonneg_of_le_const_mul_eps this] ⟩


theorem integ_of_mul {I: BoundedInterval} {f g:ℝ → ℝ} (hf: IntegrableOn f I) (hg: IntegrableOn g I) :
  IntegrableOn (f * g) I := by
  -- This proof is written to follow the structure of the original text.
  set fplus := max f (fun _ ↦ 0)
  set fminus := -min f (fun _ ↦ 0)
  set gplus := max g (fun _ ↦ 0)
  set gminus := -min g (fun _ ↦ 0)
  have := (IntegrableOn.const 0 I).1
  observe hfplus_integ : IntegrableOn fplus I
  observe hgplus_integ : IntegrableOn gplus I
  have hfminus_integ : IntegrableOn fminus I := (hf.min this).neg.1
  have hgminus_integ : IntegrableOn gminus I := (hg.min this).neg.1
  have hfplus_nonneg : MajorizesOn fplus 0 I := by intro _; simp [fplus]
  have hfminus_nonneg : MajorizesOn fminus 0 I := by intro _; simp [fminus]
  have hgplus_nonneg : MajorizesOn gplus 0 I := by intro _; simp [gplus]
  have hgminus_nonneg : MajorizesOn gminus 0 I := by intro _; simp [gminus]
  have hfplusgplus := integ_of_mul_nonneg hfplus_integ hgplus_integ hfplus_nonneg hgplus_nonneg
  have hfplusgminus := integ_of_mul_nonneg hfplus_integ hgminus_integ hfplus_nonneg hgminus_nonneg
  have hfminusgplus := integ_of_mul_nonneg hfminus_integ hgplus_integ hfminus_nonneg hgplus_nonneg
  have hfminusgminus := integ_of_mul_nonneg hfminus_integ hgminus_integ hfminus_nonneg hgminus_nonneg
  rw [show f = fplus - fminus by ext; simp [fplus, fminus],
      show g = gplus - gminus by ext; simp [gplus, gminus]]
  ring_nf
  exact ((hfplusgplus.add (hfplusgminus.neg.1.sub hfminusgplus).1).1.add hfminusgminus).1
open BoundedInterval

open Classical in
/-- Exercise 11.4.2 -/
theorem IntegrableOn.split {I: BoundedInterval} {f: ℝ → ℝ} (hf: IntegrableOn f I) (P: Partition I) :
  integ f I = ∑ J ∈ P.intervals, integ f J := by
  set φ : BoundedInterval → ℝ → ℝ := fun K x => if x ∈ K then f x else 0
  have hφ : ∀ J ∈ P.intervals, IntegrableOn (φ J) I := by
    intro J hJ
    unfold φ
    apply IntegrableOn.of_extend (P.contains J hJ)
    apply IntegrableOn.mono' (h:=hf)
    exact P.contains J hJ
  have hφ' : ∀ J ∈ P.intervals, integ (φ J) I = integ f J := by
    intro J hJ
    unfold φ
    apply IntegrableOn.of_extend' (P.contains J hJ)
    apply IntegrableOn.mono' (h:=hf)
    exact P.contains J hJ
  have hsplit (S : Finset BoundedInterval) (hS : S ⊆ P.intervals) :
    IntegrableOn (fun x => ∑ J ∈ S, φ J x) I ∧ integ (fun x => ∑ J ∈ S, φ J x) I = ∑ J ∈ S, integ f J := by
    induction S using Finset.induction with
    | empty =>
      have h0 := IntegrableOn.const 0 I
      simp; constructor
      . exact h0.1
      . simpa using h0.2
    | insert J S hnot ih =>
      have hsub : S ⊆ P.intervals := by
        have hsub' : S ⊆ insert J S := by exact Finset.subset_insert J S
        exact hsub'.trans hS
      have hJ : J ∈ P.intervals := by
        apply hS
        exact Finset.mem_insert_self J S
      specialize ih hsub
      specialize hφ J hJ
      specialize hφ' J hJ
      have := IntegrableOn.add hφ ih.1
      constructor
      . simp_rw [Finset.sum_insert hnot]
        convert this.1 using 1
      . simp_rw [Finset.sum_insert hnot]
        convert this.2 using 1
        linarith
  obtain ⟨hintegrable, hinteg⟩ := hsplit P.intervals (by rfl)
  rw [← hinteg]
  apply integ_congr
  intro x hx; simp
  choose J hJ hJuniq using P.exists_unique x hx
  simp at hJ hJuniq
  rw [Finset.sum_eq_single J ?_ ?_]
  . unfold φ
    simp [hJ.2]
  . intro L hL hLJ
    unfold φ
    suffices x ∉ L by simp [this]
    contrapose! hLJ
    exact hJuniq L hL hLJ
  . intro hJ'
    unfold φ
    suffices x ∉ J by simp [this]
    contrapose! hJ'
    exact hJ.1

end Chapter11
