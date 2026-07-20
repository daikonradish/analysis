import Mathlib.Tactic
import Analysis.Section_11_1

/-!
# Analysis I, Section 11.2: Piecewise constant functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Piecewise constant functions.
- The piecewise constant integral.

-/

namespace Chapter11
open BoundedInterval

/-- Definition 11.2.1 -/
abbrev Constant {X Y:Type} (f: X → Y) : Prop := ∃ c, ∀ x, f x = c

open Classical in
noncomputable abbrev constant_value {X Y:Type} [hY: Nonempty Y] (f:X → Y) : Y :=
  if h: Constant f then h.choose else hY.some

theorem Constant.eq {X Y:Type} {f: X → Y} [Nonempty Y] (h: Constant f) (x:X) :
  f x = constant_value f := by simp [constant_value, h]; apply h.choose_spec

theorem Constant.of_const {X Y:Type} {f:X → Y} {c:Y} (h: ∀ x, f x = c) :
  Constant f := by use c

theorem Constant.const_eq {X Y:Type} {f:X → Y} [hX: Nonempty X] [Nonempty Y] {c:Y} (h: ∀ x, f x = c) :
  constant_value f = c := by rw [←eq (of_const h) hX.some, h hX.some]

theorem Constant.of_subsingleton {X Y:Type} [hs: Subsingleton X] [hY: Nonempty Y] {f:X → Y} :
  Constant f := by
  by_cases h:Nonempty X
  . use f h.some; intros; congr; exact hs.elim _ h.some
  simp at h; exact ⟨ hY.some, h.elim ⟩

abbrev ConstantOn (f: ℝ → ℝ) (X: Set ℝ) : Prop := Constant (fun x : X ↦ f ↑x)

noncomputable abbrev constant_value_on (f:ℝ → ℝ) (X: Set ℝ) : ℝ := constant_value (fun x : X ↦ f ↑x)

theorem ConstantOn.eq {f: ℝ → ℝ} {X: Set ℝ} (h: ConstantOn f X) {x:ℝ} (hx: x ∈ X) :
  f x = constant_value_on f X := by
  convert Constant.eq h ⟨ _, hx ⟩

theorem ConstantOn.of_const {f:ℝ → ℝ} {X: Set ℝ} {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  ConstantOn f X := ⟨ c, by grind ⟩

theorem ConstantOn.of_const' (c:ℝ) (X:Set ℝ): ConstantOn (fun _ ↦ c) X := of_const (c := c) (by simp)

theorem ConstantOn.const_eq {f:ℝ → ℝ} {X: Set ℝ} (hX: X.Nonempty) {c:ℝ} (h: ∀ x ∈ X, f x = c) :
  constant_value_on f X = c := by
    rw [←eq (of_const h) hX.some_mem, h _ hX.some_mem]

theorem ConstantOn.congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) : ConstantOn f X ↔ ConstantOn g X := by
  simp_rw [ConstantOn, iff_iff_eq]; congr; grind

theorem ConstantOn.congr' {f g: ℝ → ℝ} {X: Set ℝ} (hf: ConstantOn f X) (h: ∀ x ∈ X, f x = g x) : ConstantOn g X := (congr h).mp hf

theorem ConstantOn.of_subsingleton {f: ℝ → ℝ} {X: Set ℝ} [Subsingleton X] :
  ConstantOn f X := Constant.of_subsingleton

theorem constant_value_on_congr {f g: ℝ → ℝ} {X: Set ℝ} (h: ∀ x ∈ X, f x = g x) :
  constant_value_on f X = constant_value_on g X := by
  simp [constant_value_on]; congr; grind

/-- Definition 11.2.3 (Piecewise constant functions I) -/
abbrev PiecewiseConstantWith (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) : Prop := ∀ J ∈ P, ConstantOn f (J:Set ℝ)

theorem PiecewiseConstantWith.def (f:ℝ → ℝ) {I: BoundedInterval} {P: Partition I} :
  PiecewiseConstantWith f P ↔ ∀ J ∈ P, ∃ c, ∀ x ∈ J, f x = c := by
    simp [PiecewiseConstantWith, ConstantOn, Constant, mem_iff]

theorem PiecewiseConstantWith.congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantWith f P ↔ PiecewiseConstantWith g P := by
  simp [PiecewiseConstantWith]; peel with J hJ
  apply ConstantOn.congr; have := P.contains _ hJ; grind [subset_iff]

/-- Definition 11.2.5 (Piecewise constant functions I) -/
abbrev PiecewiseConstantOn (f:ℝ → ℝ) (I: BoundedInterval) : Prop := ∃ P : Partition I, PiecewiseConstantWith f P

theorem PiecewiseConstantOn.def (f:ℝ → ℝ) (I: BoundedInterval):
  PiecewiseConstantOn f I ↔ ∃ P : Partition I, ∀ J ∈ P, ConstantOn f (J:Set ℝ) := by rfl

theorem PiecewiseConstantOn.congr {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), f x = g x) :
  PiecewiseConstantOn f I ↔ PiecewiseConstantOn g I := by
  simp_rw [PiecewiseConstantOn, PiecewiseConstantWith.congr h]

theorem PiecewiseConstantOn.congr' {f g: ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I) (h: ∀ x ∈ (I:Set ℝ), f x = g x) : PiecewiseConstantOn g I := (congr h).mp hf

/-- Example 11.2.4 / Example 11.2.6 -/
noncomputable abbrev f_11_2_4 : ℝ → ℝ := fun x ↦
  if x < 1 then 0 else  -- junk value
    if x < 3 then 7 else
      if x = 3 then 4 else
        if x < 6 then 5 else
          if x = 6 then 2 else
            0 -- junk value

example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6} ?_ ?_
  . intro J hJ
    change J ∈ ({Ico 1 3, Icc 3 3, Ioo 3 6, Icc 6 6}:Finset BoundedInterval) at hJ
    simp at hJ; rcases hJ with h | h | h | h
    all_goals
      subst h; unfold f_11_2_4; simp
    . apply ConstantOn.congr' (f:= fun x => 7)
      . apply ConstantOn.of_const'
      . intro x hx; simp at hx
        simp [hx]
    . apply ConstantOn.of_subsingleton
    . apply ConstantOn.congr' (f:= fun x => 5)
      . apply ConstantOn.of_const'
      . intro x hx; simp at hx
        simp [hx]
        split_ifs <;> linarith
    . apply ConstantOn.of_subsingleton
  . intro x hx
    rw [BoundedInterval.mem_iff] at hx; simp at hx
    by_cases hIco13 : x ∈ Set.Ico 1 3
    . use Ico 1 3; simp
      refine ⟨hIco13, ⟨?_, ?_, ?_⟩⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIcc3 : x ∈ Set.Icc 3 3
    . use Icc 3 3; simp
      refine ⟨hIcc3, ⟨?_, ?_, ?_⟩⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIoo36 : x ∈ Set.Ioo 3 6
    . use Ioo 3 6; simp
      refine ⟨hIoo36, ⟨?_, ?_, ?_⟩⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIcc66 : x ∈ Set.Icc 6 6
    · use Icc 6 6; simp
      refine ⟨hIcc66, ⟨?_, ?_, ?_⟩⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    exfalso; grind
  . intro J hJ; simp at hJ
    rcases hJ with h | h | h | h
    all_goals
    subst h
    rw [BoundedInterval.subset_iff]; simp
    all_goals grind


example : PiecewiseConstantOn f_11_2_4 (Icc 1 6) := by
  use Partition.mk { Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6} ?_ ?_
  . intro J hJ
    change J ∈ ({ Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 3, Ioo 3 5, Ico 5 6, Icc 6 6}:Finset BoundedInterval) at hJ
    simp at hJ; unfold f_11_2_4
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    . apply ConstantOn.of_const (c:=7)
      intro x hx; simp at hx; grind
    . simp; apply ConstantOn.of_subsingleton
    . apply ConstantOn.of_const (c:=7)
      intro x hx; simp at hx; grind
    . simp; apply ConstantOn.of_subsingleton
    . apply ConstantOn.of_const (c:=5)
      intro x hx; simp at hx; grind
    . apply ConstantOn.of_const (c:=5)
      intro x hx; simp at hx; grind
    . simp; apply ConstantOn.of_subsingleton
  . intro x hx
    rw [BoundedInterval.mem_iff] at hx; simp at hx
    by_cases hIco12 : x ∈ Set.Ico 1 2
    . use Ico 1 2; simp
      refine ⟨hIco12, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIcc22 : x ∈ Set.Icc 2 2
    . use Icc 2 2; simp
      refine ⟨hIcc22, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIoo23 : x ∈ Set.Ioo 2 3
    . use Ioo 2 3; simp
      refine ⟨hIoo23, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIcc3 : x ∈ Set.Icc 3 3
    . use Icc 3 3; simp
      refine ⟨hIcc3, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIoo35 : x ∈ Set.Ioo 3 5
    . use Ioo 3 5; simp
      refine ⟨hIoo35, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIco56 : x ∈ Set.Ico 5 6
    . use Ico 5 6; simp
      refine ⟨hIco56, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    by_cases hIcc66 : x ∈ Set.Icc 6 6
    · use Icc 6 6; simp
      refine ⟨hIcc66, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals rw [BoundedInterval.mem_iff]; simp; grind
    exfalso; grind
  . intro J hJ; simp at hJ
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      rw [BoundedInterval.subset_iff]
      simp
      try linarith
      try grind

/-- Example 11.2.6 -/
theorem ConstantOn.piecewiseConstantOn {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f (I:Set ℝ)) :
  PiecewiseConstantOn f I := by
  use ⊥
  intro K hK
  change K ∈ ({I}:Finset BoundedInterval) at hK
  simp at hK
  subst hK; exact h

/-- Lemma 11.2.7 / Exercise 11.2.1 -/
theorem PiecewiseConstantWith.mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I} (hPP': P ≤ P')
  (hP: PiecewiseConstantWith f P) : PiecewiseConstantWith f P' := by
  intro J' hJ'
  choose J hJ hJ'J using hPP' J' hJ'
  specialize hP J hJ
  choose c hc using hP
  apply ConstantOn.of_const (c:=c)
  intro x hx
  specialize hc ⟨x, by apply hJ'J; exact hx⟩
  simpa using hc


/-- Lemma 11.2.8 / Exercise 11.2.2 (add). -/
theorem PiecewiseConstantOn.add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f + g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=c₁+c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]

/-- Lemma 11.2.8 / Exercise 11.2.2 (sub). -/
theorem PiecewiseConstantOn.sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f - g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=c₁-c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]

/-- Lemma 11.2.8 / Exercise 11.2.2 (max). -/
theorem PiecewiseConstantOn.max {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (max f g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=Max.max c₁ c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]

/-- Lemma 11.2.8 / Exercise 11.2.2 (min). -/
theorem PiecewiseConstantOn.min {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (min f g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=Min.min c₁ c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]

/-- Lemma 11.2.8 / Exercise 11.2.2 (mul). -/
theorem PiecewiseConstantOn.mul {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) : PiecewiseConstantOn (f * g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=c₁*c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]

/-- Lemma 11.2.8 / Exercise 11.2.2 (smul). -/
theorem PiecewiseConstantOn.smul {f: ℝ → ℝ} {I: BoundedInterval}
  (c:ℝ) (hf: PiecewiseConstantOn f I) : PiecewiseConstantOn (c • f) I := by
  choose P hP using hf
  use P
  intro J hJ
  choose k hk using hP J hJ
  apply ConstantOn.of_const (c:=c * k)
  intro x hx
  specialize hk ⟨x, hx⟩
  simp at hk ⊢
  left; exact hk


/-- Lemma 11.2.8 / Exercise 11.2.2 (div). -/
theorem PiecewiseConstantOn.div {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) (hg_ne : ∀ x ∈ I.toSet, g x ≠ 0) :
  PiecewiseConstantOn (f / g) I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  use P₁ ⊔ P₂
  intro J hJ
  have ⟨hleP₁, hleP₂⟩ := BoundedInterval.le_max P₁ P₂
  choose J₁ hJ₁ hJsub₁ using hleP₁ J hJ
  choose J₂ hJ₂ hJsub₂ using hleP₂ J hJ
  choose c₁ hc₁ using hP₁ J₁ hJ₁
  choose c₂ hc₂ using hP₂ J₂ hJ₂
  apply ConstantOn.of_const (c:=c₁/c₂)
  intro x hx
  specialize hc₁ ⟨x, by apply hJsub₁; exact hx⟩
  specialize hc₂ ⟨x, by apply hJsub₂; exact hx⟩
  simp at hc₁ hc₂ ⊢
  rw [hc₁, hc₂]


/-- Definition 11.2.9 (Piecewise constant integral I). -/
noncomputable abbrev PiecewiseConstantWith.integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I)  :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * |J|ₗ

theorem PiecewiseConstantWith.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f P = integ g P := by
  apply Finset.sum_congr rfl; intro J hJ; congr 1; apply constant_value_on_congr
  have := P.contains _ hJ; grind [subset_iff]

/-- Example 11.2.12 -/
noncomputable abbrev f_11_2_12 : ℝ → ℝ := fun x ↦
    if x < 3 then 2 else
      if x = 3 then 4 else
        6

noncomputable abbrev P_11_2_12 : Partition (Icc 1 4) :=
  ((⊥: Partition (Ico 1 3)).join (⊥ : Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))

private lemma piecewiseconstantwithf11212 : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  intro J hJ
  change J ∈ P_11_2_12.intervals at hJ
  unfold P_11_2_12 at hJ; simp at hJ
  unfold f_11_2_12
  rcases hJ with rfl | rfl | rfl
  . apply ConstantOn.of_const (c:=2)
    intro x hx; simp at hx
    simp [hx]
  . simp; apply ConstantOn.of_subsingleton
  . apply ConstantOn.of_const (c:=6)
    intro x hx; simp at hx
    rw [if_neg (by linarith), if_neg (by linarith)]

example : PiecewiseConstantWith f_11_2_12 P_11_2_12 := by
  exact piecewiseconstantwithf11212

private lemma piecewiseconstantwithintegf11212 : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  unfold PiecewiseConstantWith.integ
  have hPint : P_11_2_12.intervals = ({Ico 1 3, Icc 3 3, Ioc 3 4}: Finset BoundedInterval) := by
    unfold P_11_2_12; simp
  rw [hPint]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  have h1 : (Ico 1 3).length = 2 := by simp [BoundedInterval.a, BoundedInterval.b]; norm_num
  have h2 : (Icc 3 3).length = 0 := by simp [BoundedInterval.a, BoundedInterval.b]
  have h3 : (Ioc 3 4).length = 1 := by unfold length; simp [BoundedInterval.a, BoundedInterval.b]; grind
  rw [h1, h2, h3]
  simp only [mul_one, mul_zero]
  ring_nf
  have ha : constant_value_on f_11_2_12 (Ico 1 3 : Set ℝ) = 2 := by
    unfold f_11_2_12; simp
    refine ConstantOn.const_eq ?_ ?_
    . simp
    . intro x hx; simp at hx; simp [hx]
  have hb : constant_value_on f_11_2_12 (Ioc 3 4: Set ℝ) = 6 := by
    unfold f_11_2_12; simp
    refine ConstantOn.const_eq ?_ ?_
    . simp; norm_num
    . intro x hx; simp at hx ⊢
      rw [if_neg (by linarith), if_neg (by linarith)]
  rw [ha, hb]
  norm_num

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12 = 10 := by
  exact piecewiseconstantwithintegf11212

noncomputable abbrev P_11_2_12' : Partition (Icc 1 4) :=
  ((((⊥: Partition (Ico 1 2)).join (⊥ : Partition (Ico 2 3))
  (join_Ico_Ico (by norm_num) (by norm_num) )).join
  (⊥: Partition (Icc 3 3))
  (join_Ico_Icc (by norm_num) (by norm_num))).join
  (⊥: Partition (Ioc 3 4))
  (join_Icc_Ioc (by norm_num) (by norm_num))).add_empty

example : PiecewiseConstantWith f_11_2_12 P_11_2_12' := by
  intro J hJ
  change J ∈ P_11_2_12'.intervals at hJ
  simp at hJ
  unfold f_11_2_12
  rcases hJ with rfl | rfl | rfl | rfl | rfl
  . apply ConstantOn.of_const (c:=2)
    intro x hx; simp at hx
    rw [if_pos (by linarith)]
  . apply ConstantOn.of_const (c:=2)
    intro x hx; simp at hx; simp [hx]
  . simp; apply ConstantOn.of_subsingleton
  . apply ConstantOn.of_const (c:=6)
    intro x hx; simp at hx
    rw [if_neg (by linarith), if_neg (by linarith)]
  . apply ConstantOn.of_const (c:=12029348750293485739)
    intro x hx; simp at hx

example : PiecewiseConstantWith.integ f_11_2_12 P_11_2_12' = 10 := by
  unfold PiecewiseConstantWith.integ
  have hPint : P_11_2_12'.intervals = ({Ico 1 2, Ico 2 3, Icc 3 3, Ioc 3 4, ∅}: Finset BoundedInterval) := by
    unfold P_11_2_12'; simp
  rw [hPint]
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),  Finset.sum_singleton]
  have hnot : (∅ : BoundedInterval).length = 0 := by
    rw [BoundedInterval.length_of_empty _]
    simp
  rw [hnot, mul_zero, add_zero]
  have h1 : (Ico 1 2).length = 1 := by simp [BoundedInterval.a, BoundedInterval.b]; norm_num
  have h2 : (Ico 2 3).length = 1 := by unfold length; simp [BoundedInterval.a, BoundedInterval.b]; grind
  have h3 : (Icc 3 3).length = 0 := by simp [BoundedInterval.a, BoundedInterval.b]
  have h4 : (Ioc 3 4).length = 1 := by unfold length; simp [BoundedInterval.a, BoundedInterval.b]; grind
  rw [h1, h2, h3, h4]
  simp [mul_one, mul_zero]
  have ha : constant_value_on f_11_2_12 (Ico 1 2 : Set ℝ) = 2 := by
    unfold f_11_2_12; simp
    refine ConstantOn.const_eq ?_ ?_
    . simp
    . intro x hx; simp at hx;
      rw [if_pos (by linarith)]
  have hb : constant_value_on f_11_2_12 (Ico 2 3 : Set ℝ) = 2 := by
    unfold f_11_2_12; simp
    refine ConstantOn.const_eq ?_ ?_
    . simp; norm_num
    . intro x hx; simp at hx; simp [hx]
  have hc : constant_value_on f_11_2_12 (Ioc 3 4: Set ℝ) = 6 := by
    unfold f_11_2_12; simp
    refine ConstantOn.const_eq ?_ ?_
    . simp; norm_num
    . intro x hx; simp at hx ⊢
      rw [if_neg (by linarith), if_neg (by linarith)]
  simp at ha hb hc
  rw [ha, hb, hc]
  norm_num


noncomputable def Partition.restrict {I : BoundedInterval} (P' : Partition I)
    {K : BoundedInterval} (hK : K ⊆ I) : Partition K where
  intervals := Finset.image (fun J ↦ K ∩ J) P'.intervals
  exists_unique := by
    intro x hx
    rw [BoundedInterval.subset_iff] at hK
    choose J hJ _ using P'.exists_unique x (hK hx)
    apply ExistsUnique.intro (K ∩ J)
    · simp_all; grind [mem_inter]
    · simp; grind [mem_inter]
  contains := by
    intro L hL; simp at hL
    obtain ⟨J, hJ, rfl⟩ := hL
    rw [BoundedInterval.subset_iff, BoundedInterval.inter_eq]
    exact Set.inter_subset_left


theorem Partition.sum_length_restrict {I : BoundedInterval} (P' : Partition I)
    {K : BoundedInterval} (hK : K ⊆ I) :
    ∑ J ∈ P'.intervals, |(K ∩ J : BoundedInterval)|ₗ = |K|ₗ := by
  rw [← Partition.sum_of_length K (P'.restrict hK)]
  simp only [Partition.restrict]
  rw [Finset.sum_comp BoundedInterval.length (fun J => K ∩ J)]
  apply Finset.sum_congr rfl
  intro A hA; simp at hA
  choose B hBP' hKB using hA
  by_cases hempty : (A:Set ℝ) = ∅
  . simp [BoundedInterval.length_of_empty hempty]
  . push_neg at hempty
    suffices {a ∈ P'.intervals | K ∩ a = A}.card = 1 by
      rw [this]; simp
    choose p hp using hempty
    rw [← hKB, BoundedInterval.inter_eq] at hp
    choose L hL hLuniq using P'.exists_unique p (by apply hK; exact hp.1)
    have hinteruniq : {a ∈ P'.intervals | K ∩ a = A} = {B} := by
      specialize hLuniq B ⟨hBP', hp.2⟩
      subst hLuniq
      ext B'; simp; constructor
      . intro h
        have h' : p ∈ B' := by
          rw [← BoundedInterval.inter_eq, hKB, ← h.2, BoundedInterval.inter_eq] at hp
          exact hp.2
        choose Z hZ huniq using P'.exists_unique p (by apply hK; exact hp.1); simp at huniq
        have h1 := huniq B hBP' hL.2
        have h2 := huniq B' h.1 h'
        subst h1 h2
        rfl
      . intro h; subst h
        exact ⟨hL.1, hKB⟩
    rw [hinteruniq]
    simp


theorem PiecewiseConstantWith.integ_mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hPP' : P ≤ P') : integ f P = integ f P' := by
  have hLHS : integ f P = ∑ K ∈ P.intervals, ∑ K' ∈ P'.intervals, constant_value_on f K * |(K ∩ K' : BoundedInterval)|ₗ := by
    simp only [PiecewiseConstantWith.integ]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [← Partition.sum_length_restrict P' (P.contains J hJ)]
    rw [Finset.mul_sum]
  have hRHS : integ f P' = ∑ K' ∈ P'.intervals, ∑ K ∈ P.intervals, constant_value_on f K' * |(K' ∩ K : BoundedInterval)|ₗ := by
    simp only [PiecewiseConstantWith.integ]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [← Partition.sum_length_restrict P (P'.contains J hJ)]
    rw [Finset.mul_sum]
  rw [hLHS, hRHS]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K hK
  apply Finset.sum_congr rfl
  intro K' hK'
  by_cases! hn : ((K ∩ K'):Set ℝ).Nonempty
  . choose p hp using hn
    have hP' := PiecewiseConstantWith.mono hPP' hP
    choose c hc using hP K hK
    choose c' hc' using hP' K' hK'
    simp at hc hc'
    have hcc' : c = c' := by
      specialize hc p hp.1
      specialize hc' p hp.2
      rw [hc'] at hc
      exact hc.symm
    subst hcc'
    have hconst := ConstantOn.const_eq (f:=f) (X:=K) (by use p; exact hp.1) hc
    have hconst' := ConstantOn.const_eq (f:=f) (X:=K') (by use p; exact hp.2) hc'
    rw [hconst, hconst', BoundedInterval.length_inter_comm]
  . have hn' := hn; rw [Set.inter_comm] at hn
    rw [← BoundedInterval.inter_eq] at hn hn'
    replace hn := BoundedInterval.length_of_empty hn
    replace hn' := BoundedInterval.length_of_empty hn'
    rw [hn, hn']
    simp

/-- Proposition 11.2.13 (Piecewise constant integral is independent of partition) / Exercise 11.2.3 -/
theorem PiecewiseConstantWith.integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') : integ f P = integ f P' := by
  obtain ⟨h, h'⟩ := BoundedInterval.le_max P P'
  have h1 : integ f P = integ f (P ⊔ P') := by
    apply PiecewiseConstantWith.integ_mono
    . exact hP
    . exact h
  have h2 : integ f P' = integ f (P ⊔ P') := by
    apply PiecewiseConstantWith.integ_mono
    . exact hP'
    . exact h'
  rw [h1, h2]


open Classical in
/-- Definition 11.2.14 (Piecewise constant integral II)  -/
noncomputable abbrev PiecewiseConstantOn.integ (f:ℝ → ℝ) (I: BoundedInterval) :
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.integ f h.choose else 0

noncomputable abbrev PiecewiseConstantOn.integ' {f:ℝ → ℝ} {I: BoundedInterval} (_:PiecewiseConstantOn f I) := integ f I

theorem PiecewiseConstantOn.integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) : integ f I = PiecewiseConstantWith.integ f P := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [integ, h']; exact PiecewiseConstantWith.integ_eq h'.choose_spec h

theorem PiecewiseConstantOn.integ_congr {f g:ℝ → ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), f x = g x) : integ f I = integ g I := by
  by_cases hf : PiecewiseConstantOn f I
  <;> (have hg := hf; rw [congr h] at hg; simp [integ, hf, hg])
  rw [PiecewiseConstantWith.integ_congr h, ←integ_def hg.choose_spec, ←integ_def]
  rw [←PiecewiseConstantWith.congr h]; exact hf.choose_spec

/-- Example 11.2.15 -/
example : PiecewiseConstantOn.integ f_11_2_12 (Icc 1 4) = 10 := by
  have := PiecewiseConstantOn.integ_def piecewiseconstantwithf11212
  have := piecewiseconstantwithintegf11212
  linarith


/-- Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f + g) I = integ f I + integ g I := by
  have hadd := PiecewiseConstantOn.add hf hg
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  choose P₃ hP₃ using hadd
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  obtain ⟨h3, h4⟩ := BoundedInterval.le_max P₃ Q
  set R := P₃ ⊔ Q
  have hfR : PiecewiseConstantWith f R :=  by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₁)
  have hgR : PiecewiseConstantWith g R :=  by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₂)
  have haddR : PiecewiseConstantWith (f+g) R := by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₃)
  have hfinteg := PiecewiseConstantOn.integ_def (f:=f) (P:=R) (h:=hfR)
  have hginteg := PiecewiseConstantOn.integ_def (f:=g) (P:=R) (h:=hgR)
  have haddinteg := PiecewiseConstantOn.integ_def (f:=(f+g)) (P:=R) (h:=haddR)
  rw [hfinteg, hginteg, haddinteg]
  simp only [PiecewiseConstantWith.integ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  choose c₁ hc₁ using (PiecewiseConstantWith.def f).mp hfR J hJ
  choose c₂ hc₂ using (PiecewiseConstantWith.def g).mp hgR J hJ
  choose c₃ hc₃ using (PiecewiseConstantWith.def _).mp haddR J hJ
  by_cases! hJnon : (J:Set ℝ).Nonempty
  . have key : c₃ = c₁ + c₂ := by
      choose x hx using hJnon
      specialize hc₁ x hx
      specialize hc₂ x hx
      specialize hc₃ x hx
      simp at hc₃
      linarith
    have h₁ := ConstantOn.const_eq (f:=f) (c:=c₁) hJnon hc₁
    have h₂ := ConstantOn.const_eq (f:=g) (c:=c₂) hJnon hc₂
    have h₃ := ConstantOn.const_eq (f:=(f+g)) (c:=c₃) hJnon hc₃
    rw [h₁, h₂, h₃, key, add_mul]
  . simp [BoundedInterval.length_of_empty hJnon]

/-- Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ) (hf: PiecewiseConstantOn f I) :
  integ (c • f) I = c * integ f I := by
  have hsmul := PiecewiseConstantOn.smul c hf
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hsmul
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  have hfQ : PiecewiseConstantWith f Q := by exact PiecewiseConstantWith.mono (hPP':=h1) hP₁
  have hsmulQ : PiecewiseConstantWith (c • f) Q := by exact PiecewiseConstantWith.mono (hPP':=h2) hP₂
  have hfinteg := PiecewiseConstantOn.integ_def (f:=f) hfQ
  have hsmulinteg := PiecewiseConstantOn.integ_def (f:=(c • f)) hsmulQ
  rw [hfinteg, hsmulinteg]
  simp only [PiecewiseConstantWith.integ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  choose c₁ hc₁ using (PiecewiseConstantWith.def f).mp hfQ J hJ
  choose c₂ hc₂ using (PiecewiseConstantWith.def (c • f)).mp hsmulQ J hJ
  by_cases! hJnon : (J:Set ℝ).Nonempty
  . have key : c * c₁ = c₂ := by
      choose x hx using hJnon
      specialize hc₁ x hx
      specialize hc₂ x hx
      simp at hc₂
      rwa [hc₁] at hc₂
    have h₁ := ConstantOn.const_eq hJnon hc₁
    have h₂ := ConstantOn.const_eq hJnon hc₂
    rw [h₁, h₂, ← mul_assoc, key]
  . simp [BoundedInterval.length_of_empty hJnon]

/-- Theorem 11.2.16 (c) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ (f - g) I = integ f I - integ g I := by
  have hsub := PiecewiseConstantOn.sub hf hg
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  choose P₃ hP₃ using hsub
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  obtain ⟨h3, h4⟩ := BoundedInterval.le_max P₃ Q
  set R := P₃ ⊔ Q
  have hfR : PiecewiseConstantWith f R :=  by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₁)
  have hgR : PiecewiseConstantWith g R :=  by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₂)
  have hsubR : PiecewiseConstantWith (f-g) R := by exact PiecewiseConstantWith.mono (hPP':=by order) (hP:=hP₃)
  have hfinteg := PiecewiseConstantOn.integ_def (f:=f) (P:=R) (h:=hfR)
  have hginteg := PiecewiseConstantOn.integ_def (f:=g) (P:=R) (h:=hgR)
  have hsubinteg := PiecewiseConstantOn.integ_def (f:=(f-g)) (P:=R) (h:=hsubR)
  rw [hfinteg, hginteg, hsubinteg]
  simp only [PiecewiseConstantWith.integ]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  choose c₁ hc₁ using (PiecewiseConstantWith.def f).mp hfR J hJ
  choose c₂ hc₂ using (PiecewiseConstantWith.def g).mp hgR J hJ
  choose c₃ hc₃ using (PiecewiseConstantWith.def _).mp hsubR J hJ
  by_cases! hJnon : (J:Set ℝ).Nonempty
  . have key : c₃ = c₁ - c₂ := by
      choose x hx using hJnon
      specialize hc₁ x hx
      specialize hc₂ x hx
      specialize hc₃ x hx
      simp at hc₃
      linarith
    have h₁ := ConstantOn.const_eq (f:=f) (c:=c₁) hJnon hc₁
    have h₂ := ConstantOn.const_eq (f:=g) (c:=c₂) hJnon hc₂
    have h₃ := ConstantOn.const_eq (f:=(f-g)) (c:=c₃) hJnon hc₃
    rw [h₁, h₂, h₃, key, sub_mul]
  . simp [BoundedInterval.length_of_empty hJnon]


/-- Theorem 11.2.16 (d) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, 0 ≤ f x)
  (hf: PiecewiseConstantOn f I) :
  0 ≤ integ f I := by
  choose P hP using hf
  have hfinteg := PiecewiseConstantOn.integ_def hP
  rw [hfinteg]
  simp only [PiecewiseConstantWith.integ]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases! hJnon : (J:Set ℝ).Nonempty
  . choose c hc using (PiecewiseConstantWith.def f).mp hP J hJ
    have hconstval := ConstantOn.const_eq (f:=f) (c:=c) hJnon hc
    rw [hconstval]
    have hlength : J.length ≥ 0 := by exact BoundedInterval.length_nonneg J
    suffices c ≥ 0 by nlinarith
    choose x hx using hJnon
    specialize hc x hx
    specialize h x (by apply P.contains J hJ; exact hx)
    linarith
  . simp [BoundedInterval.length_of_empty hJnon]

/-- Theorem 11.2.16 (e) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_mono {f g: ℝ → ℝ} {I: BoundedInterval} (h: ∀ x ∈ I, f x ≤ g x)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  integ f I ≤ integ g I := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  have hfQ : PiecewiseConstantWith f Q := by exact PiecewiseConstantWith.mono h1 hP₁
  have hgQ : PiecewiseConstantWith g Q := by exact PiecewiseConstantWith.mono h2 hP₂
  have hfinteg := PiecewiseConstantOn.integ_def hfQ
  have hginteg := PiecewiseConstantOn.integ_def hgQ
  rw [hfinteg, hginteg]
  simp only [PiecewiseConstantWith.integ]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hJnon : (J:Set ℝ).Nonempty
  . choose c₁ hc₁ using (PiecewiseConstantWith.def f).mp hfQ J hJ
    choose c₂ hc₂ using (PiecewiseConstantWith.def g).mp hgQ J hJ
    have hconst₁ := ConstantOn.const_eq hJnon hc₁
    have hconst₂ := ConstantOn.const_eq hJnon hc₂
    rw [hconst₁, hconst₂]
    have hlength : J.length ≥ 0 := by exact BoundedInterval.length_nonneg J
    suffices c₁ ≤ c₂ by nlinarith
    choose x hx using hJnon
    specialize hc₁ x hx
    specialize hc₂ x hx
    specialize h x (by apply Q.contains J hJ; exact hx)
    linarith
  . simp [BoundedInterval.length_of_empty hJnon]



/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const (c: ℝ) (I: BoundedInterval) :
  integ (fun _ ↦ c) I = c * |I|ₗ := by
  set P : Partition I := ⊥
  have hQ : PiecewiseConstantWith (fun _ => c) P := by
    rw [PiecewiseConstantWith.def]
    intro J hJ
    change J ∈ ({I}:Finset BoundedInterval) at hJ
    simp at hJ
    use c; tauto
  have hinteg := PiecewiseConstantOn.integ_def hQ
  rw [hinteg]
  simp only [PiecewiseConstantWith.integ]
  have : P.intervals = {I} := by rfl
  rw [this, Finset.sum_singleton]
  by_cases! hnon : (I:Set ℝ).Nonempty
  . choose c₁ hc₁ using (PiecewiseConstantWith.def _).mp hQ I (by show I ∈ P.intervals; rw [this]; simp)
    have hconst := ConstantOn.const_eq hnon hc₁
    rw [hconst]
    have key : c₁ = c := by
      choose x hx using hnon
      specialize hc₁ x hx
      linarith
    rw [key]
  . simp [BoundedInterval.length_of_empty hnon]

/-- Theorem 11.2.16 (f) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_const' {f:ℝ → ℝ} {I: BoundedInterval} (h: ConstantOn f I) :
  integ f I = (constant_value_on f I) * |I|ₗ := by
  have h' : PiecewiseConstantWith f (⊥: Partition I) := by
    intro J hJ
    change J ∈ ({I}:Finset BoundedInterval) at hJ
    simp at hJ
    subst hJ
    exact h
  rw [integ_def h']
  simp only [PiecewiseConstantWith.integ]
  have : (⊥:Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl
  rw [this, Finset.sum_singleton]


theorem Partition.extend_of_joins {I J L R M : BoundedInterval} (P : Partition I)
    (hjL : M.joins L I) (hjR : J.joins M R)
    (hdL : Disjoint (L : Set ℝ) (I : Set ℝ))
    (hdR : Disjoint (R : Set ℝ) (I : Set ℝ)) :
    ∃ P' : Partition J,
      P.intervals ⊆ P'.intervals ∧
      ∀ K ∈ P'.intervals, K ∈ P.intervals ∨ Disjoint (K : Set ℝ) (I : Set ℝ) := by
  refine ⟨ ((⊥ : Partition L).join P hjL).join (⊥ : Partition R) hjR, ?_, ?_ ⟩
  · intro K hK
    simp only [Partition.intervals_of_bot, Finset.mem_union]
    left; right; exact hK
  · intro K hK
    simp only [Partition.intervals_of_bot, Finset.mem_union, Finset.mem_singleton] at hK
    rcases hK with (rfl | hK) | rfl
    · right; exact hdL
    · left; exact hK
    · right; exact hdR

theorem Partition.exists_extend {I J : BoundedInterval} (hIJ : I ⊆ J) (P : Partition I) :
    ∃ P' : Partition J,
      P.intervals ⊆ P'.intervals ∧
      ∀ K ∈ P'.intervals, K ∈ P.intervals ∨ Disjoint (K : Set ℝ) (I : Set ℝ) := by
  by_cases hne : (I : Set ℝ).Nonempty
  · -- Nonempty `I`: expose the set inclusion, then split on both intervals.
    rw [BoundedInterval.subset_iff] at hIJ
    match I with
    | Ioo a b => match J with
      | Ioo c d =>
        simp at hIJ hne
        have := (Set.Ioo_subset_Ioo_iff hne).mp hIJ
        exact
          extend_of_joins P (M := Ioo c b)
          (join_Ioc_Ioo (by linarith) (by linarith))
          (join_Ioo_Ico (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ioc c d =>
        simp at hIJ hne
        have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
          rw [← closure_Ioo hne.ne]
          exact (closure_mono hIJ).trans (isClosed_Icc.closure_subset_iff.mpr Set.Ioc_subset_Icc_self)
        obtain ⟨hca, hbd⟩ := (Set.Icc_subset_Icc_iff hne.le).mp hIcc
        exact
          extend_of_joins P (M := Ioo c b)
          (join_Ioc_Ioo (by linarith) (by linarith))
          (join_Ioo_Icc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ico c d =>
        simp at hIJ hne
        have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
          rw [← closure_Ioo hne.ne]
          exact (closure_mono hIJ).trans (isClosed_Icc.closure_subset_iff.mpr Set.Ico_subset_Icc_self)
        obtain ⟨hca, hbd⟩ := (Set.Icc_subset_Icc_iff hne.le).mp hIcc
        exact extend_of_joins P (M := Ico c b)
          (join_Icc_Ioo (by linarith) (by linarith))
          (join_Ico_Ico (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Icc c d =>
        simp at hIJ hne
        have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
            rw [← closure_Ioo hne.ne]
            exact isClosed_Icc.closure_subset_iff.mpr hIJ
        obtain ⟨hca, hbd⟩ := (Set.Icc_subset_Icc_iff hne.le).mp hIcc
        exact extend_of_joins P (M := Ico c b)
          (join_Icc_Ioo (by linarith) (by linarith))
          (join_Ico_Icc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
    | Ioc a b => match J with
      | Ioo c d =>
        simp at hIJ hne
        have hbd : b < d := (hIJ ⟨hne, le_rfl⟩).2
        have hca : c ≤ a := ((Set.Ioo_subset_Ioo_iff hne).mp (by have h := interior_mono hIJ; rwa [interior_Ioc, interior_Ioo] at h)).1
        exact extend_of_joins P (M := Ioc c b)
          (join_Ioc_Ioc (by linarith) (by linarith))
          (join_Ioc_Ioo (by linarith) (by linarith))
          (by simp)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ioc c d =>
        simp at hIJ hne
        have := (Set.Ioc_subset_Ioc_iff hne).mp hIJ
        exact extend_of_joins P (M := Ioc c b)
          (join_Ioc_Ioc (by linarith) (by linarith))
          (join_Ioc_Ioc (by linarith) (by linarith))
          (by simp)
          (by simp)
      | Ico c d =>
        simp at hIJ hne
        have hbd : b < d := (hIJ ⟨hne, le_rfl⟩).2
        have hca : c ≤ a := ((Set.Ioo_subset_Ioo_iff hne).mp (by have h := interior_mono hIJ; rwa [interior_Ioc, interior_Ico] at h)).1
        exact extend_of_joins P (M := Icc c b)
          (join_Icc_Ioc (by linarith) (by linarith))
          (join_Icc_Ioo (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Icc c d =>
        simp at hIJ hne
        have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
          rw [← closure_Ioc hne.ne]
          exact isClosed_Icc.closure_subset_iff.mpr hIJ
        obtain ⟨hca, hbd⟩ := (Set.Icc_subset_Icc_iff hne.le).mp hIcc
        exact extend_of_joins P (M := Icc c b)
          (join_Icc_Ioc (by linarith) (by linarith))
          (join_Icc_Ioc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp)
    | Ico a b => match J with
      | Ioo c d =>
        simp at hIJ hne
        have hca : c < a := (hIJ (Set.left_mem_Ico.mpr hne)).1
        have hbd : b ≤ d := by
          have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
            rw [← closure_Ico hne.ne]
            exact (closure_mono hIJ).trans (isClosed_Icc.closure_subset_iff.mpr Set.Ioo_subset_Icc_self)
          exact ((Set.Icc_subset_Icc_iff hne.le).mp hIcc).2
        exact extend_of_joins P (M := Ioo c b)
          (join_Ioo_Ico (by linarith) (by linarith))
          (join_Ioo_Ico (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp)
      | Ioc c d =>
        simp at hIJ hne
        have hca : c < a := (hIJ (Set.left_mem_Ico.mpr hne)).1
        have hbd : b ≤ d := by
          have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
            rw [← closure_Ico hne.ne]
            exact (closure_mono hIJ).trans (isClosed_Icc.closure_subset_iff.mpr Set.Ioc_subset_Icc_self)
          exact ((Set.Icc_subset_Icc_iff hne.le).mp hIcc).2
        exact extend_of_joins P (M := Ioo c b)
          (join_Ioo_Ico (by linarith) (by linarith))
          (join_Ioo_Icc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ico c d =>
        simp at hIJ hne
        have := (Set.Ico_subset_Ico_iff hne).mp hIJ
        exact extend_of_joins P (M := Ico c b)
          (join_Ico_Ico (by linarith) (by linarith))
          (join_Ico_Ico (by linarith) (by linarith))
          (by simp)
          (by simp)
      | Icc c d =>
        simp at hIJ hne;
        have hIcc : Set.Icc a b ⊆ Set.Icc c d := by
          rw [← closure_Ico hne.ne]
          exact isClosed_Icc.closure_subset_iff.mpr hIJ
        obtain ⟨hca, hbd⟩ := (Set.Icc_subset_Icc_iff hne.le).mp hIcc
        exact extend_of_joins P (M := Ico c b)
          (join_Ico_Ico (by linarith) (by linarith))
          (join_Ico_Icc (by linarith) (by linarith))
          (by simp)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
    | Icc a b => match J with
      | Ioo c d =>
        simp at hIJ hne
        have hca : c < a := (hIJ (Set.left_mem_Icc.mpr hne)).1
        have hbd : b < d := (hIJ (Set.right_mem_Icc.mpr hne)).2
        exact extend_of_joins P (M := Ioc c b)
          (join_Ioo_Icc (by linarith) (by linarith))
          (join_Ioc_Ioo (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ioc c d =>
        simp at hIJ hne
        have hca : c < a := (hIJ (Set.left_mem_Icc.mpr hne)).1
        have hbd : b ≤ d := (hIJ (Set.right_mem_Icc.mpr hne)).2
        exact extend_of_joins P (M := Ioc c b)
          (join_Ioo_Icc (by linarith) (by linarith))
          (join_Ioc_Ioc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Ico c d =>
        simp at hIJ hne
        have hca : c ≤ a := (hIJ (Set.left_mem_Icc.mpr hne)).1
        have hbd : b < d := (hIJ (Set.right_mem_Icc.mpr hne)).2
        exact extend_of_joins P (M := Icc c b)
          (join_Ico_Icc (by linarith) (by linarith))
          (join_Icc_Ioo (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
      | Icc c d =>
        simp at hIJ hne
        have := (Set.Icc_subset_Icc_iff hne).mp hIJ
        exact extend_of_joins P (M := Icc c b)
          (join_Ico_Icc (by linarith) (by linarith))
          (join_Icc_Ioc (by linarith) (by linarith))
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
          (by simp; intro X hX hX'; simp at hX hX' ⊢; grind)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    refine ⟨⟨insert J P.intervals, ?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      refine ⟨J, ⟨Finset.mem_insert_self _ _, hx⟩, ?_⟩
      rintro K' ⟨hK'mem, hK'x⟩
      rcases Finset.mem_insert.mp hK'mem with rfl | h
      · rfl
      · exfalso
        have hxK : x ∈ (K' : Set ℝ) := hK'x
        have hxI : x ∈ (I : Set ℝ) := (BoundedInterval.subset_iff _ _).mp (P.contains K' h) hxK
        rw [hne] at hxI
        simp at hxI
    · -- contains: every cell ⊆ J
      intro K hK
      rw [BoundedInterval.subset_iff]
      rcases Finset.mem_insert.mp hK with rfl | h
      · exact Set.Subset.refl _
      · exact ((BoundedInterval.subset_iff _ _).mp (P.contains K h)).trans
              ((BoundedInterval.subset_iff _ _).mp hIJ)
    · -- P.intervals ⊆ insert J P.intervals
      exact Finset.subset_insert _ _
    · -- the disjointness disjunct is automatic since ↑I = ∅
      intro K _
      right
      rw [hne]
      simp




open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  choose P hP using h
  choose P' hPP' hdisj using Partition.exists_extend hIJ P
  use P'
  intro L hL
  specialize hdisj L hL
  rcases hdisj with hinI | hinJ
  . choose c hc using hP L hinI
    simp at hc
    refine ConstantOn.of_const (c:=c) ?_
    intro x hx
    have : x ∈ I := by
      rw [BoundedInterval.mem_iff]
      apply P.contains L hinI
      exact hx
    simp [this]
    exact hc x hx
  . refine ConstantOn.of_const (c:=0) ?_
    intro x hx
    have : x ∉ (I:Set ℝ) := by
      exact Disjoint.notMem_of_mem_left hinJ hx
    rw [if_neg (by exact this)]


open Classical in
/-- Theorem 11.2.16 (g) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) :
  integ (fun x ↦ if x ∈ I then f x else 0) J = integ f I := by
  have hpw := PiecewiseConstantOn.of_extend hIJ h
  choose P₁ hP₁ using hpw
  choose P₂ hP₂ hdisj using Partition.exists_extend hIJ ⊥
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set P := P₁ ⊔ P₂
  have hP := hP₁.mono h1
  rw [integ_def hP]
  have hcell : ∀ K ∈ P.intervals, (K:Set ℝ) ⊆ (I:Set ℝ) ∨ Disjoint (K:Set ℝ) (I:Set ℝ) := by
    intro K hK
    choose K' hK' hKK' using h2 K hK
    specialize hdisj K' hK'
    rcases hdisj with hl | hr
    . left
      change K' ∈ ({I}:Finset BoundedInterval) at hl
      simp at hl
      rw [← hl]
      exact hKK'
    . right; intro A hA hA'; simp at hA hA'
      exact hr (hA.trans hKK') hA'
  set Q : Partition I := {
    intervals := P.intervals.filter (fun K => (K:Set ℝ) ⊆ (I:Set ℝ))
    exists_unique := by
      intro x hx
      have hxJ : x ∈ J := ((BoundedInterval.subset_iff I J).mp hIJ) hx
      obtain ⟨K, ⟨hKmem, hxK⟩, hKuniq⟩ := P.exists_unique x hxJ
      have hKI : (K:Set ℝ) ⊆ (I:Set ℝ) := by
        rcases hcell K hKmem with h | h
        · exact h
        · exact absurd hx (Set.disjoint_left.mp h hxK)
      refine ⟨K, ⟨Finset.mem_filter.mpr ⟨hKmem, hKI⟩, hxK⟩, ?_⟩
      rintro K' ⟨hK'f, hxK'⟩
      exact hKuniq K' ⟨(Finset.mem_filter.mp hK'f).1, hxK'⟩
    contains := fun K hK =>
      (BoundedInterval.subset_iff _ _).mpr (Finset.mem_filter.mp hK).2
  }
  have hf : PiecewiseConstantWith f Q := by
    intro K hK
    have hKmem : K ∈ P.intervals := by
      exact (Finset.mem_filter.mp hK).1
    have hKI : (K:Set ℝ) ⊆ (I:Set ℝ) := by
      exact (Finset.mem_filter.mp hK).2
    apply ConstantOn.congr' (hP K hKmem)
    intro x hx
    rw [if_pos (by apply hKI; exact hx)]
  rw [integ_def hf]
  simp only [PiecewiseConstantWith.integ]
  have hQP : Q.intervals ⊆ P.intervals := by
    apply Finset.filter_subset
  have hzero : ∀ x ∈ P.intervals, x ∉ Q.intervals → constant_value_on (fun x ↦ if x ∈ I then f x else 0) ↑x * x.length = 0 := by
    intro K hK hK'
    have hnotsub : ¬ ((K:Set ℝ) ⊆ (I:Set ℝ)) := by
      intro hsub
      exact hK' (by exact Finset.mem_filter.mpr ⟨hK, hsub⟩)
    have hdisjK : Disjoint (K:Set ℝ) (I:Set ℝ) := by
      exact (hcell K hK).resolve_left hnotsub
    by_cases! hne : (K:Set ℝ).Nonempty
    . have h0 : constant_value_on (fun x ↦ if x ∈ I then f x else 0) ↑K = 0 := by
        apply ConstantOn.const_eq hne
        intro x hx
        have : x ∉ (I:Set ℝ) := by
          exact Disjoint.notMem_of_mem_left hdisjK hx
        rw [if_neg (by simpa using this)]
      rw [h0]; simp
    . simp [BoundedInterval.length_of_empty hne]
  rw [← Finset.sum_subset hQP hzero]
  apply Finset.sum_congr rfl
  intro K hK
  have : (K:Set ℝ) ⊆ (I:Set ℝ) := by exact (Finset.mem_filter.mp hK).2
  rw [constant_value_on_congr]
  intro x hx
  rw [if_pos (by apply this; exact hx)]



/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  (f: ℝ → ℝ) : PiecewiseConstantOn f K ↔ PiecewiseConstantOn f I ∧ PiecewiseConstantOn f J := by
  constructor
  . obtain ⟨hdisj, hunion, hlen⟩ := hIJK
    intro hfK
    have hIK : I ⊆ K := by rw [BoundedInterval.subset_iff, hunion]; simp
    have hIJ : J ⊆ K := by rw [BoundedInterval.subset_iff, hunion]; simp
    choose P hP using hfK
    constructor
    . use P.restrict hIK
      intro L' hL'
      change L' ∈ Finset.image (fun J ↦ I ∩ J) P.intervals at hL'
      simp at hL'
      choose L hL hILL' using hL'
      choose c hc using hP L hL; simp at hc
      use c
      simp; intro x hx
      have hx' : x ∈ L := by
        rw [← BoundedInterval.mem_iff, ← hILL', BoundedInterval.mem_iff, BoundedInterval.inter_eq] at hx
        exact hx.2
      exact hc x hx'
    . use P.restrict hIJ
      intro L' hL'
      change L' ∈ Finset.image (fun Z ↦ J ∩ Z) P.intervals at hL'
      simp at hL'
      choose L hL hILL' using hL'
      choose c hc using hP L hL; simp at hc
      use c
      simp; intro x hx
      have hx' : x ∈ L := by
        rw [← BoundedInterval.mem_iff, ← hILL', BoundedInterval.mem_iff, BoundedInterval.inter_eq] at hx
        exact hx.2
      exact hc x hx'
  . rintro ⟨hfI, hfJ⟩
    choose P₁ hP₁ using hfI
    choose P₂ hP₂ using hfJ
    use P₁.join P₂ hIJK
    intro J hJ
    change J ∈ P₁.intervals ∪ P₂.intervals at hJ
    simp at hJ; rcases hJ with h₁ | h₂
    . choose c hc using hP₁ J h₁; simp at hc
      use c; simp; exact hc
    . choose c hc using hP₂ J h₂; simp at hc
      use c; simp; exact hc

/-- Theorem 11.2.16 (h) (Laws of integration) / Exercise 11.2.4 -/
theorem PiecewiseConstantOn.integ_of_join {I J K: BoundedInterval} (hIJK: K.joins I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) :
  integ f K = integ f I + integ f J := by
  obtain ⟨hfI, hfJ⟩ := (PiecewiseConstantOn.of_join hIJK f).mp h
  choose P hP using hfI
  choose Q hQ using hfJ
  have hPQ : PiecewiseConstantWith f (P.join Q hIJK) := by
    intro L hL
    change L  ∈ P.intervals ∪ Q.intervals at hL
    simp at hL; rcases hL with h | h
    . choose c hc using hP L h; simp at hc
      use c; simp; exact hc
    . choose c hc using hQ L h; simp at hc
      use c; simp; exact hc
  rw [PiecewiseConstantOn.integ_def hPQ, PiecewiseConstantOn.integ_def hP, PiecewiseConstantOn.integ_def hQ]
  simp only [PiecewiseConstantWith.integ]
  rw [← Finset.sum_union_inter]
  suffices ∑ x ∈ P.intervals ∩ Q.intervals, constant_value_on f x * x.length = 0 by linarith
  apply Finset.sum_eq_zero
  intro L hL
  rw [Finset.mem_inter] at hL
  have hLemp : (L:Set ℝ) = ∅ := by
    obtain ⟨hdisj, hunion, hlen⟩ := hIJK
    by_contra! h
    choose x hx using h
    have hxI : x ∈ (I:Set ℝ) := by
      apply P.contains L hL.1
      exact hx
    have hxJ : x ∈ (J:Set ℝ) := by
      apply Q.contains L hL.2
      exact hx
    have : ((I:Set ℝ) ∩ (J:Set ℝ)).Nonempty := by use x; exact ⟨hxI, hxJ⟩
    exact absurd this (by exact Set.not_nonempty_iff_eq_empty.mpr hdisj)
  rw [BoundedInterval.length_of_empty hLemp, mul_zero]




end Chapter11
