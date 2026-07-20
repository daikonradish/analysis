import Mathlib.Tactic

/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/

namespace Chapter11

inductive BoundedInterval where
  | Ioo (a b:ℝ) : BoundedInterval
  | Icc (a b:ℝ) : BoundedInterval
  | Ioc (a b:ℝ) : BoundedInterval
  | Ico (a b:ℝ) : BoundedInterval

open BoundedInterval

/-- There is a technical issue in that this coercion is not injective: the empty set is represented by multiple bounded intervals.  This causes some of the statements in this section to be a little uglier than necessary.-/
@[coe]
def BoundedInterval.toSet (I: BoundedInterval) : Set ℝ := match I with
  | Ioo a b => .Ioo a b
  | Icc a b => .Icc a b
  | Ioc a b => .Ioc a b
  | Ico a b => .Ico a b

instance BoundedInterval.inst_coeSet : Coe BoundedInterval (Set ℝ) where
  coe := toSet

instance BoundedInterval.instEmpty : EmptyCollection BoundedInterval where
  emptyCollection := Ioo 0 0

@[simp]
theorem BoundedInterval.coe_empty : ((∅ : BoundedInterval):Set ℝ) = ∅ := by
  simp [toSet]

open Classical in
/-- This is to make {name}`Finset`s of {name}`BoundedInterval`s work properly -/
noncomputable instance BoundedInterval.decidableEq : DecidableEq BoundedInterval := instDecidableEqOfLawfulBEq

@[simp]
theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

-- Definition 11.1.1
#check Set.ordConnected_def

/-- Examples 11.1.3 -/
example : (Set.Icc 1 2 : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx y hy m hm'
  simp at *
  constructor <;> linarith


example : (Set.Ioo 1 2 : Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx y hy m hm'
  simp at *
  constructor <;> linarith

example : ¬(Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ).OrdConnected := by
  intro h
  rw [Set.ordConnected_def] at h
  have h1 : 1 ∈ (Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ) := by
    left
    simp
  have h3 : 3 ∈ (Set.Icc 1 2 ∪ Set.Icc 3 4 : Set ℝ) := by
    right
    simp; linarith
  have h2' : 2.5 ∈ (Set.Icc 1 3 : Set ℝ) := by
    simp; constructor <;> linarith
  specialize h h1 h3 h2'
  simp at h
  rcases h <;> linarith

example : (∅:Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro x hx
  exfalso
  simp at hx

example (x:ℝ) : ({x}: Set ℝ).OrdConnected := by
  rw [Set.ordConnected_def]
  intro a ha b hb m hm
  simp at *
  linarith

/-- Lemma 11.1.4 / Exercise 11.1.1 -/
theorem Bornology.IsBounded.of_boundedInterval (I: BoundedInterval) : Bornology.IsBounded (I:Set ℝ) := by
  match I with
  | Ioo a b => apply Metric.isBounded_Ioo
  | Icc a b => apply Metric.isBounded_Icc
  | Ioc a b => apply Metric.isBounded_Ioc
  | Ico a b => apply Metric.isBounded_Ico

theorem BoundedInterval.ordConnected_iff (X:Set ℝ) : Bornology.IsBounded X ∧ X.OrdConnected ↔ ∃ I: BoundedInterval, X = I := by
  constructor
  . rintro ⟨hbdd, hconn⟩
    rcases X.eq_empty_or_nonempty with hempty | hnonempty
    . use ∅; simp; exact hempty
    choose hl hr using isBounded_iff_bddBelow_bddAbove.mp hbdd
    set a := sInf X
    set b := sSup X
    have hab : a ≤ b := by
      unfold a b
      exact Real.sInf_le_sSup X hl hr
    have hXinab : X ⊆ Set.Icc a b := by
      intro x hx
      simp; constructor
      . unfold a; apply csInf_le
        · exact hl
        . exact hx
      . unfold b; apply le_csSup
        . exact hr
        . exact hx
    have habinX : Set.Ioo a b ⊆ X := by
      intro x hx
      simp at hx
      -- a < n < x
      choose n hn using exists_lt_of_csInf_lt hnonempty hx.1
      -- x < m < b
      choose m hm using exists_lt_of_lt_csSup hnonempty hx.2
      rw [Set.ordConnected_iff] at hconn
      specialize hconn n hn.1 m hm.1 (by linarith)
      apply hconn
      exact ⟨by linarith, by linarith⟩
    by_cases! haX : a ∈ X <;> by_cases hbX : b ∈ X
    . use Icc a b; simp
      apply Set.Subset.antisymm
      . exact hXinab
      . rintro x ⟨h1, h2⟩
        rcases h1.eq_or_lt with hax | hax'
        · subst hax; exact haX
        . rcases h2.eq_or_lt with hbx | hbx'
          . subst hbx; exact hbX
          . apply habinX; constructor <;> linarith
    . use Ico a b; simp
      apply Set.Subset.antisymm
      . intro x hx; simp
        constructor
        . exact csInf_le hl hx
        . have hle := le_csSup hr hx
          unfold b
          suffices x ≠ b by exact lt_of_le_of_ne hle this
          intro h'
          subst h'
          exact hbX hx
      . have : Set.Ioo a b ∪ {a} = Set.Ico a b := by
          apply Set.Ioo_union_left
          rcases hab.eq_or_lt with hab' | hab'
          . exact absurd haX (by rwa [hab'])
          . exact hab'
        rw [← this]
        refine Set.union_subset habinX ?_
        simp; exact haX
    . use Ioc a b; simp
      apply Set.Subset.antisymm
      . intro x hx; simp
        constructor
        . have hle := csInf_le hl hx
          unfold a
          suffices x ≠ a by exact lt_of_le_of_ne hle this.symm
          intro h'
          subst h'
          exact haX hx
        . exact le_csSup hr hx
      · have : Set.Ioo a b ∪ {b} = Set.Ioc a b := by
          apply Set.Ioo_union_right
          rcases hab.eq_or_lt with hab' | hab'
          . exact absurd hbX (by rwa [← hab'])
          . exact hab'
        rw [← this]
        refine Set.union_subset habinX ?_
        simp; exact hbX
    . use Ioo a b; simp
      apply Set.Subset.antisymm
      . intro x hx; simp; constructor
        . have hle := csInf_le hl hx
          unfold a
          suffices x ≠ a by exact lt_of_le_of_ne hle this.symm
          intro h'
          subst h'
          exact haX hx
        . have hle := le_csSup hr hx
          unfold b
          suffices x ≠ b by exact lt_of_le_of_ne hle this
          intro h'
          subst h'
          exact hbX hx
      . exact habinX
  · intro hexbi
    choose I hI using hexbi
    rw [hI]
    constructor
    . apply Bornology.IsBounded.of_boundedInterval I
    . match I with
      | Ioo a b => simp; exact Set.ordConnected_Ioo
      | Icc a b => simp; exact Set.ordConnected_Icc
      | Ioc a b => simp; exact Set.ordConnected_Ioc
      | Ico a b => simp; exact Set.ordConnected_Ico

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
theorem BoundedInterval.inter (I J: BoundedInterval) : ∃ K : BoundedInterval, (I:Set ℝ) ∩ (J:Set ℝ) = (K:Set ℝ) := by
  choose hIbound hIconn using (BoundedInterval.ordConnected_iff (I:Set ℝ)).mpr (by use I)
  choose hJbound hJconn using (BoundedInterval.ordConnected_iff (J:Set ℝ)).mpr (by use J)
  set Α := (I:Set ℝ) ∩ (J:Set ℝ)
  suffices Bornology.IsBounded Α ∧ Α.OrdConnected by
    exact (BoundedInterval.ordConnected_iff Α).mp this
  constructor
  . obtain ⟨m₁, hm₁⟩ := hIbound.bddBelow
    obtain ⟨M₁, hM₁⟩ := hIbound.bddAbove
    unfold Α
    apply isBounded_iff_bddBelow_bddAbove.mpr ⟨?_, ?_⟩
    . use m₁; intro x hx
      observe : x ∈ (I:Set ℝ)
      exact hm₁ this
    . use M₁; intro x hx
      observe : x ∈ (I:Set ℝ)
      exact hM₁ this
  . unfold Α
    exact Set.OrdConnected.inter'

noncomputable instance BoundedInterval.instInter : Inter BoundedInterval where
  inter I J := (inter I J).choose

@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (BoundedInterval.inter I J).choose_spec.symm

example :
  (Icc 2 4 ∩ Icc 4 6) = (Icc 4 4 : Set ℝ) := by
  rw [BoundedInterval.inter_eq]
  ext x; simp_all; constructor
  . intro hx; linarith
  . intro hx; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    all_goals linarith


instance BoundedInterval.instMembership : Membership ℝ BoundedInterval where
  mem I x := x ∈ (I:Set ℝ)

theorem BoundedInterval.mem_iff (I: BoundedInterval) (x:ℝ) :
  x ∈ I ↔ x ∈ (I:Set ℝ) := by rfl

instance BoundedInterval.instSubset : HasSubset BoundedInterval where
  Subset I J := ∀ x, x ∈ I → x ∈ J

theorem BoundedInterval.subset_iff (I J: BoundedInterval) :
  I ⊆ J ↔ (I:Set ℝ) ⊆ (J:Set ℝ) := by rfl

abbrev BoundedInterval.a (I: BoundedInterval) : ℝ := match I with
  | Ioo a _ => a
  | Icc a _ => a
  | Ioc a _ => a
  | Ico a _ => a

abbrev BoundedInterval.b (I: BoundedInterval) : ℝ := match I with
  | Ioo _ b => b
  | Icc _ b => b
  | Ioc _ b => b
  | Ico _ b => b

theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

instance BoundedInterval.instTrans : IsTrans BoundedInterval (· ⊆ ·) where
  trans I J K hIJ hJK := by grind [subset_iff]

@[simp]
theorem BoundedInterval.mem_inter (I J: BoundedInterval) (x:ℝ) :
  x ∈ (I ∩ J : BoundedInterval) ↔ x ∈ I ∧ x ∈ J := by simp [mem_iff]

abbrev BoundedInterval.length (I: BoundedInterval) : ℝ := max (I.b - I.a) 0

/-- Using ||ₗ subscript here to not override || -/
macro:max atomic("|" noWs) a:term noWs "|ₗ" : term => `(BoundedInterval.length $a)

example : |Icc 3 5|ₗ = 2 := by
  unfold BoundedInterval.length
  show max (5 - 3) 0 = 2
  norm_num

example : |Ioo 3 5|ₗ = 2 := by
  unfold BoundedInterval.length
  show max (5 - 3) 0 = 2
  norm_num

example : |Icc 5 5|ₗ = 0 := by
  unfold BoundedInterval.length
  show max (5 - 5) 0 = 0
  norm_num

theorem BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ |I|ₗ := by
  simp

theorem BoundedInterval.empty_of_lt {I: BoundedInterval} (h: I.b < I.a) : (I:Set ℝ) = ∅ := by
  cases I with
  | Ioo _ _ => simp [le_of_lt h]
  | Icc _ _ => simp [h]
  | Ioc _ _ => simp [le_of_lt h]
  | Ico _ _ => simp [le_of_lt h]

theorem Boundedinterval.subsingleton_of_le {I: BoundedInterval} (h: I.b ≤ I.a) : (I:Set ℝ).Subsingleton := by
  rcases h.eq_or_lt with heq | hlt
  . match I with
    | Icc x y =>
      simp
      change y ≤ x at h; exact h
    | Ioo x y =>
      change y = x at heq
      rw [heq]; simp
    | Ioc x y =>
      change y = x at heq
      rw [heq]; simp
    | Ico x y =>
      change y = x at heq
      rw [heq]; simp
  . have hemp := BoundedInterval.empty_of_lt hlt
    rw [hemp]
    simp


theorem BoundedInterval.length_of_empty {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : |I|ₗ = 0 := by
  simp
  match I with
  | Ioo a b =>
    rw [BoundedInterval.set_Ioo, Set.Ioo_eq_empty_iff] at hI
    simp [BoundedInterval.a, BoundedInterval.b]
    linarith
  | Icc a b =>
    rw [BoundedInterval.set_Icc, Set.Icc_eq_empty_iff] at hI
    simp [BoundedInterval.a, BoundedInterval.b]
    linarith
  | Ioc a b =>
    rw [BoundedInterval.set_Ioc, Set.Ioc_eq_empty_iff] at hI
    simp [BoundedInterval.a, BoundedInterval.b]
    linarith
  | Ico a b =>
    rw [BoundedInterval.set_Ico, Set.Ico_eq_empty_iff] at hI
    simp [BoundedInterval.a, BoundedInterval.b]
    linarith


theorem BoundedInterval.length_of_subsingleton {I: BoundedInterval} : Subsingleton (I:Set ℝ) ↔ |I|ₗ = 0 := by
  constructor
  . intro hsingle
    simp at hsingle
    suffices I.b ≤ I.a by
      unfold BoundedInterval.length
      simp; exact this
    contrapose hsingle
    push_neg at hsingle
    rw [Set.not_subsingleton_iff]
    match I with
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hsingle
      simp
      choose p₁ hpl₁ hpr₁ using exists_between hsingle
      choose p₂ hpl₂ hpr₂ using exists_between hpl₁
      use p₁; constructor
      . constructor <;> linarith
      . use p₂; constructor
        . constructor <;> linarith
        . linarith
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hsingle
      simp
      choose p₁ hpl₁ hpr₁ using exists_between hsingle
      choose p₂ hpl₂ hpr₂ using exists_between hpl₁
      use p₁; constructor
      . constructor <;> linarith
      . use p₂; constructor
        . constructor <;> linarith
        . linarith
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hsingle
      simp
      choose p₁ hpl₁ hpr₁ using exists_between hsingle
      choose p₂ hpl₂ hpr₂ using exists_between hpl₁
      use p₁; constructor
      . constructor <;> linarith
      . use p₂; constructor
        . constructor <;> linarith
        . linarith
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hsingle
      simp
      choose p₁ hpl₁ hpr₁ using exists_between hsingle
      choose p₂ hpl₂ hpr₂ using exists_between hpl₁
      use p₁; constructor
      . constructor <;> linarith
      . use p₂; constructor
        . constructor <;> linarith
        . linarith
  . intro h0
    unfold BoundedInterval.length at h0
    simp at h0
    simp
    match I with
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h0
      simp
      intro x ⟨hx, hx'⟩
      exact absurd h0 (by linarith)
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h0
      simpa using h0
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h0
      simp
      intro x ⟨hx, hx'⟩
      exact absurd h0 (by linarith)
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h0
      simp
      intro x ⟨hx, hx'⟩
      exact absurd h0 (by linarith)

lemma BoundedInterval.length_eq' {I : BoundedInterval} (h: (I:Set ℝ).Nonempty) :  |I|ₗ = sSup (I:Set ℝ) - sInf (I:Set ℝ):= by
  match I with
  | Icc a b =>
    simp at h
    simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, BoundedInterval.set_Icc]
    rw [csInf_Icc h, csSup_Icc h]
    simp; exact h
  | Ioo a b =>
    simp at h
    simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, BoundedInterval.set_Ioo]
    rw [csInf_Ioo h, csSup_Ioo h]
    simp; linarith
  | Ico a b =>
    simp at h
    simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, BoundedInterval.set_Ico]
    rw [csInf_Ico h, csSup_Ico h]
    simp; linarith
  | Ioc a b =>
    simp at h
    simp only [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b, BoundedInterval.set_Ioc]
    rw [csInf_Ioc h, csSup_Ioc h]
    simp; linarith

theorem BoundedInterval.length_congr {I J : BoundedInterval} (h: (I:Set ℝ)=(J:Set ℝ)) : |I|ₗ = |J|ₗ := by
  by_cases! hnon : (I:Set ℝ).Nonempty
  . have hnon' : (J:Set ℝ).Nonempty := by rwa [← h]
    rw [BoundedInterval.length_eq' hnon, BoundedInterval.length_eq' hnon']
    have hsup : sSup (I:Set ℝ) = sSup (J:Set ℝ) := by rw [← h]
    have hinf : sInf (I:Set ℝ) = sInf (J:Set ℝ) := by rw [← h]
    linarith
  . have hnon' : (J:Set ℝ) = ∅ := by rwa [← h]
    have hI := BoundedInterval.length_of_empty hnon
    have hJ := BoundedInterval.length_of_empty hnon'
    simp [hI, hJ]

theorem BoundedInterval.length_inter_comm {I J : BoundedInterval} : |I ∩ J|ₗ = |J ∩ I|ₗ := by
  suffices (((I ∩ J):BoundedInterval):Set ℝ) = (((J ∩ I):BoundedInterval):Set ℝ) by exact BoundedInterval.length_congr this
  simp [BoundedInterval.inter_eq, Set.inter_comm]


theorem BoundedInterval.dist_le_length {I:BoundedInterval} {x y:ℝ} (hx: x ∈ I) (hy: y ∈ I) : |x - y| ≤ |I|ₗ := by
  apply subset_Icc I at hx; apply subset_Icc I at hy; simp_all [mem_iff, abs_le']; grind

abbrev BoundedInterval.joins (K I J: BoundedInterval) : Prop := (I:Set ℝ) ∩ (J:Set ℝ) = ∅
  ∧ (K:Set ℝ) = (I:Set ℝ) ∪ (J:Set ℝ) ∧ |K|ₗ = |I|ₗ + |J|ₗ

theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Icc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins (Icc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  simp_all [joins, le_of_lt hbc]; grind

theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins (Ico a b) (Icc b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins (Ico a b) (Ico b c) := by
  simp_all [joins]; grind

theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins (Ioo a b) (Icc b c) := by
  simp_all [joins, le_of_lt hab]; grind

theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins (Ioo a b) (Ico b c) := by
  simp_all [joins, le_of_lt hab]; grind

@[ext]
structure Partition (I: BoundedInterval) where
  intervals : Finset BoundedInterval
  exists_unique (x:ℝ) (hx : x ∈ I) : ∃! J, J ∈ intervals ∧ x ∈ J
  contains (J : BoundedInterval) (hJ : J ∈ intervals) : J ⊆ I

#check Partition.mk

instance Partition.instMembership (I: BoundedInterval) : Membership BoundedInterval (Partition I) where
  mem P J := J ∈ P.intervals

instance Partition.instBot (I: BoundedInterval) : Bot (Partition I) where
  bot := {
    intervals := {I}
    exists_unique x hx := by apply ExistsUnique.intro I <;> grind
    contains := by grind [subset_iff]
    }

@[simp]
theorem Partition.intervals_of_bot (I:BoundedInterval) : (⊥:Partition I).intervals = {I} := by
  rfl

noncomputable abbrev Partition.join {I J K:BoundedInterval} (P: Partition I) (Q: Partition J) (h: K.joins I J) : Partition K
:=
{
  intervals := P.intervals ∪ Q.intervals
  exists_unique x hx := by
    have := congr(x ∈ $(h.1))
    simp [mem_iff, h.2] at hx; obtain hx | hx := hx
    . choose L _ _ using (P.exists_unique _ hx).exists
      apply ExistsUnique.intro L (by grind)
      intro K ⟨hK, hxK⟩; simp at hK; obtain _ | hKQ := hK
      map_tacs [apply (P.exists_unique _ hx).unique; apply (K.subset_iff _).mp (Q.contains _ hKQ) at hxK]
      all_goals grind
    choose L hLQ hxL using (Q.exists_unique _ hx).exists
    apply ExistsUnique.intro L (by grind)
    intro K ⟨hK, hxK⟩; simp at hK; obtain hKP | _ := hK
    map_tacs [apply (K.subset_iff _).mp (P.contains _ hKP) at hxK; apply (Q.exists_unique _ hx).unique]
    all_goals grind
  contains L hL := by
    simp at hL; obtain hLP | hLQ := hL
    . apply (P.contains _ hLP).trans; simp [h, subset_iff]
    apply (Q.contains _ hLQ).trans; simp [h, subset_iff]
}

@[simp]
theorem Partition.intervals_of_join {I J K:BoundedInterval} {h:K.joins I J} (P: Partition I) (Q: Partition J) : (P.join Q h).intervals = P.intervals ∪ Q.intervals := by
  simp

noncomputable abbrev Partition.add_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals ∪ {∅}
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by aesop)
    intro K ⟨ hK, _ ⟩; simp at hK; obtain rfl | hK := hK
    · simp_all [mem_iff]
    apply (P.exists_unique _ hx).unique <;> grind
  contains L hL := by
    simp at hL; obtain rfl | hL := hL
    · simp [subset_iff]
    exact P.contains _ hL
}

open Classical in
noncomputable abbrev Partition.remove_empty {I:BoundedInterval} (P: Partition I) : Partition I := {
  intervals := P.intervals.filter (fun J ↦ (J:Set ℝ).Nonempty)
  exists_unique x hx := by
    choose J _ _ using (P.exists_unique _ hx).exists
    apply ExistsUnique.intro J (by grind [mem_iff, Set.nonempty_of_mem])
    intro K ⟨ hK, _ ⟩; simp at hK
    apply (P.exists_unique _ hx).unique <;> grind
  contains _ _ := P.contains _ (by grind)
}

@[simp]
theorem Partition.intervals_of_add_empty (I: BoundedInterval) (P: Partition I) : (P.add_empty).intervals = P.intervals ∪ {∅} := by
  simp

example : ∃ P:Partition (Icc 1 8),
  P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8, ∅} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5.add_empty; simp_all; aesop

example : ∃ P:Partition (Icc 1 8), P.intervals = {Icc 1 1, Ioo 1 3, Ico 3 5, Icc 5 5, Ioc 5 8} := by
  set P1 : Partition (Icc 1 1) := ⊥
  set P2 : Partition (Ico 1 3) := P1.join (⊥:Partition (Ioo 1 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
  set P3 : Partition (Ico 1 5) := P2.join (⊥:Partition (Ico 3 5)) (join_Ico_Ico (by norm_num) (by norm_num) )
  set P4 : Partition (Icc 1 5) := P3.join (⊥:Partition (Icc 5 5)) (join_Ico_Icc (by norm_num) (by norm_num) )
  set P5 : Partition (Icc 1 8) := P4.join (⊥:Partition (Ioc 5 8)) (join_Icc_Ioc (by norm_num) (by norm_num) )
  use P5; aesop


example : ¬∃ P:Partition (Icc 1 5), P.intervals = {Icc 1 4, Icc 3 5} := by
  intro h
  choose K hK using h
  have h1 : 3.5 ∈ Icc 1 4 := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]
    constructor <;> linarith
  have h2 : 3.5 ∈ Icc 3 5 := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]; constructor <;> linarith
  have hmem1 : Icc 1 4 ∈ K.intervals := by rw [hK]; simp
  have hmem2 : Icc 3 5 ∈ K.intervals := by rw [hK]; simp
  have hunique := K.exists_unique 3.5 (by rw [BoundedInterval.mem_iff, BoundedInterval.set_Icc]; constructor <;> linarith)
  have heq := hunique.unique ⟨hmem1, h1⟩ ⟨hmem2, h2⟩
  simp at heq

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 1 3, Ioo 3 5} := by
  intro h'
  choose K hK using h'
  have h : 3 ∈ Ioo 1 5 := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]
    constructor <;> linarith
  have h1 : 3 ∉ Ioo 1 3 := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]
    simp
  have h2 : 3 ∉ Ioo 3 5 := by
    rw [BoundedInterval.mem_iff, BoundedInterval.set_Ioo]
    simp
  choose I hI hIunique using K.exists_unique 3 h
  obtain ⟨hIK, h3I⟩ := hI
  rw [hK] at hIK; simp at hIK
  rcases hIK with ha | hb
  . rw [ha] at h3I
    exact h1 h3I
  . rw [hb] at h3I
    exact h2 h3I

example : ¬∃ P:Partition (Ioo 1 5), P.intervals = {Ioo 0 3, Ico 3 5} := by
  intro h'
  choose K hK using h'
  have hcontains := K.contains (Ioo 0 3) (by rw [hK]; simp)
  rw [(BoundedInterval.subset_iff _ _)] at hcontains
  simp at hcontains
  have hhalf : 0.5 ∈ Set.Ioo (0:ℝ) 3 := by simp; constructor <;> norm_num
  have := hcontains hhalf
  simp at this
  linarith

lemma Partition.intervals_nonempty {I: BoundedInterval} (hI: I.a < I.b) {P: Partition I} : P.intervals.Nonempty := by
  choose m hm using exists_between hI
  have hmI : m ∈ I := by
    rw [BoundedInterval.mem_iff]
    match I with
    | Ioo a b => simp; constructor <;> linarith
    | Ioc a b => simp; constructor <;> linarith
    | Ico a b => simp; constructor <;> linarith
    | Icc a b => simp; constructor <;> linarith
  choose J hJmem hJ using P.exists_unique m hmI
  simp at hJmem hJ
  use J
  exact hJmem.1

lemma Partition.intervals_nonempty' {I: BoundedInterval} (hI: I.a < I.b) {P: Partition I} : P.remove_empty.intervals.Nonempty := by
  choose m hm using exists_between hI
  have hmI : m ∈ I := by
    rw [BoundedInterval.mem_iff]
    match I with
    | Ioo a b => simp; constructor <;> linarith
    | Ioc a b => simp; constructor <;> linarith
    | Ico a b => simp; constructor <;> linarith
    | Icc a b => simp; constructor <;> linarith
  choose J hJmem hJ using P.exists_unique m hmI
  simp at hJmem hJ
  use J; simp; constructor
  . exact hJmem.1
  . use m; exact hJmem.2

/-- Exercise 11.1.3.  The exercise only claims c ≤ b, but the stronger claim c < b is true and useful. -/
theorem Partition.exist_right {I: BoundedInterval} (hI: I.a < I.b) (hI': I.b ∉ I)
  {P: Partition I}
  : ∃ c ∈ Set.Ico I.a I.b, Ioo c I.b ∈ P ∨ Ico c I.b ∈ P := by
  by_contra! h'
  have hIinterval : I = Ioo I.a I.b ∨ I = Ico I.a I.b := by
    match I with
    | Ioo a b => left; simp
    | Icc a b =>
      simp; apply hI'
      simp [BoundedInterval.b, BoundedInterval.mem_iff]
      simp [BoundedInterval.a, BoundedInterval.b] at hI
      linarith
    | Ioc a b =>
      simp; apply hI'
      simp [BoundedInterval.b, BoundedInterval.mem_iff]
      simp [BoundedInterval.a, BoundedInterval.b] at hI
      linarith
    | Ico a b => right; simp
  have hwithin : ∀ (x:ℝ), I.a < x ∧ x < I.b → x ∈ I := by
    intro x hx
    rcases hIinterval with hIoo | hIco
    . rw [hIoo, BoundedInterval.mem_iff]; simp
      constructor <;> linarith
    . rw [hIco, BoundedInterval.mem_iff]; simp
      constructor <;> linarith
  have hnotoftheform : ∀ J ∈ P, (J:Set ℝ).Nonempty → (∀ c, J ≠ Ioo c I.b) → (∀ c, J ≠ Ico c I.b) → sSup (J:Set ℝ) < I.b := by
    intro J hJ hJnon hIoo hIco
    have hcontains := P.contains J hJ
    match J with
    | Ioo x y =>
      rw [BoundedInterval.subset_iff] at hcontains
      simp at hcontains ⊢
      specialize hIoo x; specialize hIco x
      rw [csSup_Ioo (by simpa using hJnon)]
      by_contra! hbley
      rcases hbley.eq_or_lt with heq | hlt
      . rw [heq] at hIoo
        simp at hIoo
      . rcases hIinterval with hIIoo | hIIco
        . rw [hIIoo] at hcontains; simp at hcontains hJnon
          obtain ⟨hax, hyb⟩ := (Set.Ioo_subset_Ioo_iff hJnon).mp hcontains
          linarith
        . rw [hIIco] at hcontains; simp at hcontains hJnon
          have hmax : max x I.b < y := by exact max_lt hJnon hlt
          set m := (max x I.b + y) / 2
          have hmb : m > I.b := by grind
          have hxm : x < m := by grind
          have hmy : m < y := by grind
          have hmem : m ∈ Set.Ioo x y := by exact ⟨hxm, hmy⟩
          have := (hcontains hmem).2
          linarith
    | Icc x y =>
      rw [BoundedInterval.subset_iff] at hcontains
      simp at hcontains ⊢
      rw [csSup_Icc (by simpa using hJnon)]
      by_contra! hbley
      rcases hIinterval with hIIoo | hIIco
      . rw [hIIoo] at hcontains; simp at hcontains hJnon
        have hmax : max x I.b ≤ y := by exact max_le hJnon hbley
        set m := (max x I.b + y) / 2
        have hmb : m ≥ I.b := by grind
        have hxm : x ≤ m := by grind
        have hmy : m ≤ y := by grind
        have hmem : m ∈ Set.Icc x y := by exact ⟨hxm, hmy⟩
        have := (hcontains hmem).2
        linarith
      . rw [hIIco] at hcontains; simp at hcontains hJnon
        have hmax : max x I.b ≤ y := by exact max_le hJnon hbley
        set m := (max x I.b + y) / 2
        have hmb : m ≥ I.b := by grind
        have hxm : x ≤ m := by grind
        have hmy : m ≤ y := by grind
        have hmem : m ∈ Set.Icc x y := by exact ⟨hxm, hmy⟩
        have := (hcontains hmem).2
        linarith
    | Ioc x y =>
      rw [BoundedInterval.subset_iff] at hcontains
      simp at hcontains ⊢
      rw [csSup_Ioc (by simpa using hJnon)]
      by_contra! hbley
      rcases hIinterval with hIIoo | hIIco
      . rw [hIIoo] at hcontains; simp at hcontains hJnon
        have hmax : max x I.b ≤ y := by exact max_le (by linarith) hbley
        set m := (max x I.b + y) / 2
        have hmb : m ≥ I.b := by grind
        have hxm : x < m := by grind
        have hmy : m ≤ y := by grind
        have hmem : m ∈ Set.Ioc x y := by exact ⟨hxm, hmy⟩
        have := (hcontains hmem).2
        linarith
      . rw [hIIco] at hcontains; simp at hcontains hJnon
        have hmax : max x I.b ≤ y := by exact max_le (by linarith) hbley
        set m := (max x I.b + y) / 2
        have hmb : m ≥ I.b := by grind
        have hxm : x < m := by grind
        have hmy : m ≤ y := by grind
        have hmem : m ∈ Set.Ioc x y := by exact ⟨hxm, hmy⟩
        have := (hcontains hmem).2
        linarith
    | Ico x y =>
      rw [BoundedInterval.subset_iff] at hcontains
      simp at hcontains ⊢
      specialize hIoo x; specialize hIco x
      rw [csSup_Ico (by simpa using hJnon)]
      by_contra! hbley
      rcases hbley.eq_or_lt with heq | hlt
      . rw [heq] at hIco
        simp at hIco
      . rcases hIinterval with hIIoo | hIIco
        . rw [hIIoo] at hcontains; simp at hcontains hJnon
          have hmax : max x I.b < y := by exact max_lt hJnon hlt
          set m := (max x I.b + y) / 2
          have hmb : m > I.b := by grind
          have hxm : x ≤ m := by grind
          have hmy : m < y := by grind
          have hmem : m ∈ Set.Ico x y := by exact ⟨hxm, hmy⟩
          have := (hcontains hmem).2
          linarith
        . rw [hIIco] at hcontains; simp at hcontains hJnon
          obtain ⟨hax, hyb⟩ := (Set.Ico_subset_Ico_iff hJnon).mp hcontains
          linarith
  have hjsup : ∀ J ∈ P, (J: Set ℝ).Nonempty → sSup (J: Set ℝ) < I.b := by
    intro J hJ hJnon
    apply hnotoftheform J hJ hJnon
    . intro c hJeq
      by_cases! hc : c ∈ Set.Ico I.a I.b
      . have := (h' c hc).1
        rw [hJeq] at hJ
        exact this hJ
      . simp at hc
        by_cases! hac : I.a ≤ c
        . specialize hc hac
          rw [hJeq] at hJnon
          simp at hJnon
          linarith
        . rw [hJeq] at hJnon
          simp at hJnon
          choose m hm using exists_between hac
          have hmJ : m ∈ J := by
            rw [hJeq, BoundedInterval.mem_iff]
            simp; constructor <;> linarith
          have hmI : m ∉ I := by
            intro hI
            rcases hIinterval with hIco | hIoo
            . rw [hIco, BoundedInterval.mem_iff] at hI
              simp at hI
              linarith
            · rw [hIoo, BoundedInterval.mem_iff] at hI
              simp at hI
              linarith
          have : ¬ (J ⊆ I) := by
            intro hJI
            rw [BoundedInterval.subset_iff] at hJI
            rw [BoundedInterval.mem_iff] at hmJ hmI
            exact hmI (hJI hmJ)
          exact this (P.contains J hJ)
    . intro c hJeq
      by_cases! hc : c ∈ Set.Ico I.a I.b
      . have := (h' c hc).2
        rw [hJeq] at hJ
        exact this hJ
      . simp at hc
        by_cases! hac : I.a ≤ c
        . specialize hc hac
          rw [hJeq] at hJnon
          simp at hJnon
          linarith
        . rw [hJeq] at hJnon
          simp at hJnon
          choose m hm using exists_between hac
          have hmJ : m ∈ J := by
            rw [hJeq, BoundedInterval.mem_iff]
            simp; constructor <;> linarith
          have hmI : m ∉ I := by
            intro hI
            rcases hIinterval with hIco | hIoo
            . rw [hIco, BoundedInterval.mem_iff] at hI
              simp at hI
              linarith
            · rw [hIoo, BoundedInterval.mem_iff] at hI
              simp at hI
              linarith
          have : ¬ (J ⊆ I) := by
            intro hJI
            rw [BoundedInterval.subset_iff] at hJI
            rw [BoundedInterval.mem_iff] at hmJ hmI
            exact hmI (hJI hmJ)
          exact this (P.contains J hJ)
  classical
  set S := P.remove_empty.intervals.image (fun (J:BoundedInterval) => sSup (J:Set ℝ))
  have hSnon : S.Nonempty := by
    have := Partition.intervals_nonempty' (P:=P) hI
    exact Finset.image_nonempty.mpr this
  set M := S.max' hSnon
  have hMb : M < I.b := by
    unfold M
    refine (Finset.max'_lt_iff _ hSnon).mpr ?_
    intro y hy
    unfold S at hy
    simp at hy; choose J hJ hJ' using hy
    rw [← hJ']
    exact hjsup J hJ.1 hJ.2
  have hmaxlt : max M I.a < I.b := by exact max_lt hMb hI
  set t := (max M I.a + I.b) / 2
  have hMltt : M < t := by grind
  have haltt : I.a < t := by grind
  have htltb : t < I.b := by grind
  have htI : t ∈ I := by exact hwithin t ⟨haltt, htltb⟩
  choose J hJmem hJ using P.exists_unique t htI
  simp at hJmem hJ
  have hJnon : (J:Set ℝ).Nonempty := by
    use t
    exact hJmem.2
  have htsup : t ≤ sSup (J:Set ℝ) := by
    apply le_csSup
    . have := P.contains J hJmem.1
      rw [BoundedInterval.subset_iff] at this
      use I.b
      rcases hIinterval with hIoo | hIco
      . rw [hIoo] at this; simp at this
        intro p hp
        specialize this hp
        simp at this; linarith
      . rw [hIco] at this; simp at this
        intro p hp
        specialize this hp
        simp at this; linarith
    . exact hJmem.2
  have hsupM : sSup (J : Set ℝ) ≤ M := by
    unfold M
    apply Finset.le_max' S
    unfold S; simp;
    use J; simp
    exact ⟨hJmem.1, hJnon⟩
  linarith

/-- Theorem 11.1.13 (Length is finitely additive). -/
theorem Partition.sum_of_length  (I: BoundedInterval) (P: Partition I) :
  ∑ J ∈ P.intervals, |J|ₗ = |I|ₗ := by
  -- This proof is written to follow the structure of the original text.
  generalize hcard: P.intervals.card = n
  revert I; induction' n with n hn <;> intro I P hcard
  . rw [Finset.card_eq_zero] at hcard
    have : (I:Set ℝ) = ∅ := by
      by_contra! h
      choose a ha using h
      choose J hJmem hJ using P.exists_unique a ha
      have : P.intervals.Nonempty := by
        use J; exact hJmem.1
      contrapose! hcard
      exact this
    grind [length_of_empty]
  -- the proof in the book treats the n=1 case separately, but this is unnecessary
  by_cases h : Subsingleton (I:Set ℝ)
  . have (J: BoundedInterval) (hJ: J ∈ P) : Subsingleton (J:Set ℝ) := by
      simp at h ⊢
      by_contra! hnontrivial
      choose a haJ hab using hnontrivial
      choose b hbJ hab' using hab
      have hcontains := P.contains J hJ
      rw [BoundedInterval.subset_iff] at hcontains
      contrapose! h
      use a; constructor
      . exact hcontains haJ
      . use b; exact ⟨hcontains hbJ, hab'⟩
    simp_rw [length_of_subsingleton] at *
    convert Finset.sum_eq_zero this
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins L K := by
    by_cases hI' : I.b ∈ I
    . choose K hK hbK using (P.exists_unique I.b hI').exists
      observe hKI : K ⊆ I
      by_cases hsub : Subsingleton (K:Set ℝ)
      . simp_all [mem_iff]
        apply hsub.eq_singleton_of_mem at hbK
        have : K = Icc (I.b) (I.b) := by
          match K with
          | Icc a b =>
            simp at hbK
            rw [hbK.1, hbK.2]
          | Ioo a b =>
            simp at hbK
            by_cases! hab : a < b
            . exfalso
              contrapose! hsub
              simp
              choose p hp using exists_between hab
              choose q hq using exists_between hp.1
              use p; constructor
              . exact hp
              . use q; constructor <;> grind
            . have : Set.Ioo a b = ∅ := by exact Set.Ioo_eq_empty_of_le hab
              rw [this] at hbK
              simp at hbK
          | Ico a b =>
            simp at hbK
            by_cases! hab : a < b
            . exfalso
              contrapose! hsub
              simp
              choose p hp using exists_between hab
              choose q hq using exists_between hp.1
              use p; constructor
              . constructor <;> linarith
              . use q; constructor <;> grind
            . have : Set.Ico a b = ∅ := by exact Set.Ico_eq_empty_of_le hab
              rw [this] at hbK
              simp at hbK
          | Ioc a b =>
            simp at hbK
            by_cases! hab : a < b
            . exfalso
              contrapose! hsub
              simp
              choose p hp using exists_between hab
              choose q hq using exists_between hp.1
              use p; constructor
              . constructor <;> linarith
              . use q; constructor <;> grind
            . have : Set.Ioc a b = ∅ := by exact Set.Ioc_eq_empty_of_le hab
              rw [this] at hbK
              simp at hbK
        subst this
        cases I with
        | Ioo _ _ => simp at hI'
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc <;> order
        | Ico _ _ => simp at hI'
      simp [length_of_subsingleton, -Set.subsingleton_coe] at hsub
      have hKI' := (K.Ioo_subset.trans hKI).trans I.subset_Icc
      simp only [subset_iff] at hKI'
      have hKb : K.b = I.b := by
        rw [le_antisymm_iff]; split_ands
        . apply csSup_le_csSup bddAbove_Icc (by simp [hsub]) at hKI'
          simp_all [csSup_Ioo hsub, csSup_Icc (le_of_lt h)]
        have := K.subset_Icc _ hbK; simp [mem_iff] at this; exact this.2
      have hKA : I.a ≤ K.a := by
        apply csInf_le_csInf bddBelow_Icc (by simp [hsub]) at hKI'
        simp_all [csInf_Icc (le_of_lt h), csInf_Ioo]
      cases I with
      | Ioo _ _ => simp [mem_iff] at hI'
      | Icc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp [mem_iff, subset_iff] at *; grind
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo <;> tauto
      use Ico c b₁, hK, Ioo a₁ c
      apply P.contains at hK; simp [subset_iff] at hK
      have : c ∈ Set.Ico c b₁ := by grind
      grind [join_Ioo_Ico]
    | Icc _ _ => simp [mem_iff] at hI' h; order
    | Ioc _ _ => simp [mem_iff] at hI' h; order
    | Ico a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Icc a₁ c; grind [join_Icc_Ioo]
      use Ico c b₁, hK, Ico a₁ c; grind [join_Ico_Ico]
  obtain ⟨ K, L, hK, ⟨ h1, h2, h3 ⟩ ⟩ := this
  have : ∃ P' : Partition L, P'.intervals = P.intervals.erase K := by
    set P' : Partition L := {
      intervals := P.intervals.erase K
      exists_unique := by
        intro d hd
        have hdI : d ∈ I := by
          rw [BoundedInterval.mem_iff] at hd ⊢
          rw [h2]
          left; exact hd
        choose J hJmem hJ using P.exists_unique d hdI
        simp at hJmem hJ
        have hJK : J ≠ K := by
          intro hJK
          symm at hJK
          subst hJK
          contrapose! h1
          use d; exact ⟨hd, hJmem.2⟩
        use J; simp; constructor
        . exact ⟨⟨hJK, hJmem.1⟩, hJmem.2⟩
        . intro y hy hypintervals hdy
          exact hJ y hypintervals hdy
      contains := by
        intro J hJ; simp at hJ
        obtain ⟨hJK, hJ⟩ := hJ
        have hcontains := P.contains J hJ
        rw [BoundedInterval.subset_iff] at hcontains ⊢
        rw [h2] at hcontains
        intro x hx
        rcases hcontains hx with hL' | hK'
        . exact hL'
        . have hxI : x ∈ I := by
            rw [BoundedInterval.mem_iff, h2]
            right; exact hK'
          choose B hBmem hBunique using P.exists_unique x hxI
          simp at hBmem hBunique
          have hKP : K ∈ P.intervals := by exact Finset.mem_def.mpr hK
          have hJB := hBunique J hJ hx
          have hKB := hBunique K hKP hK'
          rw [← hJB] at hKB
          exact absurd hKB.symm hJK
    }
    use P'
  choose P' hP' using this
  rw [h3, ←Finset.add_sum_erase _ _ hK, ←hP', add_comm]; congr
  apply hn; simp [hP', Finset.card_erase_of_mem hK, hcard]

/-- Definition 11.1.14 (Finer and coarser partitions) -/
instance Partition.instLE (I: BoundedInterval) : LE (Partition I) where
  le P P' := ∀ J ∈ P'.intervals, ∃ K ∈ P, J ⊆ K

instance Partition.instPreOrder (I: BoundedInterval) : Preorder (Partition I) where
  le_refl P := by
    intro J hJ
    use J; constructor
    . exact hJ
    . rw [BoundedInterval.subset_iff]
  le_trans P P' P'' hP hP' := by
    intro J hJ
    choose J' hJ' using hP' J hJ
    choose J'' hJ'' using hP J' hJ'.1
    use J''; constructor
    . exact hJ''.1
    . exact hJ'.2.trans hJ''.2

instance Partition.instOrderBot (I: BoundedInterval) : OrderBot (Partition I) where
  bot_le := by
    intro P J hJ
    use I; constructor
    . show I ∈ ({I}:Finset BoundedInterval)
      simp
    . exact P.contains J hJ

/-- Example 11.1.15 -/
example : ∃ P P' : Partition (Icc 1 4),
  P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3,
                 Icc 3 4} ∧
  P'.intervals = {Icc 1 2, Ioc 2 4} ∧
  P' ≤ P := by
    have hP  : ∃ P:Partition (Icc 1 4), P.intervals = {Ico 1 2, Icc 2 2, Ioo 2 3, Icc 3 4} := by
      set P1 : Partition (Ico 1 2) := ⊥
      set P2 : Partition (Icc 1 2) := P1.join (⊥:Partition (Icc 2 2)) (join_Ico_Icc (by norm_num) (by norm_num) )
      set P3 : Partition (Ico 1 3) := P2.join (⊥:Partition (Ioo 2 3)) (join_Icc_Ioo (by norm_num) (by norm_num) )
      set P4 : Partition (Icc 1 4) := P3.join (⊥:Partition (Icc 3 4)) (join_Ico_Icc (by norm_num) (by norm_num) )
      use P4; aesop
    have hP' : ∃ P':Partition (Icc 1 4), P'.intervals = {Icc 1 2, Ioc 2 4} := by
      set P1 : Partition (Icc 1 2) := ⊥
      set P2 : Partition (Icc 1 4) := P1.join (⊥:Partition (Ioc 2 4)) (join_Icc_Ioc (by norm_num) (by norm_num) )
      use P2; aesop
    choose P hP  using hP
    choose P' hP'  using hP'
    use P, P'
    refine ⟨hP, hP', ?_⟩
    intro J hJ
    rw [hP] at hJ
    simp at hJ
    rcases hJ with h | h | h | h
    . use Icc 1 2; constructor
      . show Icc 1 2 ∈ P'.intervals
        rw [hP']; simp
      . rw [h, BoundedInterval.subset_iff]
        simp; exact Set.Ico_subset_Icc_self
    . use Icc 1 2; constructor
      . show Icc 1 2 ∈ P'.intervals
        rw [hP']; simp
      . rw [h, BoundedInterval.subset_iff]
        simp
    . use Ioc 2 4; constructor
      . show Ioc 2 4 ∈ P'.intervals
        rw [hP']; simp
      . rw [h, BoundedInterval.subset_iff]
        intro x hx; simp at hx ⊢
        constructor <;> linarith
    . use Ioc 2 4; constructor
      . show Ioc 2 4 ∈ P'.intervals
        rw [hP']; simp
      . rw [h, BoundedInterval.subset_iff]
        intro x hx; simp at hx ⊢
        constructor <;> linarith

/-- Definition 11.1.16 (Common refinement). -/
noncomputable instance Partition.instMax (I: BoundedInterval) : Max (Partition I) where
  max P P' := {
    intervals := Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    exists_unique x hx := by
      choose J _ _ using P.exists_unique _ hx
      choose K _ _ using P'.exists_unique _ hx
      simp at *
      apply ExistsUnique.intro (J ∩ K)
      . simp_all; grind
      simp; grind [mem_inter]
    contains L hL := by
      simp at hL; obtain ⟨ J, hJ, K, hK, rfl ⟩ := hL
      apply P.contains at hJ; apply P'.contains at hK
      simp [subset_iff] at *; grind [Set.inter_subset_left]
    }


/-- Example 11.1.17. -/
example : ∃ P P' : Partition (Icc 1 4),
    P.intervals = {Ico 1 3, Icc 3 4} ∧
    P'.intervals = {Icc 1 2, Ioc 2 4} ∧
    (P' ⊔ P).intervals.image toSet =
      {Set.Icc 1 2, Set.Ioo 2 3, Set.Icc 3 4, ∅} := by
  have hP  : ∃ P:Partition (Icc 1 4), P.intervals = {Ico 1 3, Icc 3 4} := by
    set P1 : Partition (Ico 1 3) := ⊥
    set P2 : Partition (Icc 1 4) := P1.join (⊥:Partition (Icc 3 4)) (join_Ico_Icc (by norm_num) (by norm_num) )
    use P2; aesop
  have hP'  : ∃ P':Partition (Icc 1 4), P'.intervals = {Icc 1 2, Ioc 2 4} := by
    set P1 : Partition (Icc 1 2) := ⊥
    set P2 : Partition (Icc 1 4) := P1.join (⊥:Partition (Ioc 2 4)) (join_Icc_Ioc (by norm_num) (by norm_num) )
    use P2; aesop
  choose P hP using hP
  choose P' hP' using hP'
  refine ⟨P, P', hP, hP', ?_⟩
  simp [Max.max, hP, hP']
  have h1 :  Set.Icc (1:ℝ) 2 ∩ Set.Icc 3 4 = ∅ := by
    ext x; simp
    intro a ha hb; linarith
  have h2 : Set.Icc (1:ℝ) 2 ∩ Set.Ico 1 3 = Set.Icc 1 2 := by
    ext x; simp; intro a ha; constructor <;> linarith
  have h3 : Set.Ioc (2:ℝ) 4 ∩ Set.Ico 1 3 = Set.Ioo 2 3 := by
    ext x; simp; constructor
    . simp; intro h h' h'' h'''; constructor <;> linarith
    . simp; intro h h'; constructor <;> grind
  have h4 : Set.Ioc (2:ℝ) 4 ∩ Set.Icc 3 4 = Set.Icc 3 4 := by
    ext x; simp
    intro a ha; constructor <;> linarith
  rw [h1, h2, h3, h4]
  grind



/-- Lemma 11.1.8 / Exercise 11.1.4 -/
theorem BoundedInterval.le_max {I: BoundedInterval} (P P': Partition I) :
  P ≤ P ⊔ P' ∧ P' ≤ P ⊔ P' := by
  constructor
  . intro J hJ
    simp [Max.max] at hJ
    choose K hKP hKP' using hJ
    choose K' hK' hintersect using hKP'
    use K; constructor
    . exact hKP
    . rw [← hintersect, BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      simp
  . intro J hJ
    simp [Max.max] at hJ
    choose K hKP hKP' using hJ
    choose K' hK' hintersect using hKP'
    use K'; constructor
    . exact hK'
    . rw [← hintersect, BoundedInterval.subset_iff, BoundedInterval.inter_eq]
      simp

/-- Not from textbook: the reverse inclusion -/
theorem BoundedInterval.max_le_iff (I: BoundedInterval) {P P' P'': Partition I}
  {hP : P ≤ P''} {hP': P' ≤ P''} : P ⊔ P' ≤ P''  := by
  intro J hJ
  choose K hKmem hK using hP J hJ
  choose K' hK'mem hK' using hP' J hJ
  use K ∩ K'; constructor
  . simp [Max.max]
    show K ∩ K' ∈ Finset.image₂ (fun J K ↦ J ∩ K) P.intervals P'.intervals
    simp
    use K, hKmem, K', hK'mem
  . intro p hp
    simp; constructor
    . apply hK; exact hp
    . apply hK'; exact hp

lemma BoundedInterval.intervals_of_bot {I : BoundedInterval}  : (⊥:Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl

lemma BoundedInterval.intervals_of_bot' {I J : BoundedInterval}  : J ∈ (⊥:Partition I) ↔ J = I := by
  constructor
  . intro h; change J ∈ ({I}:Finset BoundedInterval) at h; simpa using h
  . intro h; change J ∈ ({I}:Finset BoundedInterval); simpa using h

end Chapter11
