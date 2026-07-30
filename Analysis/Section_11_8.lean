import Mathlib.Tactic
import Mathlib.Topology.Instances.Irrational
import Analysis.Section_11_6

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 11.8: The Riemann-Stieltjes integral

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Definition of `α_length`.
- The piecewise constant Riemann-Stieltjes integral.
- The full Riemann-Stieltjes integral.

{open Set}

Technical notes:
- In Lean it is more convenient to make definitions such as `α_length` and the Riemann-Stieltjes
  integral totally defined, thus assigning "junk" values to the cases where the definition is
  not intended to be applied. For the definition of `α_length`, the definition is intended to be
  applied in contexts where left and right limits exist, and the function is extended by
  constants to the left and right of its intended domain of definition; for instance, if a
  function `x` `f` is defined on {lean}`Icc 0 1`, then it is intended that `f x = f 1` for all `x ≥ 1`
  and `f x = f 0` for all `x ≤ 0`; in particular, at a right endpoint, the value of a function
  is intended to agree with its right limit, and similarly for the left endpoint, although we
  do not enforce this in our definition of `α_length`. (For functions defined on open intervals,
  the extension is immaterial.)
- The notion of `α_length` and piecewise constant Riemann-Stieltjes integral is intended for
  situations where left and right limits exist, such as for monotone functions or continuous
  functions, though technically they make sense without these hypotheses. The full Riemann-Stieltjes
  integral is intended for functions that are of bounded variation, though we shall restrict
  attention to the special case of monotone increasing functions for the most part.
-/

namespace Chapter11

open BoundedInterval Chapter9

/-- Left and right limits. A junk value is assigned if the limit does not exist. -/
noncomputable abbrev right_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Ioi x₀)).map f)
#check Function.rightLim

noncomputable abbrev left_lim (f: ℝ → ℝ) (x₀:ℝ) : ℝ := Filter.lim ((nhdsWithin x₀ (.Iio x₀)).map f)

theorem right_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Ioi x₀) f L x₀) :
  right_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

theorem left_lim_def {f: ℝ → ℝ} {x₀ L:ℝ} (h: Convergesto (.Iio x₀) f L x₀) :
  left_lim f x₀ = L := by
  show Filter.lim _ = L
  apply lim_eq; rwa [Convergesto.iff, Filter.Tendsto.eq_1] at h

noncomputable abbrev jump (f: ℝ → ℝ) (x₀:ℝ) : ℝ :=
  right_lim f x₀ - left_lim f x₀

/-- Right limits exist for continuous functions -/
theorem right_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  right_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply right_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo x₀ (x₀ + ε))).Tendsto f  (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ico_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo x₀ (x₀ + ε) ∈ nhdsWithin x₀ (.Ioi x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]; congr 1; simp [Set.Ioo_subset_Ioi_self]

/-- Left limits exist for continuous functions -/
theorem left_lim_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X) (hf: ContinuousWithinAt f X x₀) :
  left_lim f x₀ = f x₀ := by
  choose ε hε hX using h
  apply left_lim_def
  rw [ContinuousWithinAt.eq_1] at hf
  replace hf : (nhdsWithin x₀ (.Ioo (x₀ - ε) x₀)).Tendsto f (nhds (f x₀)) :=
    tendsto_nhdsWithin_mono_left (Set.Ioo_subset_Ioc_self.trans hX) hf
  rw [Convergesto.iff]
  convert hf using 1
  have h1 : .Ioo (x₀-ε) x₀ ∈ nhdsWithin x₀ (.Iio x₀) := by
    convert inter_mem_nhdsWithin (t := .Ioo (x₀-ε) (x₀+ε)) _ _
    . grind
    apply Ioo_mem_nhds <;> linarith
  rw [←nhdsWithin_inter_of_mem h1]
  congr 1; simp [Set.Ioo_subset_Iio_self]

/-- No jump for continuous functions -/
theorem jump_of_continuous {X:Set ℝ} {f: ℝ → ℝ} {x₀:ℝ}
  (h : X ∈ nhds x₀) (hf: ContinuousWithinAt f X x₀) :
  jump f x₀ = 0 := by
  rw [mem_nhds_iff_exists_Ioo_subset] at h
  choose l u hx₀ hX using h; simp at hx₀
  have hl : ∃ ε>0, .Ioc (x₀-ε) x₀ ⊆ X :=
    ⟨ x₀-l, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  have hu : ∃ ε>0, .Ico x₀ (x₀+ε) ⊆ X :=
    ⟨ u-x₀, by linarith, Set.Subset.trans (by intro x ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩) hX ⟩
  simp [jump, left_lim_of_continuous hl hf, right_lim_of_continuous hu hf]

/-- Right limits exist for monotone functions -/
theorem right_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Ioi x₀) f (sInf (f '' .Ioi x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsGT
  rw [bddBelow_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem right_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  right_lim f x₀ = sInf (f '' .Ioi x₀) := right_lim_def (right_lim_of_monotone x₀ hf)

/-- Left limits exist for monotone functions -/
theorem left_lim_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  Convergesto (.Iio x₀) f (sSup (f '' .Iio x₀)) x₀ := by
  rw [Convergesto.iff]
  apply (hf.monotoneOn _).tendsto_nhdsLT
  rw [bddAbove_def]; use f x₀; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind

theorem left_lim_of_monotone' {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  left_lim f x₀ = sSup (f '' .Iio x₀) := left_lim_def (left_lim_of_monotone x₀ hf)

theorem jump_of_monotone {f: ℝ → ℝ} (x₀:ℝ) (hf: Monotone f) :
  0 ≤ jump f x₀  := by
  simp [jump, left_lim_of_monotone' x₀ hf, right_lim_of_monotone' x₀ hf]
  apply csSup_le (by simp); intro a ha
  apply le_csInf (by simp); intro b hb; simp at ha hb
  obtain ⟨ x, hx, rfl ⟩ := ha; obtain ⟨ y, hy, rfl ⟩ := hb
  apply hf; grind

theorem right_lim_le_left_lim_of_monotone {f:ℝ → ℝ} {a b:ℝ} (hab: a < b)
  (hf: Monotone f) :
  right_lim f a ≤ left_lim f b := by
  rw [left_lim_of_monotone' b hf, right_lim_of_monotone' a hf]
  calc
    _ ≤ f ((a+b)/2) := by
      apply csInf_le
      . rw [bddBelow_def]; use f a; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith
    _ ≤ _ := by
      apply le_csSup
      . rw [bddAbove_def]; use f b; intro y hy; simp at hy; obtain ⟨ x, hx, rfl ⟩ := hy; apply hf; grind
      simp; use (a+b)/2; simp; linarith

/-- Definition 11.8.1 -/
noncomputable abbrev α_length (α: ℝ → ℝ) (I: BoundedInterval) : ℝ := match I with
| Icc a b => if a ≤ b then (right_lim α b) - (left_lim α a) else 0
| Ico a b => if a ≤ b then (left_lim α b) - (left_lim α a) else 0
| Ioc a b => if a ≤ b then (right_lim α b) - (right_lim α a) else 0
| Ioo a b => if a < b then (left_lim α b) - (right_lim α a) else 0

syntax:max term "[" term "]ₗ" : term
macro_rules | `($α[$I]ₗ) => `(α_length $α $I)

theorem α_length_of_empty (α: ℝ → ℝ) {I: BoundedInterval} (hI: (I:Set ℝ) = ∅) : α[I]ₗ = 0 :=
  match I with
  | Icc _ _ => by simp [Set.Icc_eq_empty_iff] at *; simp [*]
  | Ico a b => by simp [Set.Ico_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioc a b => by simp [Set.Ioc_eq_empty_iff] at *; intro h; have := le_antisymm hI h; subst this; simp
  | Ioo _ _ => by simp [Set.Ioo_eq_empty_iff] at *; simp [*]

@[simp]
theorem α_length_of_pt {α: ℝ → ℝ} (a:ℝ) : α[Icc a a]ₗ = jump α a := by simp [α_length, jump]

theorem α_length_of_cts {α:ℝ → ℝ} {I: BoundedInterval} {a b: ℝ}
  (haa: a < I.a) (hab: I.a ≤ I.b) (hbb: I.b < b)
  (hI : I ⊆ Ioo a b) (hα: ContinuousOn α (Ioo a b)) :
  α[I]ₗ = α I.b - α I.a := by
  have ha_left : left_lim α I.a = α I.a := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.a - a, by grind, by intro _; simp; grind ⟩
  have ha_right : right_lim α I.a = α I.a := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.a, by grind, by intro _; simp; grind ⟩
  have hb_left : left_lim α I.b = α I.b := by
    apply left_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ I.b - a, by grind, by intro _; simp; grind ⟩
  have hb_right : right_lim α I.b = α I.b := by
    apply right_lim_of_continuous _ (hα.continuousWithinAt (by simp; grind))
    exact ⟨ b - I.b, by grind, by intro _; simp; grind ⟩
  cases I with
  | Icc _ _ => grind
  | Ico _ _ => grind
  | Ioc _ _ => grind
  | Ioo _ _ => simp [α_length, ha_right, hb_left]; intro h; have := le_antisymm h (by linarith); subst this; simp

/-- Example 11.8.2 -/
example : (fun x ↦ x^2)[Icc 2 3]ₗ = 5 := by
  unfold α_length
  simp; rw [if_pos (by linarith)]
  have hr : right_lim (fun x ↦ x ^ 2) 3 = 9 := by
    unfold right_lim
    apply Filter.Tendsto.limUnder_eq
    have hsq : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 3) (nhds 9) := by
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds 3) (nhds 3) := by
        exact Filter.tendsto_id
      convert hid.pow 2; norm_num
    apply hsq.mono_left
    exact nhdsWithin_le_nhds
  have hl : left_lim (fun x ↦ x ^ 2) 2 = 4 := by
    unfold left_lim
    apply Filter.Tendsto.limUnder_eq
    have hsq : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 2) (nhds 4) := by
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds 2) (nhds 2) := by
        exact Filter.tendsto_id
      convert hid.pow 2; norm_num
    apply hsq.mono_left
    exact nhdsWithin_le_nhds
  rw [hl, hr]
  norm_num

example : (fun x ↦ x^2)[Icc 2 2]ₗ = 0 := by
  rw [α_length_of_pt]
  unfold jump
  have hr : right_lim (fun x ↦ x ^ 2) 2 = 4 := by
    unfold right_lim
    apply Filter.Tendsto.limUnder_eq
    have hsq : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 2) (nhds 4) := by
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds 2) (nhds 2) := by
        exact Filter.tendsto_id
      convert hid.pow 2; norm_num
    apply hsq.mono_left
    exact nhdsWithin_le_nhds
  have hl : left_lim (fun x ↦ x ^ 2) 2 = 4 := by
    unfold left_lim
    apply Filter.Tendsto.limUnder_eq
    have hsq : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 2) (nhds 4) := by
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds 2) (nhds 2) := by
        exact Filter.tendsto_id
      convert hid.pow 2; norm_num
    apply hsq.mono_left
    exact nhdsWithin_le_nhds
  rw [hr, hl]
  norm_num


example : (fun x ↦ x^2)[Ioo 2 2]ₗ = 0 := by
  rw [α_length_of_empty]
  simp

/-- Example 11.8.3 -/
@[simp]
theorem α_len_of_id (I: BoundedInterval) : (fun x ↦ x)[I]ₗ = |I|ₗ := by
  by_cases! h: I.b < I.a
  . unfold α_length; match I with
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      unfold length; simp [BoundedInterval.a, BoundedInterval.b]
      rw [if_neg (by linarith)]
      simp; linarith
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      unfold length; simp [BoundedInterval.a, BoundedInterval.b]
      rw [if_neg (by linarith)]
      simp; linarith
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      unfold length; simp [BoundedInterval.a, BoundedInterval.b]
      rw [if_neg (by linarith)]
      simp; linarith
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      unfold length; simp [BoundedInterval.a, BoundedInterval.b]
      rw [if_neg (by linarith)]
      simp; linarith
  . unfold α_length
    have hr : ∀ (b:ℝ), right_lim (fun x ↦ x) b = b := by
      intro b
      unfold right_lim
      apply Filter.Tendsto.limUnder_eq
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds b) (nhds b) := by
        exact Filter.tendsto_id
      apply hid.mono_left
      exact nhdsWithin_le_nhds
    have hl :  ∀ (a:ℝ), left_lim (fun x ↦ x) a = a := by
      intro a
      unfold left_lim
      apply Filter.Tendsto.limUnder_eq
      have hid : Filter.Tendsto (fun (x:ℝ) ↦ x) (nhds a) (nhds a) := by
        exact Filter.tendsto_id
      apply hid.mono_left
      exact nhdsWithin_le_nhds
    match I with
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      simp [h, BoundedInterval.a, BoundedInterval.b]
      rw [hl a, hr b]
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      rcases h.eq_or_lt with heq | hlt
      . simp; rw [if_neg (by linarith)]
        simp [length, BoundedInterval.a, BoundedInterval.b]
        linarith
      simp [hlt, length, BoundedInterval.a, BoundedInterval.b]
      rw [hl b, hr a];
      simp; linarith
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      simp [h, BoundedInterval.a, BoundedInterval.b]
      rw [hr b, hr a]
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h
      simp [h, BoundedInterval.a, BoundedInterval.b]
      rw [hl a, hl b]


/-- An improved version of {name}`BoundedInterval.joins` that also controls {name}`α_length`. -/
abbrev BoundedInterval.joins' (K I J: BoundedInterval) : Prop :=  K.joins I J ∧ ∀ α:ℝ → ℝ, α[K]ₗ = α[I]ₗ + α[J]ₗ

theorem BoundedInterval.join_Icc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Icc a b) (Ioc b c) := ⟨ join_Icc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩


theorem BoundedInterval.join_Icc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ico a c).joins' (Icc a b) (Ioo b c) := ⟨ join_Icc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioc a b) (Ioc b c) := ⟨ join_Ioc_Ioc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioc_Ioo' {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) : (Ioo a c).joins' (Ioc a b) (Ioo b c) := ⟨ join_Ioc_Ioo hab hbc,
  by simp [α_length, show a ≤ b by grind, show b < c by grind, show a < c by grind] ⟩

theorem BoundedInterval.join_Ico_Icc' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Icc a c).joins' (Ico a b) (Icc b c) := ⟨ join_Ico_Icc hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ico_Ico' {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) : (Ico a c).joins' (Ico a b) (Ico b c) := ⟨ join_Ico_Ico hab hbc,
  by simp [α_length, show a ≤ b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Icc' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioc a c).joins' (Ioo a b) (Icc b c) := ⟨ join_Ioo_Icc hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a ≤ c by grind] ⟩

theorem BoundedInterval.join_Ioo_Ico' {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) : (Ioo a c).joins' (Ioo a b) (Ico b c) := ⟨ join_Ioo_Ico hab hbc,
  by simp [α_length, show a < b by grind, show b ≤ c by grind, show a < c by grind] ⟩

lemma BoundedInterval.singleton_Icc {c : ℝ} {I : BoundedInterval} (h : (I:Set ℝ) = {c}) : I = Icc c c := by
  match I with
  | Icc a b => simp at h; rw [h.1, h.2]
  | Ioo a b =>
    simp at h; exfalso
    by_cases hab : a < b
    . have hinfin := Set.Ioo.infinite hab
      rw [h] at hinfin
      contrapose! hinfin
      exact Finite.of_subsingleton
    . have hempty := Set.Ioo_eq_empty hab
      rw [h] at hempty
      simp at hempty
  | Ico a b =>
    simp at h; exfalso
    by_cases hab : a < b
    . have hinfin := Set.Ico.infinite hab
      rw [h] at hinfin
      contrapose! hinfin
      exact Finite.of_subsingleton
    . have hempty := Set.Ico_eq_empty hab
      rw [h] at hempty
      simp at hempty
  | Ioc a b =>
    simp at h; exfalso
    by_cases hab : a < b
    . have hinfin := Set.Ioc.infinite hab
      rw [h] at hinfin
      contrapose! hinfin
      exact Finite.of_subsingleton
    . have hempty := Set.Ioc_eq_empty hab
      rw [h] at hempty
      simp at hempty

lemma BoundedInterval.partition_of_Icc {c : ℝ} {I : BoundedInterval} {P: Partition I} (h : I = Icc c c) :
  ∀ J ∈ P.intervals, J = Icc c c ∨ (J:Set ℝ) = ∅ := by
  intro J hJ
  by_contra! h'
  obtain ⟨hIcc, hnonempty⟩ := h'
  have hlength : 0 < J.length := by
    by_contra! h'
    replace h' : J.length = 0 := by linarith [BoundedInterval.length_nonneg J]
    have hsubsing := BoundedInterval.length_of_subsingleton.mpr h'; simp at hsubsing
    rcases Set.Subsingleton.eq_empty_or_singleton hsubsing with hempty | hsingle
    . refine absurd hempty ?_
      push_neg; exact hnonempty
    . choose x hx using hsingle
      have hIcc' := BoundedInterval.singleton_Icc hx
      have hneq : x ≠ c := by
        intro h'; subst h'; tauto
      have hcontains := P.contains J hJ
      rw [h, hIcc', BoundedInterval.subset_iff] at hcontains
      simp at hcontains
      exact absurd hcontains hneq
  have hnotsingle : ¬ (Subsingleton (J:Set ℝ)) := by
    intro h'
    exact absurd (BoundedInterval.length_of_subsingleton.mp h') (by linarith)
  simp at hnotsingle
  choose x hx y hy hxy using hnotsingle
  have hxI : x ∈ I := by
    apply P.contains J hJ
    exact hx
  have hyI : y ∈ I := by
    apply P.contains J hJ
    exact hy
  rw [h, BoundedInterval.mem_iff] at hxI hyI
  simp at hxI hyI
  exact absurd (by linarith) hxy


/-- Theorem 11.8.4 / Exercise 11.8.1 -/
theorem Partition.sum_of_α_length  {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ) :
  ∑ J ∈ P.intervals, α[J]ₗ = α[I]ₗ := by
  generalize hcard : P.intervals.card = n
  revert I
  induction' n with k ih <;> intro I P hcard
  . have hemp : P.intervals = ∅ := by exact Finset.card_eq_zero.mp hcard
    have hempI : (I:Set ℝ) = ∅ := by
      by_contra! h'
      choose x hx using h'
      obtain ⟨J, ⟨hJ, _⟩, _⟩ := P.exists_unique x hx
      rw [hemp] at hJ
      simp at hJ
    rw [hemp]; simp; symm
    exact α_length_of_empty α hempI
  by_cases h : Subsingleton (I : Set ℝ)
  . simp at h
    rcases Set.Subsingleton.eq_empty_or_singleton h with hempty | hsingle
    . have hemp : ∀ J ∈ P.intervals, (J:Set ℝ) = ∅ := by
        intro J hJ
        contrapose! hempty
        choose x hx using hempty
        use x
        apply P.contains J hJ
        exact hx
      rw [α_length_of_empty α hempty]
      apply Finset.sum_eq_zero
      intro J hJ
      specialize hemp J hJ
      exact α_length_of_empty α hemp
    . choose c hc using hsingle
      have hIcc := BoundedInterval.singleton_Icc hc
      apply Finset.sum_eq_single_of_mem
      . simp [hIcc]
        by_contra! h'
        have hcI : c ∈ I := by rw [BoundedInterval.mem_iff, hc]; tauto
        obtain ⟨J, ⟨hJ, hcJ⟩, _⟩ := P.exists_unique c hcI
        rcases BoundedInterval.partition_of_Icc hIcc J hJ with hJ' | hJ'
        . contrapose! h'
          rw [← hJ']
          exact hJ
        . contrapose! hJ'
          use c; exact hcJ
      . intro J hJ hJI
        rcases BoundedInterval.partition_of_Icc hIcc J hJ with hJ' | hJ'
        . contrapose! hJI
          rw [hIcc, hJ']
        . exact α_length_of_empty α hJ'
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  have : ∃ K L : BoundedInterval, K ∈ P ∧ I.joins' L K := by
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
        | Icc a b => use (Icc b b), hK, Ico a b; apply join_Ico_Icc' <;> order
        | Ioc a b => use (Icc b b), hK, Ioo a b; apply join_Ioo_Icc' <;> order
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
        | Icc c₂ b₂ => use Ico a₁ c₂, hK; simp_all; apply join_Ico_Icc' <;> order
        | Ioc c₂ b₂ => use Icc a₁ c₂, hK; simp_all; apply join_Icc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff] at *; grind
      | Ioc a₁ b₁ =>
        use K; cases K with
        | Ioo _ _ => simp_all [mem_iff]
        | Icc c₂ b₂ =>
          use Ioo a₁ c₂, hK
          simp_all [subset_iff]
          have : c₂ ∈ Set.Icc c₂ b₁ := by grind
          apply hKI at this; grind [join_Ioo_Icc]
        | Ioc c₂ b₂ => use Ioc a₁ c₂, hK; simp_all; apply join_Ioc_Ioc' <;> order
        | Ico _ _ => simp [mem_iff, subset_iff] at *; grind
      | Ico _ _ => simp [mem_iff] at hI'
    choose c hc hK using P.exist_right h hI'
    cases I with
    | Ioo a₁ b₁ =>
      obtain hK | hK := hK <;> simp_all [mem_iff]
      . use Ioo c b₁, hK, Ioc a₁ c; apply join_Ioc_Ioo' <;> tauto
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
  obtain ⟨ K, L, hK, ⟨h1, h2, h3⟩, hα⟩ := this
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
  rw [hα α, ← Finset.add_sum_erase _ _ hK, ← hP', add_comm]; congr
  apply ih; simp [hP', Finset.card_erase_of_mem hK, hcard]


/-- Definition 11.8.5 (Piecewise constant RS integral). -/
noncomputable abbrev PiecewiseConstantWith.RS_integ (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α: ℝ → ℝ)   :
  ℝ := ∑ J ∈ P.intervals, constant_value_on f (J:Set ℝ) * α[J]ₗ

/-- Example 11.8.6 -/
noncomputable abbrev f_11_8_6 (x:ℝ) : ℝ := if x < 2 then 4 else 2

noncomputable abbrev P_11_8_6 : Partition (Icc 1 3) :=
  (⊥: Partition (Ico 1 2)).join (⊥ : Partition (Icc 2 3))
  (join_Ico_Icc (by norm_num) (by norm_num) )

theorem f_11_8_6_RS_integ : PiecewiseConstantWith.RS_integ f_11_8_6 P_11_8_6 (fun x ↦ x^2) = 22 := by
  unfold PiecewiseConstantWith.RS_integ
  rw [show P_11_8_6.intervals = {Ico 1 2, Icc 2 3} by rfl, Finset.sum_pair (by simp)]
  have hIco12 : constant_value_on f_11_8_6 (Ico 1 2) = 4 := by
    apply ConstantOn.const_eq (by simp)
    intro x hx
    unfold f_11_8_6
    simp at hx
    simp [hx]
  have hIcc23 : constant_value_on f_11_8_6 (Icc 2 3) = 2 := by
    apply ConstantOn.const_eq (by simp; norm_num)
    intro x hx
    unfold f_11_8_6
    simp at hx
    simp [hx]
  have hαIco12 : α_length (fun x ↦ x ^ 2) (Ico 1 2) = 3 := by
    unfold α_length; simp
    have hl4 : left_lim (fun x ↦ x ^ 2) 2 = 4 := by
      unfold left_lim
      apply Filter.Tendsto.limUnder_eq
      have : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 2) (nhds 4) := by
        refine Continuous.tendsto' ?_ 2 4 (by norm_num)
        exact continuous_pow 2
      apply this.mono_left
      exact nhdsWithin_le_nhds
    have hl1 : left_lim (fun x ↦ x ^ 2) 1 = 1 := by
      unfold left_lim
      apply Filter.Tendsto.limUnder_eq
      have : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 1) (nhds 1) := by
        refine Continuous.tendsto' ?_ 1 1 (by norm_num)
        exact continuous_pow 2
      apply this.mono_left
      exact nhdsWithin_le_nhds
    rw [hl4, hl1]; norm_num
  have hαIcc23 : α_length (fun x ↦ x ^ 2) (Icc 2 3) = 5 := by
    unfold α_length; simp
    rw [if_pos (by norm_num)]
    have hl4 : left_lim (fun x ↦ x ^ 2) 2 = 4 := by
      unfold left_lim
      apply Filter.Tendsto.limUnder_eq
      have : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 2) (nhds 4) := by
        refine Continuous.tendsto' ?_ 2 4 (by norm_num)
        exact continuous_pow 2
      apply this.mono_left
      exact nhdsWithin_le_nhds
    have hr9 : right_lim (fun x ↦ x ^ 2) 3 = 9 := by
      unfold right_lim
      apply Filter.Tendsto.limUnder_eq
      have : Filter.Tendsto (fun (x:ℝ) ↦ x ^ 2) (nhds 3) (nhds 9) := by
        refine Continuous.tendsto' ?_ 3 9 (by norm_num)
        exact continuous_pow 2
      apply this.mono_left
      exact nhdsWithin_le_nhds
    rw [hl4, hr9]; norm_num
  rw [hIco12, hIcc23, hαIco12, hαIcc23]
  norm_num



/-- Example 11.8.7 -/
theorem PiecewiseConstantWith.RS_integ_eq_integ {f:ℝ → ℝ} {I: BoundedInterval} (P: Partition I) : RS_integ f P (fun x ↦ x) = integ f P := by
  unfold RS_integ integ
  simp

open Classical in
lemma α_length_congr  {I J : BoundedInterval} (α: ℝ → ℝ) (h: (I:Set ℝ)=(J:Set ℝ)) : α[I]ₗ = α[J]ₗ := by
  by_cases h' : Subsingleton (I:Set ℝ)
  . simp at h'
    rcases Set.Subsingleton.eq_empty_or_singleton h' with hempty | hsingleton
    . have hempty' : (J:Set ℝ) = ∅ := by rwa [← h]
      have hI := α_length_of_empty α hempty
      have hJ := α_length_of_empty α hempty'
      simp [hI, hJ]
    . choose x hx using hsingleton
      rw [hx] at h; symm at h
      rw [BoundedInterval.singleton_Icc hx, BoundedInterval.singleton_Icc h]
  . have h'' := h'
    rw [h] at h''
    simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h'
    simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h''
    have hSupI : sSup (I : Set ℝ) = I.b := by
      match I with
      | Ioo a b => simp [csSup_Ioo h']
      | Icc a b => simp [csSup_Icc h'.le]
      | Ioc a b => simp [csSup_Ioc h']
      | Ico a b => simp [csSup_Ico h']
    have hInfI : sInf (I : Set ℝ) = I.a:= by
      match I with
      | Ioo a b => simp [csInf_Ioo h']
      | Icc a b => simp [csInf_Icc h'.le]
      | Ioc a b => simp [csInf_Ioc h']
      | Ico a b => simp [csInf_Ico h']
    have hSupJ : sSup (J : Set ℝ) = J.b := by
      match J with
      | Ioo a b => simp [csSup_Ioo h'']
      | Icc a b => simp [csSup_Icc h''.le]
      | Ioc a b => simp [csSup_Ioc h'']
      | Ico a b => simp [csSup_Ico h'']
    have hInfJ : sInf (J : Set ℝ) = J.a := by
      match J with
      | Ioo a b => simp [csInf_Ioo h'']
      | Icc a b => simp [csInf_Icc h''.le]
      | Ioc a b => simp [csInf_Ioc h'']
      | Ico a b => simp [csInf_Ico h'']
    have ha : I.a = J.a := by rw [← hInfI, ← hInfJ, h]
    have hb : I.b = J.b := by rw [← hSupI, ← hSupJ, h]
    have heq : I = J := by
      cases I <;> cases J <;> simp_all [BoundedInterval.a, BoundedInterval.b]
    rw [heq]

lemma α_length_inter_comm {I J : BoundedInterval} (α : ℝ → ℝ): α[I ∩ J]ₗ = α[J ∩ I]ₗ := by
  suffices (((I ∩ J):BoundedInterval):Set ℝ) = (((J ∩ I):BoundedInterval):Set ℝ) by exact α_length_congr α this
  simp [BoundedInterval.inter_eq, Set.inter_comm]

open Classical in
theorem Partition.sum_α_length_restrict {α:ℝ → ℝ} {I : BoundedInterval} (P' : Partition I)
    {K : BoundedInterval} (hK : K ⊆ I) :
    ∑ J ∈ P'.intervals, α[(K ∩ J : BoundedInterval)]ₗ = α[K]ₗ := by
  rw [← Partition.sum_of_α_length (I:=K) (α:=α) (P'.restrict hK)]
  simp only [Partition.restrict]
  rw [Finset.sum_comp (α_length α) (fun J => K ∩ J)]
  apply Finset.sum_congr rfl
  intro A hA; simp at hA
  choose B hBP' hKB using hA
  by_cases hempty : (A:Set ℝ) = ∅
  . have := α_length_of_empty (α:=α) (hI:=hempty)
    simp [this]
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

theorem PiecewiseConstantWith.RS_integ_mono {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (α:ℝ → ℝ) (hP: PiecewiseConstantWith f P) (hPP' : P ≤ P') : RS_integ f P α = RS_integ f P' α := by
  have hLHS : RS_integ f P α  = ∑ K ∈ P.intervals, ∑ K' ∈ P'.intervals, constant_value_on f K * α[(K ∩ K' : BoundedInterval)]ₗ := by
    unfold RS_integ
    apply Finset.sum_congr rfl
    intro J hJ
    rw [← Partition.sum_α_length_restrict (α:=α) P' (P.contains J hJ)]
    rw [Finset.mul_sum]
  have hRHS : RS_integ f P' α = ∑ K' ∈ P'.intervals, ∑ K ∈ P.intervals, constant_value_on f K' * α[(K' ∩ K : BoundedInterval)]ₗ := by
    unfold RS_integ
    apply Finset.sum_congr rfl
    intro J hJ
    rw [← Partition.sum_α_length_restrict (α:=α) P (P'.contains J hJ)]
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
    rw [hconst, hconst', α_length_inter_comm α]
  . have hn' := hn; rw [Set.inter_comm] at hn
    rw [← BoundedInterval.inter_eq] at hn hn'
    replace hn := α_length_of_empty α hn
    replace hn' := α_length_of_empty α hn'
    rw [hn, hn']
    simp


/-- Analogue of Proposition 11.2.13 -/
theorem PiecewiseConstantWith.RS_integ_eq {f:ℝ → ℝ} {I: BoundedInterval} {P P': Partition I}
  (hP: PiecewiseConstantWith f P) (hP': PiecewiseConstantWith f P') (α:ℝ → ℝ): RS_integ f P α = RS_integ f P' α := by
  have ⟨h, h'⟩ := BoundedInterval.le_max P P'
  set Q := P ⊔ P'
  have hQ := PiecewiseConstantWith.RS_integ_mono α hP h
  have hQ' := PiecewiseConstantWith.RS_integ_mono α hP' h'
  rw [hQ, hQ']


open Classical in
noncomputable abbrev PiecewiseConstantOn.RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ):
  ℝ := if h: PiecewiseConstantOn f I then PiecewiseConstantWith.RS_integ f h.choose α else 0

theorem PiecewiseConstantOn.RS_integ_def {f:ℝ → ℝ} {I: BoundedInterval} {P: Partition I}
  (h: PiecewiseConstantWith f P) (α:ℝ → ℝ) : RS_integ f I α = PiecewiseConstantWith.RS_integ f P α := by
  have h' : PiecewiseConstantOn f I := by use P
  simp [RS_integ, h']; exact PiecewiseConstantWith.RS_integ_eq h'.choose_spec h α

/-- {name}`α_length` non-negative when α monotone -/
theorem α_length_nonneg_of_monotone {α:ℝ → ℝ}  (hα: Monotone α) (I: BoundedInterval):
  0 ≤ α[I]ₗ := by
  by_cases h : Subsingleton (I : Set ℝ)
  . simp at h
    rcases Set.Subsingleton.eq_empty_or_singleton h with hempty | hsingleton
    . suffices  α_length α I = 0 by linarith
      exact α_length_of_empty α hempty
    . choose x hx using hsingleton
      rw [BoundedInterval.singleton_Icc hx, α_length_of_pt]
      exact jump_of_monotone x hα
  simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h
  unfold α_length
  match I with
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h ⊢
      rw [if_pos (by linarith)]
      simp; rw [left_lim_of_monotone' a hα, right_lim_of_monotone' b hα]
      apply csSup_le (by simp)
      intro x hx
      obtain ⟨p, hp, rfl⟩ := hx
      apply le_csInf (by simp)
      intro y hy
      obtain ⟨q, hq, rfl⟩ := hy
      apply hα
      simp at hp hq; linarith
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h ⊢
      rw [if_pos (by linarith)]
      simp; rw [left_lim_of_monotone' a hα, left_lim_of_monotone' b hα]
      apply csSup_le_csSup
      . use α b; intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        apply hα
        simp at hp; linarith
      . simp
      . intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        simp; use p; simp at hp ⊢
        linarith
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h ⊢
      rw [if_pos (by linarith)]
      simp; rw [right_lim_of_monotone' a hα, right_lim_of_monotone' b hα]
      apply csInf_le_csInf
      . use α a; intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        apply hα
        simp at hp; linarith
      . simp
      . intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        simp; use p; simp at hp ⊢
        linarith
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at h ⊢
      simp [h]
      exact right_lim_le_left_lim_of_monotone h hα



/-- Analogue of Theorem 11.2.16 (a) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_add {f g: ℝ → ℝ} {I: BoundedInterval}
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (f + g) I α = RS_integ f I α + RS_integ g I α := by
  have hadd := PiecewiseConstantOn.add hf hg
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  choose P₃ hP₃ using hadd
  have ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
  have ⟨h₃, hmax⟩ := BoundedInterval.le_max (P₁ ⊔ P₂) P₃
  set Q := P₁ ⊔ P₂ ⊔ P₃
  have hfQ : PiecewiseConstantWith f Q := by apply hP₁.mono; order
  have hgQ : PiecewiseConstantWith g Q := by apply hP₂.mono; order
  have haddQ : PiecewiseConstantWith (f+g) Q := by apply hP₃.mono; order
  rw [
    PiecewiseConstantOn.RS_integ_def hfQ α,
    PiecewiseConstantOn.RS_integ_def hgQ α,
    PiecewiseConstantOn.RS_integ_def haddQ α
  ]
  simp only [PiecewiseConstantWith.RS_integ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← add_mul]
  by_cases! hemp : (J:Set ℝ).Nonempty
  . congr; exact constant_value_on_of_add hJ hemp hfQ hgQ
  . simp [α_length_of_empty α hemp]


/-- Analogue of Theorem 11.2.16 (b) (Laws of integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_smul {f: ℝ → ℝ} {I: BoundedInterval} (c:ℝ)
  (hf: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (c • f) I α = c * RS_integ f I α
   := by
  have hsmul := PiecewiseConstantOn.smul c hf
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hsmul
  have ⟨h₁, h₂⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  have hfQ : PiecewiseConstantWith f Q := by apply hP₁.mono; order
  have hsmulQ : PiecewiseConstantWith (c • f) Q := by apply hP₂.mono; order
  rw [
    PiecewiseConstantOn.RS_integ_def hfQ α,
    PiecewiseConstantOn.RS_integ_def hsmulQ α
  ]
  simp only [PiecewiseConstantWith.RS_integ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [← mul_assoc]
  by_cases! hemp : (J:Set ℝ).Nonempty
  . congr; exact constant_value_on_of_smul hJ hemp hfQ
  . simp [α_length_of_empty α hemp]


/-- Theorem 11.8.8 (c) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_sub {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ (f - g) I α = RS_integ f I α - RS_integ g I α := by
  have heq : (f - g) = f + ((-1:ℝ) • g) := by
    ext x; simp; linarith
  rw [heq]
  have hmulneg : PiecewiseConstantOn ((-1:ℝ) • g) I := by exact smul (-1) hg
  have hneg := PiecewiseConstantOn.RS_integ_smul (c:=-1) (hf:=hg) (hα:=hα)
  simp only [neg_mul, one_mul] at hneg
  have hadd :=  PiecewiseConstantOn.RS_integ_add hf hmulneg hα
  rw [hneg] at hadd
  simpa using hadd


/-- Theorem 11.8.8 (d) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_nonneg {f: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, 0 ≤ f x) (hf: PiecewiseConstantOn f I) :
  0 ≤ RS_integ f I α := by
  choose P hP using hf
  have hfinteg := PiecewiseConstantOn.RS_integ_def hP α
  rw [hfinteg]
  simp only [PiecewiseConstantWith.RS_integ]
  apply Finset.sum_nonneg
  intro J hJ
  by_cases! hemp : (J:Set ℝ).Nonempty
  . have := α_length_nonneg_of_monotone hα J
    suffices 0 ≤ constant_value_on f J by nlinarith
    choose c hc using (PiecewiseConstantWith.def f).mp hP J hJ
    have hconstval := ConstantOn.const_eq (f:=f) (c:=c) hemp hc
    choose x hx using hemp
    specialize hc x hx
    specialize h x (by apply P.contains J hJ; exact hx)
    linarith
  . simp [α_length_of_empty α hemp]


/-- Theorem 11.8.8 (e) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_mono {f g: ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α)
  (h: ∀ x ∈ I, f x ≤ g x) (hf: PiecewiseConstantOn f I) (hg: PiecewiseConstantOn g I) :
  RS_integ f I α ≤ RS_integ g I α := by
  choose P₁ hP₁ using hf
  choose P₂ hP₂ using hg
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set Q := P₁ ⊔ P₂
  have hfQ : PiecewiseConstantWith f Q := by exact PiecewiseConstantWith.mono h1 hP₁
  have hgQ : PiecewiseConstantWith g Q := by exact PiecewiseConstantWith.mono h2 hP₂
  rw [
    PiecewiseConstantOn.RS_integ_def hfQ α,
    PiecewiseConstantOn.RS_integ_def hgQ α
  ]
  simp only [PiecewiseConstantWith.RS_integ]
  apply Finset.sum_le_sum
  intro J hJ
  by_cases! hemp : (J:Set ℝ).Nonempty
  . choose c₁ hc₁ using (PiecewiseConstantWith.def f).mp hfQ J hJ
    choose c₂ hc₂ using (PiecewiseConstantWith.def g).mp hgQ J hJ
    have hconst₁ := ConstantOn.const_eq hemp hc₁
    have hconst₂ := ConstantOn.const_eq hemp hc₂
    rw [hconst₁, hconst₂]
    have := α_length_nonneg_of_monotone hα J
    suffices c₁ ≤ c₂ by nlinarith
    choose x hx using hemp
    specialize hc₁ x hx
    specialize hc₂ x hx
    specialize h x (by apply Q.contains J hJ; exact hx)
    linarith
  . simp [α_length_of_empty α hemp]


/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const (c: ℝ) (I: BoundedInterval) {α:ℝ → ℝ} (hα: Monotone α) :
  RS_integ (fun _ ↦ c) I α = c * α[I]ₗ := by
  set P : Partition I := ⊥
  have hQ : PiecewiseConstantWith (fun _ => c) P := by
    rw [PiecewiseConstantWith.def]
    intro J hJ
    change J ∈ ({I}:Finset BoundedInterval) at hJ
    simp at hJ
    use c; tauto
  rw [PiecewiseConstantOn.RS_integ_def hQ α]
  simp only [PiecewiseConstantWith.RS_integ]
  rw [BoundedInterval.intervals_of_bot, Finset.sum_singleton]
  by_cases! hemp : (I:Set ℝ).Nonempty
  . choose c₁ hc₁ using (PiecewiseConstantWith.def _).mp hQ I (by show I ∈ P.intervals; rw [BoundedInterval.intervals_of_bot]; simp)
    have hconst := ConstantOn.const_eq hemp hc₁
    rw [hconst]
    have key : c₁ = c := by
      choose x hx using hemp
      specialize hc₁ x hx
      linarith
    rw [key]
  . simp [α_length_of_empty α hemp]

/-- Theorem 11.8.8 (f) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_const' {f:ℝ → ℝ} {I: BoundedInterval}
  {α:ℝ → ℝ} (hα: Monotone α) (h: ConstantOn f I) :
  RS_integ f I α = (constant_value_on f I) * α[I]ₗ := by
  have h' : PiecewiseConstantWith f (⊥: Partition I) := by
    intro J hJ
    change J ∈ ({I}:Finset BoundedInterval) at hJ
    simp at hJ
    subst hJ
    exact h
  rw [PiecewiseConstantOn.RS_integ_def h']
  simp only [PiecewiseConstantWith.RS_integ]
  have : (⊥:Partition I).intervals = ({I}:Finset BoundedInterval) := by rfl
  rw [this, Finset.sum_singleton]

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  PiecewiseConstantOn (fun x ↦ if x ∈ I then f x else 0) J := by
  exact of_extend hIJ h

open Classical in
/-- Theorem 11.8.8 (g) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_extend {I J: BoundedInterval} (hIJ: I ⊆ J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f I) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ (fun x ↦ if x ∈ I then f x else 0) J α = RS_integ f I α := by
  have hpw := PiecewiseConstantOn.of_extend hIJ h
  choose P₁ hP₁ using hpw
  choose P₂ hP₂ hdisj using Partition.exists_extend hIJ ⊥
  obtain ⟨h1, h2⟩ := BoundedInterval.le_max P₁ P₂
  set P := P₁ ⊔ P₂
  have hP := hP₁.mono h1
  rw [PiecewiseConstantOn.RS_integ_def hP]
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
  rw [PiecewiseConstantOn.RS_integ_def hf]
  simp only [PiecewiseConstantWith.RS_integ]
  have hQP : Q.intervals ⊆ P.intervals := by
    apply Finset.filter_subset
  have hzero : ∀ K ∈ P.intervals, K ∉ Q.intervals → constant_value_on (fun x ↦ if x ∈ I then f x else 0) K * α[K]ₗ = 0 := by
    intro K hK hK'
    have hnotsub : ¬ ((K:Set ℝ) ⊆ (I:Set ℝ)) := by
      intro hsub
      exact hK' (by exact Finset.mem_filter.mpr ⟨hK, hsub⟩)
    have hdisjK : Disjoint (K:Set ℝ) (I:Set ℝ) := by
      exact (hcell K hK).resolve_left hnotsub
    by_cases! hne : (K:Set ℝ).Nonempty
    . have h0 : constant_value_on (fun x ↦ if x ∈ I then f x else 0) K = 0 := by
        apply ConstantOn.const_eq hne
        intro x hx
        have : x ∉ (I:Set ℝ) := by
          exact Disjoint.notMem_of_mem_left hdisjK hx
        rw [if_neg (by simpa using this)]
      rw [h0]; simp
    . simp [α_length_of_empty α hne]
  rw [← Finset.sum_subset hQP hzero]
  apply Finset.sum_congr rfl
  intro K hK
  have : (K:Set ℝ) ⊆ (I:Set ℝ) := by exact (Finset.mem_filter.mp hK).2
  rw [constant_value_on_congr]
  intro x hx
  rw [if_pos (by apply this; exact hx)]


/-- Theorem 11.8.8 (h) (Laws of RS integration) / Exercise 11.8.3 -/
theorem PiecewiseConstantOn.RS_integ_of_join {I J K: BoundedInterval} (hIJK: K.joins' I J)
  {f: ℝ → ℝ} (h: PiecewiseConstantOn f K) {α:ℝ → ℝ} (hα: Monotone α):
  RS_integ f K α = RS_integ f I α + RS_integ f J α := by
  obtain ⟨hIJK, h'⟩ := hIJK
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
  rw [PiecewiseConstantOn.RS_integ_def hPQ, PiecewiseConstantOn.RS_integ_def hP, PiecewiseConstantOn.RS_integ_def hQ]
  simp only [PiecewiseConstantWith.RS_integ]
  rw [← Finset.sum_union_inter]
  suffices ∑ ℓ ∈ P.intervals ∩ Q.intervals, constant_value_on f ℓ * α[ℓ]ₗ = 0 by linarith
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
  rw [α_length_of_empty α hLemp, mul_zero]


/-- Analogue of Definition 11.3.2 (Upper and lower Riemann integrals ). -/
noncomputable abbrev upper_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sInf ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})

noncomputable abbrev lower_RS_integral (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ): ℝ :=
  sSup ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})

lemma RS_integral_bound_upper_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval}
  (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ M, ⟨ ⟨ ?_, ?_ ⟩, PiecewiseConstantOn.RS_integ_const M I hα ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_lower_of_bounded {f:ℝ → ℝ} {M:ℝ} {I: BoundedInterval} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M) {α:ℝ → ℝ} (hα:Monotone α)
  : -M * α[I]ₗ ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I} := by
  simp; refine ⟨ fun _ ↦ -M, ⟨ ⟨ ?_, ?_ ⟩, by convert PiecewiseConstantOn.RS_integ_const _ _ hα using 1; simp ⟩ ⟩
  . grind [abs_le']
  exact (ConstantOn.of_const (c := -M) (by simp)).piecewiseConstantOn


lemma RS_integral_bound_upper_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_upper_of_bounded h hα)

lemma RS_integral_bound_lower_nonempty {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  ((PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}).Nonempty := by
  choose M h using h; exact Set.nonempty_of_mem (RS_integral_bound_lower_of_bounded h hα)

lemma RS_integral_bound_lower_le_upper {f:ℝ → ℝ} {I: BoundedInterval} {a b:ℝ}
  {α:ℝ → ℝ} (hα: Monotone α)
  (ha: a ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I})
  (hb: b ∈ (PiecewiseConstantOn.RS_integ · I α) '' {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I})
  : b ≤ a:= by
    have ⟨ g, ⟨ ⟨ hmaj, hgp⟩, hgi ⟩ ⟩ := ha
    have ⟨ h, ⟨ ⟨ hmin, hhp⟩, hhi ⟩ ⟩ := hb
    rw [←hgi, ←hhi]; apply hhp.RS_integ_mono hα _ hgp; intro _ hx; linarith [hmin _ hx, hmaj _ hx]

lemma RS_integral_bound_below {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  BddBelow ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MajorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddBelow_def]; use (RS_integral_bound_lower_nonempty h hα).some
    intro a ha; exact RS_integral_bound_lower_le_upper hα ha (RS_integral_bound_lower_nonempty h hα).some_mem

lemma RS_integral_bound_above {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α):
  BddAbove ((PiecewiseConstantOn.RS_integ · I α) ''
    {g | MinorizesOn g f I ∧ PiecewiseConstantOn g I}) := by
    rw [bddAbove_def]; use (RS_integral_bound_upper_nonempty h hα).some
    intro b hb; exact RS_integral_bound_lower_le_upper hα (RS_integral_bound_upper_nonempty h hα).some_mem hb

lemma le_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  -M * α[I]ₗ ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above (BddOn.of_bounded h) hα) (RS_integral_bound_lower_of_bounded h hα)

lemma lower_RS_integral_le_upper {f:ℝ → ℝ} {I: BoundedInterval} (h: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  lower_RS_integral f I α ≤ upper_RS_integral f I α := by
  apply csSup_le (RS_integral_bound_lower_nonempty h hα)
  intros
  apply le_csInf (RS_integral_bound_upper_nonempty h hα)
  intros; solve_by_elim [RS_integral_bound_lower_le_upper]

lemma RS_upper_integral_le {f:ℝ → ℝ} {I: BoundedInterval} {M:ℝ} (h: ∀ x ∈ (I:Set ℝ), |f x| ≤ M)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ M * α[I]ₗ :=
  csInf_le (RS_integral_bound_below (.of_bounded h) hα) (RS_integral_bound_upper_of_bounded h hα)

lemma upper_RS_integral_le_integ {f g:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfg: MajorizesOn g f I) (hg: PiecewiseConstantOn g I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  upper_RS_integral f I α ≤ PiecewiseConstantOn.RS_integ g I α :=
  csInf_le (RS_integral_bound_below hf hα) ⟨ g, by simpa [hg] ⟩

lemma integ_le_lower_RS_integral {f h:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  (hfh: MinorizesOn h f I) (hg: PiecewiseConstantOn h I)
  {α:ℝ → ℝ} (hα: Monotone α) :
  PiecewiseConstantOn.RS_integ h I α ≤ lower_RS_integral f I α :=
  le_csSup (RS_integral_bound_above hf hα) ⟨ h, by simpa [hg] ⟩

lemma lt_of_gt_upper_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α: ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: upper_RS_integral f I α < X ) :
  ∃ g, MajorizesOn g f I ∧ PiecewiseConstantOn g I ∧ PiecewiseConstantOn.RS_integ g I α < X := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_csInf_lt (RS_integral_bound_upper_nonempty hf hα) hX
  simp at hY; have ⟨ g, ⟨ hmaj, hgp ⟩, hgi ⟩ := hY; exact ⟨ g, hmaj, hgp, by rwa [hgi] ⟩

lemma gt_of_lt_lower_RS_integral {f:ℝ → ℝ} {I: BoundedInterval} (hf: BddOn f I)
  {α:ℝ → ℝ} (hα: Monotone α) {X:ℝ} (hX: X < lower_RS_integral f I α) :
  ∃ h, MinorizesOn h f I ∧ PiecewiseConstantOn h I ∧ X < PiecewiseConstantOn.RS_integ h I α := by
  have ⟨ Y, hY, hYX ⟩ := exists_lt_of_lt_csSup (RS_integral_bound_lower_nonempty hf hα) hX
  simp at hY; have ⟨ h, ⟨ hmin, hhp ⟩, hhi ⟩ := hY; exact ⟨ h, hmin, hhp, by rwa [hhi] ⟩

/-- Analogue of Definition 11.3.4 -/
noncomputable abbrev RS_integ (f:ℝ → ℝ) (I: BoundedInterval) (α:ℝ → ℝ) : ℝ := upper_RS_integral f I α

noncomputable abbrev RS_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) (α: ℝ → ℝ) : Prop :=
  BddOn f I ∧ lower_RS_integral f I α = upper_RS_integral f I α

lemma PiecewiseConstantOn.RS_integ_eq_integ (f : ℝ → ℝ) (I : BoundedInterval) :
  RS_integ f I (fun x => x) = integ f I := by
  by_cases hg : PiecewiseConstantOn f I
  . choose P hP using hg
    rw [PiecewiseConstantOn.integ_def hP, PiecewiseConstantOn.RS_integ_def hP]
    exact PiecewiseConstantWith.RS_integ_eq_integ P
  . simp [RS_integ, integ, hg]

/-- Analogue of various components of Lemma 11.3.3 -/
theorem upper_RS_integral_eq_upper_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  upper_RS_integral f I (fun x ↦ x) = upper_integral f I := by
  unfold upper_RS_integral upper_integral
  congr 1
  refine Set.image_congr ?_
  intro g hg
  apply PiecewiseConstantOn.RS_integ_eq_integ


theorem lower_RS_integral_eq_lower_integral (f:ℝ → ℝ) (I: BoundedInterval) :
  lower_RS_integral f I (fun x ↦ x) = lower_integral f I := by
  unfold lower_RS_integral lower_integral
  congr 1
  refine Set.image_congr ?_
  intro g hg
  apply PiecewiseConstantOn.RS_integ_eq_integ


theorem RS_integ_eq_integ (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_integ f I (fun x ↦ x) = integ f I := by
  unfold RS_integ integ
  exact upper_RS_integral_eq_upper_integral f I

theorem RS_IntegrableOn_iff_IntegrableOn (f:ℝ → ℝ) (I: BoundedInterval) :
  RS_IntegrableOn f I (fun x ↦ x) ↔ IntegrableOn f I := by
  constructor
  . intro ⟨hbdd, hagree⟩
    refine ⟨hbdd, ?_⟩
    rwa [← lower_RS_integral_eq_lower_integral f I, ← upper_RS_integral_eq_upper_integral f I]
  . intro ⟨hbdd, hagree⟩
    refine ⟨hbdd, ?_⟩
    rwa [lower_RS_integral_eq_lower_integral f I, upper_RS_integral_eq_upper_integral f I]

noncomputable abbrev upper_RS_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α:ℝ → ℝ) : ℝ :=
  ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * α[J]ₗ

noncomputable abbrev lower_RS_riemann_sum (f:ℝ → ℝ) {I: BoundedInterval} (P: Partition I) (α:ℝ → ℝ) : ℝ :=
  ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * α[J]ₗ

open Classical in
theorem upper_RS_integ_le_upper_sum {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    {α:ℝ → ℝ} (hα: Monotone α) (P: Partition I) :
  upper_RS_integral f I α ≤ upper_RS_riemann_sum f P α := by
  unfold upper_RS_integral upper_RS_riemann_sum
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
  . exact RS_integral_bound_below hf hα
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
    · rw [PiecewiseConstantOn.RS_integ_def hpconstwith]
      simp only [PiecewiseConstantWith.RS_integ]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J:Set ℝ).Nonempty
      . have := α_length_nonneg_of_monotone hα J
        suffices constant_value_on g J = sSup (f '' J) by nlinarith
        apply ConstantOn.const_eq hemp
        intro x hx
        exact hg_eq hJ hx
      . simp [α_length_of_empty α hemp]


open Classical in
theorem lower_RS_integ_le_lower_sum  {f:ℝ → ℝ} {I:BoundedInterval} (hf: BddOn f I)
    {α:ℝ → ℝ} (hα: Monotone α) (P: Partition I) :
  lower_RS_riemann_sum f P α ≤ lower_RS_integral f I α := by
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
  . exact RS_integral_bound_above hf hα
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
    . rw [PiecewiseConstantOn.RS_integ_def hpconstwith]
      simp only [PiecewiseConstantWith.RS_integ]
      apply Finset.sum_congr rfl
      intro J hJ
      by_cases! hemp : (J:Set ℝ).Nonempty
      . have := α_length_nonneg_of_monotone hα J
        suffices constant_value_on g J = sInf (f '' J) by nlinarith
        apply ConstantOn.const_eq hemp
        intro x hx
        exact hg_eq hJ hx
      . simp [α_length_of_empty α hemp]


/-- Exercise 11.8.4 -/
theorem RS_integ_of_uniform_cts {I: BoundedInterval} {f:ℝ → ℝ} (hf: UniformContinuousOn f I)
 {α:ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α := by
  have hfbound : BddOn f I := by
    rw [BddOn.iff']; exact hf.of_bounded subset_rfl (Bornology.IsBounded.of_boundedInterval I)
  refine ⟨hfbound, ?_ ⟩
  by_cases hsing : |I|ₗ = 0
  · haveI hsub : Subsingleton (I:Set ℝ) := length_of_subsingleton.mpr hsing
    have hfpc : PiecewiseConstantOn f I := ConstantOn.of_subsingleton.piecewiseConstantOn
    have hupper := upper_RS_integral_le_integ hfbound (by intro x y; rfl) hfpc hα
    have hlower := integ_le_lower_RS_integral hfbound (by intro x y; rfl) hfpc hα
    apply le_antisymm (lower_RS_integral_le_upper hfbound hα)
    linarith
  simp [length] at hsing
  set a := I.a
  set b := I.b
  have hsing' : 0 < b-a := by linarith
  have (ε:ℝ) (hε: ε > 0) : upper_RS_integral f I α - lower_RS_integral f I α ≤ ε * α[I]ₗ := by
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
      _ ≤ ∑ J ∈ P.intervals, (sSup (f '' J) - sInf (f '' J)) * α[J]ₗ := by
        have h1 := upper_RS_integ_le_upper_sum hfbound hα P
        have h2 := lower_RS_integ_le_lower_sum hfbound hα P
        simp [sub_mul, lower_RS_riemann_sum, upper_RS_riemann_sum] at *
        have := add_le_add h1 h2
        linarith
      _ ≤ ∑ J ∈ P.intervals, ε *  α[J]ₗ  := by
        apply Finset.sum_le_sum; intro J hJ; gcongr
        . exact α_length_nonneg_of_monotone hα J
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
      _ = ε *  ∑ J ∈ P.intervals, α[J]ₗ   := by rw [← Finset.mul_sum]
      _ = ε *  α[I]ₗ                      := by congr; exact Partition.sum_of_α_length P α
  have lower_le_upper : 0 ≤ upper_RS_integral f I α- lower_RS_integral f I α := by
    linarith [lower_RS_integral_le_upper hfbound hα]
  obtain h | h := le_iff_lt_or_eq.mp lower_le_upper
  . have hαnonneg : 0 ≤ α[I]ₗ := by exact α_length_nonneg_of_monotone hα I
    rcases hαnonneg.eq_or_lt with hzero | hpos
    . have ⟨M, hM⟩ := hfbound
      have h1 := le_lower_RS_integral hM hα
      have h2 := RS_upper_integral_le hM hα
      have h3 := lower_RS_integral_le_upper hfbound hα
      rw [← hzero] at h1 h2
      simp at h1 h2
      linarith
    . simp_rw [mul_comm _ (α_length α I)] at this
      have hle0 := nonneg_of_le_const_mul_eps this
      apply le_antisymm (lower_RS_integral_le_upper hfbound hα)
      linarith
  . linarith

lemma left_lim_of_sign_pos {b:ℝ} (h : 0 < b) : left_lim Real.sign b = 1 := by
  unfold left_lim
  apply Filter.Tendsto.limUnder_eq
  have htt : Filter.Tendsto Real.sign (nhds b) (nhds 1) := by
    apply (tendsto_const_nhds (x:=(1:ℝ))).congr'
    filter_upwards [eventually_gt_nhds h] with x hx
    symm; exact Real.sign_of_pos hx
  apply htt.mono_left
  exact nhdsWithin_le_nhds

lemma right_lim_of_sign_neg {a:ℝ} (h : a < 0) : right_lim Real.sign a = -1 := by
  unfold right_lim
  apply Filter.Tendsto.limUnder_eq
  have htt : Filter.Tendsto Real.sign (nhds a) (nhds (-1)) := by
    apply (tendsto_const_nhds (x:=(-1:ℝ))).congr'
    filter_upwards [eventually_lt_nhds h] with x hx
    symm; exact Real.sign_of_neg hx
  apply htt.mono_left
  exact nhdsWithin_le_nhds

lemma right_lim_of_sign_nonneg {b:ℝ} (h : 0 ≤ b) : right_lim Real.sign b = 1 := by
  unfold right_lim
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp at hx
  symm; apply Real.sign_of_pos
  linarith

lemma left_lim_of_sign_nonpos {a:ℝ} (h : a ≤ 0) : left_lim Real.sign a = -1 := by
  unfold left_lim
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp at hx
  symm; apply Real.sign_of_neg
  linarith

lemma RS_integ_pc_sign {g : ℝ → ℝ} (hg : PiecewiseConstantOn g (Icc (-1) 1)) :
    PiecewiseConstantOn.RS_integ g (Icc (-1) 1) Real.sign = 2 * g 0 := by
  choose P hP using hg
  rw [PiecewiseConstantOn.RS_integ_def hP]
  simp only [PiecewiseConstantWith.RS_integ]
  have hzero {J : BoundedInterval} (hJ : J ∈ P.intervals) (h : 0 ∈ J) : constant_value_on g J * α_length Real.sign J = 2 * g 0 := by
    have hconst : constant_value_on g J = g 0 := by
      apply ConstantOn.const_eq
      . use 0; exact h
      . intro y hy
        specialize hP J hJ
        rw [hP.eq hy, hP.eq h]
    have hsign : α_length Real.sign J = 2 := by
      unfold α_length
      match J with
      | Ioo a b =>
        rw [BoundedInterval.mem_iff] at h
        simp at h ⊢
        rw [
          if_pos (by linarith),
          left_lim_of_sign_pos h.2,
          right_lim_of_sign_neg h.1
        ]
        norm_num
      | Icc a b =>
        rw [BoundedInterval.mem_iff] at h
        simp at h ⊢
        rw [
          if_pos (by linarith),
          right_lim_of_sign_nonneg h.2,
           left_lim_of_sign_nonpos h.1
        ]
        norm_num
      | Ico a b =>
        rw [BoundedInterval.mem_iff] at h
        simp at h ⊢
        rw [
          if_pos (by linarith),
          left_lim_of_sign_pos h.2,
          left_lim_of_sign_nonpos h.1,
        ]
        norm_num
      | Ioc a b =>
        rw [BoundedInterval.mem_iff] at h
        simp at h ⊢
        rw [
          if_pos (by linarith),
          right_lim_of_sign_nonneg h.2,
          right_lim_of_sign_neg h.1
        ]
        norm_num
    rw [hconst, hsign]; ring_nf
  have hzero' {J : BoundedInterval} (hJ : J ∈ P.intervals) (h : 0 ∉ J) : constant_value_on g J * α_length Real.sign J = 0 := by
    by_cases h' : Subsingleton (J : Set ℝ)
    . simp at h'
      rcases Set.Subsingleton.eq_empty_or_singleton h' with hempty | hsingle
      . simp [α_length_of_empty _ hempty]
      . choose c hc using hsingle
        have hIcc := BoundedInterval.singleton_Icc hc
        suffices α_length Real.sign J = 0 by rw [this]; linarith
        rw [hIcc]
        rcases lt_trichotomy c 0 with hneg | hzero | hpos
        . have := α_length_of_cts (I:=J) (a:=3*c/2) (b:=c/2) (α:=Real.sign)
            (haa:=by rw [hIcc]; simp [BoundedInterval.a]; linarith)
            (hbb:=by rw [hIcc]; simp [BoundedInterval.b]; linarith)
            (hab:=by rw [hIcc])
            (hI:=by rw [hIcc]; rw [BoundedInterval.subset_iff]; simp; constructor <;> linarith)
            (hα:=by
              simp; apply (continuousOn_const (c:=-1)).congr
              intro x hx; unfold Real.sign; simp at hx ⊢
              intro hx'; exfalso; linarith
            )
          rw [← hIcc, this, hIcc]; simp
        . rw [hIcc] at h; subst hzero
          rw [BoundedInterval.mem_iff] at h
          exfalso; simp at h
        . have := α_length_of_cts (I:=J) (a:=c/2) (b:=3*c/2) (α:=Real.sign)
            (haa:=by rw [hIcc]; simp [BoundedInterval.a]; linarith)
            (hbb:=by rw [hIcc]; simp [BoundedInterval.b]; linarith)
            (hab:=by rw [hIcc])
            (hI:=by rw [hIcc]; rw [BoundedInterval.subset_iff]; simp; constructor <;> linarith)
            (hα:=by
              simp; apply (continuousOn_const (c:=1)).congr
              intro x hx; unfold Real.sign; simp at hx ⊢
              rw [if_neg (by linarith), if_pos (by linarith)]
            )
          rw [← hIcc, this, hIcc]; simp
    simp [length_of_subsingleton, length, -Set.subsingleton_coe] at h'
    suffices α_length Real.sign J = 0 by rw [this]; simp
    match J with
    | Icc a b =>
      simp; intro hab; simp [BoundedInterval.a, BoundedInterval.b] at h'
      have hcase : 0 < a ∨ b < 0 := by
        by_contra hcon; push_neg at hcon; exact h ⟨hcon.1, hcon.2⟩
      rcases hcase with ha | hb
      . rw [right_lim_of_sign_nonneg (by linarith), left_lim_of_sign_pos ha]; norm_num
      . rw [right_lim_of_sign_neg hb, left_lim_of_sign_nonpos (by linarith)]; norm_num
    | Ico a b =>
      simp; intro hab; simp [BoundedInterval.a, BoundedInterval.b] at h'
      have hcase : 0 < a ∨ b ≤ 0 := by
        by_contra hcon; push_neg at hcon; exact h ⟨hcon.1, hcon.2⟩
      rcases hcase with ha | hb
      . rw [left_lim_of_sign_pos (by linarith), left_lim_of_sign_pos ha]; norm_num
      . rw [left_lim_of_sign_nonpos (by linarith), left_lim_of_sign_nonpos (by linarith)]; norm_num
    | Ioc a b =>
      simp; intro hab; simp [BoundedInterval.a, BoundedInterval.b] at h'
      have hcase : 0 ≤ a ∨ b < 0 := by
        by_contra hcon; push_neg at hcon; exact h ⟨hcon.1, hcon.2⟩
      rcases hcase with ha | hb
      . rw [right_lim_of_sign_nonneg (by linarith), right_lim_of_sign_nonneg ha]; norm_num
      . rw [right_lim_of_sign_neg (by linarith), right_lim_of_sign_neg (by linarith)]; norm_num
    | Ioo a b =>
      simp; intro hab; simp [BoundedInterval.a, BoundedInterval.b] at h'
      have hcase : 0 ≤ a ∨ b ≤ 0 := by
        by_contra hcon; push_neg at hcon; exact h ⟨hcon.1, hcon.2⟩
      rcases hcase with ha | hb
      . rw [left_lim_of_sign_pos (b:=b) (by linarith), right_lim_of_sign_nonneg (b:=a) (by linarith)]; norm_num
      . rw [left_lim_of_sign_nonpos (by linarith), right_lim_of_sign_neg (a:=a) (by linarith)]; norm_num
  obtain ⟨J₀, ⟨hJ₀mem, hJ₀⟩, hJ₀uniq⟩ := P.exists_unique (x:=0) (by rw [BoundedInterval.mem_iff]; simp)
  simp at hJ₀uniq
  rw [Finset.sum_eq_single_of_mem J₀ hJ₀mem ?_]
  . exact hzero hJ₀mem hJ₀
  . intro J' hJ' hJ₀'
    refine hzero' hJ' ?_
    contrapose! hJ₀'
    exact hJ₀uniq J' hJ' hJ₀'


/-- Exercise 11.8.5 -/
theorem RS_integ_with_sign (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc (-1) 1)) : RS_IntegrableOn f (Icc (-1) 1) Real.sign ∧ RS_integ f (Icc (-1) 1) Real.sign = 2 * f 0 := by
  have hpart : ∃ P : Partition (Icc (-1) 1), P.intervals = {Ico (-1) 0, Icc 0 0, Ioc 0 1} := by
    refine ⟨(⊥ : Partition (Ico (-1) 0)).join
            ((⊥ : Partition (Icc 0 0)).join (⊥ : Partition (Ioc 0 1))
               (BoundedInterval.join_Icc_Ioc (by norm_num) (by norm_num)))
            (BoundedInterval.join_Ico_Icc (by norm_num) (by norm_num)), ?_⟩
    simp only [Partition.intervals_of_bot]
    rfl
  have hbdd : BddOn f (Icc (-1) 1) := by
    exact BddOn.of_continuous_on_compact (by norm_num) hf
  have hmono : Monotone Real.sign := by
    intro x y hxy
    unfold Real.sign
    split_ifs; all_goals try grind
  have hlo : lower_RS_integral f (Icc (-1) 1) Real.sign = 2 * f 0 := by
    apply le_antisymm
    . apply csSup_le (RS_integral_bound_lower_nonempty hbdd hmono)
      intro b hb; simp at hb
      obtain ⟨g, ⟨hgminor, hgpwconst⟩, hgRSpwconst⟩ := hb
      have := RS_integ_pc_sign hgpwconst
      rw [← hgRSpwconst, this]; simp
      apply hgminor; simp
    . apply le_csSup (RS_integral_bound_above hbdd hmono); simp
      choose M hM using hbdd
      set g : ℝ → ℝ := fun x => if x = 0 then f 0 else (-M)
      have hgminor : MinorizesOn g f (Icc (-1) 1) := by
        intro x hx
        unfold g; split_ifs with h
        . subst h; rfl
        . specialize hM x hx
          rw [abs_le] at hM; tauto
      have hgpwconst : PiecewiseConstantOn g (Icc (-1) 1) := by
        choose P hP using hpart
        use P; intro J hJ
        change J ∈ P.intervals at hJ
        rw [hP] at hJ; simp at hJ
        rcases hJ with h | h | h
        . unfold g
          apply ConstantOn.of_const (c:=-M)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_neg (by linarith)]
        . unfold g
          apply ConstantOn.of_const (c:=f 0)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_pos (by linarith)]
        . unfold g
          apply ConstantOn.of_const (c:=-M)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_neg (by linarith)]
      use g; refine ⟨⟨?_, ?_⟩, ?_⟩
      . exact hgminor
      . exact hgpwconst
      . have := RS_integ_pc_sign hgpwconst
        rw [this]; simp
        unfold g; simp
  have hup : upper_RS_integral f (Icc (-1) 1) Real.sign = 2 * f 0 := by
    apply le_antisymm
    . apply csInf_le ( RS_integral_bound_below hbdd hmono); simp
      choose M hM using hbdd
      set g : ℝ → ℝ := fun x => if x = 0 then f 0 else (M)
      have hgmajor : MajorizesOn g f (Icc (-1) 1) := by
        intro x hx
        unfold g; split_ifs with h
        . subst h; rfl
        . specialize hM x hx
          rw [abs_le] at hM; tauto
      have hgpwconst : PiecewiseConstantOn g (Icc (-1) 1) := by
        choose P hP using hpart
        use P; intro J hJ
        change J ∈ P.intervals at hJ
        rw [hP] at hJ; simp at hJ
        rcases hJ with h | h | h
        . unfold g
          apply ConstantOn.of_const (c:=M)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_neg (by linarith)]
        . unfold g
          apply ConstantOn.of_const (c:=f 0)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_pos (by linarith)]
        . unfold g
          apply ConstantOn.of_const (c:=M)
          intro x hx
          rw [h] at hx; simp at hx
          rw [if_neg (by linarith)]
      use g; refine ⟨⟨?_, ?_⟩, ?_⟩
      . exact hgmajor
      . exact hgpwconst
      . have := RS_integ_pc_sign hgpwconst
        rw [this]; simp
        unfold g; simp
    . apply le_csInf (RS_integral_bound_upper_nonempty hbdd hmono)
      intro b hb; simp at hb
      obtain ⟨g, ⟨hgmajor, hgpwconst⟩, hgRSpwconst⟩ := hb
      have := RS_integ_pc_sign hgpwconst
      rw [← hgRSpwconst, this]; simp
      apply hgmajor; simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  . exact hbdd
  . linarith
  . unfold RS_integ; linarith


/-- Analogue of Lemma 11.3.7 -/
theorem RS_integ_of_piecewise_const {f:ℝ → ℝ} {I: BoundedInterval} (hf: PiecewiseConstantOn f I)
  {α: ℝ → ℝ} (hα: Monotone α):
  RS_IntegrableOn f I α ∧ RS_integ f I α = PiecewiseConstantOn.RS_integ f I α := by
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
  have h1 := upper_RS_integral_le_integ hbdd hminff hf hα
  have h2 := integ_le_lower_RS_integral hbdd hminff hf hα
  have h3 := lower_RS_integral_le_upper hbdd hα
  refine ⟨⟨hbdd, ?_⟩, ?_⟩
  . linarith
  . linarith

end Chapter11
