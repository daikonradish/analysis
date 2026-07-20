import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_3
import Analysis.Section_9_4

/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/

namespace Chapter9

/-- Definition 9.6.1 -/
abbrev BddAboveOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, f x ≤ M

abbrev BddBelowOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, -M ≤ f x

abbrev BddOn (f:ℝ → ℝ) (X:Set ℝ) : Prop := ∃ M, ∀ x ∈ X, |f x| ≤ M

/-- Remark 9.6.2 -/
theorem BddOn.iff (f:ℝ → ℝ) (X:Set ℝ) : BddOn f X ↔ BddAboveOn f X ∧ BddBelowOn f X := by
  constructor
  · intro hbddon
    choose M hM using hbddon
    constructor <;>
    · use M; intro x hx
      specialize hM x hx
      grind
  · rintro ⟨habove, hbelow⟩
    choose M hM using habove
    choose L hL using hbelow
    use max |M| |L|
    intro x hx
    specialize hM x hx
    specialize hL x hx
    grind

theorem BddOn.iff' (f:ℝ → ℝ) (X:Set ℝ) :  BddOn f X ↔ Bornology.IsBounded (f '' X) := by
  rw [isBounded_def]
  constructor
  · intro hbddon
    choose M hM using hbddon
    by_cases! hMpozneg : M ≤ 0
    · use 1; constructor
      · simp
      · simp; grind
    · use M; constructor
      · exact hMpozneg
      · simp; grind
  · intro hborn
    choose M hMpos hM using hborn
    simp at hM
    use M; intro x hx
    have := hM hx
    simp at this
    grind

theorem BddOn.of_bounded {f :ℝ → ℝ} {X: Set ℝ} {M:ℝ} (h: ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

lemma BddOn.mono {f : ℝ → ℝ} {I J : Set ℝ} (hbd : BddOn f J) (h : I ⊆ J) : BddOn f I := by
  choose B hB using hbd
  use B
  intro x hx
  exact hB x (by apply h; exact hx)

lemma BddBelow.of_BddOn {f : ℝ → ℝ} {I:Set ℝ} (h : BddOn f I) : BddBelow (f '' I) := by
  obtain ⟨_, hbelow⟩ := (BddOn.iff _ _).mp h
  choose B hB using hbelow; use -B
  intro y hy; simp at hy; choose x hx hxeq using hy
  specialize hB x hx; linarith

lemma BddAbove.of_BddOn {f : ℝ → ℝ} {I:Set ℝ} (h : BddOn f I) : BddAbove (f '' I) := by
  obtain ⟨habove, _⟩ := (BddOn.iff _ _).mp h
  choose B hB using habove; use B
  intro y hy; simp at hy; choose x hx hxeq using hy
  specialize hB x hx; linarith

lemma BddOn.of_smul {c : ℝ} {f : ℝ → ℝ} {I:Set ℝ} (h : BddOn f I) : BddOn (c • f) I := by
  choose B hB using h
  use |c| * B
  intro x hx
  specialize hB x hx
  simp at hB ⊢
  gcongr


example : Continuous (fun x:ℝ ↦ x) := by
  exact continuous_id

example : ¬ BddOn (fun x:ℝ ↦ x) .univ  := by
  intro h
  choose M hM using h
  specialize hM (M+1)
  simp at hM
  grind

example : BddOn (fun x:ℝ ↦ x) (.Icc 1 2) := by
  use 100
  simp
  intro x hx1 hx2
  grind

example : ContinuousOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  apply ContinuousOn.div
  · exact continuousOn_const
  · exact continuousOn_id
  · simp; intro x hx0 hx1; linarith

example : ¬ BddOn (fun x:ℝ ↦ 1/x) (.Ioo 0 1) := by
  intro hb
  choose M hM using hb
  have hpos : ∀ x ∈ Set.Ioo 0 1, |(fun x ↦ 1 / (x:ℝ)) x| > 0 := by
      intro x hx
      simp at hx ⊢
      grind
  by_cases! hMpozneg : M ≤ 0
  · specialize hM 0.5 (by norm_num)
    specialize hpos 0.5 (by norm_num)
    linarith
  · have : (1 / (M + 1)) ∈ Set.Ioo 0 1 := by
      simp; constructor
      · linarith
      · field_simp
        linarith
    specialize hM (1 / (M + 1)) this
    simp at hM
    grind


theorem why_7_6_3 {n: ℕ → ℕ} (hn: StrictMono n) (j:ℕ) : n j ≥ j := by
  exact StrictMono.le_apply hn -- proven elsewhere, so i don't wanna do this again; it's just induction.

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (_h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b) ) :
  BddOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound; simp at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n:ℕ): x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

/- Definition 9.6.5.  Use the Mathlib `IsMaxOn` type. -/
#check isMaxOn_iff
#check isMinOn_iff

/-- Remark 9.6.6 -/
theorem BddAboveOn.isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMaxOn f X x₀): BddAboveOn f X := by
  rw [isMaxOn_iff] at h
  use f x₀

theorem BddBelowOn.isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (h: IsMinOn f X x₀): BddBelowOn f X := by
  rw [isMinOn_iff] at h
  use -f x₀
  simp; exact h

/-- Proposition 9.6.7 (Maximum principle) -/
theorem IsMaxOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  -- This proof is written to follow the structure of the original text.
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sSup E
  have claim1 {y:ℝ} (hy: y ∈ E) : y ≤ m := le_csSup (BddAbove.mono hE bddAbove_Icc) hy
  suffices h : ∃ xmax, xmax ∈ Set.Icc a b ∧ f xmax = m
  . simp_rw [isMaxOn_iff]
    choose xmax hmem hmax using h
    use xmax; refine ⟨hmem, ?_⟩
    intro x hx
    rw [hmax]
    unfold m E
    apply le_csSup
    · use M
      intro y hy; simp at hy
      choose x' habx' hfx' using hy
      specialize hM x' (by grind)
      rw [← hfx']
      grind
    · simp; use x; grind
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, m - 1/(n+1:ℝ) < f x := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : m - 1/(n+1:ℝ) < sSup E := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_lt_csSup hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : m - 1/(n+1:ℝ) < f (x n) := (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmax, hmax, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmax, hmax
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmax)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmax) (fun j ↦ hx (n j))
  have hlower (j:ℕ) : m - 1/(j+1:ℝ) < f (x (n j)) := by
    apply lt_of_le_of_lt _ (hfx (n j)); gcongr; grind
  have hupper (j:ℕ) : f (x (n j)) ≤ m := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (g := fun j ↦ m - 1/(j+1:ℝ)) (h := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub m (c:=0); simp
    . exact tendsto_const_nhds
    . intro _; grind
    exact hupper
  exact tendsto_nhds_unique hconv' hconvm





theorem IsMinOn.of_continuous_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) :
  ∃ xmin ∈ Set.Icc a b, IsMinOn f (.Icc a b) xmin := by
  choose M hM using BddOn.of_continuous_on_compact h hf
  set E := f '' (.Icc a b)
  have hE : E ⊆ .Icc (-M) M := by rintro _ ⟨ x, hx, rfl ⟩; simp [hM x hx, ←abs_le]
  have hnon : E ≠ ∅ := by simp [E]; contrapose! h; grind [Set.Icc_eq_empty_iff]
  set m := sInf E
  have claim1 {y:ℝ} (hy: y ∈ E) : m ≤ y := csInf_le (BddBelow.mono hE bddBelow_Icc) hy
  suffices h : ∃ xmin, xmin ∈ Set.Icc a b ∧ f xmin = m
  . simp_rw [isMinOn_iff]
    choose xmin hmem hmin using h
    use xmin; refine ⟨hmem, ?_⟩
    intro x hx
    rw [hmin]
    unfold m E
    apply csInf_le
    · use -M
      intro y hy; simp at hy
      choose x' habx' hfx' using hy
      specialize hM x' (by grind)
      rw [← hfx']
      grind
    · simp; use x; grind
  have claim2 (n:ℕ) : ∃ x ∈ Set.Icc a b, f x < m + 1/(n+1:ℝ) := by
    have : 1/(n+1:ℝ) > 0 := by positivity
    replace : sInf E < m + 1/(n+1:ℝ)  := by linarith
    rw [←Set.nonempty_iff_ne_empty] at hnon
    apply exists_lt_of_csInf_lt hnon at this
    grind
  set x : ℕ → ℝ := fun n ↦ (claim2 n).choose
  have hx (n:ℕ) : x n ∈ Set.Icc a b := (claim2 n).choose_spec.1
  have hfx (n:ℕ) : f (x n) < m + 1/(n+1:ℝ):= (claim2 n).choose_spec.2
  observe hclosed : IsClosed (.Icc a b)
  observe hbounded : Bornology.IsBounded (.Icc a b)
  have ⟨ n, hn, ⟨ xmin, hmin, hconv⟩ ⟩ := (Heine_Borel (.Icc a b)).mp ⟨hclosed, hbounded⟩ x hx
  use xmin, hmin
  have hn_lower (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  have hconv' : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds (f xmin)) :=
    hconv.comp_of_continuous (hf.continuousWithinAt hmin) (fun j ↦ hx (n j))
  have hupper (j:ℕ) : f (x (n j)) < m + 1/(j+1:ℝ) := by
    apply lt_of_lt_of_le (hfx (n j)); gcongr; grind
  have hlower (j:ℕ) : m ≤ f (x (n j))  := by apply claim1; simp [Set.mem_image, E]; use x (n j), hx (n j)
  have hconvm : Filter.atTop.Tendsto (fun j ↦ f (x (n j))) (nhds m) := by
    apply Filter.Tendsto.squeeze (h := fun j ↦ m + 1/(j+1:ℝ)) (g := fun _ ↦ m) (f := fun j ↦ f (x (n j)))
    · simp
    · convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add m (a:=0); simp
    · intro x; simp; grind
    · intro x; simp; grind
  exact tendsto_nhds_unique hconv' hconvm

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) 2 := by
  rw [isMaxOn_iff]
  simp
  intro x hx' hx
  nlinarith

example : IsMaxOn (fun x ↦ x^2) (.Icc (-2) 2) (-2) := by
  rw [isMaxOn_iff]
  simp
  intro x hx' hx
  nlinarith


theorem sSup.of_isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMaxOn f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMinOn f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

/-- Exercise 9.6.1 a) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ioo 1 2) ∧ BddOn f (.Ioo 1 2) ∧
  ∃ x₀ ∈ Set.Ioo 1 2, IsMinOn f (.Ioo 1 2) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ioo 1 2, IsMaxOn f (.Ioo 1 2) x₀
  := by
  use fun x => |x - 1.5|
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousOn.abs
    apply ContinuousOn.sub
    · exact continuousOn_id
    · exact continuousOn_const
  · use 100; intro x hx
    simp at hx ⊢; rw [abs_le]
    constructor <;> linarith
  · use 1.5; constructor
    · simp; constructor <;> norm_num
    · constructor
      · rw [isMinOn_iff]
        intro x hx; simp at hx ⊢
      · simp_rw [isMaxOn_iff]; push_neg
        intro x hx; simp at hx ⊢
        by_cases hmidpt : x ≤ 1.5
        · use (x+1) / 2; constructor <;> grind
        · use (x+2) / 2; constructor <;> grind


/-- Exercise 9.6.1 b) -/
example : ∃ f: ℝ → ℝ, ContinuousOn f (.Ici 0) ∧ BddOn f (.Ici 0) ∧
  ∃ x₀ ∈ Set.Ici 0, IsMaxOn f (.Ici 0) x₀ ∧
  ¬ ∃ x₀ ∈ Set.Ici 0, IsMinOn f (.Ici 0) x₀
  := by
  use fun x => 1 / (x+1)
  refine ⟨?_, ?_, ?_⟩
  · apply ContinuousOn.div
    · exact continuousOn_const
    · apply ContinuousOn.add
      · exact continuousOn_id
      · exact continuousOn_const
    · intro x hx; simp at hx ⊢; linarith
  · use 100; intro x hx; simp at hx ⊢
    field_simp
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  · use 0; simp; constructor
    · intro x hx; simp at hx ⊢
      field_simp; linarith
    · intro x hx; rw [isMinOn_iff]; push_neg
      use (x + 100); simp; constructor
      · linarith
      · field_simp; linarith

/-- Exercise 9.6.1 c) -/
example : ∃ f: ℝ → ℝ, BddOn f (.Icc (-1) 1) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMinOn f (.Icc (-1) 1) x₀) ∧
  (¬ ∃ x₀ ∈ Set.Icc (-1) 1, IsMaxOn f (.Icc (-1) 1) x₀)
  := by
  use fun x => if x = 1 ∨ x = -1 then 0 else x
  refine ⟨?_, ?_, ?_⟩
  · use 100; intro x hx; simp at hx ⊢
    split_ifs with h
    · simp
    · push_neg at h; rw [abs_le];
      constructor <;> linarith
  · simp_rw [isMinOn_iff]; push_neg
    intro x hx
    by_cases h1 : (x = 1 ∨ x = -1)
    · use -0.5; simp; constructor
      · constructor <;> linarith
      · rw [if_neg, if_pos]
        · norm_num
        · exact h1
        · simp; constructor <;> linarith
    · set δ := (x + 1) / 2
      use x - δ; simp at hx ⊢; constructor
      · unfold δ; simp; constructor
        · linarith
        · field_simp; grind
      · rw [if_neg, if_neg]
        · unfold δ; field_simp; ring_nf; grind
        · exact h1
        · unfold δ; simp; constructor
          · linarith
          · grind
  · simp_rw [isMaxOn_iff]; push_neg
    intro x hx
    by_cases h1 : (x = 1 ∨ x = -1)
    · use 0.5; simp; constructor
      · constructor <;> linarith
      · rw [if_pos, if_neg]
        · norm_num
        · simp; constructor <;> linarith
        · exact h1
    · set δ := (1 - x) / 2
      use x + δ; simp at hx ⊢; constructor
      · unfold δ; constructor <;> linarith
      · rw [if_neg, if_neg]
        · unfold δ; field_simp; ring_nf; grind
        · unfold δ; simp; constructor
          · grind
          · linarith
        · exact h1


/-- Exercise 9.6.1 d) -/
example : ∃ f: ℝ → ℝ, ¬ BddAboveOn f (.Icc (-1) 1) ∧ ¬ BddBelowOn f (.Icc (-1) 1) := by
  use fun x => (1/x); constructor
  · unfold BddAboveOn; push_neg; intro M
    by_contra! h
    by_cases! hM : M < 1
    · specialize h 1 (by grind); simp at h
      linarith
    · have hM2 : (1 / (2*M)) ≤ (1/2) := by field_simp; exact hM
      have hM0 : 0 <  (1 / (2*M)) := by positivity
      specialize h ((1 / (2*M))) (by grind)
      field_simp at h
      linarith
  · unfold BddBelowOn; push_neg; intro M
    by_contra! h
    by_cases! hM : M < 1
    · specialize h (-1) (by grind); simp at h
      linarith
    · have hM2 : (-1/2) ≤ (-1 / (2*M)) := by field_simp; grind
      have hM0 : 0 <  (1 / (2*M)) := by positivity
      specialize h (-(1 / (2*M))) (by grind)
      field_simp at h
      linarith

/-- Exercise 9.6.2 -/
theorem BddOn.add (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f + g) X := by
    choose M hM using hf
    choose L hL using hg
    use M + L
    intro x hx
    specialize hM x hx
    specialize hL x hx
    simp; grind

theorem BddOn.sub (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f - g) X := by
    choose M hM using hf
    choose L hL using hg
    use M + L
    intro x hx
    specialize hM x hx
    specialize hL x hx
    simp; grind

theorem BddOn.mul (f g : ℝ → ℝ) (X : Set ℝ) (hf : BddOn f X) (hg : BddOn g X) :
    BddOn (f * g) X := by
    choose M hM using hf
    choose L hL using hg
    by_cases! hpos : M ≤ 0 ∨ L ≤ 0
    · use 0
      rcases hpos with hM0 | hL0
      · have : ∀ x, x ∈ X → f x = 0 := by
          intro x hx
          specialize hM x hx
          grind
        intro x hx; simp
        specialize this x hx
        rw [this]; simp
      · have : ∀ x, x ∈ X → g x = 0 := by
          intro x hx
          specialize hM x hx
          grind
        intro x hx; simp
        specialize this x hx
        rw [this]; simp
    · use M * L
      intro x hx
      specialize hM x hx
      specialize hL x hx
      simp; gcongr
      linarith

def BddOn.div : Decidable (∀ (f g : ℝ → ℝ) (X : Set ℝ) (_ : ∀ x ∈ X, g x ≠ 0) (_ : BddOn f X)
    (_: BddOn g X), (BddOn (f / g) X)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`, depending on whether you believe the given statement to be true or false.
  apply isFalse
  push_neg
  use fun _ => 1
  use fun x => x
  use Set.Ioo 0 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; simp at hx ⊢; linarith
  · use 100; intro x hx; simp at hx ⊢
  · use 100; intro x hx; simp at hx ⊢; grind
  · intro M
    simp [-one_div]
    by_cases! hM0 : M ≤ 0
    · use 0.5; constructor
      · norm_num
      · have : 0 < |1 / (0.5:ℝ)| := by norm_num
        linarith
    · by_cases! hM1 : M ≤ 1
      · use 0.5; constructor
        · norm_num
        · norm_num; linarith
      · have hM2 : (1 / (2*M)) ≤ (1/2) := by field_simp; linarith
        have hM0 : 0 <  (1 / (2*M)) := by positivity
        use ((1 / (2*M))); constructor
        · grind
        · rw [abs_of_pos (by positivity)]
          field_simp; linarith




end Chapter9
