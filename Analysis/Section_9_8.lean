import Mathlib.Tactic
import Analysis.Section_9_6
import Analysis.Section_9_7

/-!
# Analysis I, Section 9.8: Monotonic functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Review of Mathlib monotonicity concepts.
-/

namespace Chapter9

/-- Definition 9.8.1 -/
theorem MonotoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : MonotoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≥ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictMono.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictMonoOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y > f x := by
  constructor <;> intros <;> solve_by_elim

theorem AntitoneOn.iff {X: Set ℝ} (f: ℝ → ℝ) : AntitoneOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y ≤ f x := by
  constructor
  . intros; solve_by_elim [le_of_lt]
  intro _ _ _ _ _ hxy; obtain hxy | rfl := le_iff_lt_or_eq.mp hxy
  . solve_by_elim
  simp

theorem StrictAntitone.iff {X: Set ℝ} (f: ℝ → ℝ) : StrictAntiOn f X  ↔ ∀ x ∈ X, ∀ y ∈ X, y > x → f y < f x := by
  constructor <;> intros <;> solve_by_elim

/-- Examples 9.8.2 -/
example : StrictMonoOn (fun x:ℝ ↦ x^2) (.Ici 0) := by
  intro x hx y hy hxy
  simp at hx hy ⊢; nlinarith

example : StrictAntiOn (fun x:ℝ ↦ x^2) (.Iic 0) := by
  intro x hx y hy hxy
  simp at hx hy ⊢; nlinarith

example : ¬ MonotoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro hmono
  specialize hmono
  rw [MonotoneOn.iff] at hmono
  specialize hmono (-5) (by tauto) 1 (by tauto) (by linarith)
  norm_num at hmono

example : ¬ AntitoneOn (fun x:ℝ ↦ x^2) .univ := by
  intro hanti
  specialize hanti
  rw [AntitoneOn.iff] at hanti
  specialize hanti (-1) (by tauto) 5 (by tauto) (by linarith)
  norm_num at hanti


example {X:Set ℝ} {f:ℝ → ℝ} (hf: StrictMonoOn f X) : MonotoneOn f X := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with heq | hlt
  · rw [heq]
  · specialize hf hx hy (by linarith)
    linarith

example (X:Set ℝ) : MonotoneOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro x hx y hy hxy
  simp

example (X:Set ℝ) : AntitoneOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro x hx y hy hxy
  simp

#check nontrivial_iff

example {X:Set ℝ} (hX: Nontrivial X) : ¬ StrictMonoOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro hmono; rw [StrictMono.iff] at hmono
  rw [nontrivial_iff] at hX
  choose x y hxy using hX
  rcases hxy.lt_or_gt with hlt | hgt <;> grind

example (X:Set ℝ) (hX: Nontrivial X) : ¬ StrictAntiOn (fun x:ℝ ↦ (6:ℝ)) X := by
  intro hanti; rw [StrictAntitone.iff] at hanti
  rw [nontrivial_iff] at hX
  choose x y hxy using hX
  rcases hxy.lt_or_gt with hlt | hgt <;> grind

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), ContinuousOn f X ∧ ¬ MonotoneOn f X ∧ ¬ AntitoneOn f X := by
  use .univ
  use fun x => x ^ 2
  refine ⟨?_, ?_, ?_⟩
  . apply ContinuousOn.pow
    exact continuousOn_id
  . rw [MonotoneOn.iff]
    push_neg
    use -5, by tauto
    use 1, by tauto
    norm_num
  . rw [AntitoneOn.iff]
    push_neg
    use -1, by tauto
    use 5, by tauto
    norm_num

example : ∃ (X:Set ℝ) (f:ℝ → ℝ), MonotoneOn f X ∧ ¬ ContinuousOn f X := by
  use .univ
  use fun x => if x < 0 then -1 else 1
  constructor
  . rw [MonotoneOn.iff]
    intro x hx y hy hxy
    split_ifs with h1 h2 h3
    . rfl
    . exfalso; linarith
    . linarith
    . rfl
  . suffices (¬ ContinuousAt (fun (x:ℝ) => if x < 0 then -1 else (1:ℝ)) 0) by
      intro h; simp at h
      have h0 : ContinuousAt (fun (x:ℝ) ↦ if x < 0 then -1 else (1:ℝ)) 0 := by
        apply h.continuousAt
      contradiction
    intro hcont
    have htt := hcont.tendsto
    have hleft := htt.mono_left (h:=nhdsWithin_le_nhds (s := Set.Iio 0))
    have heq : (if (0:ℝ) < 0 then (-1:ℝ) else 1) = 1 := by
      rw [if_neg (by grind)]
    simp_rw [heq] at hleft
    have hleft' : Filter.Tendsto (fun (x:ℝ) => if x < 0 then -1 else (1:ℝ)) (nhdsWithin 0 (Set.Iio 0)) (nhds (-1)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin]
      intro a ha
      simp at ha
      rw [if_pos (by linarith)]
    have := tendsto_nhds_unique hleft hleft'
    linarith

/-- Proposition 9.8.3 / Exercise 9.8.4 -/
theorem MonotoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictMonoOn f (.Icc a b)) :
  f '' (.Icc a b) = .Icc (f a) (f b) ∧
  ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
  finv '' (.Icc (f a) (f b)) = .Icc a b ∧
  (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
  ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y
   := by
  have hendpoints : f a < f b := by exact hmono (by simp; linarith) (by simp; linarith) h
  have hrange : ∀ x ∈ Set.Icc a b, f x ∈ Set.Icc (f a) (f b) := by
    intro x hx
    simp at hx ⊢
    obtain ⟨hl, hr⟩ := hx
    constructor
    . apply hmono.monotoneOn <;> grind
    . apply hmono.monotoneOn <;> grind
  constructor
  . ext x; constructor
    . intro hm
      choose z hz using hm
      specialize hrange z hz.1
      rwa [← hz.2]
    . intro hm
      choose c hc using intermediate_value h hcont (y:=x) (by left; exact hm)
      use c
  . have hmapsto : Set.MapsTo f (Set.Icc a b) (Set.Icc (f a) (f b)) := by exact hrange
    have hinjon : Set.InjOn f (Set.Icc a b) := by apply hmono.injOn
    have hsurjon : Set.SurjOn f (Set.Icc a b) (Set.Icc (f a) (f b)) := by
      intro x hx
      choose c hc using intermediate_value h hcont (y:=x) (by left; exact hx)
      use c
    have hbijon : Set.BijOn f (.Icc a b) (.Icc (f a) (f b)) := by
      exact Set.BijOn.mk hrange hinjon hsurjon
    set e := (hbijon.equiv f)
    set finv : ℝ → ℝ := fun y => if hmem : y ∈ Set.Icc (f a) (f b) then e.symm ⟨y, hmem⟩ else 0
    use finv
    have hfinvmono : StrictMonoOn finv (Set.Icc (f a) (f b)) := by
      intro y hy z hz hyz
      unfold finv
      rw [dif_pos hy, dif_pos hz]
      have hemono : StrictMonoOn e (Set.Icc ⟨a, by simp; linarith⟩ ⟨b, by simp; linarith⟩) := by
        intro x hx y hy hxy; simp at hx
        have := hmono hx hy hxy; simp at this
        exact this
      rw [Subtype.coe_lt_coe, ← hemono.lt_iff_lt]
      . simp; exact hyz
      . exact (e.symm ⟨y, hy⟩).property
      . exact (e.symm ⟨z, hz⟩).property
    refine ⟨?_, ?_, ?_, ?_⟩
    . have hcoe : ∀ z : Set.Icc a b, (f z : ℝ) = ((e z):ℝ) := by intro z; rfl
      have hmem : ∀ y ∈ Set.Icc (f a) (f b), finv y ∈ Set.Icc a b := by
        intro y hy
        simp only [finv, dif_pos hy]
        exact (e.symm ⟨y, hy⟩).2
      have hffinv : ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y := by
        intro y hy
        simp only [finv, dif_pos hy]
        calc _ = ((e (e.symm ⟨y, hy⟩)):ℝ)         := by apply hcoe
             _ = (⟨y, hy⟩ : Set.Icc (f a) (f b))  := by simp
             _ = y                                := by rfl
      have hfinvf : ∀ x ∈ Set.Icc a b, finv (f x) = x := by
        intro x hx
        have hfx : f x ∈ Set.Icc (f a) (f b) := hrange x hx
        simp only [finv, dif_pos hfx]
        have key : e.symm ⟨f x, hfx⟩ = ⟨x, hx⟩ := by
          apply e.symm_apply_eq.mpr
          apply Subtype.ext
          exact hcoe ⟨x, hx⟩
        rw [key]
      simp_rw [Metric.continuousOn_iff, Real.dist_eq]
      intro y₀ hy₀ ε hε
      set x₀ := finv y₀
      have hx₀ : x₀ ∈ Set.Icc a b := by exact hmem y₀ hy₀
      have hfx₀ : f x₀ = y₀ := by unfold x₀; apply hffinv; exact hy₀
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :
        ∃ δ₁ > 0, ∀ y ∈ Set.Icc (f a) (f b), y < y₀ + δ₁ → finv y < x₀ + ε := by
        by_cases! hb : x₀ + ε ≤ b
        . have ht : x₀ + ε ∈ Set.Icc a b := by exact ⟨by linarith [hx₀.1], hb⟩
          use f (x₀ + ε) - y₀; constructor
          . have := hmono hx₀ ht (by linarith)
            rw [← hfx₀]
            linarith
          . intro y hy hylt
            simp at hylt
            have key : finv y < finv (f (x₀ + ε)):= by
              apply hfinvmono
              . exact hy
              . apply hrange; exact ht
              . exact hylt
            rwa [hfinvf _ ht] at key
        . use 1; constructor
          . linarith
          . intro y hy hy'
            have := hmem y hy
            simp at this
            linarith
      obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :
        ∃ δ₂ > 0, ∀ y ∈ Set.Icc (f a) (f b), y₀ - δ₂ < y → x₀ - ε < finv y := by
        by_cases ha : a ≤ x₀ - ε
        . have hs : x₀ - ε ∈ Set.Icc a b := ⟨ha, by linarith [hx₀.2]⟩
          use y₀ - f (x₀ - ε); constructor
          . have := hmono hs hx₀ (by linarith)
            linarith
          . intro y hy hygt
            simp at hygt
            have key : finv (f (x₀ - ε)) < finv y := by
              apply hfinvmono
              . apply hrange; exact hs
              . exact hy
              . exact hygt
            rwa [hfinvf _ hs] at key
        . use 1; constructor
          . linarith
          . intro y hy hy'
            have := hmem y hy
            simp at this
            linarith
      use min δ₁ δ₂; constructor
      . positivity
      . intro c hc hcmin
        rw [abs_lt]; constructor
        . specialize hδ₂ c hc (by grind)
          linarith
        . specialize hδ₁ c hc (by grind)
          linarith
    . exact hfinvmono
    . ext x; constructor
      . intro hx
        choose z hzmem hzinv using hx
        unfold finv at hzinv
        rw [dif_pos hzmem] at hzinv
        have h := (e.symm ⟨z, hzmem⟩).2
        rwa [hzinv] at h
      . intro hx
        use f x; constructor
        . exact hrange x hx
        . unfold finv
          rw [dif_pos (hrange x hx)]
          have : (⟨f x, hrange x hx⟩ : (Set.Icc (f a) (f b))) = e ⟨x, hx⟩ := by
           apply Subtype.ext
           rfl
          rw [this]; simp
    . constructor
      . intro x hx
        unfold finv
        have hmem := hrange x hx
        rw [dif_pos hmem]
        have : (⟨f x, hmem⟩ : (Set.Icc (f a) (f b))) = e ⟨x, hx⟩ := by
           apply Subtype.ext
           rfl
        rw [this]; simp
      . intro y hy
        unfold finv
        rw [dif_pos hy]
        rw [show f (e.symm ⟨y, hy⟩).val = (e (e.symm ⟨y, hy⟩)).val from rfl]
        simp


/-- Example 9.8.4 -/
example {R :ℝ} (hR: R > 0) {n:ℕ} (hn: n > 0) : ∃ g : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (R^n), (g x)^n = x := by
  set f : ℝ → ℝ := fun x ↦ x^n
  have hcont : ContinuousOn f (.Icc 0 R) := by fun_prop
  have hmono : StrictMonoOn f (.Icc 0 R) := by
    intro _ hx _ _ hxy; simp_all [f]
    apply pow_lt_pow_left₀ hxy <;> grind
  obtain ⟨ g, ⟨ _, _, _, _, hg⟩ ⟩ := (MonotoneOn.exist_inverse (by positivity) f hcont hmono).2
  simp only [f, zero_pow (by positivity)] at hg; use g

/-- Exercise 9.8.1 -/
theorem IsMaxOn.of_monotone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use b; simp; constructor
  . linarith
  . intro x hx
    apply hf
    . exact hx
    . simp; linarith
    . simp at hx ⊢; linarith

theorem IsMaxOn.of_strictmono_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictMonoOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use b; simp; constructor
  . linarith
  . intro x hx
    apply hf.monotoneOn
    . exact hx
    . simp; linarith
    . simp at hx ⊢; linarith

theorem IsMaxOn.of_antitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use a; simp; constructor
  . linarith
  . intro x hx
    apply hf
    . simp; linarith
    . simp at hx ⊢; exact hx
    . simp at hx ⊢; linarith

theorem IsMaxOn.of_strictantitone_on_compact {a b:ℝ} (h:a < b) {f:ℝ → ℝ} (hf: StrictAntiOn f (.Icc a b)) :
  ∃ xmax ∈ Set.Icc a b, IsMaxOn f (.Icc a b) xmax := by
  use a; simp; constructor
  . linarith
  . intro x hx
    apply hf.antitoneOn
    . simp; linarith
    . simp at hx ⊢; exact hx
    . simp at hx ⊢; linarith

theorem BddOn.of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  use max |f a| |f b|
  intro x hx
  simp at hx; obtain ⟨ha, hb⟩ := hx
  have ha' := hf (by simp; linarith) (by tauto) ha
  have hb' := hf (by tauto) (by simp; linarith) hb
  grind

theorem BddOn.of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (.Icc a b)) :
  BddOn f (.Icc a b) := by
  use max |f a| |f b|
  intro x hx
  simp at hx; obtain ⟨ha, hb⟩ := hx
  have ha' := hf (by simp; linarith) (by tauto) ha
  have hb' := hf (by tauto) (by simp; linarith) hb
  grind


/-- Exercise 9.8.2 -/
theorem no_strictmono_intermediate_value :
    ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: StrictMonoOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  use -1, 1
  use by linarith
  use fun x => if x < 0 then x - 1 else x + 1
  use by
    intro x hx y hy hxy
    simp
    split_ifs with h1 h2 h3 <;> linarith
  use 0
  use by
    left
    simp
    rw [if_neg (by linarith)]
    simp
  use by
    push_neg
    intro c hc
    split_ifs with h <;> linarith


theorem no_monotone_intermediate_value :
    ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: MonotoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  use -1, 1
  use by linarith
  use fun x => if x < 0 then x - 1 else x + 1
  use by
    intro x hx y hy hxy
    simp
    split_ifs with h1 h2 h3 <;> linarith
  use 0
  use by
    left
    simp
    rw [if_neg (by linarith)]
    simp
  use by
    push_neg
    intro c hc
    split_ifs with h <;> linarith

theorem no_strictanti_intermediate_value :
    ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: StrictAntiOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  use -1, 1
  use by linarith
  use fun x => if x < 0 then -x + 1 else -x - 1
  use by
    intro x hx y hy hxy
    simp
    split_ifs with h1 h2 h3 <;> linarith
  use 0
  use by
    right
    simp
    rw [if_neg (by linarith)]
    simp
  use by
    push_neg
    intro c hc
    split_ifs with h <;> linarith


theorem no_antitone_intermediate_value :
    ∃ (a b:ℝ) (hab: a < b) (f:ℝ → ℝ) (hf: AntitoneOn f (.Icc a b)),
      ∃ y, (y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) ∧
      ¬ ∃ c ∈ Set.Icc a b, f c = y := by
  use -1, 1
  use by linarith
  use fun x => if x < 0 then -x + 1 else -x - 1
  use by
    intro x hx y hy hxy
    simp
    split_ifs with h1 h2 h3 <;> linarith
  use 0
  use by
    right
    simp
    rw [if_neg (by linarith)]
    simp
  use by
    push_neg
    intro c hc
    split_ifs with h <;> linarith


lemma strictMono_of_continuous_inj {a b:ℝ} (h: a < b) {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x )) (hlt : f a < f b) :
  StrictMonoOn f (.Icc a b) := by
  have hamem : a ∈ Set.Icc a b := by simp; linarith
  have hbmem : b ∈ Set.Icc a b := by simp; linarith
  have hinjrestrict {x y: ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (hf : f x = f y) :
    x = y := by
    have hf' : f (⟨x, hx⟩ : Set.Icc a b) = f (⟨y, hy⟩ : Set.Icc a b) := by
      simpa using hf
    simpa using hinj hf'
  -- at this point, we know that a < b, so by injectivity, f (a) ≠ f (b).
  have hfaneqfb : f a ≠ f b := by
    intro heq
    have hab := hinjrestrict hamem hbmem heq
    exact absurd hab (by linarith)
  by_contra! hmono
  unfold StrictMonoOn at hmono; push_neg at hmono
  choose x hxmem y hymem hxy hfxfy using hmono
  by_cases! hfyltfa : f y < f a
  . have hyltb : y < b := by
      suffices y ≠ b by simp at hymem; grind
      intro hyeqb
      rw [hyeqb] at hfyltfa
      linarith
    choose c hcmem hceq
      using intermediate_value (a:=y) (b:=b) (f:=f)
        (hab:=hyltb)                                -- look inside (y, b)
        (hf:=hf.mono (t:=Set.Icc y b) (by grind))   -- [y, b] is wholly inside [a, b], so f is still continuous here
        (y:=f a)
        (hy:=by left; simp; exact ⟨by linarith, by linarith⟩)
    have hceqa : c = a := by
      apply hinjrestrict
      . simp at hcmem hymem ⊢; exact ⟨by linarith, hcmem.2⟩
      . simp; linarith
      . exact hceq
    simp at hcmem hymem hxmem
    linarith
  . have hfyltfx : f y < f x := by
      suffices f y ≠ f x by grind
      intro h'
      have hyx := hinjrestrict hymem hxmem h'
      exact absurd hyx (by linarith)
    have hfaltfx : f a < f x := by linarith
    have haltx : a < x := by
      suffices a ≠ x by grind
      intro h'
      have := congrArg f h'
      linarith
    choose c hcmem hceq
      using intermediate_value (a:=a) (b:=x) (f:=f)
        (hab:=haltx)
        (hf:=hf.mono (t:=Set.Icc a x) (by grind))
        (y:=f y)
        (hy:=by left; simp; exact ⟨by linarith, by linarith⟩)
    have hceqa : c = y := by
      apply hinjrestrict
      . simp at hcmem hymem ⊢; exact ⟨by linarith, by linarith⟩
      . exact hymem
      . exact hceq
    simp at hcmem hymem hxmem
    linarith

/-- Exercise 9.8.3 -/
theorem mono_of_continuous_inj {a b:ℝ} (h: a < b) {f:ℝ → ℝ}
  (hf: ContinuousOn f (.Icc a b))
  (hinj: Function.Injective (fun x: Set.Icc a b ↦ f x )) :
  StrictMonoOn f (.Icc a b) ∨ StrictAntiOn f (.Icc a b) := by
  rcases lt_trichotomy (f a) (f b) with hlt | heq | hgt
  . left; exact strictMono_of_continuous_inj h hf hinj hlt
  . exfalso
    suffices a = b by linarith
    have hf' : f (⟨a, by grind⟩ : Set.Icc a b) = f (⟨b, by grind⟩ : Set.Icc a b) := by
      simpa using heq
    simpa using hinj hf'
  . right
    have hnegmono := strictMono_of_continuous_inj (h:=h) (hf:=hf.neg)
      (hinj:=neg_injective.comp hinj)
      (hlt:=by linarith)
    intro x hx y hy hxy
    specialize hnegmono hx hy hxy
    simpa using hnegmono


/-- Exercise 9.8.4 (without continuity) -/
def MonotoneOn.exist_inverse_without_continuity :
    Decidable (∀ (a b : ℝ) (_ : a < b) (f : ℝ → ℝ) (_ : StrictMonoOn f (.Icc a b)),
      f '' (.Icc a b) = .Icc (f a) (f b) ∧
      ∃ finv : ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
        finv '' (.Icc (f a) (f b)) = .Icc a b ∧
        (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
        ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) := by
  -- apply isFalse: strict mono alone doesn't guarantee a continuous inverse
  apply isFalse
  push_neg
  use -1, 1, by linarith
  use fun x => if x ≤ 0 then x else x + 1
  constructor
  . intro x hx y hy hxy
    simp at hx hy ⊢
    split_ifs with h1 h2 h3 <;> linarith
  . intro h1
    have hifneg : (if (1:ℝ) ≤ 0 then (1:ℝ) else 1 + 1) = 2 := by rw [if_neg (by linarith)]; norm_num
    rw [hifneg] at h1
    simp at h1
    exfalso
    have : (1/2) ∈ Set.Icc (-1:ℝ) 2 := by simp; grind
    rw [← h1] at this
    simp at this
    choose x hxmem hx using this
    split_ifs at hx with h1
    . field_simp at hx; linarith
    . field_simp at hx; linarith

/-- Exercise 9.8.4 (without strict monotonicity) -/
def MonotoneOn.exist_inverse_without_strictmono :
    Decidable (∀ (a b : ℝ) (_ : a < b) (f : ℝ → ℝ) (_ : ContinuousOn f (.Icc a b))
        (_ : MonotoneOn f (.Icc a b)),
      f '' (.Icc a b) = .Icc (f a) (f b) ∧
      ∃ finv : ℝ → ℝ, ContinuousOn finv (.Icc (f a) (f b)) ∧ StrictMonoOn finv (.Icc (f a) (f b)) ∧
        finv '' (.Icc (f a) (f b)) = .Icc a b ∧
        (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
        ∀ y ∈ Set.Icc (f a) (f b), f (finv y) = y) := by
  -- apply isFalse: e.g. a constant monotone f on [a,b] has no strict inverse
  apply isFalse
  push_neg
  use 0, 1, by linarith
  use fun _ => 1
  refine ⟨?_, ?_, ?_⟩
  . exact continuousOn_const
  . exact monotoneOn_const
  . intro himg finv hcont hmono hfimg hleft
    exfalso
    have h0 := hleft 0 (by simp); simp at h0
    have h1 := hleft 1 (by simp); simp at h1
    linarith



/-
Exercise 9.8.4: state and prove an analogue of `MonotoneOn.exist_inverse` for `Antitone`
functions.
-/
-- theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ) (hcont: ContinuousOn f (.Icc a b)) (hmono: StrictAntiOn f (.Icc a b)) : sorry := by sorry
theorem AntitoneOn.exist_inverse {a b:ℝ} (h: a < b) (f: ℝ → ℝ)
    (hcont: ContinuousOn f (.Icc a b)) (hanti: StrictAntiOn f (.Icc a b)) :
    f '' (.Icc a b) = .Icc (f b) (f a) ∧
    ∃ finv: ℝ → ℝ, ContinuousOn finv (.Icc (f b) (f a)) ∧ StrictAntiOn finv (.Icc (f b) (f a)) ∧
    finv '' (.Icc (f b) (f a)) = .Icc a b ∧
    (∀ x ∈ Set.Icc a b, finv (f x) = x) ∧
    ∀ y ∈ Set.Icc (f b) (f a), f (finv y) = y
     := by
  have hendpoints : f b < f a := by exact hanti (by simp; linarith) (by simp; linarith) h
  have hmono : StrictMonoOn (-f) (.Icc a b) := by
    intro x hx y hy hxy; simp
    exact hanti hx hy hxy
  choose hgimg g hgcont hgmono hgicc hgx hgy using MonotoneOn.exist_inverse h (-f) (hcont.neg) (hmono)
  refine ⟨?_, fun x => g (-x), ?_, ?_, ?_, ?_, ?_⟩
  . ext x; constructor
    . intro hx; simp at hx ⊢
      choose y hy using hx
      obtain ⟨hyl, hyr⟩ := hy
      subst hyr
      have h1 := hanti.antitoneOn (by simp; linarith) (by tauto) hyl.1
      have h2 := hanti.antitoneOn (by tauto) (by simp; linarith) hyl.2
      constructor <;> linarith
    . intro hx
      choose c hcmem hc using intermediate_value h hcont (y:=x) (by right; exact hx)
      use c
  . apply hgcont.comp
    . exact continuousOn_neg
    . intro x hx
      simp at hx ⊢
      exact ⟨hx.2, hx.1⟩
  . intro x hx y hy hxy
    simp; have hxy' : -y < -x := by linarith
    refine hgmono ?_ ?_ hxy'
    . simp at hy ⊢; exact ⟨hy.2, hy.1⟩
    . simp at hx ⊢; exact ⟨hx.2, hx.1⟩
  . rw [← hgicc]
    simp; ext x; constructor
    . intro hx; simp at hx ⊢
      choose z hz using hx
      use (-z); grind
    . intro hx; simp at hx ⊢
      choose z hz using hx
      use -z; simp; grind
  . intro x hx; simp
    exact hgx x hx
  . intro y hy; simp
    specialize hgy (-y) (by simp at hy ⊢; exact ⟨hy.2, hy.1⟩)
    simp at hgy; exact hgy



/-- An equivalence between the natural numbers and the rationals. -/
noncomputable abbrev q_9_8_5 : ℕ ≃ ℚ := nonempty_equiv_of_countable.some

noncomputable abbrev g_9_8_5 : ℚ → ℝ := fun q ↦ (2:ℝ)^(-q_9_8_5.symm q:ℤ)

noncomputable abbrev f_9_8_5 : ℝ → ℝ := fun x ↦ ∑' r : {r:ℚ // (r:ℝ) < x}, g_9_8_5 r

lemma nonneg_of_g_9_8_5 {q:ℚ} : 0 ≤ g_9_8_5 q := by
  unfold g_9_8_5
  apply zpow_nonneg
  linarith

lemma pos_of_g_9_8_5 {q:ℚ} : 0 < g_9_8_5 q := by
  unfold g_9_8_5
  apply zpow_pos
  linarith

lemma summable_of_g_9_8_5 : Summable g_9_8_5 := by
  have : g_9_8_5 = (fun n : ℕ => (2:ℝ)^(-(n:ℤ))) ∘ q_9_8_5.symm := by rfl
  rw [this]
  rw [Equiv.summable_iff]
  simp only [zpow_neg, zpow_natCast]
  convert summable_geometric_of_lt_one (r:=(1/2)) (by linarith) (by linarith) using 1
  simp

/-- Exercise 9.8.5(a) -/
theorem StrictMonoOn.of_f_9_8_5 : StrictMonoOn f_9_8_5 .univ := by
  simp
  intro x y hxy
  choose q hql hqr using exists_rat_btwn hxy
  unfold f_9_8_5
  show ∑' (r : Subtype (fun r : ℚ => (r : ℝ) < x)), g_9_8_5 (r : ℚ) < ∑' (r : Subtype (fun r : ℚ => (r : ℝ) < y)), g_9_8_5 (r : ℚ)
  rw [show (∑' (r : {r : ℚ // (r : ℝ) < x}), g_9_8_5 (r : ℚ)) = ∑' (r : ℚ), Set.indicator {r : ℚ | (r : ℝ) < x} g_9_8_5 r from tsum_subtype _ _]
  rw [show (∑' (r : {r : ℚ // (r : ℝ) < y}), g_9_8_5 (r : ℚ)) = ∑' (r : ℚ), Set.indicator {r : ℚ | (r : ℝ) < y} g_9_8_5 r from tsum_subtype _ _]
  apply Summable.tsum_lt_tsum (i := q)
  . refine Set.indicator_le_indicator_of_subset ?_ ?_
    . intro x hx; simp at hx ⊢; linarith
    . apply nonneg_of_g_9_8_5
  . rw [Set.indicator_of_notMem (by grind)]
    rw [Set.indicator_of_mem (by grind)]
    apply pos_of_g_9_8_5
  . apply Summable.indicator
    exact summable_of_g_9_8_5
  . apply Summable.indicator
    exact summable_of_g_9_8_5

lemma discontinuous_increment_of_f_9_8_5 {r : ℚ} {x:ℝ} (h : r < x) :
  f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 x := by
  show (∑' q : {q : ℚ // (q:ℝ) < r}, g_9_8_5 q) + g_9_8_5 r ≤ ∑' q : {q : ℚ // (q:ℝ) < x}, g_9_8_5 q
  rw [show (∑' q : {q : ℚ // (q:ℝ) < r}, g_9_8_5 q) = ∑' q : ℚ, {q : ℚ | (q:ℝ) < r}.indicator g_9_8_5 q from tsum_subtype {q : ℚ | (q:ℝ) < r} g_9_8_5]
  rw [show (∑' q : {q : ℚ // (q:ℝ) < x}, g_9_8_5 q) = ∑' q : ℚ, {q : ℚ | (q:ℝ) < x}.indicator g_9_8_5 q from tsum_subtype {q : ℚ | (q:ℝ) < x} g_9_8_5]
  have hsumrhs : Summable ({(q:ℚ) | (q:ℝ) < x}.indicator g_9_8_5) := summable_of_g_9_8_5.indicator _
  have hsumlhs : Summable ({(q:ℚ) | (q:ℝ) < (r:ℝ)}.indicator g_9_8_5) := summable_of_g_9_8_5.indicator _
  have hr_mem : g_9_8_5 r = {(q:ℚ) | (q:ℝ) < x}.indicator g_9_8_5 r := by
    rw [Set.indicator_of_mem]; exact h
  rw [hr_mem]
  conv_rhs => rw [Summable.tsum_eq_add_tsum_ite hsumrhs r, add_comm]
  simp
  simp only [Rat.cast_lt] at hsumlhs ⊢
  refine Summable.tsum_le_tsum ?_ hsumlhs ?_
  . intro q
    by_cases hqr : q = r
    . subst hqr
      rw [if_pos (by rfl), Set.indicator_of_notMem (by grind)]
    . rw [if_neg hqr]
      apply Set.indicator_le_indicator_of_subset
      . intro a ha; simp at ha ⊢
        rify at ha
        linarith
      . apply nonneg_of_g_9_8_5
  . apply Summable.of_nonneg_of_le _ _ hsumrhs
    . intro q
      split_ifs with hqr
      . rfl
      . refine Set.indicator_nonneg ?_ q
        intro a ha; apply nonneg_of_g_9_8_5
    . intro q
      split_ifs with hqr
      . refine Set.indicator_nonneg ?_ q
        intro a ha; apply nonneg_of_g_9_8_5
      . rfl


/-- Exercise 9.8.5(b) -/
theorem ContinuousAt.of_f_9_8_5' (r:ℚ) : ¬ ContinuousAt f_9_8_5 r := by
  intro hcont
  have htend : Filter.Tendsto f_9_8_5 (nhdsWithin (r:ℝ) (Set.Ioi (r:ℝ))) (nhds (f_9_8_5 r)) := by
    apply hcont.tendsto.mono_left
    exact nhdsWithin_le_nhds
  have hev : ∀ᶠ x in nhdsWithin (r:ℝ) (Set.Ioi (r:ℝ)), f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    apply discontinuous_increment_of_f_9_8_5
    simp at hx; exact hx
  have hle : f_9_8_5 r + g_9_8_5 r ≤ f_9_8_5 r := ge_of_tendsto htend hev
  have hpos : 0 < g_9_8_5 r := by positivity
  linarith

noncomputable abbrev fn_9_8_5 : ℕ → ℝ → ℝ :=
  fun n x ↦ ∑' r : {r:ℚ // (r:ℝ) < x ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r}, g_9_8_5 r

lemma ContinuousAt.of_fn_9_8_5 {x : ℝ} (n : ℕ) (hx: ¬ ∃ r:ℚ, x = r) :
  ContinuousAt (fn_9_8_5 n) x := by
  set δ := (Finset.range (n+1)).inf' (by exact Finset.nonempty_range_add_one) (fun n => |q_9_8_5 n - x| : ℕ → ℝ)
  have hδpos : 0 < δ := by
    unfold δ
    rw [Finset.lt_inf'_iff]
    intro q hq
    suffices |(q_9_8_5 q) - x| ≠ 0 by grind
    contrapose! hx
    have heq : (q_9_8_5 q) = x := by grind
    use q_9_8_5 q; exact heq.symm
  simp_rw [Metric.continuousAt_iff, Real.dist_eq]
  intro ε hε
  use δ; constructor
  . exact hδpos
  . intro y hy
    suffices fn_9_8_5 n y = fn_9_8_5 n x by
      rw [this]
      simp
      exact hε
    unfold fn_9_8_5
    conv_lhs =>
      rw [show (∑' r : {r : ℚ // (r:ℝ) < y ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r}, g_9_8_5 (r:ℚ)) = ∑' r : ℚ, {r : ℚ | (r:ℝ) < y ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r}.indicator g_9_8_5 r
                 from tsum_subtype _ g_9_8_5]
    conv_rhs =>
      rw [show (∑' r : {r : ℚ // (r:ℝ) < x ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r}, g_9_8_5 (r:ℚ)) = ∑' r : ℚ, {r : ℚ | (r:ℝ) < x ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r}.indicator g_9_8_5 r
                 from tsum_subtype _ g_9_8_5]
    apply tsum_congr
    intro q
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases h : (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 q
    . have key : (q:ℝ) < y ↔ (q:ℝ) < x := by
        have hk : q_9_8_5.symm q ≤ n := by
          have := (zpow_le_zpow_iff_right₀ (a:=(2:ℝ)) (ha:=by linarith)).mp h
          linarith
        have hδle : δ ≤ |(q : ℝ) - x| := by
          unfold δ
          have hn : q_9_8_5.symm q ∈ Finset.range (n+1) := by simp; exact hk
          have hndist : δ ≤ |q_9_8_5 (q_9_8_5.symm q) - x| := by
            unfold δ
            apply Finset.inf'_le
            exact hn
          simp at hndist
          exact hndist
        grind
      by_cases hqy : (q:ℝ) < y
      . have hry := key.mp hqy
        rw [if_pos (⟨hqy, h⟩), if_pos (⟨hry, h⟩)]
      . rw [if_neg (by tauto), if_neg (by tauto)]
    . rw [if_neg (by tauto), if_neg (by tauto)]


lemma geom_tail_9_8_5 (n : ℕ) : ∑' k : ℕ, (2:ℝ)^(-((n + 1 + k : ℕ):ℤ)) = 2^(-(n:ℤ)) := by
  conv_lhs =>
    arg 1
    ext k
    rw [show -(((n+1+k):ℕ):ℤ) = (-(n):ℤ) - (1:ℤ) + (-k:ℤ) by push_cast; ring_nf]
    rw [zpow_add₀ (by norm_num)]
    arg 2
    rw [zpow_neg, zpow_natCast, inv_eq_one_div]
    rw [show (1:ℝ) = 1 ^ k by exact (one_pow _).symm]
    rw [← div_pow]
  rw [tsum_mul_left, tsum_geometric_two]
  rw [zpow_sub₀ (by norm_num)]
  simp


lemma abs_diff_f_9_8_5_fn_9_8_5 (x: ℝ) (n : ℕ) : |f_9_8_5 x - fn_9_8_5 n x| ≤ 2^(-(n:ℤ)) := by
  have hthr :  ∀ r : ℚ, g_9_8_5 r < (2:ℝ)^(-(n:ℤ)) → n + 1 ≤ q_9_8_5.symm r := by
    intro r hr
    unfold g_9_8_5 at hr
    rw [zpow_lt_zpow_iff_right₀ (by linarith)] at hr
    simp at hr
    omega
  set A : Set ℚ := {r : ℚ | (r:ℝ) < x} with hA
  set B : Set ℚ := {r : ℚ | (r:ℝ) < x ∧ (2:ℝ)^(-(n:ℤ)) ≤ g_9_8_5 r} with hB
  set C : Set ℚ := {r : ℚ | (r:ℝ) < x ∧ g_9_8_5 r < (2:ℝ)^(-(n:ℤ))} with hC
  have hf : f_9_8_5 x = ∑' r : ℚ, A.indicator g_9_8_5 r := by
    rw [hA]; apply tsum_subtype
  have hfn : fn_9_8_5 n x = ∑' r : ℚ, B.indicator g_9_8_5 r := by
    rw [hB]; apply tsum_subtype
  rw [hf, hfn]
  have hAsum : Summable (A.indicator g_9_8_5) := by
    apply summable_of_g_9_8_5.indicator
  have hBsum : Summable (B.indicator g_9_8_5) := by
    apply summable_of_g_9_8_5.indicator
  rw [← Summable.tsum_sub hAsum hBsum]
  have hind : ∀ b : ℚ, A.indicator g_9_8_5 b - B.indicator g_9_8_5 b = C.indicator g_9_8_5 b := by
    intro b
    simp only [hA, hB, hC, Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hax : (b:ℝ) < x
    . simp [hax]
      split_ifs with hp hq <;> linarith
    . simp [hax]
  rw [tsum_congr hind]
  rw [abs_of_nonneg (by apply tsum_nonneg; intro q; apply Set.indicator_nonneg; intro a ha; apply nonneg_of_g_9_8_5)]
  rw [← Equiv.tsum_eq q_9_8_5 (fun b => C.indicator g_9_8_5 b)]
  have hterm : ∀ c : ℕ, C.indicator g_9_8_5 (q_9_8_5 c) ≤ (Set.Ici (n+1)).indicator (fun k => (2:ℝ)^(-(k:ℤ))) c := by
    intro c
    by_cases hc : q_9_8_5 c ∈ C
    . have hge : n + 1 ≤ c := by
        have h := hthr (q_9_8_5 c) hc.2
        rwa [Equiv.symm_apply_apply] at h
      have hval : g_9_8_5 (q_9_8_5 c) = (2:ℝ)^(-(c:ℤ)) := by
        simp only [g_9_8_5, Equiv.symm_apply_apply]
      rw [Set.indicator_of_mem hc, Set.indicator_of_mem (Set.mem_Ici.mpr hge), hval]
    . rw [Set.indicator_of_notMem hc]
      apply Set.indicator_nonneg
      intro a ha
      apply zpow_nonneg
      norm_num
  have hCsum : Summable (fun c : ℕ => C.indicator g_9_8_5 (q_9_8_5 c)) := by
    apply (summable_of_g_9_8_5.indicator C).comp_injective
    exact Equiv.injective q_9_8_5
  calc _ ≤ ∑' (c : ℕ), (Set.Ici (n+1)).indicator (fun k => (2:ℝ)^(-(k:ℤ))) c := by
                  apply Summable.tsum_le_tsum hterm hCsum ?_
                  apply Summable.indicator
                  have : (fun (k:ℕ) ↦ 2 ^ (-k:ℤ)) = (fun (k:ℕ) ↦ ((1:ℝ)/2)^k) := by
                    funext k; simp
                  rw [this]
                  exact summable_geometric_two
       _ = 2 ^ (-(n:ℤ)) := by
                  rw [← geom_tail_9_8_5 n]
                  conv_rhs => rw [tsum_congr (fun k => (Set.indicator_of_mem (Set.mem_Ici.mpr (Nat.le_add_right (n+1) k)) (fun j => (2:ℝ)^(-(j:ℤ)))).symm)]
                  refine (Function.Injective.tsum_eq (g := fun k => n + 1 + k) (by intro x y hxy; simpa using hxy) ?_).symm
                  intro c hc
                  rw [Function.mem_support] at hc
                  simp at hc ⊢
                  use c - n - 1
                  grind


/-- Exercise 9.8.5(c) -/
theorem ContinuousAt.of_f_9_8_5 {x:ℝ} (hx: ¬ ∃ r:ℚ, x = r) : ContinuousAt f_9_8_5 x := by
  simp_rw [Metric.continuousAt_iff, Real.dist_eq]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (2:ℝ)^(-(n:ℤ)) < ε/3 := by
    choose n hn using exists_pow_lt_of_lt_one (x:=ε/3) (y:=(1/2)) (by linarith) (by linarith)
    use n
    convert hn; simp
  have hcont := ContinuousAt.of_fn_9_8_5 n hx
  simp_rw [Metric.continuousAt_iff, Real.dist_eq] at hcont
  choose δ hδpos hδ using hcont (ε/100) (by positivity)
  use δ; constructor
  . exact hδpos
  . intro y hy
    specialize hδ hy
    have habsy := abs_diff_f_9_8_5_fn_9_8_5 y n
    have habsx := abs_diff_f_9_8_5_fn_9_8_5 x n
    rw [abs_sub_comm] at habsx
    calc _ = |f_9_8_5 y - fn_9_8_5 n y + (fn_9_8_5 n y - fn_9_8_5 n x) + (fn_9_8_5 n x - f_9_8_5 x)| := by congr; ring_nf
         _ ≤ |f_9_8_5 y - fn_9_8_5 n y| + |fn_9_8_5 n y - fn_9_8_5 n x| + |fn_9_8_5 n x - f_9_8_5 x| := by grind
         _ ≤ ε / 3 + |fn_9_8_5 n y - fn_9_8_5 n x| + |fn_9_8_5 n x - f_9_8_5 x|                      := by gcongr; linarith
         _ ≤ ε / 3 + |fn_9_8_5 n y - fn_9_8_5 n x| + ε / 3                                           := by gcongr; linarith
         _ ≤ ε / 3 + ε / 100 + ε / 3                                                                 := by gcongr
         _ < ε                                                                                       := by linarith


end Chapter9
