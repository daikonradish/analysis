import Mathlib.Tactic
import Analysis.Section_9_3
import Analysis.Section_9_4
import Analysis.Section_9_6


/-!
# Analysis I, Section 9.7: The intermediate value theorem

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- The intermediate value theorem.
-/

namespace Chapter9

/-- Theorem 9.7.1 (Intermediate value theorem) -/
theorem intermediate_value {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ} (hy: y ∈ Set.Icc (f a) (f b) ∨ y ∈ Set.Icc (f b) (f a)) :
  ∃ c ∈ Set.Icc a b, f c = y := by
  -- This proof is written to follow the structure of the original text.
  obtain hy_left | hy_right := hy
  . by_cases hya : y = f a; use a; grind
    by_cases hyb : y = f b; use b; grind
    simp at hy_left
    replace hya : f a < y := by grind
    replace hyb : y < f b := by grind
    set E := {x | x ∈ Set.Icc a b ∧ f x < y}
    have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
    have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
    have hEa : a ∈ E := by simp [E, hya, le_of_lt hab]
    have hE_nonempty : E.Nonempty := by use a
    set c := sSup E
    have hc : c ∈ Set.Icc a b := by
      simp; split_ands
      . solve_by_elim [le_csSup]
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      grind [csSup_Icc]
    use c, hc
    have hfc_upper : f c ≤ y := by
      have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c - 1/(n+1:ℝ) < sSup E := by linarith
        solve_by_elim [exists_lt_of_lt_csSup]
      set x := fun n ↦ (hxe n).choose
      have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.atTop.Tendsto x (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
        . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ le_csSup hE_bdd (hx1 n)
      replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
      have hfxny (n:ℕ) : f (x n) ≤ y := by specialize hx1 n; simp [E] at hx1; grind
      exact le_of_tendsto' this hfxny
    have hne : c < b := by grind
    have hfc_lower : y ≤ f c := by
      have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
        choose N hN using exists_nat_gt (1/(b-c))
        use N; intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1:ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
        linarith
      choose N hN using this
      have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp [-one_div, le_of_lt (hN n hn)]
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        grind
      have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
        intro n _
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        solve_by_elim [notMem_of_csSup_lt]
      replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≥ y := by
        intro n hn; specialize this n hn; contrapose! this
        simp [E]
        have := hmem n hn
        simp_all
      have hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (nhds c) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (.principal (.Icc a b)) := by
        simp [-one_div, -Set.mem_Icc]; use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply ge_of_tendsto (hf.comp hconv') _
      simp [-one_div]; use N
    linarith
  -- okay, now for the other case.
  by_cases hya : y = f a; use a; grind
  by_cases hyb : y = f b; use b; grind
  simp at hy_right
  replace hya : y < f a := by grind
  replace hyb : f b < y := by grind
  set E := {x | x ∈ Set.Icc a b ∧ y < f x}
  have hE : E ⊆ .Icc a b := fun x ⟨hx₁, hx₂⟩ ↦ hx₁
  have hE_bdd : BddAbove E := bddAbove_Icc.mono hE
  have hEa : a ∈ E := by unfold E; simp [hya, le_of_lt hab]
  have hE_nonempty : E.Nonempty := by use a
  set c := sSup E
  have hc : c ∈ Set.Icc a b := by
      simp; split_ands
      . solve_by_elim [le_csSup]
      convert csSup_le_csSup bddAbove_Icc hE_nonempty hE
      grind [csSup_Icc]
  use c, hc
  have hfc_lower : y ≤ f c := by
      have hxe (n:ℕ) : ∃ x ∈ E, c - 1/(n+1:ℝ) < x := by
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c - 1/(n+1:ℝ) < sSup E := by linarith
        solve_by_elim [exists_lt_of_lt_csSup]
      set x := fun n ↦ (hxe n).choose
      have hx1 (n:ℕ) : x n ∈ E := (hxe n).choose_spec.1
      have hx2 (n:ℕ) : c - 1/(n+1:ℝ) < x n := (hxe n).choose_spec.2
      have : Filter.atTop.Tendsto x (nhds c) := by
        apply Filter.Tendsto.squeeze (g := fun j ↦ c - 1/(j+1:ℝ)) (h := fun j ↦ c) (f := x)
        . convert tendsto_one_div_add_atTop_nhds_zero_nat.const_sub c;simp
        . exact tendsto_const_nhds
        . exact fun n ↦ le_of_lt (hx2 n)
        exact fun n ↦ le_csSup hE_bdd (hx1 n)
      replace := this.comp_of_continuous (hf.continuousWithinAt hc) (fun n ↦ hE (hx1 n))
      have hfxny (n:ℕ) : y ≤ f (x n)  := by specialize hx1 n; simp [E] at hx1; grind
      exact ge_of_tendsto' this hfxny
  have hne : c < b := by grind
  have hfc_upper : f c ≤ y  := by
      have : ∃ N:ℕ, ∀ n ≥ N, (c+1/(n+1:ℝ)) < b := by
        choose N hN using exists_nat_gt (1/(b-c))
        use N; intro n hn
        have hpos : 0 < b-c := by linarith
        have : 1/(n+1:ℝ) < b-c := by rw [one_div_lt] <;> (try positivity); apply hN.trans; norm_cast; linarith
        linarith
      choose N hN using this
      have hmem : ∀ n ≥ N, (c + 1/(n+1:ℝ)) ∈ Set.Icc a b := by
        intro n hn
        simp [-one_div, le_of_lt (hN n hn)]
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        grind
      have : ∀ n ≥ N, c + 1/(n+1:ℝ) ∉ E := by
        intro n _
        have : 1/(n+1:ℝ) > 0 := by positivity
        replace : c + 1/(n+1:ℝ) > c := by linarith
        solve_by_elim [notMem_of_csSup_lt]
      replace : ∀ n ≥ N, f (c + 1/(n+1:ℝ)) ≤ y := by
        intro n hn; specialize this n hn; contrapose! this
        simp [E]
        have := hmem n hn
        simp_all
      have hconv : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (nhds c) := by
        convert tendsto_one_div_add_atTop_nhds_zero_nat.const_add c; simp
      replace hf := (hf.continuousWithinAt hc).tendsto
      rw [nhdsWithin.eq_1] at hf
      have hconv' : Filter.atTop.Tendsto (fun n:ℕ ↦ c + 1/(n+1:ℝ)) (.principal (.Icc a b)) := by
        simp [-one_div, -Set.mem_Icc]; use N
      replace hconv' := Filter.tendsto_inf.mpr ⟨ hconv, hconv' ⟩
      apply le_of_tendsto (hf.comp hconv') _
      simp [-one_div]; use N
  linarith



open Classical in
noncomputable abbrev f_9_7_1 : ℝ → ℝ := fun x ↦ if x ≤ 0 then -1 else 1

example : 0 ∈ Set.Icc (f_9_7_1 (-1)) (f_9_7_1 1) ∧ ¬ ∃ x ∈ Set.Icc (-1) 1, f_9_7_1 x = 0 := by
  rw [show f_9_7_1 (-1) = -1 by unfold f_9_7_1; rw [if_pos (by linarith)]]
  rw [show f_9_7_1 1 = 1 by unfold f_9_7_1; rw [if_neg (by linarith)]]
  constructor
  · simp
  · push_neg
    intro x hx
    unfold f_9_7_1; split_ifs <;> linarith

/-- Remark 9.7.2 -/
abbrev f_9_7_2 : ℝ → ℝ := fun x ↦ x^3 - x

example : f_9_7_2 (-2) = -6 := by unfold f_9_7_2; norm_num
example : f_9_7_2 2 = 6 := by unfold f_9_7_2; norm_num
example : f_9_7_2 (-1) = 0 := by unfold f_9_7_2; norm_num
example : f_9_7_2 0 = 0 := by unfold f_9_7_2; norm_num
example : f_9_7_2 1 = 0 := by unfold f_9_7_2; norm_num

/-- Remark 9.7.3 -/
example : ∃ x:ℝ, 0 ≤ x ∧ x ≤ 2 ∧ x^2 = 2 := by
  -- here, i suppose the intention is for us to use IVT and _not_ to use
  -- the obvious witness.
  have hcont : ContinuousOn (fun (x:ℝ) => x^2) (Set.Icc 0 2) := by
    apply ContinuousOn.pow
    exact continuousOn_id
  have hivt := intermediate_value
    (a:=0)
    (b:=2)
    (by linarith)
    (f:=fun (x:ℝ) => x^2)
    (hf:=hcont)
    (y:=2)
    (by left; simp; norm_num)
  choose x hx using hivt; simp at hx
  use x
  tauto

/-- Corollary 9.7.4 (Images of continuous functions) / Exercise 9.7.1 -/
theorem continuous_image_Icc {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) {y:ℝ} (hy: sInf (f '' .Icc a b) ≤ y ∧ y ≤ sSup (f '' .Icc a b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  choose xmin hmin using IsMinOn.of_continuous_on_compact hab hf
  choose xmax hmax using IsMaxOn.of_continuous_on_compact hab hf
  have hsup : sSup (f '' Set.Icc a b) = f xmax := by
    apply IsGreatest.csSup_eq
    constructor
    · simp; use xmax; simpa using hmax.1
    · rintro y ⟨x, hx, rfl⟩
      exact (isMaxOn_iff.mp hmax.2) x hx
  have hinf : sInf (f '' Set.Icc a b) = f xmin := by
    apply IsLeast.csInf_eq
    constructor
    · simp; use xmin; simpa using hmin.1
    · rintro y ⟨x, hx, rfl⟩
      exact (isMinOn_iff.mp hmin.2) x hx
  rw [hinf, hsup] at hy
  rcases lt_trichotomy xmin xmax with hlt | heq | hgt
  · have hfrestrict : ContinuousOn f (.Icc xmin xmax) := by
      apply ContinuousOn.restrict (X:=.Icc a b) (hf:=hf)
      intro x hx; simp at hx ⊢; grind
    choose c hcmem hfc using intermediate_value hlt hfrestrict (y:=y) (by left; simp; grind)
    use c; constructor
    · simp at hcmem ⊢; grind
    · exact hfc
  · use xmin; simp; grind
  · have hfrestrict : ContinuousOn f (.Icc xmax xmin) := by
      apply ContinuousOn.restrict (X:=.Icc a b) (hf:=hf)
      intro x hx; simp at hx ⊢; grind
    choose c hcmem hfc using intermediate_value hgt hfrestrict (y:=y) (by right; simp; grind)
    use c; constructor
    · simp at hcmem ⊢; grind
    · exact hfc

theorem continuous_image_Icc' {a b:ℝ} (hab: a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b)) : f '' .Icc a b = .Icc (sInf (f '' .Icc a b)) (sSup (f '' .Icc a b)) := by
  ext x; constructor
  · intro hx
    have hbbon := BddOn.of_continuous_on_compact hab hf
    constructor
    · apply csInf_le
      · choose M hM using ((BddOn.iff _ _).mp hbbon).2
        use -M
        intro x hx
        simp at hx
        choose x' hx' using hx
        specialize hM x' (by grind)
        grind
      · simp; grind
    · apply le_csSup
      · choose M hM using ((BddOn.iff _ _).mp hbbon).1
        use M
        intro x hx
        simp at hx
        choose x' hx' using hx
        specialize hM x' (by grind)
        grind
      · simp; grind
  · intro hx
    choose c hc using continuous_image_Icc hab hf hx
    use c


/-- Exercise 9.7.2 -/
theorem exists_fixed_pt {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc 0 1)) (hmap: f '' .Icc 0 1 ⊆ .Icc 0 1) : ∃ x ∈ Set.Icc 0 1, f x = x := by
  have hf' : ContinuousOn (fun x => f x - x) (.Icc 0 1) := by
    apply ContinuousOn.sub
    · exact hf
    · exact continuousOn_id
  have hivt := intermediate_value (a:=0) (b:=1) (hab:=by linarith) (hf:=hf') (y:=0) (by
    right
    simp
    have hf1 : f 1 ∈  f '' Set.Icc 0 1 := by use 1; simp
    have hf0 : f 0 ∈  f '' Set.Icc 0 1 := by use 0; simp
    have hf1' := hmap hf1; simp at hf1'
    have hf0' := hmap hf0; simp at hf0'
    grind
  )
  choose x hxmem hx using hivt
  use x; constructor
  · exact hxmem
  · linarith

end Chapter9
