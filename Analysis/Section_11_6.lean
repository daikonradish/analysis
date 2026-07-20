import Mathlib.Tactic
import Analysis.Section_9_8
import Analysis.Section_11_1
import Analysis.Section_11_5
import Mathlib.Analysis.PSeries

/-!
# Analysis I, Section 11.6: Riemann integrability of monotone functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Riemann integrability of monotone functions.

-/

namespace Chapter11
open Chapter9 BoundedInterval

set_option maxHeartbeats 300000 in
/-- Proposition 11.6.1 -/
theorem integ_of_monotone {a b:ℝ} {f:ℝ → ℝ} (hf: MonotoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  -- This proof is adapted from the structure of the original text.
  by_cases hab : 0 < b-a
  swap
  . apply (integ_on_subsingleton _).1; rw [←BoundedInterval.length_of_subsingleton]; aesop
  have hbound := BddOn.of_monotone hf
  set I := Icc a b
  have hab' : a ≤ b := by linarith
  have (ε:ℝ) (hε: 0 < ε) : upper_integral f I - lower_integral f I ≤ ((f b - f a) * (b-a)) *ε := by
    choose N hN using exists_nat_gt (1/ε)
    have hNpos : 0 < N := by rify; linarith [show 0 < 1/ε by positivity]
    set δ := (b-a)/N
    have hδpos : 0 < δ := by positivity
    have hbeq : b = a + δ*N := by simp [δ]; field_simp; linarith
    set e : ℕ ↪ BoundedInterval := {
      toFun j := Ico (a + δ*j) (a + δ*(j+1))
      inj' j k hjk := by simp at hjk; obtain _ | _ := hjk <;> linarith
    }
    set P : Partition I := {
      intervals := insert (Icc b b) (.map e (.range N))
      exists_unique := by
        intro x hx; simp; by_cases hb: x = b
        . apply ExistsUnique.intro (Icc b b)
          . simp [hb, mem_iff]
          rintro J ⟨ rfl | ⟨ j, hA, rfl ⟩, hJb ⟩; rfl
          simp [e, mem_iff, hb, hbeq] at hJb
          replace hJb := hJb.2
          rw [mul_lt_mul_iff_of_pos_left hδpos] at hJb
          norm_cast at hJb; linarith
        simp [I, mem_iff] at hx
        set j := ⌊ (x-a)/δ ⌋₊
        have hxa : 0 ≤ x-a := by linarith
        have hxaδ : 0 ≤ (x-a)/δ := by positivity
        have hxb : x < b := lt_of_le_of_ne hx.2 hb
        have hxj : x ∈ e j := by
          simp [e, mem_iff, j]; split_ands
          . calc
              _ ≤ a + δ * ((x-a)/δ) := by gcongr; grind [Nat.floor_le]
              _ = x := by grind
          calc
            _ = a + δ * ((x-a)/δ) := by field_simp; linarith
            _ < _ := by gcongr; apply Nat.lt_floor_add_one
        apply ExistsUnique.intro (e j)
        . refine ⟨ ?_, hxj ⟩; right; use j; simp [j, Nat.floor_lt hxaδ, div_lt_iff₀' hδpos]; linarith
        rintro J ⟨ rfl | ⟨ k, hk, rfl ⟩, hxJ ⟩
        . simp [mem_iff] at hxJ; grind
        simp [mem_iff, e] at hxJ hxj
        obtain hjk | rfl | hjk := lt_trichotomy j k
        . replace hjk : δ*((j:ℝ)+1) ≤ δ*(k:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
          linarith
        . rfl
        replace hjk : δ*((k:ℝ)+1) ≤ δ*(j:ℝ) := by rw [mul_le_mul_iff_of_pos_left hδpos]; norm_cast
        linarith
      contains J hJ := by
        simp at hJ; obtain rfl | ⟨ j, hj, rfl ⟩ := hJ <;> simp [subset_iff, e, I]
        . linarith
        apply Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc _ _)
        . simp; positivity
        simp [hbeq]; gcongr; norm_cast
    }
    have hup := calc
      upper_integral f I ≤ ∑ J ∈ P.intervals, (sSup (f '' (J:Set ℝ))) * |J|ₗ := upper_integ_le_upper_sum hbound P
      _ = ∑ j ∈ .range N, (sSup (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply csSup_le
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have : a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply hf _ _ (by order) <;> simp [I, hδj1, this]; grind
    have hdown := calc
      lower_integral f I ≥ ∑ J ∈ P.intervals, (sInf (f '' (J:Set ℝ))) * |J|ₗ :=
        lower_integ_ge_lower_sum hbound P
      _ = ∑ j ∈ .range N, (sInf (f '' (Ico (a + δ*j) (a + δ*(j+1))))) * |Ico (a + δ*j) (a + δ*(j+1))|ₗ := by simp [P]; congr
      _ ≥ ∑ j ∈ .range N, f (a + δ*j) * δ := by
        apply Finset.sum_le_sum; intro j hj
        convert (mul_le_mul_iff_left₀ hδpos).mpr ?_
        . simp [length]; ring_nf; simp [le_of_lt hδpos]
        apply le_csInf
        . simp; grind
        intro y hy; simp at hy; obtain ⟨ x, ⟨ hx1, hx2 ⟩, rfl ⟩ := hy
        have hajb': a + δ*(j+1) ≤ b := by simp [hbeq]; gcongr; norm_cast; grind
        have hδj : 0 ≤ δ*j := by positivity
        have hδj1 : 0 ≤ δ*(j+1) := by positivity
        apply_rules [hf] <;> simp [I, hδj] <;> grind
    calc
      _ ≤ ∑ j ∈ .range N, f (a + δ*(j+1)) * δ - ∑ j ∈ .range N, f (a + δ*j) * δ := by linarith
      _ = (f b - f a) * δ := by
        rw [←Finset.sum_sub_distrib]
        have := Finset.sum_range_sub (fun n ↦ f (a + δ*n) * δ) N
        simp only [Nat.cast_add, Nat.cast_one] at this
        convert this using 1; simp [hbeq]; ring
      _ ≤ _ := by
        have : 0 ≤ f b - f a := by simp; apply hf <;> simp [I, hab']
        simp [mul_assoc, δ]; gcongr
        rw [div_le_iff₀', mul_comm, mul_assoc]
        nth_rewrite 1 [←mul_one (b-a)]
        gcongr; rw [←div_le_iff₀']; linarith
        all_goals positivity
  refine ⟨ hbound, ?_ ⟩
  observe low_le_up : lower_integral f I ≤ upper_integral f I
  linarith [nonneg_of_le_const_mul_eps this]


/-- Proposition 11.6.1 -/
theorem integ_of_antitone {a b:ℝ} {f:ℝ → ℝ} (hf: AntitoneOn f (Icc a b)) :
  IntegrableOn f (Icc a b) := by
  rw [←neg_neg f]; apply (integ_of_monotone _).neg.1; convert hf.neg using 1

open Classical in
/-- Corollary 11.6.3 / Exercise 11.6.1 -/
theorem integ_of_bdd_monotone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: MonotoneOn f I) : IntegrableOn f I := by
  by_cases! hab : I.b ≤ I.a
  . refine (integ_on_subsingleton ?_).1
    unfold length; simp; exact hab
  have ⟨habove, hbelow⟩ := (BddOn.iff f I).mp hbound
  replace habove : BddAbove (f '' I) := by
    choose B hB using habove
    use B; intro x hx
    choose y hy hfy using hx
    rw [← hfy]
    exact hB y hy
  replace hbelow : BddBelow (f '' I) := by
    choose B hB using hbelow
    use -B; intro x hx
    choose y hy hfy using hx
    rw [← hfy]
    exact hB y hy
  set l := sInf (f '' I); set r := sSup (f '' I)
  set g : ℝ → ℝ := fun x => if x ∈ I then f x else if x ≤ I.a then l else r
  have hinside : Ioo I.a I.b ⊆ I := by exact Ioo_subset I
  have houtside : I ⊆ Icc I.a I.b := by exact subset_Icc I
  have hIcc : ∀ x ∈ (Icc I.a I.b), x ∉ I → x = I.a ∨ x = I.b := by
    intro x hx hxI
    contrapose! hxI
    match I with
    | Ioo a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hx hxI
      simp [BoundedInterval.mem_iff] at hx ⊢
      constructor <;> grind
    | Icc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hx hxI
      simp [BoundedInterval.mem_iff] at hx ⊢
      constructor <;> linarith
    | Ioc a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hx hxI
      simp [BoundedInterval.mem_iff] at hx ⊢
      constructor <;> grind
    | Ico a b =>
      simp [BoundedInterval.a, BoundedInterval.b] at hx hxI
      simp [BoundedInterval.mem_iff] at hx ⊢
      constructor <;> grind
  have hg : MonotoneOn g (Icc I.a I.b) := by
    intro x hx y hy hxy
    by_cases! hxI : x ∈ I <;> by_cases! hyI : y ∈ I
    . unfold g; simp [hxI, hyI]
      exact hf hxI hyI hxy
    . rcases hIcc (x:=y) hy hyI with ha | hb
      . simp at hx hy
        have heq : x = y := by linarith
        rw [heq]
      . unfold g
        conv_lhs => simp [hxI]
        conv_rhs => rw [if_neg hyI, if_neg (by linarith)]
        unfold r
        apply le_csSup habove
        use x; simp; exact hxI
    . rcases hIcc (x:=x) hx hxI with ha | hb
      . unfold g
        conv_lhs => rw [if_neg hxI, if_pos (by linarith)]
        conv_rhs => simp [hyI]
        unfold l
        apply csInf_le hbelow
        use y; simp; exact hyI
      . simp at hx hy
        have heq : x = y := by linarith
        rw [heq]
    . rcases hIcc (x:=x) hx hxI with hxa | hxb  <;> rcases hIcc (x:=y) hy hyI with hya | hyb
      . rw [hxa, hya]
      . unfold g
        conv_lhs => rw [if_neg hxI, if_pos (by linarith)]
        conv_rhs => rw [if_neg hyI, if_neg (by linarith)]
        unfold l r
        exact Real.sInf_le_sSup _ hbelow habove
      . rw [hxb, hya] at hxy; linarith
      . rw [hxb, hyb]
  have hgintegrable := integ_of_monotone hg
  have hg' := IntegrableOn.mono' houtside hgintegrable
  apply IntegrableOn.congr (hf:=hg')
  intro x hx
  unfold g; rw [if_pos (by simpa using hx)]


theorem integ_of_bdd_antitone {I:BoundedInterval} {f:ℝ → ℝ} (hbound: BddOn f I)
  (hf: AntitoneOn f I) : IntegrableOn f I := by
  -- rw [←neg_neg f]; apply (integ_of_monotone _).neg.1; convert hf.neg using 1
  rw [← neg_neg f]
  have hbound' : BddOn (-f) I := by
    choose M hM using hbound
    use M
    simp; exact hM
  apply (integ_of_bdd_monotone hbound' _).neg.1
  convert hf.neg using 1


/-- Proposition 11.6.4 (Integral test) -/
theorem summable_iff_integ_of_antitone {f:ℝ → ℝ} (hnon: ∀ x ≥ 0, f x ≥ 0)
  (hf: AntitoneOn f (.Ici 0)) :
  Summable (fun n:ℕ ↦ f n) ↔ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  have hintegrable : ∀ N : ℝ, IntegrableOn f (Icc 0 N) := by
    intro N
    apply integ_of_antitone
    intro x hx y hy hxy
    have hx' : x ∈ Set.Ici 0 := by simp at hx; exact hx.1
    have hy' : y ∈ Set.Ici 0 := by simp at hy; exact hy.1
    exact hf hx' hy' hxy
  constructor
  . have key : ∀ n : ℕ, integ f (Icc 0 (n:ℝ)) ≤ ∑ j ∈ Finset.range n, f j := by
      intro n
      induction' n with k ih
      . simp; suffices integ f (Icc 0 0) = 0 by rw [this]
        refine (integ_on_subsingleton ?_).2; simp
      . have hjoin : (Icc 0 (k+1:ℝ)).joins (Icc 0 k) (Ioc k (k+1)) := by
            exact join_Icc_Ioc (by linarith) (by linarith)
        have hksucc := hintegrable (k+1)
        push_cast at hksucc ⊢
        have hintegofjoin := (hksucc.join hjoin).2.2
        conv_lhs => rw [hintegofjoin]
        conv_rhs => rw [Finset.sum_range_succ]
        gcongr
        set I := (Ioc (k:ℝ) ((k:ℝ) + 1))
        have hbddI : BddOn f I := by
          apply hksucc.1.mono
          unfold I; simp; grind
        have h1 : integ f I ≤ upper_riemann_sum f (⊥: Partition I) := by
          unfold integ
          exact upper_integ_le_upper_sum hbddI ⊥
        suffices upper_riemann_sum f (⊥: Partition I) ≤ f k by linarith
        unfold upper_riemann_sum
        rw [BoundedInterval.intervals_of_bot]; simp
        rw [show I.length = 1 by unfold I; simp]
        rw [mul_one]
        unfold I
        apply csSup_le (by simp)
        intro b hb; simp at hb; choose x hx hfx using hb
        rw [← hfx]
        apply hf
        . simp_all
        . simp_all; linarith
        . linarith
    intro h
    replace h : ∃ M:ℝ, ∀ N:ℕ, ∑ j ∈ Finset.range N, f (j:ℝ) ≤ M := by
      use ∑' (n:ℕ), f (n:ℝ)
      intro N
      apply h.sum_le_tsum (Finset.range N) ?_
      intro n hn; simp at hn
      exact hnon n (by grind)
    choose M hM using h
    use M
    intro x hx
    set x' := ⌈x⌉₊
    specialize hM x'
    specialize key x'
    suffices integ f (Icc 0 x) ≤ integ f (Icc 0 ↑x') by linarith
    have hjoin : (Icc (0:ℝ) ⌈x⌉₊).joins (Icc 0 x) (Ioc x ⌈x⌉₊) := by
            exact join_Icc_Ioc (by linarith) (by exact Nat.le_ceil x)
    have hintegofjoin := ((hintegrable ⌈x⌉₊).join hjoin).2.2
    rw [hintegofjoin]
    suffices 0 ≤ integ f (Ioc x ↑⌈x⌉₊) by linarith
    apply IntegrableOn.nonneg
    . apply integ_of_bdd_antitone
      . obtain ⟨hbd, _⟩ := hintegrable ⌈x⌉₊
        choose B hB using hbd
        use B; intro z hz; simp at hB hz ⊢
        exact hB z (by linarith) (by linarith)
      . intro a ha b hb hbc
        apply hf
        . simp_all; linarith
        . simp_all; linarith
        . exact hbc
    . intro z hz
      apply hnon
      rw [BoundedInterval.mem_iff] at hz; simp at hz
      linarith
  . intro h
    choose M hM using h
    have hMpos : 0 ≤ M := by
      specialize hM 1 (by norm_num)
      suffices 0 ≤ integ f (Icc 0 1) by linarith
      apply IntegrableOn.nonneg
      . convert hintegrable 1
      . intro x hx
        apply hnon
        rw [BoundedInterval.mem_iff] at hx;
        simp at hx; linarith
    apply summable_of_sum_range_le (c:=M + f 0)
    . intro n
      exact hnon n (by grind)
    . have key : ∀ n : ℕ, ∑ j ∈ Finset.range n, f (j+1) ≤ integ f (Icc 0 (n:ℝ)) := by
        intro n
        induction' n with k ih
        . simp; suffices integ f (Icc 0 0) = 0 by rw [this]
          refine (integ_on_subsingleton ?_).2; simp
        . have hjoin : (Icc 0 (k+1:ℝ)).joins (Icc 0 k) (Ioc k (k+1)) := by
            exact join_Icc_Ioc (by linarith) (by linarith)
          have hksucc := hintegrable (k+1)
          push_cast at hksucc ⊢
          have hintegofjoin := (hksucc.join hjoin).2.2
          conv_lhs => rw [Finset.sum_range_succ]
          conv_rhs => rw [hintegofjoin]
          gcongr
          set I := (Ioc (k:ℝ) ((k:ℝ) + 1))
          have hbddI : BddOn f I := by
            apply hksucc.1.mono
            unfold I; simp; grind
          have h1 : lower_integral f I ≤ integ f I := by
            apply lower_integral_le_upper
            exact hbddI
          have h2 : lower_riemann_sum f (⊥: Partition I) ≤ lower_integral f I := by
            apply lower_integ_ge_lower_sum
            exact hbddI
          suffices f (k+1) ≤ lower_riemann_sum f (⊥: Partition I) by linarith
          unfold lower_riemann_sum
          rw [BoundedInterval.intervals_of_bot]; simp
          rw [show I.length = 1 by unfold I; simp]
          rw [mul_one]
          unfold I
          apply le_csInf (by simp)
          intro b hb; simp at hb
          choose x hx hfx using hb
          rw [← hfx]
          apply hf
          . simp; linarith
          . simp; linarith
          . linarith
      intro n
      by_cases! h0 : n = 0
      . subst h0; simp
        specialize hnon 0 (by rfl)
        linarith
      . choose m hm using Nat.exists_eq_succ_of_ne_zero h0
        rw [hm, Finset.sum_range_succ']
        simp
        have h1 := key m
        have h2 := hM m (by linarith)
        linarith


open Classical in
theorem integ_of_piecewise_integrable {f : ℝ → ℝ} {I : BoundedInterval} {P : Partition I} (h : ∀ J ∈ P.intervals, IntegrableOn f J) :
  IntegrableOn f I := by
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
  have hgJ : ∀ J ∈ P.intervals, IntegrableOn (g J) I := by
    intro J hJ
    apply IntegrableOn.of_extend
    . exact P.contains J hJ
    . exact h J hJ
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
  have hcongr := key P.intervals hgJ
  . apply IntegrableOn.congr (hf:=hcongr)
    intro x hx
    unfold g
    simp
    specialize hg x hx
    specialize heq x hx
    rw [← hg, ← heq]

theorem integ_of_join {f : ℝ → ℝ} {I J K : BoundedInterval} (hIJK : I.joins J K) (hJ : IntegrableOn f J) (hK : IntegrableOn f K) :
  IntegrableOn f I := by
  have ⟨h1, h2, h3⟩ := hIJK
  set P : Partition I := (⊥ : Partition J).join (⊥ : Partition K) hIJK
  have hP : P.intervals = {J, K} := by rfl
  apply integ_of_piecewise_integrable (P:=P)
  intro L hL
  rw [hP] at hL; simp at hL
  rcases hL with h | h
  . subst h; exact hJ
  . subst h; exact hK


-- Exercise 11.6.2: Formulate a reasonable notion of a piecewise monotone function, and then
-- show that all bounded piecewise monotone functions are Riemann integrable.
noncomputable def PiecewiseMonotoneOn (f : ℝ → ℝ) (I : BoundedInterval) : Prop :=
  ∃ P:Partition I, ∀ J ∈ P.intervals, MonotoneOn f J

theorem integ_of_piecewise_monotone {I : BoundedInterval} {f : ℝ → ℝ} (hf : PiecewiseMonotoneOn f I) (hbd : BddOn f I) :
  IntegrableOn f I := by
  choose P hP using hf
  have hf' : ∀ J ∈ P.intervals, IntegrableOn f J := by
    intro J hJ
    apply integ_of_bdd_monotone
    . apply hbd.mono
      exact P.contains J hJ
    . exact hP J hJ
  exact integ_of_piecewise_integrable hf'

open Classical in
/-- Exercise 11.6.4 -/
example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ Summable (fun n:ℕ ↦ f n) ∧ ¬ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  set f : ℝ → ℝ := fun x => if x ∈ Set.range (Nat.cast : ℕ → ℝ) then 1 / x ^ 2 else 1
  use f; refine ⟨?_, ?_, ?_⟩
  . intro x hx
    unfold f; split_ifs with h
    . simp at h; choose n hn using h
      positivity
    . norm_num
  . have heq : (fun (n:ℕ) => f (n:ℝ)) = (fun (n:ℕ) => 1 / (n:ℝ) ^ 2) := by
      ext x
      unfold f
      rw [if_pos (by use x)]
    rw [heq]
    exact Real.summable_one_div_nat_pow.mpr (by norm_num)
  . have key : ∀ (N:ℕ), IntegrableOn f (Icc (0:ℝ) N) ∧ integ f (Icc (0:ℝ) N) = N := by
      intro N
      induction' N with k ih
      . constructor
        . apply integ_of_monotone
          intro x hx y hy hxy; simp at hx hy
          rw [hx, hy]
        . simp; suffices integ f (Icc 0 0) = 0 by rw [this]
          refine (integ_on_subsingleton ?_).2; simp
      . obtain ⟨hintegrable, hinteg⟩ := ih
        have hjoin1 := BoundedInterval.join_Ioo_Icc (a:=(k:ℝ)) (b:=(k+1:ℝ)) (c:=((k+1):ℝ)) (by linarith) (by linarith)
        have hjoin2 := join_Icc_Ioc (a:=(0:ℝ)) (b:=(k:ℝ)) (c:=((k+1):ℝ)) (by linarith) (by linarith)
        have hconst : ConstantOn f (Ioo (k:ℝ) ((k+1):ℝ)) := by
              use 1; simp
              intro x hx hx'
              unfold f; rw [if_neg]
              rintro ⟨m, rfl⟩
              have h1 : k < m := by exact_mod_cast hx
              have h2 : m < k + 1 := by exact_mod_cast hx'
              omega
        have hstep1 : IntegrableOn f (Ioc (k:ℝ) ((k + 1):ℝ)) := by
          apply integ_of_join (f:=f) (hIJK:=hjoin1)
          . exact (integ_of_piecewise_const hconst.piecewiseConstantOn).1
          . apply integ_of_monotone
            intro x hx y hy hxy; simp at hx hy
            rw [hx, hy]
        have hstep2 := integ_of_join (f:=f) (hIJK:=hjoin2) (hJ:=hintegrable) (hK:=hstep1)
        push_cast at hjoin1 hstep1 ⊢; refine ⟨hstep2, ?_⟩
        rw [(hstep2.join hjoin2).2.2, (hstep1.join hjoin1).2.2]
        conv_rhs => rw [← hinteg]
        congr
        have : integ f (Icc ((k + 1):ℝ) ((k + 1):ℝ)) = 0 := by
          refine (integ_on_subsingleton ?_).2
          simp
        push_cast at this; simp [this]
        have hpc := hconst.piecewiseConstantOn
        rw [(integ_of_piecewise_const hpc).2]
        simp only [PiecewiseConstantOn.integ']
        rw [PiecewiseConstantOn.integ_const' hconst]
        simp; apply ConstantOn.const_eq
        . simp
        . intro x hx; simp at hx
          unfold f; rw [if_neg]
          rintro ⟨m, rfl⟩
          have h1 : k < m := by exact_mod_cast hx.1
          have h2 : m < k + 1 := by exact_mod_cast hx.2
          omega
    intro h; choose M hM using h
    obtain ⟨n, hn⟩ := exists_nat_gt M          -- hn : M < ↑n.
    have h1 := (key n).2                        -- integ f (Icc 0 ↑n) = ↑n
    have h2 := hM n (Nat.cast_nonneg n)         -- integ f (Icc 0 ↑n) ≤ M
    rw [h1] at h2                               -- ↑n ≤ M
    linarith                                    -- M < ↑n ≤ M

open Classical in
example : ∃ (f:ℝ → ℝ), (∀ x ≥ 0, f x ≥ 0) ∧ ¬ Summable (fun n:ℕ ↦ f n) ∧ ∃ M, ∀ N ≥ 0, integ f (Icc 0 N) ≤ M := by
  set f : ℝ → ℝ := fun x => if x ∈ Set.range (Nat.cast : ℕ → ℝ) then 1 else 0
  use f; refine ⟨?_, ?_, ?_⟩
  . unfold f; intro x hx; simp
    split_ifs with h; all_goals linarith
  . have heq : (fun (n:ℕ) => f (n:ℝ)) = (fun (n:ℕ) => 1) := by
      ext x
      unfold f
      rw [if_pos (by use x)]
    rw [heq]
    refine (not_summable_iff_tendsto_nat_atTop_of_nonneg ?_).mpr ?_
    . simp
    . have heq : (fun (n:ℕ) ↦ ∑ i ∈ Finset.range n, (1:ℝ))  = (fun (n:ℕ) => (n:ℝ)) := by
        ext n; simp
      rw [heq]
      exact tendsto_natCast_atTop_atTop
  . have key : ∀ (N:ℕ), IntegrableOn f (Icc (0:ℝ) N) ∧ integ f (Icc (0:ℝ) N) = 0 := by
      intro N
      induction' N with k ih
      . constructor
        . apply integ_of_monotone
          intro x hx y hy hxy; simp at hx hy
          rw [hx, hy]
        . simp; suffices integ f (Icc 0 0) = 0 by rw [this]
          refine (integ_on_subsingleton ?_).2; simp
      · obtain ⟨hintegrable, hinteg⟩ := ih
        have hjoin1 := BoundedInterval.join_Ioo_Icc (a:=(k:ℝ)) (b:=(k+1:ℝ)) (c:=((k+1):ℝ)) (by linarith) (by linarith)
        have hjoin2 := join_Icc_Ioc (a:=(0:ℝ)) (b:=(k:ℝ)) (c:=((k+1):ℝ)) (by linarith) (by linarith)
        have hconst : ConstantOn f (Ioo (k:ℝ) ((k+1):ℝ)) := by
              use 0; simp
              intro x hx hx'
              unfold f; rw [if_neg]
              rintro ⟨m, rfl⟩
              have h1 : k < m := by exact_mod_cast hx
              have h2 : m < k + 1 := by exact_mod_cast hx'
              omega
        have hstep1 : IntegrableOn f (Ioc (k:ℝ) ((k + 1):ℝ)) := by
          apply integ_of_join (f:=f) (hIJK:=hjoin1)
          . exact (integ_of_piecewise_const hconst.piecewiseConstantOn).1
          . apply integ_of_monotone
            intro x hx y hy hxy; simp at hx hy
            rw [hx, hy]
        have hstep2 := integ_of_join (f:=f) (hIJK:=hjoin2) (hJ:=hintegrable) (hK:=hstep1)
        push_cast at hjoin1 hstep1 ⊢; refine ⟨hstep2, ?_⟩
        rw [(hstep2.join hjoin2).2.2, (hstep1.join hjoin1).2.2]
        conv_rhs => rw [← hinteg]
        have : integ f (Icc ((k + 1):ℝ) ((k + 1):ℝ)) = 0 := by
          refine (integ_on_subsingleton ?_).2
          simp
        push_cast at this; simp [this]
        have hpc := hconst.piecewiseConstantOn
        rw [(integ_of_piecewise_const hpc).2]
        simp only [PiecewiseConstantOn.integ']
        rw [PiecewiseConstantOn.integ_const' hconst]
        simp; apply ConstantOn.const_eq
        . simp
        . intro x hx; simp at hx
          unfold f; rw [if_neg]
          rintro ⟨m, rfl⟩
          have h1 : k < m := by exact_mod_cast hx.1
          have h2 : m < k + 1 := by exact_mod_cast hx.2
          omega
    use 0; intro x hx
    specialize key (⌊x⌋₊)
    have hnotnat : ∀ p ∈ Ioc ⌊x⌋₊ x, p ∉ Set.range Nat.cast := by
      intro p hp; rw [BoundedInterval.mem_iff] at hp; simp at hp
      intro hm; choose N hN using hm
      subst hN; obtain ⟨h1, h2⟩ := hp
      replace h1 : ⌊x⌋₊ < (N:ℝ) := by exact_mod_cast h1
      replace h2 : N ≤ ⌊x⌋₊ := by exact Nat.le_floor h2
      rify at h2
      linarith
    have h0 : ∀ p ∈ Ioc ⌊x⌋₊ x, f p = 0 := by
      intro p hp
      unfold f
      rw [if_neg (hnotnat p hp)]
    have hjoin := BoundedInterval.join_Icc_Ioc (a:=(0:ℝ)) (b:=⌊x⌋₊) (c:=x) (by linarith) (by exact Nat.floor_le hx)
    have hconst : ConstantOn f (Ioc ⌊x⌋₊ x) := by
      use 0; intro ⟨p, hp⟩
      simp
      exact h0 p hp
    have hstep : IntegrableOn f (Icc (0:ℝ) x) := by
      apply integ_of_join (f:=f) (hIJK:=hjoin) (hJ:=key.1)
      apply integ_of_bdd_monotone
      . use 0; intro p hp
        rw [h0 p hp]; simp
      . intro p hp r hr hpr
        rw [h0 p hp, h0 r hr]
    rw [(hstep.join hjoin).2.2, key.2]
    simp
    suffices integ f (Ioc ⌊x⌋₊ x) = 0 by linarith
    have hpc := hconst.piecewiseConstantOn
    rw [(integ_of_piecewise_const hpc).2]
    simp only [PiecewiseConstantOn.integ']
    rw [PiecewiseConstantOn.integ_const' hconst]
    by_cases! h' : ↑⌊x⌋₊ < x
    . suffices constant_value_on f (Ioc ⌊x⌋₊ x) = 0 by
        rw [this]; simp
      simp; apply ConstantOn.const_eq
      . simp; exact h'
      . exact h0
    . suffices (Ioc ⌊x⌋₊ x).length = 0 by rw [this]; simp
      simp [BoundedInterval.a, BoundedInterval.b]
      exact h'


end Chapter11
