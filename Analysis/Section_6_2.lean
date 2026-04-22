import Mathlib.Tactic
import Analysis.Section_5_5
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.2: The extended real number system

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some API for Mathlib's extended reals {name}`EReal`, particularly with regard to the supremum
  operation {name}`sSup` and infimum operation {name}`sInf`.

-/

open EReal

/-- Definition 6.2.1 -/
theorem EReal.def (x:EReal) : (∃ (y:Real), y = x) ∨ x = ⊤ ∨ x = ⊥ := by
  revert x
  simp [EReal.forall]

theorem EReal.real_neq_infty (x:ℝ) : (x:EReal) ≠ ⊤ := coe_ne_top _

theorem EReal.real_neq_neg_infty (x:ℝ) : (x:EReal) ≠ ⊥ := coe_ne_bot _

theorem EReal.infty_neq_neg_infty : (⊤:EReal) ≠ (⊥:EReal) := add_top_iff_ne_bot.mp rfl

abbrev EReal.IsFinite (x:EReal) : Prop := ∃ (y:Real), y = x

abbrev EReal.IsInfinite (x:EReal) : Prop := x = ⊤ ∨ x = ⊥

theorem EReal.infinite_iff_not_finite (x:EReal): x.IsInfinite ↔ ¬ x.IsFinite := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp [IsFinite, IsInfinite]

/-- Definition 6.2.2 (Negation of extended reals) -/
theorem EReal.neg_of_real (x:Real) : -(x:EReal) = (-x:ℝ) := rfl

#check EReal.neg_top
#check EReal.neg_bot

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.le_iff (x y:EReal) :
    x ≤ y ↔ (∃ (x' y':Real), x = x' ∧ y = y' ∧ x' ≤ y') ∨ y = ⊤ ∨ x = ⊥ := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y <;> simp <;> tauto

/-- Definition 6.2.3 (Ordering of extended reals) -/
theorem EReal.lt_iff (x y:EReal) : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

#check EReal.coe_lt_coe_iff
#check EReal.coe_le_coe

/-- Examples 6.2.4 -/
example : (3:EReal) ≤ (5:EReal) := by rw [le_iff]; left; use (3:ℝ), (5:ℝ); norm_cast


/-- Examples 6.2.4 -/
example : (3:EReal) < ⊤ := by rw [lt_iff]; exact ⟨le_top, real_neq_infty 3⟩


/-- Examples 6.2.4 -/
example : (⊥:EReal) < ⊤ := bot_lt_top


/-- Examples 6.2.4 -/
example : ¬ (3:EReal) ≤ ⊥ := by
  by_contra h
  simp at h
  exact real_neq_neg_infty 3 h

#check instCompleteLinearOrderEReal

/-- Proposition 6.2.5(a) / Exercise 6.2.1 -/
theorem EReal.refl (x:EReal) : x ≤ x := by
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def x <;> simp

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.trichotomy (x y:EReal) : x < y ∨ x = y ∨ x > y := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> try grind

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_eq (x y:EReal) : ¬ (x < y ∧ x = y) := by
  intro ⟨hxy, heq⟩
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> try grind

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_gt_and_eq (x y:EReal) : ¬ (x > y ∧ x = y) := by
  intro ⟨hxy, heq⟩
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> try grind

/-- Proposition 6.2.5(b) / Exercise 6.2.1 -/
theorem EReal.not_lt_and_gt (x y:EReal) : ¬ (x < y ∧ x > y) := by
  intro ⟨hxy, heq⟩
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> try grind

/-- Proposition 6.2.5(c) / Exercise 6.2.1 -/
theorem EReal.trans {x y z:EReal} (hxy : x ≤ y) (hyz: y ≤ z) : x ≤ z := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> obtain ⟨ z', rfl ⟩ | rfl | rfl := EReal.def z
    <;> try grind

/-- Proposition 6.2.5(d) / Exercise 6.2.1 -/
theorem EReal.neg_of_lt {x y:EReal} (hxy : x ≤ y): -y ≤ -x := by
  obtain ⟨ x', rfl ⟩ | rfl | rfl := EReal.def x
    <;> obtain ⟨ y', rfl ⟩ | rfl | rfl := EReal.def y
    <;> try grind
  · simp_all
  · simp_all
  · simp_all
    norm_cast
    have this := (EReal.le_iff ((-y'):ℝ) ⊤).mpr; simp at this
    exact_mod_cast this
  · simp_all



/-- Definition 6.2.6 -/
theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = sSup E := calc
  _ = sSup
      ((fun (x:WithTop ℝ) ↦ (x:WithBot (WithTop ℝ))) '' ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E)) := by
    rw [←Set.image_comp]; congr
  _ = sSup ((fun (x:ℝ) ↦ (x:WithTop ℝ)) '' E) := by
    symm; apply WithBot.coe_sSup'
    . simp [hnon]
    exact WithTop.coe_mono.map_bddAbove hbound
  _ = ((sSup E : ℝ) : WithTop ℝ) := by congr; symm; exact WithTop.coe_sSup' hbound
  _ = _ := rfl

/-- Definition 6.2.6 -/
theorem EReal.sup_of_unbounded_nonempty {E: Set ℝ} (hunbound: ¬ BddAbove E) (hnon: E.Nonempty) :
    sSup ((fun (x:ℝ) ↦ (x:EReal)) '' E) = ⊤ := by
  erw [sSup_eq_top]
  intro b hb
  obtain ⟨ y, rfl ⟩ | rfl | rfl := EReal.def b
  . simp; contrapose! hunbound; exact ⟨ y, hunbound ⟩
  . exact absurd hb (lt_irrefl _)
  exact ⟨↑hnon.choose, Set.mem_image_of_mem _ hnon.choose_spec, bot_lt_coe _⟩

/-- Definition 6.2.6 -/
theorem EReal.sup_of_empty : sSup (∅:Set EReal) = ⊥ := sSup_empty

/-- Definition 6.2.6 -/
theorem EReal.sup_of_infty_mem {E: Set EReal} (hE: ⊤ ∈ E) : sSup E = ⊤ := csSup_eq_top_of_top_mem hE

/-- Definition 6.2.6 -/
theorem EReal.sup_of_neg_infty_mem {E: Set EReal} : sSup E = sSup (E \ {⊥}) := (sSup_diff_singleton_bot _).symm

theorem EReal.inf_eq_neg_sup (E: Set EReal) : sInf E = - sSup (-E) := by
  simp_rw [←isGLB_iff_sInf_eq, isGLB_iff_le_iff, EReal.le_neg]
  intro b
  simp [lowerBounds]

/-- Example 6.2.7 -/
abbrev Example_6_2_7 : Set EReal := { x | ∃ n:ℕ, x = -((n+1):EReal)} ∪ {⊥}

example : sSup Example_6_2_7 = -1 := by
  rw [EReal.sup_of_neg_infty_mem]
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use (-1)
    simp_all
    constructor
    · use 0; simp
    · push_neg
      exact EReal.real_neq_infty 1
  · have hlt : ∀ N : ℕ, -((N+1):EReal) ≤ -1 := by
      intro n
      induction' n with k ih
      · simp
      · norm_cast at ih ⊢
        have : -((k+1+1):ℝ) ≤ -((k+1):ℝ) := by linarith
        have := EReal.coe_le_coe this
        push_cast at this ih ⊢
        exact EReal.trans this ih
    intro a ha
    obtain ⟨hin, hnotbot⟩ := ha
    rcases hin with ⟨N, hN⟩ | hbot
    · specialize hlt N
      rw [hN]
      exact hlt
    · exact absurd hbot hnotbot
  · intro w hw
    use (-1)
    constructor
    · simp
      constructor
      · use 0; simp
      · push_neg; exact EReal.real_neq_infty 1
    · exact hw

example : sInf Example_6_2_7 = ⊥ := by
  rw [EReal.inf_eq_neg_sup]
  suffices alternatively : sSup (-Example_6_2_7) = ⊤ by
    rw [← neg_top]
    exact neg_inj.mpr alternatively
  have hinf : ⊤ ∈ (-Example_6_2_7) := by simp
  exact sup_of_infty_mem hinf

/-- Example 6.2.8 -/
abbrev Example_6_2_8 : Set EReal := { x | ∃ n:ℕ, x = (1 - (10:ℝ)^(-(n:ℤ)-1):Real)}

lemma example628gt : ∀ N : ℕ,  (1 - (10:ℝ)^(-(N:ℤ)-1):Real) ≥ 0.9 := by
    intro n
    induction' n with k ih
    · norm_num
    · have : (-((k + 1):ℕ):ℤ) - 1 ≤ (-(k:ℕ):ℤ) - 1 := by grind
      --have : (10:ℝ) ^ ((-((k + 1):ℕ):ℤ) - 1) ≤ (10:ℝ) ^ (-(k:ℕ):ℤ) := by apply?
      have := zpow_le_zpow_right₀ (a:=(10:ℝ)) (by linarith) this
      grind

lemma example628btw' (w : ℝ) (hlt : w < 1) (hge : 0.9 ≤ w) :
    ∃ N : ℕ, (1 - (10 : ℝ) ^ (-(N : ℤ) - 1)) > w := by
  -- 1. Identify that (1 - w) is a positive distance
  have h_dist : 0 < 1 - w := sub_pos.mpr hlt

  -- 2. Use the Archimedean property for powers: (1/10)^m approaches 0
  -- We find an 'm' such that (1/10)^m < 1 - w
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one h_dist (by norm_num : |(1/10 : ℝ)| < 1)

  -- 3. We need N such that N + 1 = m.
  -- Since 1 - w ≤ 0.1 (from w ≥ 0.9) and (1/10)^0 = 1, m cannot be 0.
  have hm_ne_zero : m ≠ 0 := by
    intro h_zero
    rw [h_zero, pow_zero] at hm
    linarith -- Contradiction: 1 < 1 - w and w ≥ 0.9

  -- Since m ≠ 0, there exists N such that m = N + 1
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero

  -- 4. Provide N as the witness
  use N

  -- 5. Prove (1 - 10^(-N-1)) > w
  -- This is equivalent to showing 1 - w > 10^(-N-1)
  rw [gt_iff_lt]

  have h_exp_eq : (10 : ℝ) ^ (-(N : ℤ) - 1) = (1 / 10) ^ m := by
    rw [hN]
    -- Bridge -(N)-1 to -(N+1)
    have h_exp : -(N : ℤ) - 1 = -((N + 1) : ℕ) := by
      push_cast
      ring
    rw [h_exp]
    -- Use zpow_neg to get the inverse
    rw [zpow_neg]
    -- Use zpow_natCast to turn the integer power into a natural power
    rw [zpow_natCast]
    -- Now we have (10 ^ (N+1))⁻¹ = (1 / 10) ^ (N+1)
    -- This can be solved by showing (1/10) is 10⁻¹
    rw [one_div, inv_pow]

  -- Final Inequality manipulation
  rw [h_exp_eq]
  -- We have: w < 1 - (1/10)^m
  -- We know: (1/10)^m < 1 - w (this is hm)
  linarith

example : sInf Example_6_2_8 = (0.9:ℝ) := by
  rw [EReal.inf_eq_neg_sup]
  suffices alternatively : sSup (-Example_6_2_8) = (-0.9:ℝ) by
    exact neg_eq_iff_eq_neg.mpr alternatively
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use (-(1 - (10:ℝ)^(-(1:ℤ)-1):Real))
    simp_all
    use 1
    simp
  · intro a ha
    have hnegmem : (-a) ∈ Example_6_2_8 := by exact Set.mem_setOf.mpr ha
    obtain ⟨n, hn⟩ := hnegmem
    have hgt := example628gt n
    have := EReal.coe_le_coe hgt
    rw [← hn] at this
    replace this := EReal.neg_of_lt this
    rw [neg_neg] at this
    exact_mod_cast this
  · intro w hw
    use (-(1 - (10:ℝ)^(-(0:ℤ)-1):Real))
    constructor
    · use 0
      simp_all
    · norm_num at *
      norm_cast

example : sSup Example_6_2_8 = 1 := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use (1 - (10:ℝ)^(-(1:ℤ)-1):Real)
    simp
    use 1
    simp
  · intro a ha
    obtain ⟨N, hN⟩ := ha
    simp at hN
    have : (10:ℝ) ^ (-(N:ℤ) -1) > 0 := by positivity
    rw [hN]
    have : 1 - (10:ℝ) ^ (-(N:ℤ) -1) ≤ 1 := by grind
    exact_mod_cast this
  · intro w hw
    by_cases h' : w < (0.9:ℝ)
    · use (1 - (10:ℝ)^(-(0:ℤ)-1):Real)
      constructor
      · simp
        use 0
        simp_all
      · have hgt := example628gt 0
        norm_num at *
        exact h'
    · push_neg at h'
      obtain ⟨ w', rfl ⟩ | rfl | rfl := EReal.def w
      · have hlt1 := EReal.coe_lt_coe_iff.mp hw
        have hgt09 := EReal.coe_le_coe_iff.mp h'
        obtain ⟨N, hN⟩ := example628btw' w' hlt1 hgt09
        use (1 - (10:ℝ)^(-(N:ℤ)-1):Real)
        constructor
        · use N
        · norm_cast
      · exact absurd hw not_top_lt
      · use (1 - (10:ℝ)^(-(1:ℤ)-1):Real)
        simp
        constructor
        · use 1; simp
        · exact bot_lt_iff_ne_bot.mpr (EReal.real_neq_neg_infty _)

/-- Example 6.2.9 -/
abbrev Example_6_2_9 : Set EReal := { x | ∃ n:ℕ, x = n+1}

lemma example629gt : ∀ N : ℕ, N + 1 ≥ 1 := by
  intro n; linarith

example : sInf Example_6_2_9 = 1 := by
  rw [EReal.inf_eq_neg_sup]
  suffices alternatively : sSup (-Example_6_2_9) = -1 by
    exact neg_eq_iff_eq_neg.mpr alternatively
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use -1
    use 0
    simp_all
  · intro a ha
    change -a ∈ Example_6_2_9 at ha
    obtain ⟨n, hn⟩ := ha
    have hgt := example629gt n
    suffices alternatively : -a ≥ 1 by exact EReal.le_neg_of_le_neg alternatively
    rw [hn]
    exact_mod_cast hgt
  · intro w hw
    use -1
    constructor
    · use 0
      simp_all
    · exact hw

example : sSup Example_6_2_9 = ⊤ := by
  let ex629 := { x : ℝ | ∃ n:ℕ, x = n + 1}
  have hsetR : Example_6_2_9 = ((fun (x:ℝ) ↦ (x:EReal)) '' ex629) := by
    ext y
    constructor
    · intro hy
      unfold Example_6_2_9 at hy
      unfold ex629
      simp at hy ⊢
      obtain ⟨n, hn⟩ := hy
      use n
      symm at hn
      exact_mod_cast hn
    · intro hy
      unfold ex629 at hy
      unfold Example_6_2_9
      simp at hy ⊢
      obtain ⟨n, hn⟩ := hy
      use n
      symm at hn
      exact_mod_cast hn
  have hunbound : ¬ (BddAbove ex629) := by
    intro hbd
    obtain ⟨Bd, hBd⟩ := hbd
    have hflr : ⌊Bd⌋ + 1 > Bd := by exact Int.lt_floor_add_one Bd
    have hmem : ((⌊Bd⌋ + 1):ℝ) ∈ ex629 := by
      by_cases hBd0 : Bd ≥ 0
      · use Int.toNat ⌊Bd⌋
        simp
        have hpos : 0 ≤ ⌊Bd⌋ := Int.floor_nonneg.mpr hBd0
        norm_cast
        exact Int.eq_natCast_toNat.mpr hpos
      · push_neg at hBd0
        have hone : 1 ∈ ex629 := by
          unfold ex629
          simp
        specialize hBd hone
        linarith
    specialize hBd hmem
    linarith
  have hnon : ex629.Nonempty := by
    use 1
    unfold ex629
    simp
  have hsupofunbound := EReal.sup_of_unbounded_nonempty hunbound hnon
  rwa [hsetR]

example : sInf (∅ : Set EReal) = ⊤ := by
  exact sInf_empty

example (E: Set EReal) : sSup E < sInf E ↔ E = ∅ := by
  constructor
  · intro hsupinf
    by_contra! h'
    obtain ⟨x, hx⟩ := h'
    have hlt : x ≤ sSup E := by exact le_sSup_iff.mpr fun b a ↦ a hx
    have hgt : sInf E ≤ sSup E := by exact sInf_le_of_le hx hlt
    grind
  · intro hempty
    rw [hempty]
    simp

/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_le_sup (E: Set EReal) {x:EReal} (hx: x ∈ E) : x ≤ sSup E := by
 -- theorem EReal.sup_of_bounded_nonempty {E: Set ℝ} (hbound: BddAbove E) (hnon: E.Nonempty) :
 exact le_sSup_iff.mpr fun b a ↦ a hx


/-- Theorem 6.2.11 (a) / Exercise 6.2.2 -/
theorem EReal.mem_ge_inf (E: Set EReal) {x:EReal} (hx: x ∈ E) : sInf E ≤ x := by
  exact sInf_le_iff.mpr fun b a ↦ a hx

/-- Theorem 6.2.11 (b) / Exercise 6.2.2 -/
theorem EReal.sup_le_upper (E: Set EReal) {M:EReal} (hM: M ∈ upperBounds E) : sSup E ≤ M := by
  exact sSup_le_iff.mpr hM

/-- Theorem 6.2.11 (c) / Exercise 6.2.2 -/
theorem EReal.inf_ge_lower (E: Set EReal) {M:EReal} (hM: M ∈ lowerBounds E) : sInf E ≥ M := by sorry

#check isLUB_iff_sSup_eq
#check isGLB_iff_sInf_eq

/-- Not in textbook: identify the Chapter 5 extended reals with the Mathlib {name}`EReal`.
-/
noncomputable abbrev Chapter5.ExtendedReal.toEReal (x:ExtendedReal) : EReal := match x with
  | real r => ((Real.equivR r):EReal)
  | infty => ⊤
  | neg_infty => ⊥

theorem Chapter5.ExtendedReal.coe_inj : Function.Injective toEReal := by
  intro x y heq
  cases x <;> cases y <;> simp [toEReal] at heq ⊢
  · exact absurd heq EReal.infty_neq_neg_infty.symm
  · exact Real.equivR.injective heq
  · exact absurd heq EReal.infty_neq_neg_infty


theorem Chapter5.ExtendedReal.coe_surj : Function.Surjective toEReal := by
  intro y
  obtain ⟨y', rfl⟩ | rfl | rfl := EReal.def y
  · have := Real.equivR.surjective y'
    obtain ⟨x, hx⟩ := this
    use x
    simp_all
  · use infty
  · use neg_infty

noncomputable abbrev Chapter5.ExtendedReal.equivEReal : Chapter5.ExtendedReal ≃ EReal :=
  Equiv.ofBijective toEReal ⟨Chapter5.ExtendedReal.coe_inj, Chapter5.ExtendedReal.coe_surj⟩
