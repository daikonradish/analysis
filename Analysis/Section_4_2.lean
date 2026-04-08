import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.2

This file is a translation of Section 4.2 of Analysis I to Lean 4.
All numbering refers to the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.2" rationals, `Section_4_2.Rat`, as formal quotients `a // b` of
  integers `a b:ℤ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_2.PreRat`, which consists of formal quotients without any equivalence imposed.)

- Field operations and order on these rationals, as well as an embedding of {lean}`ℕ` and {lean}`ℤ`.

- Equivalence with the Mathlib rationals {name}`_root_.Rat` (or {lean}`ℚ`), which we will use going forward.

Note: here (and in the sequel) we use Mathlib's natural numbers {lean}`ℕ` and integers {lean}`ℤ` rather than
the Chapter 2 natural numbers and Section 4.1 integers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_2

structure PreRat where
  numerator : ℤ
  denominator : ℤ
  nonzero : denominator ≠ 0

/-- Exercise 4.2.1 -/
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := {
    refl  := by
      intro x; rfl
    symm  := by
      intro x y hxy
      exact hxy.symm
    trans := by
      intro ⟨x₁, x₂, hx⟩ ⟨y₁, y₂, hy⟩ ⟨z₁, z₂, hz⟩ hxy hyz
      dsimp at hxy hyz ⊢
      have h1 := congrArg (· * z₂) hxy; dsimp at h1
      have h2 := congrArg (· * x₂) hyz; dsimp at h2
      have hrw : y₁ * x₂ * z₂ = y₁ * z₂ * x₂ := by ring
      rw [hrw] at h1
      rw [h2] at h1
      have hc : y₂ * (x₁ * z₂) = y₂ * (z₁ * x₂) := by
        linarith only [h1]
      exact mul_left_cancel₀ hy hc
    }

@[simp]
theorem PreRat.eq (a b c d:ℤ) (hb: b ≠ 0) (hd: d ≠ 0) :
    (⟨ a,b,hb ⟩: PreRat) ≈ ⟨ c,d,hd ⟩ ↔ a * d = c * b := by rfl

abbrev Rat := Quotient PreRat.instSetoid

/-- We give division a "junk" value of 0//1 if the denominator is zero -/
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨ a,b,h ⟩ else ⟨ 0, 1, by decide ⟩)

infix:100 " // " => Rat.formalDiv

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0): a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv, hb, hd, Quotient.eq, PreRat.instSetoid]

/-- Definition 4.2.1 (Rationals) -/
theorem Rat.eq_diff (n:Rat) : ∃ a b, b ≠ 0 ∧ n = a // b := by
  apply Quotient.ind _ n; intro ⟨ a, b, h ⟩
  refine ⟨ a, b, h, ?_ ⟩
  simp [formalDiv, h]

/--
  Decidability of equality. Hint: modify the proof of {lean}`DecidableEq Int` from the previous
  section. However, because formal division handles the case of zero denominator separately, it
  may be more convenient to avoid that operation and work directly with the {name}`Quotient` API.

-/
instance Rat.decidableEq : DecidableEq Rat := by
  intro a b
  have : ∀ (n : PreRat) (m : PreRat),
    Decidable (Quotient.mk PreRat.instSetoid n = Quotient.mk PreRat.instSetoid m) := by
    intro ⟨n₁, n₂, hn⟩ ⟨m₁, m₂, hm⟩
    rw [Quotient.eq]
    simp [PreRat.eq]
    exact inferInstance
  exact Quotient.recOnSubsingleton₂ a b this

/-- Lemma 4.2.3 (Addition well-defined) -/
instance Rat.add_inst : Add Rat where
  add := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*d+b*c) // (b*d)) (by
    intro ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ⟨ a', b', h1' ⟩ ⟨ c', d', h2' ⟩ h3 h4
    simp_all [Quotient.eq]
    linear_combination d * d' * h3 + b * b' * h4
  )

/-- Definition 4.2.2 (Addition of rationals) -/
theorem Rat.add_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) + (c // d) = (a*d + b*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Multiplication well-defined) -/
instance Rat.mul_inst : Mul Rat where
  mul := Quotient.lift₂ (fun ⟨ a, b, h1 ⟩ ⟨ c, d, h2 ⟩ ↦ (a*c) // (b*d)) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ ⟨c₁, c₂, hc⟩ ⟨d₁, d₂, hd⟩ hab hcd
    dsimp
    rw [PreRat.eq] at hab hcd
    refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
    · exact Int.mul_ne_zero ha hb
    · exact Int.mul_ne_zero hc hd
    · calc a₁ * b₁ * (c₂ * d₂) = (a₁ * c₂) * (b₁ * d₂) := by ring
                           _ = (c₁ * a₂) * (d₁ * b₂) := by rw [hab, hcd]
                           _ = c₁ * d₁ * (a₂ * b₂)   := by ring
  )

/-- Definition 4.2.2 (Multiplication of rationals) -/
theorem Rat.mul_eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0) :
    (a // b) * (c // d) = (a*c) // (b*d) := by
  convert Quotient.lift₂_mk _ _ _ _ <;> simp [hb, hd]

/-- Lemma 4.2.3 (Negation well-defined) -/
instance Rat.neg_inst : Neg Rat where
  neg := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ (-a) // b) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ hab
    rw [PreRat.eq] at hab
    dsimp
    refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
    · exact ha
    · exact hb
    · have h := congrArg (λ expr => -(expr)) hab; dsimp at h
      rw [Int.neg_mul, Int.neg_mul]
      exact h
  )

/-- Definition 4.2.2 (Negation of rationals) -/
theorem Rat.neg_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : - (a // b) = (-a) // b := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

/-- Embedding the integers in the rationals -/
instance Rat.instIntCast : IntCast Rat where
  intCast a := a // 1

instance Rat.instNatCast : NatCast Rat where
  natCast n := (n:ℤ) // 1

instance Rat.instOfNat {n:ℕ} : OfNat Rat n where
  ofNat := (n:ℤ) // 1

theorem Rat.coe_Int_eq (a:ℤ) : (a:Rat) = a // 1 := rfl

theorem Rat.coe_Nat_eq (n:ℕ) : (n:Rat) = n // 1 := rfl

theorem Rat.of_Nat_eq (n:ℕ) : (ofNat(n):Rat) = (ofNat(n):Nat) // 1 := rfl

/-- natCast distributes over successor -/
theorem Rat.natCast_succ (n: ℕ) : ((n + 1: ℕ): Rat) = (n: Rat) + 1 := by
  refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
  · linarith
  · linarith
  · rw [Int.mul_one, Int.mul_one, Int.mul_one, Int.mul_one, Int.one_mul]
    rw [Nat.cast_add]

/-- intCast distributes over addition -/
lemma Rat.intCast_add (a b:ℤ) : (a:Rat) + (b:Rat) = (a+b:ℤ) := by
  refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
  · linarith
  · linarith
  · repeat rw [Int.mul_one]
    rw [Int.one_mul]

/-- intCast distributes over multiplication -/
lemma Rat.intCast_mul (a b:ℤ) : (a:Rat) * (b:Rat) = (a*b:ℤ) := by
  refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
  · linarith
  · linarith
  · repeat rw [Int.mul_one]

/-- intCast commutes with negation -/
lemma Rat.intCast_neg (a:ℤ) : - (a:Rat) = (-a:ℤ) := rfl

theorem Rat.coe_Int_inj : Function.Injective (fun n:ℤ ↦ (n:Rat)) := by
  intro a b hfab
  dsimp at hfab
  change a // 1 = b // 1 at hfab
  rw [Rat.eq a b (by linarith) (by linarith)] at hfab
  repeat rw [Int.mul_one] at hfab
  exact hfab

/--
  Whereas the book leaves the inverse of 0 undefined, it is more convenient in Lean to assign a
  "junk" value to this inverse; we arbitrarily choose this junk value to be 0.
-/
instance Rat.instInv : Inv Rat where
  inv := Quotient.lift (fun ⟨ a, b, h1 ⟩ ↦ b // a) (by
    -- hint: split into the `a=0` and `a≠0` cases
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ hab
    dsimp
    rw [PreRat.eq] at hab
    by_cases ha1 : a₁ = 0
    · subst ha1
      simp at hab
      have hb1 : b₁ = 0 := hab.resolve_right ha
      subst hb1
      simp [Rat.formalDiv]
    · change a₁ ≠ 0 at ha1
      refine (Rat.eq _ _ ?h1 ?h2).mpr ?main
      · exact ha1
      · have hab0 : a₁ * b₂ ≠ 0 := Int.mul_ne_zero ha1 hb
        intro hb0
        rw [hb0] at hab
        rw [Int.zero_mul] at hab
        exact hab0 hab
      · conv at hab => lhs; rw [mul_comm]
        conv at hab => rhs; rw [mul_comm]
        exact hab.symm
)

lemma Rat.inv_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a // b)⁻¹ = b // a := by
  convert Quotient.lift_mk _ _ _ <;> simp [hb]

@[simp]
theorem Rat.inv_zero : (0:Rat)⁻¹ = 0 := rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.addGroup_inst : AddGroup Rat :=
AddGroup.ofLeftAxioms
(by
  -- this proof is written to follow the structure of the original text.
  intro x y z
  obtain ⟨ a, b, hb, rfl ⟩ := eq_diff x
  obtain ⟨ c, d, hd, rfl ⟩ := eq_diff y
  obtain ⟨ e, f, hf, rfl ⟩ := eq_diff z
  have hbd : b*d ≠ 0 := Int.mul_ne_zero hb hd     -- can also use `observe hbd : b*d ≠ 0` here
  have hdf : d*f ≠ 0 := Int.mul_ne_zero hd hf     -- can also use `observe hdf : d*f ≠ 0` here
  have hbdf : b*d*f ≠ 0 := Int.mul_ne_zero hbd hf -- can also use `observe hbdf : b*d*f ≠ 0` here
  rw [add_eq _ _ hb hd, add_eq _ _ hbd hf, add_eq _ _ hd hf,
      add_eq _ _ hb hdf, ←mul_assoc b, eq _ _ hbdf hbdf]
  ring)
(by
  intro a
  obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
  change 0 // 1 + a₁ // a₂ = a₁ // a₂
  rw [Rat.add_eq _ _ one_ne_zero ha]
  rw [Int.zero_mul, Int.zero_add]
  rw [Int.one_mul, Int.one_mul])
(by
  intro a
  obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
  rw [Rat.neg_eq _ ha]
  rw [Rat.add_eq _ _ ha ha]
  have fact : (-a₁ * a₂ + a₂ * a₁) = 0 := by linarith
  rw [fact]
  change 0 // (a₂ * a₂) = 0 // 1
  refine (Rat.eq _ _ ?hl ?hr).mpr ?main
  · intro haa
    apply ha
    exact (mul_eq_zero_iff_right ha).mp haa
  · linarith
  · simp
  )

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instAddCommGroup : AddCommGroup Rat where
  add_comm := by
    intro a b
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    conv => lhs; rw [Rat.add_eq _ _ ha hb]
    conv => rhs; rw [Rat.add_eq _ _ hb ha]
    have fact1 : a₂ * b₂ = b₂ * a₂ := by linarith
    have fact2 : a₁ * b₂ + a₂ * b₁ = b₁ * a₂ + b₂ * a₁ := by linarith
    rw [fact1, fact2]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommMonoid : CommMonoid Rat where
  mul_comm := by
    intro a b
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    conv => lhs; rw [Rat.mul_eq _ _ ha hb]
    conv => rhs; rw [Rat.mul_eq _ _ hb ha]
    have fact1 : a₁ * b₁ = b₁ * a₁ := by linarith
    have fact2 : a₂ * b₂ = b₂ * a₂ := by linarith
    rw [fact1, fact2]
  mul_assoc := by
    intro a b c
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    obtain ⟨c₁, c₂, hc, rfl⟩ := Rat.eq_diff c
    conv => lhs; rw [Rat.mul_eq _ _ ha hb]
    conv => lhs; rw [Rat.mul_eq _ _ (mul_ne_zero ha hb) hc]
    conv => rhs; rw [Rat.mul_eq _ _ hb hc]
    conv => rhs; rw [Rat.mul_eq _ _ ha (mul_ne_zero hb hc)]
    have fact1 : (a₁ * b₁ * c₁) = (a₁ * (b₁ * c₁)) := by ring
    have fact2 : (a₂ * b₂ * c₂) = (a₂ * (b₂ * c₂)) := by ring
    rw [fact1, fact2]
  one_mul := by
    intro a
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    change 1 // 1 * a₁ // a₂ = a₁ // a₂
    conv => lhs; rw [Rat.mul_eq _ _ (by linarith) ha]
    rw [Int.one_mul, Int.one_mul]
  mul_one := by
    intro a
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    change a₁ // a₂ * 1 // 1 = a₁ // a₂
    conv => lhs; rw [Rat.mul_eq _ _ ha (by linarith)]
    rw [Int.mul_one, Int.mul_one]

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instCommRing : CommRing Rat where
  left_distrib := by
    intro a b c
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    obtain ⟨c₁, c₂, hc, rfl⟩ := Rat.eq_diff c
    conv =>
      lhs
      rw [Rat.add_eq _ _ hb hc]
      rw [Rat.mul_eq _ _ ha (mul_ne_zero hb hc)]
    conv =>
      rhs
      rw [Rat.mul_eq _ _ ha hb]
      rw [Rat.mul_eq _ _ ha hc]
      rw [Rat.add_eq _ _ (mul_ne_zero ha hb) (mul_ne_zero ha hc)]
    refine (Rat.eq _ _ ?_ ?_).mpr ?_
    · exact mul_ne_zero ha (mul_ne_zero hb hc)
    · apply mul_ne_zero
      · exact mul_ne_zero ha hb
      · exact mul_ne_zero ha hc
    · ring
  right_distrib := by
    intro a b c
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    obtain ⟨c₁, c₂, hc, rfl⟩ := Rat.eq_diff c
    conv =>
      lhs
      rw [Rat.add_eq _ _ ha hb]
      rw [Rat.mul_eq _ _ (mul_ne_zero ha hb) hc]
    conv =>
      rhs
      rw [Rat.mul_eq _ _ ha hc]
      rw [Rat.mul_eq _ _ hb hc]
      rw [Rat.add_eq _ _ (mul_ne_zero ha hc) (mul_ne_zero hb hc)]
    refine (Rat.eq _ _ ?_ ?_).mpr ?_
    · apply mul_ne_zero
      · exact mul_ne_zero ha hb
      · exact hc
    · apply mul_ne_zero
      · exact mul_ne_zero ha hc
      · exact mul_ne_zero hb hc
    · ring
  zero_mul := by
    intro a
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    change 0 // 1 * a₁ // a₂ = 0 // 1
    rw [Rat.mul_eq _ _ (by linarith) ha]
    refine (Rat.eq _ _ ?_ ?_).mpr ?_
    · rw [Int.one_mul]
      exact ha
    · linarith
    · ring
  mul_zero := by
    intro a
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    change a₁ // a₂ * 0 // 1 = 0 // 1
    rw [Rat.mul_eq _ _ ha (by linarith)]
    refine (Rat.eq _ _ ?_ ?_).mpr ?_
    · rw [Int.mul_one]
      exact ha
    · linarith
    · ring
  mul_assoc := by
    intro a b c
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
    obtain ⟨c₁, c₂, hc, rfl⟩ := Rat.eq_diff c
    conv =>
      lhs
      rw [Rat.mul_eq _ _ ha hb]
      rw [Rat.mul_eq _ _ (mul_ne_zero ha hb) hc]
    conv =>
      rhs
      rw [Rat.mul_eq _ _ hb hc]
      rw [Rat.mul_eq _ _ ha (mul_ne_zero hb hc)]
    have fact1 : (a₁ * b₁ * c₁) = (a₁ * (b₁ * c₁)) := by ring
    have fact2 : (a₂ * b₂ * c₂) = (a₂ * (b₂ * c₂)) := by ring
    rw [fact1, fact2]
  -- Usually CommRing will generate a natCast instance and a proof for this.
  -- However, we are using a custom natCast for which `natCast_succ` cannot
  -- be proven automatically by `rfl`. Luckily we have proven it already.
  natCast_succ := natCast_succ

instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den

theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := by
  intro ⟨n₁, n₂, hn, hnr⟩ ⟨m₁, m₂, hm, hmr⟩ hnm
  change n₁ // n₂ = m₁ // m₂ at hnm
  simp
  rw [Rat.eq _ _ (Nat.cast_ne_zero.mpr hn) (Nat.cast_ne_zero.mpr hm)] at hnm
  -- 1. Prove n₂ = m₂ by looking at the absolute values
  have h_abs : n₁.natAbs * m₂ = m₁.natAbs * n₂ := by
    -- 'zify' at hnm would be the dream, but let's do it manually via natAbs
    replace hnm := congr_arg Int.natAbs hnm
    simpa [Int.natAbs_mul] using hnm
  -- 2. Use the coprime property (these lemmas are very stable)
  have h_n2_dvd_m2 : n₂ ∣ m₂ :=
    hnr.symm.dvd_of_dvd_mul_left (h_abs ▸ dvd_mul_left n₂ m₁.natAbs)
  have h_m2_dvd_n2 : m₂ ∣ n₂ :=
    hmr.symm.dvd_of_dvd_mul_left (h_abs.symm ▸ dvd_mul_left m₂ n₁.natAbs)
  have h2 : n₂ = m₂ := Nat.dvd_antisymm h_n2_dvd_m2 h_m2_dvd_n2
  constructor
  · rw [h2] at hnm
    -- Use a generic cancellation tactic
    exact Int.eq_of_mul_eq_mul_right (Int.ofNat_ne_zero.mpr hm) hnm
  · exact h2

theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := by
  set q := (a/b:ℚ)
  set num :ℤ := q.num
  set den :ℤ := (q.den:ℤ)
  have hden : den ≠ 0 := by simp [den, q.den_nz]
  change num // den = a // b
  rw [eq _ _ hden hb]
  qify
  have hq : num / den = q := Rat.num_div_den q
  rwa [div_eq_div_iff] at hq <;> simp [hden, hb]

/-- Default definition of division -/
instance Rat.instDivInvMonoid : DivInvMonoid Rat where

theorem Rat.div_eq (q r:Rat) : q/r = q * r⁻¹ := by rfl

/-- Proposition 4.2.4 (laws of algebra) / Exercise 4.2.3 -/
instance Rat.instField : Field Rat where
  exists_pair_ne := by
    use 0 // 1
    use 1 // 1
    intro h
    rw [@Rat.eq 0 1 _ _ (by linarith) (by linarith)] at h
    norm_num at h
  mul_inv_cancel := by
    intro a h0
    obtain ⟨a₁, a₂, ha0₂, rfl⟩ := Rat.eq_diff a
    have ha0₁ : a₁ ≠ 0 := by
      intro ha
      apply h0
      change a₁ // a₂ = 0 // 1
      rw [@Rat.eq _ _ _ _ ha0₂ (by linarith)]
      rw [ha]
      norm_num
    rw [@Rat.inv_eq _ _ ha0₂]
    rw [@Rat.mul_eq _ _ _ _ ha0₂ ha0₁]
    change (a₁ * a₂) // (a₂ * a₁) = 1 // 1
    rw [@Rat.eq _ _ _ _ (mul_ne_zero ha0₂ ha0₁) (by linarith)]
    norm_num
    ring
  inv_zero := rfl
  ratCast_def := by
    intro q
    set num := q.num
    set den := q.den
    have hden : (den:ℤ) ≠ 0 := by simp [den, q.den_nz]
    rw [← Rat.num_div_den q]
    convert coe_Rat_eq _ hden
    rw [coe_Int_eq, coe_Nat_eq, div_eq, inv_eq, mul_eq, eq] <;> simp [num, den, q.den_nz]
  qsmul := _
  nnqsmul := _

example : (3//4) / (5//6) = 9 // 10 := by
  rw [Rat.div_eq]
  rw [@Rat.inv_eq 5 6 (by linarith)]
  rw [@Rat.mul_eq 3 6 4 5 (by linarith) (by linarith)]
  norm_num
  rw [@Rat.eq 18 9 20 10 (by linarith) (by linarith)]
  norm_num

/-- Definition of subtraction -/
theorem Rat.sub_eq (a b:Rat) : a - b = a + (-b) := by rfl

def Rat.coe_int_hom : ℤ →+* Rat where
  toFun n := (n:Rat)
  map_zero' := rfl
  map_one'  := rfl
  map_add'  := by
    intro x y
    qify
  map_mul'  := by
    intro x y
    qify

/-- Definition 4.2.6 (positivity) -/
def Rat.isPos (q:Rat) : Prop := ∃ a b:ℤ, a > 0 ∧ b > 0 ∧ q = a/b

/-- Definition 4.2.6 (negativity) -/
def Rat.isNeg (q:Rat) : Prop := ∃ r:Rat, r.isPos ∧ q = -r

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.trichotomous (x:Rat) : x = 0 ∨ x.isPos ∨ x.isNeg := by
  obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff x
  rcases Int.lt_trichotomy a₁ 0 with (hlt₁ | heq₁ | hgt₁)
  · -- start wiht hlt₁ : a₁ < 0
    rcases Int.lt_trichotomy a₂ 0 with (hlt₂ | heq₂ | hgt₂)
    · have hlt₁' : 0 < (-a₁) := by exact Int.neg_pos_of_neg hlt₁
      have hlt₂' : 0 < (-a₂) := by exact Int.neg_pos_of_neg hlt₂
      right; left;
      use (-a₁), (-a₂)
      constructor
      · exact hlt₁'
      · constructor
        · exact hlt₂'
        · change a₁ // a₂ = ((-a₁) // 1) / ((-a₂) // 1)
          rw [Rat.div_eq]
          rw [Rat.inv_eq (-a₂) (by linarith)]
          rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)]
          rw [@Rat.eq _ _ _ _ ha (by linarith)]
          norm_num
    · exact absurd heq₂ ha
    · right; right
      have hlt₁' : 0 < (-a₁) := by exact Int.neg_pos_of_neg hlt₁
      rw [Rat.isNeg]
      use (-a₁) // a₂
      constructor
      · use (-a₁), a₂
        constructor
        · exact hlt₁'
        · constructor
          · exact hgt₂
          · change (-a₁) // a₂ = ((-a₁) // 1) / (a₂ // 1)
            rw [Rat.div_eq]
            rw [Rat.inv_eq (a₂) (by linarith)]
            rw [@Rat.mul_eq _ _ _ _ (by linarith) ha]
            rw [@Rat.eq _ _ _ _ ha (by linarith)]
            norm_num
      · rw [Rat.neg_eq _ ha]
        have fact : (- - a₁) = a₁ := by exact Int.neg_neg a₁
        rw [fact]
  · left
    change a₁ // a₂ = 0 // 1
    rw [@Rat.eq _ _ _ _ ha (by linarith)]
    rw [heq₁]
    norm_num
  · rcases Int.lt_trichotomy a₂ 0 with (hlt₂ | heq₂ | hgt₂)
    · right; right
      have hlt₂' : 0 < -a₂ := by exact Int.neg_pos_of_neg hlt₂
      rw [Rat.isNeg]
      use a₁ // (-a₂)
      constructor
      · use a₁, (-a₂)
        constructor
        · exact hgt₁
        · constructor
          · exact hlt₂'
          · change a₁ // (-a₂) = (a₁ // 1) / ((-a₂) // 1)
            rw [Rat.div_eq]
            rw [Rat.inv_eq (-a₂) (by linarith)]
            rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)]
            rw [@Rat.eq _ _ _ _ (by linarith) (by linarith)]
            norm_num
      · rw [Rat.neg_eq _ (by linarith)]
        rw [@Rat.eq _ _ _ _ (by linarith) (by linarith)]
        norm_num
    · exact absurd heq₂ ha
    · right; left
      use a₁, a₂
      constructor
      · exact hgt₁
      · constructor
        · exact hgt₂
        · change a₁ // a₂ = (a₁ // 1) / (a₂ // 1)
          rw [Rat.div_eq]
          rw [Rat.inv_eq a₂ (by linarith)]
          rw [@Rat.mul_eq _ _ _ _ (by linarith) ha]
          rw [@Rat.eq _ _ _ _ ha (by linarith)]
          norm_num

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_pos (x:Rat) : ¬(x = 0 ∧ x.isPos) := by
  intro ⟨h0, hpos⟩
  rw [Rat.isPos] at hpos
  obtain ⟨x₁, x₂, ⟨hx₁, hx₂, hdiv⟩⟩ := hpos
  rw [h0] at hdiv
  change 0 // 1 = (x₁ // 1) / (x₂ // 1) at hdiv
  rw [Rat.div_eq] at hdiv
  rw [Rat.inv_eq x₂ (by linarith)] at hdiv
  rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)] at hdiv
  rw [@Rat.eq _ _ _ _ (by linarith) (by linarith)] at hdiv
  linarith

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_zero_and_neg (x:Rat) : ¬(x = 0 ∧ x.isNeg) := by
  intro ⟨h0, hneg⟩
  rw [Rat.isNeg] at hneg
  obtain ⟨r, ⟨hrpos, hreq⟩⟩ := hneg
  obtain ⟨x₁, x₂, ⟨hx₁, hx₂, hdiv⟩⟩ := hrpos
  rw [h0] at hreq
  norm_num at hreq
  rw [hreq] at hdiv
  change 0 // 1 = (x₁ // 1) / (x₂ // 1) at hdiv
  rw [Rat.div_eq] at hdiv
  rw [Rat.inv_eq x₂ (by linarith)] at hdiv
  rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)] at hdiv
  rw [@Rat.eq _ _ _ _ (by linarith) (by linarith)] at hdiv
  linarith

/-- Lemma 4.2.7 (trichotomy of rationals) / Exercise 4.2.4 -/
theorem Rat.not_pos_and_neg (x:Rat) : ¬(x.isPos ∧ x.isNeg) := by
  intro ⟨hpos, hneg⟩
  rw [Rat.isPos] at hpos
  rw [Rat.isNeg] at hneg
  obtain ⟨x₁, x₂, ⟨hx₁, hx₂, hdiv⟩⟩ := hpos
  obtain ⟨r, ⟨hrpos, hreq⟩⟩ := hneg
  obtain ⟨y₁, y₂, ⟨hy₁, hy₂, hydiv⟩⟩ := hrpos
  rw [hdiv, hydiv] at hreq
  change (x₁ // 1) / (x₂ // 1) = -((y₁ // 1) / (y₂ // 1)) at hreq
  conv at hreq =>
    lhs
    rw [Rat.div_eq]
    rw [Rat.inv_eq _ (by linarith)]
    rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)]
  conv at hreq =>
    rhs
    rw [Rat.div_eq]
    rw [Rat.inv_eq _ (by linarith)]
    rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)]
    rw [Rat.neg_eq _ (by linarith)]
  rw [@Rat.eq (x₁ * 1) _ (1 * x₂) _ (by linarith) (by linarith)] at hreq
  norm_num at hreq
  nlinarith

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLT : LT Rat where
  lt x y := (x-y).isNeg

/-- Definition 4.2.8 (Ordering of the rationals) -/
instance Rat.instLE : LE Rat where
  le x y := (x < y) ∨ (x = y)

theorem Rat.lt_iff (x y:Rat) : x < y ↔ (x-y).isNeg := by rfl
theorem Rat.le_iff (x y:Rat) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Rat.gt_iff (x y:Rat) : x > y ↔ (x-y).isPos := by
  constructor
  · intro hxy
    change (y - x).isNeg at hxy
    rw [Rat.isNeg] at hxy
    obtain ⟨r, ⟨hrpos, hreq⟩⟩ := hxy
    have hreq' := congrArg (λ expr => (-1) * (expr)) hreq; simp at hreq'
    rw [hreq']
    exact hrpos
  · intro hpos
    change (y - x).isNeg
    rw [Rat.isNeg]
    use x - y
    constructor
    · exact hpos
    · simp

theorem Rat.ge_iff (x y:Rat) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  constructor
  · intro hxy
    rcases hxy with (hle | heq)
    · left;  exact hle
    · right; exact heq.symm
  · rintro (hle | heq)
    · left;  exact hle
    · right; exact heq.symm

theorem Rat.div_is_div (x y : ℤ) (h : y ≠ 0) : x // y = x / y := by
  change x // y = (x // 1) / (y // 1)
  rw [Rat.div_eq]
  rw [Rat.inv_eq _ (by linarith)]
  rw [@Rat.mul_eq _ _ _ _ (by linarith) h]
  rw [Int.one_mul, Int.mul_one]

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.trichotomous' (x y:Rat) : x > y ∨ x < y ∨ x = y := by
  rcases Rat.trichotomous (x - y) with (h0 | hpos | hneg)
  · right; right
    have fact := congrArg (· +y) h0; simp at fact
    exact fact
  · left
    obtain ⟨a, b, hc⟩ := hpos
    use (a // b)
    constructor
    · use a, b
      constructor
      · exact hc.1
      · constructor
        · exact hc.2.1
        · exact Rat.div_is_div a b (by linarith)
    · rcases hc with ⟨h1, h2, h3⟩
      rw [← Rat.div_is_div a b (by linarith)] at h3
      rw [← h3]
      ring
  · right; left
    exact hneg

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_lt (x y:Rat) : ¬ (x > y ∧ x < y) := by
  intro ⟨hxgr, hygr⟩
  have hneg := (Rat.lt_iff x y).mp hygr
  have hpos := (Rat.gt_iff x y).mp hxgr
  apply Rat.not_pos_and_neg (x - y)
  exact ⟨hpos, hneg⟩

/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_gt_and_eq (x y:Rat) : ¬ (x > y ∧ x = y) := by
  intro ⟨hxgr, heq⟩
  have hpos := (Rat.gt_iff x y).mp hxgr
  have h0 := congrArg (· -y) heq; simp at h0
  apply Rat.not_zero_and_pos (x - y)
  exact ⟨h0, hpos⟩


/-- Proposition 4.2.9(a) (order trichotomy) / Exercise 4.2.5 -/
theorem Rat.not_lt_and_eq (x y:Rat) : ¬ (x < y ∧ x = y) := by
  intro ⟨hygr, heq⟩
  have hneg := (Rat.lt_iff x y).mp hygr
  have h0 := congrArg (· -y) heq; simp at h0
  apply Rat.not_zero_and_neg (x - y)
  exact ⟨h0, hneg⟩

/-- Proposition 4.2.9(b) (order is anti-symmetric) / Exercise 4.2.5 -/
theorem Rat.antisymm (x y:Rat) : x < y ↔ y > x := by
  constructor
  · intro hxy
    exact (Rat.lt_iff x y).mpr hxy
  · intro hyx
    exact (Rat.lt_iff x y).mpr hyx

theorem Rat.pos_add_pos_is_pos (x y : Rat) (hx : x.isPos) (hy : y.isPos) : (x + y).isPos := by
  obtain ⟨x₁, x₂, ⟨h0x₁, h0x₂, hxeq⟩⟩ := hx
  obtain ⟨y₁, y₂, ⟨h0y₁, h0y₂, hyeq⟩⟩ := hy
  change x = (x₁ // 1) * (1 // x₂) at hxeq
  change y = (y₁ // 1) * (1 // y₂) at hyeq
  use (x₁ * y₂ + x₂ * y₁), (x₂ * y₂)
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · rw [hxeq, hyeq]
      conv =>
        lhs
        rw [@Rat.mul_eq x₁ 1 _ _ (by linarith) (by linarith)]
        rw [@Rat.mul_eq y₁ 1 _ _ (by linarith) (by linarith)]
        rw [@Rat.add_eq _ _ _ _ (by linarith) (by linarith)]
      conv =>
        rhs
        rw [← Rat.div_is_div (x₁ * y₂ + x₂ * y₁) (x₂ * y₂) (by nlinarith)]
      simp

theorem Rat.pos_mul_pos_is_pos (x y : Rat) (hx : x.isPos) (hy : y.isPos) : (x * y).isPos := by
  obtain ⟨x₁, x₂, ⟨h0x₁, h0x₂, hxeq⟩⟩ := hx
  obtain ⟨y₁, y₂, ⟨h0y₁, h0y₂, hyeq⟩⟩ := hy
  change x = (x₁ // 1) * (1 // x₂) at hxeq
  change y = (y₁ // 1) * (1 // y₂) at hyeq
  use (x₁ * y₁), (x₂ * y₂)
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · rw [hxeq, hyeq]
      conv =>
        lhs
        rw [@Rat.mul_eq x₁ 1 _ _ (by linarith) (by linarith)]
        rw [@Rat.mul_eq y₁ 1 _ _ (by linarith) (by linarith)]
        rw [@Rat.mul_eq (x₁ * 1) (y₁ * 1) _ _ (by linarith) (by linarith)]
      conv =>
        rhs
        change ((x₁ * y₁) // 1) * (1 // (x₂ * y₂))
        rw [@Rat.mul_eq (x₁ * y₁) 1 1 _ (by linarith) (by nlinarith)]
      simp

/-- Proposition 4.2.9(c) (order is transitive) / Exercise 4.2.5 -/
theorem Rat.lt_trans {x y z:Rat} (hxy: x < y) (hyz: y < z) : x < z := by
  obtain ⟨c, ⟨hcpos, hceq⟩⟩ := hxy
  obtain ⟨d, ⟨hdpos, hdeq⟩⟩ := hyz
  use (c + d)
  constructor
  · apply Rat.pos_add_pos_is_pos c d
    · exact hcpos
    · exact hdpos
  · have hc := congrArg (λ expr => expr + z) hdeq; simp at hc
    rw [hc] at hceq
    ring_nf at *
    linear_combination hceq

/-- Proposition 4.2.9(d) (addition preserves order) / Exercise 4.2.5 -/
theorem Rat.add_lt_add_right {x y:Rat} (z:Rat) (hxy: x < y) : x + z < y + z := by
  obtain ⟨d, ⟨hdpos, heq⟩⟩ := hxy
  use d
  constructor
  · exact hdpos
  · ring
    exact heq

-- let's do left just in case it's useful.
theorem Rat.add_lt_add_left {x y:Rat} (z:Rat) (hxy: x < y) : z + x < z + y := by
  obtain ⟨d, ⟨hdpos, heq⟩⟩ := hxy
  use d
  constructor
  · exact hdpos
  · ring
    exact heq

/-- Proposition 4.2.9(e) (positive multiplication preserves order) / Exercise 4.2.5 -/
theorem Rat.mul_lt_mul_right {x y z:Rat} (hxy: x < y) (hz: z.isPos) : x * z < y * z := by
  obtain ⟨d, ⟨hdpos, heq⟩⟩ := hxy
  use (d * z)
  constructor
  · exact Rat.pos_mul_pos_is_pos d z hdpos hz
  · have fact1 : x * z - y * z = (x - y) * z := by exact Eq.symm (sub_mul x y z)
    have fact2 : -(d * z) = (-d) * z := by exact neg_mul_eq_neg_mul d z
    rw [fact1, fact2]
    congr

-- let's do left just in case it's useful.
theorem Rat.mul_lt_mul_left {x y z:Rat} (hxy: x < y) (hz: z.isPos) : z * x < z * y  := by
  obtain ⟨d, ⟨hdpos, heq⟩⟩ := hxy
  use (z * d)
  constructor
  · exact Rat.pos_mul_pos_is_pos z d hz hdpos
  · have fact1 : z * x - z * y = z * (x - y) := by exact Eq.symm (mul_sub_left_distrib z x y)
    have fact2 : -(z * d) = z * (-d) := by exact neg_mul_eq_mul_neg z d
    rw [fact1, fact2]
    congr

/-- (Not from textbook) Establish the decidability of this order. -/
instance Rat.decidableRel : DecidableRel (· ≤ · : Rat → Rat → Prop) := by
  intro n m
  have : ∀ (n:PreRat) (m: PreRat),
      Decidable (Quotient.mk PreRat.instSetoid n ≤ Quotient.mk PreRat.instSetoid m) := by
    intro ⟨ a,b,hb ⟩ ⟨ c,d,hd ⟩
    -- at this point, the goal is morally `Decidable(a//b ≤ c//d)`, but there are technical
    -- issues due to the junk value of formal division when the denominator vanishes.
    -- It may be more convenient to avoid formal division and work directly with `Quotient.mk`.
    cases (0:ℤ).decLe (b*d) with
      | isTrue hbd =>
        cases (a * d).decLe (b * c) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
      | isFalse hbd =>
        cases (b * c).decLe (a * d) with
          | isTrue h =>
            apply isTrue
            sorry
          | isFalse h =>
            apply isFalse
            sorry
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) Rat has the structure of a linear ordering. -/
instance Rat.instLinearOrder : LinearOrder Rat where
  le_refl := by
    intro a
    right
    rfl
  le_trans := by
    intro a b c haleb hblec
    rcases haleb with (haltb | haeqb)
    · rcases hblec with (hbltc | hbeqc)
      · left; exact lt_trans haltb hbltc
      · left; rw [hbeqc] at haltb; exact haltb
    · rcases hblec with (hbltc | hbeqc)
      · left; rw [← haeqb] at hbltc; exact hbltc
      · right; rw [← haeqb] at hbeqc; exact hbeqc
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h
      constructor
      · left; exact h
      · rintro (hlt | heq)
        · apply Rat.not_gt_and_lt a b
          exact ⟨hlt, h⟩
        · apply Rat.not_lt_and_eq a b
          exact ⟨h, heq.symm⟩
    · intro ⟨haleb, hnblea⟩
      rcases haleb with (hle | heq)
      · exact hle
      · change ¬(b < a ∨ b = a) at hnblea
        push_neg at hnblea
        exact absurd heq.symm hnblea.2
  le_antisymm := by
    intro a b hab hba
    rcases hab with (haleb | haeqb)
    · rcases hba with (hblea | hbeqa)
      · exfalso
        apply Rat.not_gt_and_lt a b
        exact ⟨hblea, haleb⟩
      · exact hbeqa.symm
    · exact haeqb
  le_total := by
    intro a b
    by_contra h
    push_neg at h
    rcases h with ⟨h1, h2⟩
    change ¬(a < b ∨ a = b) at h1
    change ¬(b < a ∨ b = a) at h2
    push_neg at h1
    push_neg at h2
    rcases Rat.trichotomous' a b with (hgt | hlt | heq)
    · exact h2.1 hgt
    · exact h1.1 hlt
    · exact h1.2 heq
  toDecidableLE := decidableRel

/-- (Not from textbook) Rat has the structure of a strict ordered ring. -/
instance Rat.instIsStrictOrderedRing : IsStrictOrderedRing Rat where
  add_le_add_left := by
    intro a b haleb c
    rcases haleb with (haltb | heq)
    · left; exact add_lt_add_right c haltb
    · right; rw [heq]
  add_le_add_right := by
    intro a b haleb c
    rcases haleb with (haltb | heq)
    · left; exact add_lt_add_left c haltb
    · right; rw [heq]
  mul_lt_mul_of_pos_left := by
    intro a hagt0 b c hbltc
    have hpos : a.isPos := by
      have fact := (Rat.gt_iff a 0).mp hagt0
      rw [sub_zero] at fact
      exact fact
    exact mul_lt_mul_left hbltc hpos
  mul_lt_mul_of_pos_right := by
    intro c hcgt0 a b haltb
    have hpos : c.isPos := by
      have fact := (Rat.gt_iff c 0).mp hcgt0
      rw [sub_zero] at fact
      exact fact
    exact mul_lt_mul_right haltb hpos
  le_of_add_le_add_left := by
    intro a b c habc
    rcases habc with (hlt | heq)
    · left
      obtain ⟨t, ⟨ht₁, ht₂⟩⟩ := hlt
      use t
      constructor
      · exact ht₁
      · simp at ht₂
        exact ht₂
    · right
      have hc := congrArg (λ expr => -a + expr) heq; simp at hc
      exact hc
  zero_le_one := by
    left
    use 1
    constructor
    · use 1, 1
      constructor
      · linarith
      · constructor
        · linarith
        · norm_cast
    · norm_num

/-- Exercise 4.2.6 -/
theorem Rat.mul_lt_mul_right_of_neg (x y z:Rat) (hxy: x < y) (hz: z.isNeg) : x * z > y * z := by
  rw [Rat.isNeg] at hz
  obtain ⟨t, ⟨htpos, ht⟩⟩ := hxy
  obtain ⟨r, ⟨hrpos, hr⟩⟩ := hz
  use (t * r)
  have ht' := congrArg (λ expr => -(expr)) ht; simp at ht'
  constructor
  · exact Rat.pos_mul_pos_is_pos t r htpos hrpos
  · calc y * z - x * z = (y - x) * z  := by exact (sub_mul y x z).symm
                     _ = t * (-r)     := by rw [ht', hr]
                     _ = -(t * r)     := by field

/--
  Not in textbook: create an equivalence between Rat and ℚ. This requires some familiarity with
  the API for Mathlib's version of the rationals.
-/
abbrev Rat.equivRat : Rat ≃ ℚ where
  toFun := Quotient.lift (fun ⟨ a, b, h ⟩ ↦ a / b) (by
    intro ⟨a₁, a₂, ha⟩ ⟨b₁, b₂, hb⟩ hab
    dsimp
    rw [PreRat.eq] at hab
    apply (@div_eq_div_iff ℚ _ (a₁ : ℚ) a₂ b₁ b₂ ?_ ?_).mpr
    · norm_cast
    · intro h
      have ha' : (a₂ : ℚ) ≠ 0 := by exact Rat.num_ne_zero.mp ha
      exact absurd h ha'
    · intro h
      have hb' : (b₂ : ℚ) ≠ 0 := by exact Rat.num_ne_zero.mp hb
      exact absurd h hb'
    )
  invFun := fun n: ℚ ↦ (n:Rat)
  left_inv   := by
    intro a
    obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
    simp
    split_ifs with hif
    · simp
      exact absurd hif ha
    · simp
      change (a₁ // 1) / (a₂ // 1) = a₁ // a₂
      conv =>
        lhs
        change (a₁ // 1) * (1 // a₂)
        rw [@Rat.mul_eq _ _ _ _ (by linarith) ha]
        rw [mul_one, one_mul]
  right_inv  := by
    intro q
    dsimp
    show Quotient.lift _ _ (q.num // (q.den : ℤ)) = q
    simp only [Quotient.lift_mk]
    split_ifs with hif
    · simp
      norm_cast
      exact Rat.num_divInt_den q
    · simp
      obtain ⟨q₁, q₂, q₃, q₄⟩ := q
      simp at hif
      exact absurd hif q₃

theorem Rat.equivRat_mk (a b : ℤ) (hb : b ≠ 0) : equivRat (a // b) = (a : ℚ) / (b : ℚ) := by
  simp
  split_ifs with hif
  · exact absurd hif hb
  · simp

theorem Rat.equivRat_zero : equivRat 0 = 0 := by
  simp
  show Quotient.lift _ _ ((0 : ℚ).num // (0 : ℚ).den) = 0
  simp

theorem Rat.equivRat_neg (q: Rat) : equivRat (-q) = - equivRat q := by
  obtain ⟨q₁, q₂, hq, rfl⟩ := Rat.eq_diff q
  simp [Quotient.lift_mk]
  split_ifs with h
  · exact absurd h hq
  · simp
    rw [Rat.neg_eq _ hq]
    rw [Quotient.lift_mk]
    simp
    split_ifs
    · simp
      norm_cast
      exact Eq.symm (Rat.neg_divInt q₁ q₂)

theorem Rat.equivRat_add (a b : Rat) : equivRat (a + b) = equivRat a + equivRat b := by
  obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
  obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
  conv =>
    lhs
    rw [@Rat.add_eq _ _ _ _ ha hb]
  simp
  split_ifs with hif
  · simp
    norm_cast
    have fact := (Rat.divInt_add_divInt a₁ b₁ ha hb).symm
    have nit : a₁ * b₂ + b₁ * a₂ = a₁ * b₂ + a₂ * b₁ := by linarith
    rw [nit] at fact
    exact fact
  · push_neg at hif
    exact absurd (hif ha) hb

theorem Rat.equivRat_mul (a b : Rat) : equivRat (a * b) = equivRat a * equivRat b := by
  obtain ⟨a₁, a₂, ha, rfl⟩ := Rat.eq_diff a
  obtain ⟨b₁, b₂, hb, rfl⟩ := Rat.eq_diff b
  conv => 
    lhs 
    rw [@Rat.mul_eq _ _ _ _ ha hb]
  simp 
  split_ifs with hif
  · simp 
    norm_cast 
    exact Eq.symm (Rat.divInt_mul_divInt a₁ b₁)
  · push_neg at hif
    exact absurd (hif ha) hb 

theorem Rat.equivRat_sub (a b : Rat) : equivRat (a - b) = equivRat a - equivRat b := by
  change equivRat (a + (-b)) = equivRat a - equivRat b
  calc equivRat (a + (-b))
     = equivRat a + equivRat (-b)  := by exact Rat.equivRat_add a (-b)
   _ = equivRat a + (- equivRat b) := by rw [Rat.equivRat_neg b]
   _ = equivRat a - equivRat b     := by linarith


theorem Rat.neg_div_neg (a b : ℤ) (hb : b ≠ 0): (-a) // (-b) = a // b := by 
  rw [@Rat.eq _ _ _ _ (Int.neg_ne_zero.mpr hb) hb]
  simp

theorem Rat.equivRat_isPos (q : Rat) : q.isPos ↔ 0 < equivRat q := by
  constructor
  · intro hpos
    obtain ⟨a, b, hab⟩ := hpos
    rw [hab.2.2]
    conv =>
      rhs
      change equivRat ((a // 1) * (1 // b))
      rw [@Rat.mul_eq _ _ _ _ (by linarith) (by linarith)]
      rw [one_mul, mul_one]
    rw [Rat.equivRat_mk _ _ (by linarith)]
    apply div_pos
    · exact_mod_cast hab.1
    · exact_mod_cast hab.2.1
  · intro hgt0
    -- Rat.equivRat_mk (a b : ℤ) (hb : b ≠ 0) : equivRat (a // b) = (a : ℚ) / (b : ℚ) := by
    obtain ⟨q₁, q₂, hq, rfl⟩ := Rat.eq_diff q
    rw [Rat.equivRat_mk _ _ hq] at hgt0
    rcases div_pos_iff.mp hgt0 with (⟨hq₁, hq₂⟩ | ⟨hq₁, hq₂⟩)
    · use q₁, q₂
      constructor 
      · exact Rat.intCast_pos.mp hq₁
      · constructor 
        · exact Rat.intCast_pos.mp hq₂
        · exact Rat.div_is_div q₁ q₂ hq
    · use (-q₁), (-q₂)
      constructor 
      · exact_mod_cast neg_pos.mpr hq₁
      · constructor 
        · exact_mod_cast neg_pos.mpr hq₂
        · rw [← Rat.neg_div_neg _ _ hq]
          exact Rat.div_is_div (-q₁) (-q₂) (Int.neg_ne_zero.mpr hq) 

theorem Rat.equivRat_isNeg (q : Rat) : q.isNeg ↔ equivRat q < 0 := by 
  constructor 
  · intro hneg 
    obtain ⟨r, ⟨hrpos, hreq⟩⟩ := hneg 
    rw [Rat.equivRat_isPos] at hrpos
    have hreq' := congr_arg equivRat hreq
    rw [Rat.equivRat_neg] at hreq'
    rw [hreq']
    exact Rat.neg_lt_iff.mp hrpos
  · intro h 
    have h' : -(equivRat q) > 0 := by exact Rat.lt_neg_iff.mp h
    rw [← Rat.equivRat_neg] at h'
    rw [gt_iff_lt] at h'
    rw [← Rat.equivRat_isPos (-q)] at h'
    use -q
    constructor 
    · exact h' 
    · simp
  
/-- Not in textbook: equivalence preserves order -/
abbrev Rat.equivRat_order : Rat ≃o ℚ where
  toEquiv := equivRat
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      rcases lt_or_eq_of_le h with (hlt | heq)
      · left 
        change (a-b).isNeg
        have  hlt' : equivRat a + (-equivRat b) < 0 := by linarith 
        rw [← Rat.equivRat_neg, ← Rat.equivRat_add] at hlt'
        change equivRat (a - b) < 0 at hlt' 
        rw [← Rat.equivRat_isNeg] at hlt' 
        exact hlt'
      · right; exact equivRat.injective heq
    · rintro (hlt | heq)
      · obtain ⟨d, ⟨hdpos, hdeq⟩⟩ := hlt 
        rw [Rat.equivRat_isPos] at hdpos 
        have hdeq' := congr_arg (-(·)) hdeq; simp at hdeq'
        rw [← hdeq'] at hdpos 
        change 0 < equivRat (b + (-a)) at hdpos
        rw [Rat.equivRat_add] at hdpos
        rw [Rat.equivRat_neg] at hdpos 
        linarith [hdpos]
      · have heq' := congr_arg equivRat heq
        linarith [heq']

/-- Not in textbook: equivalence preserves ring operations -/
abbrev Rat.equivRat_ring : Rat ≃+* ℚ where
  toEquiv := equivRat
  map_add' := by 
    intro x y 
    obtain ⟨x₁, x₂, hx, rfl⟩ := Rat.eq_diff x 
    obtain ⟨y₁, y₂, hy, rfl⟩ := Rat.eq_diff y 
    show equivRat (x₁ // x₂ + y₁ // y₂) = equivRat (x₁ // x₂) + equivRat (y₁ // y₂)
    rw [Rat.equivRat_add]
  map_mul' := by 
    intro x y 
    obtain ⟨x₁, x₂, hx, rfl⟩ := Rat.eq_diff x 
    obtain ⟨y₁, y₂, hy, rfl⟩ := Rat.eq_diff y 
    show equivRat (x₁ // x₂ * y₁ // y₂) = equivRat (x₁ // x₂) * equivRat (y₁ // y₂)
    sorry

/--
  (Not from textbook) The textbook rationals are isomorphic (as a field) to the Mathlib rationals.
-/
def Rat.equivRat_ring_symm : ℚ ≃+* Rat := Rat.equivRat_ring.symm

end Section_4_2
