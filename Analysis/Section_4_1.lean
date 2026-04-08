import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 4.1: The integers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of the "Section 4.1" integers, `Section_4_1.Int`, as formal differences `a —— b` of
  natural numbers `a b:ℕ`, up to equivalence.  (This is a quotient of a scaffolding type
  `Section_4_1.PreInt`, which consists of formal differences without any equivalence imposed.)

- ring operations and order these integers, as well as an embedding of {lean}`ℕ`.

- Equivalence with the Mathlib integers {name}`_root_.Int` (or {lean}`ℤ`), which we will use going forward.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- Definition 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by
      intro x
      rfl
    symm := by
      intro x y hxy
      exact hxy.symm
    trans := by
      -- This proof is written to follow the structure of the original text.
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
    }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- Decidability of equality -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- Definition 4.1.1 (Integers) -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- Lemma 4.1.3 (Addition well-defined) -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- Definition 4.1.2 (Definition of addition) -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- Lemma 4.1.3 (Multiplication well-defined) -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- Definition 4.1.2 (Multiplication of integers) -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/-- (Not from textbook) 0 is the only natural whose cast is 0 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  constructor
  · intro hn
    -- uncomment this line to see what Lean does when coercing
    -- a ℕ into an Int.
    -- dsimp only [Nat.cast, NatCast.natCast] at hn
    have hn' := Quotient.exact hn
    rw [PreInt.eq] at hn'
    rw [Nat.add_zero, Nat.zero_add] at hn'
    exact hn'
  · intro hn
    -- dsimp only [Nat.cast, NatCast.natCast]
    change n —— 0 = 0
    apply Quotient.sound
    rw [PreInt.eq]
    rw [Nat.add_zero, Nat.zero_add]
    exact hn

/-- Definition 4.1.4 (Negation of integers) / Exercise 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (
    by intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hn
       apply Quotient.sound
       rw [PreInt.eq] at *
       symm at hn
       rw [Nat.add_comm b₁ a₂, Nat.add_comm a₁ b₂] at hn
       exact hn
  )

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- Lemma 4.1.5 (trichotomy of integers )-/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- This proof is slightly modified from that in the original text.
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq]; abel
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- Lemma 4.1.5 (trichotomy of integers)-/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms
   (by apply Quotient.ind; intro ⟨a₁, a₂⟩
       apply Quotient.ind; intro ⟨b₁, b₂⟩
       apply Quotient.ind; intro ⟨c₁, c₂⟩
       apply Quotient.sound
       rw [PreInt.eq]
       abel)
   (by apply Quotient.ind; intro ⟨a₁, a₂⟩
       apply Quotient.sound
       rw [PreInt.eq]
       rw [Nat.zero_add, Nat.zero_add])
   (by apply Quotient.ind; intro ⟨a₁, a₂⟩
       apply Quotient.sound
       rw [PreInt.eq]
       rw [Nat.add_zero, Nat.zero_add]
       abel)

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.ind; intro ⟨b₁, b₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    abel


/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.ind; intro ⟨b₁, b₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    -- it's a little messy and annoying to manage the
    -- multiplication ourselves, so let's just use
    -- Mathlib's ring tactic.
    ring
  mul_assoc := by
    -- This proof is written to follow the structure of the original text.
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    rw [Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero]
  mul_one := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    -- It was tiring to rewring all the one_muls and zero_muls...
    ring

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.ind; intro ⟨b₁, b₂⟩
    apply Quotient.ind; intro ⟨c₁, c₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    ring
  right_distrib := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.ind; intro ⟨b₁, b₂⟩
    apply Quotient.ind; intro ⟨c₁, c₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    ring
  zero_mul := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    ring
  mul_zero := by
    apply Quotient.ind; intro ⟨a₁, a₂⟩
    apply Quotient.sound
    rw [PreInt.eq]
    ring

/-- Definition of subtraction -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  change (a —— 0) - (b —— 0) = a —— b
  apply Quotient.sound
  rw [PreInt.eq]
  rw [Nat.add_zero, Nat.zero_add]

/-- Proposition 4.1.8 (No zero divisors) / Exercise 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨⟨a₁, a₂⟩, ha⟩ := Quotient.exists_rep a
  obtain ⟨⟨b₁, b₂⟩, hb⟩ := Quotient.exists_rep b
  rw [← ha, ← hb] at h
  have h := Quotient.exact h
  rw [PreInt.eq] at h
  rw [Nat.add_zero, Nat.zero_add] at h
  have heq : a₁ = a₂ ∨ b₁ = b₂ := by
    rcases Nat.lt_trichotomy a₁ a₂ with (hlt | heq | hgt)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
      rw [hk] at h
      simp [Nat.add_mul] at h
      repeat rw [Nat.add_assoc] at h
      have hcancel : (a₁ * b₁ + a₁ * b₂) + (k + 1) * b₂ = (a₁ * b₁ + a₁ * b₂) + (k + 1) * b₁ := by
        linarith [h]
      have hcanceladd := Nat.add_left_cancel hcancel
      have hcancelmul := Nat.mul_left_cancel (by linarith) hcanceladd
      right; exact hcancelmul.symm
    · left; exact heq
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
      rw [hk] at h
      simp [Nat.add_mul] at h
      repeat rw [Nat.add_assoc] at h
      have hcancel : (a₂ * b₁ + a₂ * b₂) + (k + 1) * b₁= (a₂ * b₁ + a₂ * b₂) + (k + 1) * b₂ := by
        linarith [h]
      have hcanceladd := Nat.add_left_cancel hcancel
      have hcancelmul := Nat.mul_left_cancel (by linarith) hcanceladd
      right; exact hcancelmul
  rcases heq with (ha0 | hb0)
  · left
    rw [← ha]
    apply Quotient.sound
    rw [PreInt.eq]
    rw [Nat.add_zero, Nat.zero_add]
    exact ha0
  · right
    rw [← hb]
    apply Quotient.sound
    rw [PreInt.eq]
    rw [Nat.add_zero, Nat.zero_add]
    exact hb0

/-- Corollary 4.1.9 (Cancellation law) / Exercise 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  have f1 := congrArg (· -(b * c)) h; simp at f1
  have f2 : (a - b) * c = a * c - b * c := sub_mul a b c
  rw [← f2] at f1
  rcases Int.mul_eq_zero f1 with (hab | hc')
  · have f3 := congrArg (· + b) hab; simp at f3
    exact f3
  · exact absurd hc' hc

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- Definition 4.1.10 (Ordering of the integers) -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- Lemma 4.1.11(a) (Properties of order) / Exercise 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  constructor
  · intro hab
    obtain ⟨⟨x, hx⟩, h'⟩ := (Int.lt_iff a b).mp hab
    use x
    constructor
    · intro h0
      rw [h0] at hx
      simp at hx
      exact h' hx.symm
    · exact hx
  · intro h
    obtain ⟨x, ⟨h₁, h₂⟩⟩ := h
    constructor
    · use x
    · intro h
      rw [h] at h₂
      have he0 : (x : Int) = 0 := by
         have := congrArg (· + (-b)) h₂
         simp at this
         exact this.symm
      have hnat : x = 0 := (Int.ofNat_inj x 0).mp he0
      exact h₁ hnat

/-- Lemma 4.1.11(b) (Addition preserves order) / Exercise 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  obtain ⟨x, ⟨h₁, h₂⟩⟩ := (Int.lt_iff_exists_positive_difference a b).mp h
  apply (Int.lt_iff_exists_positive_difference (a + c) (b + c)).mpr
  use x
  constructor
  · exact h₁
  . rw [h₂]
    abel

/-- Lemma 4.1.11(c) (Positive multiplication preserves order) / Exercise 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  obtain ⟨⟨x, hx₁⟩, hx₂⟩ := (Int.lt_iff a b).mp hab
  obtain ⟨⟨y, hy₁⟩, hy₂⟩ := (Int.lt_iff 0 c).mp hc
  simp at hy₁
  apply (Int.lt_iff (a * c) (b * c)).mpr
  constructor
  · use x * y
    rw [hy₁]
    rw [hx₁]
    rw [add_mul]
    simp
  · intro h
    have heq := Int.mul_right_cancel₀ a b c h hy₂.symm
    exact absurd heq hx₂

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
-- theorem Int.lt_iff_exists_positive_difference (a b:Int) :
--  a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := (Int.lt_iff_exists_positive_difference b a).mp h
  apply (Int.lt_iff_exists_positive_difference (-a) (-b)).mpr
  use x
  constructor
  · exact hx₁
  · rw [hx₂]
    rw [neg_add']
    simp

/-- Lemma 4.1.11(d) (Negation reverses order) / Exercise 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
--theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl
  obtain ⟨x, hx⟩ := (Int.le_iff b a).mp h
  apply (Int.le_iff (-a) (-b)).mpr
  use x
  rw [hx]
  rw [neg_add']
  simp

/-- Lemma 4.1.11(e) (Order is transitive) / Exercise 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := (Int.lt_iff_exists_positive_difference a b).mp hab
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := (Int.lt_iff_exists_positive_difference b c).mp hbc
  apply (Int.lt_iff_exists_positive_difference a c).mpr
  use x + y
  constructor
  · intro heq
    rcases Nat.add_eq_zero_iff.mp heq with ⟨hx0, hy0⟩
    exact absurd hx0 hx₁
  · rw [hy₂]
    rw [hx₂]
    abel_nf
    simp

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  rcases Int.trichotomous (a - b) with (heq0 | hpos | hneg)
  · have heq : a = b := by
      have hc := congrArg (· + b) heq0
      simp at hc
      exact hc
    right; right; exact heq
  · obtain ⟨x, ⟨hxgt0, habx⟩⟩ := hpos
    have : b < a := by
      apply (Int.lt_iff b a).mpr
      constructor
      · use x
        rw [← habx]
        abel
      · intro heq
        rw [heq] at habx
        simp at habx
        have heq0 : x = 0 := (Int.ofNat_inj x 0).mp habx.symm
        linarith only [heq0, hxgt0]
    left; exact this
  · obtain ⟨x, ⟨hxgt0, habx⟩⟩ := hneg
    have : a < b := by
      apply (Int.lt_iff a b).mpr
      constructor
      · use x
        have hc := congrArg (· * (-1)) habx
        simp at hc
        rw [← hc]
        abel
      · intro heq
        rw [heq] at habx
        simp at habx
        have heq0 : x = 0 := (Int.ofNat_inj x 0).mp habx
        linarith only [heq0, hxgt0]
    right; left; exact this


/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b) := by
  intro ⟨hagtb, haltb⟩
  obtain ⟨x, ⟨hx₁, hx₂⟩⟩ := (Int.lt_iff_exists_positive_difference b a).mp hagtb
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := (Int.lt_iff_exists_positive_difference a b).mp haltb
  rw [hx₂] at hy₂
  have hcancel := congrArg (λ expr => (-b) + expr) hy₂
  simp at hcancel; rw [add_assoc] at hcancel; simp at hcancel; norm_cast at hcancel
  have hxgt0 : 0 < x := by exact Nat.zero_lt_of_ne_zero hx₁
  have hygt0 : 0 < y := by exact Nat.zero_lt_of_ne_zero hy₁
  have hgt0  : 0 < x + y := by linarith [hxgt0, hygt0]
  have hnat  : 0 = x + y := (Int.ofNat_inj 0 (x+y)).mp hcancel
  linarith [hnat, hgt0]

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b):= by
  intro ⟨hagtb, heq⟩
  obtain ⟨_, hneq⟩ := hagtb
  exact absurd heq.symm hneq

/-- Lemma 4.1.11(f) (Order trichotomy) / Exercise 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b):= by
  intro ⟨haltb, heq⟩
  obtain ⟨_, hneq⟩ := haltb
  exact absurd heq hneq

/-- (Not from textbook) Establish the decidability of this order. -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (b + c) with
      | isTrue h =>
        apply isTrue
        obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le h
        use x
        apply Quotient.sound
        rw [PreInt.eq]
        rw [Nat.add_zero]
        rw [Nat.add_comm c b]
        rw [hx]
        abel
      | isFalse h =>
        apply isFalse
        intro hrel
        obtain ⟨y, hy⟩ := hrel
        have hquo := Quotient.exact hy
        rw [PreInt.eq] at hquo
        simp at hquo
        apply h
        rw [Nat.add_comm c b, Nat.add_comm a y, Nat.add_assoc] at hquo
        have hle : a + d ≤ (a + d) + y := Nat.le_add_right (a + d) y
        have hrw : y + (a + d) = a + d + y := by abel
        rw [← hrw] at hle
        rw [← hquo] at hle
        exact hle
  exact Quotient.recOnSubsingleton₂ n m this

/-- (Not from textbook) 0 is the only additive identity -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor
  · intro h
    specialize h 0
    simp at h
    exact h.symm
  · intro h a
    rw [h]
    simp

/-- (Not from textbook) Int has the structure of a linear ordering. -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by
    intro a
    use 0
    simp
  le_trans := by
    intro a b c hab hbc
    obtain ⟨x, hx⟩ := hab
    obtain ⟨y, hy⟩ := hbc
    use x + y
    rw [hx] at hy
    rw [hy]
    simp
    rw [add_assoc]
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro hab
      constructor
      · exact hab.1
      · intro hba
        by_cases heq : a = b
        · exact Int.not_lt_and_eq a b ⟨hab, heq⟩
        · change a ≠ b at heq
          have hblta : b < a := ⟨hba, heq.symm⟩
          exact Int.not_gt_and_lt b a ⟨hab, hblta⟩
    · intro ⟨haleb, hn⟩
      constructor
      · exact haleb
      · intro heq
        apply hn
        rw [heq]
        use 0
        simp
  le_antisymm := by
    intro a b hab hba
    obtain ⟨x, hx⟩ := hab
    obtain ⟨y, hy⟩ := hba
    rw [hx] at hy
    have hc := congrArg (λ expr => (-a) + expr) hy
    simp at hc; rw [add_assoc] at hc; simp at hc; norm_cast at hc
    have hxy0 : x + y = 0 := by exact (cast_eq_0_iff_eq_0 (x + y)).mp (hc.symm)
    rcases Nat.eq_zero_of_add_eq_zero hxy0 with ⟨hx0, hy0⟩
    rw [hx0] at hx
    simp at hx
    exact hx.symm
  le_total := by
    intro a b
    rcases Int.trichotomous' a b with (hgt | hlt | heq)
    · right; exact hgt.1
    · left;  exact hlt.1
    · left
      use 0
      simp
      exact heq.symm
  toDecidableLE := decidableRel

#check Int.add_left_cancel

/-- Exercise 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  induction a using Quotient.ind; rename_i a
  cases a with
  | mk a₁ a₂ =>
    apply Quotient.sound
    rw [PreInt.eq]
    simp

/-- Exercise 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  use (fun x => 0 ≤ x)
  dsimp
  constructor
  · constructor
    · use 0; simp
    · intro n hn
      have : n ≤ n + 1 := by
        use 1
        simp
      exact Int.instLinearOrder.le_trans 0 n (n+1) hn this
  · intro hall
    have hbad := hall (-1)
    obtain ⟨x, hx⟩ := hbad
    rw [zero_add] at hx
    have hq := Quotient.exact hx
    rw [PreInt.eq] at hq
    rw [zero_add] at hq
    symm at hq
    have ⟨hx, h0⟩ := Nat.eq_zero_of_add_eq_zero hq
    linarith [h0]

/-- A nonnegative number squared is nonnegative. This is a special case of 4.1.9 that's useful for proving the general case. --/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  by_cases h0 : n = 0
  · rw [h0]
    simp
  · change n ≠ 0 at h0
    have hgt0 : 0 < n := ⟨h, h0.symm⟩
    have h' :=  Int.mul_lt_mul_of_pos_right hgt0 hgt0
    simp at h'
    exact h'.1

/-- Exercise 4.1.9. The square of any integer is nonnegative. -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  by_cases h : 0 ≤ n
  · exact Int.sq_nonneg_of_pos n h
  · push_neg at h
    have hnegng0 : - 0 < -n := Int.neg_gt_neg h
    simp at hnegng0
    have this := Int.sq_nonneg_of_pos (-n) hnegng0.1
    simp at this
    exact this

/-- Exercise 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h := Int.sq_nonneg n
  obtain ⟨m, hm⟩ := h
  simp at hm
  use m

/--
  Not in textbook: create an equivalence between {name}`Int` and {lean}`ℤ`.
  This requires some familiarity with the API for Mathlib's version of the integers.
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ a - b) (by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hequiv
    simp at *
    -- zify comes from coercing the Ns to the Ints, so we don't have
    -- to worry about manually doing the coercions.
    zify at hequiv
    linarith
  )
  invFun := fun (z : ℤ)  ↦
    match z with
    | .ofNat n   => n
    | .negSucc n => -(n + 1)
  left_inv  := by
    intro n
    obtain ⟨a, b, rfl⟩ := eq_diff n
    simp only [Quotient.lift_mk]
    rcases h : (a : ℤ) - b with (x | x)
    · simp_all only [Int.ofNat_eq_natCast, Int.natCast_eq, Int.eq]
      rw [Nat.add_zero]
      have hc := congrArg (λ expr => expr + (b : ℤ)) h; simp at hc
      zify
      rw [hc]
    · simp_all only [Int.ofNat_eq, Int.natCast_eq, Int.neg_eq, Int.add_eq]
      rw [Int.eq]
      simp_all
      have h' : (b : ℤ) - a = x + 1 := by
        simp [_root_.Int.negSucc_eq] at h
        linarith only [h]
      have hc := congrArg (· + (a : ℤ)) h'; simp at hc
      zify
      rw [hc]
      abel
  right_inv := by
    intro n
    rcases n with (m | m)
    · simp only [Int.ofNat_eq_natCast, Int.natCast_eq, Quotient.lift_mk]
      simp
    · simp only [Int.ofNat_eq, Int.natCast_eq, Int.neg_eq, Int.add_eq, Quotient.lift_mk]
      simp [_root_.Int.negSucc_eq]

/-- Not in textbook: equivalence preserves order and ring operations -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv  := equivInt
  map_add' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := Int.eq_diff b
    simp_all only [Int.add_eq, Quotient.lift_mk]
    omega
  map_mul' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := Int.eq_diff b
    simp_all only [Int.mul_eq, Quotient.lift_mk]
    grind
  map_le_map_iff' := by
    intro a b
    obtain ⟨a₁, a₂, rfl⟩ := Int.eq_diff a
    obtain ⟨b₁, b₂, rfl⟩ := Int.eq_diff b
    simp_all only [Quotient.lift_mk, Int.le_iff, Int.natCast_eq, Int.add_eq, Int.eq]
    simp
    constructor
    · intro ha
      obtain ⟨t, ht⟩ := _root_.Int.exists_add_of_le ha
      have hc := congrArg (λ expr => expr + (b₂ : ℤ)) ht
      dsimp at hc
      abel_nf at hc
      use t
      zify
      rw [hc]
      abel
    · intro ⟨t, ht⟩
      linarith only [ht]

end Section_4_1
