import Mathlib.Tactic
import Analysis.Section_2_2

/-!
# Analysis I, Section 2.3: Multiplication

This file is a translation of Section 2.3 of Analysis I to Lean 4. All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of multiplication and exponentiation for the "Chapter 2" natural numbers,
  {name}`Chapter2.Nat`.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter2

/-- Definition 2.3.1 (Multiplication of natural numbers) -/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod ↦ prod + m) 0 n

/-- This instance allows for the {kw (of := «term_*_»)}`*` notation to be used for natural number multiplication. -/
instance Nat.instMul : Mul Nat where
  mul := mul

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.zero_mul` -/
theorem Nat.zero_mul (m: Nat) : 0 * m = 0 := recurse_zero (fun _ prod ↦ prod+m) _

/-- Definition 2.3.1 (Multiplication of natural numbers)
Compare with Mathlib's {name}`Nat.succ_mul` -/
theorem Nat.succ_mul (n m: Nat) : (n++) * m = n * m + m := recurse_succ (fun _ prod ↦ prod+m) _ _

theorem Nat.one_mul' (m: Nat) : 1 * m = 0 + m := by
  rw [←zero_succ, succ_mul, zero_mul]

/-- Compare with Mathlib's {name}`Nat.one_mul` -/
theorem Nat.one_mul (m: Nat) : 1 * m = m := by
  rw [one_mul', zero_add]

theorem Nat.two_mul (m: Nat) : 2 * m = 0 + m + m := by
  rw [←one_succ, succ_mul, one_mul']

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_zero` -/
lemma Nat.mul_zero (n: Nat) : n * 0 = 0 := by
  induction n with
  | zero      =>
    change 0 * 0 = 0
    rw [zero_mul]
  | succ k ih =>
    rw [Nat.succ_mul]
    rw [ih]
    rw [add_zero]

/-- This lemma will be useful to prove Lemma 2.3.2.
Compare with Mathlib's {name}`Nat.mul_succ` -/
lemma Nat.mul_succ (n m:Nat) : n * m++ = n * m + n := by
  induction n with
  | zero      =>
    change 0 * m++ = 0 * m + 0
    rw [zero_mul, zero_mul, zero_add]
  | succ k ih =>
    -- show k++ * m++ = k++ * m + k++
    calc k++ * m++ = k * m++ + m++       := by rw [succ_mul]
                 _ = (k * m + k) + m++   := by rw [ih]
                 _ = (k * m) + (k + m++) := by abel
                 _ = k * m + (k + m)++   := by rw [add_succ k m]
                 _ = k * m + (m + k)++   := by rw [add_comm k m]
                 _ = k * m + (m + k++)   := by rw [← add_succ m k]
                 _ = (k * m + m) + k++   := by abel
                 _ = k++ * m + k++       := by rw [← succ_mul k m]


/-- Lemma 2.3.2 (Multiplication is commutative) / Exercise 2.3.1
Compare with Mathlib's {name}`Nat.mul_comm` -/
lemma Nat.mul_comm (n m: Nat) : n * m = m * n := by
  induction n with
  | zero =>
    change 0 * m = m * 0
    rw [zero_mul, mul_zero]
  | succ k ih =>
    rw [succ_mul, mul_succ, ih]

/-- Compare with Mathlib's {name}`Nat.mul_one` -/
theorem Nat.mul_one (m: Nat) : m * 1 = m := by
  rw [mul_comm, one_mul]

/-- This lemma will be useful to prove Lemma 2.3.3.
Compare with Mathlib's {name}`Nat.mul_pos` -/
lemma Nat.pos_mul_pos {n m: Nat} (h₁: n.IsPos) (h₂: m.IsPos) : (n * m).IsPos := by
  cases n with
  | zero   =>
    intro h
    exact absurd rfl h₁
  | succ k =>
    rw [succ_mul]
    exact Nat.add_pos_right (k * m) h₂

/-- Lemma 2.3.3 (Positive natural numbers have no zero divisors) / Exercise 2.3.2.
    Compare with Mathlib's {name}`Nat.mul_eq_zero`.  -/
lemma Nat.mul_eq_zero (n m: Nat) : n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have hn : n.IsPos := h'.1
    have hm : m.IsPos := h'.2
    have hc : (n * m).IsPos := Nat.pos_mul_pos hn hm
    exact hc h
  · rintro (hn | hm)
    · rw [hn, zero_mul]
    · rw [hm, mul_zero]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.mul_add` -/
theorem Nat.mul_add (a b c: Nat) : a * (b + c) = a * b + a * c := by
  -- This proof is written to follow the structure of the original text.
  revert c; apply induction
  . rw [add_zero]
    rw [mul_zero, add_zero]
  intro c habc
  rw [add_succ, mul_succ]
  rw [mul_succ, ←add_assoc, ←habc]

/-- Proposition 2.3.4 (Distributive law)
Compare with Mathlib's {name}`Nat.add_mul`  -/
theorem Nat.add_mul (a b c: Nat) : (a + b)*c = a*c + b*c := by
  simp only [mul_comm, mul_add]

/-- Proposition 2.3.5 (Multiplication is associative) / Exercise 2.3.3
Compare with Mathlib's {name}`Nat.mul_assoc` -/
theorem Nat.mul_assoc (a b c: Nat) : (a * b) * c = a * (b * c) := by
  revert c; apply induction
  · rw [mul_zero, mul_zero, mul_zero]
  · intro n hn
    nth_rewrite 2 [mul_succ]
    rw [Nat.mul_add]
    rw [← hn]
    rw [mul_succ]

/-- (Not from textbook)  {name}`Nat` is a commutative semiring.
    This allows tactics such as {tactic}`ring` to apply to the Chapter 2 natural numbers. -/
instance Nat.instCommSemiring : CommSemiring Nat where
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm

/-- This illustration of the {tactic}`ring` tactic is not from the
    textbook. -/
example (a b c d:ℕ) : (a+b)*1*(c+d) = d*b+a*c+c*b+a*d+0 := by ring


/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_right` -/
theorem Nat.mul_lt_mul_of_pos_right {a b c: Nat} (h: a < b) (hc: c.IsPos) : a * c < b * c := by
  -- This proof is written to follow the structure of the original text.
  rw [lt_iff_add_pos] at h
  choose d hdpos hd using h
  replace hd := congr($hd * c)
  rw [add_mul] at hd
  have hdcpos : (d * c).IsPos := pos_mul_pos hdpos hc
  rw [lt_iff_add_pos]
  use d*c

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_right {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    a * c > b * c := mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order)
Compare with Mathlib's {name}`Nat.mul_lt_mul_of_pos_left` -/
theorem Nat.mul_lt_mul_of_pos_left {a b c: Nat} (h: a < b) (hc: c.IsPos) : c * a < c * b := by
  simp [mul_comm]
  exact mul_lt_mul_of_pos_right h hc

/-- Proposition 2.3.6 (Multiplication preserves order) -/
theorem Nat.mul_gt_mul_of_pos_left {a b c: Nat} (h: a > b) (hc: c.IsPos) :
    c * a > c * b := mul_lt_mul_of_pos_left h hc

/-- Corollary 2.3.7 (Cancellation law)
Compare with Mathlib's {name}`Nat.mul_right_cancel` -/
lemma Nat.mul_cancel_right {a b c: Nat} (h: a * c = b * c) (hc: c.IsPos) : a = b := by
  -- This proof is written to follow the structure of the original text.
  have := trichotomous a b
  obtain hlt | rfl | hgt := this
  . replace hlt := mul_lt_mul_of_pos_right hlt hc
    apply ne_of_lt at hlt
    contradiction
  . rfl
  replace hgt := mul_gt_mul_of_pos_right hgt hc
  apply ne_of_gt at hgt
  contradiction

/-- (Not from textbook) {name}`Nat` is an ordered semiring.
This allows tactics such as {tactic}`gcongr` to apply to the Chapter 2 natural numbers. -/
instance Nat.isOrderedRing : IsOrderedRing Nat where
  zero_le_one := Nat.zero_le 1
  mul_le_mul_of_nonneg_left := by
    intro a ha b c hbc
    by_cases hne0 : a = 0
    · rw [hne0, zero_mul, zero_mul]
    · change a.IsPos at hne0
      by_cases hbeqc : b = c
      · rw [hbeqc]
      · have hltbc  : b < c := by exact ⟨hbc, hbeqc⟩
        have hltabc : a * b < a * c := Nat.mul_gt_mul_of_pos_left hltbc hne0
        exact le_of_lt hltabc
  mul_le_mul_of_nonneg_right := by
    intro a ha b c hbc
    by_cases hne0 : a = 0
    · rw [hne0, mul_zero, mul_zero]
    · change a.IsPos at hne0
      by_cases hbeqc : b = c
      · rw [hbeqc]
      · have hltbc  : b < c := by exact ⟨hbc, hbeqc⟩
        have hltabc : b * a < c * a := Nat.mul_gt_mul_of_pos_right hltbc hne0
        exact le_of_lt hltabc

/-- This illustration of the {tactic}`gcongr` tactic is not from the
    textbook. -/
example (a b c d:Nat) (hab: a ≤ b) : c*a*d ≤ c*b*d := by
  gcongr
  . exact d.zero_le
  exact c.zero_le

/-- Proposition 2.3.9 (Euclid's division lemma) / Exercise 2.3.5
Compare with Mathlib's {name}`Nat.mod_eq_iff` -/
theorem Nat.exists_div_mod (n:Nat) {q: Nat} (hq: q.IsPos) :
    ∃ m r: Nat, 0 ≤ r ∧ r < q ∧ n = m * q + r := by
  induction n with
  | zero      =>
    use 0, 0
    constructor
    · exact zero_le 0
    · constructor
      · constructor
        · exact zero_le q
        · symm; exact hq
      · change 0 = 0 * q + 0
        rw [zero_mul, add_zero]
  | succ k ih =>
    obtain ⟨m, r, ⟨h1, h2, h3⟩⟩ := ih
    have hle : r + 1 ≤ q := by
      have := (Nat.lt_iff_succ_le r q).mp h2
      rw [succ_eq_add_one] at this
      exact this
    have hcases := (Nat.le_iff_lt_or_eq (r + 1) q).mp hle
    rcases hcases with (hr1 | hr2)
    · use m, r + 1
      constructor
      · exact zero_le (r + 1)
      · constructor
        · exact hr1
        · calc k++ = (m * q + r)++   := by rw [h3]
                 _ = m * q + r++     := by rw [add_succ (m * q) r]
                 _ = m * q + (r + 1) := by rw [succ_eq_add_one]
    · use m+1, 0
      constructor
      · exact zero_le 0
      · constructor
        · exact lt_of_le_of_lt h1 h2
          -- ⊢ k++ = (m + 1) * q + 0
        · calc k++ = (m * q + r)++   := by rw [h3]
                 _ = m * q + r++     := by rw [add_succ (m * q) r]
                 _ = m * q + (r + 1) := by rw [succ_eq_add_one]
                 _ = m * q + q       := by rw [hr2]
                 _ = m++ * q         := by rw [succ_mul]
                 _ = (m + 1) * q     := by rw [succ_eq_add_one]
                 _ = (m + 1) * q + 0 := by rw [add_zero]


/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
abbrev Nat.pow (m n: Nat) : Nat := Nat.recurse (fun _ prod ↦ prod * m) 1 n

instance Nat.instPow : HomogeneousPow Nat where
  pow := Nat.pow

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_zero` -/
@[simp]
theorem Nat.pow_zero (m: Nat) : m ^ (0:Nat) = 1 := recurse_zero (fun _ prod ↦ prod * m) _

/-- Definition 2.3.11 (Exponentiation for natural numbers) -/
@[simp]
theorem Nat.zero_pow_zero : (0:Nat) ^ 0 = 1 := recurse_zero (fun _ prod ↦ prod * 0) _

/-- Definition 2.3.11 (Exponentiation for natural numbers)
Compare with Mathlib's {name}`Nat.pow_succ` -/
theorem Nat.pow_succ (m n: Nat) : (m:Nat) ^ n++ = m^n * m :=
  recurse_succ (fun _ prod ↦ prod * m) _ _

/-- Compare with Mathlib's {name}`Nat.pow_one` -/
@[simp]
theorem Nat.pow_one (m: Nat) : m ^ (1:Nat) = m := by
  rw [←zero_succ, pow_succ]; simp

/-- Exercise 2.3.4-/
theorem Nat.sq_add_eq (a b: Nat) :
    (a + b) ^ (2 : Nat) = a ^ (2 : Nat) + 2 * a * b + b ^ (2 : Nat) := by
  calc (a + b) ^ 2
     = (a + b) * (a + b)               := by exact pow_two (a + b)
   _ = a * (a + b) + b * (a + b)       := by exact add_mul a b (a + b)
   _ = (a * a + a * b) + b * (a + b)   := by rw [mul_add a a b]
   _ = a^2 + a * b + b * (a + b)       := by rw [pow_two a]
   _ = a^2 + a * b + (b * a + b * b)   := by rw [mul_add b a b]
   _ = a^2 + a * b + (b * a + b^2)     := by rw [pow_two b]
   _ = a^2 + a * b + (a * b + b^2)     := by rw [mul_comm]
   _ = a^2 + (a * b + a * b) + b^2     := by abel
   _ = a^2 + (0 + a * b + a * b) + b^2 := by rw [zero_add]
   _ = a^2 + 2 * (a * b) + b^2         := by rw [← two_mul (a * b)]
   _ = a^2 + (2 * a * b) + b^2         := by rw [mul_assoc]

#check Nat.two_mul
end Chapter2
