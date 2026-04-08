import Mathlib.Tactic

/-!
# Analysis I, Section 4.4: gaps in the rational numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Irrationality of √2, and related facts about the rational numbers

Many of the results here can be established more quickly by relying more heavily on the Mathlib
API; one can set oneself the exercise of doing so.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Proposition 4.4.1 (Interspersing of integers by rationals) / Exercise 4.4.1 -/
theorem Rat.between_int (x:ℚ) : ∃! n:ℤ, n ≤ x ∧ x < n+1 := by
  use ⌊x⌋
  constructor
  · constructor
    · exact Rat.floor_le x
    · norm_cast
      exact Rat.lt_floor_add_one x
  · intro m ⟨h₁, h₂⟩
    apply le_antisymm
    · exact Int.le_floor.mpr h₁
    · exact Int.floor_le_iff.mpr h₂

theorem Nat.exists_gt (x:ℚ) : ∃ n:ℕ, n > x := by
  obtain ⟨n, ⟨⟨hn₁, hn₂⟩, _⟩⟩ := x.between_int
  cases n with
  | ofNat n'   =>
    use n' + 1
    norm_cast at hn₂
  | negSucc n' =>
    use 0
    simp [Int.negSucc_eq] at hn₂
    have h0 : (-n' : ℤ) ≤ (0 : ℚ) := by
      norm_cast
      linarith
    norm_cast at hn₂
    push_cast
    linarith

/-- Proposition 4.4.3 (Interspersing of rationals) -/
theorem Rat.exists_between_rat {x y:ℚ} (h: x < y) : ∃ z:ℚ, x < z ∧ z < y := by
  -- This proof is written to follow the structure of the original text.
  -- The reader is encouraged to find shorter proofs, for instance
  -- using Mathlib's `linarith` tactic.
  use (x+y)/2
  have h' : x/2 < y/2 := by
    rw [show x/2 = x*(1/2) by ring, show y/2 = y*(1/2) by ring]
    apply mul_lt_mul_of_pos_right h; positivity
  constructor
  . convert add_lt_add_right h' (x/2) using 1 <;> ring
  convert add_lt_add_right h' (y/2) using 1 <;> ring

/-- Exercise 4.4.2 (a) -/
theorem Nat.no_infinite_descent : ¬ ∃ a:ℕ → ℕ, ∀ n, a (n+1) < a n := by
  rintro ⟨a, h⟩
  have hge0 : ∀ n, 0 ≤ a n := by
    intro n
    exact zero_le (a n) -- all the elements of the sequence are naturals, so they are greater or equal to 0.
  have hdesc : ∀ k n, a n ≥ k := by
    intro k
    induction' k with k ih
    · exact hge0
    · intro n
      specialize ih (n+1)
      specialize h n
      have fact : k < k + 1 := by linarith
      change k ≤ a (n + 1) at ih
      change k + 1 ≤ a n
      have : k < a n := by
        calc k ≤ a (n + 1) := ih
             _ < a n       := h
      exact add_one_le_iff.mpr this
  specialize hdesc (a 0 + 1) 0
  have weird : a 0 > a 0 := by
          calc a 0 ≥ a 0 + 1 := by exact hdesc
                 _ > a 0     := by exact Nat.lt_add_one (a 0)
  exact Nat.lt_irrefl (a 0) weird


/-- Exercise 4.4.2 (b) -/
def Int.infinite_descent : Decidable (∃ a:ℕ → ℤ, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use (fun n => -n)
  intro n
  simp

/-- Exercise 4.4.2 (b) -/
def Rat.pos_infinite_descent : Decidable (∃ a:ℕ → {x: ℚ // 0 < x}, ∀ n, a (n+1) < a n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isTrue
  use (fun n => ⟨1 / (n + 1 : ℚ), by positivity⟩)
  intro n
  simp
  refine (inv_lt_inv₀ ?_ ?_).mpr ?_
  · positivity
  · positivity
  · linarith

#check even_iff_exists_two_mul
#check odd_iff_exists_bit1

theorem Nat.even_or_odd'' (n:ℕ) : Even n ∨ Odd n := by
  induction' n with n hn
  · left; use 0
  · rcases hn with (hev | hod)
    · obtain ⟨d, hd⟩ := hev
      right
      use d
      rw [hd]
      ring_nf
    · obtain ⟨d, hd⟩ := hod
      left
      use d + 1
      rw [hd]
      ring_nf

theorem Nat.not_even_and_odd (n:ℕ) : ¬ (Even n ∧ Odd n) := by
  rintro ⟨hev, hod⟩
  obtain ⟨d₁, hd₁⟩ := hev
  obtain ⟨d₂, hd₂⟩ := hod
  have hmod₁ : n % 2 = 0 := by
    rw [hd₁]
    rw [← two_mul]
    exact mul_mod_right 2 d₁
  have hmod₂ : n % 2 = 1 := by
    rw [hd₂]
    rw [Nat.add_mod]
    rw [mul_mod_right 2 d₂]
    rw [zero_add]
    rw [one_mod]
  rw [hmod₂] at hmod₁
  norm_num at hmod₁

#check Nat.rec

/-- Proposition 4.4.4 / Exercise 4.4.3  -/
theorem Rat.not_exist_sqrt_two : ¬ ∃ x:ℚ, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra h
  choose x hx using h
  have hnon : x ≠ 0 := by aesop
  wlog hpos : x > 0
  . apply  -- generalize x to the nonneg case
      this -- this : ∀ (x : ℚ), x ^ 2 = 2 → x ≠ 0 → x > 0 → False
      (-x)
      _    -- prove that (-x)^2 = 2
      _    -- prove that x ≠ 0
      (show -x>0 by simp; order) -- prove that -x > 0
      <;> grind
  have hrep : ∃ p q:ℕ, p > 0 ∧ q > 0 ∧ p^2 = 2*q^2 := by
    use x.num.toNat, x.den
    observe hnum_pos : x.num > 0
    observe hden_pos : x.den > 0
    refine ⟨ by simp [hpos], hden_pos, ?_ ⟩
    rw [←num_div_den x] at hx; field_simp at hx
    have hnum_cast : x.num = x.num.toNat := Int.eq_natCast_toNat.mpr (by positivity)
    rw [hnum_cast] at hx; norm_cast at hx; grind
  set P : ℕ → Prop := fun p ↦ p > 0 ∧ ∃ q > 0, p^2 = 2*q^2
  have hP : ∃ p, P p := by aesop
  have hiter (p:ℕ) (hPp: P p) : ∃ q, q < p ∧ P q := by
    obtain hp | hp := p.even_or_odd''
    . rw [even_iff_exists_two_mul] at hp
      obtain ⟨ k, rfl ⟩ := hp
      choose q hpos hq using hPp.2
      have : q^2 = 2 * k^2 := by linarith
      use q; constructor
      . nlinarith
      exact ⟨ hpos, k, by linarith [hPp.1], this ⟩
    have h1 : Odd (p^2) := by
      obtain ⟨d, hd⟩ := hp
      have hdsq := congrArg (λ expr => expr ^ 2) hd; dsimp at hdsq
      conv at hdsq =>
        rhs
        ring_nf
      use (2 * d^2 + 2 * d)
      rw [hdsq]
      ring_nf
    have h2 : Even (p^2) := by
      choose q hpos hq using hPp.2
      rw [even_iff_exists_two_mul]
      use q^2
    observe : ¬(Even (p ^ 2) ∧ Odd (p ^ 2))
    tauto
  classical
  set f : ℕ → ℕ := fun p ↦ if hPp: P p then (hiter p hPp).choose else 0
  have hf (p:ℕ) (hPp: P p) : (f p < p) ∧ P (f p) := by
    simp [f, hPp]; exact (hiter p hPp).choose_spec
  choose p hP using hP
  set a : ℕ → ℕ := Nat.rec p (fun n p ↦ f p)
  have ha (n:ℕ) : P (a n) := by
    induction n with
    | zero => exact hP
    | succ n ih => exact (hf _ ih).2
  have hlt (n:ℕ) : a (n+1) < a n := by
    have : a (n+1) = f (a n) := n.rec_add_one p (fun n p ↦ f p)
    grind
  exact Nat.no_infinite_descent ⟨ a, hlt ⟩


/-- Proposition 4.4.5 -/
theorem Rat.exist_approx_sqrt_two {ε:ℚ} (hε:ε>0) : ∃ x ≥ (0:ℚ), x^2 < 2 ∧ 2 < (x+ε)^2 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! h
  have (n:ℕ): (n*ε)^2 < 2 := by
    induction' n with n hn; simp
    simp [add_mul]
    apply lt_of_le_of_ne (h (n*ε) (by positivity) hn)
    have := not_exist_sqrt_two
    aesop
  choose n hn using Nat.exists_gt (2/ε)
  rw [gt_iff_lt, div_lt_iff₀', mul_comm, ←sq_lt_sq₀] at hn <;> try positivity
  grind

/-- Example 4.4.6 -/
example :
  let ε:ℚ := 1/1000
  let x:ℚ := 1414/1000
  x^2 < 2 ∧ 2 < (x+ε)^2 := by norm_num
