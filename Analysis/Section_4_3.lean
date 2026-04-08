import Mathlib.Tactic

/-!
# Analysis I, Section 4.3: Absolute value and exponentiation

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Basic properties of absolute value and exponentiation on the rational numbers (here we use the
  Mathlib rational numbers {lean}`ℚ` rather than the Section 4.2 rational numbers).

Note: to avoid notational conflict, we are using the standard Mathlib definitions of absolute
value and exponentiation.  As such, it is possible to solve several of the exercises here rather
easily using the Mathlib API for these operations.  However, the spirit of the exercises is to
solve these instead using the API provided in this section, as well as more basic Mathlib API for
the rational numbers that does not reference either absolute value or exponentiation.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


/--
  This definition needs to be made outside of the Section 4.3 namespace for technical reasons.
-/
def Rat.Close (ε : ℚ) (x y:ℚ) := |x-y| ≤ ε


namespace Section_4_3

/-- Definition 4.3.1 (Absolute value) -/
abbrev abs (x:ℚ) : ℚ := if x > 0 then x else (if x < 0 then -x else 0)

theorem abs_of_pos {x: ℚ} (hx: 0 < x) : abs x = x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_neg {x: ℚ} (hx: x < 0) : abs x = -x := by grind

/-- Definition 4.3.1 (Absolute value) -/
theorem abs_of_zero : abs 0 = 0 := rfl

/--
  (Not from textbook) This definition of absolute value agrees with the Mathlib one.
  Henceforth we use the Mathlib absolute value.
-/
theorem abs_eq_abs (x: ℚ) : abs x = |x| := by
  rcases lt_trichotomy x 0 with (hlt | heq | hgt)
  · grind
  · grind
  · grind


abbrev dist (x y : ℚ) := |x - y|

/--
  Definition 4.2 (Distance).
  We avoid the Mathlib notion of distance here because it is real-valued.
-/
theorem dist_eq (x y: ℚ) : dist x y = |x-y| := rfl

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_nonneg (x: ℚ) : |x| ≥ 0 := by
  rcases lt_trichotomy x 0 with (hlt | heq | hgt)
  · grind
  · grind
  · grind

/-- Proposition 4.3.3(a) / Exercise 4.3.1 -/
theorem abs_eq_zero_iff (x: ℚ) : |x| = 0 ↔ x = 0 := by
  constructor
  · intro habs0
    rcases lt_trichotomy x 0 with  (hlt | heq | hgt)
    · have fact : 0 < |x| := by exact abs_pos_of_neg hlt
      exact absurd habs0 (ne_of_gt fact)
    · exact heq
    · have fact : 0 < |x| := by exact abs_pos_of_pos hgt
      exact absurd habs0 (ne_of_gt fact)
  · intro hx0
    rw [hx0]
    simp


/-- Proposition 4.3.3(b) / Exercise 4.3.1 -/
theorem abs_add (x y:ℚ) : |x + y| ≤ |x| + |y| := by
  by_cases h : 0 ≤ x + y
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · push_neg at h
    have h' := _root_.abs_of_neg h
    rw [h']
    linarith [neg_le_abs x, neg_le_abs y]

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem abs_le_iff (x y:ℚ) : -y ≤ x ∧ x ≤ y ↔ |x| ≤ y := by
  constructor
  · intro ⟨hle, hge⟩
    rw [abs_eq_max_neg]
    apply max_le
    · exact hge
    · linarith only [hle]
  · intro h
    rw [abs_eq_max_neg] at h
    have hl : x ≤ y := by exact le_of_max_le_left h
    have hr : -x ≤ y := by exact le_of_max_le_right h
    constructor
    · linarith only [hr]
    · exact hl

/-- Proposition 4.3.3(c) / Exercise 4.3.1 -/
theorem le_abs (x:ℚ) : -|x| ≤ x ∧ x ≤ |x| := by
  constructor
  · rw [abs_eq_max_neg]
    suffices h : max x (-x) ≥ -x by linarith
    exact le_max_right x (-x)
  · rw [abs_eq_max_neg]
    exact le_max_left x (-x)

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_mul (x y:ℚ) : |x * y| = |x| * |y| := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · have hxy    : 0 ≤ x * y       := by exact _root_.mul_nonneg hx hy
      have hxabs  : |x| = x         := by exact _root_.abs_of_nonneg hx
      have hyabs  : |y| = y         := by exact _root_.abs_of_nonneg hy
      have hxyabs : |x * y| = x * y := by exact _root_.abs_of_nonneg hxy
      rw [hxabs, hyabs, hxyabs]
    · push_neg at hy
      have hxy    : x * y ≤ 0          := by nlinarith
      have hxabs  : |x| = x            := by exact _root_.abs_of_nonneg hx
      have hyabs  : |y| = -y           := by exact _root_.abs_of_neg hy
      have hxyabs : |x * y| = -(x * y) := by exact _root_.abs_of_nonpos hxy
      rw [hxabs, hyabs, hxyabs]
      ring
  · by_cases hy : 0 ≤ y
    · push_neg at hx
      have hxy    : x * y ≤ 0          := by nlinarith
      have hxabs  : |x| = -x           := by exact _root_.abs_of_neg hx
      have hyabs  : |y| = y            := by exact _root_.abs_of_nonneg hy
      have hxyabs : |x * y| = -(x * y) := by exact _root_.abs_of_nonpos hxy
      rw [hxabs, hyabs, hxyabs]
      ring
    · push_neg at hx hy
      have hxy    : 0 < x * y := by nlinarith
      have hxabs  : |x| = -x         := by exact _root_.abs_of_neg hx
      have hyabs  : |y| = -y         := by exact _root_.abs_of_neg hy
      have hxyabs : |x * y| = x * y  := by exact _root_.abs_of_pos hxy
      rw [hxabs, hyabs, hxyabs]
      ring

/-- Proposition 4.3.3(d) / Exercise 4.3.1 -/
theorem abs_neg (x:ℚ) : |-x| = |x| := by
  have fact : -x = -1 * x := by exact neg_eq_neg_one_mul x
  rw [fact]
  rw [abs_mul]
  norm_num

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_nonneg (x y:ℚ) : dist x y ≥ 0 := by
  rw [dist]
  apply abs_nonneg

/-- Proposition 4.3.3(e) / Exercise 4.3.1 -/
theorem dist_eq_zero_iff (x y:ℚ) : dist x y = 0 ↔ x = y := by
  rw [dist]
  constructor
  · intro h
    rw [abs_eq_zero_iff (x-y)] at h
    linarith [h]
  · intro h
    have fact : x - y = 0 := by linarith [h]
    rw [fact]
    norm_num

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_symm (x y:ℚ) : dist x y = dist y x := by
  rw [dist, dist]
  have fact : x - y = (-1) * (y - x) := by linarith
  rw [fact]
  rw [abs_mul]
  norm_num

/-- Proposition 4.3.3(f) / Exercise 4.3.1 -/
theorem dist_le (x y z:ℚ) : dist x z ≤ dist x y + dist y z := by
  rw [dist, dist, dist]
  have fact : x - z = (x - y) + (y - z) := by linarith
  rw [fact]
  apply abs_add (x - y) (y - z)

/--
  Definition 4.3.4 (eps-closeness).  In the text the notion is undefined for ε zero or negative,
  but it is more convenient in Lean to assign a "junk" definition in this case.  But this also
  allows some relaxations of hypotheses in the lemmas that follow.
-/
theorem close_iff (ε x y:ℚ): ε.Close x y ↔ |x - y| ≤ ε := by rfl

/-- Examples 4.3.6 -/
example : (0.1:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [Rat.Close]
  norm_num

/-- Examples 4.3.6 -/
example : ¬ (0.01:ℚ).Close (0.99:ℚ) (1.01:ℚ) := by
  rw [Rat.Close]
  norm_num

/-- Examples 4.3.6 -/
example (ε : ℚ) (hε : ε > 0) : ε.Close 2 2 := by
  rw [Rat.Close]
  norm_num
  linarith

theorem close_refl (x:ℚ) : (0:ℚ).Close x x := by
  rw [Rat.Close]
  norm_num

/-- Proposition 4.3.7(a) / Exercise 4.3.2 -/
theorem eq_if_close (x y:ℚ) : x = y ↔ ∀ ε:ℚ, ε > 0 → ε.Close x y := by
  constructor
  · intro heq ε hε
    rw [Rat.Close]
    rw [heq]
    norm_num
    linarith
  · intro hclose
    by_contra hneq
    change x ≠ y at hneq
    have fact : 0 < |x - y| := by exact abs_sub_pos.mpr hneq
    specialize hclose (|x - y| / 2) (by positivity)
    rw [Rat.Close] at hclose
    linarith [hclose]

/-- Proposition 4.3.7(b) / Exercise 4.3.2 -/
theorem close_symm (ε x y:ℚ) : ε.Close x y ↔ ε.Close y x := by
  constructor
  · intro hxy
    rw [Rat.Close] at *
    calc |y - x| = |(-1) * (x - y)| := by congr; linarith
               _ = |(-1)| * |x - y| := by exact abs_mul (-1) (x - y)
               _ = |x - y|          := by norm_num
               _ ≤ ε                := hxy
  · intro hyx
    rw [Rat.Close] at *
    calc |x - y| = |(-1) * (y - x)| := by congr; linarith
               _ = |(-1)| * |y - x| := by exact abs_mul (-1) (y - x)
               _ = |y - x|          := by norm_num
               _ ≤ ε                := hyx

/-- Proposition 4.3.7(c) / Exercise 4.3.2 -/
theorem close_trans {ε δ x y z:ℚ} (hxy: ε.Close x y) (hyz: δ.Close y z) :
    (ε + δ).Close x z := by
      rw [Rat.Close] at *
      calc |x - z| = |x - y + (y - z)| := by congr; linarith
                 _ ≤ |x - y| + |y - z| := by exact abs_add (x - y) (y - z)
                 _ ≤ ε + δ             := by linarith [hxy, hyz]

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem add_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x+z) (y+w) := by
    rw [Rat.Close] at *
    calc |x + z - (y + w)| = |x - y + (z - w)| := by congr; linarith
                         _ ≤ |x - y| + |z - w| := by exact abs_add (x - y) (z - w)
                         _ ≤ ε + δ             := by linarith [hxy, hzw]

/-- Proposition 4.3.7(d) / Exercise 4.3.2 -/
theorem sub_close {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε + δ).Close (x-z) (y-w) := by
    rw [Rat.Close] at *
    calc |x - z - (y - w)|
       = |x - y + (w - z)|  := by congr; linarith
     _ ≤ |x - y| + |w - z|  := by exact abs_add (x - y) (w - z)
     _ = |x - y| + |z - w|  := by apply congrArg (|x - y| + ·); exact dist_symm w z
     _ ≤ ε + δ              := by linarith [hxy, hzw]

/-- Proposition 4.3.7(e) / Exercise 4.3.2, slightly strengthened -/
theorem close_mono {ε ε' x y:ℚ} (hxy: ε.Close x y) (hε: ε' ≥  ε) :
    ε'.Close x y := by
    rw [Rat.Close] at *
    calc |x - y| ≤ ε  := by exact hxy
               _ ≤ ε' := by exact hε

/-- Proposition 4.3.7(f) / Exercise 4.3.2 -/
theorem close_between {ε x y z w:ℚ} (hxy: ε.Close x y) (hxz: ε.Close x z)
  (hbetween: (y ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ y)) : ε.Close x w := by
  rw [Rat.Close] at *
  rw [abs_le] at *
  rcases hbetween with (⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩)
  · constructor <;> linarith
  · constructor <;> linarith


/-- Proposition 4.3.7(g) / Exercise 4.3.2 -/
theorem close_mul_right {ε x y z:ℚ} (hxy: ε.Close x y) :
    (ε*|z|).Close (x * z) (y * z) := by
    rw [Rat.Close] at *
    calc |x * z - y * z| = |(x - y) * z|   := by congr; linarith
                       _ = |(x - y)| * |z| := by exact abs_mul (x - y) z
                       _ ≤ ε * |z|         := by nlinarith [abs_nonneg z]

/-- Proposition 4.3.7(h) / Exercise 4.3.2 -/
theorem close_mul_mul {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|x|+ε*δ).Close (x * z) (y * w) := by
  -- The proof is written to follow the structure of the original text, though
  -- non-negativity of ε and δ are implied and don't need to be provided as
  -- explicit hypotheses.
  have hε : ε ≥ 0 := le_trans (abs_nonneg _) hxy
  set a := y-x
  have ha : y = x + a := by grind
  have haε: |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
  set b := w-z
  have hb : w = z + b := by grind
  have hbδ: |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
  have : y*w = x * z + a * z + x * b + a * b := by grind
  rw [close_symm, close_iff]
  calc
    _ = |a * z + b * x + a * b| := by grind
    _ ≤ |a * z + b * x| + |a * b| := abs_add _ _
    _ ≤ |a * z| + |b * x| + |a * b| := by grind [abs_add]
    _ = |a| * |z| + |b| * |x| + |a| * |b| := by grind [abs_mul]
    _ ≤ _ := by gcongr

/-- This variant of Proposition 4.3.7(h) was not in the textbook, but can be useful
in some later exercises. -/
theorem close_mul_mul' {ε δ x y z w:ℚ} (hxy: ε.Close x y) (hzw: δ.Close z w) :
    (ε*|z|+δ*|y|).Close (x * z) (y * w) := by
    have hε : 0 ≤ ε := le_trans (abs_nonneg _) hxy
    set a := y - x
    have ha : y = x + a := by linarith
    have haε : |a| ≤ ε := by rwa [close_symm, close_iff] at hxy
    set b := w - z
    have hb : w = z + b := by linarith
    have hbδ : |b| ≤ δ := by rwa [close_symm, close_iff] at hzw
    have : y * w = x * z + a * z + x * b + a * b := by nlinarith
    rw [close_symm, close_iff]
    calc
      _ = |a * z + (x * b + a * b)|   := by congr; linarith
      _ = |a * z + (x + a) * b|       := by congr; linarith
      _ ≤ |a * z| + |(x + a) * b|     := by exact abs_add (a * z) ((x + a) * b)
      _ = |a| * |z| + |(x + a)| * |b| := by rw [abs_mul a z, abs_mul (x+a) b]
      _ = |a| * |z| + |y| * |b|       := by rw [ha]
      _ ≤ (|a| * |z|) + (|y| * |b|)   := by linarith
      _ ≤ (ε * |z|) + (|y| * δ)       := by gcongr
      _ = ε * |z| + δ * |y|           := by linarith

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_zero (x:ℚ) : x^0 = 1 := _root_.pow_zero x

example : (0:ℚ)^0 = 1 := pow_zero 0

/-- Definition 4.3.9 (exponentiation).  Here we use the Mathlib definition.-/
lemma pow_succ (x:ℚ) (n:ℕ) : x^(n+1) = x^n * x := _root_.pow_succ x n

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_add (x:ℚ) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' n with n ih
  · rw [pow_zero, one_mul, zero_add]
  · rw [pow_succ, mul_comm (x^n) x, mul_assoc, ih, mul_comm x, ← pow_succ]
    congr 1
    linarith

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_mul (x:ℚ) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with m hm
  · rw [mul_zero, pow_zero, pow_zero]
  · rw [pow_succ, hm, pow_add, ← Nat.mul_succ n m]

/-- Proposition 4.3.10(a) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem mul_pow (x y:ℚ) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with n ih
  · repeat rw [pow_zero]
    rw [one_mul]
  · rw [pow_succ, ih]
    have fact : x ^ n * y ^ n * (x * y) = x^n * x * (y^n * y) := by linarith
    rw [fact, ← pow_succ, ← pow_succ]

lemma ne_zero_pow_ne_zero (x : ℚ) (n : ℕ) (hx : x ≠ 0) : x ^ n ≠ 0 := by
  induction' n with n ih
  · rw [pow_zero]; simp
  · rw [pow_succ]
    intro heq0
    rcases mul_eq_zero.mp heq0 with (hf | hf)
    · exact absurd hf ih
    · exact absurd hf hx

/-- Proposition 4.3.10(b) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_eq_zero (x:ℚ) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  · intro hpow0
    by_contra heq0
    push_neg at heq0
    exact absurd hpow0 (ne_zero_pow_ne_zero x n heq0)
  · intro hx0
    have hneq0 : n ≠ 0 := by linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hneq0
    rw [hm, pow_succ, hx0, mul_zero]


/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_nonneg {x:ℚ} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with n ih
  · rw [pow_zero]
    norm_num
  · rw [pow_succ]
    nlinarith

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_pos {x:ℚ} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with n ih
  · rw [pow_zero]
    norm_num
  · rw [pow_succ]
    nlinarith

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_ge_pow (x y:ℚ) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  · rw [pow_zero, pow_zero]
  · rw [pow_succ, pow_succ]
    gcongr
    · exact pow_nonneg n (by linarith)

/-- Proposition 4.3.10(c) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_gt_pow (x y:ℚ) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
  induction' n with n ih
  · absurd hn
    exact lt_irrefl 0
  · by_cases hn0 : n = 0
    · rw [hn0]
      rw [zero_add, pow_one, pow_one]
      exact hxy
    · have hnge0 : 0 < n := by exact Nat.zero_lt_of_ne_zero hn0
      specialize ih hnge0
      rw [pow_succ, pow_succ]
      gcongr

/-- Proposition 4.3.10(d) (Properties of exponentiation, I) / Exercise 4.3.3 -/
theorem pow_abs (x:ℚ) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  · rw [pow_zero, pow_zero]
    norm_num
  · rw [pow_succ, pow_succ, ih, abs_mul]

/--
  Definition 4.3.11 (Exponentiation to a negative number).
  Here we use the Mathlib notion of integer exponentiation
-/
theorem zpow_neg (x:ℚ) (n:ℕ) : x^(-(n:ℤ)) = 1/(x^n) := by simp

example (x:ℚ): x^(-3:ℤ) = 1/(x^3) := zpow_neg x 3

example (x:ℚ): x^(-3:ℤ) = 1/(x*x*x) := by convert zpow_neg x 3; ring

theorem pow_eq_zpow (x:ℚ) (n:ℕ): x^(n:ℤ) = x^n := zpow_natCast x n

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_add (x:ℚ) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  cases n with
  | ofNat n   =>
    cases m with
    | ofNat m   =>
      simp only [Int.ofNat_eq_natCast]
      exact pow_add x m n
    | negSucc m =>
      simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
      rw [show (↑m + 1 : ℤ) = ↑(m+1) by push_cast; ring]
      rw [zpow_neg]
      by_cases h : n ≤ m
      · rw [show (↑n : ℤ) + -↑(m+1) = -↑(m+1-n) by push_cast; omega]
        field_simp [hx]
        rw [zpow_neg, pow_eq_zpow, ← zpow_natCast x (m+1)]
        rw [← pow_eq_zpow x n]
        rw [← zpow_neg x (m+1-n)]
        rw [zpow_neg]
        rw [one_div, ← div_eq_mul_inv]
        rw [pow_eq_zpow x (m+1)]
        rw [eq_div_iff (pow_ne_zero (m+1-n) hx)]
        rw [pow_eq_zpow x n]
        rw [pow_add]
        congr 1
        · omega
      · sorry
  | negSucc n' =>
    cases m with
    | ofNat m'   => sorry
    | negSucc m' => sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_mul (x:ℚ) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  sorry

/-- Proposition 4.3.12(a) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem mul_zpow (x y:ℚ) (n:ℤ) : (x*y)^n = x^n * y^n := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_pos {x:ℚ} (n:ℤ) (hx: x > 0) : x^n > 0 := by sorry

/-- Proposition 4.3.12(b) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_ge_zpow {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by sorry

theorem zpow_ge_zpow_ofneg {x y:ℚ} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  sorry

/-- Proposition 4.3.12(c) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_inj {x y:ℚ} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  sorry

/-- Proposition 4.3.12(d) (Properties of exponentiation, II) / Exercise 4.3.4 -/
theorem zpow_abs (x:ℚ) (n:ℤ) : |x|^n = |x^n| := by sorry

/-- Exercise 4.3.5 -/
theorem two_pow_geq (N:ℕ) : 2^N ≥ N := by sorry
