import Mathlib.Tactic
import Analysis.Section_5_5


/-!
# Analysis I, Section 5.6: Real exponentiation, part I

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Exponentiating reals to natural numbers and integers.
- nth roots.
- Raising a real to a rational number.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.6.1 (Exponentiating a real by a natural number). Here we use the
    Mathlib definition coming from {name}`Monoid`. -/

lemma Real.pow_zero (x: Real) : x ^ 0 = 1 := rfl

lemma Real.pow_succ (x: Real) (n:ℕ) : x ^ (n+1) = (x ^ n) * x := rfl

lemma Real.pow_of_coe (q: ℚ) (n:ℕ) : (q:Real) ^ n = (q ^ n:ℚ) := by induction' n with n hn <;> simp

/- The claims below can be handled easily by existing Mathlib API (as `Real` already is known
to be a `Field`), but the spirit of the exercises is to adapt the proofs of
Proposition 4.3.10 that you previously established. -/

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_add (x:Real) (m n:ℕ) : x^n * x^m = x^(n+m) := by
  induction' n with k ih
  · simp_all
  · rw [Real.pow_succ, mul_comm _ x, mul_assoc, ih, mul_comm, ← Real.pow_succ]
    congr 1
    linarith

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.pow_mul (x:Real) (m n:ℕ) : (x^n)^m = x^(n*m) := by
  induction' m with k ih
  · simp_all
  · rw [Real.pow_succ, ih, Real.pow_add]
    congr 1

/-- Analogue of Proposition 4.3.10(a) -/
theorem Real.mul_pow (x y:Real) (n:ℕ) : (x*y)^n = x^n * y^n := by
  induction' n with k ih
  · simp_all
  · rw [Real.pow_succ, ih, Real.pow_succ, Real.pow_succ]
    grind

lemma Real.ne_zero_pow_ne_zero (x : Real) (n : ℕ) (hx : x ≠ 0) : x ^ n ≠ 0 := by
  induction' n with n ih
  · simp
  · rw [Real.pow_succ]
    intro heq0
    rcases mul_eq_zero.mp heq0 with (hf | hf)
    · exact absurd hf ih
    · exact absurd hf hx

/-- Analogue of Proposition 4.3.10(b) -/
theorem Real.pow_eq_zero (x:Real) (n:ℕ) (hn : 0 < n) : x^n = 0 ↔ x = 0 := by
  constructor
  · intro hpow0
    by_contra heq0
    push_neg at heq0
    exact absurd hpow0 (ne_zero_pow_ne_zero x n heq0)
  · intro hx0
    have hneq0 : n ≠ 0 := by linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hneq0
    rw [hm, pow_succ, hx0, mul_zero]

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_nonneg {x:Real} (n:ℕ) (hx: x ≥ 0) : x^n ≥ 0 := by
  induction' n with k ih
  · simp_all
  · rw [pow_succ]
    nlinarith

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_pos {x:Real} (n:ℕ) (hx: x > 0) : x^n > 0 := by
  induction' n with k ih
  · simp_all
  · rw [pow_succ]
    nlinarith

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_ge_pow (x y:Real) (n:ℕ) (hxy: x ≥ y) (hy: y ≥ 0) : x^n ≥ y^n := by
  induction' n with n ih
  · rw [Real.pow_zero, Real.pow_zero]
  · rw [pow_succ, pow_succ]
    gcongr
    · exact Real.pow_nonneg n (by linarith)

/-- Analogue of Proposition 4.3.10(c) -/
theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
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


/-- Analogue of Proposition 4.3.10(d) -/
theorem Real.pow_abs (x:Real) (n:ℕ) : |x|^n = |x^n| := by
  induction' n with n ih
  · rw [pow_zero, pow_zero]
    norm_num
  · rw [pow_succ, pow_succ, ih, abs_mul]


theorem Real.pow_inj {x y:Real} {n:ℕ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases lt_trichotomy x y with (hlt | heq | hgt)
  · have hpow := @Real.pow_gt_pow y x n hlt (by linarith) (by omega)
    linarith
  · exact heq
  · have hpow := @Real.pow_gt_pow x y n hgt (by linarith) (by omega)
    linarith

/-- Definition 5.6.2 (Exponentiating a real by an integer). Here we use the Mathlib definition coming from {name}`DivInvMonoid`. -/
lemma Real.pow_eq_pow (x: Real) (n:ℕ): x ^ (n:ℤ) = x ^ n := by rfl

@[simp]
lemma Real.zpow_zero (x: Real) : x ^ (0:ℤ) = 1 := by rfl

lemma Real.zpow_neg {x:Real} (n:ℕ) : x^(-n:ℤ) = 1 / (x^n) := by simp

lemma Real.zpow_add_nonneg (x:Real) (n m:ℤ) (hn0 : n ≥ 0) (hm0 : m ≥ 0) : x^n * x^m = x^(n+m) := by
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  have hpow := Real.pow_add x m n
  exact_mod_cast hpow

lemma Real.zpow_add_nonneg_neg (x:Real) (n m:ℤ) (hx: x ≠ 0) (hn0 : n ≥ 0) (hm0 : m < 0) : x^n * x^m = x^(n+m) := by
  rw [← neg_neg m]
  set q := -m
  have hqpos : q > 0 := by linarith
  have hqint := @Int.toNat_of_nonneg q (by linarith)
  rw [← hqint]
  set q' := Int.toNat q
  lift n to ℕ using (by omega)
  by_cases hsplit : n ≥ q'
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hsplit
    rw [hd]
    push_cast
    ring_nf
    rw [Real.zpow_neg, ← Real.zpow_add_nonneg x q' d (by omega) (by omega)]
    field_simp
    norm_cast
  · push_neg at hsplit
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hsplit
    rw [add_assoc] at hd
    rw [Real.zpow_neg]
    field_simp
    set d' := d + 1
    rw [hd]
    push_cast
    ring_nf
    rw [Real.zpow_neg]
    field_simp
    rw [Real.pow_eq_pow]

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_add (x:Real) (n m:ℤ) (hx: x ≠ 0): x^n * x^m = x^(n+m) := by
  by_cases hn0 : 0 ≤ n
  · by_cases hm0 : 0 ≤ m
    · exact Real.zpow_add_nonneg x n m hn0 hm0
    · push_neg at hm0
      exact Real.zpow_add_nonneg_neg x n m hx hn0 hm0
  · by_cases hm0 : 0 ≤ m
    · push_neg at hn0
      rw [mul_comm, add_comm]
      exact Real.zpow_add_nonneg_neg x m n hx hm0 hn0
    · push_neg at hn0 hm0
      rw [← neg_neg n, ← neg_neg m, ← neg_add]
      set n' := -n
      set m' := -m
      have hn'pos : n' > 0 := by linarith
      have hm'pos : m' > 0 := by linarith
      have hn'int := @Int.toNat_of_nonneg n' (by linarith)
      have hm'int := @Int.toNat_of_nonneg m' (by linarith)
      rw [← hn'int, ← hm'int]
      set n'' := Int.toNat n'
      set m'' := Int.toNat m'
      rw [Real.zpow_neg, Real.zpow_neg]
      norm_cast
      rw [Real.zpow_neg]
      rw [one_div_mul_one_div]
      rw [Real.pow_add]

lemma Real.zpow_inv (x : Real) (n : ℕ) : (1 / x) ^ n = 1 / (x ^ n) := by
  induction' n with n ih
  · simp_all
  · rw [← Real.pow_add, ih]
    field_simp
    nth_rewrite 2 [← pow_one x]
    rw [Real.pow_add]

lemma Real.zpow_mul_nonneg (x:Real) (n m:ℤ)  (hn0 : n ≥ 0) (hm0 : m ≥ 0) : (x^n)^m = x^(n*m) := by
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  have hpm := Real.pow_mul x m n
  exact_mod_cast hpm

lemma Real.zpow_mul_nonneg_neg (x:Real) (n m:ℤ)  (hn0 : n ≥ 0) (hm0 : m < 0) : (x^n)^m = x^(n*m) := by
  lift n to ℕ using (by omega)
  rw [← neg_neg m]
  set m' := -m
  have hm'pos : m' > 0 := by linarith
  have hm'int := @Int.toNat_of_nonneg m' (by linarith)
  rw [← hm'int]
  set m'' := Int.toNat m'
  rw [Real.zpow_neg, ← Real.pow_eq_pow _ m'', Real.zpow_mul_nonneg x n m'' (by omega) (by omega)]
  norm_cast
  rw [← zpow_neg]
  congr
  grind


lemma Real.zpow_mul_neg_nonneg (x:Real) (n m:ℤ)  (hn0 : n < 0) (hm0 : m ≥ 0) : (x^n)^m = x^(n*m) := by
  lift m to ℕ using (by omega)
  rw [← neg_neg n]
  set n' := -n
  have hn'pos : n' > 0 := by linarith
  have hn'int := @Int.toNat_of_nonneg n' (by linarith)
  rw [← hn'int]
  set n'' := Int.toNat n'
  rw [Real.zpow_neg, Real.pow_eq_pow, Real.zpow_inv, Real.pow_mul, ← Real.zpow_neg]
  congr
  grind

/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.zpow_mul (x:Real) (n m:ℤ) : (x^n)^m = x^(n*m) := by
  by_cases hn0 : 0 ≤ n
  · by_cases hm0 : 0 ≤ m
    · exact Real.zpow_mul_nonneg x n m hn0 hm0
    · push_neg at hm0
      exact Real.zpow_mul_nonneg_neg x n m hn0 hm0
  · by_cases hm0 : 0 ≤ m
    · push_neg at hn0
      exact Real.zpow_mul_neg_nonneg x n m hn0 hm0
    · push_neg at hn0 hm0
      conv =>
        lhs
        rw [← neg_neg n, ← neg_neg m]
      have hmul : n * m = ((-n) * (-m)) := by ring
      rw [hmul]
      set n' := -n
      set m' := -m
      have hn'pos : n' > 0 := by linarith
      have hm'pos : m' > 0 := by linarith
      have hn'int := @Int.toNat_of_nonneg n' (by linarith)
      have hm'int := @Int.toNat_of_nonneg m' (by linarith)
      rw [← hn'int, ← hm'int]
      set n'' := Int.toNat n'
      set m'' := Int.toNat m'
      rw [Real.zpow_neg, Real.zpow_neg]
      rw [Real.zpow_inv]
      rw [← Real.zpow_mul_nonneg x n'' m'' (by omega) (by omega)]
      field_simp
      norm_cast


/-- Analogue of Proposition 4.3.12(a) -/
theorem Real.mul_zpow (x y:Real) (n:ℤ) : (x*y)^n = x^n * y^n := by
  by_cases hn0 : n ≥ 0
  · lift n to ℕ using (by omega)
    have hpow := Real.mul_pow x y n
    exact_mod_cast hpow
  · push_neg at hn0
    rw [← neg_neg n]
    set n' := -n
    have hn'pos : n' > 0 := by linarith
    have hn'int := @Int.toNat_of_nonneg n' (by linarith)
    rw [← hn'int]
    set n'' := Int.toNat n'
    rw [Real.zpow_neg, Real.mul_pow, ← one_div_mul_one_div_rev]
    rw [← Real.zpow_neg, ← Real.zpow_neg]
    rw [mul_comm]

/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_pos {x:Real} (n:ℤ) (hx: x > 0) : x^n > 0 := by
  by_cases hn0 : n ≥ 0
  · lift n to ℕ using (by omega)
    have hpow := Real.pow_pos n hx
    exact_mod_cast hpow
  · push_neg at hn0
    rw [← neg_neg n]
    set n' := -n
    have hn'pos : n' > 0 := by linarith
    have hn'int := @Int.toNat_of_nonneg n' (by linarith)
    rw [← hn'int]
    set n'' := Int.toNat n'
    rw [Real.zpow_neg]
    have hpow := Real.pow_pos n'' hx
    exact one_div_pos.mpr hpow


/-- Analogue of Proposition 4.3.12(b) -/
theorem Real.zpow_ge_zpow {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n > 0): x^n ≥ y^n := by
  lift n to ℕ using (by omega)
  have hpow := Real.pow_ge_pow x y n hxy (by linarith)
  exact_mod_cast hpow

theorem Real.zpow_ge_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x ≥ y) (hy: y > 0) (hn: n < 0) : x^n ≤ y^n := by
  rw [← neg_neg n]
  set n' := -n
  have hn'pos : n' > 0 := by linarith
  have hn'int := @Int.toNat_of_nonneg n' (by linarith)
  rw [← hn'int]
  set n'' := Int.toNat n'
  rw [Real.zpow_neg, Real.zpow_neg]
  have hx : x > 0 := by linarith
  have hxpowpos := Real.zpow_pos n'' hx
  have hypowpos := Real.zpow_pos n'' hy
  field_simp
  have := Real.pow_ge_pow x y n'' hxy (by linarith)
  linarith

theorem Real.zpow_gt_zpow {x y:Real} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n > 0): x^n > y^n := by
  lift n to ℕ using (by omega)
  have hpow := Real.pow_gt_pow x y n hxy (by linarith) (by omega)
  exact_mod_cast hpow

theorem Real.zpow_gt_zpow_ofneg {x y:Real} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n < 0) : x^n < y^n := by
  rw [← neg_neg n]
  set n' := -n
  have hn'pos : n' > 0 := by linarith
  have hn'int := @Int.toNat_of_nonneg n' (by linarith)
  rw [← hn'int]
  set n'' := Int.toNat n'
  rw [Real.zpow_neg, Real.zpow_neg]
  have hx : x > 0 := by linarith
  have hxpowpos := zpow_pos n'' hx
  have hypowpos := zpow_pos n'' hy
  field_simp
  have := pow_gt_pow x y n'' hxy (by linarith) (by omega)
  linarith

/-- Analogue of Proposition 4.3.12(c) -/
theorem Real.zpow_inj {x y:Real} {n:ℤ} (hx: x > 0) (hy : y > 0) (hn: n ≠ 0) (hxy: x^n = y^n) : x = y := by
  rcases n.lt_trichotomy 0 with (hneg | hzero | hpos)
  · by_contra! h'
    rcases lt_trichotomy x y with (hlt | heq | hgt)
    · have hpow := @Real.zpow_gt_zpow_ofneg y x n hlt hx hneg
      linarith
    · exact absurd heq h'
    · have hpow := @Real.zpow_gt_zpow_ofneg x y n hgt hy hneg
      linarith
  · exact absurd hzero hn
  · rcases lt_trichotomy x y with (hlt | heq | hgt)
    · have hpow := @Real.zpow_gt_zpow y x n hlt hx hpos
      linarith
    · exact heq
    · have hpow := @Real.zpow_gt_zpow x y n hgt hy hpos
      linarith


lemma zpow_abs_inv {x : Real} : |1/x| = 1/|x| := by grind

/-- Analogue of Proposition 4.3.12(d) -/
theorem Real.zpow_abs (x:Real) (n:ℤ) : |x|^n = |x^n| := by
  by_cases hn0 : n ≥ 0
  · lift n to ℕ using (by omega)
    have hpow := pow_abs x n
    exact_mod_cast hpow
  · rw [← neg_neg n]
    set n' := -n
    have hn'pos : n' > 0 := by linarith
    have hn'int := @Int.toNat_of_nonneg n' (by linarith)
    rw [← hn'int]
    set n'' := Int.toNat n'
    rw [zpow_neg, zpow_neg]
    grind


lemma Real.pow_mono {x : Real} {n : ℕ} (hx : x > 1)  (hn : n ≥ 1): x ≤ x ^ n := by
  induction n, hn using Nat.le_induction with
  | base          => simp_all
  | succ n hle ih =>
    rw [Real.pow_succ]
    nlinarith


/-- Definition 5.6.2. We permit "junk values" when {lean}`x` is negative or {lean}`n` vanishes. -/
noncomputable abbrev Real.root (x:Real) (n:ℕ) : Real := sSup { y:Real | y ≥ 0 ∧ y^n ≤ x }

noncomputable abbrev Real.sqrt (x:Real) := x.root 2

/-- Lemma 5.6.5 (Existence of n^th roots) -/
theorem Real.rootset_nonempty {x:Real} (hx: x ≥ 0) (n:ℕ) (hn: n ≥ 1) : { y:Real | y ≥ 0 ∧ y^n ≤ x }.Nonempty := by
  use 0
  simp_all
  calc _ = 0 := by exact (pow_eq_zero 0 n hn).mpr rfl
       _ ≤ x := by exact hx

theorem Real.rootset_bddAbove {x:Real} (n:ℕ) (hn: n ≥ 1) : BddAbove { y:Real | y ≥ 0 ∧ y^n ≤ x } := by
  -- This proof is written to follow the structure of the original text.
  rw [_root_.bddAbove_def]
  obtain h | h := le_or_gt x 1
  . use 1; intro y hy; simp at hy
    by_contra! hy'
    replace hy' : 1 < y^n := by
      -- theorem Real.zpow_gt_zpow {x y:Real} {n:ℤ} (hxy: x > y) (hy: y > 0) (hn: n > 0): x^n > y^n := by
      have hpow := Real.pow_gt_pow y 1 n hy' (by linarith) (by linarith)
      norm_num at hpow
      exact hpow
    linarith
  use x; intro y hy; simp at hy
  by_contra! hy'
  replace hy' : x < y^n := by
    calc _ < y   := by exact hy'
         _ ≤ y^n := by exact Real.pow_mono (by linarith) hn
  linarith

/-- Lemma 5.6.6 (ab) / Exercise 5.6.1 -/
lemma helper566point1 {y : Real} {n : ℕ} (hy : y > 0) (hn : n ≥ 1) :
  ∃ (M : Real), M > 0 ∧ (∀ ε : Real, ε > 0 → ε < y → (y - ε)^n ≥ y^n - M * ε) := by
  induction n, hn using Nat.le_induction with
  | base =>
    use 1
    simp
  | succ k hle ih =>
    obtain ⟨M, hMpos, hM⟩ := ih
    use y^k + M * y
    constructor
    · positivity
    · intro ε hεpos hεlt
      specialize hM ε hεpos hεlt
      rw [Real.pow_succ]
      --have hyε : y - ε > 0 := by grind
      calc      (y - ε) ^ k     * (y - ε)
              ≥ (y ^ k - M * ε) * (y - ε)                     := by gcongr; grind
            _ = (y ^ k - M * ε) * y - (y ^ k - M * ε) * ε     := by rw [mul_sub]
            _ = (y ^ k * y - M * ε * y) - (y ^ k - M * ε) * ε := by rw [sub_mul]
            _ = y ^ (k + 1) - M * ε * y - (y ^ k - M * ε )* ε := by rw [Real.pow_succ]
            _ = y ^ (k + 1) + (-M * y - y ^ k + M * ε) * ε    := by ring_nf
            _ ≥ y ^ (k + 1) + (-M * y - y ^ k) * ε            := by gcongr; nlinarith
            _ = y ^ (k + 1) - (y ^ k + M * y) * ε             := by ring_nf

lemma helper566point2 {y : Real} {n : ℕ} (hy : y ≥ 0) (hn : n ≥ 1) :
    ∃ (M : Real), M > 0 ∧ (∀ ε : Real, ε > 0 → ε < 1 → (y + ε)^n ≤ y ^ n + M * ε) := by
  induction n, hn using Nat.le_induction with
  | base =>
    use 1
    simp
  | succ k hle ih =>
    obtain ⟨M, hMpos, hM⟩ := ih
    use (M*y + y^k + M)
    constructor
    · positivity
    · intro ε hεpos hεlt1
      specialize hM ε hεpos hεlt1
      rw [Real.pow_succ]
      calc _ ≤ (y ^ k + M * ε) * (y + ε)                           := by nlinarith
           _ = (y ^ k + M * ε) * y + (y ^ k + M * ε) * ε           := by rw [mul_add]
           _ = (y ^ k + M * ε) * y + ((y ^ k * ε) + (M * ε * ε))   := by congr 1; rw [add_mul]
           _ ≤ (y ^ k + M * ε) * y + ((y ^ k * ε) + (M * ε * 1))   := by gcongr
           _ = (y ^ k + M * ε) * y + ((y ^ k * ε) + (M * ε))       := by rw [mul_one]
           _ = (y ^ k * y + M * ε * y) + ((y ^ k * ε) + (M * ε))   := by congr; rw [add_mul]
           _ = (y ^ k * y) + ((M * y) * ε) + (y ^ k * ε) + (M * ε) := by ring_nf
           _ = y ^ (k+1) + ((M * y) * ε) + (y ^ k * ε) + (M * ε)   := by rw [Real.pow_succ]
           _ = y ^ (k+1) +  (M * y + y ^ k + M) * ε                := by ring_nf

theorem Real.eq_root_if_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n → y^n = x := by
  intro hroot
  rw [Real.root] at hroot
  apply le_antisymm
  · by_contra! h'
    have hy' : y > 0 := by
      by_cases h0 : y = 0
      · rw [h0] at h'
        have : (0: Real) ^ n = 0 := by exact (pow_eq_zero 0 n hn).mpr rfl
        rw [this] at h'
        linarith
      · push_neg at h0
        exact lt_of_le_of_ne hy (id (Ne.symm h0))
    obtain ⟨M, hMpos, hM⟩ := helper566point1 hy' hn
    let ε₁ := min y ((y^ n - x) / M)
    have hε₁pos : 0 < ε₁ := by
      unfold ε₁
      rw [lt_min_iff]
      constructor
      · positivity
      · apply div_pos
        · linarith
        · exact hMpos
    have hε₁gey : ε₁ ≤ y := by grind
    let ε₂ := ε₁ / 2
    have hε₂pos : ε₂ > 0 := by positivity
    have hε₂lty : ε₂ < y := by grind
    have hε₂lt : ε₂ < ((y^ n - x) / M) := by grind
    specialize hM ε₂ hε₂pos hε₂lty
    have hcontra : (y - ε₂) ^ n > x := by
      calc _ ≥ y ^ n - M * ε₂                := by exact hM
            _ > y ^ n - M * ((y ^ n - x) / M) := by gcongr
            _ = x                             := by field_simp; ring_nf
    have hlb : ∀ c ∈ {y | y ≥ 0 ∧ y ^ n ≤ x}, (y - ε₂) ≥ c := by
      intro c hc
      simp at hc
      obtain ⟨hc1, hc2⟩ := hc
      by_contra! h'
      have h'' := Real.pow_gt_pow c (y - ε₂) n h' (by grind) (by grind)
      grind
    have hineq := csSup_le (Real.rootset_nonempty hx n hn) hlb
    rw [← hroot] at hineq
    linarith
  · by_contra! h'
    obtain ⟨M, hMpos, hM⟩ := helper566point2 hy hn
    let ε₁ := min 1 ((x - y ^ n) / M)
    have hε₁pos : 0 < ε₁ := by
      unfold ε₁
      rw [lt_min_iff]
      constructor
      · norm_num
      · apply div_pos
        · linarith
        · exact hMpos
    let ε₂ := ε₁ / 2
    have hε₂pos : ε₂ > 0 := by positivity
    have hε₂lt1 : ε₂ < 1 := by grind
    have hε₂lt : ε₂ < ((x - y ^ n) / M) := by grind
    specialize hM ε₂ hε₂pos hε₂lt1
    have hcontra : (y + ε₂) ^ n < x            := by
      calc _ ≤ y ^ n + M * ε₂                  := by exact hM
            _ < y ^ n + M * ((x - y ^ n) / M)   := by gcongr
            _ = x                               := by field_simp; ring_nf
    have hyε₂mem : y + ε₂ ∈ {y | y ≥ 0 ∧ y ^ n ≤ x} := by
      simp
      constructor <;> grind
    have hineq := le_csSup (Real.rootset_bddAbove n hn) hyε₂mem
    rw [← hroot] at hineq
    linarith [hineq]

theorem Real.eq_root_iff_pow_eq {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  y = x.root n ↔ y^n = x := by
  constructor
  · exact Real.eq_root_if_pow_eq hx hy hn
  · intro hynx
    rw [Real.root]
    apply le_antisymm
    · have hymem : y ∈ {y | y ≥ 0 ∧ y ^ n ≤ x} := by
        simp
        constructor <;> grind
      exact le_csSup (Real.rootset_bddAbove n hn) hymem
    · have hylb :  ∀ z ∈ {y | y ≥ 0 ∧ y ^ n ≤ x}, z ≤ y := by
        intro z hz
        simp at hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [← hynx] at hz2
        by_contra! h'
        have h'' := Real.pow_gt_pow z y n h' hy (by linarith)
        linarith
      exact csSup_le (Real.rootset_nonempty hx n hn) hylb


/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_nonneg {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n ≥ 0 := by
  rw [Real.root]
  have hmem : 0 ∈ {y | y ≥ 0 ∧ y ^ n ≤ x} := by
    simp_all
    have : (0:Real) ^ n = 0 := by exact (pow_eq_zero 0 n hn).mpr rfl
    rw [this]
    exact hx
  exact le_csSup (Real.rootset_bddAbove n hn) hmem


theorem Real.pow_of_root {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x.root n)^n = x := by
  have hrootge0 := Real.root_nonneg hx hn
  exact Real.eq_root_if_pow_eq hx hrootge0 hn rfl

/-- Lemma 5.6.6 (c) / Exercise 5.6.1 -/
theorem Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have h0pow : (0:Real) ^ n = 0 := by exact (pow_eq_zero 0 n hn).mpr rfl
  constructor
  · intro hroot
    -- theorem Real.pow_gt_pow (x y:Real) (n:ℕ) (hxy: x > y) (hy: y ≥ 0) (hn: n > 0) : x^n > y^n := by
    have hpow := Real.pow_gt_pow _ 0 n hroot (by linarith) (by linarith)
    rw [Real.pow_of_root hx hn, h0pow] at hpow
    exact hpow
  · intro hxpos
    have hnonneg := Real.root_nonneg hx hn
    by_contra! h'
    have heq0 : x.root n = 0 := by linarith
    have heq0pow := congrArg (λ expr => expr ^ n) heq0; dsimp at heq0pow
    rw [Real.pow_of_root hx hn, h0pow] at heq0pow
    linarith


theorem Real.root_of_pow {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) :
  (x^n).root n = x := by
  rw [Real.root]
  have hbdd : ∀ z ∈ {y | y ≥ 0 ∧ y ^ n ≤ x ^ n}, z ≤ x := by
    intro z hz
    simp at hz
    obtain ⟨hlb, hub⟩ := hz
    by_contra! h'
    have hpow := Real.pow_gt_pow z x n h' hx (by linarith)
    linarith
  have hxpowge0 : x ^ n ≥ 0 := by positivity
  have hmem : x ∈  {y | y ≥ 0 ∧ y ^ n ≤ x ^ n} := by
    simp
    linarith
  have hbdabve : BddAbove {y | y ≥ 0 ∧ y ^ n ≤ x ^ n} := by
    use x
    intro y hy
    simp at hy
    obtain ⟨hlb, hub⟩ := hy
    by_contra! h'
    have hpow := Real.pow_gt_pow y x n h' hx (by linarith)
    linarith
  apply le_antisymm
  · exact csSup_le (Real.rootset_nonempty hxpowge0 n hn) hbdd
  · exact le_csSup hbdabve hmem

/-- Lemma 5.6.6 (d) / Exercise 5.6.1 -/
theorem Real.root_mono {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : x > y ↔ x.root n > y.root n := by
  constructor
  · intro hxy
    by_contra! h'
    have hpow := Real.pow_ge_pow (y.root n) (x.root n) n h' (Real.root_nonneg hx hn)
    rw [Real.pow_of_root hx hn, Real.pow_of_root hy hn] at hpow
    linarith
  · intro hrootxy
    have hpow := Real.pow_gt_pow (x.root n) (y.root n) n hrootxy (Real.root_nonneg hy hn) (by linarith)
    rw [Real.pow_of_root hx hn, Real.pow_of_root hy hn] at hpow
    exact hpow

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_gt_one {x : Real} (hx: x > 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k < x.root l := by
  by_contra! h'
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
  rw [add_assoc] at hd
  have hpow := Real.pow_ge_pow (x.root k) (x.root l) k h' (Real.root_nonneg (by linarith) hl)
  rw [@Real.pow_of_root x (by linarith) k (by linarith)] at hpow
  rw [hd, ← Real.pow_add] at hpow
  rw [@Real.pow_of_root x (by linarith) l hl] at hpow
  replace hpow : 1 ≥ x.root l ^ (d + 1) := by nlinarith
  replace hpow := Real.pow_ge_pow 1 (x.root l ^ (d+1)) l hpow (Real.pow_nonneg (d+1) (Real.root_nonneg (by linarith) hl))
  rw [one_pow] at hpow
  rw [Real.pow_mul, mul_comm, ← Real.pow_mul] at hpow
  rw [@Real.pow_of_root x (by linarith) l hl] at hpow
  have hpow' := Real.pow_gt_pow x 1 (d+1) hx (by linarith) (by linarith)
  rw [one_pow] at hpow'
  linarith only [hpow, hpow']

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_mono_of_lt_one {x : Real} (hx0: 0 < x) (hx: x < 1) {k l: ℕ} (hkl: k > l) (hl: l ≥ 1) : x.root k > x.root l := by
  by_contra! h'
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
  rw [add_assoc] at hd
  have hpow := Real.pow_ge_pow (x.root l) (x.root k) k h' (Real.root_nonneg (by linarith) (by linarith))
  rw [@Real.pow_of_root x (by linarith) k (by linarith)] at hpow
  rw [hd, ← Real.pow_add] at hpow
  rw [@Real.pow_of_root x (by linarith) l hl] at hpow
  replace hpow : x.root l ^ (d + 1) ≥ 1 := by nlinarith
  replace hpow := Real.pow_ge_pow (x.root l ^ (d+1)) 1 l hpow (by linarith)
  rw [one_pow] at hpow
  rw [Real.pow_mul, mul_comm, ← Real.pow_mul] at hpow
  rw [@Real.pow_of_root x (by linarith) l hl] at hpow
  have hpow' := Real.pow_gt_pow 1 x (d+1) hx (by linarith) (by linarith)
  rw [one_pow] at hpow'
  linarith only [hpow, hpow']

/-- Lemma 5.6.6 (e) / Exercise 5.6.1 -/
theorem Real.root_of_one {k: ℕ} (hk: k ≥ 1): (1:Real).root k = 1 := by
  apply le_antisymm
  · by_contra! h'
    have hpow := Real.pow_gt_pow _ 1 k h' (by linarith) (by linarith)
    rw [@Real.pow_of_root 1 (by linarith) k (by linarith), one_pow] at hpow
    linarith only [hpow]
  · by_contra! h'
    have hpow := Real.pow_gt_pow 1 _ k h' (Real.root_nonneg (by linarith) (by linarith)) (by linarith)
    rw [one_pow, @Real.pow_of_root 1 (by linarith) k (by linarith)] at hpow
    linarith only [hpow]

theorem Real.root_of_zero {k : ℕ}  (hk: k ≥ 1) : (0:Real).root k = 0 := by
  apply le_antisymm
  · by_contra! h'
    have hpow := Real.pow_gt_pow _ 0 k h' (by linarith) (by linarith)
    rw [@Real.pow_of_root 0 (by linarith) k (by linarith), zero_pow (by linarith)] at hpow
    linarith only [hpow]
  · by_contra! h'
    have hpow := Real.pow_gt_pow 0 _ k h' (Real.root_nonneg (by linarith) (by linarith)) (by linarith)
    rw [zero_pow (by linarith), @Real.pow_of_root 0 (by linarith) k (by linarith)] at hpow
    linarith only [hpow]

/-- Lemma 5.6.6 (f) / Exercise 5.6.1 -/
theorem Real.root_mul {x y:Real} (hx: x ≥ 0) (hy: y ≥ 0) {n:ℕ} (hn: n ≥ 1) : (x*y).root n = (x.root n) * (y.root n) := by
  rcases eq_or_lt_of_le hx with (hx0 | hxpos)
  · rw [← hx0, zero_mul, Real.root_of_zero hn, zero_mul]
  · rcases eq_or_lt_of_le hy with (hy0 | hypos)
    · rw [← hy0, mul_zero, Real.root_of_zero hn, mul_zero]
    · -- have hxypos : x * y > 0 := by nlinarith
      have hrtxypos := (@Real.root_pos (x * y) (by nlinarith) n hn).mpr (by nlinarith)
      have hrtxpos := (@Real.root_pos x (by linarith) n hn).mpr hxpos
      have hrtypos := (@Real.root_pos y (by linarith) n hn).mpr hypos
      have hmulpos : x.root n * y.root n > 0 := by nlinarith
      suffices alternatively : (x*y).root n ^ n = ((x.root n) * (y.root n)) ^ n by
        exact Real.pow_inj hrtxypos hmulpos (by linarith) alternatively
      rw [Real.mul_pow]
      rw [
        @Real.pow_of_root (x*y) (by nlinarith) n hn,
        @Real.pow_of_root x     (by  linarith) n hn,
        @Real.pow_of_root y     (by  linarith) n hn,
      ]

/-- Lemma 5.6.6 (g) / Exercise 5.6.1 -/
theorem Real.root_root {x:Real} (hx: x ≥ 0) {n m:ℕ} (hn: n ≥ 1) (hm: m ≥ 1): (x.root n).root m = x.root (n*m) := by
  rcases eq_or_lt_of_le hx with (hx0 | hxpos)
  · rw [← hx0, Real.root_of_zero hn, Real.root_of_zero hm, Real.root_of_zero (by nlinarith)]
  · have hrtnpos   := (@Real.root_pos x (by linarith) n hn).mpr hxpos
    have hrtmrnpos := (@Real.root_pos (x.root n) (by linarith) m hm).mpr hrtnpos
    have hrtmnpos  := (@Real.root_pos x (by linarith) (n*m) (by nlinarith)).mpr hxpos
    suffices alternatively : (x.root n).root m  ^ (n*m) = x.root (n * m) ^ (n*m) by
        exact Real.pow_inj hrtmrnpos hrtmnpos (by nlinarith) alternatively
    nth_rewrite 1 [mul_comm n m, ← @Real.pow_mul ((x.root n).root m) n m]
    rw [
        @Real.pow_of_root (x.root n) (by linarith) m     hm,
        @Real.pow_of_root x          (by linarith) n     hn,
        @Real.pow_of_root x          (by linarith) (n*m) (by nlinarith),
    ]

theorem Real.root_one {x:Real} (hx: x > 0): x.root 1 = x := by
  have hrtpos := (@Real.root_pos x (by linarith) 1 (by linarith)).mpr hx
  suffices alternatively : (x.root 1) ^ 1 = x ^ 1 by
    exact Real.pow_inj hrtpos (by linarith) (by linarith) alternatively
  rw [@Real.pow_of_root x (by linarith) 1 (by linarith), pow_one]

theorem Real.pow_cancel {y z:Real} (hy: y > 0) (hz: z > 0) {n:ℕ} (hn: n ≥ 1)
  (h: y^n = z^n) : y = z := by
  exact Real.pow_inj hy hz (by linarith) h

example : ¬(∀ (y:Real) (z:Real) (n:ℕ) (_: n ≥ 1) (_: y^n = z^n), y = z) := by
  simp; refine ⟨ (-3), 3, 2, ?_, ?_, ?_ ⟩ <;> norm_num

/-- Definition 5.6.7 -/
noncomputable abbrev Real.ratPow (x:Real) (q:ℚ) : Real := (x.root q.den)^(q.num)

noncomputable instance Real.instRatPow : Pow Real ℚ where
  pow x q := x.ratPow q

theorem Rat.eq_quot (q:ℚ) : ∃ a:ℤ, ∃ b:ℕ, b > 0 ∧ q = a / b := by
  use q.num, q.den; have := q.den_nz
  refine ⟨ by omega, (Rat.num_div_den q).symm ⟩

/-- Lemma 5.6.8 -/
theorem Real.pow_root_eq_pow_root {a a':ℤ} {b b':ℕ} (hb: b > 0) (hb' : b' > 0)
  (hq : (a/b:ℚ) = (a'/b':ℚ)) {x:Real} (hx: x > 0) :
    (x.root b')^(a') = (x.root b)^(a) := by
  -- This proof is written to follow the structure of the original text.
  wlog ha: a > 0 generalizing a b a' b'
  . simp at ha
    obtain ha | ha := le_iff_lt_or_eq.mp ha
    . replace hq : ((-a:ℤ)/b:ℚ) = ((-a':ℤ)/b':ℚ) := by
        push_cast at *; ring_nf at *; simp [hq]
      specialize this hb hb' hq (by linarith)
      simpa [zpow_neg] using this
    have : a' = 0 := by
      rw [ha] at hq
      simp at hq
      symm at hq
      rw [div_eq_zero_iff] at hq
      rcases hq with (hq | hq)
      · exact_mod_cast hq
      · have : b' = 0 := by exact_mod_cast hq
        linarith
    simp_all
  have : a' > 0 := by
    field_simp at hq
    by_contra! h'
    have hab' : (a : ℚ) * (b' : ℚ) > 0 := by positivity
    have hba' : (b : ℚ) * (a' : ℚ) ≤ 0 := by
      qify at hb h'
      nlinarith
    linarith
  field_simp at hq
  lift a to ℕ using by order
  lift a' to ℕ using by order
  norm_cast at *
  set y := x.root (a*b')
  have h1 : y = (x.root b').root a := by rw [root_root, mul_comm] <;> linarith
  have h2 : y = (x.root b).root a' := by rw [root_root, ←hq] <;> linarith
  have h3 : y^a = x.root b' := by rw [h1]; apply pow_of_root (root_nonneg _ _) <;> linarith
  have h4 : y^a' = x.root b := by rw [h2]; apply pow_of_root (root_nonneg _ _) <;> linarith
  rw [←h3, pow_mul, mul_comm, ←pow_mul, h4]

theorem Real.ratPow_def {x:Real} (hx: x > 0) (a:ℤ) {b:ℕ} (hb: b > 0) : x^(a/b:ℚ) = (x.root b)^a := by
  set q := (a/b:ℚ)
  convert pow_root_eq_pow_root hb _ _ hx
  . have := q.den_nz; omega
  rw [Rat.num_div_den q]


theorem Real.ratPow_eq_root {x:Real} (hx: x > 0) {n:ℕ} (hn: n ≥ 1) : x^(1/n:ℚ) = x.root n := by
  -- have f1 : x.root n = x.root n ^ (1 : ℕ) := by exact Eq.symm (pow_one (x.root n))
  have hdef := @Real.ratPow_def x hx 1 n hn
  rw [zpow_one] at hdef
  push_cast at hdef
  exact hdef

theorem Real.ratPow_eq_pow {x:Real} (hx: x > 0) (n:ℤ) : x^(n:ℚ) = x^n := by
  have hdef := @Real.ratPow_def x hx n 1 (by linarith)
  simp at hdef
  rwa [Real.root_one hx] at hdef

/-- Lemma 5.6.9(a) / Exercise 5.6.2 -/
theorem Real.ratPow_pos {x:Real} (hx: x > 0) (q:ℚ) : x^q > 0 := by
  obtain ⟨n, d, hdpos, hq⟩ := Rat.eq_quot q
  rw [hq]
  rw [@Real.ratPow_def x hx n d hdpos]
  have hrtpos := (@Real.root_pos x (by linarith) d (by linarith)).mpr hx
  exact Real.zpow_pos n hrtpos

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_add {x:Real} (hx: x > 0) (q r:ℚ) : x^(q+r) = x^q * x^r := by
  obtain ⟨n₁, d₁, hd₁pos, hq₁⟩ := Rat.eq_quot q
  obtain ⟨n₂, d₂, hd₂pos, hq₂⟩ := Rat.eq_quot r
  have hq₁' : q = ((n₁ * d₂):ℤ) / ((d₁ * d₂):ℕ) := by
    norm_cast at hq₁ ⊢
    rw [hq₁]
    rw [Rat.divInt_eq_divInt_iff]
    · conv =>
        rhs
        rw [mul_assoc]
      congr 1
      norm_cast
      ring_nf
    · nlinarith
    · norm_cast
      push_neg
      nlinarith
  have hq₂' : r = ((n₂ * d₁):ℤ) / ((d₁ * d₂):ℕ) := by
    norm_cast at hq₂ ⊢
    rw [hq₂]
    rw [Rat.divInt_eq_divInt_iff]
    · conv =>
        rhs
        rw [mul_assoc]
      congr 1
    · nlinarith
    · norm_cast
      push_neg
      nlinarith
  nth_rewrite 2 [hq₁', hq₂']
  have hqr : q + r = ((n₁ * d₂) + (n₂ * d₁):ℤ) / ((d₁ * d₂):ℕ) := by
    rw [hq₁', hq₂']
    field_simp
    norm_cast
  rw [hqr]
  nth_rewrite 1 [@Real.ratPow_def x (by linarith) _ (d₁ * d₂) (by nlinarith)]
  --have : hx : x.root (d₁ * d₂) ≠ 0)
  -- Real.root_pos {x:Real} (hx: x ≥ 0) {n:ℕ} (hn: n ≥ 1) : x.root n > 0 ↔ x > 0 := by
  have hrootpos := (@Real.root_pos x (by linarith) (d₁ * d₂) (by nlinarith)).mpr (by linarith)
  rw [← @Real.zpow_add (x.root (d₁ * d₂)) _ _ (by linarith)]
  rw [
    @Real.ratPow_def x (by linarith) _ (d₁ * d₂) (by nlinarith),
    @Real.ratPow_def x (by linarith) _ (d₁ * d₂) (by nlinarith)
  ]

/-- Lemma 5.6.9(b) / Exercise 5.6.2 -/
theorem Real.ratPow_ratPow {x:Real} (hx: x > 0) (q r:ℚ) : (x^q)^r = x^(q*r) := by
  obtain ⟨n₁, d₁, hd₁pos, hq₁⟩ := Rat.eq_quot q
  obtain ⟨n₂, d₂, hd₂pos, hq₂⟩ := Rat.eq_quot r
  suffices alternatively : ((x ^ q) ^ r) ^ ((d₁:ℤ) * (d₂:ℤ)) = (x ^ (q * r)) ^ ((d₁:ℤ) * (d₂:ℤ)) by
    -- Chapter5.Real.pow_inj {x y : Real} {n : ℕ} (hx : x > 0) (hy : y > 0) (hn : n ≠ 0) (hxy : x ^ n = y ^ n) : x = y
    exact Real.zpow_inj
      (Real.ratPow_pos (Real.ratPow_pos (by linarith) q) r)
      (Real.ratPow_pos (by linarith) (q * r)) (by nlinarith)
      alternatively
  conv =>
    lhs
    rw [
      hq₂,
      @Real.ratPow_def (x ^ q) (Real.ratPow_pos (by linarith ) q) _ _ (by linarith),
      mul_comm,
      Real.zpow_mul,
      mul_comm, mul_assoc,
      ← Real.zpow_mul,
      Real.pow_eq_pow,
      Real.pow_of_root (by linarith [Real.ratPow_pos hx q]) (by linarith),
      hq₁,
      @Real.ratPow_def x (by linarith) _ _ (by linarith),
      Real.zpow_mul,
      mul_comm, mul_assoc,
      ← Real.zpow_mul,
      Real.pow_eq_pow,
      Real.pow_of_root (by linarith) (by linarith),
      mul_comm
    ]
  have hqr : q * r = ((n₁ * n₂) : ℤ) / ((d₁ * d₂):ℕ) := by
    rw [hq₁, hq₂]
    field_simp
    norm_cast
    ring
  have hawkward : (d₁:ℤ) * (d₂:ℤ) = (((d₁ * d₂):ℕ):ℤ) := by norm_cast
  conv =>
    rhs
    rw [
      hqr,
      @Real.ratPow_def x hx _ _ (by nlinarith),
      Real.zpow_mul, mul_comm (n₁ * n₂) _,
      ← Real.zpow_mul,
      hawkward,
      Real.pow_eq_pow,
      Real.pow_of_root (by linarith) (by nlinarith)
    ]

/-- Lemma 5.6.9(c) / Exercise 5.6.2 -/
theorem Real.ratPow_neg {x:Real} (hx: x > 0) (q:ℚ) : x^(-q) = 1 / x^q := by
  have hq : -q = q * (-(1:ℕ):ℤ) := by simp
  have hratpow := @Real.ratPow_eq_pow (x ^ q) (Real.ratPow_pos hx q) (-(1:ℕ))
  rw [hq, ← Real.ratPow_ratPow hx _ _, hratpow]
  rw [Real.zpow_neg]
  rw [pow_one]

/-- Lemma 5.6.9(d) / Exercise 5.6.2 -/
theorem Real.ratPow_mono {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (h: q > 0) : x > y ↔ x^q > y^q := by
  obtain ⟨n, d, dpos, hq⟩ := Rat.eq_quot q
  rw [hq]
  rw [@Real.ratPow_def x hx n d dpos, @Real.ratPow_def y hy n d dpos]
  have npos : n > 0 := by
      field_simp at hq
      qify at dpos
      have : (n:ℚ) > 0 := by nlinarith
      exact_mod_cast this
  lift n to ℕ using (by omega)
  rw [Real.pow_eq_pow, Real.pow_eq_pow]
  have hxyroot := (@Real.root_mono x y (by linarith) (by linarith) d (by linarith))
  have hxrootpos := (@Real.root_pos x (by linarith) d (by linarith)).mpr hx
  have hyrootpos := (@Real.root_pos y (by linarith) d (by linarith)).mpr hy
  rw [hxyroot]
  constructor
  · intro hxy
    exact @Real.pow_gt_pow (x.root d) (y.root d) n hxy (by linarith) (by linarith)
  · intro hxy
    have := (@Real.root_mono
                (x.root d ^ n)
                (y.root d ^ n)
                (Real.pow_nonneg n (by linarith))
                (Real.pow_nonneg n (by linarith))
                n
                (by linarith)
            ).mp hxy
    rwa [
      @Real.root_of_pow (x.root d) (by linarith) n (by linarith),
      @Real.root_of_pow (y.root d) (by linarith) n (by linarith)
    ] at this


/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
-- need lemma : if x > 1,

lemma Real.ratPow_zero_eq_one {x:Real} : x ^ (0:ℚ) = 1 := by
   have := Real.pow_zero x
   norm_cast at this

lemma Real.ratPow_of_one_eq_one {q : ℚ}: (1:Real) ^ q = 1 := by
  obtain ⟨n, d, hdpos, hq⟩ := Rat.eq_quot q
  rw [hq]
  rw [@Real.ratPow_def _ (by linarith) n d hdpos]
  rw [Real.root_of_one (by linarith)]
  simp_all

theorem Real.ratPow_mono_of_gt_one {x:Real} (hx: x > 1) {q r:ℚ} : x^q > x^r ↔ q > r := by
  constructor
  · obtain ⟨n₁, d₁, hd₁pos, hq₁⟩ := Rat.eq_quot q
    obtain ⟨n₂, d₂, hd₂pos, hq₂⟩ := Rat.eq_quot r
    intro h
    have hxqpos := @Real.ratPow_pos x (by linarith) q
    have hxrpos := @Real.ratPow_pos x (by linarith) r
    have hawkward : (d₁:ℚ) * (d₂:ℚ) = (((d₁ * d₂):ℕ):ℚ) := by norm_cast
    have hineq := @Real.pow_gt_pow (x^q) (x^r) (d₁ * d₂) h (by linarith) (by nlinarith)
    rw [← Real.pow_eq_pow (x^q) (d₁ * d₂), ← Real.pow_eq_pow (x^r) (d₁ * d₂)] at hineq
    rw [← Real.ratPow_eq_pow hxqpos ((d₁ * d₂):ℕ), ← Real.ratPow_eq_pow hxrpos ((d₁ * d₂):ℕ)] at hineq
    norm_cast at hineq
    rw [← hawkward] at hineq
    rw [@Real.ratPow_ratPow x (by linarith) q _, @Real.ratPow_ratPow x (by linarith) r _] at hineq
    rw [hq₁, hq₂] at hineq
    field_simp at hineq
    have hnqpos := @Real.ratPow_pos x (by linarith) (-(n₂ * d₁))
    have hineq' := mul_lt_mul_of_pos_right hineq hnqpos
    rw [← @Real.ratPow_add x (by linarith) _ _, ← @Real.ratPow_add x (by linarith) _ _] at hineq'
    ring_nf at hineq'
    rw [Real.ratPow_zero_eq_one] at hineq'
    norm_cast at hineq'
    rcases lt_trichotomy ((↑(-(n₂ * (d₁:ℤ)) + (d₂:ℤ) * n₁)):ℚ) 0 with (hneg | hzero | hpos)
    · norm_cast at hneg
      have hneg' := neg_pos.mpr hneg
      set δ:ℤ := (-(n₂ * (d₁:ℤ)) + (d₂:ℤ) * n₁)
      rw [← neg_neg δ, Real.ratPow_eq_pow (by linarith) _] at hineq'
      set β := -δ
      have hβpos : β > 0 := by linarith
      have hβint := @Int.toNat_of_nonneg β (by linarith)
      rw [← hβint] at hineq'
      set β' := Int.toNat β
      rw [Real.zpow_neg] at hineq'
      field_simp at hineq'
      have hgt := Real.pow_gt_pow x 1 β' hx (by linarith) (by linarith); simp at hgt
      linarith only [hineq', hgt]
    · rw [hzero, Real.ratPow_zero_eq_one] at hineq'
      linarith only [hineq']
    · rw [hq₁, hq₂]
      field_simp
      norm_cast at hpos ⊢
      linarith
  · intro hqr
    have hpos : q - r > 0 := by linarith
    have hrfl : q = (q - r) + r := by linarith
    rw [hrfl, Real.ratPow_add (by linarith)]
    have hmono := (@Real.ratPow_mono x 1 (by linarith) (by linarith) (q - r) hpos).mp (by linarith)
    rw [Real.ratPow_of_one_eq_one] at hmono
    nth_rewrite 2 [← one_mul (x^r)]
    gcongr
    exact @Real.ratPow_pos x (by linarith) r


/-- Lemma 5.6.9(e) / Exercise 5.6.2 -/
theorem Real.ratPow_mono_of_lt_one {x:Real} (hx0: 0 < x) (hx: x < 1) {q r:ℚ} : x^q > x^r ↔ q < r := by
  constructor
  · obtain ⟨n₁, d₁, hd₁pos, hq₁⟩ := Rat.eq_quot q
    obtain ⟨n₂, d₂, hd₂pos, hq₂⟩ := Rat.eq_quot r
    intro h
    have hxqpos := @Real.ratPow_pos x (by linarith) q
    have hxrpos := @Real.ratPow_pos x (by linarith) r
    have hawkward : (d₁:ℚ) * (d₂:ℚ) = (((d₁ * d₂):ℕ):ℚ) := by norm_cast
    have hineq := @Real.pow_gt_pow (x^q) (x^r) (d₁ * d₂) h (by linarith) (by nlinarith)
    rw [← Real.pow_eq_pow (x^q) (d₁ * d₂), ← Real.pow_eq_pow (x^r) (d₁ * d₂)] at hineq
    rw [← Real.ratPow_eq_pow hxqpos ((d₁ * d₂):ℕ), ← Real.ratPow_eq_pow hxrpos ((d₁ * d₂):ℕ)] at hineq
    norm_cast at hineq
    rw [← hawkward] at hineq
    rw [@Real.ratPow_ratPow x (by linarith) q _, @Real.ratPow_ratPow x (by linarith) r _] at hineq
    rw [hq₁, hq₂] at hineq
    field_simp at hineq
    have hnqpos := @Real.ratPow_pos x (by linarith) (-(n₂ * d₁))
    have hineq' := mul_lt_mul_of_pos_right hineq hnqpos
    rw [← @Real.ratPow_add x (by linarith) _ _, ← @Real.ratPow_add x (by linarith) _ _] at hineq'
    ring_nf at hineq'
    rw [Real.ratPow_zero_eq_one] at hineq'
    norm_cast at hineq'
    rcases lt_trichotomy ((↑(-(n₂ * (d₁:ℤ)) + (d₂:ℤ) * n₁)):ℚ) 0 with (hneg | hzero | hpos)
    · rw [hq₁, hq₂]
      field_simp
      norm_cast at hneg ⊢
      linarith
    · rw [hzero, Real.ratPow_zero_eq_one] at hineq'
      linarith only [hineq']
    · norm_cast at hpos
      set δ : ℤ := (-(n₂ * (d₁:ℤ)) + (d₂:ℤ) * n₁)
      rw [Real.ratPow_eq_pow (by linarith) _] at hineq'
      have hgt := @Real.zpow_gt_zpow 1 x δ hx (by linarith) (by linarith); simp at hgt
      linarith only [hgt, hineq']
  · intro hqr
    have hpos : r - q > 0 := by linarith
    have hrfl : r = (r - q) + q := by linarith
    rw [hrfl, Real.ratPow_add (by linarith)]
    have hmono := (@Real.ratPow_mono 1 x (by linarith) (by linarith) (r - q) hpos).mp (by linarith)
    rw [Real.ratPow_of_one_eq_one] at hmono
    nth_rewrite 1 [← one_mul (x^q)]
    gcongr
    exact @Real.ratPow_pos x (by linarith) q

/-- Lemma 5.6.9(f) / Exercise 5.6.2 -/
theorem Real.ratPow_mul {x y:Real} (hx: x > 0) (hy: y > 0) (q:ℚ) : (x*y)^q = x^q * y^q := by
  obtain ⟨n, d, dpos, hq⟩ := Rat.eq_quot q
  nth_rewrite 1 [hq]
  have hxrootpos := (@Real.root_pos x (by linarith) d (by linarith)).mpr hx
  have hyrootpos := (@Real.root_pos y (by linarith) d (by linarith)).mpr hy
  rw [@Real.ratPow_def (x * y) (by nlinarith) n d (by linarith)]
  rw [@Real.root_mul x y (by linarith) (by linarith) d (by linarith)]
  rw [@Real.mul_zpow (x.root d) (y.root d) n]
  rw [
    ← @Real.ratPow_def x (by nlinarith) n d (by linarith),
    ← @Real.ratPow_def y (by nlinarith) n d (by linarith)
  ]
  rw [← hq]


/-- Exercise 5.6.3 -/
lemma Real.pow_square (x:Real) : x ^ 2 ≥ 0 := by
  rw [Real.pow_succ, pow_one]
  rcases Real.trichotomous' x 0 with (h | h | h)
  · nlinarith
  · nlinarith
  · simp_all

theorem Real.pow_even (x:Real) {n:ℕ} (hn: Even n) : x^n ≥ 0 := by
  obtain ⟨k, hk⟩ := hn
  rw [← two_mul, mul_comm] at hk
  rw [hk]
  rw [← Real.pow_mul x 2 k]
  exact Real.pow_square (x^k)

/-- Exercise 5.6.5 -/
theorem Real.max_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  max (x^q) (y^q) = (max x y)^q := by
  simp [max_def]
  rcases Real.trichotomous' x y with (h | h | h)
  · have hpowxy := (@Real.ratPow_mono x y hx hy q hq).mp h
    rw [if_neg (by linarith), if_neg (by linarith)]
  · have hpowxy := (@Real.ratPow_mono y x hy hx q hq).mp h
    rw [if_pos (by linarith), if_pos (by linarith)]
  · have hxy : x ≤ y := by linarith
    have hpowxy : x ^ q ≤ y ^ q := by rw [h]
    simp_all

/-- Exercise 5.6.5 -/
theorem Real.min_ratPow {x y:Real} (hx: x > 0) (hy: y > 0) {q:ℚ} (hq: q > 0) :
  min (x^q) (y^q) = (min x y)^q := by
  simp [min_def]
  rcases Real.trichotomous' x y with (h | h | h)
  · have hpowxy := (@Real.ratPow_mono x y hx hy q hq).mp h
    rw [if_neg (by linarith), if_neg (by linarith)]
  · have hpowxy := (@Real.ratPow_mono y x hy hx q hq).mp h
    rw [if_pos (by linarith), if_pos (by linarith)]
  · have hxy : x ≤ y := by linarith
    have hpowxy : x ^ q ≤ y ^ q := by rw [h]
    simp_all

-- Final part of Exercise 5.6.5: state and prove versions of the above lemmas covering the case of negative q.

end Chapter5
