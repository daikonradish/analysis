import Mathlib.Tactic

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 7.1: Finite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Technical note: it is convenient in Lean to extend finite sequences (usually by zero) to be
functions on the entire integers.

Main constructions and results of this section:
-/

-- This makes available the convenient notation `∑ n ∈ A, f n` to denote summation of `f n` for
-- `n` ranging over a finite set `A`.
open BigOperators

/-!
- API for summation over finite sets (encoded using Mathlib's {name}`Finset` type), using the
  {name}`Finset.sum` method and the `∑ n ∈ A, f n` notation.
- Fubini's theorem for finite series

We do not attempt to replicate the full API for {name}`Finset.sum` here, but in subsequent sections we
shall make liberal use of this API.

-/

-- This is a technical device to avoid Mathlib's insistence on decidable equality for finite sets.
open Classical

namespace Finset

-- We use `Finset.Icc` to describe finite intervals in the integers. `Finset.mem_Icc` is the
-- standard Mathlib tool for checking membership in such intervals.
#check mem_Icc

/-- Definition 7.1.1 -/
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Icc m n, a i = 0 := by
  rw [sum_eq_zero]; intro _; rw [mem_Icc]; grind

/--
  Definition 7.1.1. This is similar to Mathlib's {name}`Finset.sum_Icc_succ_top` except that the
  latter involves summation over the natural numbers rather than integers.
-/
theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Icc m (n+1), a i = ∑ i ∈ Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-2), a i = 0 := by
  apply sum_of_empty
  · linarith

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m-1), a i = 0 := by
  apply sum_of_empty
  · linarith

private lemma sum_of_one_item  (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m m, a i = a m := by
  have hid := sum_of_nonempty (m:=m) (n:=(m-1)) (by linarith) a
  ring_nf at hid
  rwa [sum_of_empty (n:=(-1+m)) (m:=m) (by linarith), zero_add] at hid

private lemma helper2 (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+1), a i = a m + a (m+1) := by
  have hid := sum_of_nonempty (m:=m) (n:=m) (by linarith) a
  rwa [sum_of_one_item a m] at hid

example (a: ℤ → ℝ) (m:ℤ) : ∑ i ∈ Icc m (m+2), a i = a m + a (m+1) + a (m+2) := by
  have hid := sum_of_nonempty (m:=m) (n:=(m+1)) (by linarith) a
  rw [helper2 a m] at hid
  grind

/-- Remark 7.1.3 -/
example (a: ℤ → ℝ) (m n:ℤ) : ∑ i ∈ Icc m n, a i = ∑ j ∈ Icc m n, a j := rfl

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc (n+1) p, a i = ∑ i ∈ Icc m p, a i := by
  induction' p, hpn using Int.le_induction with p' hp' ih
  · rw [sum_of_empty (n:=n) (m:=(n+1)) (by linarith), add_zero]
  · rw [sum_of_nonempty (n:=p') (by linarith), ← add_assoc, ih, ← sum_of_nonempty (by linarith)]

/-- Lemma 7.1.4(b) / Exercise 7.1.1 -/
theorem shift_finite_series {m n k:ℤ} (a: ℤ → ℝ) :
  ∑ i ∈ Icc m n, a i = ∑ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item]; simp
    · rw [sum_of_nonempty (m:=m) (by linarith), ih]
      have : a (p' + 1) = a (p' + k + 1 - k) := by ring_nf
      rw [this, ← sum_of_nonempty (m:=m+k) (n:=p'+k) (a:=fun n => a (n-k)) (by linarith)]
      ring_nf
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=(m+k)) (by linarith)]

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_add {m n:ℤ} (a b: ℤ → ℝ) :
  ∑ i ∈ Icc m n, (a i + b i) = ∑ i ∈ Icc m n, a i + ∑ i ∈ Icc m n, b i := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item, sum_of_one_item]
    · rw [sum_of_nonempty (m:=m) (by linarith), ih]
      rw [sum_of_nonempty (m:=m) (by linarith), sum_of_nonempty (m:=m) (by linarith)]
      ring_nf
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith)]
    simp

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_const_mul {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item]
    · rw [sum_of_nonempty (m:=m) (by linarith), ih, ← mul_add c _ _, ← sum_of_nonempty (m:=m) (by linarith)]
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith)]
    simp


/-- Lemma 7.1.4(e) / Exercise 7.1.1 -/
theorem abs_finite_series_le {m n:ℤ} (a: ℤ → ℝ) :
  |∑ i ∈ Icc m n, a i| ≤ ∑ i ∈ Icc m n, |a i| := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item]
    · rw [sum_of_nonempty (m:=m) (by linarith)]
      calc _ ≤ |∑ i ∈ Icc m p', a i| + |a (p' + 1)| := by apply abs_add_le
           _ ≤ ∑ i ∈ Icc m p', |a i| + |a (p' + 1)| := by gcongr
           _ = ∑ i ∈ Icc m (p' + 1), |a i|          := by rw [← sum_of_nonempty (m:=m) (by linarith)]
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith)]
    simp

/-- Lemma 7.1.4(f) / Exercise 7.1.1 -/
theorem finite_series_of_le {m n:ℤ}  {a b: ℤ → ℝ} (h: ∀ i, m ≤ i → i ≤ n → a i ≤ b i) :
  ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item]
      specialize h m (by linarith) (by linarith)
      exact h
    · rw [sum_of_nonempty (m:=m) (by linarith), sum_of_nonempty (m:=m) (by linarith)]
      apply add_le_add
      · apply ih
        intro i hmi hip
        specialize h i hmi (by linarith)
        exact h
      · specialize h (p' + 1) (by linarith) (by linarith)
        exact h
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith)]

#check sum_congr

set_option maxHeartbeats 500000 in
/--
  Proposition 7.1.8.
-/
theorem finite_series_of_rearrange {n:ℕ} {X':Type*} (X: Finset X') (hcard: X.card = n)
  (f: X' → ℝ) (g h: Icc (1:ℤ) n → X) (hg: Function.Bijective g) (hh: Function.Bijective h) :
    ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0)
    = ∑ i ∈ Icc (1:ℤ) n, (if hi: i ∈ Icc (1:ℤ) n then f (h ⟨ i, hi ⟩) else 0) := by
  -- This proof is written to broadly follow the structure of the original text.
  revert X n; intro n
  induction' n with n hn
  . simp
  intro X hX g h hg hh
  -- A technical step: we extend g, h to the entire integers using a slightly artificial map π
  set π : ℤ → Icc (1:ℤ) (n+1) :=
    fun i ↦ if hi: i ∈ Icc (1:ℤ) (n+1) then ⟨ i, hi ⟩ else ⟨ 1, by simp ⟩
  have hπ (g : Icc (1:ℤ) (n+1) → X) :
      ∑ i ∈ Icc (1:ℤ) (n+1), (if hi:i ∈ Icc (1:ℤ) (n+1) then f (g ⟨ i, hi ⟩) else 0)
      = ∑ i ∈ Icc (1:ℤ) (n+1), f (g (π i)) := by
    apply sum_congr rfl _
    intro i hi; simp [hi, π, -mem_Icc]
  simp [-mem_Icc, hπ]
  rw [sum_of_nonempty (by linarith) _]
  set x := g (π (n+1))
  have ⟨⟨j, hj'⟩, hj⟩ := hh.surjective x
  simp at hj'; obtain ⟨ hj1, hj2 ⟩ := hj'
  set h' : ℤ → X := fun i ↦ if (i:ℤ) < j then h (π i) else h (π (i+1))
  have : ∑ i ∈ Icc (1:ℤ) (n + 1), f (h (π i)) = ∑ i ∈ Icc (1:ℤ) n, f (h' i) + f x := calc
    _ = ∑ i ∈ Icc (1:ℤ) j, f (h (π i)) + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      symm; apply concat_finite_series <;> linarith
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f ( h (π j) )
        + ∑ i ∈ Icc (j+1:ℤ) (n + 1), f (h (π i)) := by
      congr; convert sum_of_nonempty _ _ <;> simp [hj1]
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + f x + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) := by
      congr 1
      . simp [←hj, π,hj1, hj2]
      symm; convert shift_finite_series _; simp
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h (π i)) + ∑ i ∈ Icc (j:ℤ) n, f (h (π (i+1))) + f x := by abel
    _ = ∑ i ∈ Icc (1:ℤ) (j-1), f (h' i) + ∑ i ∈ Icc (j:ℤ) n, f (h' i) + f x := by
      congr 2
      all_goals apply sum_congr rfl _; intro i hi; simp [h'] at *
      . simp [show i < j by linarith]
      simp [show ¬ i < j by linarith]
    _ = _ := by congr; convert concat_finite_series _ _ _ <;> linarith
  rw [this]
  congr 1
  have g_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : g (π i) ≠ x := by
    simp at hi
    simp [x, hg.injective.eq_iff, π, hi.1, show i ≤ n+1 by linarith]
    linarith
  have h'_ne_x {i:ℤ} (hi : i ∈ Icc (1:ℤ) n) : h' i ≠ x := by
    simp at hi
    have hi' : 0 ≤ i := by linarith
    have hi'' : i ≤ n+1 := by linarith
    by_cases hlt: i < j <;> by_contra! heq
    all_goals simp [h', hlt, ←hj, hh.injective.eq_iff, ←Subtype.val_inj,
                    π, hi.1, hi.2, hi',hi''] at heq
    . linarith
    contrapose! hlt; linarith
  set gtil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (g (π i)).val, by simp [mem_erase, g_ne_x] ⟩
  set htil : Icc (1:ℤ) n → X.erase x :=
    fun i ↦ ⟨ (h' i).val, by simp [mem_erase, h'_ne_x] ⟩
  set ftil : X.erase x → ℝ := fun y ↦ f y.val
  have hπval {i:ℤ} (hi : i ∈ Icc (1:ℤ) (n+1)) : (π i).val = i := by
    unfold π
    simp [hi]
  have hπinj {a b :ℤ} (ha : a ∈ Icc (1:ℤ) n) (hb : b ∈ Icc (1:ℤ) n) (heq : π a = π b) :
    a = b := by
    have heq' := congrArg Subtype.val heq
    have haeq := hπval (i:=a) (by grind)
    have hbeq := hπval (i:=b) (by grind)
    rwa [haeq, hbeq] at heq'
  have hcard : Nat.card (Icc (1:ℤ) n) = Nat.card (X.erase x.val) := by
    rw [Nat.card_eq_finsetCard, Nat.card_eq_finsetCard]
    rw [Finset.card_erase_of_mem x.2]
    rw [hX]
    simp
  have why : Function.Bijective gtil := by
    rw [Nat.bijective_iff_injective_and_card]
    constructor
    · intro a b heq
      have heq' := Subtype.mk.inj heq; norm_cast at heq'
      have hπeq := hg.injective heq'
      have hvaleq := hπinj a.property b.property hπeq
      exact_mod_cast hvaleq
    · exact hcard
  have why2 : Function.Bijective htil := by
    rw [Nat.bijective_iff_injective_and_card]
    constructor
    · intro a b heq
  -- 1. Extract the equality of the underlying values
      have heq' : (h' a).val = (h' b).val := by
        simp [htil] at heq
        exact Subtype.mk.inj heq
      by_cases ha : (a : ℤ) < j <;> by_cases hb : (b : ℤ) < j
      all_goals simp [h', ha, hb] at heq'; have hπeq := hh.injective heq'
      · exact Subtype.ext (hπinj a.property b.property hπeq)
      · have haabb : (a : ℤ) = b + 1 := by
          have haa := hπval (i:=a) (by grind); norm_cast at haa
          have hbb := hπval (i:=(b+1)) (by grind); norm_cast at hbb
          rw [← haa, ← hbb]; norm_cast
        linarith
      · have haabb : a + 1 = (b:ℤ) := by
          have haa := hπval (i:=(a+1)) (by grind); norm_cast at haa
          have hbb := hπval (i:=(b)) (by grind); norm_cast at hbb
          rw [← haa, ← hbb]; norm_cast
        linarith
      · have haabb : (a:ℤ) + 1 = b + 1 := by
          have haa := hπval (i:=(a+1)) (by grind); norm_cast at haa
          have hbb := hπval (i:=(b+1)) (by grind); norm_cast at hbb
          rw [← haa, ← hbb]; norm_cast
        exact Subtype.ext (by linarith)
    · exact hcard
  calc
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (gtil ⟨ i, hi ⟩ ) else 0 := by
      apply sum_congr rfl; grind
    _ = ∑ i ∈ Icc (1:ℤ) n, if hi: i ∈ Icc (1:ℤ) n then ftil (htil ⟨ i, hi ⟩ ) else 0 := by
      convert hn _ _ gtil htil why why2
      rw [Finset.card_erase_of_mem _, hX] <;> simp
    _ = _ := by apply sum_congr rfl; grind

/--
  This fact ensures that Definition 7.1.6 would be well-defined even if we did not appeal to the
  existing {name}`Finset.sum` method.
-/
theorem exist_bijection {n:ℕ} {Y:Type*} (X: Finset Y) (hcard: X.card = n) :
    ∃ g: Icc (1:ℤ) n → X, Function.Bijective g := by
  have := Finset.equivOfCardEq (show (Icc (1:ℤ) n).card = X.card by simp [hcard])
  exact ⟨ this, this.bijective ⟩

/-- Definition 7.1.6 -/
theorem finite_series_eq {n:ℕ} {Y:Type*} (X: Finset Y) (f: Y → ℝ) (g: Icc (1:ℤ) n → X)
  (hg: Function.Bijective g) :
    ∑ i ∈ X, f i = ∑ i ∈ Icc (1:ℤ) n, (if hi:i ∈ Icc (1:ℤ) n then f (g ⟨ i, hi ⟩) else 0) := by
  symm
  convert sum_bij (t:=X) (fun i hi ↦ g ⟨ i, hi ⟩ ) _ _ _ _
  . aesop
  . intro _ _ _ _ h; simpa [Subtype.val_inj, hg.injective.eq_iff] using h
  . intro b hb; have := hg.surjective ⟨ b, hb ⟩; grind
  intros; simp_all

/-- Proposition 7.1.11(a) / Exercise 7.1.2 -/
theorem finite_series_of_empty {X':Type*} (f: X' → ℝ) : ∑ i ∈ ∅, f i = 0 := by
  have hempty : Finset.Icc (1:ℤ) (0:ℕ) = ∅ := by exact Finset.Icc_eq_empty_of_lt (by omega)
  let g : Icc (1:ℤ) (0:ℕ) → (∅ : Finset X') := fun ⟨_, hx⟩ => absurd (hempty ▸ hx) (notMem_empty _)
  rw [finite_series_eq ∅ f g]
  · simp
  · constructor
    · intro ⟨v, hv⟩
      rw [Finset.mem_Icc] at hv
      norm_cast at hv
    · intro ⟨v, hv⟩
      simp at hv


/-- Proposition 7.1.11(b) / Exercise 7.1.2 -/
theorem finite_series_of_singleton {X':Type*} (f: X' → ℝ) (x₀:X') : ∑ i ∈ {x₀}, f i = f x₀ := by
  let g : Icc (1:ℤ) 1 → ({x₀} : Finset X') := fun _ ↦ ⟨x₀, by simp⟩
  have hg : Function.Bijective g := by
    constructor
    · intro ⟨v1, h1⟩ ⟨v2, h2⟩ heq
      simp at h1 h2
      have hv1 : v1 = 1 := by linarith
      have hv2 : v2 = 1 := by linarith
      congr
      rwa [← hv2] at hv1
    · intro ⟨y, hy⟩
      simp at hy
      subst hy
      use ⟨1, by simp⟩
  rw [finite_series_eq {x₀} f g hg]
  norm_cast
  rw [sum_of_one_item]
  rw [dif_pos (by grind)]

/--
  A technical lemma relating a sum over a finset with a sum over a fintype. Combines well with
  tools such as `map_finite_series` below.
-/
theorem finite_series_of_fintype {X':Type*} (f: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, f x = ∑ x:X, f x.val := (sum_coe_sort X f).symm

/-- Proposition 7.1.11(c) / Exercise 7.1.2 -/
theorem map_finite_series {X:Type*} [Fintype X] [Fintype Y] (f: X → ℝ) {g:Y → X}
  (hg: Function.Bijective g) :
    ∑ x, f x = ∑ y, f (g y) := by
  -- First, observe that the cardinalities are equal.
  set n := Fintype.card X with hndef
  have hcardX : (Finset.univ : Finset X).card = n := by grind
  have hcardY : (Finset.univ : Finset Y).card = n := by
    simp [Finset.card_univ, Fintype.card_congr (Equiv.ofBijective g hg)]
    grind
  -- Now, we handle the right hand side.
  obtain ⟨γ, hγ⟩ := exist_bijection Finset.univ hcardY
  rw [finite_series_eq Finset.univ (fun y => f (g y)) γ hγ]
  -- Then, handle the left hand side.
  let γ' : Icc (1:ℤ) (n:ℤ) → (Finset.univ : Finset X) :=
    fun n => ⟨g (γ n), by exact mem_univ _⟩
  have hγ' : Function.Bijective γ' := by
    constructor
    · intro a b hab
      unfold γ' at hab
      simp only [Subtype.mk.injEq] at hab
      have hab' := hg.injective hab
      norm_cast at hab'
      exact hγ.injective hab'
    · intro ⟨a, ha⟩
      obtain ⟨a', rfl⟩ := hg.surjective a
      obtain ⟨a'', ha''⟩ := hγ.surjective ⟨a', by exact mem_univ a'⟩
      use a''
      apply Subtype.ext
      norm_cast
      unfold γ'
      grind
  rw [finite_series_eq Finset.univ f γ' hγ']

-- Proposition 7.1.11(d) is `rfl` in our formalism and is therefore omitted.

/-- Proposition 7.1.11(e) / Exercise 7.1.2 -/
theorem finite_series_of_disjoint_union {Z:Type*} {X Y: Finset Z} (hdisj: Disjoint X Y) (f: Z → ℝ) :
    ∑ z ∈ X ∪ Y, f z = ∑ z ∈ X, f z + ∑ z ∈ Y, f z := by
  set a := Finset.card X with hcardX
  set b := Finset.card Y with hcardY
  set XY := X ∪ Y with hXYdef
  have hcardXY : Finset.card XY = a + b := by
    rw [hXYdef, card_union_of_disjoint hdisj, hcardX, hcardY]
  obtain ⟨α, hα⟩ := exist_bijection X hcardX
  obtain ⟨β, hβ⟩ := exist_bijection Y hcardY
  set g : Icc (1:ℤ) ((a + b):ℤ) → XY := fun ⟨i, hi⟩ =>
    -- if i is less than a, map it into X.
    if ha : i ≤ (a:ℤ) then ⟨(α ⟨i, by grind⟩).val, by rw [hXYdef]; simp⟩
    -- else, if map it into Y
    else ⟨(β ⟨(i-a), by grind⟩).val, by rw [hXYdef]; simp⟩
  have hg : Function.Bijective g := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp
      unfold g at heq
      simp at heq
      split_ifs at heq with ha1 ha2 ha3
      · simp at heq
        exact congrArg Subtype.val (hα.injective heq)
      · simp at heq
        have hx := (α ⟨i, (by grind)⟩).2
        have hy := (β ⟨j - a, (by grind)⟩).2
        rw [heq] at hx
        exfalso
        exact Set.not_disjoint_iff.mpr ⟨_, hx, hy⟩ (by exact_mod_cast hdisj)
      · simp at heq
        push_neg at ha1
        have hy := (β ⟨i - a, (by grind)⟩).2
        have hx := (α ⟨j, (by grind)⟩).2
        rw [← heq] at hx
        exfalso
        exact Set.not_disjoint_iff.mpr ⟨_, hx, hy⟩ (by exact_mod_cast hdisj)
      · simp at heq
        have := congrArg Subtype.val (hβ.injective heq)
        norm_cast at this
        simp only [Subtype.mk.injEq] at this
        linarith
    · intro ⟨d, hd⟩
      unfold XY at hd
      rcases Finset.mem_union.mp hd with hx | hy
      · obtain ⟨⟨i, hi⟩, heq⟩ := hα.surjective ⟨d, hx⟩
        use ⟨i, by grind⟩
        unfold g
        have hia : i ≤ a := by grind
        simp; rw [dif_pos hia, heq]
      · obtain ⟨⟨i, hi⟩, heq⟩ := hβ.surjective ⟨d, hy⟩
        use ⟨i + a, by grind⟩
        unfold g
        have hia : a < (i+a) := by grind
        simp; rw [dif_neg (by grind)]
        simp; rw [heq]
  rw [finite_series_eq XY f g hg]
  rw [← concat_finite_series (m:=1) (n:=a) (by grind) (by grind)]
  congr 1
  · rw [finite_series_eq X f α hα]
    apply sum_congr
    · rfl
    · intro i hi
      rw [dif_pos (by grind), dif_pos (by grind)]
      congr 1
      unfold g; simp
      rw [dif_pos (by grind)]
  · rw [finite_series_eq Y f β hβ]
    conv_rhs => rw [shift_finite_series (k:=a)]
    apply sum_congr
    · grind
    · intro i hi; simp at hi
      rw [dif_pos (by grind), dif_pos (by grind)]
      congr 1
      unfold g; simp
      rw [dif_neg (by grind)]

/-- Proposition 7.1.11(f) / Exercise 7.1.2 -/
theorem finite_series_of_add {X':Type*} (f g: X' → ℝ) (X: Finset X') :
    ∑ x ∈ X, (f + g) x = ∑ x ∈ X, f x + ∑ x ∈ X, g x := by
  set n := X.card with hcardX
  obtain ⟨φ, hφ⟩ := exist_bijection X hcardX
  let π (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) X.card then  h (φ ⟨i, hi⟩) else 0
  let converter (h : X' → ℝ) : ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) X.card, π h i :=
    by exact finite_series_eq X h φ hφ
  rw [converter (f+g), converter f, converter g]
  have hsum : ∀ (i:ℤ), π (f + g) i = π f i + π g i := by
    intro i
    unfold π
    split_ifs <;> simp
  simp_rw [hsum]
  rw [finite_series_add]

/-- Proposition 7.1.11(g) / Exercise 7.1.2 -/
theorem finite_series_of_const_mul {X':Type*} (f: X' → ℝ) (X: Finset X') (c:ℝ) :
    ∑ x ∈ X, c * f x = c * ∑ x ∈ X, f x := by
  set n := X.card with hcardX
  obtain ⟨φ, hφ⟩ := exist_bijection X hcardX
  let π (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) X.card then  h (φ ⟨i, hi⟩) else 0
  let converter (h : X' → ℝ) : ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) X.card, π h i :=
    by exact finite_series_eq X h φ hφ
  rw [converter, converter]
  have hmul : ∀ (i:ℤ), π (fun x ↦ c * f x) i = c * π f i := by
    intro i
    unfold π
    split_ifs <;> simp
  simp_rw [hmul]
  rw [finite_series_const_mul]

/-- Proposition 7.1.11(h) / Exercise 7.1.2 -/
theorem finite_series_of_le' {X':Type*} (f g: X' → ℝ) (X: Finset X') (h: ∀ x ∈ X, f x ≤ g x) :
    ∑ x ∈ X, f x ≤ ∑ x ∈ X, g x := by
  set n := X.card with hcardX
  obtain ⟨φ, hφ⟩ := exist_bijection X hcardX
  let π (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) X.card then  h (φ ⟨i, hi⟩) else 0
  let converter (h : X' → ℝ) : ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) X.card, π h i :=
    by exact finite_series_eq X h φ hφ
  rw [converter, converter]
  --  ∀ {m n : ℤ} {a b : ℤ → ℝ} (h : ∀ (i : ℤ), m ≤ i → i ≤ n → a i ≤ b i), ∑ i ∈ Icc m n, a i ≤ ∑ i ∈ Icc m n, b i
  apply finite_series_of_le
  · intro i hi hi'
    unfold π
    split_ifs <;> simp_all

#check finite_series_of_le
/-- Proposition 7.1.11(i) / Exercise 7.1.2 -/
theorem abs_finite_series_le' {X':Type*} (f: X' → ℝ) (X: Finset X') :
    |∑ x ∈ X, f x| ≤ ∑ x ∈ X, |f x| := by
  set n := X.card with hcardX
  obtain ⟨φ, hφ⟩ := exist_bijection X hcardX
  let π (h : X' → ℝ) : ℤ → ℝ := fun i =>
    if hi : i ∈ Icc (1:ℤ) X.card then  h (φ ⟨i, hi⟩) else 0
  let converter (h : X' → ℝ) : ∑ x ∈ X, h x = ∑ i ∈ Icc (1:ℤ) X.card, π h i :=
    by exact finite_series_eq X h φ hφ
  rw [converter, converter]
  have habs : ∀ (i:ℤ), π (fun x ↦ |f x|) i = |π f i| := by
    intro i
    unfold π
    split_ifs <;> simp
  simp_rw [habs]
  apply abs_finite_series_le

/-- Lemma 7.1.13 -/
theorem finite_series_of_finite_series {XX YY:Type*} (X: Finset XX) (Y: Finset YY)
  (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ z ∈ X.product Y, f z := by
  generalize h: X.card = n
  revert X; induction' n with n hn
  . intro X hX
    simp_all
  intro X hX
  have hnon : X.Nonempty := by grind [card_ne_zero]
  choose x₀ hx₀ using hnon.exists_mem
  set X' := X.erase x₀
  have hcard : X'.card = n := by simp [X', card_erase_of_mem hx₀, hX]
  have hunion : X = X' ∪ {x₀} := by ext x; by_cases x = x₀ <;> grind
  have hdisj : Disjoint X' {x₀} := by simp [X']
  calc
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ x ∈ {x₀}, ∑ y ∈ Y, f (x, y) := by
      convert finite_series_of_disjoint_union hdisj _
    _ = ∑ x ∈ X', ∑ y ∈ Y, f (x, y) + ∑ y ∈ Y, f (x₀, y) := by
      rw [finite_series_of_singleton]
    _ = ∑ z ∈ X'.product Y, f z + ∑ y ∈ Y, f (x₀, y) := by rw [hn X' hcard]
    _ = ∑ z ∈ X'.product Y, f z + ∑ z ∈ .product {x₀} Y, f z := by
      congr 1
      rw [finite_series_of_fintype, finite_series_of_fintype f]
      set π : Finset.product {x₀} Y → Y :=
        fun z ↦ ⟨ z.val.2, by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; grind ⟩
      have hπ : Function.Bijective π := by
        constructor
        . intro ⟨ ⟨ x, y ⟩, hz ⟩ ⟨ ⟨ x', y' ⟩, hz' ⟩ hzz'; simp [π] at hz hz' hzz' ⊢; grind
        intro ⟨ y, hy ⟩; use ⟨ (x₀, y), by simp [hy] ⟩
      convert map_finite_series _ hπ with z
      obtain ⟨⟨x, y⟩, hz ⟩ := z
      simp at hz ⊢; grind
    _ = _ := by
      symm; convert finite_series_of_disjoint_union _ _
      . rw [hunion]
        ext ⟨a, b⟩
        simp_all; tauto
      apply Finset.disjoint_product.mpr
      left; exact hdisj

/-- Corollary 7.1.14 (Fubini's theorem for finite series). -/
theorem finite_series_refl {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ z ∈ X.product Y, f z = ∑ z ∈ Y.product X, f (z.2, z.1) := by
  set h : Y.product X → X.product Y :=
    fun z ↦ ⟨ (z.val.2, z.val.1), by obtain ⟨ z, hz ⟩ := z; simp at hz ⊢; tauto ⟩
  have hh : Function.Bijective h := by
    constructor
    . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _
      simp_all [h]
    intro ⟨ z, hz ⟩; simp at hz
    use ⟨ (z.2, z.1), by simp [hz] ⟩
  rw [finite_series_of_fintype]
  nth_rewrite 2 [finite_series_of_fintype]
  convert map_finite_series _ hh with z

theorem finite_series_comm {XX YY:Type*} (X: Finset XX) (Y: Finset YY) (f: XX × YY → ℝ) :
    ∑ x ∈ X, ∑ y ∈ Y, f (x, y) = ∑ y ∈ Y, ∑ x ∈ X, f (x, y) := by
  rw [finite_series_of_finite_series, finite_series_refl,
      finite_series_of_finite_series _ _ (fun z ↦ f (z.2, z.1))]


-- Exercise 7.1.3 : develop as many analogues as you can of the above theory for finite products
-- instead of finite sums.
theorem prod_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∏ i ∈ Icc m n, a i = 1 := by
  rw [prod_eq_one]; intro _; rw [mem_Icc]; grind

theorem prod_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∏ i ∈ Icc m (n+1), a i = (∏ i ∈ Icc m n, a i) * a (n+1) := by
  rw [mul_comm _ (a (n+1))]
  convert prod_insert _
  · ext; simp; omega
  · infer_instance
  simp

/-- Lemma 7.1.4(a) / Exercise 7.1.1 -/
theorem concat_finite_series_prod {m n p:ℤ} (hmn: m ≤ n+1) (hpn : n ≤ p) (a: ℤ → ℝ) :
  (∏ i ∈ Icc m n, a i) * (∏ i ∈ Icc (n+1) p, a i) = ∏ i ∈ Icc m p, a i := by
  induction' p, hpn using Int.le_induction with p' hp' ih
  · rw [prod_of_empty (n:=n) (m:=(n+1)) (by linarith), mul_one]
  · rw [prod_of_nonempty (n:=p') (by linarith), ← mul_assoc, ih, ← prod_of_nonempty (by linarith)]

private lemma prod_of_one_item  (a: ℤ → ℝ) (m:ℤ) : ∏ i ∈ Icc m m, a i = a m := by
  have hid := prod_of_nonempty (m:=m) (n:=(m-1)) (by linarith) a
  ring_nf at hid
  rwa [prod_of_empty (n:=(-1+m)) (m:=m) (by linarith), one_mul] at hid


theorem shift_finite_series_prod {m n k:ℤ} (a: ℤ → ℝ) :
  ∏ i ∈ Icc m n, a i = ∏ i ∈ Icc (m+k) (n+k), a (i-k) := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [prod_of_one_item, prod_of_one_item]; simp
    · rw [prod_of_nonempty (m:=m) (by linarith), ih]
      have : a (p' + 1) = a (p' + k + 1 - k) := by ring_nf
      rw [this, ← prod_of_nonempty (m:=m+k) (n:=p'+k) (a:=fun n => a (n-k)) (by linarith)]
      ring_nf
  · rw [prod_of_empty (m:=m) (by linarith), prod_of_empty (m:=(m+k)) (by linarith)]

/-- Lemma 7.1.4(c) / Exercise 7.1.1 -/
theorem finite_series_prod_mul {m n:ℤ} (a b: ℤ → ℝ) :
  ∏ i ∈ Icc m n, (a i * b i) = (∏ i ∈ Icc m n, a i) * (∏ i ∈ Icc m n, b i) := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [prod_of_one_item, prod_of_one_item, prod_of_one_item]
    · rw [prod_of_nonempty (m:=m) (by linarith), ih]
      rw [prod_of_nonempty (m:=m) (by linarith), prod_of_nonempty (m:=m) (by linarith)]
      ring_nf
  · rw [prod_of_empty (m:=m) (by linarith), prod_of_empty (m:=m) (by linarith), prod_of_empty (m:=m) (by linarith)]
    simp

/-- Lemma 7.1.4(d) / Exercise 7.1.1 -/
theorem finite_series_prod_pow {m n:ℤ} (a: ℤ → ℝ) (c:ℝ) :
  ∑ i ∈ Icc m n, c * a i = c * ∑ i ∈ Icc m n, a i := by
  by_cases! hmn : m ≤ n
  · induction' n, hmn using Int.le_induction with p' hp' ih
    · rw [sum_of_one_item, sum_of_one_item]
    · rw [sum_of_nonempty (m:=m) (by linarith), ih, ← mul_add c _ _, ← sum_of_nonempty (m:=m) (by linarith)]
  · rw [sum_of_empty (m:=m) (by linarith), sum_of_empty (m:=m) (by linarith)]
    simp



#check Nat.factorial_zero
#check Nat.factorial_succ

#check Finset.range_eq_Ico

/--
  Exercise 7.1.4. Note: there may be some technicalities passing back and forth between natural
  numbers and integers. Look into the tactics {tactic}`zify`, {tactic}`norm_cast`, and {tactic}`omega`
-/
lemma binomial_nat (x y : ℝ) (n:ℕ) :
  (x + y)^n = ∑ j ∈ range (n+1), (n.choose j) * x^j * y^(n-j) := by
  let f : ℕ → ℕ → ℝ := (fun n m => (n.choose m) * x^m * y^(n-m))
  change (x + y) ^ n = ∑ m ∈ range (n + 1), f n m
  induction' n with n ih
  · unfold f
    simp
  · have hy : ∀ (n:ℕ), f n 0 = y^n := by unfold f; simp
    have h' : ∀ (n:ℕ), f n (n+1) = 0 := by unfold f; simp
    have h  : ∀ (n : ℕ), ∀ k ∈ range (n + 1), f (n + 1) (k + 1) = x * f n k + y * f n (k + 1) := by
      intro n k hk
      have hkn : k ≤ n := by grind
      unfold f
      -- massage; i think i am going blind
      conv_lhs => rw [Nat.choose_succ_succ, Nat.cast_add, add_mul, add_mul]; ring_nf
      conv_rhs => ring_nf
      congr 1
      · have : (1 + n - (1 + k)) = n - k := by grind
        rw [this]
        ring_nf
      · have : y = y ^ 1 := by grind
        nth_rewrite 2 [this]
        conv_rhs => rw [show x * x ^ k * y ^ 1 * y ^ (n - (1 + k)) = x * x ^ k * (y ^ 1 * y ^ (n - (1 + k))) by ring_nf]
        rw [← pow_add]
        simp
        by_cases! hik : n = k
        · rw [hik]
          simp; right
          have := Nat.choose_succ_self k
          rw [Nat.succ_eq_add_one] at this
          ring_nf at this
          exact this
        · grind
    -- handle lhs
    rw [pow_succ, ih, Finset.sum_mul]
    simp_rw [mul_add]
    -- handle rhs
    rw [Finset.sum_add_distrib, Finset.sum_range_succ' (f (n + 1)), hy]
    have hrw : ∑ k ∈ range (n + 1), f (n + 1) (k + 1) =
           ∑ k ∈ range (n + 1), (x * f n k + y * f n (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact h n k hk
    rw [hrw]
    simp_rw [Finset.sum_add_distrib, mul_comm _ x]
    suffices h : ∑ x ∈ range (n + 1), f n x * y = ∑ x ∈ range (n + 1), y * f n (x + 1) + y ^ (n + 1) by linarith
    simp_rw [mul_comm (f n _) y]
    rw [Finset.sum_range_succ']
    rw [hy, pow_add, pow_one, mul_comm (y ^ n) y]
    rw [Finset.sum_range_succ, h', mul_zero, add_zero]


#check sum_congr
theorem binomial_theorem (x y:ℝ) (n:ℕ) :
    (x + y)^n
    = ∑ j ∈ Icc (0:ℤ) n,
    n.factorial / (j.toNat.factorial * (n-j).toNat.factorial) * x^j * y^(n - j) := by
  rw [binomial_nat]
  have heq : Icc (0:ℤ) n = (range (n+1)).map Nat.castEmbedding := by
    ext k; simp
    constructor
    · rintro ⟨h1, h2⟩; use k.toNat; grind
    · intro ha; obtain ⟨a, ha'⟩ := ha; grind
  rw [heq, sum_map]; simp
  apply Finset.sum_congr
  · rfl
  · intro x hx
    rw [Nat.choose_eq_factorial_div_factorial (by grind)]
    congr 1
    · congr 1
      · rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial (by grind)) (by positivity), Nat.cast_mul]
    · rw [← Nat.cast_sub (by grind)]
      simp [zpow_natCast]

/-- Exercise 7.1.5 -/
theorem lim_of_finite_series {X:Type*} [Fintype X] (a: X → ℕ → ℝ) (L : X → ℝ)
  (h: ∀ x, Filter.atTop.Tendsto (a x) (nhds (L x))) :
    Filter.atTop.Tendsto (fun n ↦ ∑ x, a x n) (nhds (∑ x, L x)) := by
  suffices foreverysubset :
    ∀ χ : Finset X, Filter.atTop.Tendsto (fun n ↦ ∑ x ∈ χ, a x n) (nhds (∑ x ∈ χ, L x)) by exact foreverysubset univ
  intro χ
  induction' χ using Finset.induction with x S hx ih
  · simp
  · specialize h x
    rw [Metric.tendsto_atTop] at h ih ⊢
    simp_rw [Real.dist_eq] at h ih ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := h  (ε/2) (by positivity)
    obtain ⟨N₂, hN₂⟩ := ih (ε/2) (by positivity)
    use max N₁ N₂; intro n hn
    specialize hN₁ n (by grind)
    specialize hN₂ n (by grind)
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    grind


/-- Exercise 7.1.6 -/
theorem sum_union_disjoint {n : ℕ} {S : Type*} [Fintype S]
    (E : Fin n → Finset S)
    (disj : ∀ i j : Fin n, i ≠ j → Disjoint (E i) (E j))
    (cover : ∀ s : S, ∃ i, s ∈ E i)
    (f : S → ℝ) :
    ∑ s, f s = ∑ i, ∑ s ∈ E i, f s := by
  suffices h : ∑ s ∈ Finset.biUnion Finset.univ E, f s = ∑ i, ∑ s ∈ E i, f s by
    have : Finset.biUnion Finset.univ E = Finset.univ := by
      ext s; simp
      exact cover s
    rwa [this] at h
  revert E disj cover
  induction' n with k ih
  · simp
  · intro E disj cover
    rw [Fin.univ_succ, Finset.sum_biUnion]
    intro i hi j hj hij
    exact disj i j hij

/-- {given}`aᵢ` Exercise 7.1.7. Uses {lean}`Fin m` (so {lean}`aᵢ < m`) instead of the book's {lean}`aᵢ ≤ m`;
  the bound is baked into the type, and {kw (of := «term_<_»)}`<` replaces {kw (of := «term_≤_»)}`≤` to match the 0-indexed shift. -/
theorem sum_finite_col_row_counts {n m : ℕ} (a : Fin n → Fin m) :
    ∑ i, (a i : ℕ) = ∑ j : Fin m, {i : Fin n | j < a i}.toFinset.card := by
  simp_rw [← Fin.card_Iio]
  simp_rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm' (s' := fun j => {i | j < a i}.toFinset) (t' := Finset.univ)]
  simp


end Finset
