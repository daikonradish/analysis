import Mathlib.Tactic
import Analysis.Section_5_3


/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/--
  Definition 5.4.1 (sequences bounded away from zero with sign). Sequences are indexed to start
  from zero as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayPos (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
abbrev BoundedAwayNeg (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayPos_def (a:ℕ → ℚ) : BoundedAwayPos a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≥ c := by
  rfl

/-- Definition 5.4.1 (sequences bounded away from zero with sign). -/
theorem boundedAwayNeg_def (a:ℕ → ℚ) : BoundedAwayNeg a ↔ ∃ (c:ℚ), c > 0 ∧ ∀ n, a n ≤ -c := by
  rfl

/-- Examples 5.4.2 -/
example : BoundedAwayPos (fun n ↦ 1 + 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : BoundedAwayNeg (fun n ↦ -1 - 10^(-(n:ℤ)-1)) := ⟨ 1, by norm_num, by intros; simp; positivity ⟩

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayPos (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 1; grind

/-- Examples 5.4.2 -/
example : ¬ BoundedAwayNeg (fun n ↦ (-1)^n) := by
  intro ⟨ c, h1, h2 ⟩; specialize h2 0; grind

/-- Examples 5.4.2 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := ⟨ 1, by norm_num, by intros; simp ⟩

theorem BoundedAwayZero.boundedAwayPos {a:ℕ → ℚ} (ha: BoundedAwayPos a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rwa [abs_of_nonneg (by linarith)]

theorem BoundedAwayZero.boundedAwayNeg {a:ℕ → ℚ} (ha: BoundedAwayNeg a) : BoundedAwayZero a := by
  peel 3 ha with c h1 n h2; rw [abs_of_neg (by linarith)]; linarith

theorem not_boundedAwayPos_boundedAwayNeg {a:ℕ → ℚ} : ¬ (BoundedAwayPos a ∧ BoundedAwayNeg a) := by
  intro ⟨ ⟨ _, _, h2⟩ , ⟨ _, _, h4 ⟩ ⟩; linarith [h2 0, h4 0]

abbrev Real.IsPos (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

abbrev Real.IsNeg (x:Real) : Prop :=
  ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a

theorem Real.isPos_def (x:Real) :
    IsPos x ↔ ∃ a:ℕ → ℚ, BoundedAwayPos a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

theorem Real.isNeg_def (x:Real) :
    IsNeg x ↔ ∃ a:ℕ → ℚ, BoundedAwayNeg a ∧ (a:Sequence).IsCauchy ∧ x = LIM a := by rfl

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.trichotomous (x:Real) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  by_cases h0 : x = 0
  · left; exact h0
  · push_neg at h0
    obtain ⟨a, hcauch, hbdd, hlim⟩ := Real.boundedAwayZero_of_nonzero h0
    obtain ⟨Bd, hBdpos, hBd⟩ := hbdd
    have hcauch' := hcauch
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at hcauch

    -- This is basically saying, okay, since |a n| ≥ Bd, then after some point in the
    -- sequence, elements must be either all positive, or all negative. Otherwise,
    -- if there are infinitely many pairs that cross zero, then this violates the
    -- Cauchy condition.
    have onesided : ∃ N, ∀ j ≥ N, ∀ k ≥ N, (a j > 0 ∧ a k > 0) ∨ (a j < 0 ∧ a k < 0) := by
      obtain ⟨N, hN⟩ := hcauch (Bd / 2) (by positivity)
      use N
      intro j hj k hk
      by_contra h'
      push_neg at h'
      specialize hN j hj k hk
      have hanj  := hBd j
      have hank  := hBd k
      by_cases haj : a j > 0
      · have hak   := h'.1 haj
        have hanj' : a j ≥ Bd  := by grind
        have hank' : a k ≤ -Bd := by grind
        grind
      · push_neg at haj
        by_cases h0 : a j = 0
        · grind
        · push_neg at h0
          have haj' : a j < 0 := by grind
          have hak   := h'.2 haj'
          have hanj' : a j ≤ -Bd := by grind
          have hank' : a k ≥ Bd  := by grind
          grind

    obtain ⟨N, hN⟩ := onesided
    specialize hN N (by linarith)

    have hNabs := hBd N
    have hNnz : a N ≠ 0 := by grind

    -- todo later: refactor this into its own thing.
    -- this has to do with the tail of a sequence.
    let α := (fun n => a (n + N))
    have hαcauch : (α:Sequence).IsCauchy := by
      simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
      intro ε hε
      specialize hcauch ε hε
      obtain ⟨N₀, hN⟩ := hcauch
      use N₀
      intro j hj k jk
      unfold α
      specialize hN (j + N) (by linarith) (k + N) (by linarith)
      exact hN
    have hlimα : x = LIM α := by
      rw [hlim]
      rw [Real.LIM_eq_LIM]
      rw [Sequence.equiv_iff]
      · intro ε hε
        specialize hcauch ε (by positivity)
        obtain ⟨N₁, hN₁⟩ := hcauch
        use N₁
        intro n hn
        unfold α
        specialize hN₁ n (by linarith) (n + N) (by linarith)
        exact hN₁
      · exact hcauch'
      · exact hαcauch

    rcases lt_or_gt_of_ne hNnz with (hlt | hgt)
    · right; right
      have hneg : BoundedAwayNeg α := by
        use Bd
        constructor
        · exact hBdpos
        · intro n
          unfold α
          specialize hN (n+N) (by linarith)
          rcases hN with (h'' | h'')
          · linarith
          · specialize hBd (n + N)
            grind
      exact ⟨α, hneg, hαcauch, hlimα⟩
    · right; left
      have hpos : BoundedAwayPos α := by
        use Bd
        constructor
        · exact hBdpos
        · intro n
          unfold α
          specialize hN (n+N) (by linarith)
          rcases hN with (h'' | h'')
          · specialize hBd (n + N)
            grind
          · linarith
      exact ⟨α, hpos, hαcauch, hlimα⟩


/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_pos (x:Real) : ¬(x = 0 ∧ x.IsPos) := by
  intro ⟨h0, hpos⟩
  obtain ⟨a, abddpos, acauch, alim⟩ := hpos
  obtain ⟨B, Bgt0, hBdd⟩ := abddpos
  rw [h0] at alim
  rw [← Real.LIM.zero] at alim
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const 0) acauch, Sequence.equiv_iff] at alim
  specialize alim (B/2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := alim
  specialize hN₀ N₀ (by linarith); simp at hN₀
  specialize hBdd N₀
  grind

theorem Real.nonzero_of_pos {x:Real} (hx: x.IsPos) : x ≠ 0 := by
  have := not_zero_pos x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
  intro ⟨h0, hneg⟩
  obtain ⟨a, abddneg, acauch, alim⟩ := hneg
  obtain ⟨B, Bgt0, hBdd⟩ := abddneg
  rw [h0] at alim
  rw [← Real.LIM.zero] at alim
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const 0) acauch, Sequence.equiv_iff] at alim
  specialize alim (B/2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := alim
  specialize hN₀ N₀ (by linarith); simp at hN₀
  specialize hBdd N₀
  grind

theorem Real.nonzero_of_neg {x:Real} (hx: x.IsNeg) : x ≠ 0 := by
  have := not_zero_neg x
  simpa [hx] using this

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.not_pos_neg (x:Real) : ¬(x.IsPos ∧ x.IsNeg) := by
  intro ⟨hpos, hneg⟩
  obtain ⟨a, abddpos, acauch, alim⟩ := hpos
  obtain ⟨b, bbddneg, bcauch, blim⟩ := hneg
  obtain ⟨A, Agt0, hBddA⟩ := abddpos
  obtain ⟨B, Bgt0, hBddB⟩ := bbddneg
  rw [alim] at blim
  rw [Real.LIM_eq_LIM acauch bcauch, Sequence.equiv_iff] at blim
  specialize blim ((A + B) / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := blim
  specialize hN₀ N₀ (by linarith)
  specialize hBddA N₀
  specialize hBddB N₀
  grind

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
@[simp]
theorem Real.neg_iff_pos_of_neg (x:Real) : x.IsNeg ↔ (-x).IsPos := by
  constructor
  · intro hneg
    obtain ⟨b, bbddneg, bcauch, blim⟩ := hneg
    obtain ⟨B, Bgt0, hBddB⟩ := bbddneg
    have bcauch' := Sequence.IsCauchy.neg b bcauch
    have blim'   := Real.neg_LIM b bcauch; rw [← blim] at blim'
    have bbddpos : BoundedAwayPos (-b) := by
      use B
      constructor
      · exact Bgt0
      · intro n; simp
        specialize hBddB n
        linarith
    exact ⟨-b, bbddpos, bcauch', blim'⟩
  · intro hpos
    obtain ⟨b, bbddpos, bcauch, blim⟩ := hpos
    obtain ⟨B, Bgt0, hBddB⟩ := bbddpos
    have bcauch' := Sequence.IsCauchy.neg b bcauch
    have blim'   := Real.neg_LIM b bcauch; rw [← blim] at blim'; simp at blim'
    have bbddneg : BoundedAwayNeg (-b) := by
      use B
      constructor
      · exact Bgt0
      · intro n; simp
        specialize hBddB n
        exact hBddB
    exact ⟨-b, bbddneg, bcauch', blim'⟩


/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1-/
theorem Real.pos_add {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x+y).IsPos := by
  obtain ⟨a, abddpos, acauch, alim⟩ := hx
  obtain ⟨b, bbddpos, bcauch, blim⟩ := hy
  use a + b
  constructor
  · obtain ⟨A, Agt0, hBddA⟩ := abddpos
    obtain ⟨B, Bgt0, hBddB⟩ := bbddpos
    use A + B
    constructor
    · linarith
    · intro n; simp
      specialize hBddA n
      specialize hBddB n
      linarith
  · constructor
    · exact Sequence.IsCauchy.add acauch bcauch
    · rw [alim, blim]
      rw [Real.LIM_add acauch bcauch]

/-- Proposition 5.4.4 (basic properties of positive reals) / Exercise 5.4.1 -/
theorem Real.pos_mul {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x*y).IsPos := by
  obtain ⟨a, abddpos, acauch, alim⟩ := hx
  obtain ⟨b, bbddpos, bcauch, blim⟩ := hy
  use a * b
  constructor
  · obtain ⟨A, Agt0, hBddA⟩ := abddpos
    obtain ⟨B, Bgt0, hBddB⟩ := bbddpos
    use A * B
    constructor
    · nlinarith
    · intro n; simp
      specialize hBddA n
      specialize hBddB n
      nlinarith
  · constructor
    · exact Sequence.IsCauchy.mul acauch bcauch
    · rw [alim, blim]
      rw [Real.LIM_mul acauch bcauch]


theorem Real.pos_of_coe (q:ℚ) : (q:Real).IsPos ↔ q > 0 := by
  constructor
  · intro h
    obtain ⟨a, abddpos, acauch, alim⟩ := h
    by_contra h'
    push_neg at h'
    change ((q:ℚ):Real) = LIM a at alim
    rw [Real.ratCast_def] at alim
    rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const q) acauch] at alim
    rw [Sequence.equiv_iff] at alim
    obtain ⟨A, Agt0, hBddA⟩ := abddpos
    specialize alim (A/2) (by positivity)
    obtain ⟨N₀, hN₀⟩ := alim
    specialize hN₀ N₀ (by linarith)
    specialize hBddA N₀
    grind
  · intro h
    use (fun _ => q)
    constructor
    · use (q/2)
      constructor
      · positivity
      · intro n; simp
        linarith
    · constructor
      · exact Sequence.IsCauchy.const q
      · rw [Real.ratCast_def]

theorem Real.neg_of_coe (q:ℚ) : (q:Real).IsNeg ↔ q < 0 := by
  constructor
  · intro h
    obtain ⟨a, abddneg, acauch, alim⟩ := h
    by_contra h'
    push_neg at h'
    rw [Real.ratCast_def] at alim
    rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const q) acauch] at alim
    rw [Sequence.equiv_iff] at alim
    obtain ⟨A, Agt0, hBddA⟩ := abddneg
    specialize alim (A/2) (by positivity)
    obtain ⟨N₀, hN₀⟩ := alim
    specialize hN₀ N₀ (by linarith)
    specialize hBddA N₀
    grind
  · intro h
    use (fun _ => q)
    constructor
    · use (-q/2)
      constructor
      · nlinarith
      · intro n; simp
        linarith
    · constructor
      · exact Sequence.IsCauchy.const q
      · rw [Real.ratCast_def]

open Classical in
/-- Need to use classical logic here because {name}`IsPos` and {name}`IsNeg` are not decidable -/
noncomputable abbrev Real.abs (x:Real) : Real := if x.IsPos then x else (if x.IsNeg then -x else 0)

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_pos (x:Real) (hx: x.IsPos) : abs x = x := by
  simp [abs, hx]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_neg (x:Real) (hx: x.IsNeg) : abs x = -x := by
  have : ¬x.IsPos := by have := not_pos_neg x; simpa [hx] using this
  simp [abs, hx, this]

/-- Definition 5.4.5 (absolute value) -/
@[simp]
theorem Real.abs_of_zero : abs 0 = 0 := by
  have hpos: ¬(0:Real).IsPos := by have := not_zero_pos 0; simpa using this
  have hneg: ¬(0:Real).IsNeg := by have := not_zero_neg 0; simpa using this
  simp [abs, hpos, hneg]

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)

theorem Real.lt_iff (x y:Real) : x < y ↔ (x-y).IsNeg := by rfl
theorem Real.le_iff (x y:Real) : x ≤ y ↔ (x < y) ∨ (x = y) := by rfl

theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  constructor
  · intro h
    change (y - x).IsNeg at h
    rw [← neg_sub x y] at h
    rw [Real.neg_iff_pos_of_neg] at h
    simp at h
    exact h
  · intro h
    rw [← neg_sub y x] at h
    rw [← Real.neg_iff_pos_of_neg] at h
    exact h

theorem Real.ge_iff (x y:Real) : x ≥ y ↔ (x > y) ∨ (x = y) := by
  constructor
  · intro h
    rcases h with (hgt | heq)
    · left;  exact hgt
    · right; exact heq.symm
  · rintro (hgt | heq)
    · left; exact hgt
    · right; exact heq.symm

theorem Real.lt_of_coe (q q':ℚ): q < q' ↔ (q:Real) < (q':Real) := by
  constructor
  · intro h
    have hq := (Real.neg_of_coe ((q:ℚ) - (q':ℚ))).mpr (by linarith)
    rw [← Real.ratCast_sub] at hq
    exact hq
  · intro h
    change ((q:Real) - (q'):Real).IsNeg at h
    rw [Real.ratCast_sub] at h
    have hq := (Real.neg_of_coe _).mp h
    linarith

theorem Real.gt_of_coe (q q':ℚ): q > q' ↔ (q:Real) > (q':Real) := Real.lt_of_coe _ _

theorem Real.isPos_iff (x:Real) : x.IsPos ↔ x > 0 := by
  -- theorem Real.gt_iff (x y:Real) : x > y ↔ (x-y).IsPos := by
  have fact := Real.gt_iff x 0
  rw [sub_zero] at fact
  exact fact.symm

theorem Real.isNeg_iff (x:Real) : x.IsNeg ↔ x < 0 := by
  have fact := Real.lt_iff x 0
  rw [sub_zero] at fact
  exact fact.symm

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.trichotomous' (x y:Real) : x > y ∨ x < y ∨ x = y := by
  rcases Real.trichotomous (x - y) with (heq | hpos | hneg)
  · right; right
    have heq' := congrArg (λ expr => expr + y) heq; simp at heq'
    exact heq'
  · left
    rw [← Real.gt_iff] at hpos
    exact hpos
  · right; left
    rw [← Real.lt_iff] at hneg
    exact hneg

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_lt (x y:Real) : ¬ (x > y ∧ x < y):= by
  intro ⟨hgt, hlt⟩
  rw [Real.gt_iff] at hgt
  rw [Real.lt_iff] at hlt
  exact Real.not_pos_neg (x - y) ⟨hgt, hlt⟩

/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_gt_and_eq (x y:Real) : ¬ (x > y ∧ x = y):= by
  intro ⟨hgt, heq⟩
  rw [Real.gt_iff] at hgt
  have heq' := congrArg (λ expr => expr - y) heq; simp at heq'
  exact Real.not_zero_pos (x - y) ⟨heq', hgt⟩

-- Real.not_zero_neg (x:Real) : ¬(x = 0 ∧ x.IsNeg) := by
/-- Proposition 5.4.7(a) (order trichotomy) / Exercise 5.4.2 -/
theorem Real.not_lt_and_eq (x y:Real) : ¬ (x < y ∧ x = y):= by
  intro ⟨hlt, heq⟩
  rw [Real.lt_iff] at hlt
  have heq' := congrArg (λ expr => expr - y) heq; simp at heq'
  exact Real.not_zero_neg (x - y) ⟨heq', hlt⟩

/-- Proposition 5.4.7(b) (order is anti-symmetric) / Exercise 5.4.2 -/
theorem Real.antisymm (x y:Real) : x < y ↔ y > x := by
  constructor
  · intro h; exact h
  · intro h; exact h

/-- Proposition 5.4.7(c) (order is transitive) / Exercise 5.4.2 -/
theorem Real.lt_trans {x y z:Real} (hxy: x < y) (hyz: y < z) : x < z := by
  rw [antisymm, gt_iff] at *
  have : z - x = y - x + (z - y) := by ring
  rw [this]
  exact pos_add hxy hyz

/-- Proposition 5.4.7(d) (addition preserves order) / Exercise 5.4.2 -/
theorem Real.add_lt_add_right {x y:Real} (z:Real) (hxy: x < y) : x + z < y + z := by
  rw [antisymm, gt_iff] at hxy ⊢
  simp
  exact hxy

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_lt_mul_right {x y z:Real} (hxy: x < y) (hz: z.IsPos) : x * z < y * z := by
  rw [antisymm, gt_iff] at hxy ⊢
  convert pos_mul hxy hz using 1
  ring

/-- Proposition 5.4.7(e) (positive multiplication preserves order) / Exercise 5.4.2 -/
theorem Real.mul_le_mul_left {x y z:Real} (hxy: x ≤ y) (hz: z.IsPos) : z * x ≤ z * y := by
  rcases hxy with (hpos | hzero)
  · have h' := Real.mul_lt_mul_right hpos hz
    rw [mul_comm z x, mul_comm z y]
    left; exact h'
  · right
    rw [hzero]

theorem Real.mul_pos_neg {x y:Real} (hx: x.IsPos) (hy: y.IsNeg) : (x * y).IsNeg := by
  have hy' := (Real.neg_iff_pos_of_neg y).mp hy
  have hxy := Real.pos_mul hx hy'
  simp at hxy
  exact (Real.neg_iff_pos_of_neg (x*y)).mpr hxy

open Classical in
/--
  (Not from textbook) {name}`Real` has the structure of a linear ordering. The order is not computable,
  and so classical logic is required to impose decidability.
-/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := by
    intro a
    right; rfl
  le_trans := by
    intro a b c hab hbc
    rcases hab with (haltb | haeqb)
    · rcases hbc with (hbltc | hbeqc)
      · left; exact Real.lt_trans haltb hbltc
      · rw [hbeqc] at haltb
        left; exact haltb
    · rcases hbc with (hbltc | hbeqc)
      · rw [← haeqb] at hbltc
        left; exact hbltc
      · rw [hbeqc] at haeqb
        right; exact haeqb
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro hab
      constructor
      · left; exact hab
      · rintro (hba | heq)
        · exact (Real.not_gt_and_lt a b) ⟨hba, hab⟩
        · exact (Real.not_gt_and_eq b a) ⟨hab, heq⟩
    · intro ⟨hab, hba⟩
      rcases hab with (hlt | heq)
      · exact hlt
      · have hle : b ≤ a := by
          right
          exact heq.symm
        exfalso
        exact hba hle
  le_antisymm := by
    intro a b hab hba
    (rcases hab with (hab | hab); rcases hba with (hba | hba))
    · exfalso; exact (Real.not_gt_and_lt a b) ⟨hba, hab⟩
    · exact hba.symm
    · exact hab
  le_total := by
    intro a b
    rcases Real.trichotomous' a b with (h | h | h)
    · right; left;  exact h
    · left; left;   exact h
    · right; right; exact h.symm
  toDecidableLE := Classical.decRel _

/--
  (Not from textbook) {name}`LinearOrder`s come with a definition of absolute value {lean (type := "Real → Real")}`(|·|)`.
  Show that it agrees with our earlier definition.
-/
theorem Real.abs_eq_abs (x:Real) : |x| = abs x := by
  rcases Real.trichotomous x with (hzero | hpos | hneg)
  · unfold abs
    have hnpos: ¬(x.IsPos) := by
      intro hpos
      exact Real.not_zero_pos x ⟨hzero, hpos⟩
    have hnneg : ¬(x.IsNeg) := by
      intro hneg
      exact Real.not_zero_neg x ⟨hzero, hneg⟩
    rw [if_neg hnpos, if_neg hnneg]
    unfold _root_.abs
    rw [hzero]
    simp
  · unfold abs
    rw [if_pos hpos]
    unfold _root_.abs
    simp
    left
    rw [antisymm, gt_iff]
    simp
    exact pos_add hpos hpos
  · unfold abs
    have hnneg : ¬(x.IsPos) := by
      intro hpos
      exact Real.not_pos_neg x ⟨hpos, hneg⟩
    rw [if_neg hnneg, if_pos hneg]
    unfold _root_.abs
    simp
    left
    rw [antisymm, gt_iff]
    have hpos := (Real.neg_iff_pos_of_neg x).mp hneg
    have hpospos := pos_add hpos hpos
    ring_nf at hpospos
    ring_nf
    exact hpospos




/-- Proposition 5.4.8 -/
theorem Real.inv_of_pos {x:Real} (hx: x.IsPos) : x⁻¹.IsPos := by
  observe hnon: x ≠ 0
  observe hident : x⁻¹ * x = 1
  have hinv_non: x⁻¹ ≠ 0 := by contrapose! hident; simp [hident]
  have hnonneg : ¬x⁻¹.IsNeg := by
    intro h
    observe : (x * x⁻¹).IsNeg
    have id : -(1:Real) = (-1:ℚ) := by simp
    simp only [neg_iff_pos_of_neg, id, pos_of_coe, self_mul_inv hnon] at this
    linarith
  have trich := trichotomous x⁻¹
  simpa [hinv_non, hnonneg] using trich

theorem Real.div_of_pos {x y:Real} (hx: x.IsPos) (hy: y.IsPos) : (x/y).IsPos := by
  rw [Real.div_eq]
  have hy' := Real.inv_of_pos hy
  exact Real.pos_mul hx hy'


theorem Real.inv_of_gt {x y:Real} (hx: x.IsPos) (hy: y.IsPos) (hxy: x > y) : x⁻¹ < y⁻¹ := by
  observe hxnon: x ≠ 0
  observe hynon: y ≠ 0
  observe hxinv : x⁻¹.IsPos
  by_contra! this
  have : (1:Real) > 1 := calc
    1 = x * x⁻¹ := (self_mul_inv hxnon).symm
    _ > y * x⁻¹ := mul_lt_mul_right hxy hxinv
    _ ≥ y * y⁻¹ := mul_le_mul_left this hy
    _ = _ := self_mul_inv hynon
  simp at this

/-- (Not from textbook) {name}`Real` has the structure of a strict ordered ring. -/
instance Real.instIsStrictOrderedRing : IsStrictOrderedRing Real where
  add_le_add_left := by
    intro a b hab c
    rcases hab with (hab | hab)
    · left; exact add_lt_add_right c hab
    · right; rw [hab]
  add_le_add_right := by
    intro a b hab c
    rcases hab with (hab | hab)
    · left;
      have fact := add_lt_add_right c hab
      rw [add_comm c a, add_comm c b]
      exact fact
    · right; rw [hab]
  mul_lt_mul_of_pos_left := by
    intro a hagt0 b c hbc
    have apos : a.IsPos := by exact (isPos_iff a).mpr hagt0
    have fact := Real.mul_lt_mul_right hbc apos
    rw [mul_comm a b, mul_comm a c]
    exact fact
  mul_lt_mul_of_pos_right := by
    intro c hcgt0 a b hab
    have cpos : c.IsPos := by exact (isPos_iff c).mpr hcgt0
    exact Real.mul_lt_mul_right hab cpos
  le_of_add_le_add_left := by
    intro a b c habc
    rcases habc with (habc | habc)
    · left
      have fact := Real.add_lt_add_right (-a) habc
      simp at fact
      exact fact
    · right
      have fact := congrArg (λ expr => expr -a) habc; simp at fact
      exact fact
  zero_le_one := by
    left
    apply (Real.lt_of_coe 0 1).mp
    linarith

/-- Proposition 5.4.9 (The non-negative reals are closed)-/
theorem Real.LIM_of_nonneg {a: ℕ → ℚ} (ha: ∀ n, a n ≥ 0) (hcauchy: (a:Sequence).IsCauchy) :
    LIM a ≥ 0 := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hlim
  set x := LIM a
  rw [←isNeg_iff, isNeg_def] at hlim; choose b hb hb_cauchy hlim using hlim
  rw [boundedAwayNeg_def] at hb; choose c cpos hb using hb
  have claim1 : ∀ n, ¬ (c/2).Close (a n) (b n) := by
    intro n; specialize ha n; specialize hb n
    simp [Section_4_3.close_iff]
    calc
      _ < c := by linarith
      _ ≤ a n - b n := by linarith
      _ ≤ _ := le_abs_self _
  have claim2 : ¬(c/2).EventuallyClose (a:Sequence) (b:Sequence) := by
    contrapose! claim1; rw [Rat.eventuallyClose_iff] at claim1; peel claim1 with N claim1; grind [Section_4_3.close_iff]
  have claim3 : ¬Sequence.Equiv a b := by contrapose! claim2; rw [Sequence.equiv_def] at claim2; solve_by_elim [half_pos]
  simp_rw [x, LIM_eq_LIM hcauchy hb_cauchy] at hlim
  contradiction

/-- Corollary 5.4.10 -/
theorem Real.LIM_mono {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy)
  (hmono: ∀ n, a n ≤ b n) :
    LIM a ≤ LIM b := by
  -- This proof is written to follow the structure of the original text.
  have := LIM_of_nonneg (a := b - a) (by intro n; simp [hmono n]) (Sequence.IsCauchy.sub hb ha)
  rw [←Real.LIM_sub hb ha] at this; linarith

/-- Remark 5.4.11 --/
theorem Real.LIM_mono_fail :
    ∃ (a b:ℕ → ℚ), (a:Sequence).IsCauchy
    ∧ (b:Sequence).IsCauchy
    ∧ (∀ n, a n > b n)
    ∧ ¬LIM a > LIM b := by
  use (fun n ↦ 1 + 1/((n:ℚ) + 1))
  use (fun n ↦ 1 - 1/((n:ℚ) + 1))
  have shrinker
    {ε : ℚ} {N : ℕ}
    (const : ℕ) (j : ℕ) (hconst : const > 0) (hεpos : ε > 0) (hj : N < j) (ineq : const / ε ≤ N) :
  |1 / (j:ℚ)| ≤ ε / const := by
    rw [abs_of_nonneg (by positivity)]
    have hn0 : 0 ≤ N := by positivity
    have hj0 : 0 < j := by linarith
    qify at hj
    field_simp at *
    rw [mul_comm]
    calc const ≤ ε * N := by exact ineq
              _≤ ε * j := by nlinarith
  have acauch : ((fun (n:ℕ) ↦ 1 + 1/((n:ℚ) + 1)):Sequence).IsCauchy := by
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge (2 / ε)
    use M
    intro j hj k hk
    have jshrunk := shrinker 2 (j+1) (by linarith) hε (by linarith) hM
    have kshrunk := shrinker 2 (k+1) (by linarith) hε (by linarith) hM
    calc _ = |1/((j:ℚ) + 1) - 1/((k:ℚ) + 1)|   := by ring_nf
         _ ≤ |1/((j:ℚ) + 1)| + |1/((k:ℚ) + 1)| := by exact abs_sub _ _
         _ ≤ ε / 2 + ε / 2                     := by grind
         _ = ε                                 := by norm_num
  have bcauch : ((fun (n:ℕ) ↦ 1 - 1/((n:ℚ) + 1)):Sequence).IsCauchy := by
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge (2 / ε)
    use M
    intro j hj k hk
    have jshrunk := shrinker 2 (j+1) (by linarith) hε (by linarith) hM
    have kshrunk := shrinker 2 (k+1) (by linarith) hε (by linarith) hM
    calc _ = |1/((k:ℚ) + 1) - 1/((j:ℚ) + 1)|   := by ring_nf
         _ ≤ |1/((k:ℚ) + 1)| + |1/((j:ℚ) + 1)| := by exact abs_sub _ _
         _ ≤ ε / 2 + ε / 2                     := by grind
         _ = ε                                 := by norm_num
  have limaeqlimb : LIM (fun (n:ℕ) ↦ 1 + 1/((n:ℚ) + 1)) = LIM (fun (n:ℕ) ↦ 1 - 1/((n:ℚ) + 1)) := by
    rw [LIM_eq_LIM acauch bcauch]
    rw [Sequence.equiv_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_ge (2 / ε)
    use M
    intro j hj
    have jshrunk := shrinker 2 (j+1) (by linarith) hε (by linarith) hM
    calc _ = |1/((j:ℚ) + 1) +  1/((j:ℚ) + 1)|  := by ring_nf
         _ ≤ |1/((j:ℚ) + 1)| + |1/((j:ℚ) + 1)| := by exact abs_add_le _ _
         _ ≤ ε / 2 + ε / 2                     := by grind
         _ = ε                                 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact acauch
  · exact bcauch
  · intro n
    dsimp
    have hpos : 0 < 1/((n:ℚ) + 1) := by positivity
    have hneg : - 1/((n:ℚ) + 1) < 0 := by grind
    grind
  · intro hn
    exact Real.not_gt_and_eq _ _ ⟨hn, limaeqlimb⟩


/-- Proposition 5.4.12 (Bounding reals by rationals) -/
theorem Real.exists_rat_le_and_nat_gt {x:Real} (hx: x.IsPos) :
    (∃ q:ℚ, q > 0 ∧ (q:Real) ≤ x) ∧ ∃ N:ℕ, x < (N:Real) := by
  -- This proof is written to follow the structure of the original text.
  rw [isPos_def] at hx; choose a hbound hcauchy heq using hx
  rw [boundedAwayPos_def] at hbound; choose q hq hbound using hbound
  have := Sequence.isBounded_of_isCauchy hcauchy
  rw [Sequence.isBounded_def] at this; choose r hr this using this
  simp [Sequence.boundedBy_def] at this
  refine ⟨ ⟨ q, hq, ?_ ⟩, ?_ ⟩
  . convert LIM_mono (Sequence.IsCauchy.const _) hcauchy hbound
    exact Real.ratCast_def q
  choose N hN using exists_nat_gt r; use N
  calc
    x ≤ r := by
      rw [Real.ratCast_def r]
      convert LIM_mono hcauchy (Sequence.IsCauchy.const r) _
      intro n; specialize this n; simp at this
      exact (le_abs_self _).trans this
    _ < ((N:ℚ):Real) := by simp [hN]
    _ = N := rfl

/-- Corollary 5.4.13 (Archimedean property ) -/
theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
  -- This proof is written to follow the structure of the original text.
  obtain rfl | hx | hx := trichotomous x
  . use 1; simpa [isPos_iff] using hε
  . choose N hN using (exists_rat_le_and_nat_gt (div_of_pos hx hε)).2
    set M := N+1; refine ⟨ M, by positivity, ?_ ⟩
    replace hN : x/ε < M := hN.trans (by simp [M])
    simp
    convert mul_lt_mul_right hN hε
    rw [isPos_iff] at hε; field_simp
  use 1; simp_all [isPos_iff]; linarith

lemma Real.ex544 {x : Real} (hx : x > 0) : ∃ n:ℕ, 0 < (1:ℚ)/n ∧ (1:ℚ)/n < x := by
  rw [Real.gt_iff, sub_zero] at hx
  obtain ⟨M, hMpos, hMgt⟩ := Real.le_mul hx 1
  use M
  constructor
  · positivity
  · field_simp
    norm_cast

lemma Real.nat_exists_gt (x : Real) : ∃ N : ℕ, N > x := by
  have h1 : 1 > (0:Real)  := by linarith
  rw [Real.gt_iff, sub_zero] at h1
  obtain ⟨M, hMpos, hMineq⟩ := @Real.le_mul 1 h1 x
  rw [mul_one] at hMineq
  use M

lemma Real.exist_some_floor_nat {x : Real} (hx : x > 0): ∃ N : ℕ, (N:Real) ≤ x ∧ x < (N:Real)+1 := by
  have h1 : 1 > (0:Real)  := by linarith
  rw [Real.gt_iff, sub_zero] at h1
  have hexists := @Real.le_mul 1 h1 x; simp_rw [mul_one] at hexists
  let M := Nat.find hexists
  have ⟨hM0, hMgt⟩ := Nat.find_spec hexists
  change M > 0 at hM0
  have : M ≠ 0 := by exact Nat.ne_zero_of_lt hM0
  change (M:Real) > x at hMgt
  use (M - 1)
  constructor
  · have Mlt : M - 1 < M := by exact Nat.sub_lt_self (by linarith) (by linarith)
    have hmin := Nat.find_min hexists Mlt
    push_neg at hmin
    by_cases hM1p : (M-1) > 0
    · exact hmin hM1p
    · have : M - 1 = 0 := by linarith
      rw [this]
      norm_cast
      linarith
  · norm_cast
    rw [Nat.sub_one, ← Nat.succ_eq_add_one, Nat.succ_pred (by linarith [hM0])]
    exact hMgt

lemma Real.exists_some_floor_int (x : Real) : ∃ Z : ℤ, (Z:Real) ≤ x ∧ x < (Z:Real)+1 := by
  rcases Real.trichotomous' x 0 with (hpos | hneg | hzero)
  · obtain ⟨N, hN1, hN2⟩ := Real.exist_some_floor_nat hpos
    use N
    norm_cast at *
  · have hpos' : -x > 0 := by linarith
    obtain ⟨N, hN1, hN2⟩ := Real.exist_some_floor_nat hpos'
    by_cases integervalued : (N : Real) = - x
    · use -N
      simp_all
    · use -N - 1
      norm_cast
      simp_all
      push_neg at integervalued
      have h_strict : (N : Real) < -x := lt_of_le_of_ne hN1 integervalued
      simp_all
      constructor
      · linarith
      · linarith
  · use 0
    simp_all


/-- Proposition 5.4.14 / Exercise 5.4.5 -/
theorem Real.rat_between {x y:Real} (hxy: x < y) : ∃ q:ℚ, x < (q:Real) ∧ (q:Real) < y := by
  -- have ex544 : (x > 0)
  -- need to learn Nat.find api first.
  obtain ⟨N, stepPos, stepyx⟩ := @Real.ex544 (y - x) (by linarith)
  have hnPos : (N:Real) > 0 := by
    by_cases h0 : N = 0
    · simp [h0] at stepPos
    · have : N > 0 := by positivity
      simp_all
  obtain ⟨M, Mlb, Mub⟩ := Real.exists_some_floor_int (N * x)
  use (M+1) / N
  field_simp at *
  constructor
  · push_cast
    rw [lt_div_iff₀ hnPos]
    exact Mub
  · push_cast
    rw [mul_sub] at stepyx
    rw [div_lt_iff₀ hnPos]
    push_cast at *
    linarith

/-- Exercise 5.4.3 -/
theorem Real.floor_exist (x:Real) : ∃! n:ℤ, (n:Real) ≤ x ∧ x < (n:Real)+1 := by
  obtain ⟨z, zlb, zub⟩ := Real.exists_some_floor_int x
  use z
  constructor
  · simp_all
  · intro z' ⟨hzlb', hzub'⟩
    by_contra! h'
    have furtherthan1 : 1 ≤ |z' - z| := by grind
    rcases le_abs.mp furtherthan1 with (h | h)
    · have : (1:Real) ≤ ((z' - z):Real) := by exact_mod_cast h
      grind
    · simp at h
      have : (1:Real) ≤ ((z - z'):Real) := by exact_mod_cast h
      grind


/-- Exercise 5.4.4 -/
theorem Real.exist_inv_nat_le {x:Real} (hx: x.IsPos) : ∃ N:ℤ, N>0 ∧ (N:Real)⁻¹ < x := by
  obtain ⟨N, ⟨hPos, hG⟩⟩ := Real.le_mul hx 1
  use N
  constructor
  · positivity
  · norm_cast
    field_simp
    exact hG

/-- Exercise 5.4.6 -/
theorem Real.dist_lt_iff (ε x y:Real) : |x-y| < ε ↔ y-ε < x ∧ x < y+ε := by
  rw [abs_lt]
  constructor
  · intro ⟨h1, h2⟩
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    constructor <;> linarith

/-- Exercise 5.4.6 -/
theorem Real.dist_le_iff (ε x y:Real) : |x-y| ≤ ε ↔ y-ε ≤ x ∧ x ≤ y+ε := by
  rw [abs_le]
  constructor
  · intro ⟨h1, h2⟩
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    constructor <;> linarith

/-- Exercise 5.4.7 -/
theorem Real.le_add_eps_iff (x y:Real) : (∀ ε > 0, x ≤ y+ε) ↔ x ≤ y := by
  constructor
  · intro hε
    by_contra! h
    have hpos : x - y > 0 := by linarith
    specialize hε ((x-y)/2) (by positivity)
    grind
  · intro hge ε hε
    linarith

/-- Exercise 5.4.7 -/
theorem Real.dist_le_eps_iff (x y:Real) : (∀ ε > 0, |x-y| ≤ ε) ↔ x = y := by
  constructor
  · intro hε
    by_contra! h
    have hpos : |x - y| > 0 := by grind
    specialize hε (|x-y|/2) (by positivity)
    grind
  · intro heq ε hε
    rw [heq]; simp
    linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_le {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≤ x) :
    LIM a ≤ x := by
  by_contra! h''
  obtain ⟨q, hlb, hub⟩ := Real.rat_between h''
  obtain ⟨b, hb, rfl⟩ := Real.eq_lim x
  have hle : ∀ n:ℕ, a n ≤ q := by
    intro n
    specialize h n
    suffices alternatively : ((a n):Real) < (q : Real) by
      have := (gt_of_coe q (a n)).mpr alternatively
      linarith
    linarith
  have hcont := Real.LIM_mono hcauchy (Sequence.IsCauchy.const q) hle
  rw [← Real.ratCast_def] at hcont
  linarith

/-- Exercise 5.4.8 -/
theorem Real.LIM_of_ge {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy) (h: ∀ n, a n ≥ x) :
    LIM a ≥ x := by
  by_contra! h''
  change ∀ n, x ≤ a n at h
  obtain ⟨q, hlb, hub⟩ := Real.rat_between h''
  obtain ⟨b, hb, rfl⟩ := Real.eq_lim x
  have hle : ∀ n : ℕ, q ≤ a n := by
    intro n
    specialize h n
    suffices alternatively : (q : Real) < ((a n):Real) by
      have := (gt_of_coe (a n) q).mpr alternatively
      linarith
    linarith
  have hcont := Real.LIM_mono (Sequence.IsCauchy.const q) hcauchy hle
  rw [← Real.ratCast_def] at hcont
  linarith

theorem Real.max_eq (x y:Real) : max x y = if x ≥ y then x else y := max_def' x y

theorem Real.min_eq (x y:Real) : min x y = if x ≤ y then x else y := rfl

/-- Exercise 5.4.9 -/
theorem Real.neg_max (x y:Real) : max x y = - min (-x) (-y) := by
  rcases Real.trichotomous' x y with (h | h | h)
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
    simp
  · rw [Real.max_eq, if_neg (by linarith)]
    rw [Real.min_eq, if_neg (by linarith)]
    simp
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
    simp

/-- Exercise 5.4.9 -/
theorem Real.neg_min (x y:Real) : min x y = - max (-x) (-y) := by
  rcases Real.trichotomous' x y with (h | h | h)
  · rw [Real.max_eq, if_neg (by linarith)]
    rw [Real.min_eq, if_neg (by linarith)]
    simp
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
    simp
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
    simp

/-- Exercise 5.4.9 -/
theorem Real.max_comm (x y:Real) : max x y = max y x := by
  rcases Real.trichotomous' x y with (h | h | h)
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.max_eq, if_neg (by linarith)]
  · rw [Real.max_eq, if_neg (by linarith)]
    rw [Real.max_eq, if_pos (by linarith)]
  · rw [Real.max_eq, if_pos (by linarith)]
    rw [Real.max_eq, if_pos (by linarith)]
    exact h

/-- Exercise 5.4.9 -/
theorem Real.max_self (x:Real) : max x x = x := by
  rw [Real.max_eq, if_pos (by linarith)]

/-- Exercise 5.4.9 -/
theorem Real.max_add (x y z:Real) : max (x + z) (y + z) = max x y + z := by
  rw [Real.max_eq, Real.max_eq]
  by_cases h : x ≥ y
  · rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [if_neg (by linarith), if_neg (by linarith)]

/-- Exercise 5.4.9 -/
theorem Real.max_mul (x y :Real) {z:Real} (hz: z.IsPos) : max (x * z) (y * z) = max x y * z := by
  rw [Real.max_eq, Real.max_eq]
  rw [← sub_zero z, ← gt_iff] at hz
  by_cases h : x ≥ y
  · rw [if_pos (by nlinarith), if_pos (by linarith)]
  · rw [if_neg (by nlinarith), if_neg (by linarith)]

  --sorry
/- Additional exercise: What happens if z is negative? -/

/-- Exercise 5.4.9 -/
theorem Real.min_comm (x y:Real) : min x y = min y x := by
  rcases Real.trichotomous' x y with (h | h | h)
  · rw [Real.min_eq, if_neg (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
  · rw [Real.min_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_neg (by linarith)]
  · rw [Real.min_eq, if_pos (by linarith)]
    rw [Real.min_eq, if_pos (by linarith)]
    exact h

/-- Exercise 5.4.9 -/
theorem Real.min_self (x:Real) : min x x = x := by
  rw [Real.min_eq, if_pos (by linarith)]


/-- Exercise 5.4.9 -/
theorem Real.min_add (x y z:Real) : min (x + z) (y + z) = min x y + z := by
  rw [Real.min_eq, Real.min_eq]
  by_cases h : x ≤ y
  · rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [if_neg (by linarith), if_neg (by linarith)]


/-- Exercise 5.4.9 -/
theorem Real.min_mul (x y :Real) {z:Real} (hz: z.IsPos) : min (x * z) (y * z) = min x y * z := by
  rw [Real.min_eq, Real.min_eq]
  rw [← sub_zero z, ← gt_iff] at hz
  by_cases h : x ≤ y
  · rw [if_pos (by nlinarith), if_pos (by linarith)]
  · rw [if_neg (by nlinarith), if_neg (by linarith)]

/-- Exercise 5.4.9 -/
theorem Real.inv_max {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (max x y)⁻¹ = min x⁻¹ y⁻¹ := by
  rw [Real.min_eq, Real.max_eq]
  rw [← sub_zero x, ← gt_iff] at hx
  rw [← sub_zero y, ← gt_iff] at hy
  rcases Real.trichotomous' x y with (h | h | h)
  · have : x⁻¹ < y⁻¹ := by exact (inv_lt_inv₀ hx hy).mpr h
    rw [if_pos (by linarith), if_pos (by linarith)]
  · have : y⁻¹ < x⁻¹ := by exact (inv_lt_inv₀ hy hx).mpr h
    rw [if_neg (by linarith), if_neg (by linarith)]
  · rw [h]; simp_all

/-- Exercise 5.4.9 -/
theorem Real.inv_min {x y :Real} (hx:x.IsPos) (hy:y.IsPos) : (min x y)⁻¹ = max x⁻¹ y⁻¹ := by
  rw [Real.min_eq, Real.max_eq]
  rw [← sub_zero x, ← gt_iff] at hx
  rw [← sub_zero y, ← gt_iff] at hy
  rcases Real.trichotomous' x y with (h | h | h)
  · have : x⁻¹ < y⁻¹ := by exact (inv_lt_inv₀ hx hy).mpr h
    rw [if_neg (by linarith), if_neg (by linarith)]
  · have : y⁻¹ < x⁻¹ := by exact (inv_lt_inv₀ hy hx).mpr h
    rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [h]; simp_all

/-- Not from textbook: the rationals map as an ordered ring homomorphism into the reals. -/
abbrev Real.ratCast_ordered_hom : ℚ →+*o Real where
  toRingHom := ratCast_hom
  monotone' := by
    intro a b hab
    simp_all

end Chapter5
