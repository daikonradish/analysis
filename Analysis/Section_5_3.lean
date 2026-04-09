import Mathlib.Tactic
import Analysis.Section_5_2
import Mathlib.Algebra.Group.MinimalAxioms


/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- A class of Cauchy sequences that start at zero. -/
@[ext]
class CauchySequence extends Sequence where
  zero : n₀ = 0
  cauchy : toSequence.IsCauchy

/-structure Sequence where
  n₀ : ℤ
  seq : ℤ → ℚ
  vanish : ∀ n < n₀, seq n = 0
-/

theorem CauchySequence.ext' {a b: CauchySequence} (h: a.seq = b.seq) : a = b := by
  apply CauchySequence.ext _ h
  rw [a.zero, b.zero]

/-- A sequence starting at zero that is Cauchy, can be viewed as a {name}`CauchySequence`. -/
abbrev CauchySequence.mk' {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : CauchySequence where
  n₀ := 0
  seq := (a:Sequence).seq
  vanish := by aesop
  zero := rfl
  cauchy := ha

@[simp]
theorem CauchySequence.coe_eq {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    (mk' ha).toSequence = (a:Sequence) := rfl

instance CauchySequence.instCoeFun : CoeFun CauchySequence (fun _ ↦ ℕ → ℚ) where
  coe a n := a.toSequence (n:ℤ)

@[simp]
theorem CauchySequence.coe_to_sequence (a: CauchySequence) :
    ((a:ℕ → ℚ):Sequence) = a.toSequence := by
  apply Sequence.ext (by simp [Sequence.n0_coe, a.zero])
  ext n; by_cases h:n ≥ 0 <;> simp_all
  rw [a.vanish]; rwa [a.zero]

@[simp]
theorem CauchySequence.coe_coe {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) : mk' ha = a := by rfl

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
  Equiv a c := by
  have hab' := (Sequence.equiv_iff a b).mp hab
  have hbc' := (Sequence.equiv_iff b c).mp hbc
  rw [(Sequence.equiv_iff a c)]
  intro ε hε
  specialize hab' (ε/2) (by positivity)
  specialize hbc' (ε/2) (by positivity)
  obtain ⟨N₁, hN₁⟩ := hab'
  obtain ⟨N₂, hN₂⟩ := hbc'
  use max N₁ N₂
  intro n hn
  specialize hN₁ n (by omega)
  specialize hN₂ n (by omega)
  calc |a n - c n| = |(a n - b n) + (b n - c n)| := by ring_nf
                  _≤ |a n - b n| + |b n - c n|   := by exact Section_4_3.abs_add (a n - b n) (b n - c n)
                  _≤ (ε / 2) + (ε / 2)           := by linarith
                  _= ε                           := by norm_num

theorem Sequence.equiv_refl {a : ℕ → ℚ} : Equiv a a := by
  rw [(Sequence.equiv_iff a a)]
  intro ε hε
  use 0
  intro n hn
  norm_num
  linarith


/-- Proposition 5.3.3 / Exercise 5.3.1 -/
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := {
     refl := by
       intro a
       exact Sequence.equiv_refl
     symm := by
       intro a b hab
       exact Sequence.equiv_symm a b hab
     trans := by
       intro a b c hab hbc
       exact Sequence.equiv_trans hab hbc
  }

theorem CauchySequence.equiv_iff (a b: CauchySequence) : a ≈ b ↔ Sequence.Equiv a b := by rfl

/-- Every constant sequence is Cauchy. -/
theorem Sequence.IsCauchy.const (a:ℚ) : ((fun _:ℕ ↦ a):Sequence).IsCauchy := by
  intro ε hε
  use 0
  constructor
  · simp_all
  · simp_all [Rat.Steady, Rat.Close]
    intro n hn z mz
    linarith

instance CauchySequence.instZero : Zero CauchySequence where
  zero := CauchySequence.mk' (a := fun _: ℕ ↦ 0) (Sequence.IsCauchy.const (0:ℚ))

abbrev Real := Quotient CauchySequence.instSetoid

open Classical in
/--
  It is convenient in Lean to assign the "dummy" value of {lean}`0` to {lean}`LIM a` when {lean}`a` is not Cauchy.
  This requires classical logic, because the property of being Cauchy is not computable or
  decidable.
-/
noncomputable abbrev LIM (a:ℕ → ℚ) : Real :=
  Quotient.mk _ (if h : (a:Sequence).IsCauchy then CauchySequence.mk' h else (0:CauchySequence))

theorem LIM_def {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (a:Sequence).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x; intro a; use (a:ℕ → ℚ)
  observe : ((a:ℕ → ℚ):Sequence) = a.toSequence
  rw [this, LIM_def (by convert a.cauchy)]
  refine ⟨ a.cauchy, ?_ ⟩
  congr; ext n; simp; replace := congr($this n); simp_all

/-- Definition 5.3.1 (Real numbers) -/
theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  . intro h; replace h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  intro h; apply Quotient.sound
  rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/--Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy)-/
theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a + b:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  rw [coe] at *
  intro ε hε
  choose N1 ha using ha _ (half_pos hε)
  choose N2 hb using hb _ (half_pos hε)
  use max N1 N2
  intro j hj k hk
  have h1 := ha j ?_ k ?_ <;> try omega
  have h2 := hb j ?_ k ?_ <;> try omega
  simp [Section_4_3.dist] at *; rw [←Rat.Close] at *
  convert Section_4_3.add_close h1 h2
  linarith

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  rw [equiv_def] at *
  peel 2 haa' with ε hε haa'
  rw [Rat.eventuallyClose_def] at *
  choose N haa' using haa'; use N
  simp [Rat.closeSeq_def] at *
  peel 5 haa' with n hn hN _ _ haa'
  simp [hn, hN] at *
  convert Section_4_3.add_close haa' (Section_4_3.close_refl (b n.toNat))
  simp

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/--Lemma 5.3.7 (Sum of equivalent sequences is equivalent)-/
theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
  (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

/-- Definition 5.3.4 (Addition of reals) -/
noncomputable instance Real.add_inst : Add Real where
  add := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a + b)) (by
      intro a b a' b' _ _
      change LIM ((a:ℕ → ℚ) + (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) + (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . solve_by_elim [Sequence.add_equiv]
      all_goals apply Sequence.IsCauchy.add <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

/-- Definition 5.3.4 (Addition of reals) -/
theorem Real.LIM_add {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a + LIM b = LIM (a + b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.add ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind


/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}  (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    (a * b:Sequence).IsCauchy := by
  obtain ⟨A, ⟨hApos, hAbd⟩⟩ := Sequence.isBounded_of_isCauchy ha
  obtain ⟨B, ⟨hBpos, hBbd⟩⟩ := Sequence.isBounded_of_isCauchy hb
  intro ε hε
  specialize ha (ε / (2 * (B + 1))) (by positivity)
  specialize hb (ε / (2 * (A + 1))) (by positivity)
  obtain ⟨N₁, ⟨hN₁, hstd₁⟩⟩ := ha
  obtain ⟨N₂, ⟨hN₂, hstd₂⟩⟩ := hb
  simp at hN₁ hN₂
  lift N₁ to ℕ using (by omega)
  lift N₂ to ℕ using (by omega)
  use max N₁ N₂
  simp
  intro n hn m hm
  simp at hn hm
  lift n to ℕ using (by omega)
  lift m to ℕ using (by omega)
  specialize hstd₁ n (by simp_all) m (by simp_all)
  specialize hstd₂ n (by simp_all) m (by simp_all)
  specialize hAbd n
  specialize hBbd m
  have fact1 : (A / (2 * (A + 1))) ≤ 1/2 := by field_simp; linarith
  have fact2 : (B / (2 * (B + 1))) ≤ 1/2 := by field_simp; linarith
  simp_all [Rat.Close]
  calc |a n * b n - a m * b m|
     = |a n * (b n - b m) + b m * (a n - a m)|           := by ring_nf
    _≤ |a n * (b n - b m)| + |b m * (a n - a m)|         := by exact Section_4_3.abs_add (a n * (b n - b m)) (b m * (a n - a m))
    _= |a n| * |b n - b m| + |b m| * |a n - a m|         := by rw [abs_mul (a n) _, abs_mul (b m) _]
    _≤ A * |b n - b m| + B * |a n - a m|                 := by gcongr
    _≤ A * (ε / (2 * (A + 1))) + B * (ε / (2 * (B + 1))) := by gcongr
    _= ε * (A / (2 * (A + 1))) + ε * (B / (2 * (B + 1))) := by field_simp
    _≤ ε * (1/2) + ε * (1/2)                             := by nlinarith
    _= ε                                                 := by ring_nf


/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (hb : (b:Sequence).IsCauchy) (haa': Equiv a a') :
  Equiv (a * b) (a' * b) := by
  rw [Sequence.equiv_iff (a * b) (a' * b)]
  dsimp
  simp_rw [← sub_mul]
  intro ε hε
  obtain ⟨B, hB0, hBbd⟩ := Sequence.isBounded_of_isCauchy hb
  specialize haa' (ε / (B+1)) (by positivity)
  obtain ⟨N₀, hN₀⟩ := haa'
  use N₀.toNat
  intro n hn
  specialize hN₀ n (by simp_all)
  specialize hBbd n
  simp_all [Rat.Close]
  calc |a n - a' n| * |b n| ≤ |a n - a' n| * B   := by gcongr
                           _≤ ε / (B + 1) * B    := by gcongr
                           _= (B / (B + 1)) * ε  := by field_simp
                           _≤ ε                  := by field_simp; linarith



/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)  (ha : (a:Sequence).IsCauchy)  (hbb': Equiv b b') :
  Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/--Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2 -/
theorem Sequence.mul_equiv
  {a b a' b':ℕ → ℚ}
  (ha : (a:Sequence).IsCauchy)
  (hb' : (b':Sequence).IsCauchy)
  (haa': Equiv a a')
  (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
    equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

/-- Definition 5.3.9 (Product of reals) -/
noncomputable instance Real.mul_inst : Mul Real where
  mul := fun x y ↦
    Quotient.liftOn₂ x y (fun a b ↦ LIM (a * b)) (by
      intro a b a' b' haa' hbb'
      change LIM ((a:ℕ → ℚ) * (b:ℕ → ℚ)) = LIM ((a':ℕ → ℚ) * (b':ℕ → ℚ))
      rw [LIM_eq_LIM]
      . exact Sequence.mul_equiv (by rw [CauchySequence.coe_to_sequence]; exact a.cauchy) (by rw [CauchySequence.coe_to_sequence]; exact b'.cauchy) haa' hbb'
      all_goals apply Sequence.IsCauchy.mul <;> rw [CauchySequence.coe_to_sequence] <;> convert @CauchySequence.cauchy ?_
      )

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  simp_rw [LIM_def ha, LIM_def hb, LIM_def (Sequence.IsCauchy.mul ha hb)]
  convert Quotient.liftOn₂_mk _ _ _ _ using 1
  simp [LIM]; grind

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (Sequence.IsCauchy.const q))

theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by rw [LIM_def]; rfl

/-- Exercise 5.3.3 -/
@[simp]
theorem Real.ratCast_inj (q r:ℚ) : (q:Real) = (r:Real) ↔ q = r := by
  constructor
  · intro h
    have h' := Quotient.exact h
    rw [CauchySequence.equiv_iff] at h'
    have h'' := (Sequence.equiv_iff _ _).mp h'
    by_contra hneq
    push_neg at hneq
    have hpos : 0 < |q - r| := abs_pos.mpr (sub_ne_zero_of_ne hneq)
    specialize h'' (|q - r| / 2) (by positivity)
    obtain ⟨N, hN⟩ := h''
    specialize hN N (by linarith)
    simp_all only [CauchySequence.coe_eq, Sequence.eval_coe_at_int, ge_iff_le, Nat.cast_nonneg, ↓reduceIte]
    linarith
  · intro h
    rw [h]

instance Real.instOfNat {n:ℕ} : OfNat Real n where
  ofNat := ((n:ℚ):Real)

instance Real.instNatCast : NatCast Real where
  natCast n := ((n:ℚ):Real)

@[simp]
theorem Real.LIM.zero : LIM (fun _ ↦ (0:ℚ)) = 0 := by rw [←ratCast_def 0]; rfl

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over addition -/
theorem Real.ratCast_add (a b:ℚ) : (a:Real) + (b:Real) = (a+b:ℚ) := by
  apply Quotient.sound
  rw [dif_pos (Sequence.IsCauchy.add _ _)]
  · rw [CauchySequence.equiv_iff]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0
    intro n hn
    simp_all
    linarith
  · simp; exact Sequence.IsCauchy.const a
  . simp; exact Sequence.IsCauchy.const b

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over multiplication -/
theorem Real.ratCast_mul (a b:ℚ) : (a:Real) * (b:Real) = (a*b:ℚ) := by
  apply Quotient.sound
  rw [dif_pos (Sequence.IsCauchy.mul _ _)]
  · rw [CauchySequence.equiv_iff]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0
    intro n hn
    simp_all
    linarith
  · simp; exact Sequence.IsCauchy.const a
  . simp; exact Sequence.IsCauchy.const b

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- {name (full := RatCast.ratCast)}`ratCast` commutes with negation -/
theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  apply Quotient.sound
  rw [dif_pos (Sequence.IsCauchy.mul _ _)]
  · rw [CauchySequence.equiv_iff]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0
    intro n hn
    simp_all
    linarith
  · simp; exact Sequence.IsCauchy.const (-1)
  . simp; exact Sequence.IsCauchy.const a

theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) :
    ((-a:ℕ → ℚ):Sequence).IsCauchy := by
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at *
  intro ε hε
  specialize ha ε hε
  obtain ⟨N, hN⟩ := ha
  use N
  intro j hj k hk
  specialize hN j hj k hk
  simp
  grind


/-- It may be possible to omit the {name (full := Sequence.IsCauchy)}`IsCauchy` hypothesis here. -/
theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (a:Sequence).IsCauchy) : -LIM a = LIM (-a) := by
  apply Quotient.sound
  have ha' := Sequence.IsCauchy.neg a ha
  rw [dif_pos ha, dif_pos ha']
  rw [dif_pos (Sequence.IsCauchy.mul _ _)]
  · rw [CauchySequence.equiv_iff]
    rw [Sequence.equiv_iff]
    intro ε hε
    use 0
    intro n hn
    simp_all
    linarith
  · simp; exact Sequence.IsCauchy.const (-1)
  · simp
    change (a : Sequence).IsCauchy
    exact ha

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms
  (by
    intro a b c
    obtain ⟨a', ha, rfl⟩ := eq_lim a
    obtain ⟨b', hb, rfl⟩ := eq_lim b
    obtain ⟨c', hc, rfl⟩ := eq_lim c
    have hab : ((a' + b'):Sequence).IsCauchy := by exact Sequence.IsCauchy.add ha hb
    have hbc : ((b' + c'):Sequence).IsCauchy := by exact Sequence.IsCauchy.add hb hc
    rw [Real.LIM_add ha hb, Real.LIM_add hab hc, Real.LIM_add hb hc, Real.LIM_add ha hbc]
    rw [add_assoc])
  (by
    intro a
    obtain ⟨a', ha, rfl⟩ := eq_lim a
    rw [← Real.LIM.zero]
    rw [Real.LIM_add (Sequence.IsCauchy.const 0) ha]
    congr
    ext y
    simp)
  (by
    intro a
    obtain ⟨a', ha, rfl⟩ := eq_lim a
    rw [Real.neg_LIM a' ha]
    rw [Real.LIM_add (Sequence.IsCauchy.neg a' ha) ha]
    · simp
      change LIM (fun _ ↦ (0:ℚ)) = 0
      rw [Real.LIM.zero])

theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
    ((a-b:ℕ → ℚ):Sequence).IsCauchy := by
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at *
    intro ε hε
    specialize ha (ε / 2) (by positivity)
    specialize hb (ε / 2) (by positivity)
    obtain ⟨N₁, hN₁⟩ := ha
    obtain ⟨N₂, hN₂⟩ := hb
    use max N₁ N₂
    intro j hj k hk
    specialize hN₁ j (by omega) k (by omega)
    specialize hN₂ j (by omega) k (by omega)
    simp
    grind

/-- {name}`LIM` distributes over subtraction -/
theorem Real.LIM_sub {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a - LIM b = LIM (a - b) := by
  rw [Real.sub_eq_add_neg]
  rw [Real.neg_LIM b hb]
  rw [Real.LIM_add ha (Sequence.IsCauchy.neg b hb)]
  congr; ring

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over subtraction -/
theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  rw [Real.sub_eq_add_neg]
  rw [Real.neg_ratCast]
  rw [Real.ratCast_add]
  congr; ring

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instAddCommGroup : AddCommGroup Real where
  add_comm := by
    intro a b
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    calc LIM a' + LIM b' = LIM (a' + b')    := by rw [Real.LIM_add ha hb]
                        _= LIM (b' + a')    := by rw [add_comm]
                        _= LIM b' + LIM a'  := by rw [← Real.LIM_add hb ha]

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_comm := by
    intro a b
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    calc LIM a' * LIM b' = LIM (a' * b')    := by rw [Real.LIM_mul ha hb]
                        _= LIM (b' * a')    := by rw [mul_comm]
                        _= LIM b' * LIM a'  := by rw [← Real.LIM_mul hb ha]
  mul_assoc := by
    intro a b c
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    obtain ⟨c', hc, rfl⟩ := Real.eq_lim c
    --lhs
    rw [Real.LIM_mul ha hb]
    rw [Real.LIM_mul (Sequence.IsCauchy.mul ha hb) hc]
    --rhs
    rw [Real.LIM_mul hb hc]
    rw [Real.LIM_mul ha (Sequence.IsCauchy.mul hb hc)]
    congr 1
    ring
  one_mul := by
    intro a
    change ((1:ℚ):Real) * a = a
    rw [Real.ratCast_def]
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    rw [Real.LIM_mul (Sequence.IsCauchy.const 1) ha]
    congr
    ext y
    simp
  mul_one := by
    intro a
    change a * ((1:ℚ):Real) = a
    rw [Real.ratCast_def]
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    rw [Real.LIM_mul ha (Sequence.IsCauchy.const 1)]
    congr
    ext y
    simp

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommRing : CommRing Real where
  left_distrib := by
    intro a b c
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    obtain ⟨c', hc, rfl⟩ := Real.eq_lim c
    --lhs
    rw [Real.LIM_add hb hc, Real.LIM_mul ha (Sequence.IsCauchy.add hb hc)]
    --rhs
    rw [Real.LIM_mul ha hb, Real.LIM_mul ha hc, Real.LIM_add (Sequence.IsCauchy.mul ha hb) (Sequence.IsCauchy.mul ha hc)]
    congr
    ring
  right_distrib := by
    intro a b c
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    obtain ⟨c', hc, rfl⟩ := Real.eq_lim c
    rw [Real.LIM_add ha hb, Real.LIM_mul (Sequence.IsCauchy.add ha hb) hc]
    rw [Real.LIM_mul ha hc, Real.LIM_mul hb hc, Real.LIM_add (Sequence.IsCauchy.mul ha hc) (Sequence.IsCauchy.mul hb hc)]
    congr
    ring
  zero_mul := by
    intro a
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    rw [← Real.LIM.zero]
    rw [Real.LIM_mul (Sequence.IsCauchy.const 0) ha]
    congr
    ext y
    simp
  mul_zero := by
    intro a
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    rw [← Real.LIM.zero]
    rw [Real.LIM_mul ha (Sequence.IsCauchy.const 0)]
    congr
    ext y
    simp
  mul_assoc := by
    intro a b c
    obtain ⟨a', ha, rfl⟩ := Real.eq_lim a
    obtain ⟨b', hb, rfl⟩ := Real.eq_lim b
    obtain ⟨c', hc, rfl⟩ := Real.eq_lim c
    rw [Real.LIM_mul ha hb, Real.LIM_mul (Sequence.IsCauchy.mul ha hb) hc]
    rw [Real.LIM_mul hb hc, Real.LIM_mul ha (Sequence.IsCauchy.mul hb hc)]
    congr 1
    ring
  natCast_succ := by
    intro n
    change ((n.succ):Real) = (n:Real) + (1:Real)
    change (((n.succ):ℚ):Real) = ((n:ℚ):Real) + ((1:ℚ):Real)
    simp [Real.ratCast_def]
    rw [Real.LIM_add (Sequence.IsCauchy.const n) (Sequence.IsCauchy.const 1)]
    congr
  intCast_negSucc := by
    intro n
    change (((Int.negSucc n):ℚ):Real) = -(((n.succ):ℚ):Real)
    simp [Real.ratCast_def]
    rw [Real.neg_LIM]
    · congr
      ext y
      simp
    · apply Sequence.IsCauchy.const

abbrev Real.ratCast_hom : ℚ →+* Real where
  toFun := RatCast.ratCast
  map_zero' := by rfl
  map_one'  := by rfl
  map_add'  := by
    intro a b
    rw [Real.ratCast_add]
  map_mul'  := by
    intro a b
    rw [Real.ratCast_mul]

/--
  Definition 5.3.12 (sequences bounded away from zero). Sequences are indexed to start from zero
  as this is more convenient for Mathlib purposes.
-/
abbrev BoundedAwayZero (a:ℕ → ℚ) : Prop :=
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c

theorem bounded_away_zero_def (a:ℕ → ℚ) : BoundedAwayZero a ↔
  ∃ (c:ℚ), c > 0 ∧ ∀ n, |a n| ≥ c := by rfl

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ (-1)^n) := by use 1; simp

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 10^(-(n:ℤ)-1)) := by
  have htinier : ∀ ε : ℚ, ε > 0 → ∃ n : ℕ, 10^(-(n:ℤ)-1) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    use N
    have fact : -(N:ℤ) - 1 = -(N+1) := by ring
    rw [fact]
    rw [zpow_neg]
    apply inv_lt_of_inv_lt₀ hε
    calc ε⁻¹ = 1/ε      := by ring
            _< N        := hN
            _< N+1      := by linarith
            _< 10^(N+1) := by exact_mod_cast Nat.lt_pow_self (by linarith)
  intro ⟨Bd, hg0, hBdBy⟩
  specialize htinier Bd hg0
  obtain ⟨N₁, hlt⟩ := htinier
  specialize hBdBy N₁
  simp at hBdBy
  linarith

/-- Examples 5.3.13 -/
example : ¬ BoundedAwayZero (fun n ↦ 1 - 10^(-(n:ℤ))) := by
  intro ⟨Bd, hg0, hBdBy⟩
  specialize hBdBy 0
  simp at hBdBy
  linarith

/-- Examples 5.3.13 -/
example : BoundedAwayZero (fun n ↦ 10^(n+1)) := by
  use 1, by norm_num
  intro n; dsimp
  rw [abs_of_nonneg (by positivity), show (1:ℚ) = 10^0 by norm_num]
  gcongr <;> grind

/-- Examples 5.3.13 -/
example : ¬ ((fun (n:ℕ) ↦ (10:ℚ)^(n+1)):Sequence).IsBounded := by
  have hpow10 : ∀ n : ℕ, n < 10 ^ n := by
    intro n
    exact Nat.lt_pow_self (by linarith)
  intro ⟨Bd, hBd0, hBdBy⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (⌊Bd⌋ + 1)
  specialize hBdBy N
  simp at hBdBy
  have hineq := calc 10 ^ (N + 1) ≤ Bd       := by exact hBdBy
                                 _< ⌊Bd⌋ + 1 := by exact Int.lt_floor_add_one Bd
                                 _< N        := by exact_mod_cast hN
                                 _< N + 1    := by linarith
  specialize hpow10 (N+1)
  norm_cast at hineq hpow10
  linarith

/-- Lemma 5.3.14 -/
theorem Real.boundedAwayZero_of_nonzero {x:Real} (hx: x ≠ 0) :
    ∃ a:ℕ → ℚ, (a:Sequence).IsCauchy ∧ BoundedAwayZero a ∧ x = LIM a := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ b, hb, rfl ⟩ := eq_lim x
  simp only [←LIM.zero, ne_eq] at hx
  rw [LIM_eq_LIM hb (by convert Sequence.IsCauchy.const 0), Sequence.equiv_iff] at hx
  simp at hx
  choose ε hε hx using hx
  choose N hb' using (Sequence.IsCauchy.coe _).mp hb _ (half_pos hε)
  change ∀ j ≥ N, ∀ k ≥ N, |b j - b k| ≤ ε / 2 at hb'
  choose n₀ hn₀ hx using hx N
  have how : ∀ j ≥ N, |b j| ≥ ε/2 := by
    intro j hj
    specialize hb' j hj n₀ hn₀
    have hrev : |b n₀| - |b j| ≤ |b n₀ - b j| := abs_sub_abs_le_abs_sub (b n₀) (b j)
    rw [abs_sub_comm] at hrev
    linarith
  set a : ℕ → ℚ := fun n ↦ if n < n₀ then ε/2 else b n
  have not_hard : Sequence.Equiv a b := by
    rw [Sequence.equiv_iff]
    intro δ hδ
    use n₀ + 1
    intro n  hn
    unfold a
    rw [if_neg (by linarith)]
    simp
    linarith
  have ha := (Sequence.isCauchy_of_equiv not_hard).mpr hb
  refine ⟨ a, ha, ?_, by rw [(LIM_eq_LIM ha hb).mpr not_hard] ⟩
  rw [bounded_away_zero_def]
  use ε/2, half_pos hε
  intro n; by_cases hn: n < n₀ <;> simp [a, hn, le_abs_self _]
  grind

/--
  This result was not explicitly stated in the text, but is needed in the theory. It's a good
  exercise, so I'm setting it as such.
-/
theorem Real.lim_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    LIM a ≠ 0 := by
    rw [← Real.LIM.zero]
    intro hlim0
    rw [Real.LIM_eq_LIM ha_cauchy (Sequence.IsCauchy.const 0)] at hlim0
    rw [Sequence.equiv_iff] at hlim0
    obtain ⟨Bd, ⟨hBd0, hBdd⟩⟩ := ha
    specialize hlim0 (Bd/2) (half_pos hBd0)
    obtain ⟨N, hN⟩ := hlim0
    specialize hN N (by linarith)
    specialize hBdd N
    simp at hN
    linarith

theorem Real.nonzero_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a) (n: ℕ) : a n ≠ 0 := by
   choose c hc ha using ha; specialize ha n; contrapose! ha; simp [ha, hc]

/-- Lemma 5.3.15 -/
theorem Real.inv_isCauchy_of_boundedAwayZero {a:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) :
    ((a⁻¹:ℕ → ℚ):Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  have ha' (n:ℕ) : a n ≠ 0 := nonzero_of_boundedAwayZero ha n
  rw [bounded_away_zero_def] at ha; choose c hc ha using ha
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha_cauchy ⊢
  intro ε hε; specialize ha_cauchy (c^2 * ε) (by positivity)
  choose N ha_cauchy using ha_cauchy; use N;
  peel 4 ha_cauchy with n hn m hm ha_cauchy
  calc
    _ = |(a m - a n) / (a m * a n)| := by
        congr; simp only [Pi.inv_apply]; field_simp [ha' m, ha' n]
    _ ≤ |a m - a n| / c^2 := by rw [abs_div, abs_mul, sq]; gcongr <;> solve_by_elim
    _ = |a n - a m| / c^2 := by rw [abs_sub_comm]
    _ ≤ (c^2 * ε) / c^2 := by gcongr
    _ = ε := by field_simp [hc]

/-- Lemma 5.3.17 (Reciprocation is well-defined) -/
theorem Real.inv_of_equiv {a b:ℕ → ℚ} (ha: BoundedAwayZero a)
  (ha_cauchy: (a:Sequence).IsCauchy) (hb: BoundedAwayZero b)
  (hb_cauchy: (b:Sequence).IsCauchy) (hlim: LIM a = LIM b) :
    LIM a⁻¹ = LIM b⁻¹ := by
  -- This proof is written to follow the structure of the original text.
  set P := LIM a⁻¹ * LIM a * LIM b⁻¹
  have hainv_cauchy := Real.inv_isCauchy_of_boundedAwayZero ha ha_cauchy
  have hbinv_cauchy := Real.inv_isCauchy_of_boundedAwayZero hb hb_cauchy
  have haainv_cauchy := hainv_cauchy.mul ha_cauchy
  have habinv_cauchy := hainv_cauchy.mul hb_cauchy
  have claim1 : P = LIM b⁻¹ := by
    simp only [P, LIM_mul hainv_cauchy ha_cauchy, LIM_mul haainv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero ha n]
  have claim2 : P = LIM a⁻¹ := by
    simp only [P, hlim, LIM_mul hainv_cauchy hb_cauchy, LIM_mul habinv_cauchy hbinv_cauchy]
    rcongr n; simp [nonzero_of_boundedAwayZero hb n]
  grind

open Classical in
/--
  Definition 5.3.16 (Reciprocation of real numbers).  Requires classical logic because we need to
  assign a "junk" value to the inverse of 0.
-/
noncomputable instance Real.instInv : Inv Real where
  inv x := if h: x ≠ 0 then LIM (boundedAwayZero_of_nonzero h).choose⁻¹ else 0

theorem Real.inv_def {a:ℕ → ℚ} (h: BoundedAwayZero a) (hc: (a:Sequence).IsCauchy) :
    (LIM a)⁻¹ = LIM a⁻¹ := by
  observe hx : LIM a ≠ 0
  set x := LIM a
  have ⟨ h1, h2, h3 ⟩ := (boundedAwayZero_of_nonzero hx).choose_spec
  simp [Inv.inv, hx]
  exact inv_of_equiv h2 h1 h hc h3.symm

@[simp]
theorem Real.inv_zero : (0:Real)⁻¹ = 0 := by simp [Inv.inv]

theorem Real.self_mul_inv {x:Real} (hx: x ≠ 0) : x * x⁻¹ = 1 := by
  have ⟨x', hcauchy, hb0, hlim⟩ := boundedAwayZero_of_nonzero hx
  rw [hlim]
  rw [Real.inv_def hb0 hcauchy]
  rw [Real.LIM_mul hcauchy (Real.inv_isCauchy_of_boundedAwayZero hb0 hcauchy)]
  change LIM (x' * x'⁻¹) = ((1:ℚ):Real)
  rw [Real.ratCast_def]
  congr
  ext n
  obtain ⟨c, hcge0, hbdc⟩ := hb0
  specialize hbdc n
  have fact1 : |x' n| > 0 := by linarith
  have fact2 : x' n ≠ 0   := by exact abs_pos.mp fact1
  simp
  field_simp

theorem Real.inv_mul_self {x:Real} (hx: x ≠ 0) : x⁻¹ * x = 1 := by
  have ⟨x', hcauchy, hb0, hlim⟩ := boundedAwayZero_of_nonzero hx
  rw [hlim]
  rw [Real.inv_def hb0 hcauchy]
  rw [Real.LIM_mul (Real.inv_isCauchy_of_boundedAwayZero hb0 hcauchy) hcauchy]
  change LIM (x'⁻¹ * x') = ((1:ℚ):Real)
  rw [Real.ratCast_def]
  congr
  ext n
  obtain ⟨c, hcge0, hbdc⟩ := hb0
  specialize hbdc n
  have fact1 : |x' n| > 0 := by linarith
  have fact2 : x' n ≠ 0   := by exact abs_pos.mp fact1
  simp
  field_simp

lemma BoundedAwayZero.const {q : ℚ} (hq : q ≠ 0) : BoundedAwayZero fun _ ↦ q := by
  use |q|; simp [hq]

theorem Real.inv_ratCast (q:ℚ) : (q:Real)⁻¹ = (q⁻¹:ℚ) := by
  by_cases h : q = 0
  . rw [h, ← show (0:Real) = (0:ℚ) by norm_cast]; norm_num; norm_cast
  simp_rw [ratCast_def, inv_def (BoundedAwayZero.const h) (by apply Sequence.IsCauchy.const)]; congr

/-- Default definition of division. -/
noncomputable instance Real.instDivInvMonoid : DivInvMonoid Real where

theorem Real.div_eq (x y:Real) : x/y = x * y⁻¹ := rfl

noncomputable instance Real.instField : Field Real where
  exists_pair_ne := by
    use 0, 1
    intro h
    change ((0:ℚ):Real) = ((1:ℚ):Real) at h
    rw [Real.ratCast_def, Real.ratCast_def] at h
    rw [Real.LIM_eq_LIM (Sequence.IsCauchy.const 0) (Sequence.IsCauchy.const 1)] at h
    rw [Sequence.equiv_iff] at h
    specialize h (0.5) (by positivity)
    obtain ⟨N, hN⟩ := h
    specialize hN N (by linarith)
    norm_num at hN
  mul_inv_cancel := by
    intro a hn0
    exact Real.self_mul_inv hn0
  inv_zero := by
    exact Real.inv_zero
  ratCast_def := by
    intro q
    change (q:Real) = (((q.num):ℚ):Real) / (((q.den):ℚ):Real)
    rw [Real.ratCast_def, Real.ratCast_def, Real.ratCast_def]
    have hqdenbdd : BoundedAwayZero (fun x ↦ q.den) := by
      use q.den
      have fact : q.den > 0 := by exact Rat.den_pos q
      constructor
      · exact_mod_cast fact
      · intro n; simp_all
    have hqdencauchy := Sequence.IsCauchy.const ((q.den):ℚ)
    have hqnumcauchy := Sequence.IsCauchy.const ((q.num):ℚ)
    have hqinvcauchy := Real.inv_isCauchy_of_boundedAwayZero hqdenbdd hqdencauchy
    rw [Real.div_eq]
    rw [Real.inv_def hqdenbdd hqdencauchy]
    rw [Real.LIM_mul hqnumcauchy hqinvcauchy]
    congr
    ext y
    simp
    field_simp
    exact Rat.mul_den_eq_num q
  qsmul := _
  nnqsmul := _

theorem Real.mul_right_cancel₀ {x y z:Real} (hz: z ≠ 0) (h: x * z = y * z) : x = y := by
  obtain ⟨x', hx', rfl⟩ := Real.eq_lim x
  obtain ⟨y', hy', rfl⟩ := Real.eq_lim y
  obtain ⟨z', hz', hzbd0, hzeq⟩ := Real.boundedAwayZero_of_nonzero hz
  rw [hzeq] at h
  rw [Real.LIM_mul hx' hz', Real.LIM_mul hy' hz'] at h
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.mul hx' hz') (Sequence.IsCauchy.mul hy' hz')] at h
  rw [Real.LIM_eq_LIM hx' hy']
  rw [Sequence.equiv_iff] at *
  dsimp at h
  simp_rw [← sub_mul, abs_mul] at h
  obtain ⟨Bd, hBdPos, hBdd⟩ := hzbd0
  intro ε hε
  specialize h (ε * Bd) (by positivity)
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n (by linarith)
  specialize hBdd n
  nlinarith

theorem Real.mul_right_nocancel : ¬ ∀ (x y z:Real), (hz: z = 0) → (x * z = y * z) → x = y := by
  intro h
  specialize h 0 1 0 (by rfl) (by simp)
  simp at h

/-- Exercise 5.3.4 -/
theorem Real.IsBounded.equiv {a b:ℕ → ℚ} (ha: (a:Sequence).IsBounded) (hab: Sequence.Equiv a b) :
    (b:Sequence).IsBounded := by
  obtain ⟨Bd, hBdpos, hBdd⟩ := ha
  rw [Sequence.equiv_iff] at hab
  specialize hab 1 (by linarith)
  obtain ⟨N, hN⟩ := hab
  set headBd := Finset.sup' (Finset.Icc 0 N) (Finset.nonempty_Icc.mpr (Nat.zero_le N)) (fun n => |b n|)
  set tailBd := 1 + Bd
  use max headBd tailBd
  constructor
  · have fact : tailBd ≥ 0 := by positivity
    exact le_max_of_le_right fact
  · intro n
    by_cases vanishing : n < 0
    · have fact := (b:Sequence).vanish n vanishing
      rw [fact]
      norm_num
      right; positivity
    · lift n to ℕ using (by omega)
      by_cases headtail : n ≤ N
      · have fact : n ∈ Finset.Icc 0 N := by exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, headtail⟩
        simp
        left
        unfold headBd
        exact Finset.le_sup' (fun n => |b n|) fact
      · push_neg at headtail
        specialize hN n (by linarith)
        specialize hBdd n; simp at hBdd
        simp
        right
        unfold tailBd
        calc |b n| = |b n - a n + a n| := by ring_nf
                  _≤ |b n - a n| + |a n| := by exact Section_4_3.abs_add (b n - a n) (a n)
                  _= |a n - b n| + |a n| := by rw [abs_sub_comm]
                  _≤ 1 + |a n|           := by linarith
                  _≤ 1 + Bd              := by linarith

/--
  Same as {name}`Sequence.IsCauchy.harmonic` but reindexing the sequence as a₀ = 1, a₁ = 1/2, ...
  This form is more convenient for the upcoming proof of Theorem 5.5.9.
-/
theorem Sequence.IsCauchy.harmonic' : ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy := by
  rw [coe]; intro ε hε; choose N h1 h2 using (mk _).mp harmonic ε hε
  use N.toNat; intro j _ k _; specialize h2 (j+1) _ (k+1) _ <;> try omega
  simp_all

/-- Exercise 5.3.5 -/
theorem Real.LIM.harmonic : LIM (fun n ↦ 1/((n:ℚ)+1)) = 0 := by
  rw [← Real.LIM.zero]
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.harmonic') (Sequence.IsCauchy.const 0)]
  rw [Sequence.equiv_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (ε⁻¹)
  use N
  intro n hn
  have hnpos : 0 ≤ n      := by exact Nat.zero_le n
  have hnplus : 0 < n + 1 := by linarith
  simp
  qify at hn hnpos hnplus
  have almostthere : ε⁻¹ < n + 1 := by linarith
  have this : |(n:ℚ) + 1| = n + 1 := by exact abs_of_pos hnplus
  rw [this]
  field_simp at *
  linarith

end Chapter5
