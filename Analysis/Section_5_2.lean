import Mathlib.Tactic
import Analysis.Section_5_1


/-!
# Analysis I, Section 5.2: Equivalent Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Notion of an ε-close and eventually ε-close sequences of rationals.
- Notion of an equivalent Cauchy sequence of rationals.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


abbrev Rat.CloseSeq (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Rat.EventuallyClose (ε: ℚ) (a b: Chapter5.Sequence) : Prop :=
  ∃ N, ε.CloseSeq (a.from N) (b.from N)

namespace Chapter5

/-- Definition 5.2.1 ($ε$-close sequences) -/
lemma Rat.closeSeq_def (ε: ℚ) (a b: Sequence) :
    ε.CloseSeq a b ↔ ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n) := by rfl

/-- Example 5.2.2 -/
example : (0.1:ℚ).CloseSeq
    ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence)
    ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  rw [Rat.CloseSeq]
  intro n ha hb
  simp at ha hb
  simp_all [Rat.Close]
  lift n to ℕ using (by omega)
  have fact : (n : ℤ).toNat = n := by exact Int.toNat_natCast n
  rw [fact]
  have habs :  |(-1) ^ n| ≤ 1 := by simp [abs_pow]
  qify at habs
  calc |(-1) ^ n - 1.1 * (((-1) ^ n):ℚ)|
     = |(1 * (-1) ^ n) - (1.1 * (-1) ^ n)| := by field_simp
    _= |(1 - 1.1) * (-1) ^ n|              := by congr; rw [sub_mul]
    _= |(-0.1) * (-1) ^ n|                 := by congr; norm_num
    _= |(-0.1)| * |(-1) ^ n|               := by rw [abs_mul]
    _= 0.1 * |(-1) ^ n|                    := by congr; norm_num
    _≤ 0.1 * 1                             := by gcongr
    _= 0.1                                 := by norm_num

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((-1)^n:ℚ)):Sequence) := by
  intro hstd
  rw [Rat.Steady] at hstd
  specialize hstd 0 (by simp) 1 (by simp)
  simp_all [Rat.Close]
  norm_num at hstd

/-- Example 5.2.2 -/
example : ¬ (0.1:ℚ).Steady ((fun n:ℕ ↦ ((1.1:ℚ) * (-1)^n)):Sequence) := by
  intro hstd
  rw [Rat.Steady] at hstd
  specialize hstd 0 (by simp) 1 (by simp)
  simp_all [Rat.Close]
  norm_num at hstd

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_def (ε: ℚ) (a b: Sequence) :
    ε.EventuallyClose a b ↔ ∃ N, ε.CloseSeq (a.from N) (b.from N) := by rfl

/-- Definition 5.2.3 (Eventually ε-close sequences) -/
lemma Rat.eventuallyClose_iff (ε: ℚ) (a b: ℕ → ℚ) :
    ε.EventuallyClose (a:Sequence) (b:Sequence) ↔ ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  · intro hεclose
    obtain ⟨N, hN⟩ := hεclose
    rw [Rat.CloseSeq] at hN
    use Int.toNat N
    intro n hn
    specialize hN n (by simp_all) (by simp_all)
    simp_all [Rat.Close]
  · intro hN
    obtain ⟨N, hn⟩ := hN
    simp_all [Rat.EventuallyClose]
    use N
    simp_all [Rat.CloseSeq]
    intro n hn'
    simp_all [Rat.Close]
    have hNpos : (0:ℤ) ≤ N := by positivity
    have hnpos : (0:ℤ) ≤ n := by linarith
    rw [if_pos hnpos, if_pos hnpos]
    specialize hn (n.toNat) (by omega)
    exact hn

lemma Rat.eventuallyClose_symm (ε : ℚ) (a b : ℕ → ℚ) :
  ε.EventuallyClose (a:Sequence) (b:Sequence) → ε.EventuallyClose (b:Sequence) (a:Sequence) := by
  intro hab
  have hab' := (Rat.eventuallyClose_iff ε a b).mp hab
  simp_rw [abs_sub_comm (a _) (b _ )] at hab'
  exact (Rat.eventuallyClose_iff ε b a).mpr hab'

/-- Example 5.2.5 -/
example : ¬ (0.1:ℚ).CloseSeq ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  intro h
  specialize h 0 (by simp) (by simp)
  simp_all [Rat.Close]
  norm_num at h

example : (0.1:ℚ).EventuallyClose
  ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 1
  simp_all [Rat.CloseSeq]
  intro n hn
  rw [if_pos (by positivity), if_pos (by positivity)]
  simp_all [Rat.Close]
  rw [← two_mul]
  rw [abs_mul]
  rw [← neg_add']
  norm_num
  have hexp : (-1 + -n) ≤ -2 := by linarith
  have hpow : (10:ℚ) ^ (-1 + -n) ≤ 10 ^ (-2 : ℤ) := by
    exact (zpow_le_zpow_iff_right₀ rfl).mpr hexp
  have hmul : 2 * (10:ℚ) ^ (-1 + -n) ≤ 2 * 10 ^ (-2 : ℤ) := by
    exact Rat.mul_le_mul_of_nonneg_left hpow rfl
  norm_num at hmul
  linarith

example : (0.01:ℚ).EventuallyClose
  ((fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)):Sequence)
  ((fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)):Sequence) := by
  use 2
  simp_all [Rat.CloseSeq]
  intro n hn
  rw [if_pos (by positivity), if_pos (by positivity)]
  simp_all [Rat.Close]
  rw [← two_mul]
  rw [abs_mul]
  rw [← neg_add']
  norm_num
  have hexp : (-1 + -n) ≤ -3 := by linarith
  have hpow : (10:ℚ) ^ (-1 + -n) ≤ 10 ^ (-3 : ℤ) := by
    exact (zpow_le_zpow_iff_right₀ rfl).mpr hexp
  have hmul : 2 * (10:ℚ) ^ (-1 + -n) ≤ 2 * 10 ^ (-3 : ℤ) := by
    exact Rat.mul_le_mul_of_nonneg_left hpow rfl
  norm_num at hmul
  linarith

/-- Definition 5.2.6 (Equivalent sequences) -/
abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (a:Sequence) (b:Sequence)

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (a:Sequence) (b:Sequence) := by rfl

/-- Definition 5.2.6 (Equivalent sequences) -/
lemma Sequence.equiv_iff (a b: ℕ → ℚ) : Equiv a b ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| ≤ ε := by
  constructor
  · intro hequiv ε hε
    specialize hequiv ε hε
    rw [Rat.eventuallyClose_iff] at hequiv
    exact hequiv
  · intro hεpos ε hε
    specialize hεpos ε hε
    exact (Rat.eventuallyClose_iff ε a b).mpr hεpos

lemma Sequence.equiv_symm (a b : ℕ → ℚ) : Equiv a b → Equiv b a := by
  intro hequiv
  have hequiv' := (Sequence.equiv_iff a b).mp hequiv
  simp_rw [abs_sub_comm (a _) (b _)] at hequiv'
  exact (Sequence.equiv_iff b a).mpr hequiv'

/-- Proposition 5.2.8 -/
lemma Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [equiv_iff]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Section_4_3.two_pow_geq (N+1)) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN; use N; intro n hn
  linarith [hab' N n hn]

/-- Exercise 5.2.1 -/
theorem Sequence.isCauchy_of_equiv {a b: ℕ → ℚ} (hab: Equiv a b) :
    (a:Sequence).IsCauchy ↔ (b:Sequence).IsCauchy := by
  constructor
  · intro hcauchy ε hε
    specialize hcauchy (ε / 3) (by positivity)
    specialize hab (ε / 3)     (by positivity)
    obtain ⟨N, ⟨hge, hsteady⟩⟩ := hcauchy
    obtain ⟨M, hclose⟩ := hab
    use max N M
    constructor
    · simp_all
    · intro n hn m hm
      simp at hn hm
      lift n to ℕ using (by omega)
      lift m to ℕ using (by omega)
      have hclosem := hclose m (by simp_all) (by simp_all)
      have hclosen := hclose n (by simp_all) (by simp_all)
      specialize hsteady n (by simp_all) m (by simp_all)
      simp_all [Rat.Close]
      calc |b n - b m| = |(b n - a n) + ((a n - a m) + (a m - b m))|  := by congr; linarith
                     _ ≤ |b n - a n| + |(a n - a m) + (a m - b m)|    := by exact Section_4_3.abs_add (b n - a n) ((a n - a m) + (a m - b m))
                     _ ≤ |b n - a n| + (|a n - a m| + |a m - b m|)    := by gcongr; exact Section_4_3.abs_add (a n - a m) _
                     _ ≤ |a n - b n| + (|a n - a m| + |a m - b m|)    := by rw [abs_sub_comm]
                     _ ≤ (ε / 3) + (ε / 3) + (ε / 3)                  := by linarith
                     _ = ε                                            := by field
  · intro hcauchy ε hε
    specialize hcauchy (ε / 3) (by positivity)
    specialize hab (ε / 3)     (by positivity)
    obtain ⟨N, ⟨hge, hsteady⟩⟩ := hcauchy
    obtain ⟨M, hclose⟩ := hab
    use max N M
    constructor
    · simp_all
    · intro n hn m hm
      simp at hn hm
      lift n to ℕ using (by omega)
      lift m to ℕ using (by omega)
      have hclosem := hclose m (by simp_all) (by simp_all)
      have hclosen := hclose n (by simp_all) (by simp_all)
      specialize hsteady n (by simp_all) m (by simp_all)
      simp_all [Rat.Close]
      calc |a n - a m| = |(a n - b n) + ((b n - b m) + (b m - a m))|  := by congr; linarith
                     _ ≤ |a n - b n| + |(b n - b m) + (b m - a m)|    := by exact Section_4_3.abs_add (a n - b n)  ((b n - b m) + (b m - a m))
                     _ ≤ |a n - b n| + (|b n - b m| + |b m - a m|)    := by gcongr; exact Section_4_3.abs_add (b n - b m) _
                     _ ≤ |a n - b n| + (|b n - b m| + |a m - b m|)    := by rw [abs_sub_comm (b m) (a m)]
                     _ ≤ (ε / 3) + (ε / 3) + (ε / 3)                  := by linarith
                     _ = ε                                            := by field


lemma Sequence.isBounded_of_eventuallyClose' {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded →  (b:Sequence).IsBounded := by
    intro habdd
    obtain ⟨L, ⟨hLpos, hLbd⟩⟩ := habdd
    rw [BoundedBy] at hLbd
    have hab' := (Rat.eventuallyClose_iff ε a b).mp hab
    obtain ⟨N, hN⟩ := hab'
    set headbound := (Finset.Icc 0 N).sup' (Finset.nonempty_Icc.mpr (by positivity)) (λ n => |b n|)
    set tailbound := |ε| + L
    have hmax : 0 ≤ max headbound tailbound := by
      apply le_max_iff.mpr
      right
      positivity
    use max headbound tailbound
    constructor
    · exact hmax
    · rw [BoundedBy]
      intro n
      by_cases vanished : n < 0
      · have fact := (b:Sequence).vanish n vanished
        rw [fact]
        rw [abs_zero]
        exact hmax
      · specialize hLbd n
        lift n to ℕ using (by omega)
        by_cases headtail : n ≤ N
        · have fact : n ∈ Finset.Icc 0 N := Finset.mem_Icc.mpr ⟨(by positivity), headtail⟩
          simp; left
          unfold headbound
          exact Finset.le_sup' (λ n => |b n|) fact
        · push_neg at headtail
          simp at hLbd
          simp; right
          unfold tailbound
          specialize hN n (by linarith)
          have habsnonneg : 0 ≤ |a n - b n| := by exact Section_4_3.dist_nonneg (a n) (b n)
          have hεnonneg :   0 ≤ ε := by linarith
          have hεabs :      |ε| = ε := by exact abs_of_nonneg hεnonneg
          calc |b n| = |b n - a n + a n|   := by ring_nf
                   _ ≤ |b n - a n| + |a n| := by exact Section_4_3.abs_add (b n - a n) (a n)
                   _ = |a n - b n| + |a n| := by rw [abs_sub_comm]
                   _ ≤ ε + |a n|           := by linarith
                   _ = |ε| + |a n|         := by rw [hεabs]
                   _ ≤ |ε| + L             := by linarith

/-- Exercise 5.2.2 -/
theorem Sequence.isBounded_of_eventuallyClose {ε:ℚ} {a b: ℕ → ℚ} (hab: ε.EventuallyClose a b) :
    (a:Sequence).IsBounded ↔ (b:Sequence).IsBounded := by
  constructor
  · intro habdd
    exact isBounded_of_eventuallyClose' hab habdd
  · intro hbddd
    have hba : ε.EventuallyClose b a := by exact Rat.eventuallyClose_symm ε a b hab
    exact isBounded_of_eventuallyClose' hba hbddd

end Chapter5
