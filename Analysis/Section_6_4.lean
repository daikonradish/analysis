import Mathlib.Tactic
import Analysis.Section_6_3

/-!
# Analysis I, Section 6.4: Limsup, liminf, and limit points

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Lim sup and lim inf of sequences
- Limit points of sequences
- Comparison and squeeze tests
- Completeness of the reals

-/

abbrev Real.Adherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) := ∃ n ≥ a.m, ε.Close (a n) x

abbrev Real.ContinuallyAdherent (ε:ℝ) (a:Chapter6.Sequence) (x:ℝ) :=
  ∀ N ≥ a.m, ε.Adherent (a.from N) x

namespace Chapter6

open EReal

abbrev Sequence.LimitPoint (a:Sequence) (x:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.ContinuallyAdherent a x

theorem Sequence.limit_point_def (a:Sequence) (x:ℝ) :
  a.LimitPoint x ↔ ∀ ε > 0, ∀ N ≥ a.m, ∃ n ≥ N, |a n - x| ≤ ε := by
    unfold LimitPoint Real.ContinuallyAdherent Real.Adherent
    peel with ε hε
    peel with N hN
    constructor
    · intro hclose
      simp_all
      obtain ⟨N₀, hN₀, hN₀dist⟩ := hclose
      use N₀
      constructor
      · exact hN₀
      · rwa [if_pos (hN₀), Real.dist_eq] at hN₀dist
    · intro habs
      obtain ⟨N₀, hN₀, hN₀abs⟩ := habs
      use N₀
      constructor
      · simp_all
      · simp_all
        rwa [Real.dist_eq]

noncomputable abbrev Example_6_4_3 : Sequence := (fun (n:ℕ) ↦ 1 - (10:ℝ)^(-(n:ℤ)-1))

/-- Example 6.4.3 -/
example : (0.1:ℝ).Adherent Example_6_4_3 0.8 := by
  use 0
  constructor
  · simp_all
  · simp_all
    rw [Real.dist_eq]
    norm_num

/-- Example 6.4.3 -/
example : ¬ (0.1:ℝ).ContinuallyAdherent Example_6_4_3 0.8 := by
  rw [Real.ContinuallyAdherent]
  simp_all
  use 1
  constructor
  · simp_all
  · intro x hx hx2
    rw [Real.dist_eq]
    ring_nf
    have hlb : (10:ℝ) ^ (-1-x) > 0 := by positivity
    have hexp : - 1 - x ≤ -2 := by linarith
    have hpow : (10:ℝ) ^ (-1 - x) ≤ (10:ℝ) ^ ((-2):ℤ) := by
      gcongr
      norm_num
    have hpow' : (10:ℝ) ^ (-1 - x) ≤ 1/5 := by
      have : (10:ℝ) ^ ((-2):ℤ) ≤ 1/5 := by norm_num
      grind
    have hpow'' : 1 / 5 - (10:ℝ) ^ (-1 - x) ≥ 0 := by linarith
    rw [abs_of_nonneg hpow'']
    suffices alternatively : (10:ℝ) ^ (-1 - x) < 1/5 - 1/10 by linarith
    norm_num
    norm_num at hpow
    linarith

/-- Example 6.4.3 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_3 1 := by
  intro N hN
  simp at hN
  use N
  constructor
  · grind
  · simp_all
    have : (0.1:ℝ) = 10 ^ (-1:ℤ) := by norm_num
    rw [this]
    gcongr <;> simp_all


/-- Example 6.4.3 -/
example : Example_6_4_3.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  unfold Example_6_4_3
  simp_all
  have hrwexp (n : ℤ) : (10:ℝ) ^ (-n-1) = (1/10) ^ (n+1) := by
    have : - n - 1 = -(n+1) := by linarith
    rw [this]
    rw [zpow_neg, ← inv_zpow]
    norm_num
  lift N to ℕ using (by omega)
  have htenth : 1 / 10 < (1:ℝ) := by grind
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε htenth
  use max N N₀
  constructor
  · grind
  · rw [if_pos (by omega)]
    norm_num
    specialize hrwexp N₀
    have : (-N₀:ℤ) - 1 ≥ -max (N:ℤ) (N₀:ℤ) - 1 := by grind
    calc _ ≤ (10:ℝ) ^ ((-N₀:ℤ) - 1)            := by gcongr; linarith
         _ = (1 / 10) ^ (N₀+1)                 := by exact hrwexp
         _ = (1/10) ^ N₀ * (1/10)^1            := by rw [pow_add]
         _ = (1/10)^ N₀ * (1/10)               := by rw [pow_one]
         _ ≤ ε * (1/10)                        := by linarith
         _ ≤ ε                                 := by linarith

noncomputable abbrev Example_6_4_4 : Sequence :=
  (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

/-- Example 6.4.4 -/
example : (0.1:ℝ).Adherent Example_6_4_4 1 := by
  use 0
  constructor
  · simp_all
  · simp_all
    norm_num

/-- Example 6.4.4 -/
example : (0.1:ℝ).ContinuallyAdherent Example_6_4_4 1 := by
  rw [Real.ContinuallyAdherent]
  intro N hN
  simp at hN
  lift N to ℕ using (by omega)
  rw [Real.Adherent]
  simp_all
  obtain ⟨N', hN⟩ := Nat.exists_gt N
  norm_cast at hN
  have h2N : N' * 2 ≥ N := by grind
  use (N' * 2)
  constructor
  · grind
  · rw [if_pos (by grind), if_pos (by grind)]
    rw [Real.dist_eq]
    have : ((N':ℤ) * 2).toNat = (N':ℤ).toNat * 2 := by exact Int.toNat_mul (by grind) (by grind)
    rw [this, pow_mul]
    simp
    have hsimplify (n : ℕ) : ((-1:ℝ) ^ n) ^ 2 = 1 := by
      norm_num [← pow_mul]
    rw [hsimplify]
    simp
    have : (-(↑N' * 2) - 1) = - ((N':ℤ) * 2 + 1) := by grind
    rw [this]
    rw [zpow_neg, ← inv_zpow]
    norm_num
    have : 1 ≤ N'*2+1 := by grind
    -- ⊢ (1 / 10) ^ (↑N' * 2 + 1) ≤ 1 / 10
    have := pow_le_pow_of_le_one (a:=((1/10):ℝ)) (m:=1) (n:=N'*2+1) (by grind) (by grind) this
    rw [pow_one] at this
    exact_mod_cast this

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint 1 := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  simp at hN
  lift N to ℕ using (by omega)
  unfold Example_6_4_4
  have hrwexp (n : ℤ) : (10:ℝ) ^ (-n-1) = (1/10) ^ (n+1) := by
    have : - n - 1 = -(n+1) := by linarith
    rw [this]
    rw [zpow_neg, ← inv_zpow]
    norm_num
  have htenth : 1 / 10 < (1:ℝ) := by grind
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε htenth
  have hN₀' : (1 / 10) ^ (N₀:ℤ) < ε := by exact_mod_cast hN₀
  use (max N N₀) * 2
  constructor
  · grind
  · simp
    rw [Int.toNat_mul (by grind) (by grind)]
    simp
    calc _ ≤ (10:ℝ) ^ ((-(N₀:ℤ) * 2)-1)           := by gcongr <;> grind
         _ ≤ (10:ℝ) ^ (-(N₀:ℤ)-1)                 := by gcongr <;> grind
         _ = (1/10:ℝ) ^ ((N₀:ℤ) + 1)              := by rw [hrwexp N₀]
         _ = (1/10:ℝ) ^ (N₀:ℤ) * (1/10:ℝ)^(1:ℤ)   := by rw [zpow_add₀ (by norm_num : (1/10:ℝ) ≠ 0)]
         _ = (1/10:ℝ) ^ (N₀:ℤ) * (1/10:ℝ)         := by rw [zpow_one]
         _ ≤ ε * (1/10:ℝ)                         := by linarith
         _ ≤ ε                                    := by linarith

/-- Example 6.4.4 -/
example : Example_6_4_4.LimitPoint (-1) := by
  rw [Sequence.limit_point_def]
  intro ε hε N hN
  simp at hN
  lift N to ℕ using (by omega)
  unfold Example_6_4_4
  have hrwexp (n : ℤ) : (10:ℝ) ^ (-n-1) = (1/10) ^ (n+1) := by
    have : - n - 1 = -(n+1) := by linarith
    rw [this]
    rw [zpow_neg, ← inv_zpow]
    norm_num
  have htenth : 1 / 10 < (1:ℝ) := by grind
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε htenth
  have hN₀' : (1 / 10) ^ (N₀:ℤ) < ε := by exact_mod_cast hN₀
  use ((max N N₀) * 2) + 1
  constructor
  · grind
  · simp
    rw [if_pos (by grind)]
    rw [Int.toNat_add (by grind) (by grind)]
    simp
    rw [Int.toNat_mul (by grind) (by grind)]
    simp
    rw [pow_add]
    simp
    rw [max_eq_left (by grind)]
    calc _ ≤ (10:ℝ) ^ ((-(N₀:ℤ) * 2)-1)           := by gcongr <;> grind
         _ ≤ (10:ℝ) ^ (-(N₀:ℤ)-1)                 := by gcongr <;> grind
         _ = (1/10:ℝ) ^ ((N₀:ℤ) + 1)              := by rw [hrwexp N₀]
         _ = (1/10:ℝ) ^ (N₀:ℤ) * (1/10:ℝ)^(1:ℤ)   := by rw [zpow_add₀ (by norm_num : (1/10:ℝ) ≠ 0)]
         _ = (1/10:ℝ) ^ (N₀:ℤ) * (1/10:ℝ)         := by rw [zpow_one]
         _ ≤ ε * (1/10:ℝ)                         := by linarith
         _ ≤ ε                                    := by linarith

/-- Example 6.4.4 -/
example : ¬ Example_6_4_4.LimitPoint 0 := by
  rw [Sequence.limit_point_def]
  push_neg
  use 0.5
  constructor
  · norm_num
  · use 0
    simp_all
    intro n hn
    lift n to ℕ using (by omega)
    have : (10:ℝ) ^ ((-n:ℤ) - 1) > 0 := by positivity
    have : 1 + (10:ℝ) ^ ((-n:ℤ) - 1) > 0 := by positivity
    rw [abs_of_pos this]
    suffices whatever : 0.5 - 1 < 1 + (10:ℝ) ^ ((-n:ℤ) - 1) - 1 by linarith
    norm_num
    linarith

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit {a:Sequence} {x:ℝ} (h: a.TendsTo x) : a.LimitPoint x := by
  rw [Sequence.tendsTo_iff] at h
  rw [Sequence.limit_point_def]
  intro ε hε N hNam
  obtain ⟨M, hM⟩ := h ε hε
  use max N M
  constructor <;> simp_all

/-- Proposition 6.4.5 / Exercise 6.4.1 -/
theorem Sequence.limit_point_of_limit_unique {a:Sequence} {x y:ℝ} (h: a.TendsTo x) (hy: a.LimitPoint y) : x = y := by
  sorry

/--
  A technical issue uncovered by the formalization: the upper and lower sequences of a real
  sequence take values in the extended reals rather than the reals, so the definitions need to be
  adjusted accordingly.
-/
noncomputable abbrev Sequence.upperseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).sup

noncomputable abbrev Sequence.limsup (a:Sequence) : EReal :=
  sInf { x | ∃ N ≥ a.m, x = a.upperseq N }

noncomputable abbrev Sequence.lowerseq (a:Sequence) : ℤ → EReal := fun N ↦ (a.from N).inf

noncomputable abbrev Sequence.liminf (a:Sequence) : EReal :=
  sSup { x | ∃ N ≥ a.m, x = a.lowerseq N }


noncomputable abbrev Example_6_4_7 : Sequence := (fun (n:ℕ) ↦ (-1:ℝ)^n * (1 + (10:ℝ)^(-(n:ℤ)-1)))

lemma example647_even_decreasing {n₁ n₂ : ℕ} (heven₁: Even n₁) (heven₂: Even n₂) (h: n₁ ≤ n₂) :
  (Example_6_4_7:Sequence).seq n₁ ≥  (Example_6_4_7:Sequence).seq n₂ := by
    obtain ⟨d₁, hd₁⟩ := heven₁
    obtain ⟨d₂, hd₂⟩ := heven₂
    unfold Example_6_4_7
    simp
    nth_rewrite 1 [hd₁, hd₂]
    simp; grind

lemma example647_even_odd {n₁ n₂ : ℕ}  (heven : Even n₁) (hodd: Odd n₂) :
    (Example_6_4_7:Sequence).seq n₁ ≥  (Example_6_4_7:Sequence).seq n₂ := by
    obtain ⟨d₁, hd₁⟩ := heven
    obtain ⟨d₂, hd₂⟩ := hodd
    unfold Example_6_4_7
    simp
    nth_rewrite 1 [hd₁, hd₂]
    rw [pow_add]
    simp
    have f1 : (10:ℝ) ^ (-(n₁:ℤ) - 1) > 0 := by positivity
    have f2 : (10:ℝ) ^ (-(n₂:ℤ) - 1) > 0 := by positivity
    grind

lemma example647_even_max {n₁ n₂ : ℕ} (heven: Even n₁) (h: n₁ ≤ n₂) :
  (Example_6_4_7:Sequence).seq n₁ ≥  (Example_6_4_7:Sequence).seq n₂ := by
  by_cases heven' : Even n₂
  · exact example647_even_decreasing heven heven' h
  · rw [Nat.not_even_iff_odd] at heven'
    exact example647_even_odd heven heven'

lemma example647_upperseq_equivalent_def (n:ℕ) :
    Example_6_4_7.upperseq n = if Even n then 1 + (10:ℝ)^(-(n:ℤ)-1) else 1 + (10:ℝ)^(-(n:ℤ)-2) := by
  split_ifs with hif
  -- First, handle the even case. In this case, a n is the sup.
  · apply le_antisymm
    · have hseqn :  (Example_6_4_7:Sequence).seq n = 1 + (10:ℝ)^(-(n:ℤ)-1) := by
        unfold Example_6_4_7; simp_all
      apply csSup_le
      · use  (Example_6_4_7:Sequence).seq n
        use n
        constructor
        · grind
        · simp_all
      · rw [← hseqn]
        intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        have hgreater : N ≥ n := by grind
        have h0 : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ hgreater] at hN
        rw [hN]
        have desired := example647_even_max hif (by exact_mod_cast hgreater)
        exact_mod_cast desired
    · apply le_csSup
      · use (Example_6_4_7:Sequence).seq n
        intro y hy
        obtain ⟨N, hNam, hN⟩ := hy
        have hgreater : N ≥ n := by grind
        have h0 : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ hgreater] at hN
        rw [hN]
        have desired := example647_even_max hif (by exact_mod_cast hgreater)
        exact_mod_cast desired
      · use n
        constructor <;> simp_all
  -- Now, handle the odd case. a (n+1) is the sup.
  · rw [Nat.not_even_iff_odd] at hif
    have hnplusone : Even (n+1) := by exact Odd.add_one hif
    apply le_antisymm
    · have hseqnone : (Example_6_4_7:Sequence).seq (n+1) = 1 + (10:ℝ)^(-(n:ℤ)-2) := by
        unfold Example_6_4_7
        simp_all
        rw [if_pos (by grind)]
        ring_nf
      apply csSup_le
      · use (Example_6_4_7:Sequence).seq n
        use n
        constructor <;> simp_all
      · rw [← hseqnone]
        intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        have hgreater : N ≥ n := by grind
        have h0 : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ hgreater] at hN
        rw [hN]
        norm_cast at hgreater
        rcases Nat.lt_or_eq_of_le hgreater with hlt | heq
        · observe : n+1 ≤ N
          have desired := example647_even_max hnplusone (by exact_mod_cast this)
          exact_mod_cast desired
        · rw [← heq]
          have desired := example647_even_odd hnplusone hif
          exact_mod_cast desired
    · apply le_csSup
      · use (Example_6_4_7:Sequence).seq (n+1)
        intro y hy
        obtain ⟨N, hNam, hN⟩ := hy
        have hgreater : N ≥ n := by grind
        have h0 : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ hgreater] at hN
        rw [hN]
        norm_cast at hgreater
        rcases Nat.lt_or_eq_of_le hgreater with hlt | heq
        · observe : n+1 ≤ N
          have desired := example647_even_max hnplusone (by exact_mod_cast this)
          exact_mod_cast desired
        · rw [← heq]
          have desired := example647_even_odd hnplusone hif
          exact_mod_cast desired
      · use (n+1)
        unfold Example_6_4_7
        constructor
        · simp_all
        · simp_all
          rw [if_pos (by grind)]
          ring_nf
          norm_cast

example : Example_6_4_7.limsup = 1 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · set n := (Example_6_4_7:Sequence).m
    have f1 : n ≥ (Example_6_4_7:Sequence).m := by grind
    have f2 : n ≥ 0 := by grind
    use (Example_6_4_7:Sequence).seq 0
    use 0
    constructor
    · exact f1
    · apply le_antisymm
      · apply le_csSup
        · use (Example_6_4_7:Sequence).seq 0
          intro y hy
          obtain ⟨N, hNam, hN⟩ := hy
          have : N ≥ 0 := by grind
          lift N to ℕ using (by omega)
          rw [Sequence.from_eval _ (by grind)] at hN
          rw [hN]
          norm_cast
          have heven : Even 0 := by grind
          simp at hNam
          have hge0 : N ≥ 0 := by grind
          have desired := example647_even_max heven hge0
          exact_mod_cast desired
        · use 0
          constructor <;> simp_all
      · apply csSup_le
        · use (Example_6_4_7:Sequence).seq 0
          use 0
          constructor <;> grind
        · intro b hb
          obtain ⟨N, hNam, hN⟩ := hb
          have h0 : N ≥ 0 := by grind
          lift N to ℕ using (by omega)
          rw [Sequence.from_eval _ (by grind)] at hN
          rw [hN]
          have heven : Even 0 := by grind
          have hge0 : N ≥ 0 := by grind
          have desired := example647_even_max heven hge0
          exact_mod_cast desired
  · intro a ha
    obtain ⟨N, hNam, hupperseq⟩ := ha
    simp at hNam
    lift N to ℕ using (by omega)
    rw [example647_upperseq_equivalent_def] at hupperseq
    by_cases hevodd : Even N
    · rw [if_pos hevodd] at hupperseq
      rw [hupperseq]
      norm_cast
      norm_num
      positivity
    · rw [if_neg hevodd] at hupperseq
      rw [hupperseq]
      norm_cast
      norm_num
      positivity
  · intro w hw
    obtain ⟨c', heq⟩ | htop | hbot := EReal.def w
    · rw [← heq] at hw
      have hw' := EReal.coe_lt_coe_iff.mp hw
      have hc1 : c' - 1 > 0 := by linarith
      have htenth : (1/10:ℝ) < 1 := by norm_num
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc1 htenth
      use Example_6_4_7.upperseq (2 * N)
      constructor
      · use 2 * N
        simp_all
      · rw [← heq]
        norm_cast
        rw [example647_upperseq_equivalent_def]
        simp
        norm_cast
        have : - (((2*N):ℕ):ℤ) - 1 = -((((2*N):ℕ):ℤ) +1) := by ring_nf
        rw [this]
        rw [zpow_neg, ← inv_zpow]
        observe : (1/10:Real) < 1
        have almostthere :  (1/10:ℝ) ^ (2 * N + 1) < (1/10:ℝ) ^ N := by
          exact (pow_lt_pow_iff_right_of_lt_one₀
                    (a:=(1/10:ℝ))
                    (n:=N)
                    (m:=2*N+1)
                    (by linarith)
                    (by linarith)).mpr (by linarith)
        suffices alt : (10:ℝ)⁻¹ ^ ((((2 * N):ℕ):ℤ) + 1) < c' - 1 by linarith
        have : (10:ℝ)⁻¹ = (1/10:ℝ) := by norm_num
        rw [this]
        calc _ < (1 / 10) ^ N := by exact_mod_cast almostthere
             _ < c' - 1       := by exact hN
    · use Example_6_4_7.upperseq 0
      constructor
      · use 0
      · rw [htop]
        rw [Sequence.upperseq]
        have : (Example_6_4_7.from 0).sup ≤ (Example_6_4_7).seq 0 := by
          apply csSup_le
          · use (Example_6_4_7).seq 0
            use 0
            constructor <;> simp_all
          · intro b hb
            obtain ⟨N, hNam, hN⟩ := hb
            have h0 : N ≥ 0 := by grind
            lift N to ℕ using (by omega)
            rw [Sequence.from_eval _ (by grind)] at hN
            rw [hN]
            have heven : Even 0 := by grind
            have hge0 : N ≥ 0 := by grind
            have desired := example647_even_max heven hge0
            exact_mod_cast desired
        exact this.trans_lt (EReal.coe_lt_top _)
    · rw [hbot] at hw
      exact absurd hw not_lt_bot

lemma example647_odd_increasing {n₁ n₂ : ℕ} (hodd₁: Odd n₁) (hodd₂: Odd n₂) (h: n₁ ≤ n₂) :
  (Example_6_4_7:Sequence).seq n₁ ≤  (Example_6_4_7:Sequence).seq n₂ := by
    obtain ⟨d₁, hd₁⟩ := hodd₁
    obtain ⟨d₂, hd₂⟩ := hodd₂
    unfold Example_6_4_7
    simp
    nth_rewrite 1 [hd₁, hd₂]
    rw [pow_add, pow_add]
    simp_all
    grind

lemma example647_odd_min {n₁ n₂ : ℕ} (hodd: Odd n₁) (h: n₁ ≤ n₂) :
  (Example_6_4_7:Sequence).seq n₁ ≤ (Example_6_4_7:Sequence).seq n₂ := by
  by_cases hodd' : Odd n₂
  · exact example647_odd_increasing hodd hodd' h
  · rw [Nat.not_odd_iff_even] at hodd'
    exact example647_even_odd hodd' hodd

lemma example647_lowerseq_equivalent_def (n:ℕ) :
    Example_6_4_7.lowerseq n
    = if Even n then -(1 + (10:ℝ)^(-(n:ℤ)-2)) else -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  split_ifs with hif
  · have hseqnone :  (Example_6_4_7:Sequence).seq (n+1) = -(1 + (10:ℝ)^(-(n:ℤ)-2)) := by
      unfold Example_6_4_7
      simp_all
      grind
    have hnplusone : Odd (n+1) := by exact Even.add_one hif
    apply le_antisymm
    · apply csInf_le
      · use (Example_6_4_7:Sequence).seq (n+1)
        intro y hy
        obtain ⟨N, hNam, hN⟩ := hy
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        rcases Nat.lt_or_eq_of_le hNam with hlt | heq
        · observe : n+1 ≤ N
          exact example647_odd_min hnplusone this
        · rw [← heq]
          exact example647_even_odd hif hnplusone
      · use n + 1
        constructor <;> simp_all
    · apply le_csInf
      · use (Example_6_4_7:Sequence).seq n
        use n; simp
      · intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [← hseqnone, hN]
        simp at hNam
        norm_cast
        rcases Nat.lt_or_eq_of_le hNam with hlt | heq
        · observe : n+1 ≤ N
          exact example647_odd_min hnplusone this
        · rw [← heq]
          exact example647_even_odd hif hnplusone
  · rw [Nat.not_even_iff_odd] at hif
    apply le_antisymm
    · apply csInf_le
      · use (Example_6_4_7:Sequence).seq 1
        intro y hy
        obtain ⟨N, hNam, hN⟩ := hy
        simp at hNam
        lift N to ℕ using (by omega)
        rw [hN]
        norm_cast
        rw [Sequence.from_eval _ (by grind)]
        observe hodd : Odd 1
        by_cases hevodd : Even N
        · exact_mod_cast example647_even_odd hevodd hodd
        · rw [Nat.not_even_iff_odd] at hevodd
          have hge1 : N ≥ 1 := by grind
          exact_mod_cast example647_odd_increasing hodd hevodd hge1
      · use n
        constructor <;> simp_all
    · apply le_csInf
      · use (Example_6_4_7:Sequence).seq n
        use n
        constructor <;> simp_all
      · have hseqn :  (Example_6_4_7:Sequence).seq n = -(1 + (10:ℝ)^(-(n:ℤ)-1)) := by
          unfold Example_6_4_7
          simp_all
        intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        rw [Sequence.from_eval _ (by grind)] at hN
        simp at hNam
        rw [← hseqn, hN]
        norm_cast
        have desired := example647_odd_min hif hNam
        linarith

example : Example_6_4_7.liminf = -1 := by
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use (Example_6_4_7:Sequence).seq 1
    use 1
    constructor
    · simp
    · apply le_antisymm
      · apply le_csInf
        · use (Example_6_4_7:Sequence).seq 1
          use 1; simp
        · intro b hb
          obtain ⟨N, hNam, hN⟩ := hb
          have : N ≥ 0 := by grind
          lift N to ℕ using (by omega)
          rw [Sequence.from_eval _ (by grind)] at hN
          simp at hNam
          rw [hN]
          norm_cast
          observe hodd : Odd 1
          exact example647_odd_min hodd hNam
      · apply csInf_le
        · use (Example_6_4_7:Sequence).seq 1
          intro b hb
          obtain ⟨N, hNam, hN⟩ := hb
          have : N ≥ 0 := by grind
          lift N to ℕ using (by omega)
          rw [Sequence.from_eval _ (by grind)] at hN
          simp at hNam
          rw [hN]
          norm_cast
          observe hodd : Odd 1
          exact example647_odd_min hodd hNam
        · use 1; simp
  · intro a ha
    obtain ⟨N, hNam, hN⟩ := ha
    have : N ≥ 0 := by grind
    lift N to ℕ using (by omega)
    rw [example647_lowerseq_equivalent_def N] at hN
    rw [hN]
    split_ifs
    · have : (10:ℝ) ^ (-(N:ℤ) - 2) > 0 := by positivity
      have : -(1+(10:ℝ) ^ (-(N:ℤ) - 2)) ≤ -1 := by linarith
      exact EReal.coe_le_coe this
    · have : (10:ℝ) ^ (-(N:ℤ) - 1) > 0 := by positivity
      have : -(1+(10:ℝ) ^ (-(N:ℤ) - 1)) ≤ -1 := by linarith
      exact EReal.coe_le_coe this
  · intro w hw
    obtain ⟨c', heq⟩ | htop | hbot := EReal.def w
    · rw [← heq] at hw
      have hw' := EReal.coe_lt_coe_iff.mp hw
      have hc1 : -1-c' > 0 := by linarith
      have htenth : (1/10:ℝ) < 1 := by norm_num
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc1 htenth
      use Example_6_4_7.lowerseq N
      constructor
      · use N
        constructor <;> grind
      · rw [← heq]
        rw [example647_lowerseq_equivalent_def]
        norm_cast
        have ht : 10⁻¹ = (1 / 10:ℝ) := by norm_num
        split_ifs
        · rw [← neg_add' (N:ℤ) 2, zpow_neg, ← inv_zpow, ht, neg_add']
          suffices alt : (1 / 10) ^ ((N:ℤ) + 2) < -1 -c' by linarith
          have hN': (1 / 10) ^ (N:ℤ) < -1 - c' := by exact_mod_cast hN
          have : (1 / 10:ℝ) ^ ((N:ℤ) + 2) <  (1 / 10:ℝ) ^ (N:ℤ) := by
            rw [zpow_add₀ (by norm_num : (1/10:ℝ) ≠ 0)]
            norm_num
          linarith
        · rw [← neg_add' (N:ℤ) 1, zpow_neg, ← inv_zpow, ht, neg_add']
          suffices alt : (1 / 10) ^ ((N:ℤ) + 1) < -1 -c' by linarith
          have hN': (1 / 10) ^ (N:ℤ) < -1 - c' := by exact_mod_cast hN
          have : (1 / 10:ℝ) ^ ((N:ℤ) + 1) <  (1 / 10:ℝ) ^ (N:ℤ) := by
            rw [zpow_add₀ (by norm_num : (1/10:ℝ) ≠ 0)]
            norm_num
          linarith
    · rw [htop] at hw
      exact absurd hw not_top_lt
    · use Example_6_4_7.lowerseq 1
      constructor
      · use 1
        constructor <;> simp_all
      · rw [Sequence.lowerseq]
        have :  (Example_6_4_7).seq 1 ≤ (Example_6_4_7.from 1).inf := by
          apply le_csInf
          · use (Example_6_4_7:Sequence).seq 1
            use 1; simp
          · intro y hy
            obtain ⟨N, hNam, hN⟩ := hy
            simp at hNam
            rw [Sequence.from_eval _ (by grind)] at hN
            lift N to ℕ using (by omega)
            rw [hN]
            norm_cast
            by_cases hN0 : N = 0
            · observe heven : Even 0
              observe hodd : Odd 1
              rw [hN0]
              exact example647_even_odd heven hodd
            · observe hodd : Odd 1
              observe hge1 : N ≥ 1
              exact example647_odd_min hodd hge1
        rw [hbot]
        exact this.trans_lt' (EReal.bot_lt_coe _)

example : Example_6_4_7.sup = (1.1:ℝ) := by
  have : Example_6_4_7.seq 0 = 1.1 := by norm_num
  rw [← this]
  apply le_antisymm
  · apply csSup_le
    · use (Example_6_4_7:Sequence).seq 0
      use 0
    · intro y hy
      obtain ⟨N, hNam, hN⟩ := hy
      simp at hNam
      lift N to ℕ using (by omega)
      rw [hN]
      norm_cast
      observe hge : 0 ≤ N
      observe heven : Even 0
      exact example647_even_max heven hge
  · apply le_csSup
    · use (Example_6_4_7:Sequence).seq 0
      intro y hy
      obtain ⟨N, hNam, hN⟩ := hy
      simp at hNam
      lift N to ℕ using (by omega)
      rw [hN]
      norm_cast
      observe hge : 0 ≤ N
      observe heven : Even 0
      exact example647_even_max heven hge
    · use 0

example : Example_6_4_7.inf = (-1.01:ℝ) := by
  have : Example_6_4_7.seq 1 = -1.01 := by norm_num
  rw [← this]
  apply le_antisymm
  · apply csInf_le
    · use Example_6_4_7.seq 1
      intro y hy
      obtain ⟨N, hNam, hN⟩ := hy
      simp at hNam
      lift N to ℕ using (by omega)
      rw [hN]
      norm_cast
      by_cases hN0 : N = 0
      · rw [hN0]
        norm_num
      · observe hge : 1 ≤ N
        observe hodd : Odd 1
        exact example647_odd_min hodd hge
    · use 1; simp
  · apply le_csInf
    · use (Example_6_4_7:Sequence).seq 0
      use 0
    · intro y hy
      obtain ⟨N, hNam, hN⟩ := hy
      simp at hNam
      lift N to ℕ using (by omega)
      rw [hN]
      norm_cast
      by_cases hN0 : N = 0
      · rw [hN0]
        norm_num
      · observe hge : 1 ≤ N
        observe hodd : Odd 1
        exact example647_odd_min hodd hge

noncomputable abbrev Example_6_4_8 : Sequence := (fun (n:ℕ) ↦ if Even n then (n+1:ℝ) else -(n:ℝ)-1)

lemma example648_upperseq_eq_top (n:ℕ) : Example_6_4_8.upperseq n = ⊤ := by
  rw [Sequence.upperseq, Sequence.sup]
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def b
  · by_cases hbpos : b' ≥ 0
    · simp
      have hflrnonneg : ⌊b'⌋ ≥ 0 := by positivity
      have natflr := Int.toNat_of_nonneg hflrnonneg
      let k := (max n ⌊b'⌋.toNat) * 2
      have hkeven : Even k := by unfold k; grind
      use k
      constructor
      · grind
      · simp
        rw [if_pos (by grind), if_pos hkeven]
        unfold k
        norm_cast
        push_cast
        rify at natflr
        rw [natflr]
        have h1 := Int.lt_floor_add_one b'
        grind
    · push_neg at hbpos
      simp
      by_cases hevodd : Even n
      · use n
        simp_all
        grind
      · observe : Even (n+1)
        use (n+1)
        simp_all
        rw [if_pos (by grind)]
        grind
  · exfalso
    exact lt_irrefl ⊤ hb
  · use (Example_6_4_8:Sequence).seq n
    constructor
    · use n
      constructor <;> simp
    · exact bot_lt_coe _

example : Example_6_4_8.limsup = ⊤ := by
  unfold Sequence.limsup
  apply sInf_eq_top.mpr
  intro x hx
  obtain ⟨N, hNam, hN⟩ := hx
  simp at hNam
  lift N to ℕ using (by omega)
  rwa [example648_upperseq_eq_top N] at hN


lemma example648_lowerseq_eq_bot (n:ℕ) : Example_6_4_8.lowerseq n = ⊥ := by
  rw [Sequence.lowerseq, Sequence.inf]
  apply sInf_eq_bot.mpr
  intro b hb
  obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def b
  · by_cases hbneg : b' ≤ 0
    · simp
      have hbpos : -b' ≥ 0 := by grind
      have hflrnonneg : ⌊-b'⌋ ≥ 0 := by positivity
      have natflr := Int.toNat_of_nonneg hflrnonneg
      let k := (max n ⌊-b'⌋.toNat) * 2 + 1
      have hkodd : ¬ Even k := by unfold k; grind
      use k
      constructor
      · grind
      · simp
        rw [if_pos (by grind), if_neg hkodd]
        unfold k
        rify at natflr
        push_cast
        rw [natflr]
        have h1 := Int.lt_floor_add_one (-b')
        grind
    · push_neg at hbneg
      simp
      by_cases hevodd : Odd n
      · use n
        simp_all
        grind
      · observe : Odd (n+1)
        use (n+1)
        simp_all
        rw [if_pos (by grind)]
        grind
  · use (Example_6_4_8:Sequence).seq n
    constructor
    · use n
      constructor <;> simp
    · exact coe_lt_top _
  · exfalso
    exact lt_irrefl ⊥ hb

example : Example_6_4_8.liminf = ⊥ := by
  unfold Sequence.liminf
  apply sSup_eq_bot.mpr
  intro x hx
  obtain ⟨N, hNam, hN⟩ := hx
  simp at hNam
  lift N to ℕ using (by omega)
  rwa [example648_lowerseq_eq_bot N] at hN

noncomputable abbrev Example_6_4_9 : Sequence :=
  (fun (n:ℕ) ↦ if Even n then (n+1:ℝ)⁻¹ else -(n+1:ℝ)⁻¹)

<<<<<<< HEAD
example (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by sorry
=======
lemma example649_even_decreasing {n₁ n₂ : ℕ} (heven₁: Even n₁) (heven₂: Even n₂) (h: n₁ ≤ n₂) :
  (Example_6_4_9:Sequence).seq n₁ ≥  (Example_6_4_9:Sequence).seq n₂ := by
    unfold Example_6_4_9
    simp_all
    field_simp
    rify at h
    grind
>>>>>>> 440d3d1 (finally 6_4 is done)

lemma example649_odd_increasing {n₁ n₂ : ℕ} (hodd₁: Odd n₁) (hodd₂: Odd n₂) (h: n₁ ≤ n₂) :
  (Example_6_4_9:Sequence).seq n₁ ≤  (Example_6_4_9:Sequence).seq n₂ := by
    observe hnoteven₁ : ¬ Even n₁
    observe hnoteven₂ : ¬ Even n₂
    unfold Example_6_4_9
    simp
    rw [if_neg hnoteven₁, if_neg hnoteven₂]
    field_simp
    rify at h
    grind

lemma example649_even_odd {n₁ n₂ : ℕ}  (heven : Even n₁) (hodd: Odd n₂) :
    (Example_6_4_9:Sequence).seq n₁ ≥  (Example_6_4_9:Sequence).seq n₂ := by
    unfold Example_6_4_9
    simp
    rw [if_pos heven, if_neg (by grind)]
    field_simp
    have : (n₁:ℝ) ≥ 0 := by positivity
    have : (n₂:ℝ) ≥ 0 := by positivity
    grind

lemma example649_even_max {n₁ n₂ : ℕ} (heven: Even n₁) (h: n₁ ≤ n₂) :
  (Example_6_4_9:Sequence).seq n₁ ≥  (Example_6_4_9:Sequence).seq n₂ := by
  by_cases heven' : Even n₂
  · exact example649_even_decreasing heven heven' h
  · rw [Nat.not_even_iff_odd] at heven'
    exact example649_even_odd heven heven'

lemma example649_odd_min {n₁ n₂ : ℕ} (hodd: Odd n₁) (h: n₁ ≤ n₂) :
  (Example_6_4_9:Sequence).seq n₁ ≤ (Example_6_4_9:Sequence).seq n₂ := by
  by_cases hodd' : Odd n₂
  · exact example649_odd_increasing hodd hodd' h
  · rw [Nat.not_odd_iff_even] at hodd'
    exact example649_even_odd hodd' hodd

lemma example649_upperseq_equivalent_def (n:ℕ) : Example_6_4_9.upperseq n = if Even n then (n+1:ℝ)⁻¹ else (n+2:ℝ)⁻¹ := by
  split_ifs with h
  · apply le_antisymm
    · apply csSup_le
      · use (Example_6_4_9:Sequence).seq n
        use n; simp_all
      · intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        simp at hNam
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        have : (Example_6_4_9:Sequence).seq n = (n+1:ℝ)⁻¹ := by simp_all
        norm_cast at this
        rw [← this]
        exact example649_even_max h hNam
    · apply le_csSup
      · use (Example_6_4_9:Sequence).seq n
        intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        simp at hNam
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        have : (Example_6_4_9:Sequence).seq n = (n+1:ℝ)⁻¹ := by simp_all
        norm_cast at this
        exact example649_even_max h hNam
      · use n; simp_all
  · have heven : Even (n+1) := by grind
    have : (Example_6_4_9:Sequence).seq (n+1) = (n+2:ℝ)⁻¹ := by
      unfold Example_6_4_9
      simp_all
      rw [if_pos (by grind)]
      grind
    apply le_antisymm
    · apply csSup_le
      · use (Example_6_4_9:Sequence).seq n
        use n; simp_all
      · intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        simp at hNam
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast at this ⊢
        rw [← this]
        by_cases heq : N = n
        · observe hodd : Odd n
          rw [heq]
          exact example649_even_odd heven hodd
        · push_neg at heq
          have : N ≥ n+1 := by grind
          exact example649_even_max heven this
    · apply le_csSup
      · use (Example_6_4_9:Sequence).seq (n+1)
        intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        simp at hNam
        have : N ≥ 0 := by grind
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        by_cases heq : N = n
        · observe hodd : Odd n
          rw [heq]
          exact example649_even_odd heven hodd
        · push_neg at heq
          have : N ≥ n+1 := by grind
          exact example649_even_max heven this
      · use n+1
        grind

example : Example_6_4_9.limsup = 0 := by
  rw [Sequence.limsup]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · use Example_6_4_9.seq 0
    use 0
    constructor
    · grind
    · simp_all
      have := example649_upperseq_equivalent_def 0
      simp at this
      symm at this
      exact this
  · intro a ha
    obtain ⟨N, hNam, hN⟩ := ha
    simp at hNam
    lift N to ℕ using (by omega)
    have := example649_upperseq_equivalent_def N
    rw [hN, this]
    rcases Nat.even_or_odd N with (heven | hodd)
    · simp_all; grind
    · rw [if_neg (by grind)]
      positivity
  · intro w hw
    obtain ⟨c', heq⟩ | htop | hbot := EReal.def w
    · rw [← heq] at hw
      have hw' := EReal.coe_lt_coe_iff.mp hw
      obtain ⟨N, hN⟩ := exists_nat_gt (1/c')
      have : 1/c' < ((N+1):ℕ) := by grind
      field_simp at this
      use Example_6_4_9.upperseq ((N+1):ℕ)
      constructor
      · use (N+1)
        constructor
        · grind
        · simp
      · rw [← heq, example649_upperseq_equivalent_def (N+1)]
        split_ifs
        · norm_cast
          field_simp
          grind
        · norm_cast
          field_simp
          grind
    · rw [htop]
      use Example_6_4_9.seq Example_6_4_9.m
      constructor
      · use Example_6_4_9.m
        constructor <;> simp_all
        have := example649_upperseq_equivalent_def 0
        simp at this
        symm at this
        exact this
      · exact coe_lt_top _
    · rw [hbot] at hw
      exact absurd hw not_lt_bot

lemma example649_lowerseq_equivalent_def (n:ℕ) : Example_6_4_9.lowerseq n = if Even n then -(n+2:ℝ)⁻¹ else -(n+1:ℝ)⁻¹ := by
  split_ifs with hif
  · have hodd : Odd (n+1) := by grind
    have : -(n+2:ℝ)⁻¹ = Example_6_4_9.seq (n+1) := by
      simp_all
      rw [if_pos (by grind), if_neg (by grind)]
      grind
    rw [this]; clear this
    apply le_antisymm
    · apply csInf_le
      · use Example_6_4_9.seq (n+1)
        intro a ha
        obtain ⟨N, hNam, hN⟩ := ha
        simp at hNam
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        by_cases h : N = n
        · rw [h]
          exact example649_even_odd hif hodd
        · have hgt : N ≥ n + 1 := by grind
          exact example649_odd_min hodd hgt
      · use (n+1)
        constructor <;> simp_all
    · apply le_csInf
      · use Example_6_4_9.seq n
        use n
        constructor <;> simp_all
      · intro a ha
        obtain ⟨N, hNam, hN⟩ := ha
        simp at hNam
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        by_cases h : N = n
        · rw [h]
          exact example649_even_odd hif hodd
        · have hgt : N ≥ n + 1 := by grind
          exact example649_odd_min hodd hgt
  · have hodd : Odd n := by grind
    have : -(n+1:ℝ)⁻¹ = Example_6_4_9.seq n := by simp_all
    rw [this]; clear this
    apply le_antisymm
    · apply csInf_le
      · use Example_6_4_9.seq n
        intro a ha
        obtain ⟨N, hNam, hN⟩ := ha
        simp at hNam
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        exact example649_odd_min hodd hNam
      · use n
        constructor <;> simp_all
    · apply le_csInf
      · use Example_6_4_9.seq n
        use n
        constructor <;> simp_all
      · intro b hb
        obtain ⟨N, hNam, hN⟩ := hb
        simp at hNam
        lift N to ℕ using (by omega)
        simp at hNam
        rw [Sequence.from_eval _ (by grind)] at hN
        rw [hN]
        norm_cast
        exact example649_odd_min hodd hNam


example : Example_6_4_9.liminf = 0 := by
  rw [Sequence.liminf]
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use -(2:ℝ)⁻¹
    use 0
    constructor
    · simp_all
    · have := example649_lowerseq_equivalent_def 0; simp at this
      symm at this
      exact this
  · intro a ha
    obtain ⟨N, hNam, hN⟩ := ha
    simp at hNam
    lift N to ℕ using (by omega)
    rw [example649_lowerseq_equivalent_def N] at hN
    rw [hN]
    rcases Nat.even_or_odd N with (heven | hodd)
    · simp_all; grind
    · have : ¬ Even N := by grind
      rw [if_neg this]
      simp_all; grind
  · intro w hw
    obtain ⟨c', heq⟩ | htop | hbot := EReal.def w
    · rw [← heq] at hw
      have hw' := EReal.coe_lt_coe_iff.mp hw
      observe hcpos : -c' > 0
      obtain ⟨N, hN⟩ := exists_nat_gt (1/(-c'))
      rw [div_lt_iff₀ hcpos] at hN
      use Example_6_4_9.lowerseq ((N+1):ℕ)
      constructor
      · use (N+1)
        constructor
        · grind
        · simp
      · rw [example649_lowerseq_equivalent_def, ← heq]
        split_ifs
        · norm_cast
          field_simp
          grind
        · norm_cast
          field_simp
          grind
    · rw [htop] at hw
      exact absurd hw not_top_lt
    · rw [hbot]
      use Example_6_4_9.lowerseq (Example_6_4_9.m).toNat
      constructor
      · simp_all
        use 0
      · simp_all
        have := example649_lowerseq_equivalent_def 0
        rw [if_pos (by grind)] at this
        norm_cast at this
        rw [this]
        exact bot_lt_coe _

noncomputable abbrev Example_6_4_10 : Sequence := (fun (n:ℕ) ↦ (n+1:ℝ))

lemma example6410_upperseq_equivalent_def (n:ℕ) : Example_6_4_10.upperseq n = ⊤ := by
  rw [Sequence.upperseq, Sequence.sup]
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def b
  · by_cases hb0 : b' < 0
    · use Example_6_4_10.seq n
      constructor
      · use n
        constructor <;> simp
      · simp_all
        norm_cast
        grind
    · push_neg at hb0
      have hflrnonneg : ⌊b'⌋ ≥ 0 := by positivity
      use (⌊b'⌋.toNat) + n + 1
      constructor
      · use (⌊b'⌋.toNat) + n
        constructor
        · grind
        · simp_all
          rw [if_pos (by grind)]
          simp_all
          norm_cast
          grind
      · have hint := Int.toNat_of_nonneg hflrnonneg
        have hflr := Int.lt_floor_add_one b'
        rify at hint
        norm_cast
        push_cast
        rw [hint]
        grind
  · exfalso
    exact lt_irrefl ⊤ hb
  · use Example_6_4_10.seq n
    constructor
    · use n
      constructor <;> simp
    · exact bot_lt_coe _

<<<<<<< HEAD
example : Example_6_4_10.limsup = ⊤ := by sorry

example (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by sorry

example : Example_6_4_10.liminf = ⊤ := by sorry
=======
example : Example_6_4_10.limsup = ⊤ := by
  unfold Sequence.limsup
  apply sInf_eq_top.mpr
  intro x hx
  obtain ⟨N, hNam, hN⟩ := hx
  simp at hNam
  lift N to ℕ using (by omega)
  rwa [example6410_upperseq_equivalent_def N] at hN

lemma example6410_lowerseq_equivalent_def (n:ℕ) : Example_6_4_10.lowerseq n = n+1 := by
  rw [Sequence.lowerseq, Sequence.inf]
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · use Example_6_4_10.seq n
    grind
  · intro a ha
    obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def a
    · obtain ⟨N, hNam, hN⟩ := ha
      simp at hNam hN
      rw [if_pos hNam, if_pos (by grind)] at hN
      norm_cast
      rw [hN]
      have : N ≥ 0 := by grind
      have := Int.toNat_of_nonneg this
      rify at this
      rw [this]
      rify at hNam
      grind
    · simp at ha
    · simp at ha
  · intro w hw
    obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def w
    · use n + 1
      constructor
      · use n
        constructor
        · grind
        · simp_all
      · exact hw
    · use n+1
      constructor
      · use n
        constructor <;> simp_all
      · exact coe_lt_top _
    · exact absurd hw not_lt_bot

example : Example_6_4_10.liminf = ⊤ := by
  rw [Sequence.liminf]
  apply sSup_eq_top.mpr
  intro b hb
  obtain ⟨b', rfl⟩ | rfl | rfl := EReal.def b
  · by_cases hb0 : b' < 0
    · use 1
      constructor
      · use 0
        constructor
        · simp
        · have := example6410_lowerseq_equivalent_def 0; simp at this
          symm at this
          exact this
      · norm_cast
        linarith
    · push_neg at hb0
      have hflrnonneg : ⌊b'⌋ ≥ 0 := by positivity
      have hint := Int.toNat_of_nonneg hflrnonneg
      use ((⌊b'⌋.toNat + 1):ℕ)
      constructor
      · use ((⌊b'⌋.toNat):ℕ)
        constructor
        · grind
        · have := example6410_lowerseq_equivalent_def (⌊b'⌋.toNat)
          rw [this]
          norm_cast
      · norm_cast
        push_cast
        rify at hint
        rw [hint]
        exact Int.lt_floor_add_one b'
  · exfalso
    exact lt_irrefl ⊤ hb
  · use 1
    constructor
    · use 0
      constructor
      · simp
      · have := example6410_lowerseq_equivalent_def 0; simp at this
        symm at this
        exact this
    · exact bot_lt_coe _

>>>>>>> 440d3d1 (finally 6_4 is done)

/-- Proposition 6.4.12(a) -/
theorem Sequence.gt_limsup_bounds {a:Sequence} {x:EReal} (h: x > a.limsup) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n < x := by
  -- This proof is written to follow the structure of the original text.
  simp only [limsup, sInf_lt_iff] at h
  obtain ⟨y, hy, ha⟩ := h
  obtain ⟨N, hN, hNy⟩ := hy
  rw [hNy] at ha; use N
  simp [hN, upperseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  convert lt_of_le_of_lt ((a.from N).le_sup hn') ha using 1
  grind

/-- Proposition 6.4.12(a) -/
theorem Sequence.lt_liminf_bounds {a:Sequence} {y:EReal} (h: y < a.liminf) :
    ∃ N ≥ a.m, ∀ n ≥ N, a n > y := by
  simp only [Sequence.liminf, lt_sSup_iff] at h
  obtain ⟨z, hz, ha⟩ := h
  obtain ⟨N, hN, hNz⟩ := hz
  rw [hNz] at ha; use N
  simp [hN, Sequence.lowerseq] at ha ⊢; intro n _
  have hn' : n ≥ (a.from N).m := by grind
  have hinf := (a.from N).ge_inf hn'
  convert lt_of_lt_of_le ha hinf using 1
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.lt_limsup_bounds {a:Sequence} {x:EReal} (h: x < a.limsup) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n > x := by
  -- This proof is written to follow the structure of the original text.
  have hx : x < a.upperseq N := by
    unfold upperseq
    apply lt_of_lt_of_le h (sInf_le _)
    simp
    use N
  choose n hn hxn _ using exists_between_lt_sup hx
  grind

/-- Proposition 6.4.12(b) -/
theorem Sequence.gt_liminf_bounds {a:Sequence} {x:EReal} (h: x > a.liminf) {N:ℤ} (hN: N ≥ a.m) :
    ∃ n ≥ N, a n < x := by
  have hx : x > a.lowerseq N := by
    unfold lowerseq
    apply lt_of_le_of_lt (le_sSup _) h
    simp
    use N
  choose n hn hxn _ using exists_between_gt_inf hx
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.inf_le_liminf (a:Sequence) : a.inf ≤ a.liminf := by
  by_contra! h'
  have hbd := Sequence.gt_liminf_bounds (N:=a.m) h' (by grind)
  obtain ⟨N, hNam, hN⟩ := hbd
  have hgeinf := Sequence.ge_inf hNam
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.limsup_le_sup (a:Sequence) : a.limsup ≤ a.sup := by
  by_contra! h'
  have hbd := Sequence.lt_limsup_bounds (N:=a.m) h' (by grind)
  obtain ⟨N, hNam, hN⟩ := hbd
  have hlesup := Sequence.le_sup hNam
  grind

/-- Proposition 6.4.12(c) / Exercise 6.4.3 -/
theorem Sequence.liminf_le_limsup (a:Sequence) : a.liminf ≤ a.limsup := by
  apply sSup_le
  intro b hb; obtain ⟨N₁, hNam₁, hN₁⟩ := hb
  apply le_sInf
  intro c hc; obtain ⟨N₂, hNam₂, hN₂⟩ := hc
  subst hN₁ hN₂
  rw [Sequence.lowerseq, Sequence.upperseq]
  have h₁ : max N₁ N₂ ≥ (a.from N₁).m := by grind
  have h₂ : max N₁ N₂ ≥ (a.from N₂).m := by grind
  have hgeinf := (a.from N₁).ge_inf h₁; rw [a.from_eval (by grind)] at hgeinf
  have hlesup := (a.from N₂).le_sup h₂; rw [a.from_eval (by grind)] at hlesup
  grind

/-- Proposition 6.4.12(d) / Exercise 6.4.3 -/
lemma Sequence.inf_ne_top {a:Sequence} : a.inf ≠ ⊤ := by
  by_contra! h'
  have hallbot := sInf_eq_top.mp h'
  specialize hallbot (a.seq a.m) (by grind)
  exact absurd hallbot (coe_ne_top _)

lemma Sequence.sup_ne_bot {a:Sequence} : a.sup ≠ ⊥ := by
  by_contra! h'
  have halltop := sSup_eq_bot.mp h'
  specialize halltop (a.seq a.m) (by grind)
  exact absurd halltop (coe_ne_bot _)


theorem Sequence.limit_point_between_liminf_limsup {a:Sequence} {c:ℝ} (h: a.LimitPoint c) :
  a.liminf ≤ c ∧ c ≤ a.limsup := by
  rw [Sequence.limit_point_def] at h
  constructor
  · apply sSup_le
    rintro _ ⟨N, hNam, rfl⟩
    obtain ⟨x', hreal⟩ | htop | hbot := EReal.def (a.lowerseq N)
    · rw [← hreal]
      norm_cast
      by_contra! hcont
      obtain ⟨n, hngeN, hseqhalf⟩ := h ((x'-c)/2) (by grind) N hNam
      rw [Sequence.lowerseq] at hreal
      have hseqeq : a.seq n = (a.from N).seq n := by grind
      rw [hseqeq] at hseqhalf
      have hgeinf := Sequence.ge_inf (n:=n) (a:=(a.from N)) (by grind)
      rw [← hreal] at hgeinf; norm_cast at hgeinf
      rw [a.from_eval (by grind)] at *
      grind
    · exact absurd htop Sequence.inf_ne_top
    · rw [hbot]; exact bot_le
  · apply le_sInf
    rintro _ ⟨N, hNam, rfl⟩
    obtain ⟨x', hreal⟩ | htop | hbot := EReal.def (a.upperseq N)
    · rw [← hreal]
      norm_cast
      by_contra! hcont
      obtain ⟨n, hngeN, hseqhalf⟩ := h ((c-x')/2) (by grind) N hNam
      rw [Sequence.upperseq] at hreal
      have hseqeq : a.seq n = (a.from N).seq n := by grind
      rw [hseqeq] at hseqhalf
      have hlesup := Sequence.le_sup (n:=n) (a:=(a.from N)) (by grind)
      rw [← hreal] at hlesup; norm_cast at hlesup
      rw [a.from_eval (by grind)] at *
      grind
    · rw [htop]; exact le_top
    · exact absurd hbot Sequence.sup_ne_bot

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_limsup {a:Sequence} {L_plus:ℝ} (h: a.limsup = L_plus) :
    a.LimitPoint L_plus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hNam
  have hub : L_plus < L_plus + ε := by linarith
  have hlb : L_plus - ε < L_plus := by linarith
  have hub' := EReal.coe_lt_coe hub
  have hlb' := EReal.coe_lt_coe hlb
  rw [← h] at hub' hlb'
  obtain ⟨N₁, hNam₁, hN₁⟩ := Sequence.gt_limsup_bounds hub'
  obtain ⟨N₂, hNam₂, hN₂⟩ := Sequence.lt_limsup_bounds (N:=max N N₁) hlb' (by grind)
  specialize hN₁ N₂ (by grind)
  use N₂
  norm_cast at hN₁ hN₂
  constructor <;> grind

/-- Proposition 6.4.12(e) / Exercise 6.4.3 -/
theorem Sequence.limit_point_of_liminf {a:Sequence} {L_minus:ℝ} (h: a.liminf = L_minus) :
    a.LimitPoint L_minus := by
  rw [Sequence.limit_point_def]
  intro ε hε N hNam
  have hub : L_minus < L_minus + ε := by linarith
  have hlb : L_minus - ε < L_minus := by linarith
  have hub' := EReal.coe_lt_coe hub
  have hlb' := EReal.coe_lt_coe hlb
  rw [← h] at hub' hlb'
  obtain ⟨N₁, hNam₁, hN₁⟩ := Sequence.lt_liminf_bounds hlb'
  obtain ⟨N₂, hNam₂, hN₂⟩ := Sequence.gt_liminf_bounds (N:=max N N₁) hub' (by grind)
  specialize hN₁ N₂ (by grind)
  use N₂
  norm_cast at hN₁ hN₂
  constructor <;> grind

/-- Proposition 6.4.12(f) / Exercise 6.4.3 -/
lemma Sequence.limsup_of_bddBelow_ne_bot {a:Sequence} (h : a.BddBelow) : a.limsup ≠ ⊥:= by
  by_contra! h'
  have hbot' := sInf_eq_bot.mp h'
  obtain ⟨B, hB⟩ := h
  specialize hbot' B (by exact bot_lt_coe _)
  obtain ⟨x, hupper, hlt⟩ := hbot'
  obtain ⟨N, hNam, haupper⟩ := hupper
  rw [Sequence.upperseq] at haupper
  rw [haupper] at hlt
  have : (a.from N).seq N = a.seq N := by rw [a.from_eval (by grind)]
  specialize hB N hNam
  rw [← this] at hB
  have hlesup := Sequence.le_sup (a:=(a.from N)) (n:=N) (by grind)
  have := lt_of_le_of_lt hlesup hlt
  norm_cast at this
  linarith

lemma Sequence.liminf_of_bddAbove_ne_top {a:Sequence} (h : a.BddAbove) : a.liminf ≠ ⊤ := by
  by_contra! h'
  have htop' := sSup_eq_top.mp h'
  obtain ⟨A, hA⟩ := h
  specialize htop' A (by exact coe_lt_top _)
  obtain ⟨x, hlower, hgt⟩ := htop'
  obtain ⟨N, hNam, halower⟩ := hlower
  rw [Sequence.lowerseq] at halower
  rw [halower] at hgt
  have : (a.from N).seq N = a.seq N := by rw [a.from_eval (by grind)]
  specialize hA N hNam
  rw [← this] at hA
  have hgeinf := Sequence.ge_inf (a:=(a.from N)) (n:=N) (by grind)
  have := lt_of_lt_of_le hgt hgeinf
  norm_cast at this
  linarith

lemma Sequence.limsup_of_bddAbove_ne_top {a:Sequence} (h: a.BddAbove) : a.limsup ≠ ⊤ := by
  by_contra! h'
  have htop := sInf_eq_top.mp h'
  specialize htop (a.upperseq a.m) (by grind)
  have htop' := sSup_eq_top.mp htop
  obtain ⟨A, hA⟩ := h
  specialize htop' A (by exact coe_lt_top _)
  obtain ⟨x, ⟨N, hNam, hN⟩, hlt⟩ := htop'
  simp_all
  specialize hA N (by grind)
  linarith

lemma Sequence.liminf_of_bddBelow_ne_bot {a:Sequence} (h: a.BddBelow) : a.liminf ≠ ⊥ := by
  by_contra! h'
  have hbot := sSup_eq_bot.mp h'
  specialize hbot (a.lowerseq a.m) (by grind)
  have hbot' := sInf_eq_bot.mp hbot
  obtain ⟨B, hB⟩ := h
  specialize hbot' B (by exact bot_lt_coe _)
  obtain ⟨x, ⟨N, hNam, hN⟩, hgt⟩ := hbot'
  simp_all
  specialize hB N (by grind)
  linarith


theorem Sequence.tendsTo_iff_eq_limsup_liminf {a:Sequence} (c:ℝ) :
  a.TendsTo c ↔ a.liminf = c ∧ a.limsup = c := by
  constructor
  · intro htends
    observe hconv : a.Convergent
    have hclimpt := Sequence.limit_point_of_limit htends
    -- Sequence.limit_point_of_limit
    have ⟨habv, hblw⟩ := (Sequence.bounded_iff a).mp (Sequence.bounded_of_convergent hconv)
    rw [Sequence.tendsTo_iff] at htends
    constructor
    · obtain ⟨x, hreal⟩ | htop | hbot := EReal.def a.liminf
      · apply le_antisymm
        · exact (Sequence.limit_point_between_liminf_limsup hclimpt).1
        · by_contra! h'
          rw [← hreal] at h'
          have hltR := EReal.coe_lt_coe_iff.mp h'
          have hltR' : x < x + ((c - x)/2) := by linarith
          have hltER := EReal.coe_lt_coe hltR'
          rw [hreal] at hltER
          obtain ⟨N₁, hN₁⟩ := htends ((c - x)/2) (by grind)
          obtain ⟨N₂, hNam₂, hN₂⟩ := Sequence.gt_liminf_bounds (N:=max N₁ a.m) hltER (by grind)
          norm_cast at hN₂
          specialize hN₁ N₂ (by grind)
          grind
      · exact absurd htop (Sequence.liminf_of_bddAbove_ne_top habv)
      · exact absurd hbot (Sequence.liminf_of_bddBelow_ne_bot hblw)
    · obtain ⟨x, hreal⟩ | htop | hbot := EReal.def a.limsup
      · apply le_antisymm
        · by_contra! h'
          rw [← hreal] at h'
          have hltR := EReal.coe_lt_coe_iff.mp h'
          have hltR' : ((c - x)/2) + x < x := by linarith
          have hltER := EReal.coe_lt_coe hltR'
          rw [hreal] at hltER
          obtain ⟨N₁, hN₁⟩ := htends ((x - c)/2) (by grind)
          obtain ⟨N₂, hNam₂, hN₂⟩ := Sequence.lt_limsup_bounds (N:=max N₁ a.m) hltER (by grind)
          norm_cast at hN₂
          specialize hN₁ N₂ (by grind)
          grind
        · exact (Sequence.limit_point_between_liminf_limsup hclimpt).2
      · exact absurd htop (Sequence.limsup_of_bddAbove_ne_top habv)
      · exact absurd hbot (Sequence.limsup_of_bddBelow_ne_bot hblw)
  · rintro ⟨hlinf, hlsup⟩
    rw [Sequence.tendsTo_iff]
    intro ε hε
    observe hlt : c - ε < c; have hlt' := EReal.coe_lt_coe hlt; rw [← hlinf] at hlt'
    obtain ⟨N₁, hNam₁, hN₁⟩ := Sequence.lt_liminf_bounds hlt'
    observe hgt : c < c + ε; have hgt' := EReal.coe_lt_coe hgt; rw [← hlsup] at hgt'
    obtain ⟨N₂, hNam₂, hN₂⟩ := Sequence.gt_limsup_bounds hgt'
    use max N₁ N₂
    intro n hn
    specialize hN₁ n (by grind)
    specialize hN₂ n (by grind)
    norm_cast at hN₁ hN₂
    grind

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by
    by_contra! h'
    obtain ⟨N, hNam, hsuplt, _⟩ := Sequence.exists_between_lt_sup h'
    have hlesup : b.seq N ≤ b.sup := by exact Sequence.le_sup (by grind)
    have hcontra := lt_of_le_of_lt hlesup hsuplt
    norm_cast at hcontra
    specialize hab N (by grind)
    linarith

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by
    by_contra! h'
    obtain ⟨N, hNam, hinfgt , _⟩ := Sequence.exists_between_gt_inf h'
    have hgeinf : a.seq N ≥ a.inf := by exact Sequence.ge_inf (by grind)
    have hcontra := lt_of_lt_of_le hinfgt hgeinf
    norm_cast at hcontra
    specialize hab N (by grind)
    linarith

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by
    apply le_sInf
    rintro x ⟨N, hNam, hN⟩
    rw [hN]
    have halimsuple : a.limsup ≤ a.upperseq N := by
      apply sInf_le
      use N; grind
    have haupperseqle : a.upperseq N ≤ b.upperseq N := by
      apply sup_mono
      grind
      intro n hn
      rw [a.from_eval (by grind), b.from_eval (by grind)]
      specialize hab n (by grind)
      exact hab
    exact EReal.trans halimsuple haupperseqle


/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by
    apply sSup_le
    rintro x ⟨N, hnAm, hN⟩
    rw [hN]
    have halowerseqle : a.lowerseq N ≤ b.lowerseq N := by
      apply inf_mono
      grind
      intro n hn
      rw [a.from_eval (by grind), b.from_eval (by grind)]
      specialize hab n (by grind)
      exact hab
    have hblowerseqle : b.lowerseq N ≤ b.liminf := by
      apply le_sSup
      use N; grind
    exact EReal.trans halowerseqle hblowerseqle

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by
    obtain ⟨hambm, hcmam⟩ := hm
    have hbmcm : b.m = c.m := by grind
    obtain ⟨haliminf, halimsup⟩ := (Sequence.tendsTo_iff_eq_limsup_liminf L).mp ha
    obtain ⟨hcliminf, hclimsup⟩ := (Sequence.tendsTo_iff_eq_limsup_liminf L).mp hb
    have hanbn : ∀ n ≥ a.m, a n ≤ b n := by grind
    have hbncn : ∀ n ≥ b.m, b n ≤ c n := by grind
    have hainfbinf := Sequence.liminf_mono (by grind) hanbn
    have hbsupcsup := Sequence.limsup_mono (by grind) hbncn
    have hbinfcinf := Sequence.liminf_mono (by grind) hbncn
    have hasupbsup := Sequence.limsup_mono (by grind) hanbn
    rw [haliminf] at hainfbinf
    rw [halimsup] at hasupbsup
    rw [hclimsup] at hbsupcsup
    rw [hcliminf] at hbinfcinf
    have hblimsup : b.limsup = L := by grind
    have hbliminf : b.liminf = L := by grind
    exact (Sequence.tendsTo_iff_eq_limsup_liminf L).mpr ⟨hbliminf, hblimsup⟩

lemma Sequence.lim_harmonic_mul (c:ℝ) :
  ((fun (n:ℕ) ↦ c / (n+1:ℝ)):Sequence).TendsTo 0 := by
  have hlimharm := Sequence.lim_eq.mpr Sequence.lim_harmonic
  have hclimharm := Sequence.tendsTo_smul c hlimharm
  rw [mul_zero] at hclimharm
  rw [Sequence.tendsTo_iff] at hclimharm ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hclimharm ε hε
  use max 0 N
  intro n hn
  specialize hN n (by grind)
  simp at hN ⊢
  rw [if_pos (by grind)] at hN ⊢
  grind

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  exact Sequence.lim_harmonic_mul 2

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  exact Sequence.lim_harmonic_mul (-2)

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  apply Sequence.lim_of_between
    (a  := (fun (n:ℕ) ↦ -2/(n+1:ℝ)))
    (c  := (fun (n:ℕ) ↦ 2/(n+1:ℝ)))
    (hm := by grind)
    (ha := Sequence.lim_harmonic_mul (-2))
    (hb := Sequence.lim_harmonic_mul 2)
  intro n hn
  simp at hn
  lift n to ℕ using (by omega)
  constructor
  · simp_all
    field_simp
    rcases Nat.even_or_odd n with (heven | hodd)
    · simp_all; grind
    · simp_all; grind
  · simp_all
    field_simp
    rcases Nat.even_or_odd n with (heven | hodd)
    · simp_all; grind
    · simp_all; grind

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  have hconst0 : ((fun (n:ℕ) ↦ (0:ℝ)):Sequence).TendsTo 0 := by
    rw [Sequence.tendsTo_iff]
    intro ε hε
    use  ((fun (n:ℕ) ↦ (0:ℝ)):Sequence).m
    grind
  apply Sequence.lim_of_between
    (a  := ((fun (n:ℕ) ↦ (0:ℝ))))
    (c  := (fun (n:ℕ) ↦ 2/(n+1:ℝ)))
    (hm := by grind)
    (ha := hconst0)
    (hb := Sequence.lim_harmonic_mul 2)
  intro n hn
  simp at hn
  lift n to ℕ using (by omega)
  simp
  field_simp
  induction' n with k ih
  · grind
  · rw [pow_add, pow_one]
    norm_cast at *
    norm_num
    calc ((k+1):ℕ) + 1 ≤ 2 ^ k * 2 + 1 := by gcongr;
         _ ≤ 2 ^ k * 2 + 2 ^ k * 2     := by gcongr; grind
         _ = (2 ^ k * 2) * 2           := by grind

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  rw [Sequence.tendsTo_iff, Sequence.tendsTo_iff]
  peel with ε hε
  simp_all

/--
  This helper lemma, implicit in the textbook proofs of Theorem 6.4.18 and Theorem 6.6.8, is made
  explicit here.
-/
theorem Sequence.finite_limsup_liminf_of_bounded {a:Sequence} (hbound: a.IsBounded) :
    (∃ L_plus:ℝ, a.limsup = L_plus) ∧ (∃ L_minus:ℝ, a.liminf = L_minus) := by
  choose M hMpos hbound using hbound
  have hlimsup_bound : a.limsup ≤ M := by
    apply a.limsup_le_sup.trans (sup_le_upper _)
    intro n hN; simp
    exact (le_abs_self _).trans (hbound n)
  have hliminf_bound : -M ≤ a.liminf := by
    apply (inf_ge_lower _).trans a.inf_le_liminf
    intro n hN; simp [←coe_neg]; rw [neg_le]
    exact (neg_le_abs _).trans (hbound n)
  split_ands
  . use a.limsup.toReal
    symm; apply coe_toReal
    . contrapose! hlimsup_bound; simp [hlimsup_bound]
    replace hliminf_bound := hliminf_bound.trans a.liminf_le_limsup
    contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]
  use a.liminf.toReal; symm; apply coe_toReal
  . apply a.liminf_le_limsup.trans at hlimsup_bound
    contrapose! hlimsup_bound; simp [hlimsup_bound]
  contrapose! hliminf_bound; simp [hliminf_bound, ←coe_neg]

/-- Theorem 6.4.18 (Completeness of the reals) -/
theorem Sequence.Cauchy_iff_convergent (a:Sequence) :
  a.IsCauchy ↔ a.Convergent := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, IsCauchy.convergent ⟩; intro h
  have ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ L_minus, hL_minus ⟩ ⟩ :=
    finite_limsup_liminf_of_bounded (bounded_of_cauchy h)
  use L_minus; simp [tendsTo_iff_eq_limsup_liminf, hL_minus, hL_plus]
  have hlow : 0 ≤ L_plus - L_minus := by
    have := a.liminf_le_limsup; simp [hL_minus, hL_plus] at this; grind
  have hup (ε:ℝ) (hε: ε>0) : L_plus - L_minus ≤ 2*ε := by
    specialize h ε hε; choose N hN hsteady using h
    have hN0 : N ≥ (a.from N).m := by grind
    have hN1 : (a.from N).seq N = a.seq N := by grind
    have h1 : (a N - ε:ℝ) ≤ (a.from N).inf := by
      apply inf_ge_lower; grind [Real.dist_eq, abs_le',EReal.coe_le_coe_iff]
    have h2 : (a.from N).inf ≤ L_minus := by
      simp_rw [←hL_minus, liminf, lowerseq]; apply le_sSup; simp; use N
    have h3 : (a.from N).sup ≤ (a N + ε:ℝ) := by
      apply sup_le_upper; grind [EReal.coe_le_coe_iff, Real.dist_eq, abs_le']
    have h4 : L_plus ≤ (a.from N).sup := by
      simp_rw [←hL_plus, limsup, upperseq]; apply sInf_le; simp; use N
    replace h1 := h1.trans h2
    replace h4 := h4.trans h3
    grind [EReal.coe_le_coe_iff]
  obtain hlow | hlow := le_iff_lt_or_eq.mp hlow
  . specialize hup ((L_plus - L_minus)/3) ?_ <;> linarith
  grind

/-- Exercise 6.4.6 -/
lemma Sequence.sup_harmonic_mul {c:ℝ} (hc : c < 0) :
  ((fun (n:ℕ) ↦ c / (n+1:ℝ)):Sequence).sup = 0 := by
  apply  csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · use c; use 0; simp_all
  · rintro a ⟨N, hNam, hN⟩
    simp at hNam; lift N to ℕ using (by omega)
    simp at hN; rw [hN]
    norm_cast; field_simp; grind
  · intro w hw
    obtain ⟨w', hreal⟩ | htop | hbot := EReal.def w
    · rw [← hreal] at hw
      norm_cast at hw
      observe : -w' > 0
      obtain ⟨N, hN⟩ := exists_nat_gt (c/w')
      use (fun (n:ℕ) ↦ c / (n+1:ℝ)) N
      constructor
      · use N; simp
      · rw [← hreal]
        norm_cast
        simp
        rw [div_lt_iff_of_neg (by grind)] at hN
        field_simp
        grind
    · rw [htop] at hw
      exact absurd hw not_top_lt
    · use c
      constructor
      · use 0; simp_all
      · rw [hbot]
        exact bot_lt_coe _
#check exists_nat_gt

theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  use (fun (n:ℕ) ↦ -2 / (n+1:ℝ))
  use (fun (n:ℕ) ↦ -1 / (n+1:ℝ))
  constructor
  · intro n
    gcongr; grind
  · have h1 := Sequence.sup_harmonic_mul (c:=-1) (by grind)
    have h2 := Sequence.sup_harmonic_mul (c:=-2) (by grind)
    intro nope
    rw [h1, h2] at nope
    grind


/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro hh
  let α : ℕ → ℝ := fun n => (-1)^n
  specialize hh (α:Sequence) 1
  have habstends : (α:Sequence).abs.TendsTo 1 := by
    rw [Sequence.tendsTo_iff]
    intro ε hε
    use (α:Sequence).m
    intro n hn
    unfold α
    simp_all
    grind
  have hdoesnttend : ¬ ((α:Sequence).TendsTo 1) := by
    rw [Sequence.tendsTo_iff]
    push_neg
    use 1
    constructor
    · simp
    · intro n
      by_cases hn0 : n < 0
      · use 1
        constructor
        · grind
        · unfold α; grind
      · push_neg at hn0
        lift n to ℕ using (by omega)
        use ((2:ℕ) * (n:ℕ)) + 1
        constructor
        · grind
        · unfold α
          dsimp
          rw [if_pos (by grind)]
          rw [Int.toNat_add (by grind) (by grind)]
          rw [pow_add]
          rw [← zpow_natCast ((-1) : ℝ) (2 * (n:ℤ)).toNat]
          rw [Int.toNat_of_nonneg (by positivity)]
          simp_all
          rw [mul_comm, zpow_mul]
          simp
          rcases Nat.even_or_odd n with (heven | hodd)
          · simp_all
            grind
          · simp_all
            norm_num
  exact hdoesnttend (hh.mpr habstends)

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by
  unfold Sequence.ExtendedLimitPoint
  obtain ⟨c, hc⟩ | htop | hbot := EReal.def a.limsup
  · split_ifs with h1 h2 <;> try grind
    · intro hbddabove
      exact Sequence.limsup_of_bddAbove_ne_top hbddabove h1
    · intro hbddbelow
      exact Sequence.limsup_of_bddBelow_ne_bot hbddbelow h2
    · rw [← hc]
      simp
      exact Sequence.limit_point_of_limsup hc.symm
  · rw [htop]
    split_ifs <;> try grind
    intro hbddabove
    exact Sequence.limsup_of_bddAbove_ne_top hbddabove htop
  · rw [hbot]
    split_ifs with h1 <;> try grind
    · intro _
      exact bot_ne_top h1
    · intro hbddbelow
      exact Sequence.limsup_of_bddBelow_ne_bot hbddbelow hbot

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by
  unfold Sequence.ExtendedLimitPoint
  obtain ⟨c, hc⟩ | htop | hbot := EReal.def a.liminf
  · split_ifs with h1 h2 <;> try grind
    · intro hbddabove
      exact Sequence.liminf_of_bddAbove_ne_top hbddabove h1
    · intro hbddbelow
      exact Sequence.liminf_of_bddBelow_ne_bot hbddbelow h2
    · rw [← hc]
      simp
      exact Sequence.limit_point_of_liminf hc.symm
  · rw [htop]
    split_ifs <;> try grind
    intro hbddabove
    exact Sequence.liminf_of_bddAbove_ne_top hbddabove htop
  · rw [hbot]
    split_ifs with h1 <;> try grind
    · intro _
      exact bot_ne_top h1
    · intro hbddbelow
      exact Sequence.liminf_of_bddBelow_ne_bot hbddbelow hbot

lemma Sequence.sup_of_not_bddAbove {a:Sequence} (hunbound : ¬ a.BddAbove) : a.sup = ⊤ := by
  apply sSup_eq_top.mpr
  intro b hb
  unfold Sequence.BddAbove at hunbound; push_neg at hunbound
  obtain ⟨b', hb'⟩ | htop | hbot := EReal.def b
  · specialize hunbound b'
    unfold Sequence.BddAboveBy at hunbound
    push_neg at hunbound
    obtain ⟨N, hNam, hN⟩ := hunbound
    use a.seq N
    constructor
    · use N
    · rw [← hb']
      norm_cast
  · rw [htop] at hb
    exact absurd hb (lt_irrefl _)
  · rw [hbot]
    use a.seq a.m
    constructor
    · use a.m
    · exact bot_lt_coe _

lemma Sequence.not_bddAbove_from {a:Sequence} (N:ℤ) (hunbound : ¬ a.BddAbove) : ¬ (a.from N).BddAbove := by
  unfold Sequence.BddAbove Sequence.BddAboveBy at hunbound ⊢
  contrapose hunbound
  obtain ⟨A, hA⟩ := hunbound; simp at hA
  use Finset.fold max A a.seq (Finset.Icc a.m N)
  intro n hn
  by_cases hnn : n < N
  · rw [Finset.le_fold_max]
    right
    use n
    constructor <;> grind
  · push_neg at hnn
    rw [Finset.le_fold_max]
    left
    specialize hA n hn hnn
    rwa [if_pos (by grind)] at hA


lemma Sequence.inf_of_not_bddBelow {a:Sequence} (hunbound : ¬ a.BddBelow) : a.inf = ⊥ := by
  apply sInf_eq_bot.mpr
  intro b hb
  unfold Sequence.BddBelow at hunbound; push_neg at hunbound
  obtain ⟨b', hb'⟩ | htop | hbot := EReal.def b
  · specialize hunbound b'
    unfold Sequence.BddBelowBy at hunbound
    push_neg at hunbound
    obtain ⟨N, hNam, hN⟩ := hunbound
    use a.seq N
    constructor
    · use N
    · rw [← hb']
      norm_cast
  · rw [htop]
    use a.seq a.m
    constructor
    · use a.m
    · exact coe_lt_top _
  · rw [hbot] at hb
    exact absurd hb (lt_irrefl _)

lemma Sequence.not_bddBelow_from {a:Sequence} (N:ℤ) (hunbound : ¬ a.BddBelow) : ¬ (a.from N).BddBelow := by
  unfold Sequence.BddBelow Sequence.BddBelowBy at hunbound ⊢
  contrapose hunbound
  obtain ⟨B, hB⟩ := hunbound; simp at hB
  use Finset.fold min B a.seq (Finset.Icc a.m N)
  intro n hn
  by_cases hnn : n < N
  · rw [ge_iff_le, Finset.fold_min_le]
    right
    use n
    constructor <;> grind
  · push_neg at hnn
    rw [ge_iff_le, Finset.fold_min_le]
    left
    specialize hB n hn hnn
    rwa [if_pos (by grind)] at hB

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by
  unfold Sequence.ExtendedLimitPoint at h
  -- eliminate the impossible cases
  split_ifs at h with hltop hlbot
    <;> rcases EReal.def L with ⟨L', hL'⟩ | hltop' | hlbot'
    <;> try grind
  · rw [hltop] at hL'; exact absurd hL' (coe_ne_top _)
  · rcases EReal.def L with ⟨alimsup, halimsup⟩ | hatop | habot
    · rw [hltop'] at halimsup; exact absurd halimsup (coe_ne_top _)
    · rw [hltop]
      apply le_sInf_iff.mpr
      rintro b ⟨N, hNam, hN⟩
      unfold Sequence.upperseq at hN
      rw [hN]
      apply top_le_iff.mpr
      have hfromunbound := Sequence.not_bddAbove_from N h
      exact Sequence.sup_of_not_bddAbove hfromunbound
    · rw [habot] at hltop'; exact absurd hltop' bot_ne_top
  · rw [hlbot'] at hltop; exact absurd hltop bot_ne_top
  · rw [hlbot] at hL'; exact absurd hL' (coe_ne_bot _)
  · rw [hlbot]
    apply le_sInf_iff.mpr
    rintro b ⟨N, hNam, hN⟩
    apply bot_le
  · rw [← hL'] at h
    simp at h
    have := (Sequence.limit_point_between_liminf_limsup h).2
    rwa [hL'] at this


theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by
  unfold Sequence.ExtendedLimitPoint at h
  split_ifs at h with hltop hlbot
    <;> rcases EReal.def L with ⟨L', hL'⟩ | hltop' | hlbot'
    <;> try grind
  · rw [hltop] at hL'; exact absurd hL' (coe_ne_top _)
  · rw [hltop']
    apply sSup_le_iff.mpr
    rintro b ⟨N, hNam, hN⟩
    apply le_top
  · rw [hlbot'] at hltop; exact absurd hltop bot_ne_top
  · rw [hlbot] at hL'; exact absurd hL' (coe_ne_bot _)
  · rcases EReal.def L with ⟨alimsup, halimsup⟩ | hatop | habot
    · rw [hlbot] at halimsup; exact absurd halimsup (coe_ne_bot _)
    · rw [hlbot'] at hatop; exact absurd hatop bot_ne_top
    · rw [hlbot]
      apply sSup_le_iff.mpr
      rintro b ⟨N, hNam, hN⟩
      unfold Sequence.lowerseq at hN
      rw [hN]
      apply le_bot_iff.mpr
      have hfromunbound := Sequence.not_bddBelow_from N h
      exact Sequence.inf_of_not_bddBelow hfromunbound
  · rw [← hL'] at h
    simp at h
    have := (Sequence.limit_point_between_liminf_limsup h).1
    rwa [hL'] at this


/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by
  let α : ℕ → ℝ := fun n => match n % 3 with
    | 0 => 0
    | 1 => n
    | _ => -n
  use α
  intro L
  constructor
  · intro hextpt
    unfold Sequence.ExtendedLimitPoint at hextpt
    split_ifs at hextpt with htop hbot
    · right; right; exact htop
    · left; exact hbot
    · right; left
      obtain ⟨L', hL'⟩ | htop' | hbot' := EReal.def L
      · rw [← hL']
        norm_cast
        by_contra! h'
        have hpos : |L'| > 0 := by grind
        rw [← hL'] at hextpt
        simp at hextpt
        rw [Sequence.limit_point_def] at hextpt
        specialize hextpt (|L'| / 2) (by positivity)
        specialize hextpt (max (α:Sequence).m (2 *⌈|L'|⌉)) (by grind)
        obtain ⟨N, hNam, hN⟩ := hextpt
        simp at hNam
        lift N to ℕ using (by omega)
        unfold α at hN
        simp at hN
        obtain ⟨hNam0, hNceil⟩ := hNam
        have hceil : L' ≤ ⌈L'⌉ := by exact Int.le_ceil L'
        split at hN
        · grind
        · have hceil' : |L'| ≤ (⌈|L'|⌉ : ℝ) := Int.le_ceil |L'|
          have hNceil' : 2 * |L'| ≤ (N : ℝ) := by
            have h := @Int.cast_le ℝ _ _ _ |>.mpr hNceil
            push_cast at h
            linarith
          rw [abs_le] at hN
          grind
        · have hceil' : |L'| ≤ (⌈|L'|⌉ : ℝ) := Int.le_ceil |L'|
          have hNceil' : 2 * |L'| ≤ (N : ℝ) := by
            have h := @Int.cast_le ℝ _ _ _ |>.mpr hNceil
            push_cast at h
            linarith
          rw [abs_le] at hN
          grind
      · exact absurd htop' htop
      · exact absurd hbot' hbot
  · unfold Sequence.ExtendedLimitPoint
    rintro (htop | hzero | hbot) <;> split_ifs with hbot' htop' <;> try grind
    · rw [htop] at hbot'; exact absurd hbot' bot_ne_top
    · intro hbelow
      obtain ⟨B, hB⟩ := hbelow
      obtain ⟨N, hN⟩ := exists_nat_gt |B|
      specialize hB (3 * N + 2) (by grind)
      unfold α at hB; simp_all
      rw [if_pos (by grind)] at hB
      have hmod : (3 * (N:ℤ) + 2).toNat % 3 = 2 := by omega
      simp [hmod] at hB
      rw [abs_lt] at hN
      have hcast : ((3 * (N : ℤ) + 2).toNat : ℝ) = 3 * N + 2 := by
        have : (3 * (N : ℤ) + 2) ≥ 0 := by grind
        have := Int.toNat_of_nonneg this
        exact_mod_cast this
      linarith [hN.1, hB, hcast]
    · rw [hzero] at hbot'; exact absurd hbot' (coe_ne_top _)
    · rw [hzero] at htop'; exact absurd htop' (coe_ne_bot _)
    · rw [hzero]
      simp
      rw [Sequence.limit_point_def]
      intro ε hε N hNam
      use 3 * N
      constructor
      · grind
      · simp_all
        unfold α
        have hmod : (3 * N).toNat % 3 = 0 := by omega
        simp [hmod]
        grind
    · intro habove
      obtain ⟨A, hA⟩ := habove
      obtain ⟨N, hN⟩ := exists_nat_gt |A|
      specialize hA (3 * N + 1) (by grind)
      unfold α at hA; simp_all
      rw [if_pos (by grind)] at hA
      have hmod : (3 * (N:ℤ) + 1).toNat % 3 = 1 := by omega
      simp [hmod] at hA
      rw [abs_lt] at hN
      have hcast : ((3 * (N : ℤ) + 1).toNat : ℝ) = 3 * N + 1 := by
        have : (3 * (N : ℤ) + 1) ≥ 0 := by grind
        have := Int.toNat_of_nonneg this
        exact_mod_cast this
      linarith [hN.1, hA, hcast]


/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by
  rw [Sequence.limit_point_def] at hbc ⊢
  intro ε hε N hNam
  specialize hbc (ε/2) (by positivity)
  specialize hbc (max N b.m) (by grind)
  obtain ⟨N₁, hNbm₁, hN₁⟩ := hbc
  specialize hab N₁ (by grind)
  rw [Sequence.limit_point_def] at hab
  specialize hab (ε/2) (by positivity) N₁ (by grind)
  obtain ⟨N₂, hNam₂, hN₂⟩ := hab
  use N₂
  constructor <;> grind

end Chapter6
