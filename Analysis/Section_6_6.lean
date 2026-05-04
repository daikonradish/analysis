import Mathlib.Tactic
import Analysis.Section_6_5

/-!
# Analysis I, Section 6.6: Subsequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of a subsequence.
-/

namespace Chapter6

/-- Definition 6.6.1 -/
abbrev Sequence.subseq (a b: ℕ → ℝ) : Prop := ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, b n = a (f n)

/- Example 6.6.2 -/
example (a:ℕ → ℝ) : Sequence.subseq a (fun n ↦ a (2 * n)) := by
  use (fun n => 2 * n)
  constructor
  · intro n₁ n₂ hn
    simp_all
  · intro n
    simp_all

example {f: ℕ → ℕ} (hf: StrictMono f) : Function.Injective f := by
  intro n₁ n₂ heq
  rcases lt_trichotomy n₁ n₂ with hlt | heq | hgt
  · linarith [hf hlt]
  · exact heq
  · linarith [hf hgt]

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ 1 + (10:ℝ)^(-(n:ℤ)-1)) := by
  use (fun n => 2 * n)
  constructor
  · intro n₁ n₂ hn; simp_all
  · intro n
    simp

example :
    Sequence.subseq (fun n ↦ if Even n then 1 + (10:ℝ)^(-(n/2:ℤ)-1) else (10:ℝ)^(-(n/2:ℤ)-1))
    (fun n ↦ (10:ℝ)^(-(n:ℤ)-1)) := by
  use (fun n => 2 * n + 1)
  constructor
  · intro n₁ n₂ hn; simp_all
  · intro n
    simp; grind

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_self (a:ℕ → ℝ) : Sequence.subseq a a := by
  use id
  constructor
  · intro n₁ n₂ hn; simp_all
  · intro n; simp

/-- Lemma 6.6.4 / Exercise 6.6.1 -/
theorem Sequence.subseq_trans {a b c:ℕ → ℝ} (hab: Sequence.subseq a b) (hbc: Sequence.subseq b c) :
    Sequence.subseq a c := by
    obtain ⟨f, hmonof, hf⟩ := hab
    obtain ⟨g, hmonog, hg⟩ := hbc
    use f ∘ g
    constructor
    · exact StrictMono.comp hmonof hmonog
    · intro n; simp_all

/-- Proposition 6.6.5 / Exercise 6.6.4 -/
theorem Sequence.convergent_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ ∀ b:ℕ → ℝ, Sequence.subseq a b → (b:Sequence).TendsTo L := by
  constructor
  · intro hatt b hb
    obtain ⟨f, hmonof, hf⟩ := hb
    rw [Sequence.tendsTo_iff] at hatt ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hatt ε hε
    use max 0 N
    intro n hn
    observe : n ≥ 0
    lift n to ℕ using (by omega)
    simp at hn
    have : f n ≥ N := by
      by_cases hN0 : N < 0
      · grind
      · push_neg at hN0
        lift N to ℕ using (by omega)
        simp at hn ⊢
        have hle := (StrictMono.id_le hmonof) n; simp at hle
        linarith
    specialize hN (f n) this
    specialize hf n
    simp at hN ⊢
    rwa [hf]
  · intro hsubseq
    specialize hsubseq a (Sequence.subseq_self a)
    exact hsubseq

/-- Proposition 6.6.6 / Exercise 6.6.5 -/
theorem Sequence.limit_point_iff_subseq (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).TendsTo L := by
  constructor
  · intro halimpt
    rw [Sequence.limit_point_def] at halimpt
    have hchoice : ∀ k : ℕ, ∃ n : ℕ, n > k ∧ |a n - L| ≤ 1 / (k+1:ℝ) := by
      intro k
      obtain ⟨N, hNam, hN⟩ := halimpt (1/(k+1:ℝ)) (by positivity) (k+1) (by grind)
      have : N ≥ 0 := by grind
      lift N to ℕ using (by omega)
      simp at hNam
      use N
      constructor
      · grind
      · simp at hN; grind
    let f : ℕ → ℕ := Nat.rec
      (hchoice 0).choose
      (fun k prev => (hchoice prev).choose)
    have hfdef : ∀ n, f (n+1) = (hchoice (f n)).choose := fun n => rfl
    have hfmono : StrictMono f := by
      apply strictMono_nat_of_lt_succ
      intro n
      exact (hchoice (f n)).choose_spec.1
    have hsuccle : ∀ n:ℕ, n+1 ≤ f n := by
      intro n
      induction' n with k ih
      · exact (hchoice 0).choose_spec.1
      · have :=
          calc k + 1 + 1
                 ≤ f k + 1     := by linarith only [ih]
               _ < f (k+1) + 1 := by observe : k < k+1; gcongr; exact (hfmono this)
        grind
    have habsle : ∀ n:ℕ, |a (f n) - L| ≤ 1 / (n+1:ℝ) := by
      intro n
      induction' n with k _
      · exact (hchoice 0).choose_spec.2
      · obtain h1 := (hchoice (f k)).choose_spec.2; rw [← hfdef k] at h1
        have h2 : (k+1) + 1 ≤ (f k) + 1 := by linarith only [hsuccle k]
        push_cast at h1 ⊢
        rify at h2
        have h3 := div_le_div_of_nonneg_left (a:=1) (by grind) (by positivity) h2
        grind
    let b : ℕ → ℝ := fun n => a (f n)
    have hsubseq : Sequence.subseq a b := by
      use f
      constructor
      · exact hfmono
      · intro n; unfold b; rfl
    use b
    constructor
    · exact hsubseq
    · rw [Sequence.tendsTo_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
      use N
      intro n hn
      lift n to ℕ using (by omega)
      simp at hn ⊢; unfold b
      specialize habsle n
      have : 1 / ((n:ℝ) + 1) ≤ 1 / ((N:ℝ) + 1) := by gcongr
      grind
  · intro hsubseq
    obtain ⟨b, hbseq, hbtt⟩ := hsubseq
    obtain ⟨f, hfmono, hf⟩ := hbseq
    rw [Sequence.limit_point_def]
    intro ε hε N hNam; simp at hNam; lift N to ℕ using (by omega)
    rw [Sequence.tendsTo_iff] at hbtt
    obtain ⟨N', hN'⟩ := hbtt ε hε
    let M := max N' N
    have : M ≥ 0 := by grind
    specialize hN' M (by grind)
    simp at hN'; rw [if_pos (by grind)] at hN'
    specialize hf M.toNat; rw [hf] at hN'
    use (f M.toNat)
    constructor
    · norm_cast
      have := hfmono.id_le M.toNat; simp at this
      grind
    · simp_all


/-- Theorem 6.6.8 (Bolzano-Weierstrass theorem) -/
theorem Sequence.convergent_of_subseq_of_bounded {a:ℕ→ ℝ} (ha: (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence).Convergent := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ ⟨ L_plus, hL_plus ⟩, ⟨ _, _ ⟩ ⟩ := finite_limsup_liminf_of_bounded ha
  have := limit_point_of_limsup hL_plus
  rw [limit_point_iff_subseq] at this; peel 2 this; solve_by_elim

/- Exercise 6.6.2 -/

def Sequence.exist_subseq_of_subseq :
  Decidable (∃ a b : ℕ → ℝ, a ≠ b ∧ Sequence.subseq a b ∧ Sequence.subseq b a) := by
    -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  apply isTrue
  let a : ℕ → ℝ := fun n => if Even n then 1 else -1
  let b : ℕ → ℝ := fun n => if Even n then -1 else 1
  use a
  use b
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have := congr_arg (· 1) heq; simp at this
    unfold a b at this
    simp_all; norm_num at this
  · use (fun n:ℕ => n + 1)
    constructor
    · intro n₁ n₂ hn
      simp_all
    · intro n
      by_cases hevodd : Even n
      · unfold a b; simp_all
      · unfold a b; simp_all
  · use (fun n:ℕ => n + 1)
    constructor
    · intro n₁ n₂ hn
      simp_all
    · intro n
      by_cases hevodd : Even n
      · unfold a b; simp_all
      · unfold a b; simp_all
/--
  Exercise 6.6.3.  You may find the API around Mathlib's {name}`Nat.find` to be useful
  (and {syntax command}`open Classical` to avoid any decidability issues)
-/
theorem Sequence.subseq_of_unbounded {a:ℕ → ℝ} (ha: ¬ (a:Sequence).IsBounded) :
    ∃ b:ℕ → ℝ, Sequence.subseq a b ∧ (b:Sequence)⁻¹.TendsTo 0 := by
  have hchoice : ∀ (M k : ℕ), ∃ n : ℕ, n > k ∧ |a n| > M := by
    intro M k
    by_contra! h'
    contrapose ha
    use Finset.fold max M (fun n => |a n|) (Finset.Icc 0 k)
    constructor
    · rw [ge_iff_le]
      rw [Finset.le_fold_max]
      grind
    · intro n
      simp_all
      split_ifs with h
      · lift n to ℕ using (by omega)
        by_cases hnk : k < n
        · specialize h' n hnk
          simp_all
          rw [Finset.le_fold_max]
          left; grind
        · push_neg at hnk
          rw [Finset.le_fold_max]
          right; use n;
          constructor <;> simp_all
      · simp; rw [Finset.le_fold_max]
        grind
  let f : ℕ → ℕ := fun k ↦ Nat.rec
    (hchoice 0 0).choose
    (fun k fk' ↦ (hchoice (k + 1) fk').choose) k
  have hfmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (hchoice (n+1) (f n)).choose_spec.1
  let b : ℕ → ℝ := fun n => a (f n)
  have hbound : ∀ n : ℕ, |b n| > (n:ℝ) := by
    intro n
    induction' n with k ih
    · exact (hchoice 0 0).choose_spec.2
    · exact (hchoice (k+1) (f k)).choose_spec.2
  use b
  constructor
  · use f
    constructor
    · exact hfmono
    · intro n; unfold b; rfl
  · rw [Sequence.tendsTo_iff]
    simp_rw [sub_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_ge (1/ε)
    use max 1 N
    intro n hn
    simp at hn
    lift n to ℕ using (by omega)
    simp at hn
    simp_all
    specialize hbound n
    field_simp at hN ⊢
    rw [div_le_iff₀ (by grind)]
    have := calc (1:ℝ) ≤ ε * (N:ℝ) := by exact hN
                     _ ≤ ε * (n:ℝ) := by gcongr; grind
                     _ < ε * |b n| := by gcongr
    linarith


end Chapter6
