import Mathlib.Tactic
import Analysis.Section_8_1
import Analysis.Section_8_2

/-!
# Analysis I, Section 8.3: Uncountable sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Uncountable sets.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

-/

namespace Chapter8

/-- Theorem 8.3.1 -/
theorem EqualCard.power_set_false (X:Type) : ¬ EqualCard X (Set X) := by
  -- This proof is written to follow the structure of the original text.
  by_contra!; choose f hf using this
  set A := {x | x ∉ f x }; choose x hx using hf.2 A
  by_cases h : x ∈ A <;> have h' := h
  . simp [A] at h'; simp_all
  rw [←hx] at h'
  have : x ∈ A := by simp [A, h']
  contradiction

theorem Uncountable.iff (X:Type) : Uncountable X ↔ ¬ AtMostCountable X := by
  rw [AtMostCountable.iff, uncountable_iff_not_countable]


theorem Uncountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Uncountable X ↔ Uncountable Y := by
    simp [Uncountable.iff, AtMostCountable.equiv hXY]

/-- Corollary 8.3.3 -/
theorem Uncountable.power_set_nat : Uncountable (Set ℕ) := by
  -- This proof is written to follow the structure of the original text.
  rw [Uncountable.iff]
  unfold AtMostCountable
  have : ¬ CountablyInfinite (Set ℕ) := by
    have := EqualCard.power_set_false ℕ
    contrapose! this; exact this.symm
  have : ¬ Finite (Set ℕ) := by
    by_contra!
    have : Finite ((fun x:ℕ ↦ ({x}:Set ℕ)) '' .univ) := Finite.Set.subset (s := .univ) (by aesop)
    replace : Finite ℕ := by
      apply Finite.of_finite_univ
      rw [←Set.finite_coe_iff]
      apply Finite.Set.finite_of_finite_image (f := fun x ↦ ({x}:Set ℕ))
      intro _ _ _ _ _; aesop
    have hinf : ¬ Finite ℕ := by rw [not_finite_iff_infinite]; infer_instance
    contradiction
  tauto

open Real in
/-- Corollary 8.3.4 -/
theorem Uncountable.real : Uncountable ℝ := by
  -- This proof is written to follow the structure of the original text.
  set a : ℕ → ℝ := fun n ↦ (10:ℝ)^(-(n:ℝ))
  set f : Set ℕ → ℝ := fun A ↦ ∑' n:A, a n
  have hsummable (A: Set ℕ) : Summable (fun n:A ↦ a n) := by
    apply Summable.subtype (f := a)
    convert summable_geometric_of_lt_one (?_:0 ≤ (1/10:ℝ)) ?_ using 2 with n <;> try norm_num
    unfold a
    rw [one_div_pow, rpow_neg, one_div]; simp; norm_num
  have h_decomp {A B C: Set ℕ} (hC : C = A ∪ B) (hAB: ∀ n, n ∉ A ∩ B) :  ∑' n:C, a n = ∑' n:A, a n + ∑' n:B, a n := by
    convert Summable.tsum_union_disjoint ?_ ?_ ?_ <;> first | infer_instance | try apply hsummable
    . rw [hC]
    rw [Set.disjoint_iff_inter_eq_empty]; grind
  have h_nonneg (A:Set ℕ) : ∑' n:A, a n ≥ 0 := by simp [a]; positivity
  have h_congr {A B: Set ℕ} (hAB: A = B) : ∑' n:A, a n = ∑' n:B, a n  := by rw [hAB]
  have : Function.Injective f := by
    intro A B hAB; by_contra!
    rw [←Set.symmDiff_nonempty] at this
    apply Nat.min_spec at this
    set n₀ := Nat.min (symmDiff A B)
    simp [symmDiff] at this; choose h1 h2 using this
    wlog h : n₀ ∈ A ∧ n₀ ∉ B generalizing A B
    . simp [h] at h1
      apply this hAB.symm <;> simp [symmDiff_comm] <;> grind
    replace h2 {n:ℕ} (hn: n < n₀) : n ∈ A ↔ n ∈ B := by grind
    have : (0:ℝ) > 0 := calc
      _ = f A - f B := by linarith
      _ = ∑' n:A, a n - ∑' n:B, a n := rfl
      _ = (∑' n:{n ∈ A|n ≤ n₀}, a n + ∑' n:{n ∈ A|n > n₀}, a n) -
          (∑' n:{n ∈ B|n ≤ n₀}, a n + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp; grind
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + ∑' n:{n ∈ A|n = n₀}, a n) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + ∑' n:{n ∈ B|n = n₀}, a n) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr; all_goals {
          apply h_decomp
          . ext n; simp [le_iff_lt_or_eq]
          intro n hn; simp at hn; linarith
        }
      _ = ((∑' n:{n ∈ A|n < n₀}, a n + a n₀) + ∑' n:{n ∈ A|n > n₀}, a n) -
          ((∑' n:{n ∈ B|n < n₀}, a n + 0) + ∑' n:{n ∈ B|n > n₀}, a n) := by
        congr 3
        . calc
            _ = ∑' n:({n₀}:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
        . calc
            _ = ∑' n:(∅:Set ℕ), a n := by apply h_congr; ext n; simp; grind
            _ = _ := by simp
      _ = (∑' n:{n ∈ A|n < n₀}, a n - ∑' n:{n ∈ B|n < n₀}, a n) + a n₀ +
          ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by abel
      _ = 0 + a n₀ + ∑' n:{n ∈ A|n > n₀}, a n - ∑' n:{n ∈ B|n > n₀}, a n := by
        congr; rw [sub_eq_zero]; apply tsum_congr_set_coe; grind
      _ ≥ 0 + a n₀ + 0 - ∑' n:{n|n > n₀}, a n := by
        gcongr; positivity
        calc
          _ = ∑' (n : {n ∈ B|n > n₀}), a n + ∑' (n : {n ∉ B|n > n₀}), a n := by
            apply h_decomp
            . ext n; simp; tauto
            intro n hn; simp at hn; tauto
          _ ≥ ∑' (n : {n ∈ B|n > n₀}), a n + 0 := by gcongr; solve_by_elim
          _ = _ := by simp
      _ = 0 + (10:ℝ)^(-(n₀:ℝ)) + 0 - (1 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by
        congr
        set ι : ℕ → {n | n > n₀} := fun j ↦ ⟨ j+(n₀+1), by simp; linarith ⟩
        have hι : Function.Bijective ι := by
          split_ands
          . intro j k hjk; simpa [ι] using hjk
          intro ⟨ n, hn ⟩; simp [ι] at hn ⊢; use n - n₀ - 1; omega
        rw [←(Equiv.ofBijective ι hι).tsum_eq]
        simp [ι, a]
        calc
          _ = ∑' j:ℕ, (10:ℝ)^(-1-n₀:ℝ) * (1/(10:ℝ))^j := by
            apply tsum_congr; intro j
            simp only [Equiv.ofBijective, DFunLike.coe, EquivLike.coe]
            rw [pow_add, pow_add, rpow_sub, rpow_neg, rpow_one, rpow_natCast] <;> try positivity
            simp; congr
          _ = (10:ℝ)^(-1-n₀:ℝ) * ∑' j:ℕ, (1/(10:ℝ))^j := tsum_mul_left
          _ = _ := by
            rw [tsum_geometric_of_lt_one, (?_:-1 - (n₀:ℝ) = (-n₀:ℝ) + (-1:ℝ)),
                rpow_add, rpow_neg, rpow_natCast] <;> try positivity
            ring; abel; norm_num
      _ = (8 / (9:ℝ)) * (10:ℝ)^(-(n₀:ℝ)) := by ring
      _ > 0 := by positivity
    simp at this
  replace : EqualCard (Set ℕ) (Set.range f) := ⟨(Equiv.ofInjective _ this).toFun, (Equiv.ofInjective _ this).bijective⟩
  replace := (equiv this).mp power_set_nat
  contrapose this
  rw [not_uncountable_iff] at this ⊢
  apply SetCoe.countable

/-- Exercise 8.3.1 -/
example {X:Type} [Finite X] : Nat.card (Set X) = 2 ^ Nat.card X := by
  classical
  induction X using Finite.induction_empty_option with
  | of_equiv e ih =>
      rw [← Nat.card_congr e, ← ih]
      apply Nat.card_congr
      exact Equiv.Set.congr e.symm
  | h_empty =>
      simp
  | h_option ih =>
      rename_i X _
      have e : Set (Option X) ≃ Set X × Bool :=
        { toFun := fun s => (some ⁻¹' s, none ∈ s)
          invFun := fun p => if p.2 then insert none (some '' p.1) else some '' p.1
          left_inv := by
            intro s
            ext x
            cases x with
            | none =>
                simp
                split_ifs with h
                · simp; exact h
                · simp; exact h
            | some a =>
                simp
                split_ifs with h <;>
                simp
          right_inv := by
            intro ⟨s, b⟩
            cases b
            · simp
              grind
            · simp
              grind
        }
      rw [Nat.card_congr e]
      rw [Nat.card_eq_fintype_card (α := Set X × Bool)]
      rw [Fintype.card_prod]
      rw [Fintype.card_bool]
      rw [Nat.card_eq_fintype_card (α := Option X)]
      rw [Fintype.card_option]
      simp
      rw [pow_succ]

open Classical in
/-- Exercise 8.3.2.  Some subtle type changes due to how sets are implemented in Mathlib. Also we shift the sequence {lit}`D` by one so that we can work in {lean}`Set A` rather than {lean}`Set B`. -/
theorem Schroder_Bernstein_lemma {X: Type} {A B C: Set X} (hAB: A ⊆ B) (hBC: B ⊆ C) (f: C ↪ A) :
  let D : ℕ → Set A := Nat.rec ((f.image ∘ ((B.embeddingOfSubset _ hBC).image)) {x:B | ↑x ∉ A}) (fun _ ↦ (f.image ∘ ((B.embeddingOfSubset _ hBC).image) ∘ (A.embeddingOfSubset _ hAB).image))
  Set.univ.PairwiseDisjoint D ∧
  let g : A → B := fun x ↦ if h: x ∈ ⋃ n, D n ∧ ∃ y:B, f ⟨↑y, hBC y.property⟩ = x then h.2.choose else ⟨ ↑x, hAB x.property ⟩
  Function.Bijective g
  := by
  sorry

open Classical in
lemma Schroder_Bernstein_lemma' {A : Type} {B : Set A}
    (f : A → A) (hf : Function.Injective f) (hfA : ∀ x, f x ∈ B) : EqualCard A B := by
  suffices h : ∃ Bf : Set A,
      Bf ⊆ B ∧
      f '' (Set.univ \ (B \ Bf)) = Bf ∧
      f '' (B \ Bf) ⊆ B \ Bf by
    obtain ⟨Bf, hBfA, hBfsubset, hBf⟩ := h
    let g : A → B := fun x =>
      if hx : x ∈ Set.univ \ (B \ Bf)
      then ⟨f x, by exact hfA x⟩
      else ⟨x, by simp at hx; exact hx.1⟩
    use g; constructor
    · intro x y hxy
      unfold g at hxy
      split_ifs at hxy with h₁ h₂ h₃
      · simp at hxy
        exact hf hxy
      · simp at hxy h₁ h₂
        have hfxBf : f x ∈ Bf := by
          rw [← hBfsubset]
          use x
          simp
          exact h₁
        rw [hxy] at hfxBf
        exact absurd hfxBf h₂.2
      · simp at hxy h₁ h₃
        have hynotB : y ∈ Set.univ \ (B \ Bf) := by
          exact ⟨trivial, by simp; exact h₃⟩
        have hfyBf : f y ∈ Bf := by
          rw [← hBfsubset]
          use y
        rw [← hxy] at hfyBf
        exact absurd hfyBf h₁.2
      · simp at hxy
        exact hxy
    · intro ⟨y, hy⟩
      by_cases hyBf : y ∈ Bf
      · rw [← hBfsubset] at hyBf
        simp at hyBf
        choose z hz hz' using hyBf
        use z
        unfold g
        simp
        rw [dif_pos hz]
        simp
        exact hz'
      · use y
        unfold g
        simp
        rw [dif_neg (by simp; exact ⟨hy, hyBf⟩)]
  set Bf := ⋃ n : ℕ, f^[n+1] '' (Set.univ \ B)
  use Bf
  refine ⟨?_, ?_, ?_⟩
  · unfold Bf
    intro x hx
    simp at hx
    obtain ⟨i, y, hnotin, rfl⟩ := hx
    induction i with
    | zero      =>
        simp
        apply hfA
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp]
        apply hfA
  · ext x
    simp
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := hx
      by_cases hyB : y ∈ B
      · have hyBf := hy hyB
        unfold Bf at hyBf; simp at hyBf
        obtain ⟨n, z, hz, rfl⟩ := hyBf
        have := hy hyB
        unfold Bf; simp
        use n + 1
        use z
        constructor
        · exact hz
        · exact Function.iterate_succ_apply' f n (f z)
      · unfold Bf; simp
        use 0; simp
        use y
    · intro hx
      unfold Bf at hx
      simp at hx
      obtain ⟨n, z, hz, rfl⟩ := hx
      use f^[n] z
      constructor
      · intro h
        unfold Bf; simp
        cases n with
        | zero => exact absurd h (by simp [hz])
        | succ n => exact ⟨n, z, hz, rfl⟩
      · exact (Function.iterate_succ_apply' f n z).symm
  · intro x hx
    simp at hx ⊢
    obtain ⟨y, ⟨hyB, hyBf⟩, rfl⟩ := hx
    constructor
    · apply hfA
    · intro hfy
      unfold Bf at hfy; simp at hfy
      obtain ⟨i, x, hx, hfx⟩ := hfy
      apply hyBf
      unfold Bf
      simp only [Set.mem_iUnion, Set.mem_image]
      have : f^[i] (f x) = f (f^[i] x) := by exact Function.iterate_succ_apply' f i x
      rw [this] at hfx
      use i - 1
      use x
      constructor
      · trivial
      · simp
        cases i with
        | zero => exact absurd (hf hfx) (by simp; intro h; rw [← h] at hyB; exact hx hyB)
        | succ n =>
            simp
            have hfffx := hf hfx
            simp at hfffx
            exact hfffx

abbrev LeCard (X Y: Type) : Prop := ∃ f: X → Y, Function.Injective f

/-- Exercise 8.3.3 -/
theorem Schroder_Bernstein {X Y:Type} (hXY : LeCard X Y) (hYX : LeCard Y X) : EqualCard X Y := by
  choose f hf using hXY
  choose g hg using hYX
  let A := g '' Set.univ
  have h1 : EqualCard X A := by
    apply Schroder_Bernstein_lemma' (g ∘ f)
    · exact hg.comp hf
    · intro x
      simp
      apply Set.mem_image_of_mem g
      trivial
  have h2 : EqualCard Y A := by
    use fun y => ⟨g y, by apply Set.mem_image_of_mem g; trivial⟩
    constructor
    · intro x y hxy
      simp at hxy
      exact hg hxy
    · intro x
      simp
      choose z hz using x.property
      use z
      simp at hz
      exact Subtype.ext hz
  exact h1.trans h2.symm


abbrev LtCard (X Y: Type) : Prop := LeCard X Y ∧ ¬ EqualCard X Y

/-- Exercise 8.3.4 -/
example {X:Type} : LtCard X (Set X) := by
  unfold LtCard
  let f : X → Set X := fun x => {x}
  have hfinj : Function.Injective f := by
    intro a b hab
    unfold f at hab
    simp at hab
    exact hab
  constructor
  · use f
  · exact EqualCard.power_set_false X

example {A B C: Type} (hAB: LtCard A B) (hBC: LtCard B C) :
  LtCard A C := by
  choose hleAB hltAB using hAB
  choose hleBC hltBC using hBC
  have ⟨f, hf⟩ := hleAB
  have ⟨g, hg⟩ := hleBC
  constructor
  · use (g ∘ f)
    apply hg.comp
    exact hf
  · intro h
    have : EqualCard B C := by
      apply Schroder_Bernstein
      · exact hleBC
      · have ⟨τ, hτ⟩ := h
        set τ' := Equiv.ofBijective τ hτ
        use f ∘ τ'.symm
        apply hf.comp
        exact Equiv.injective τ'.symm
    grind


abbrev CardOrder : Preorder Type := {
  le := LeCard
  lt := LtCard
  le_refl := by
    intro a
    use id
    exact Function.injective_id
  le_trans := by
    intro a b c hab hbc
    choose f hf using hab
    choose g hg using hbc
    use g ∘ f
    apply hg.comp
    exact hf
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro ⟨hlt, hne⟩
      constructor
      · exact hlt
      · intro hba
        have heq := Schroder_Bernstein hlt hba
        exact absurd heq hne
    · intro ⟨hle, hnlt⟩
      constructor
      · exact hle
      · intro hne
        have : EqualCard b a := by exact EqualCard.symm hne
        choose g hg using this
        push_neg at hnlt
        specialize hnlt g
        exact absurd hg.injective hnlt
}

/-- Exercise 8.3.5 -/
example (X:Type) : ¬ CountablyInfinite (Set X) := by
  intro hci
  have hatmost : AtMostCountable X := by
    rw [AtMostCountable.iff]
    choose f hf using hci
    use fun x => f {x}
    intro a b hab
    simp at hab
    have hsingleton := hf.injective hab
    simp at hsingleton
    exact hsingleton
  rcases hatmost with hcinf | hfin
  · choose e he using hcinf
    have hcount : EqualCard (Set X) (Set ℕ) := by
      have t := Equiv.ofBijective e he
      use fun S => t '' S  -- map each S to the preimage of t
      constructor
      · apply Set.image_injective.mpr
        exact Equiv.injective t
      · apply Set.image_surjective.mpr
        exact Equiv.surjective t
    have hpowerset := ((CountablyInfinite.equiv hcount).mp hci)
    have hnotcountable := (Uncountable.iff _).mp (Uncountable.power_set_nat)
    unfold AtMostCountable at hnotcountable
    rw [not_or] at hnotcountable
    exact absurd hpowerset hnotcountable.1
  · haveI := Fintype.ofFinite X
    have hfin : Finite (Set X) := by
      exact Set.instFinite
    exact absurd hci.toInfinite (not_infinite_iff_finite.mpr hfin)

end Chapter8
