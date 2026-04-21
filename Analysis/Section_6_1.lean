import Mathlib.Tactic
import Analysis.Section_5_1
import Analysis.Section_5_3
import Analysis.Section_5_epilogue

/-!
# Analysis I, Section 6.1: Convergence and limit laws

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of $`ε`-closeness, $`ε`-steadiness, and their eventual counterparts.
- Notion of a Cauchy sequence, convergent sequence, and bounded sequence of reals.

-/


/- Definition 6.1.1 (Distance).  Here we use the Mathlib distance. -/
#check Real.dist_eq

abbrev Real.Close (ε x y : ℝ) : Prop := dist x y ≤ ε

/--
  Definition 6.1.2 (ε-close). This is similar to the previous notion of ε-closeness, but where
  all quantities are real instead of rational.
-/
theorem Real.close_def (ε x y : ℝ) : ε.Close x y ↔ dist x y ≤ ε := by rfl

namespace Chapter6

/--
  Definition 6.1.3 (Sequence). This is similar to the Chapter 5 sequence, except that now the
  sequence is real-valued. As with Chapter 5, we start sequences from 0 by default.
-/
@[ext]
structure Sequence where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Sequences can be thought of as functions from {lean}`ℤ` to {lean}`ℝ`. -/
instance Sequence.instCoeFun : CoeFun Sequence (fun _ ↦ ℤ → ℝ) where
  coe a := a.seq

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

/-- Functions from {lean}`ℕ` to {lean}`ℝ` can be thought of as sequences. -/
instance Sequence.instCoe : Coe (ℕ → ℝ) Sequence where
  coe := ofNatFun

abbrev Sequence.mk' (m:ℤ) (a: { n // n ≥ m } → ℝ) : Sequence where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by simp_all

lemma Sequence.eval_mk {n m:ℤ} (a: { n // n ≥ m } → ℝ) (h: n ≥ m) :
    (Sequence.mk' m a) n = a ⟨ n, h ⟩ := by simp [h]

@[simp]
lemma Sequence.eval_coe (n:ℕ) (a: ℕ → ℝ) : (a:Sequence) n = a n := by simp

/--
  {given -show}`n₁, n₀`
  {lean}`a.from n₁` starts {lean}`a : Sequence` from {name}`n₁`.  It is intended for use when {lean}`n₁ ≥ n₀`, but returns
  the "junk" value of the original sequence {name}`a` otherwise.
-/
abbrev Sequence.from (a:Sequence) (m₁:ℤ) : Sequence := mk' (max a.m m₁) (a ↑·)

lemma Sequence.from_eval (a:Sequence) {m₁ n:ℤ} (hn: n ≥ m₁) :
  (a.from m₁) n = a n := by
  simp [hn]; intros; symm; solve_by_elim [a.vanish]

end Chapter6

/-- Definition 6.1.3 (ε-steady) -/
abbrev Real.Steady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m)

/-- Definition 6.1.3 (ε-steady) -/
lemma Real.steady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.Steady a ↔ ∀ n ≥ a.m, ∀ m ≥ a.m, ε.Close (a n) (a m) := by rfl

/-- Definition 6.1.3 (Eventually ε-steady) -/
abbrev Real.EventuallySteady (ε: ℝ) (a: Chapter6.Sequence) : Prop :=
  ∃ N ≥ a.m, ε.Steady (a.from N)

/-- Definition 6.1.3 (Eventually ε-steady) -/
lemma Real.eventuallySteady_def (ε: ℝ) (a: Chapter6.Sequence) :
  ε.EventuallySteady a ↔ ∃ N, (N ≥ a.m) ∧ ε.Steady (a.from N) := by rfl

/-- For fixed {name}`a`, the function `ε ↦ ε.Steady s` is monotone -/
theorem Real.Steady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂) (hsteady: ε₁.Steady a) :
    ε₂.Steady a := by grind

/-- For fixed {name}`a`, the function `ε ↦ ε.EventuallySteady s` is monotone -/
theorem Real.EventuallySteady.mono {a: Chapter6.Sequence} {ε₁ ε₂: ℝ} (hε: ε₁ ≤ ε₂)
  (hsteady: ε₁.EventuallySteady a) :
    ε₂.EventuallySteady a := by peel 2 hsteady; grind [Steady.mono]

namespace Chapter6

/-- Definition 6.1.3 (Cauchy sequence) -/
abbrev Sequence.IsCauchy (a:Sequence) : Prop := ∀ ε > (0:ℝ), ε.EventuallySteady a

/-- Definition 6.1.3 (Cauchy sequence) -/
lemma Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℝ), ε.EventuallySteady a := by rfl

/-- This is almost the same as {name}`Chapter5.Sequence.IsCauchy.coe` -/
lemma Sequence.IsCauchy.coe (a:ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ ∀ ε > 0, ∃ N, ∀ j ≥ N, ∀ k ≥ N, dist (a j) (a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩
    lift N to ℕ using hN; use N
    intro j hj k hk
    simp [Real.steady_def] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all
  rintro ⟨ N, h' ⟩; refine ⟨ max N 0, by simp, ?_ ⟩
  intro n hn m hm; simp at hn hm
  have npos : 0 ≤ n := by omega
  have mpos : 0 ≤ m := by omega
  simp [hn, hm, npos, mpos]
  lift n to ℕ using npos
  lift m to ℕ using mpos
  specialize h' n ?_ m ?_ <;> try grind

lemma Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℝ) :
    (mk' n₀ a).IsCauchy
    ↔ ∀ ε > 0, ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N, dist (mk' n₀ a j) (mk' n₀ a k) ≤ ε := by
  peel with ε hε
  constructor
  · rintro ⟨ N, hN, h' ⟩; refine ⟨ N, hN, ?_ ⟩
    dsimp at hN
    intro j hj k hk
    simp only [Real.Steady, show max n₀ N = N by omega] at h'
    specialize h' j ?_ k ?_ <;> try omega
    simp_all [show n₀ ≤ j by omega, show n₀ ≤ k by omega]
  rintro ⟨ N, _, _ ⟩; use max n₀ N; grind

@[coe]
abbrev Sequence.ofChapter5Sequence (a: Chapter5.Sequence) : Sequence :=
{
  m := a.n₀
  seq n := a n
  vanish n hn := by simp [a.vanish n hn]
}

instance Chapter5.Sequence.inst_coe_sequence : Coe Chapter5.Sequence Sequence where
  coe := Sequence.ofChapter5Sequence

@[simp]
theorem Chapter5.coe_sequence_eval (a: Chapter5.Sequence) (n:ℤ) : (a:Sequence) n = (a n:ℝ) := rfl

theorem Sequence.is_steady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.Steady a ↔ (ε:ℝ).Steady (a:Sequence) := by
  rw [Rat.Steady]
  rw [Real.Steady]
  peel with n hn m hm
  rw [Rat.Close, Real.Close, Real.dist_eq]
  constructor
  · intro hrat
    push_cast
    exact_mod_cast hrat
  · intro hreal
    push_cast at hreal
    exact_mod_cast hreal

theorem Sequence.is_eventuallySteady_of_rat (ε:ℚ) (a: Chapter5.Sequence) :
    ε.EventuallySteady a ↔ (ε:ℝ).EventuallySteady (a:Sequence) := by
  peel with N hN
  rw [Rat.Steady, Real.Steady]
  peel with n hn m hm
  simp at hn hm
  simp_all
  rw [Rat.Close, Rat.dist_eq]
  constructor
  · intro hrat
    exact_mod_cast hrat
  · intro hreal
    exact_mod_cast hreal

/-- Proposition 6.1.4 -/
theorem Sequence.isCauchy_of_rat (a: Chapter5.Sequence) : a.IsCauchy ↔ (a:Sequence).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  constructor
  swap
  . intro h; rw [isCauchy_def] at h
    rw [Chapter5.Sequence.isCauchy_def]
    intro ε hε
    specialize h ε (by positivity)
    rwa [is_eventuallySteady_of_rat]
  intro h
  rw [Chapter5.Sequence.isCauchy_def] at h
  rw [isCauchy_def]
  intro ε hε
  choose ε' hε' hlt using exists_pos_rat_lt hε
  specialize h ε' hε'
  rw [is_eventuallySteady_of_rat] at h
  exact h.mono (le_of_lt hlt)

end Chapter6

/-- Definition 6.1.5 -/
abbrev Real.CloseSeq (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop := ∀ n ≥ a.m, ε.Close (a n) L

/-- Definition 6.1.5 -/
theorem Real.closeSeq_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.CloseSeq a L ↔ ∀ n ≥ a.m, dist (a n) L ≤ ε := by rfl

/-- Definition 6.1.5 -/
abbrev Real.EventuallyClose (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) : Prop :=
  ∃ N ≥ a.m, ε.CloseSeq (a.from N) L

/-- Definition 6.1.5 -/
theorem Real.eventuallyClose_def (ε: ℝ) (a: Chapter6.Sequence) (L:ℝ) :
  ε.EventuallyClose a L ↔ ∃ N, (N ≥ a.m) ∧ ε.CloseSeq (a.from N) L := by rfl

theorem Real.CloseSeq.coe (ε : ℝ) (a : ℕ → ℝ) (L : ℝ):
  (ε.CloseSeq a L) ↔ ∀ n, dist (a n) L ≤ ε := by
  constructor
  . intro h n; specialize h n; grind
  . intro h n hn; lift n to ℕ using (by omega); specialize h n; grind

theorem Real.CloseSeq.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.CloseSeq a L) :
    ε₂.CloseSeq a L := by peel 2 hclose; rw [Real.Close, Real.dist_eq] at *; linarith

theorem Real.EventuallyClose.mono {a: Chapter6.Sequence} {ε₁ ε₂ L: ℝ} (hε: ε₁ ≤ ε₂)
  (hclose: ε₁.EventuallyClose a L) :
    ε₂.EventuallyClose a L := by peel 2 hclose; grind [CloseSeq.mono]
namespace Chapter6

abbrev Sequence.TendsTo (a:Sequence) (L:ℝ) : Prop :=
  ∀ ε > (0:ℝ), ε.EventuallyClose a L

theorem Sequence.tendsTo_def (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > (0:ℝ), ε.EventuallyClose a L := by rfl

/-- Exercise 6.1.2 -/
theorem Sequence.tendsTo_iff (a:Sequence) (L:ℝ) :
  a.TendsTo L ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| ≤ ε := by
  peel with ε hε
  rw [Real.EventuallyClose]
  constructor
  · intro hseq
    obtain ⟨N, hNam, hεcl⟩ := hseq
    use N
    intro n hn
    rw [Real.closeSeq_def] at hεcl
    specialize hεcl n (by grind)
    rwa [Sequence.from_eval (a:Sequence) hn, Real.dist_eq] at hεcl
  · intro habs
    obtain ⟨N, hN⟩ := habs
    use max a.m N
    constructor
    · grind
    · rw [Real.closeSeq_def]
      intro n hn
      simp at hn
      specialize hN n (by grind)
      rwa [Sequence.from_eval (a:Sequence) (by grind), Real.dist_eq]

noncomputable def seq_6_1_6 : Sequence := (fun (n:ℕ) ↦ 1-(10:ℝ)^(-(n:ℤ)-1):Sequence)

/-- Examples 6.1.6 -/
example : (0.1:ℝ).CloseSeq seq_6_1_6 1 := by
  rw [seq_6_1_6, Real.CloseSeq.coe]
  intro n
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
    rw [sub_nonneg]
    rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
    gcongr
    positivity
  ), sub_sub_cancel, show (0.1:ℝ) = (10:ℝ)^(-1:ℤ) by norm_num]
  gcongr <;> grind


/-- Examples 6.1.6 -/
example : ¬ (0.01:ℝ).CloseSeq seq_6_1_6 1 := by
  intro h
  specialize h 0 (by positivity); simp [seq_6_1_6] at h; norm_num at h

/-- Examples 6.1.6 -/
example : (0.01:ℝ).EventuallyClose seq_6_1_6 1 := by
  rw [Real.eventuallyClose_def]
  use 2
  constructor
  · simp [seq_6_1_6]
  · rw [Real.closeSeq_def]
    intro n hn
    rw [Sequence.from_eval (seq_6_1_6:Sequence) (by grind)]
    simp at hn
    simp [seq_6_1_6]
    simp_all
    rw [if_pos (by linarith)]
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
      rw [sub_nonneg]
      rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
      gcongr
      positivity
    ), sub_sub_cancel, show (0.01:ℝ) = (10:ℝ)^(-2:ℤ) by norm_num]
    gcongr <;> grind


/-- Examples 6.1.6 -/
example : seq_6_1_6.TendsTo 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (10:ℝ)^(-1:ℤ) < 1)
  use N
  constructor
  · simp [seq_6_1_6]
  · intro n hn
    rw [Sequence.from_eval (seq_6_1_6:Sequence) (by grind)]
    simp at hn
    simp [seq_6_1_6]
    rw [if_pos (by linarith)]
    rw [@Int.max_eq_left n 0 (by omega)]
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by
      rw [sub_nonneg]
      rw (occs := .pos [2]) [show (1:ℝ) = 1 - 0 by norm_num]
      gcongr
      positivity
    ), sub_sub_cancel]
    rw [← zpow_natCast, ← zpow_mul] at hN
    rw [neg_one_mul] at hN
    have := calc 10 ^ (-n-1) ≤ 10 ^ (-(N:ℤ)) := by gcongr <;> grind
                           _ < ε             := by exact hN
    linarith


/-- Proposition 6.1.7 (Uniqueness of limits) -/
theorem Sequence.tendsTo_unique (a:Sequence) {L L':ℝ} (h:L ≠ L') :
    ¬ (a.TendsTo L ∧ a.TendsTo L') := by
  -- This proof is written to follow the structure of the original text.
  by_contra this
  choose hL hL' using this
  replace h : L - L' ≠ 0 := by grind
  replace h : |L-L'| > 0 := by positivity
  set ε := |L-L'| / 3
  have hε : ε > 0 := by positivity
  rw [tendsTo_iff] at hL hL'
  specialize hL ε hε; choose N hN using hL
  specialize hL' ε hε; choose M hM using hL'
  set n := max N M
  specialize hN n (by omega)
  specialize hM n (by omega)
  have : |L-L'| ≤ 2 * |L-L'|/3 := calc
    _ = dist L L' := by rw [Real.dist_eq]
    _ ≤ dist L (a.seq n) + dist (a.seq n) L' := dist_triangle _ _ _
    _ ≤ ε + ε := by rw [←Real.dist_eq] at hN hM; rw [dist_comm] at hN; gcongr
    _ = 2 * |L-L'|/3 := by grind
  linarith

/-- Definition 6.1.8 -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

/-- Definition 6.1.8 -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

/-- Definition 6.1.8 -/
abbrev Sequence.Divergent (a:Sequence) : Prop := ¬ a.Convergent

/-- Definition 6.1.8 -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

open Classical in
/--
  Definition 6.1.8.  We give the limit of a sequence the junk value of {lean}`0` if it is not convergent.
-/
noncomputable abbrev lim (a:Sequence) : ℝ := if h: a.Convergent then h.choose else 0

/-- Definition 6.1.8 -/
theorem Sequence.lim_def {a:Sequence} (h: a.Convergent) : a.TendsTo (lim a) := by
  simp [lim, h]; exact h.choose_spec

/-- Definition 6.1.8-/
theorem Sequence.lim_eq {a:Sequence} {L:ℝ} :
a.TendsTo L ↔ a.Convergent ∧ lim a = L := by
  constructor
  . intro h; by_contra! eq
    have : a.Convergent := by rw [convergent_def]; use L
    replace eq := a.tendsTo_unique (eq this)
    apply lim_def at this; tauto
  intro ⟨ h, rfl ⟩; convert lim_def h


/-- Proposition 6.1.11 -/
theorem Sequence.lim_harmonic :
    ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ (n+1:ℝ)⁻¹):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  rw [←lim_eq, tendsTo_iff]
  intro ε hε
  choose N hN using exists_int_gt (1 / ε); use N; intro n hn
  have hNpos : (N:ℝ) > 0 := by apply LT.lt.trans _ hN; positivity
  simp at hNpos
  have hnpos : n ≥ 0 := by linarith
  simp [hnpos, abs_inv]
  calc
    _ ≤ (N:ℝ)⁻¹ := by
      rw [inv_le_inv₀] <;> try positivity
      calc
        _ ≤ (n:ℝ) := by simp [hn]
        _ = (n.toNat:ℤ) := by simp [hnpos]
        _ = n.toNat := rfl
        _ ≤ (n.toNat:ℝ) + 1 := by linarith
        _ ≤ _ := le_abs_self _
    _ ≤ ε := by
      rw [inv_le_comm₀] <;> try positivity
      rw [←inv_eq_one_div _] at hN; order

/-- Proposition 6.1.12 / Exercise 6.1.5 -/
theorem Sequence.IsCauchy.convergent {a:Sequence} (h:a.Convergent) : a.IsCauchy := by
  intro ε hε
  obtain ⟨L, hL⟩ := h
  obtain ⟨N, hNam, hNcl⟩ := hL (ε/2) (by positivity)
  use N
  constructor
  · exact hNam
  · intro n hn m hm
    simp at hn hm
    have hncl := hNcl n (by grind)
    have hmcl := hNcl m (by grind)
    rw [Sequence.from_eval (a:Sequence) hn.2, Sequence.from_eval (a:Sequence) hm.2] at *
    rw [Real.close_def, Real.dist_eq] at *
    calc |a.seq n - a.seq m| = |a.seq n - L + (L - a.seq m)| := by ring_nf
                           _ ≤ |a.seq n - L| + |L - a.seq m| := by exact abs_add_le _ _
                           _ = |a.seq n - L| + |a.seq m - L| := by congr 1; rw [abs_sub_comm _ _]
                           _ ≤ ε                             := by grind

/-- Example 6.1.13 -/
lemma example6113part1 : ¬ (0.1:ℝ).EventuallySteady ((fun n ↦ (-1:ℝ)^n):Sequence) := by
  intro hevsteady
  obtain ⟨N, hN, hsteady⟩ := hevsteady
  simp at hN
  specialize hsteady N (by grind) (N+1) (by grind)
  rw [Sequence.from_eval _ (by grind), Sequence.from_eval _ (by grind)] at hsteady
  simp at hsteady
  rw [if_pos hN, if_pos (by linarith)] at hsteady
  rw [Real.dist_eq] at hsteady
  rcases Nat.even_or_odd N.toNat with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [@Int.toNat_add N 1 hN (by linarith), hk ] at hsteady
    simp at hsteady
    norm_num at hsteady
  · rw [@Int.toNat_add N 1 hN (by linarith), hk ] at hsteady
    simp at hsteady
    norm_num at hsteady


/-- Example 6.1.13 -/
lemma example6113part2 : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).IsCauchy := by
  rw [Sequence.isCauchy_def]
  intro hsteady
  exact example6113part1 (hsteady 0.1 (by linarith))

/-- Example 6.1.13 -/
example : ¬ ((fun n ↦ (-1:ℝ)^n):Sequence).Convergent := by
  intro hconverge
  have hcauchy := Sequence.IsCauchy.convergent hconverge
  exact example6113part2 hcauchy

/-- Proposition 6.1.15 / Exercise 6.1.6 (Formal limits are genuine limits)-/
theorem Sequence.lim_eq_LIM {a:ℕ → ℚ} (h: (a:Chapter5.Sequence).IsCauchy) :
    ((a:Chapter5.Sequence):Sequence).TendsTo (Chapter5.Real.equivR (Chapter5.LIM a)) := by

  sorry

/-  simp_rw [Chapter5.Sequence.IsCauchy.coe, Section_4_3.dist_eq] at h
  rw [Sequence.tendsTo_def]
  by_contra! hdoesnottend
  obtain ⟨ε₀, hε₀pos, hnotclose⟩ := hdoesnottend
  obtain ⟨ε₁, hε₁pos, hεlt⟩ := exists_rat_btwn hε₀pos
  have hcauchyclose := h (ε₁ / 2) (half_pos (by exact_mod_cast hε₁pos))
  obtain ⟨N₁, hNcauchy⟩ := hcauchyclose
  specialize hnotclose N₁
  simp at hnotclose
  obtain ⟨N₂, hN₂, hnotclose⟩ := hnotclose
  have : 0 ≤ N₂ := by grind
  lift N₂ to ℕ using (by omega)
  simp at hnotclose
  rw [if_pos (by omega)] at hnotclose
  rw [Real.dist_eq] at hnotclose
  --set L :=  (Chapter5.LIM a).toCut.toR
  specialize hNcauchy N₁ (by linarith)
  replace hnotclose : ε₁ < |a N₂ -  (Chapter5.LIM a).toCut.toR| := by linarith
  --have hnotclosereal : (ε₁:Chapter5.Real) < |((a N₂):Chapter5.Real) -  Chapter5.LIM a| := by exact_mod_cast hnotreal
  rcases lt_abs.mp hnotclose with (case1 | case2)
  · -- have : ∃ N : ℕ,
    --have : L + ((ε₁:ℝ) - ((ε₁:ℝ) / 2)) < ((a N₂):ℝ) - ((ε₁:ℝ) / 2) := by linarith
    --conv at this =>
      --lhs
      --ring_nf
      -- ⊢ ∀ {x : Chapter5.Real} {a : ℕ → ℚ}, (↑a).IsCauchy → (∃ N, ∀ n ≥ N, x ≤ ↑(a n)) → x ≤ Chapter5.LIM a
    sorry
  · sorry
#check Chapter5.Real.LIM_of_ge' -/


/-- Definition 6.1.16 -/
abbrev Sequence.BoundedBy (a:Sequence) (M:ℝ) : Prop :=
  ∀ n, |a n| ≤ M

/-- Definition 6.1.16 -/
lemma Sequence.boundedBy_def (a:Sequence) (M:ℝ) :
  a.BoundedBy M ↔ ∀ n, |a n| ≤ M := by rfl

/-- Definition 6.1.16 -/
abbrev Sequence.IsBounded (a:Sequence) : Prop := ∃ M ≥ 0, a.BoundedBy M

/-- Definition 6.1.16 -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

theorem Sequence.bounded_of_cauchy {a:Sequence} (h: a.IsCauchy) : a.IsBounded := by
  rw [Sequence.IsCauchy] at h
  obtain ⟨N, hN⟩ := h 1 (by positivity)
  simp at hN; obtain ⟨hNm, hsteady⟩ := hN
  rw [Real.Steady] at hsteady
  set tailbound := |a.seq N| + 1
  set headelems := Finset.Icc a.m N
  set headbound := (Finset.Icc a.m N).sup' (by exact Finset.nonempty_Icc.mpr hNm) (λ n => |a.seq n|)
  use max headbound tailbound
  have hmax : 0 ≤ max headbound tailbound := by
    apply le_max_iff.mpr
    right
    unfold tailbound
    positivity
  constructor
  · exact hmax
  · intro n
    by_cases vanished : n < a.m
    · have fact := a.vanish n vanished
      rw [fact, abs_zero]
      exact hmax
    · push_neg at vanished
      by_cases headtail : n ≤ N
      · have fact : n ∈ Finset.Icc a.m N := by exact Finset.mem_Icc.mpr ⟨vanished, headtail⟩
        simp; left
        unfold headbound
        exact Finset.le_sup' (λ n => |a.seq n|) fact
      · push_neg at headtail
        simp; right
        unfold tailbound
        specialize hsteady N (by grind) n (by grind)
        rw [Real.close_def, Real.dist_eq] at hsteady
        rw [@Sequence.from_eval a N N (by linarith)] at hsteady
        rw [@Sequence.from_eval a N n (by linarith)] at hsteady
        grind

/-- Corollary 6.1.17 -/
theorem Sequence.bounded_of_convergent {a:Sequence} (h: a.Convergent) : a.IsBounded := by
  exact Sequence.bounded_of_cauchy (Sequence.IsCauchy.convergent h)

/-- Example 6.1.18 -/
lemma example6118 : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).IsBounded := by
  intro hbdd
  obtain ⟨Bd, hBdpos, hBd⟩ := hbdd
  obtain ⟨N, hN⟩ := exists_nat_gt Bd
  specialize hBd N
  simp at hBd
  grind

/-- Example 6.1.18 -/
example : ¬ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).Convergent := by
  by_contra! h'
  have hbdd := Sequence.bounded_of_convergent h'
  exact example6118 hbdd

instance Sequence.inst_add : Add Sequence where
  add a b := {
    m := min a.m b.m
    seq n := a n + b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.add_eval {a b: Sequence} (n:ℤ) : (a + b) n = a n + b n := rfl

theorem Sequence.add_coe (a b: ℕ → ℝ) : (a:Sequence) + (b:Sequence) = (fun n ↦ a n + b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(a) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_add {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
  (a+b).TendsTo (L+M) := by
  intro ε hε
  specialize ha (ε / 2) (by positivity)
  specialize hb (ε / 2) (by positivity)
  obtain ⟨N₁, hNam, haclose⟩ := ha
  obtain ⟨N₂, hNbm, hbclose⟩ := hb
  use max (a+b).m (max N₁ N₂)
  --simp at hNam hNbm haclose hbclose ⊢
  constructor
  · grind
  · rw [Real.closeSeq_def] at haclose hbclose ⊢
    intro n hn
    simp at hn ⊢
    specialize haclose n (by grind)
    specialize hbclose n (by grind)
    simp at haclose hbclose
    rw [if_pos (by grind)] at haclose hbclose ⊢
    rw [Real.dist_eq] at haclose hbclose ⊢
    grind

theorem Sequence.lim_add {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
  (a + b).Convergent ∧ lim (a + b) = lim a + lim b := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (a + b).Convergent := by
    use lim a + lim b
    exact Sequence.tendsTo_add hlima hlimb
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_add hlima hlimb
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (a+b) hneq
    exact hunique ⟨hlimab, hlimab'⟩


instance Sequence.inst_mul : Mul Sequence where
  mul a b := {
    m := min a.m b.m
    seq n := a n * b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.mul_eval {a b: Sequence} (n:ℤ) : (a * b) n = a n * b n := rfl

theorem Sequence.mul_coe (a b: ℕ → ℝ) : (a:Sequence) * (b:Sequence) = (fun n ↦ a n * b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(b) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_mul {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a * b).TendsTo (L * M) := by
    have haconv : a.Convergent := by exact ⟨L, ha⟩
    have habdd := Sequence.bounded_of_convergent haconv
    obtain ⟨A, hApos, hAbd⟩ := habdd
    intro ε hε
    specialize ha (ε / (2 * (|M|+1))) (by positivity)
    specialize hb (ε / (2*(A+1))) (by positivity)
    obtain ⟨N₁, hNam, haclose⟩ := ha
    obtain ⟨N₂, hNbm, hbclose⟩ := hb
    use max (a*b).m (max N₁ N₂)
    constructor
    · grind
    · rw [Real.closeSeq_def] at haclose hbclose ⊢
      intro n hn
      simp at hn ⊢
      specialize haclose n (by grind)
      specialize hbclose n (by grind)
      simp at haclose hbclose
      rw [if_pos (by grind)] at haclose hbclose ⊢
      rw [Real.dist_eq] at haclose hbclose ⊢
      specialize hAbd n
      have habsle : |a.seq n| ≤ A + 1 := by linarith
      calc _ = |a.seq n * (b.seq n - M) + (M * (a.seq n - L))|     := by ring_nf!
           _ ≤ |a.seq n * (b.seq n - M)| + |M * (a.seq n - L)|     := by exact abs_add_le _ _
           _ = |a.seq n| * |(b.seq n - M)| + |M| * |(a.seq n - L)| := by rw [abs_mul _ _, abs_mul _ _]
           _ ≤ (A+1) * |(b.seq n - M)| + |M| * |(a.seq n - L)|     := by gcongr
           _ ≤ (A+1) * (ε / (2 * (A + 1))) + |M|     * |(a.seq n - L)| := by gcongr
           _ ≤ ε / 2 + |M| * |(a.seq n - L)|                           := by gcongr; field_simp; norm_num
           _ ≤ ε / 2 + (|M| + 1) * |(a.seq n - L)|                     := by grind
           _ ≤ ε / 2 + (|M| + 1) * (ε / (2 * (|M| + 1)))               := by gcongr
           _ ≤ ε / 2 + ε / 2                                           := by gcongr; field_simp; norm_num
           _ = ε                                                       := by norm_num

theorem Sequence.lim_mul {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a * b).Convergent ∧ lim (a * b) = lim a * lim b := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (a * b).Convergent := by
    use lim a * lim b
    exact Sequence.tendsTo_mul hlima hlimb
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_mul hlima hlimb
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (a*b) hneq
    exact hunique ⟨hlimab, hlimab'⟩


instance Sequence.inst_smul : SMul ℝ Sequence where
  smul c a := {
    m := a.m
    seq n := c * a n
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.smul_eval {a: Sequence} (c: ℝ) (n:ℤ) : (c • a) n = c * a n := rfl

theorem Sequence.smul_coe (c:ℝ) (a:ℕ → ℝ) : (c • (a:Sequence)) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Theorem 6.1.19(c) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_smul (c:ℝ) {a:Sequence} {L:ℝ} (ha: a.TendsTo L) :
    (c • a).TendsTo (c * L) := by
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul]
    intro ε hε
    use ((0:ℝ) • a).m
    constructor
    · grind
    · rw [Real.closeSeq_def]
      intro n hn
      simp
      linarith
  · push_neg at hc0
    intro ε hε
    obtain ⟨N, hNam, hnclose⟩ := ha (ε / |c|) (by positivity)
    simp at hNam
    use max N (c • a).m
    constructor
    · grind
    · rw [Real.closeSeq_def] at hnclose ⊢
      intro n hn
      specialize hnclose n (by grind)
      simp at hn hnclose ⊢
      rw [if_pos (by grind), Real.dist_eq] at hnclose ⊢
      rw [← mul_sub, abs_mul]
      field_simp at hnclose
      nlinarith

theorem Sequence.lim_smul (c:ℝ) {a:Sequence} (ha: a.Convergent) :
    (c • a).Convergent ∧ lim (c • a) = c * lim a := by
  have hlima := Sequence.lim_def ha
  have hconv : (c • a).Convergent := by
    use c * lim a
    exact Sequence.tendsTo_smul c hlima
  constructor
  · exact hconv
  · obtain hlim := Sequence.lim_def hconv
    obtain hlim' := Sequence.tendsTo_smul c hlima
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (c • a) hneq
    exact hunique ⟨hlim, hlim'⟩

instance Sequence.inst_sub : Sub Sequence where
  sub a b := {
    m := min a.m b.m
    seq n := a n - b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.sub_eval {a b: Sequence} (n:ℤ) : (a - b) n = a n - b n := rfl

theorem Sequence.sub_coe (a b: ℕ → ℝ) : (a:Sequence) - (b:Sequence) = (fun n ↦ a n - b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(d) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_sub {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (a - b).TendsTo (L - M) := by
  intro ε hε
  specialize ha (ε / 2) (by positivity)
  specialize hb (ε / 2) (by positivity)
  obtain ⟨N₁, hNam, haclose⟩ := ha
  obtain ⟨N₂, hNbm, hbclose⟩ := hb
  use max (a-b).m (max N₁ N₂)
  --simp at hNam hNbm haclose hbclose ⊢
  constructor
  · grind
  · rw [Real.closeSeq_def] at haclose hbclose ⊢
    intro n hn
    simp at hn ⊢
    specialize haclose n (by grind)
    specialize hbclose n (by grind)
    simp at haclose hbclose
    rw [if_pos (by grind)] at haclose hbclose ⊢
    rw [Real.dist_eq] at haclose hbclose ⊢
    grind

theorem Sequence.LIM_sub {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (a - b).Convergent ∧ lim (a - b) = lim a - lim b := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (a - b).Convergent := by
    use lim a - lim b
    exact Sequence.tendsTo_sub hlima hlimb
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_sub hlima hlimb
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (a-b) hneq
    exact hunique ⟨hlimab, hlimab'⟩


noncomputable instance Sequence.inst_inv : Inv Sequence where
  inv a := {
    m := a.m
    seq n := (a n)⁻¹
    vanish n hn := by simp [a.vanish n hn]
  }

@[simp]
theorem Sequence.inv_eval {a: Sequence} (n:ℤ) : (a⁻¹) n = (a n)⁻¹ := rfl

theorem Sequence.inv_coe (a: ℕ → ℝ) : (a:Sequence)⁻¹ = (fun n ↦ (a n)⁻¹) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(e) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_inv {a:Sequence} {L:ℝ} (ha: a.TendsTo L) (hnon: L ≠ 0) :
    (a⁻¹).TendsTo (L⁻¹) := by
  have hhalfL : ∃ N : ℤ, ∀ n ≥ N, |a n| ≥ |L| / 2 := by
    obtain ⟨N, hNam, hclose⟩ := ha (|L|/2) (by positivity)
    use N
    intro n hn
    specialize hclose n (by grind)
    simp at hclose
    rw [if_pos (by grind)] at hclose
    rw [Real.dist_eq] at hclose
    have reversetriangle := calc |L| = |L - a.seq n + a.seq n|   := by ring_nf
                                   _ ≤ |L - a.seq n| + |a.seq n| := by exact abs_add_le _ _
                                   _ = |a.seq n - L| + |a.seq n| := by rw [abs_sub_comm]
                                   _ ≤ |L|/2 + |a.seq n|         := by gcongr
    grind
  intro ε hε
  obtain ⟨N₁, hhalf⟩ := hhalfL
  obtain ⟨N₂, hNa, hclose⟩ := ha ((ε * |L| * |L|) / 2) (by positivity)
  use max (a⁻¹.m) (max N₁ N₂)
  rw [Real.closeSeq_def] at hclose ⊢
  constructor
  · grind
  · intro n hn
    simp at hn
    specialize hclose n (by grind)
    specialize hhalf n (by grind)
    have hpos : 0 < |a.seq n| := by grind
    field_simp at hhalf
    simp at hclose ⊢
    rw [if_pos (by grind)] at hclose ⊢
    rw [Real.dist_eq] at hclose ⊢
    calc |(a.seq n)⁻¹ - L⁻¹| = |(L - a.seq n) / (a.seq n * L)|         := by grind
                           _ = |(L - a.seq n)| / |(a.seq n * L)|       := by rw [abs_div]
                           _ = |(L - a.seq n)| / (|a.seq n| * |L|)     := by rw [abs_mul]
                           _ = 1/|a.seq n| * (1/|L| * |(L - a.seq n)|) := by field
                           _ ≤ 2/|L| * (1/|L| * |(L - a.seq n)|)       := by gcongr 1; field_simp; linarith
                           _ = 2/|L| * (1/|L| * |(a.seq n - L)|)       := by rw [abs_sub_comm]
                           _ ≤ 2/|L| * (1/|L| * ((ε * |L| * |L|) / 2)) := by gcongr
                           _ = ε                                       := by grind


theorem Sequence.lim_inv {a:Sequence} (ha: a.Convergent) (hnon: lim a ≠ 0) :
  (a⁻¹).Convergent ∧ lim (a⁻¹) = (lim a)⁻¹ := by
  have hlima := Sequence.lim_def ha
  have hconv : (a⁻¹).Convergent := by
    use (lim a)⁻¹
    exact Sequence.tendsTo_inv hlima hnon
  constructor
  · exact hconv
  · obtain hlim := Sequence.lim_def hconv
    obtain hlim' := Sequence.tendsTo_inv hlima hnon
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (a⁻¹) hneq
    exact hunique ⟨hlim, hlim'⟩

noncomputable instance Sequence.inst_div : Div Sequence where
  div a b := {
    m := min a.m b.m
    seq n := a n / b n
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.div_eval {a b: Sequence} (n:ℤ) : (a / b) n = a n / b n := rfl

theorem Sequence.div_coe (a b: ℕ → ℝ) : (a:Sequence) / (b:Sequence) = (fun n ↦ a n / b n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(f) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
theorem Sequence.tendsTo_div {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hnon: M ≠ 0) :
    (a / b).TendsTo (L / M) := by
  have hrw : (a / b) = a * (b⁻¹) := by
    ext n; rfl
    by_cases h: n ≥ 0
    · simp
      field_simp
    · simp
      field_simp
  rw [hrw]
  have hbinv := Sequence.tendsTo_inv hb hnon
  have hbmul := Sequence.tendsTo_mul ha hbinv
  exact hbmul

theorem Sequence.lim_div {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) (hnon: lim b ≠ 0) :
  (a / b).Convergent ∧ lim (a / b) = lim a / lim b := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (a / b).Convergent := by
    use lim a / lim b
    exact Sequence.tendsTo_div hlima hlimb hnon
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_div hlima hlimb hnon
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (a/b) hneq
    exact hunique ⟨hlimab, hlimab'⟩

instance Sequence.inst_max : Max Sequence where
  max a b := {
    m := min a.m b.m
    seq n := max (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.max_eval {a b: Sequence} (n:ℤ) : (a ⊔ b) n = (a n) ⊔ (b n) := rfl

theorem Sequence.max_coe (a b: ℕ → ℝ) : (a:Sequence) ⊔ (b:Sequence) = (fun n ↦ max (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(g) (limit laws).  The {name}`Sequence.TendsTo` version is more usable than the {name}`lim` version
    in applications. -/
lemma Sequence.lt_exists {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) (hmlt : L < M) :
  ∃ N : ℤ, ∀ n ≥ N, b n ≥ a n := by
  obtain ⟨N₁, hNam, hnaclose⟩ := ha ((M-L)/2) (by grind)
  obtain ⟨N₂, hNbm, hnbclose⟩ := hb ((M-L)/2) (by grind)
  use max N₁ N₂
  intro n hn
  simp at hn
  rw [Real.closeSeq_def] at hnaclose hnbclose
  specialize hnaclose n (by grind)
  specialize hnbclose n (by grind)
  rw [Real.dist_eq] at hnaclose hnbclose
  simp_all
  have ⟨halb, haub⟩ := abs_le.mp hnaclose
  have ⟨hblb, hbub⟩ := abs_le.mp hnbclose
  grind

theorem Sequence.tendsTo_max {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (max a b).TendsTo (max L M) := by
  wlog h : L ≤ M with H
  · push_neg at h
    have hlm : M ≤ L := by linarith
    have hreverse := H hb ha hlm
    have : (a ⊔ b) = (b ⊔ a) := by
      ext n
      · change min a.m b.m = min b.m a.m
        grind
      · simp
        grind
    rw [this]
    rw [max_comm]
    exact hreverse
  · rcases h.lt_or_eq with (hlt | heq)
    · intro ε hε
      obtain ⟨N₁, haltb⟩ := Sequence.lt_exists ha hb hlt
      obtain ⟨N₂, hBam, hbclose⟩ := hb ε hε
      use max (a ⊔ b).m (max N₁ N₂)
      constructor
      · simp
      · intro n hn
        simp at hn
        specialize haltb n (by grind)
        specialize hbclose n (by grind)
        simp_all
    · intro ε hε
      obtain ⟨N₁, hNam, hnaclose⟩ := ha ε hε
      obtain ⟨N₂, hNbm, hnbclose⟩ := hb ε hε
      use max (a ⊔ b).m (max N₁ N₂)
      constructor
      · simp
      · rw [Real.closeSeq_def] at hnaclose hnbclose ⊢
        intro n hn
        simp at hn
        specialize hnaclose n (by grind)
        specialize hnbclose n (by grind)
        rw [Real.dist_eq] at hnaclose hnbclose ⊢
        simp_all
        by_cases hgt : a.seq n ≥ b.seq n
        · rwa [max_eq_left hgt]
        · push_neg at hgt
          rwa [max_eq_right (by linarith)]


theorem Sequence.lim_max {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (max a b).Convergent ∧ lim (max a b) = max (lim a) (lim b) := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (max a b).Convergent := by
    use max (lim a) (lim b)
    exact Sequence.tendsTo_max hlima hlimb
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_max hlima hlimb
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (max a b) hneq
    exact hunique ⟨hlimab, hlimab'⟩

instance Sequence.inst_min : Min Sequence where
  min a b := {
    m := min a.m b.m
    seq n := min (a n) (b n)
    vanish n hn := by simp [a.vanish n (by grind), b.vanish n (by grind)]
  }

@[simp]
theorem Sequence.min_eval {a b: Sequence} (n:ℤ) : (a ⊓ b) n = (a n) ⊓ (b n) := rfl

theorem Sequence.min_coe (a b: ℕ → ℝ) : (a:Sequence) ⊓ (b:Sequence) = (fun n ↦ min (a n) (b n)) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h]

/-- Theorem 6.1.19(h) (limit laws) -/
theorem Sequence.tendsTo_min {a b:Sequence} {L M:ℝ} (ha: a.TendsTo L) (hb: b.TendsTo M) :
    (min a b).TendsTo (min L M) := by
  have hnegm : min a b = - (1:ℝ) • (max ((-1:ℝ) • a) ((-1:ℝ) • b)) := by
    ext n
    · change min a.m b.m = min a.m b.m
      rfl
    · simp_all
      conv =>
        lhs
        rw [← neg_neg (min _ _)]
      rw [max_neg_neg]
  have hlima := Sequence.tendsTo_smul (-1) ha; simp at hlima
  have hlimb := Sequence.tendsTo_smul (-1) hb; simp at hlimb
  have hlimab := Sequence.tendsTo_max hlima hlimb
  have hlimbnegab := Sequence.tendsTo_smul (-1) hlimab; simp at hlimbnegab
  rw [max_neg_neg] at hlimbnegab; simp at hlimbnegab
  rwa [hnegm]

theorem Sequence.lim_min {a b:Sequence} (ha: a.Convergent) (hb: b.Convergent) :
    (min a b).Convergent ∧ lim (min a b) = min (lim a) (lim b) := by
  have hlima := Sequence.lim_def ha
  have hlimb := Sequence.lim_def hb
  have habconv : (min a b).Convergent := by
    use min (lim a) (lim b)
    exact Sequence.tendsTo_min hlima hlimb
  constructor
  · exact habconv
  · obtain hlimab := Sequence.lim_def habconv
    obtain hlimab' := Sequence.tendsTo_min hlima hlimb
    by_contra! hneq
    have hunique := Sequence.tendsTo_unique (min a b) hneq
    exact hunique ⟨hlimab, hlimab'⟩

/-- Exercise 6.1.1 -/
theorem Sequence.mono_if {a: ℕ → ℝ} (ha: ∀ n, a (n+1) > a n) {n m:ℕ} (hnm: m > n) : a m > a n := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hnm
  subst hd
  induction' d with k ih
  · simp_all
  · simp_all
    calc a (n + (k + 1) + 1) = a ((n+k+1) + 1) := by ring_nf
                           _ > a (n+k+1)       := by exact ha (n+k+1)
                           _ > a n             := by exact ih

/-- Exercise 6.1.3 -/
theorem Sequence.tendsTo_of_from {a: Sequence} {c:ℝ} (m:ℤ) :
    a.TendsTo c ↔ (a.from m).TendsTo c := by
  constructor
  · intro htt ε hε
    obtain ⟨N, hNam, hclose⟩ := htt ε hε
    use max a.m (max m N)
    constructor
    · grind
    · rw [Real.closeSeq_def] at hclose ⊢
      intro n hn
      specialize hclose n (by grind)
      simp_all
      rwa [if_pos (by grind)]
  · intro hfromm ε hε
    obtain ⟨N, hNam, hclose⟩ := hfromm ε hε
    use max a.m (max m N)
    constructor
    · grind
    · rw [Real.closeSeq_def] at hclose ⊢
      intro n hn
      specialize hclose n (by grind)
      simp_all
      rw [if_pos (by grind)] at hclose
      exact hclose

/-- Exercise 6.1.4 -/
theorem Sequence.tendsTo_of_shift {a: Sequence} {c:ℝ} (k:ℕ) :
    a.TendsTo c ↔ (Sequence.mk' a.m (fun n : {n // n ≥ a.m} ↦ a (n+k))).TendsTo c := by
  constructor
  · intro htt ε hε
    obtain ⟨N, hNam, hclose⟩ := htt ε hε
    use max a.m N
    constructor
    · grind
    · intro n hn
      specialize hclose (n+k) (by grind)
      simp_all
      rw [if_pos (by grind)] at hclose ⊢
      exact hclose
  · intro htt ε hε
    obtain ⟨N, hNam, hclose⟩ := htt ε hε
    use max a.m (N+k)
    constructor
    · simp
    · intro n hn
      have : n - k ≥ N := by grind
      specialize hclose (n-k) (by grind)
      simp_all
      rw [if_pos (by grind)] at hclose
      exact hclose

/-- Exercise 6.1.7 -/
theorem Sequence.isBounded_of_rat (a: Chapter5.Sequence) :
    a.IsBounded ↔ (a:Sequence).IsBounded := by
  constructor
  · intro hrat
    obtain ⟨Bd, hBdpos, hBdd⟩ := hrat
    use Bd
    constructor
    · exact_mod_cast hBdpos
    · intro n
      specialize hBdd n
      simp
      exact_mod_cast hBdd
  · intro hreal
    obtain ⟨Bd, hBdpos, hBdd⟩ := hreal
    have : Bd < Bd+1 := by linarith
    obtain ⟨A, hAgt, hAlt⟩ := exists_rat_btwn this
    use A
    constructor
    · have : (A:ℝ) ≥ 0 := by grind
      exact_mod_cast this
    · intro n
      specialize hBdd n
      simp at hBdd
      have : |((a.seq n):ℝ)| ≤ (A:ℝ) := by grind
      exact_mod_cast this

/-- Exercise 6.1.9 -/
theorem Sequence.lim_div_fail :
    ∃ a b, a.Convergent
    ∧ b.Convergent
    ∧ lim b = 0
    ∧ ¬ ((a / b).Convergent ∧ lim (a / b) = lim a / lim b) := by
  --use ((fun _ => (1:ℝ)):Sequence) --((fun n => 1/n):Sequence)
  let α : ℕ → ℝ := fun _ => 1
  let β : ℕ → ℝ := fun n => (n+1)⁻¹
  use (α:Sequence)
  use (β:Sequence)
  refine ⟨?_, ?_, ?_, ?_⟩
  · use 1
    intro ε hε
    use (α:Sequence).m
    constructor
    · simp_all
    · intro n hn
      simp_all
      lift n to ℕ using (by omega)
      rw [Real.dist_eq]
      unfold α
      norm_num
      linarith
  · unfold β
    exact Sequence.lim_harmonic.1
  · unfold β
    exact Sequence.lim_harmonic.2
  · -- intro ⟨h1, _⟩
    intro ⟨hconv, hprime⟩
    have hbd := Sequence.bounded_of_convergent hconv
    obtain ⟨Bd, hBdpos, hBdd⟩ := hbd
    obtain ⟨N, hN⟩ := exists_nat_gt Bd
    specialize hBdd N
    simp at hBdd
    unfold α β at hBdd
    field_simp at hBdd
    grind

theorem Chapter5.Sequence.IsCauchy_iff (a:Chapter5.Sequence) :
    a.IsCauchy ↔ ∀ ε > (0:ℝ), ∃ N ≥ a.n₀, ∀ n ≥ N, ∀ m ≥ N, |a n - a m| ≤ ε := by
  constructor
  · intro hcauchy
    rw [Chapter5.Sequence.isCauchy_def] at hcauchy
    intro ε₀ hε₀
    obtain ⟨ε, hεpos, hεlt⟩ := exists_rat_btwn hε₀
    obtain ⟨N, hN, hsteady⟩ := hcauchy ε (by exact_mod_cast hεpos)
    use N
    constructor
    · grind
    · intro n hn m hm
      specialize hsteady n (by grind) m (by grind)
      simp at hsteady
      rw [if_pos (by grind), if_pos (by grind)] at hsteady
      change |a.seq n - a.seq m| ≤ ε at hsteady
      have : (((|a.seq n - a.seq m|):ℚ):ℝ) ≤ (ε:ℝ) := by exact_mod_cast hsteady
      linarith
  · rw [Chapter5.Sequence.isCauchy_def]
    intro hevery ε hε
    obtain ⟨N, hNam, habs⟩ := hevery ε (by exact_mod_cast hε)
    use N
    constructor
    · grind
    · intro n hn m hm
      -- rw [Real.close_def]
      simp
      rw [if_pos (by grind), if_pos (by grind)]
      change |a.seq n - a.seq m| ≤ ε
      specialize habs n (by grind) m (by grind)
      exact_mod_cast habs
end Chapter6

-- additional definitions for exercise 6.1.10
abbrev Real.SeqCloseSeq (ε: ℝ) (a b: Chapter5.Sequence) : Prop :=
  ∀ n, n ≥ a.n₀ → n ≥ b.n₀ → ε.Close (a n) (b n)

abbrev Real.SeqEventuallyClose (ε: ℝ) (a b: Chapter5.Sequence): Prop :=
  ∃ N, ε.SeqCloseSeq (a.from N) (b.from N)

-- extended definition of rational sequences equivalence but with positive real ε
abbrev Chapter5.Sequence.RatEquiv (a b: ℕ → ℚ) : Prop :=
  ∀ (ε:ℝ), ε > 0 → ε.SeqEventuallyClose (a:Chapter5.Sequence) (b:Chapter5.Sequence)

namespace Chapter6
/-- Exercise 6.1.10 -/
theorem Chapter5.Sequence.equiv_rat (a b: ℕ → ℚ) :
  Chapter5.Sequence.Equiv a b ↔ Chapter5.Sequence.RatEquiv a b := by
  constructor
  · intro hequiv
    rw [Chapter5.Sequence.equiv_iff] at hequiv
    rw [Chapter5.Sequence.RatEquiv]
    intro ε₀ hε₀
    obtain ⟨ε, hεpos, hε⟩ := exists_rat_btwn hε₀
    obtain ⟨N, hN⟩ := hequiv ε (by exact_mod_cast hεpos)
    use N
    rw [Real.SeqCloseSeq]
    intro n ha hb
    simp_all
    rw [if_pos (by grind), if_pos (by grind)]
    lift n to ℕ using (by omega)
    simp_all
    specialize hN n (by linarith)
    rw [Rat.dist_eq]
    rify at hN
    linarith
  · intro hrateq ε hε
    obtain ⟨N, hN⟩ := hrateq ε (by exact_mod_cast hε)
    use N
    rw [Real.SeqCloseSeq] at hN
    intro n ha hb
    specialize hN n (by omega) (by omega)
    rw [Real.Close, Real.dist_eq] at hN
    rw [Rat.Close]
    simp_all
    lift n to ℕ using (by omega)
    simp_all
    exact_mod_cast hN

end Chapter6
