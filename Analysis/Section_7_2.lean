import Mathlib.Tactic
import Mathlib.Algebra.Field.Power
import Mathlib.Analysis.PSeries

/-!
# Analysis I, Section 7.2: Infinite series

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Formal series and their limits.
- Absolute convergence; basic series laws.

-/

namespace Chapter7

open BigOperators

/--
  Definition 7.2.1 (Formal infinite series). This is similar to Chapter 6 sequence, but is
  manipulated differently. As with Chapter 5, we will start series from 0 by default.
-/
@[ext]
structure Series where
  m : ℤ
  seq : ℤ → ℝ
  vanish : ∀ n < m, seq n = 0

/-- Functions from ℕ to ℝ can be thought of as series. -/
instance Series.instCoe : Coe (ℕ → ℝ) Series where
  coe := fun a ↦ {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by grind
  }

@[simp]
theorem Series.eval_coe (a: ℕ → ℝ) (n: ℕ) : (a: Series).seq n = a n := by simp

abbrev Series.mk' {m:ℤ} (a: { n // n ≥ m } → ℝ) : Series where
  m := m
  seq n := if h : n ≥ m then a ⟨n, h⟩ else 0
  vanish := by grind

theorem Series.eval_mk' {m:ℤ} (a : { n // n ≥ m } → ℝ) {n : ℤ} (h:n ≥ m) :
    (Series.mk' a).seq n = a ⟨ n, h ⟩ := by simp [h]

/-- Definition 7.2.2 (Convergence of series) -/
noncomputable abbrev Series.partial (s : Series) (N:ℤ) : ℝ := ∑ n ∈ Finset.Icc s.m N, s.seq n

theorem Series.partial_succ (s : Series) {N:ℤ} (h: N ≥ s.m-1) : s.partial (N+1) = s.partial N + s.seq (N+1) := by
  unfold Series.partial
  rw [add_comm (s.partial N) _]
  convert Finset.sum_insert (show N+1 ∉ Finset.Icc s.m N by simp)
  symm; apply Finset.insert_Icc_right_eq_Icc_add_one; linarith

theorem Series.partial_of_lt {s : Series} {N:ℤ} (h: N < s.m) : s.partial N = 0 := by
  unfold Series.partial
  rw [Finset.sum_eq_zero]
  intro n hn; simp at hn; grind

abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)

abbrev Series.converges (s : Series) : Prop := ∃ L, s.convergesTo L

abbrev Series.diverges (s : Series) : Prop := ¬s.converges

open Classical in
noncomputable abbrev Series.sum (s : Series) : ℝ := if h : s.converges then h.choose else 0

theorem Series.converges_of_convergesTo {s : Series} {L:ℝ} (h: s.convergesTo L) :
    s.converges := by use L

/-- Remark 7.2.3 -/
theorem Series.sum_of_converges {s : Series} {L:ℝ} (h: s.convergesTo L) : s.sum = L := by
  simp [sum, converges_of_convergesTo h]
  exact tendsto_nhds_unique ((converges_of_convergesTo h).choose_spec) h

theorem Series.convergesTo_uniq {s : Series} {L L':ℝ} (h: s.convergesTo L) (h': s.convergesTo L') :
    L = L' := tendsto_nhds_unique h h'

theorem Series.convergesTo_sum {s : Series} (h: s.converges) : s.convergesTo s.sum := by
  simp [sum, h]; exact h.choose_spec

/-- Example 7.2.4 -/
noncomputable abbrev Series.example_7_2_4 := mk' (m := 1) (fun n ↦ (2:ℝ)^(-n:ℤ))

theorem Series.example_7_2_4a {N:ℤ} (hN: N ≥ 1) : example_7_2_4.partial N = 1 - (2:ℝ)^(-N) := by
  simp
  -- rw [Finset.sum_ite_of_true (by grind)]
  induction' N, hN using Int.le_induction with n hn ih
  · unfold example_7_2_4 Series.partial
    simp; norm_num
  · rw [example_7_2_4.partial_succ (by simp; grind), ih]
    unfold example_7_2_4; simp
    rw [if_pos (by linarith)]
    rw [sub_add_eq_add_sub, add_sub_assoc]
    congr 1
    field_simp
    rw [sub_mul]
    simp
    conv_lhs => left; rw [← zpow_add₀ (by grind), ← zpow_add₀ (by grind)]; simp
    rw [zpow_add₀ (by grind), zpow_one]
    grind

theorem Series.example_7_2_4b : example_7_2_4.convergesTo 1 := by
  unfold Series.convergesTo
  -- cool use of Filter.Tendsto.congr'
  apply Filter.Tendsto.congr' (f₁:=fun N => 1 - (2:ℝ)^(-N)) (f₂:=example_7_2_4.partial)
  -- first condition: eventually, the functions agree.
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (Series.example_7_2_4a hn).symm
  -- second condition: the replacing function has the same behavior as the replaced.
  · have h1 : Filter.Tendsto (fun (N:ℤ) => (1:ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have h2 : Filter.Tendsto (fun (N:ℤ) => (2:ℝ)^(-N)) Filter.atTop (nhds 0) := by
      rw [Metric.tendsto_atTop]
      simp_rw [Real.dist_eq]
      intro ε hε
      choose N hN using exists_int_gt (1/ε)
      field_simp at hN
      use max 0 N; intro n hn
      simp at hn
      lift n to ℕ using (by omega)
      simp
      field_simp
      ring_nf at hN ⊢
      have hlt := Nat.lt_pow_self (a:=2) (n:=n) (by grind)
      calc 1 < ε * (N:ℤ)  := by exact hN
            _≤ ε * n      := by gcongr; exact_mod_cast hn.2
            _< ε * (2 ^n) := by gcongr; exact_mod_cast hlt
    simpa using h1.sub h2

theorem Series.example_7_2_4c : example_7_2_4.sum = 1 := by
  apply Series.sum_of_converges
  exact Series.example_7_2_4b

noncomputable abbrev Series.example_7_2_4' := mk' (m := 1) (fun n ↦ (2:ℝ)^(n:ℤ))

theorem Series.example_7_2_4'a {N:ℤ} (hN: N ≥ 1) : example_7_2_4'.partial N = (2:ℝ)^(N+1) - 2 := by
  induction' N, hN using Int.le_induction with k hk ih
  · unfold example_7_2_4' Series.partial
    simp; norm_num
  · rw [example_7_2_4'.partial_succ (by simp; grind), ih]
    simp; rw [if_pos (by grind)]
    conv_lhs => rw [sub_add_eq_add_sub]
    norm_num
    rw [← two_mul, mul_comm, ← zpow_add_one₀ (by norm_num)]

private lemma Series.example_7_2_4'age {N:ℤ}  (hN: N ≥ 1) : example_7_2_4'.partial N ≥ 1 := by
  induction' N, hN using Int.le_induction with k hk ih
  · unfold example_7_2_4' Series.partial; simp
  · rw [example_7_2_4'.partial_succ (by simp; grind)]
    simp; rw [if_pos (by grind)]
    suffices (2:ℝ) ^ (k + 1) ≥ 0 by linarith
    positivity

theorem Series.example_7_2_4'b : example_7_2_4'.diverges := by
  intro ⟨L, hL⟩
  unfold Series.convergesTo at hL
  rw [Metric.tendsto_atTop] at hL
  contrapose! hL
  simp_rw [Real.dist_eq]
  use 1; constructor
  · grind
  · intro N
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (x:=(L+3)) (y:=(2:ℝ)) (by norm_num)
    use max 1 (max N M); constructor
    · grind
    · rw [le_abs]
      left
      rw [Series.example_7_2_4'a (by grind)]
      suffices L + 3 < 2 ^ (max 1 (max N (M:ℤ)) + 1) by linarith
      calc  L + 3 < 2 ^ M      := by exact hM
                 _= 2 ^ (M:ℤ)  := by apply zpow_natCast
                 _< 2 ^ (max 1 (max N ↑M) + 1) := by gcongr <;> grind

/-- Proposition 7.2.5 / Exercise 7.2.2 -/
-- copied over from prev exercise
theorem sum_of_empty {n m:ℤ} (h: n < m) (a: ℤ → ℝ) : ∑ i ∈ Finset.Icc m n, a i = 0 := by
  rw [Finset.sum_eq_zero]; intro _; rw [Finset.mem_Icc]; grind

theorem sum_of_nonempty {n m:ℤ} (h: n ≥ m-1) (a: ℤ → ℝ) :
    ∑ i ∈ Finset.Icc m (n+1), a i = ∑ i ∈ Finset.Icc m n, a i + a (n+1) := by
  rw [add_comm _ (a (n+1))]
  convert Finset.sum_insert _
  . ext; simp; omega
  . infer_instance
  simp

lemma partial_sum_difference {n₁ n₂:ℤ}  {s:Series} (hn₁ : n₁ ≥ s.m) (hn₂ : n₂ ≥ s.m) (h : n₂ ≥ n₁) :
  s.partial n₂ - s.partial n₁ = ∑ n ∈ Finset.Icc (n₁+1) n₂, s.seq n := by
  induction' n₂, h using Int.le_induction with k hk ih
  · simp_all
  · have : k ≥ s.m := by grind
    specialize ih this
    rw [s.partial_succ (by grind), ← sub_add_eq_add_sub, ih]
    symm
    apply sum_of_nonempty (by grind)

lemma partial_sum_difference' {n₁ n₂:ℤ}  {s:Series} (hn₁ : n₁ ≥ s.m) (hn₂ : n₂ ≥ s.m) (h : n₂ ≤ n₁) :
  s.partial n₂ - s.partial n₁ = -(∑ n ∈ Finset.Icc (n₂+1) n₁, s.seq n) := by
  induction' n₁, h using Int.le_induction with k hk ih
  · simp_all
  · have : k ≥ s.m := by grind
    specialize ih this
    rw [s.partial_succ (by grind), sub_add_eq_sub_sub, ih, ← neg_add']
    apply neg_inj.mpr
    symm
    apply sum_of_nonempty (by grind)

theorem Series.converges_iff_tail_decay (s:Series) :
    s.converges ↔ ∀ ε > 0, ∃ N ≥ s.m, ∀ p ≥ N, ∀ q ≥ N, |∑ n ∈ Finset.Icc p q, s.seq n| ≤ ε := by
  constructor
  · intro hconv
    unfold Series.converges Series.convergesTo at hconv
    obtain ⟨L, hL⟩ := hconv
    have hcauchy := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at hcauchy; simp_rw [Real.dist_eq] at hcauchy
    intro ε hε
    choose N hN using hcauchy ε hε
    use max (s.m+1) (N+1); constructor
    · grind
    · intro n hn m hm; simp at hn hm
      by_cases! hmn : m < n
      · rw [sum_of_empty (by grind)]
        grind
      · specialize hN m (by grind) (n-1) (by grind)
        rw [partial_sum_difference (by grind) (by grind) (by grind)] at hN
        simp at hN
        linarith
  · intro hevery
    unfold Series.converges Series.convergesTo
    have : CauchySeq s.partial := by
      rw [Metric.cauchySeq_iff]; simp_rw [Real.dist_eq]
      intro ε hε
      choose N hN using hevery (ε/2) (by positivity)
      use N; intro n hn m hm
      by_cases! hmn : m < n
      · rw [partial_sum_difference (by grind) (by grind) (by grind)]
        grind
      · rw [partial_sum_difference' (by grind) (by grind) (by grind)]
        grind
    exact cauchy_iff_exists_le_nhds.mp this


/-- Corollary 7.2.6 (Zero test) / Exercise 7.2.3 -/
theorem Series.decay_of_converges {s:Series} (h: s.converges) :
    Filter.atTop.Tendsto s.seq (nhds 0) := by
  rw [s.converges_iff_tail_decay] at h
  rw [Metric.tendsto_atTop]; simp_rw [Real.dist_eq, sub_zero]
  intro ε hε
  choose N  hNsm hN using h (ε/2) (by positivity)
  use N; intro n hn
  specialize hN n hn n hn
  rw [Finset.Icc_self, Finset.sum_singleton] at hN
  grind

theorem Series.diverges_of_nodecay {s:Series} (h: ¬ Filter.atTop.Tendsto s.seq (nhds 0)) :
    s.diverges := by
  intro hdiv
  contrapose h
  exact Series.decay_of_converges hdiv

/-- Example 7.2.7 -/
theorem Series.example_7_2_7 : ((fun _:ℕ ↦ (1:ℝ)):Series).diverges := by
  apply diverges_of_nodecay
  rw [Metric.tendsto_atTop]
  push_neg
  use 0.5; constructor
  · norm_num
  · intro n
    use max 0 (2*n); constructor
    · grind
    · simp_all; norm_num

theorem Series.example_7_2_7' : ((fun n:ℕ ↦ (-1:ℝ)^n):Series).diverges := by
  apply diverges_of_nodecay
  rw [Metric.tendsto_atTop]
  push_neg
  use 0.5; constructor
  · norm_num
  · intro n
    use max 0 (2*n); constructor
    · grind
    · simp_all; norm_num

/-- Definition 7.2.8 (Absolute convergence) -/
abbrev Series.abs (s:Series) : Series := mk' (m:=s.m) (fun n ↦ |s.seq n|)

abbrev Series.absConverges (s:Series) : Prop := s.abs.converges

abbrev Series.condConverges (s:Series) : Prop := s.converges ∧ ¬ s.absConverges

/-- Proposition 7.2.9 (Absolute convergence test) / Exercise 7.2.4 -/
theorem Series.converges_of_absConverges {s:Series} (h : s.absConverges) : s.converges := by
  unfold Series.absConverges Series.abs at h
  rw [Series.converges_iff_tail_decay] at h ⊢
  intro ε hε
  choose N hNm hN using h ε hε
  use N
  constructor
  · grind
  · intro p hp q hq
    specialize hN p hp q hq
    simp at hN
    rw [Finset.sum_ite_of_true (by grind)] at hN
    have habs := Finset.abs_sum_le_sum_abs (s:=Finset.Icc p q) (f:=s.seq)
    grind

theorem Series.abs_le {s:Series} (h : s.absConverges) : |s.sum| ≤ s.abs.sum := by
  have hconv := converges_of_absConverges h
  -- abbrev Series.convergesTo (s : Series) (L:ℝ) : Prop := Filter.atTop.Tendsto (s.partial) (nhds L)
  have h' : Filter.atTop.Tendsto (s.abs.partial) (nhds s.abs.sum) := by
    have := s.abs.convergesTo_sum h
    unfold convergesTo at this; exact this
  have hconv' : Filter.atTop.Tendsto (s.partial) (nhds s.sum) := by
    have := s.convergesTo_sum hconv
    unfold convergesTo at this; exact this
  apply le_of_tendsto_of_tendsto hconv'.abs h'
  filter_upwards
  intro n
  unfold Series.partial Series.abs
  simp; rw [Finset.sum_ite_of_true (by grind)]
  apply Finset.abs_sum_le_sum_abs


/-- Proposition 7.2.12 (Alternating series test) -/
theorem Series.converges_of_alternating {m:ℤ} {a: { n // n ≥ m} → ℝ} (ha: ∀ n, a n ≥ 0)
  (ha': Antitone a) :
    ((mk' (fun n ↦ (-1)^(n:ℤ) * a n)).converges ↔ Filter.atTop.Tendsto a (nhds 0)) := by
  -- This proof is written to follow the structure of the original text.
  constructor
  . intro h; apply decay_of_converges at h
    rw [tendsto_iff_dist_tendsto_zero] at h ⊢
    rw [←Filter.tendsto_comp_val_Ici_atTop (a := m)] at h
    refine h.congr (fun n => ?_)
    simp [n.property]
  intro h
  unfold converges convergesTo
  set b := mk' fun n ↦ (-1) ^ (n:ℤ) * a n
  set S := b.partial
  have claim0 {N:ℤ} (hN: N ≥ m) : S (N+1) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ := by
    convert b.partial_succ ?_; simp [b, show N+1 ≥ m by grind]; linarith
  have claim1 {N:ℤ} (hN: N ≥ m) : S (N+2) = S N + (-1)^(N+1) * (a ⟨ N+1, by grind ⟩ - a ⟨ N+2, by grind ⟩) := calc
      S (N+2) = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1)^(N+2) * a ⟨ N+2, by grind ⟩ := by
        simp_rw [←claim0 hN, show N+2=N+1+1 by abel]; apply claim0; linarith
      _ = S N + (-1)^(N+1) * a ⟨ N+1, by grind ⟩ + (-1) * (-1)^(N+1) * a ⟨ N+2, by grind ⟩ := by
        congr; rw [←zpow_one_add₀] <;> grind
      _ = _ := by ring
  have claim2 {N:ℤ} (hN: N ≥ m) (h': Odd N) : S (N+2) ≥ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have claim3 {N:ℤ} (hN: N ≥ m) (h': Even N) : S (N+2) ≤ S N := by
    simp [claim1 hN, h'.add_one.neg_one_zpow]; apply ha'; simp
  have why1 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k) ≤ S N := by
    induction' k with j ih
    · simp
    · push_cast [mul_add]; rw [← add_assoc]
      have := claim3 (N:=N+2*(j:ℤ)) (by grind) (by grind)
      linarith
  have why2 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≥ S N - a ⟨ N+1, by grind ⟩ := by
    induction' k with j ih
    · simp
      set x := a ⟨N+1, _⟩ with hxdef
      have : S (N+1) - S N = b.seq (N+1) := by
        unfold S
        rw [b.partial_succ (N:=N) (by simp_all; grind)]
        linarith
      suffices -x ≤ S (N+1) - S N by linarith
      rw [this]
      unfold x b; simp
      rw [dif_pos (by omega)]
      have hminusone : (-1:ℝ) ^ (N + 1) = (-1:ℝ) := by exact Odd.neg_one_zpow h'.add_one
      rw [hminusone]
      simp
    · push_cast [mul_add]
      rw [add_assoc, add_right_comm, ← add_assoc, ← add_assoc]
      have h2j : Even (2 * (j:ℤ)) := by apply even_two_mul
      have hN2j : Even (N+2*(j:ℤ)) := by exact Even.add h' h2j
      have := claim2 (N:=N+2*(j:ℤ)+1) (by grind) (by exact hN2j.add_one)
      linarith
  have why3 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S (N+2*k+1) ≤ S (N+2*k) := by
    conv_lhs =>
      unfold S
      rw [b.partial_succ (by simp_all; grind)]
    suffices b.seq (N + 2 * (k:ℤ) + 1) ≤ 0 by linarith
    unfold b; simp; rw [dif_pos (by omega)]
    specialize ha ⟨(N + 2 * (k:ℤ) + 1) , by grind⟩
    have hodd : Odd (N + 2 * (k:ℤ) + 1) := by exact (Even.add h' (by apply even_two_mul)).add_one
    rw [Odd.neg_one_zpow hodd]
    linarith
  have claim4 {N:ℤ} (hN: N ≥ m) (h': Even N) (k:ℕ) : S N -
 a ⟨ N+1, by grind ⟩ ≤ S (N + 2*k + 1) ∧ S (N + 2*k + 1) ≤ S (N + 2*k) ∧ S (N + 2*k) ≤ S N := ⟨ ge_iff_le.mp (why2 hN h' k), why3 hN h' k, why1 hN h' k ⟩
  have why4 {N n:ℤ} (hN: N ≥ m) (h': Even N) (hn: n ≥ N) : S N - a ⟨ N+1, by grind ⟩ ≤ S n ∧ S n ≤ S N := by
    specialize claim4 hN h'
    obtain ⟨d, hd⟩ := Int.le.dest hn
    rcases d.even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [← two_mul] at hk; zify at hk
      obtain ⟨h1, h2, h3⟩ := claim4 k
      grind
    · zify at hk
      obtain ⟨h1, h2, h3⟩ := claim4 k
      grind
  have why5 {ε:ℝ} (hε: ε > 0) : ∃ N, ∀ n ≥ N, ∀ m ≥ N, |S n - S m| ≤ ε := by
    have hnon : Nonempty { n // n ≥ m } := by use m+1; grind
    rw [Metric.tendsto_atTop] at h
    simp_rw [Real.dist_eq, sub_zero] at h
    choose N hN using h (ε/2) (by positivity)
    set N' := 2 * max 0 (max m N)
    use N'
    have hN'm : N' ≥ m := by
      unfold N'
      have : max 0 (max m N) ≥ 0 := by positivity
      have : max 0 (max m N) ≥ m := by grind
      grind
    have hN'N : N' ≥ N := by
      unfold N'
      have : max 0 (max m N) ≥ 0 := by positivity
      have : max 0 (max m N) ≥ N := by grind
      grind
    intro n hn k hk
    have why41 := why4 (N:=N') hN'm (by grind) hn
    have why42 := why4 (N:=N') hN'm (by grind) hk
    specialize hN ⟨N'+1, by grind⟩ (by change N' + 1 ≥ N; grind)
    set α := a ⟨N'+1, _⟩
    have why41' : |S n - S N'| ≤ |α| := by
      rw [abs_sub_comm]
      apply abs_le_abs
      · grind
      · grind
    have why42' : |S k - S N'| ≤ |α| := by
      rw [abs_sub_comm]
      apply abs_le_abs
      · grind
      · grind
    calc |S n - S k| = |(S n - S N') + (S N' - S k)| := by ring_nf
                   _ ≤ |S n - S N'| + |S N' - S k|   := by apply abs_add_le
                   _ = |S n - S N'| + |S k - S N'|   := by congr 1; apply abs_sub_comm
                   _ ≤ |α| + |α|                     := by linarith
                   _ ≤ (ε / 2) + (ε / 2)             := by linarith
                   _ = ε                             := by norm_num
  have : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε; choose N hN using why5 (half_pos hε); use N
    intro n hn; rw [Real.dist_eq]; linarith [hN n hn N (by simp)]
  exact cauchySeq_tendsto_of_complete this

/-- Example 7.2.13 -/
noncomputable abbrev Series.example_7_2_13 : Series := (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) / (n:ℤ)))

private lemma Series.example_7_2_13_alt : example_7_2_13 = (mk' (m:=1) (fun n ↦ (-1:ℝ)^(n:ℤ) *  (1 / n))) := by
  unfold example_7_2_13
  congr
  ext n
  field_simp

theorem Series.example_7_2_13a : example_7_2_13.converges := by
  set a : {n:ℤ // n ≥ 1} → ℝ := fun n => 1 / n
  have ha : ∀ n, a n ≥ 0 := by
    intro n
    unfold a
    simp; grind
  have ha' : Antitone a := by
    intro n k hle
    unfold a
    apply one_div_le_one_div_of_le
    · have := n.property
      norm_cast
    · norm_cast
  have htop : Filter.atTop.Tendsto a (nhds 0) := by
    have hinv := @tendsto_inv_atTop_zero ℝ _ _ _ _ _
    unfold a
    simp only [one_div]
    refine hinv.comp ?_
    apply Filter.Tendsto.comp
    · exact tendsto_intCast_atTop_atTop
    · have hnonempty : Nonempty { n:ℤ // n ≥ 1 } := by use (1:ℤ)
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      use ⟨max b 1, by grind⟩
      intro ⟨n, hn⟩ hge
      simp_all
  have halternatingseries := (Series.converges_of_alternating ha ha').mpr htop
  unfold a at halternatingseries
  rwa [← Series.example_7_2_13_alt] at halternatingseries

private lemma Series.example_7_2_13_abs_alt : example_7_2_13.abs = (mk' (m:=1) (fun n ↦ (1 / n))) := by
  unfold example_7_2_13
  ext n; simp
  unfold Series.abs; simp
  split_ifs
  · rw [div_eq_mul_inv, abs_mul]
    simp; grind
  · rfl

theorem Series.example_7_2_13b : ¬ example_7_2_13.absConverges := by
  unfold Series.absConverges
  rw [Series.example_7_2_13_abs_alt]
  unfold Series.converges Series.convergesTo
  unfold Series.partial; simp
  intro x hx
  have hx' : Filter.Tendsto (fun (N:ℤ) ↦ ∑ x ∈ Finset.Icc 1 N,  (↑x)⁻¹) Filter.atTop (nhds x) := by
    convert hx using 2 with N
    rw [Finset.sum_ite_of_true (by grind)]
  have : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1) = ∑ x ∈ Finset.Icc (1:ℤ) n, (x:ℝ)⁻¹ := by
    intro n
    induction' n with k ih
    · simp
    · rw [Finset.sum_range_succ, ih]
      rw [← inv_eq_one_div]
      conv_rhs => rw [Nat.cast_succ, sum_of_nonempty (by grind)]
      congr
      norm_cast
  have hx'' := hx'.comp tendsto_natCast_atTop_atTop
  have hx''' : Filter.Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range n, (1:ℝ) / (i + 1)) Filter.atTop (nhds x) :=
    hx''.congr (fun n => (this n).symm)
  have htop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact not_tendsto_nhds_of_tendsto_atTop htop x hx'''


theorem Series.example_7_2_13c :  example_7_2_13.condConverges := by
  exact ⟨example_7_2_13a, example_7_2_13b⟩

instance Series.inst_add : Add Series where
  add a b := {
    m := min a.m b.m
    seq n := a.seq n + b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.add_coe (a b: ℕ → ℝ) : (a:Series) + (b:Series) = (fun n ↦ a n + b n) := by
  ext n; rfl
  change (a:Series).seq n + (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

/-- Proposition 7.2.14 (a) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.add {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s + t).convergesTo (L + M) := by
  unfold Series.convergesTo Series.partial at hs ht ⊢
  have hst := hs.add ht
  convert hst using 2 with n
  change ∑ n ∈ Finset.Icc (min s.m t.m) n, (s.seq n + t.seq n) = ∑ n ∈ Finset.Icc s.m n, s.seq n + ∑ n ∈ Finset.Icc t.m n, t.seq n
  rw [Finset.sum_add_distrib]
  congr 1
  · symm; apply Finset.sum_subset
    · intro x hx; simp; grind
    · intro x hx hx'; simp at hx hx'
      have hltm : x < s.m := by grind
      exact s.vanish x hltm
  · symm; apply Finset.sum_subset
    · intro x hx; simp; grind
    · intro x hx hx'; simp at hx hx'
      have hltm : x < t.m := by grind
      exact t.vanish x hltm

#check Finset.sum_subset

theorem Series.add {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s + t).converges ∧ (s+t).sum = s.sum + t.sum := by
  have hssum := Series.convergesTo_sum hs
  have htsum := Series.convergesTo_sum ht
  have hadd := Series.convergesTo.add hssum htsum
  constructor
  · use s.sum + t.sum
  · exact sum_of_converges hadd

instance Series.inst.smul : SMul ℝ Series where
  smul c s := {
    m := s.m
    seq n := if n ≥ s.m then c * s.seq n else 0
    vanish := by grind
  }

theorem Series.smul_coe (a: ℕ → ℝ) (c: ℝ) : (c • a:Series) = (fun n ↦ c * a n) := by
  ext n; rfl
  by_cases h:n ≥ 0 <;> simp [h, HSMul.hSMul, SMul.smul]

/-- Proposition 7.2.14 (b) (Series laws) / Exercise 7.2.5.  The {name}`convergesTo` form can be more convenient for applications. -/
theorem Series.convergesTo.smul {s:Series} {L c: ℝ} (hs: s.convergesTo L) :
    (c • s).convergesTo (c * L) := by
  unfold Series.convergesTo Series.partial at hs ⊢
  have hsmul := hs.const_mul c
  convert hsmul using 2 with n
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · congr 1
  · intro x hx
    change (if x ≥ s.m then c * s.seq x else 0) = c * s.seq x
    rw [if_pos (by grind)]

theorem Series.smul {c:ℝ} {s:Series} (hs: s.converges) :
    (c • s).converges ∧ (c • s).sum = c * s.sum := by
  have hsum := Series.convergesTo_sum hs
  have hsmul := Series.convergesTo.smul (c:=c) hsum
  constructor
  · use c * s.sum
  · exact sum_of_converges hsmul

/-- The corresponding API for subtraction was not in the textbook, but is useful in later sections, so is included here. -/
instance Series.inst_sub : Sub Series where
  sub a b := {
    m := min a.m b.m
    seq n := a.seq n - b.seq n
    vanish n hn := by simp [a.vanish n (by omega), b.vanish n (by omega)]
  }

theorem Series.sub_coe (a b: ℕ → ℝ) : (a:Series) - (b:Series) = (fun n ↦ a n - b n) := by
  ext n; rfl
  change (a:Series).seq n - (b:Series).seq n = _
  by_cases h:n ≥ 0 <;> simp [h]

theorem Series.convergesTo.sub {s t:Series} {L M: ℝ} (hs: s.convergesTo L) (ht: t.convergesTo M) :
    (s - t).convergesTo (L - M) := by
  unfold Series.convergesTo Series.partial at hs ht ⊢
  have hst := hs.sub ht
  convert hst using 2 with n
  change ∑ n ∈ Finset.Icc (min s.m t.m) n, (s.seq n - t.seq n) = ∑ n ∈ Finset.Icc s.m n, s.seq n - ∑ n ∈ Finset.Icc t.m n, t.seq n
  rw [Finset.sum_sub_distrib]
  congr 1
  · symm; apply Finset.sum_subset
    · intro x hx; simp; grind
    · intro x hx hx'; simp at hx hx'
      have hltm : x < s.m := by grind
      exact s.vanish x hltm
  · symm; apply Finset.sum_subset
    · intro x hx; simp; grind
    · intro x hx hx'; simp at hx hx'
      have hltm : x < t.m := by grind
      exact t.vanish x hltm

theorem Series.sub {s t:Series} (hs: s.converges) (ht: t.converges) :
    (s - t).converges ∧ (s-t).sum = s.sum - t.sum := by
  have hssum := Series.convergesTo_sum hs
  have htsum := Series.convergesTo_sum ht
  have hsub := Series.convergesTo.sub hssum htsum
  constructor
  · use s.sum - t.sum
  · exact sum_of_converges hsub

abbrev Series.from (s:Series) (m₁:ℤ) : Series := mk' (m := max s.m m₁) (fun n ↦ s.seq (n:ℤ))

/-- Proposition 7.2.14 (c) (Series laws) / Exercise 7.2.5 -/
theorem Series.converges_from (s:Series) (k:ℕ) : s.converges ↔ (s.from (s.m+k)).converges := by
  have htail : (s.from (s.m+k)).m = s.m + k := by grind
  rw [Series.converges_iff_tail_decay, Series.converges_iff_tail_decay, htail]
  constructor
  · intro hconv ε hε
    choose N hNsm hN using hconv ε hε
    use N + k
    constructor
    · grind
    · intro p hp q hq
      specialize hN p (by grind) q (by grind)
      simp; rw [Finset.sum_ite_of_true (by grind)]
      exact hN
  · intro htail ε hε
    choose N hNsm hN using htail ε hε
    use max N (s.m + k)
    constructor
    · grind
    · intro p hp q hq
      specialize hN p (by grind) q (by grind)
      simp at hN
      rwa [Finset.sum_ite_of_true (by grind)] at hN

theorem Series.sum_from {s:Series} (k:ℕ) (h: s.converges) :
    s.sum = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).sum := by
  have hfr := (Series.converges_from s k).mp h
  have hsum := Series.convergesTo_sum h
  have hfrsum := Series.convergesTo_sum hfr
  unfold Series.convergesTo at hsum hfrsum
  have hpartial : ∀ N ≥ s.m + k, s.partial N = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).partial N := by
    intro N hN
    unfold Series.partial
    have htail : (s.from (s.m+k)).m = s.m + k := by grind
    rw [htail]
    simp; rw [Finset.sum_ite_of_true (by grind)]
    have hunion : Finset.Icc s.m N = Finset.Ico s.m (s.m+k) ∪ Finset.Icc (s.m+k) N := by
      ext x
      simp; grind
    have hdisj : Disjoint (Finset.Ico s.m (s.m+k)) (Finset.Icc (s.m+k) N) := by
      rw [Finset.disjoint_left]
      intro x hx
      simp; grind
    rw [hunion, Finset.sum_union hdisj]
  have hge : ∀ᶠ N in Filter.atTop, s.partial N = ∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n + (s.from (s.m+k)).partial N := by
    apply Filter.eventually_atTop.mpr
    use s.m + k
  have hconstadd := hfrsum.const_add (∑ n ∈ Finset.Ico s.m (s.m+k), s.seq n)
  have hsum' := (Filter.tendsto_congr' hge).mpr hconstadd
  exact tendsto_nhds_unique hsum hsum'

/-- Proposition 7.2.14 (d) (Series laws) / Exercise 7.2.5 -/
theorem Series.shift {s:Series} {x:ℝ} (h: s.convergesTo x) (L:ℤ) :
    (mk' (m := s.m + L) (fun n ↦ s.seq (n - L))).convergesTo x := by
  unfold Series.convergesTo at h ⊢
  have hlag : Filter.Tendsto (fun (n:ℤ) => n - L) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b; use b + L; intro a; grind
  have hcomplag := h.comp hlag
  convert hcomplag using 1
  unfold Series.partial
  simp
  ext n
  rw [Finset.sum_ite_of_true (by grind)]
  apply Finset.sum_nbij (fun n => n - L)
  · intro a ha; simp at ha ⊢
    grind
  · intro x hx y hy hxy
    simp at hxy
    exact hxy
  · intro x hx
    use x + L
    simp; grind
  · intro a ha
    simp


#check Filter.tendsto_atTop_atTop

/-- Lemma 7.2.15 (telescoping series) / Exercise 7.2.6 -/
theorem Series.telescope {a:ℕ → ℝ} (ha: Filter.atTop.Tendsto a (nhds 0)) :
    ((fun n:ℕ ↦ a n - a (n+1)):Series).convergesTo (a 0) := by
  have hforall : ∀ n : ℕ, (fun n:ℕ ↦ a n - a (n+1):Series).partial n = a 0 - a (n+1) := by
    intro n
    induction' n with k ih
    · unfold Series.partial
      simp
    · unfold Series.partial at ih ⊢
      simp at ih ⊢
      rw [Finset.sum_ite_of_true (by grind)] at ih ⊢
      rw [sum_of_nonempty (by grind), ih]
      simp
  unfold Series.convergesTo
  set f := (fun n:ℕ ↦ a n - a (n+1):Series).partial with hfdef
  have ha' : Filter.Tendsto (fun n => a (n+1)) Filter.atTop (nhds 0) := by
    exact (Filter.tendsto_add_atTop_iff_nat 1).mpr ha
  suffices Filter.Tendsto (fun n : ℤ => a 0 - a (n.toNat + 1)) Filter.atTop (nhds (a 0)) by
    apply this.congr'
    apply Filter.eventually_atTop.mpr
    use 0
    intro b hb
    lift b to ℕ using (by omega)
    simp
    specialize hforall b
    exact hforall.symm
  nth_rewrite 2 [← sub_zero (a:=a 0)]
  apply tendsto_const_nhds.sub
  apply ha'.comp
  apply Filter.tendsto_atTop_atTop_of_monotone
  · intro a b hab
    simp; grind
  · intro b
    use b + 1
    grind

/- Exercise 7.2.1  -/

def Series.exercise_7_2_1_convergent :
  Decidable ( (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).converges ) := by
  -- The first line of this proof should be `apply isTrue` or `apply isFalse`.
  apply isFalse
  intro hconv
  -- have hsum := Series.convergesTo_sum hconv
  choose L hL using hconv
  unfold Series.convergesTo at hL
  have hforall : ∀ N ≥ 1,(mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).partial N = if Even N then 0 else -1 := by
    intro N hN
    induction' N, hN using Int.le_induction with k hk ih
    · unfold Series.partial
      simp
    · unfold Series.partial at ih ⊢
      simp at ih ⊢
      rw [Finset.sum_ite_of_true (by grind)] at ih ⊢
      rw [sum_of_nonempty (by grind), ih]
      by_cases! hevodd : Even k
      · rw [if_pos (by grind), if_neg (by grind)]
        simp
        rw [Odd.neg_one_zpow hevodd.add_one]
      · have hodd := Int.not_even_iff_odd.mp hevodd
        rw [if_neg hevodd, if_pos hodd]
        rw [Even.neg_one_zpow hodd.add_one]
        simp
  set f := (mk' (m := 1) (fun n ↦ (-1:ℝ)^(n:ℤ))).partial with hfdef
  choose N hN using Metric.tendsto_atTop.mp hL (1/4) (by norm_num)
  set N' := max 1 N with hN'def
  have hN'ge1 : N' ≥ 1 := by grind
  have hN'ge : 2 * N' ≥ N := by grind
  have heven : Even (2 * N') := by grind
  have hodd := heven.add_one
  have hN1 := hforall (2 * N') (by grind); rw [if_pos heven] at hN1
  have hN2 := hforall (2 * N' + 1) (by grind); rw [if_neg (Int.not_even_iff_odd.mpr hodd)] at hN2
  have hN1dist := hN (2 * N') (by grind)
  have hN2dist := hN (2 * N' + 1) (by grind)
  rw [hN1] at hN1dist
  rw [hN2] at hN2dist
  rw [Real.dist_eq] at hN1dist hN2dist
  grind

end Chapter7
