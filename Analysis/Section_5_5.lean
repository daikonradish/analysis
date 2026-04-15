import Mathlib.Tactic
import Analysis.Section_4_4
import Analysis.Section_5_4


/-!
# Analysis I, Section 5.5: The least upper bound property

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Upper bound and least upper bound on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5

/-- Definition 5.5.1 (upper bounds). Here we use the {name}`upperBounds` set defined in Mathlib. -/
theorem Real.upperBound_def (E: Set Real) (M: Real) : M ∈ upperBounds E ↔ ∀ x ∈ E, x ≤ M :=
  mem_upperBounds

theorem Real.lowerBound_def (E: Set Real) (M: Real) : M ∈ lowerBounds E ↔ ∀ x ∈ E, x ≥ M :=
  mem_lowerBounds

/-- API for Example 5.5.2 -/
theorem Real.Icc_def (x y:Real) : .Icc x y = { z | x ≤ z ∧ z ≤ y } := rfl

/-- API for Example 5.5.2 -/
theorem Real.mem_Icc (x y z:Real) : z ∈ Set.Icc x y ↔ x ≤ z ∧ z ≤ y := by simp [Real.Icc_def]

/-- Example 5.5.2 -/
example (M: Real) : M ∈ upperBounds (.Icc 0 1) ↔ M ≥ 1 := by
  constructor
  · intro hm
    by_contra! h
    have h1mem : 1 ∈ Set.Icc (0:Real) 1 := by simp
    have hlem : 1 ≤ M := by
      rw [Real.upperBound_def] at hm
      specialize hm 1 h1mem
      exact hm
    linarith
  · intro hm
    rw [Real.upperBound_def]
    intro x ⟨hx1, hx₂⟩
    linarith


/-- API for Example 5.5.3 -/
theorem Real.Ioi_def (x:Real) : .Ioi x = { z | z > x } := rfl

/-- Example 5.5.3 -/
example : ¬ ∃ M : Real, M ∈ upperBounds (.Ioi 0) := by
  by_contra! h
  obtain ⟨M, hM⟩ := h
  have hMpos : 0 < M := by
    by_contra! h'
    rw [Real.upperBound_def] at hM
    specialize hM 1 (by simp)
    linarith
  rw [Real.upperBound_def] at hM
  specialize hM (M+1) (by grind)
  linarith

/-- Example 5.5.4 -/
example : ∀ M, M ∈ upperBounds (∅ : Set Real) := by
  intro M
  simp_all

theorem Real.upperBound_upper {M M': Real} (h: M ≤ M') {E: Set Real} (hb: M ∈ upperBounds E) :
    M' ∈ upperBounds E := by
  rw [Real.upperBound_def] at *
  intro x hx
  specialize hb x hx
  linarith

/-- Definition 5.5.5 (least upper bound).  Here we use the {name}`IsLUB` predicate defined in Mathlib. -/
theorem Real.isLUB_def (E: Set Real) (M: Real) :
    IsLUB E M ↔ M ∈ upperBounds E ∧ ∀ M' ∈ upperBounds E, M' ≥ M := by rfl

theorem Real.isGLB_def (E: Set Real) (M: Real) :
    IsGLB E M ↔ M ∈ lowerBounds E ∧ ∀ M' ∈ lowerBounds E, M' ≤ M := by rfl

/-- Example 5.5.6 -/
example : IsLUB (.Icc 0 1) (1 : Real) := by
  constructor
  · rw [Real.upperBound_def]
    intro x hx
    exact hx.2
  · rw [Real.lowerBound_def]
    intro y hy
    by_contra hlt
    let z := (max 0 y + 1) / 2
    have hzin : z ∈ Set.Icc 0 1 := by constructor <;> grind
    have hzgt : z > y := by
      have := le_max_right 0 y
      unfold z
      linarith
    have hcont := hy hzin
    grind


/-- Example 5.5.7 -/
example : ¬∃ M, IsLUB (∅: Set Real) M := by
  intro h
  obtain ⟨M, hM⟩ := h
  simp_all

/-- Proposition 5.5.8 (Uniqueness of least upper bound)-/
theorem Real.LUB_unique {E: Set Real} {M M': Real} (h1: IsLUB E M) (h2: IsLUB E M') : M = M' := by
  grind [Real.isLUB_def]

/-- Definition of "bounded above", using Mathlib notation -/
theorem Real.bddAbove_def (E: Set Real) : BddAbove E ↔ ∃ M, M ∈ upperBounds E := Set.nonempty_def

theorem Real.bddBelow_def (E: Set Real) : BddBelow E ↔ ∃ M, M ∈ lowerBounds E := Set.nonempty_def

/-- Exercise 5.5.2 -/
theorem Real.upperBound_between {E: Set Real} {n:ℕ} {L K:ℤ} (hLK: L < K)
  (hK: K*((1/(n+1):ℚ):Real) ∈ upperBounds E) (hL: L*((1/(n+1):ℚ):Real) ∉ upperBounds E) :
    ∃ m, L < m
    ∧ m ≤ K
    ∧ m*((1/(n+1):ℚ):Real) ∈ upperBounds E
    ∧ (m-1)*((1/(n+1):ℚ):Real) ∉ upperBounds E := by
  by_contra! h'
  have hinduct : ∀ j : ℕ, (K - j) * ((1/(n+1):ℚ):Real) ∈ upperBounds E := by
    intro j'
    induction' j' with j ih
    · simp_all
    · rw [Real.upperBound_def] at hL hK ih
      push_neg at hL
      obtain ⟨x₀, ⟨hmemx₀, hltx₀⟩⟩ := hL
      have ih' :=  ih x₀ hmemx₀
      rw [← Real.upperBound_def] at ih
      have hineq : L * ((1/(n+1):ℚ):Real) < (K - j) * ((1/(n+1):ℚ):Real) := by linarith
      have hpos : ((1/(n+1):ℚ):Real) ≥ 0 := by positivity
      have hineq' := lt_of_mul_lt_mul_right hineq hpos
      specialize h' (K - j) (by exact_mod_cast hineq') (by linarith) (by exact_mod_cast ih)
      push_cast at h'
      push_cast
      grind
  specialize hinduct (K - L).toNat
  have hksubl := @Int.toNat_of_nonneg (K - L) (by omega)
  have hksubl' : ((K - L).toNat : Real) = K - L := by exact_mod_cast hksubl
  rw [hksubl'] at hinduct
  rw [sub_sub_self] at hinduct
  exact absurd hinduct hL

/-- Exercise 5.5.3 -/
theorem Real.upperBound_discrete_unique {E: Set Real} {n:ℕ} {m m':ℤ}
  (hm1: (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm2: (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E)
  (hm'1: (((m':ℚ) / (n+1):ℚ):Real) ∈ upperBounds E)
  (hm'2: (((m':ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∉ upperBounds E) :
    m = m' := by
  rw [Real.upperBound_def] at *
  push_neg at hm2 hm'2
  apply le_antisymm
  · obtain ⟨x₀, hmemx₀, hltx₀⟩ := hm2
    specialize hm'1 x₀ hmemx₀
    have htrans := lt_of_lt_of_le hltx₀ hm'1
    push_cast at htrans
    rw [← sub_div] at htrans
    field_simp at htrans
    norm_cast at htrans
    grind
  · obtain ⟨x₀, hmemx₀, hltx₀⟩ := hm'2
    specialize hm1 x₀ hmemx₀
    have htrans :=  lt_of_lt_of_le hltx₀ hm1
    push_cast at htrans
    rw [← sub_div] at htrans
    field_simp at htrans
    norm_cast at htrans
    grind


/-- Lemmas that can be helpful for proving 5.5.4 -/
theorem Sequence.IsCauchy.abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy):
  ((|a| : ℕ → ℚ) : Sequence).IsCauchy := by
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at *
  intro ε hε
  specialize ha ε hε
  obtain ⟨N₁, hN₁⟩ := ha
  use N₁
  intro j hj k hk
  specialize hN₁ j hj k hk
  simp_all
  grind

theorem Real.LIM.abs_eq {a b:ℕ → ℚ} (ha: (a: Sequence).IsCauchy)
    (hb: (b: Sequence).IsCauchy) (h: LIM a = LIM b): LIM |a| = LIM |b| := by
  rw [Real.LIM_eq_LIM (Sequence.IsCauchy.abs ha) (Sequence.IsCauchy.abs hb)]
  rw [Real.LIM_eq_LIM ha hb] at h
  rw [Sequence.equiv_iff] at *
  intro ε hε
  specialize h ε hε
  obtain ⟨N₁, hN₁⟩ := h
  use N₁
  intro n hn
  specialize hN₁ n hn
  simp_all
  grind

lemma Real.LIM.pos_ge_zero_ge {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy)
  : ∃ N : ℕ, ∀ n ≥ N, a n > 0 := by
  have : (LIM a).IsPos := by exact (isPos_iff (LIM a)).mpr h
  rw [Real.isPos_def] at this
  obtain ⟨b, bddpos, bcauch, blima⟩ := this
  rw [Real.LIM_eq_LIM ha bcauch] at blima
  rw [Sequence.equiv_iff] at blima
  obtain ⟨Bd, BdPos, Bdlt⟩ := bddpos
  by_contra! h
  specialize blima (Bd / 2) (by positivity)
  obtain ⟨N, hN⟩ := blima
  specialize h N
  obtain ⟨n₀, hn₀, ale0⟩ := h
  specialize hN n₀ hn₀
  specialize Bdlt n₀
  grind

theorem Real.LIM.abs_eq_pos {a: ℕ → ℚ} (h: LIM a > 0) (ha: (a:Sequence).IsCauchy):
    LIM a = LIM |a| := by
  rw [Real.LIM_eq_LIM ha (Sequence.IsCauchy.abs ha)]
  rw [Sequence.equiv_iff]
  obtain ⟨N₁, hN₁⟩ := Real.LIM.pos_ge_zero_ge h ha
  intro ε hε
  use N₁
  intro n hn
  specialize hN₁ n hn
  dsimp
  rw [_root_.abs_of_pos hN₁]
  simp_all
  linarith

theorem Real.LIM_abs {a:ℕ → ℚ} (ha: (a:Sequence).IsCauchy): |LIM a| = LIM |a| := by
  rcases Real.trichotomous (LIM a) with (h | h | h)
  · rw [h]
    simp
    change ((0:ℚ):Real) = LIM |a|
    change LIM a = ((0:ℚ):Real) at h
    rw [Real.ratCast_def] at *
    rw [LIM_eq_LIM (Sequence.IsCauchy.const 0) (Sequence.IsCauchy.abs ha)]
    rw [LIM_eq_LIM ha (Sequence.IsCauchy.const 0)] at h
    rw [Sequence.equiv_iff] at *
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := h ε hε
    use N₁
    intro n hn
    specialize hN₁ n hn
    simp_all
  · rw [Real.abs_eq_abs]
    rw [Real.abs_of_pos (LIM a) h]
    have hlimpos : LIM a > 0 := by exact (isPos_iff (LIM a)).mp h
    exact Real.LIM.abs_eq_pos hlimpos ha
  · rw [Real.abs_eq_abs]
    have hlimpos : (LIM a) < 0 := by exact (isNeg_iff (LIM a)).mp h
    have hlimneg : -LIM a > 0 := by linarith
    rw [Real.abs_of_neg (LIM a) h]
    -- have hneglimpos : (- LIM a).IsPos := by exact (neg_iff_pos_of_neg (LIM a)).mp h
    rw [Real.neg_LIM a ha] at *
    have hlim := @Real.LIM.abs_eq_pos (-a) hlimneg (Sequence.IsCauchy.neg a ha)
    rw [abs_neg a] at hlim
    exact hlim

lemma Sequence.IsCauchy.tail (a:ℕ → ℚ) (N : ℕ) (ha: (a:Sequence).IsCauchy) :
  ((fun n => a (n + N)):Sequence).IsCauchy := by
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at *
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := ha ε hε
  use N₀
  intro j hj k hk
  specialize hN₀ (j+N) (by linarith) (k+N) (by linarith)
  exact hN₀

lemma Real.LIM_of_tail {a : ℕ → ℚ} (N : ℕ) (hcauchy: (a:Sequence).IsCauchy) :
  LIM a = LIM (fun n => a (n + N)) := by
  have htailcauchy := Sequence.IsCauchy.tail a N hcauchy
  rw [Real.LIM_eq_LIM hcauchy htailcauchy]
  rw [Sequence.equiv_iff]
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at hcauchy
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
  use N₀
  intro n hn
  specialize hN₀ n hn (n + N) (by linarith)
  exact hN₀

theorem Real.LIM_of_le' {x:Real} {a:ℕ → ℚ} (hcauchy: (a:Sequence).IsCauchy)
    (h: ∃ N, ∀ n ≥ N, a n ≤ x) : LIM a ≤ x := by
  obtain ⟨N₀, hN₀⟩ := h
  set α : ℕ → ℚ := fun n => a (n + N₀)
  have hlimα : LIM a = LIM α := by
    unfold α
    exact Real.LIM_of_tail N₀ hcauchy
  have hα : ∀ n : ℕ, α n ≤ x := by
    intro n
    unfold α
    specialize hN₀ (n + N₀) (by linarith)
    exact hN₀
  rw [hlimα]
  by_contra! h'
  obtain ⟨q, hqlb, hqub⟩ := Real.rat_between h'
  set β : ℕ → ℚ := fun _ => q
  have hmono : ∀ n : ℕ, α n ≤ β n := by
    intro n
    specialize hα n
    unfold β
    have hreal : ((α n) : Real) ≤ (q : Real) := by linarith
    exact_mod_cast hreal
  have hcontra := Real.LIM_mono (Sequence.IsCauchy.tail a N₀ hcauchy) (Sequence.IsCauchy.const q) hmono
  rw [← Real.ratCast_def] at hcontra
  change LIM α ≤ q at hcontra
  linarith


theorem Rat.LIM_of_le {x : ℚ} {a : ℕ → ℚ}
  (hcauchy: (a:Sequence).IsCauchy) (h : ∀ (n : ℕ), a n ≤ x) : LIM a ≤ x := by
  have : ∀ n : ℕ, ((a n):Real) ≤ (x:Real) := by exact_mod_cast h
  exact @Real.LIM_of_le (x:Real) a hcauchy this

theorem Rat.LIM_of_ge {x : ℚ} {a : ℕ → ℚ}
  (hcauchy: (a:Sequence).IsCauchy) (h : ∀ (n : ℕ), a n ≥ x) : LIM a ≥ x := by
  have : ∀ n : ℕ, ((a n):Real) ≥ (x:Real) := by exact_mod_cast h
  exact @Real.LIM_of_ge (x:Real) a hcauchy this

/-- Exercise 5.5.4 -/
theorem Real.LIM_of_Cauchy {q:ℕ → ℚ} (hq: ∀ M, ∀ n ≥ M, ∀ n' ≥ M, |q n - q n'| ≤ 1 / (M+1)) :
    (q:Sequence).IsCauchy ∧ ∀ M, |q M - LIM q| ≤ 1 / (M+1) := by
  have hqcauchy : (q:Sequence).IsCauchy := by
    simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1/ε)
    use N₀
    intro j hj k hk
    specialize hq N₀ j hj k hk
    have hεpos : 0 < 1/ε := by positivity
    have hN₀pos : 0 < (N₀:ℚ) := by linarith
    have hNPlus1 : (N₀:ℚ) ≤ N₀ + 1 := by linarith
    have hNPlus1Inv := one_div_le_one_div_of_le hN₀pos hNPlus1
    have : 1 / N₀ ≤ ε := by exact (one_div_le hε hN₀pos).mp hN₀
    grind
  constructor
  · exact hqcauchy
  · intro M
    specialize hq M M (by linarith)
    set α : ℕ → ℚ := fun n => q (n + M)
    have hαcauchy := Sequence.IsCauchy.tail q M hqcauchy
    simp_rw [abs_sub_comm (q M) _, abs_le] at hq
    have hqlb := fun n' hn' => (hq n' hn').1
    have hqub := fun n' hn' => (hq n' hn').2
    conv at hqlb =>
      intro n hm
      rw [le_sub_iff_add_le]
    conv at hqub =>
      intro n hm
      rw [sub_le_iff_le_add]
    have hαlb : ∀ n : ℕ, -(1 / (M + 1)) + q M ≤ α n := by
      intro n
      specialize hqlb (n+M) (by linarith)
      exact hqlb
    have hαub : ∀ n : ℕ, α n ≤ 1 / (M + 1) + q M := by
      intro n
      specialize hqub (n+M) (by linarith)
      exact hqub
    have hlb := Rat.LIM_of_ge hαcauchy hαlb
    have hub := Rat.LIM_of_le hαcauchy hαub
    have hlimtail := Real.LIM_of_tail M hqcauchy
    rw [← hlimtail] at hlb hub
    push_cast at hlb hub
    rw [abs_le]
    constructor
    · grind
    · grind

/--
The sequence m₁, m₂, … is well-defined.
This proof uses a different indexing convention than the text
-/
lemma Real.LUB_claim1 (n : ℕ) {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E)
:  ∃! m:ℤ,
      (((m:ℚ) / (n+1):ℚ):Real) ∈ upperBounds E
      ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Real) ∈ upperBounds E := by
  set x₀ := Set.Nonempty.some hE
  observe hx₀ : x₀ ∈ E
  set ε := ((1/(n+1):ℚ):Real)
  have hpos : ε.IsPos := by simp [isPos_iff, ε]; positivity
  apply existsUnique_of_exists_of_unique
  . rw [bddAbove_def] at hbound; obtain ⟨ M, hbound ⟩ := hbound
    choose K _ hK using le_mul hpos M
    choose L' _ hL using le_mul hpos (-x₀)
    set L := -(L':ℤ)
    have claim1_1 : L * ε < x₀ := by simp [L]; linarith
    have claim1_2 : L * ε ∉ upperBounds E := by grind [upperBound_def]
    have claim1_3 : (K:Real) > (L:Real) := by
      contrapose! claim1_2
      replace claim1_2 := mul_le_mul_left claim1_2 hpos
      simp_rw [mul_comm] at claim1_2
      replace claim1_2 : M ≤ L * ε := by order
      grind [upperBound_upper]
    have claim1_4 : ∃ m:ℤ, L < m ∧ m ≤ K ∧ m*ε ∈ upperBounds E ∧ (m-1)*ε ∉ upperBounds E := by
      convert Real.upperBound_between (n := n) _ _ claim1_2
      . qify; rwa [←gt_iff_lt, gt_of_coe]
      simp [ε] at *; apply upperBound_upper _ hbound; order
    choose m _ _ hm hm' using claim1_4; use m
    have : (m/(n+1):ℚ) = m*ε := by simp [ε]; field_simp
    exact ⟨ by convert hm, by convert hm'; simp [this, sub_mul, ε] ⟩
  grind [upperBound_discrete_unique]

lemma Real.LUB_claim2 {E : Set Real} (N:ℕ) {a b: ℕ → ℚ}
  (hb : ∀ n, b n = 1 / (↑n + 1))
  (hm1 : ∀ (n : ℕ), ↑(a n) ∈ upperBounds E)
  (hm2 : ∀ (n : ℕ), ↑((a - b) n) ∉ upperBounds E)
: ∀ n ≥ N, ∀ n' ≥ N, |a n - a n'| ≤ 1 / (N+1) := by
    intro n hn n' hn'
    rw [abs_le]
    split_ands
    . specialize hm1 n; specialize hm2 n'
      have bound1 : ((a-b) n') < a n := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
      have bound3 : 1/((n':ℚ)+1) ≤ 1/(N+1) := by gcongr
      rw [←neg_le_neg_iff] at bound3; rw [Pi.sub_apply] at bound1; grind
    specialize hm1 n'; specialize hm2 n
    have bound1 : ((a-b) n) < a n' := by rw [lt_of_coe]; contrapose! hm2; grind [upperBound_upper]
    have bound2 : ((a-b) n) = a n - 1 / (n+1) := by simp [hb n]
    have bound3 : 1/((n+1):ℚ) ≤ 1/(N+1) := by gcongr
    linarith

/-- Theorem 5.5.9 (Existence of least upper bound)-/
theorem Real.LUB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddAbove E): ∃ S, IsLUB E S := by
  -- This proof is written to follow the structure of the original text.
  set x₀ := hE.some
  have hx₀ : x₀ ∈ E := hE.some_mem
  set m : ℕ → ℤ := fun n ↦ (LUB_claim1 n hE hbound).exists.choose
  set a : ℕ → ℚ := fun n ↦ (m n:ℚ) / (n+1)
  set b : ℕ → ℚ := fun n ↦ 1 / (n+1)
  have claim1 (n: ℕ) := LUB_claim1 n hE hbound
  have hb : (b:Sequence).IsCauchy := .harmonic'
  have hm1 (n:ℕ) := (claim1 n).exists.choose_spec.1
  have hm2 (n:ℕ) : ¬((a - b) n: Real) ∈ upperBounds E := (claim1 n).exists.choose_spec.2
  have claim2 (N:ℕ) := LUB_claim2 N (by aesop) hm1 hm2
  have claim3 : (a:Sequence).IsCauchy := (LIM_of_Cauchy claim2).1
  set S := LIM a; use S
  have claim4 : S = LIM (a - b) := by
    have : LIM b = 0 := LIM.harmonic
    simp [←LIM_sub claim3 hb, S, this]
  rw [isLUB_def, upperBound_def]
  split_ands
  . intro x hx; apply LIM_of_ge claim3; intro n
    exact (upperBound_def E (a n)).mp (hm1 n) x hx
  intro y hy
  have claim5 (n:ℕ) : y ≥ (a-b) n := by contrapose! hm2; use n; apply upperBound_upper _ hy; order
  rw [claim4]; apply LIM_of_le _ claim5; solve_by_elim [Sequence.IsCauchy.sub]

/-- A bare-bones extended real class to define supremum. -/
inductive ExtendedReal where
| neg_infty : ExtendedReal
| real (x:Real) : ExtendedReal
| infty : ExtendedReal

/-- Mathlib prefers {syntax term}`⊤` to denote the +∞ element. -/
instance ExtendedReal.inst_Top : Top ExtendedReal where
  top := infty

/-- Mathlib prefers {syntax term}`⊥` to denote the -∞ element. -/
instance ExtendedReal.inst_Bot: Bot ExtendedReal where
  bot := neg_infty

instance ExtendedReal.coe_real : Coe Real ExtendedReal where
  coe x := ExtendedReal.real x

instance ExtendedReal.real_coe : Coe ExtendedReal Real where
  coe X := match X with
  | neg_infty => 0
  | real x => x
  | infty => 0

abbrev ExtendedReal.IsFinite (X : ExtendedReal) : Prop := match X with
  | neg_infty => False
  | real _ => True
  | infty => False

theorem ExtendedReal.finite_eq_coe {X: ExtendedReal} (hX: X.IsFinite) :
    X = ((X:Real):ExtendedReal) := by
  cases X <;> try simp [IsFinite] at hX
  simp

open Classical in
/-- Definition 5.5.10 (Supremum)-/
noncomputable abbrev ExtendedReal.sup (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddAbove E then ((Real.LUB_exist h1 h2).choose:Real) else ⊤) else ⊥

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_empty : sup ∅ = ⊥ := by simp [sup]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_unbounded {E: Set Real} (hb: ¬ BddAbove E) : sup E = ⊤ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [sup, hE, hb]

/-- Definition 5.5.10 (Supremum)-/
theorem ExtendedReal.sup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sup E) := by
  simp [hnon, hb, sup]; exact (Real.LUB_exist hnon hb).choose_spec

theorem ExtendedReal.sup_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    (sup E).IsFinite := by simp [sup, hnon, hb, IsFinite]

/-- Proposition 5.5.12 -/
theorem Real.exist_sqrt_two : ∃ x:Real, x^2 = 2 := by
  -- This proof is written to follow the structure of the original text.
  set E := { y:Real | y ≥ 0 ∧ y^2 < 2 }
  have claim1: 2 ∈ upperBounds E := by
    rw [upperBound_def]
    intro y hy; simp [E] at hy; contrapose! hy
    intro hpos
    calc
      _ ≤ 2 * 2 := by norm_num
      _ ≤ y * y := by gcongr
      _ = y^2 := by ring
  have claim1' : BddAbove E := by rw [bddAbove_def]; use 2
  have claim2: 1 ∈ E := by simp [E]
  observe claim2': E.Nonempty
  set x := ((ExtendedReal.sup E):Real)
  have claim3 : IsLUB E x := by grind [ExtendedReal.sup_of_bounded]
  have claim4 : x ≥ 1 := by grind [isLUB_def, upperBound_def]
  have claim5 : x ≤ 2 := by grind [isLUB_def]
  have claim6 : x.IsPos := by rw [isPos_iff]; linarith
  use x; obtain h | h | h := trichotomous' (x^2) 2
  . have claim11: ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 - 4*ε > 2 := by
      set ε := min (1/2) ((x^2-2)/8)
      have hx : x^2 - 2 > 0 := by linarith
      have hε : 0 < ε := by positivity
      observe hε1: ε ≤ 1/2
      observe hε2: ε ≤ (x^2-2)/8
      refine' ⟨ ε, hε, _, _ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim11
    have claim12: (x-ε)^2 > 2 := calc
      _ = x^2 - 2 * ε * x + ε * ε := by ring
      _ ≥ x^2 - 2 * ε * 2 + 0 * 0 := by gcongr
      _ = x^2 - 4 * ε := by ring
      _ > 2 := hε3
    have why (y:Real) (hy: y ∈ E) : x - ε ≥ y := by
      have fact1 : y ^ 2 < 2 := by simp [E] at hy; exact hy.2
      have fact2 : y ^ 2  < (x - ε) ^ 2 := by linarith
      have fact3 := (sq_lt_sq₀ (by grind) (by linarith)).mp fact2
      linarith
    have claim13: x-ε ∈ upperBounds E := by rwa [upperBound_def]
    have claim14: x ≤ x-ε := by grind [isLUB_def]
    linarith
  . have claim7 : ∃ ε, 0 < ε ∧ ε < 1 ∧ x^2 + 5*ε < 2 := by
      set ε := min (1/2) ((2-x^2)/10)
      have hx : 2 - x^2 > 0 := by linarith
      have hε: 0 < ε := by positivity
      have hε1: ε ≤ 1/2 := min_le_left _ _
      have hε2: ε ≤ (2 - x^2)/10 := min_le_right _ _
      refine ⟨ ε, hε, ?_, ?_ ⟩ <;> linarith
    choose ε hε1 hε2 hε3 using claim7
    have claim8 : (x+ε)^2 < 2 := calc
      _ = x^2 + (2*x)*ε + ε*ε := by ring
      _ ≤ x^2 + (2*2)*ε + 1*ε := by gcongr
      _ = x^2 + 5*ε := by ring
      _ < 2 := hε3
    have claim9 : x + ε ∈ E := by simp [E, claim8]; linarith
    have claim10 : x + ε ≤ x := by grind [isLUB_def, upperBound_def]
    linarith
  assumption

/-- Remark 5.5.13 -/
theorem Real.exist_irrational : ∃ x:Real, ¬ ∃ q:ℚ, x = (q:Real) := by
  obtain ⟨x, hx⟩ := Real.exist_sqrt_two
  use x
  have hsqrttwonotrat := Rat.not_exist_sqrt_two
  push_neg at *
  intro q hxq
  specialize hsqrttwonotrat q
  rw [hxq] at hx
  norm_cast at hx

/-- Helper lemma for Exercise 5.5.1. -/
theorem Real.mem_neg (E: Set Real) (x:Real) : x ∈ -E ↔ -x ∈ E := Set.mem_neg

/-- Exercise 5.5.1-/
theorem Real.inf_neg {E: Set Real} {M:Real} (h: IsLUB E M) : IsGLB (-E) (-M) := by
  constructor
  · intro x hx
    rw [Real.mem_neg] at hx
    have hbound := h.1 hx
    linarith
  · intro y hy
    obtain ⟨hl, hr⟩ := h
    have hnegy : ∀ α : Real, α ∈ E → -α ∈ -E := by
      intro α hα
      rw [Real.mem_neg]
      simpa
    have hub : -y ∈ upperBounds (E) := by
      intro y' hy'
      specialize hy (hnegy y' hy')
      linarith
    specialize hr hub
    linarith

theorem Real.GLB_exist {E: Set Real} (hE: Set.Nonempty E) (hbound: BddBelow E): ∃ S, IsGLB E S := by
  have hE' : Set.Nonempty (-E) := by
    exact Set.Nonempty.neg hE
  have hbound' : BddAbove (-E) := by
    obtain ⟨Bd, hBd⟩ := hbound
    use -Bd
    intro x hx
    rw [Real.mem_neg] at hx
    specialize hBd hx
    linarith
  obtain ⟨S, hLUB⟩ := Real.LUB_exist hE' hbound'
  use -S
  have hGLB := Real.inf_neg hLUB
  simp at hGLB
  exact hGLB


open Classical in
noncomputable abbrev ExtendedReal.inf (E: Set Real) : ExtendedReal :=
  if h1:E.Nonempty then (if h2:BddBelow E then ((Real.GLB_exist h1 h2).choose:Real) else ⊥) else ⊤

theorem ExtendedReal.inf_of_empty : inf ∅ = ⊤ := by simp [inf]

theorem ExtendedReal.inf_of_unbounded {E: Set Real} (hb: ¬ BddBelow E) : inf E = ⊥ := by
  have hE : E.Nonempty := by contrapose! hb; simp [hb]
  simp [inf, hE, hb]

theorem ExtendedReal.inf_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    IsGLB E (inf E) := by simp [hnon, hb, inf]; exact (Real.GLB_exist hnon hb).choose_spec

theorem ExtendedReal.inf_of_bounded_finite {E: Set Real} (hnon: E.Nonempty) (hb: BddBelow E) :
    (inf E).IsFinite := by simp [inf, hnon, hb, IsFinite]

/-- Exercise 5.5.5 -/
theorem Real.irrat_between {x y:Real} (hxy: x < y) :
    ∃ z, x < z ∧ z < y ∧ ¬ ∃ q:ℚ, z = (q:Real) := by
  obtain ⟨sqrttwo, hsqrttwo⟩ := Real.exist_sqrt_two
  have hxy' : x + sqrttwo < y + sqrttwo := by linarith
  obtain ⟨q, hqlb, hqub⟩ := Real.rat_between hxy'
  use q - sqrttwo
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro hq'
    obtain ⟨q', hq'⟩ := hq'
    have hq'' : sqrttwo = q - q' := by linarith
    norm_cast at hq''
    have hsq := congrArg (λ expr => expr ^2) hq''; dsimp at hsq
    rw [hsqrttwo] at hsq; symm at hsq
    have weird : ∃ x : ℚ, x ^ 2 = 2 := by
      use q - q'
      exact_mod_cast hsq
    exact Rat.not_exist_sqrt_two weird

/- Use the notion of supremum in this section to define a Mathlib `sSup` operation -/
noncomputable instance Real.inst_SupSet : SupSet Real where
  sSup E := ((ExtendedReal.sup E):Real)

/-- Use the {name}`sSup` operation to build a conditionally complete lattice structure on {name}`Real`. -/
noncomputable instance Real.inst_conditionallyCompleteLattice :
    ConditionallyCompleteLattice Real :=
  conditionallyCompleteLatticeOfLatticeOfsSup Real
  (by intros; solve_by_elim [ExtendedReal.sup_of_bounded])

theorem ExtendedReal.sSup_of_bounded {E: Set Real} (hnon: E.Nonempty) (hb: BddAbove E) :
    IsLUB E (sSup E) := sup_of_bounded hnon hb

end Chapter5
