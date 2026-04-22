import Mathlib.Tactic
import Analysis.Section_6_1
import Analysis.Section_6_2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analysis I, Section 6.3: Suprema and infima of sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Suprema and infima of sequences.

-/

namespace Chapter6

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.sup (a:Sequence) : EReal := sSup { x | ∃ n ≥ a.m, x = a n }

/-- Definition 6.3.1 -/
noncomputable abbrev Sequence.inf (a:Sequence) : EReal := sInf { x | ∃ n ≥ a.m, x = a n }

/-- Example 6.3.3 -/
lemma example633nat : ∀ n : ℕ, (-1:ℝ)^(n+1) = 1 ∨ (-1:ℝ)^(n+1) = -1 := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · right
    rw [hk, pow_add]; simp
  · left
    rw [hk]; norm_num

example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).sup = 1 := by
  apply le_antisymm
  · apply csSup_le
    · use (-1:ℝ)^(0+1)
      simp
      use 0
      constructor <;> simp_all
    · simp
      intro x z hz0 hx
      rw [if_pos hz0] at hx; simp at hx
      rcases example633nat (z.toNat) with (hone | hnegone)
      · have hone' := EReal.coe_eq_coe_iff.mpr hone; push_cast at hone'
        rw [hone'] at hx
        rw [hx]
      · have hnegone' := EReal.coe_eq_coe_iff.mpr hnegone; push_cast at hnegone'
        rw [hnegone'] at hx
        rw [hx]
        exact EReal.coe_le_coe (show (-1:ℝ) ≤ (1:ℝ) by linarith)
  · apply le_csSup
    · use 1
      simp
      intro x hx
      obtain ⟨n, hnpos, heq⟩ := hx
      simp_all
      rcases example633nat (n.toNat) with (hone | hnegone)
      · have hone' := EReal.coe_eq_coe_iff.mpr hone; push_cast at hone'
        rw [hone']
      · have hnegone' := EReal.coe_eq_coe_iff.mpr hnegone; push_cast at hnegone'
        rw [hnegone']
        exact EReal.coe_le_coe (show (-1:ℝ) ≤ (1:ℝ) by linarith)
    · simp_all
      use 1
      constructor <;> simp

/-- Example 6.3.3 -/
example : ((fun (n:ℕ) ↦ (-1:ℝ)^(n+1)):Sequence).inf = -1 := by
  apply le_antisymm
  · apply csInf_le
    · use -1
      simp
      intro x hx
      obtain ⟨n, hnpos, heq⟩ := hx
      simp_all
      rcases example633nat (n.toNat) with (hone | hnegone)
      · have hone' := EReal.coe_eq_coe_iff.mpr hone; push_cast at hone'
        rw [hone']
        exact EReal.coe_le_coe (show (-1:ℝ) ≤ (1:ℝ) by linarith)
      · have hnegone' := EReal.coe_eq_coe_iff.mpr hnegone; push_cast at hnegone'
        rw [hnegone']
    · simp_all
      use 0
      constructor <;> simp
  · apply le_csInf
    · use (-1:ℝ)^(0+1)
      simp
      use 0
      constructor <;> simp_all
    · simp
      intro x z hz0 hx
      rw [if_pos hz0] at hx; simp at hx
      rcases example633nat (z.toNat) with (hone | hnegone)
      · have hone' := EReal.coe_eq_coe_iff.mpr hone; push_cast at hone'
        rw [hone'] at hx
        rw [hx]
        exact EReal.coe_le_coe (show (-1:ℝ) ≤ (1:ℝ) by linarith)
      · have hnegone' := EReal.coe_eq_coe_iff.mpr hnegone; push_cast at hnegone'
        rw [hnegone'] at hx
        rw [hx]

/-- Example 6.3.4 / Exercise 6.3.1 -/
example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).sup = 1 := by
  apply le_antisymm
  · apply csSup_le
    · use 1; simp;
      use 0; constructor <;> simp_all
    · intro x hx
      simp_all
      obtain ⟨n, hnpos, heq⟩ := hx
      simp_all
      norm_cast at *
      exact Nat.cast_inv_le_one (n.toNat + 1)
  · apply le_csSup
    · use 1; simp
      intro x hx
      obtain ⟨n, hnpos, heq⟩ := hx
      simp_all
      norm_cast at *
      exact Nat.cast_inv_le_one (n.toNat + 1)
    · use 0; simp

/-- Example 6.3.4 / Exercise 6.3.1 -/
lemma example634exist : ∀ ε > 0, ∃ n:ℕ, 1/((n:ℝ)+1) < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1/ε)
  use n
  field_simp at *
  grind

example : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf = 0 := by
  apply le_antisymm
  · -- we need to show that the inf is ≤ 0.
    -- this is equivalent to showing that for every c > 0, inf < c.
    apply le_of_forall_gt
    intro c hc
    -- But this is where it gets a little ugly, because c is an EReal, so we must
    -- first unpack EReal into the cases: where it is some Real, infinity or negative infinity.
    obtain ⟨c', heq⟩ | ctop | cbot := EReal.def c
    · -- this is where you need to show that there exists some member of the
      -- set, using example 634
      by_contra! h'
      have hc'pos : 0 < c' := by
        rw [← heq] at hc
        norm_cast at hc
      obtain ⟨N, hN⟩ := example634exist c' hc'pos
      have hNEReal := EReal.coe_lt_coe_iff.mpr hN
      rw [heq] at hNEReal
      have hinf : ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)):Sequence).inf ≤ (((1/((N:ℝ)+1)):ℝ):EReal) := by
        apply sInf_le
        simp
        use N; constructor <;> simp_all
      have hclt := EReal.trans h' hinf
      grind
    · -- we need to show that the inf of the set is less than infinity.
      -- the only case where it could be infinity is when the set only consists
      -- of infinity, i.e. {⊤}
      rw [ctop]
      apply lt_top_iff_ne_top.mpr
      intro htop
      have htop' := sInf_eq_top.mp htop
      contrapose! htop'
      use 1
      constructor
      · simp_all
        use 0; constructor <;> simp_all
      · exact EReal.real_neq_infty 1
    · rw [cbot] at hc
      exfalso
      exact not_lt_bot hc
  · apply le_csInf
    · use 1; simp
      use 0; constructor <;> simp_all
    · intro x hx
      simp_all
      obtain ⟨n, hnpos, heq⟩ := hx
      simp_all
      positivity

/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).sup = ⊤ := by
  let ex635EReal := {x : EReal | ∃ n : ℕ, x = (((n + 1):ℝ):EReal)}
  let ex635Real := {x : ℝ | ∃ n : ℕ, x = ((n+1):ℝ)}
  unfold Sequence.sup
  have heqEReal : ex635EReal = {x:EReal | ∃ n ≥ ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).m, x = ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence) n} := by
    ext y
    unfold ex635EReal
    constructor
    · intro hy
      obtain ⟨N, hN⟩ := hy
      use N; constructor <;> simp_all
    · intro hy
      obtain ⟨N, hNam, hneq⟩ := hy
      simp_all
      use N.toNat
  have heqReal : ex635EReal = (fun (x:ℝ) ↦ (x:EReal)) '' ex635Real := by
    ext y
    unfold ex635EReal ex635Real
    constructor
    · intro hy
      obtain ⟨N, hN⟩ := hy
      simp_all
    · intro hy
      simp_all
      obtain ⟨N, hN⟩ := hy
      use N
      simp_all
  have hunbound : ¬ BddAbove ex635Real := by
    unfold ex635Real
    intro hbdd
    obtain ⟨Bd, hupper⟩ := hbdd
    have hflr : ⌊Bd⌋ + 1 > Bd := by exact Int.lt_floor_add_one Bd
    have hmem : ((⌊Bd⌋ + 1):ℝ) ∈ ex635Real := by
      by_cases hBd0 : Bd ≥ 0
      · use Int.toNat ⌊Bd⌋
        simp
        have hpos : 0 ≤ ⌊Bd⌋ := Int.floor_nonneg.mpr hBd0
        norm_cast
        exact Int.eq_natCast_toNat.mpr hpos
      · push_neg at hBd0
        have hone : 1 ∈ ex635Real := by
          unfold ex635Real
          simp
        specialize hupper hone
        linarith
    specialize hupper hmem
    linarith
  have hnon : ex635Real.Nonempty := by
    use 1
    unfold ex635Real
    simp_all
  rw [← heqEReal, heqReal]
  exact EReal.sup_of_unbounded_nonempty hunbound hnon


/-- Example 6.3.5 -/
example : ((fun (n:ℕ) ↦ (n+1:ℝ)):Sequence).inf = 1 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · use 1
    simp_all
    use 0; constructor <;> simp_all
  · intro x hx
    obtain ⟨x', heq⟩ | ctop | cbot := EReal.def x
    · simp at hx
      obtain ⟨N, hNpos, hNeq⟩ := hx
      rw [if_pos (by grind)] at hNeq
      rw [← heq] at hNeq
      have hNeq' := EReal.coe_eq_coe_iff.mp hNeq
      rw [← heq]
      have : 1 ≤ x' := by grind
      exact EReal.coe_le_coe this
    · rw [ctop]
      apply le_top
    · simp at hx
      obtain ⟨N, hNpos, hNeq⟩ := hx
      rw [if_pos (by grind)] at hNeq
      rw [hNeq] at cbot
      exact absurd cbot (EReal.real_neq_neg_infty _)
  · intro w hw
    use 1
    constructor
    · simp_all
      use 0; constructor <;> simp_all
    · exact hw

abbrev Sequence.BddAboveBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≤ M

abbrev Sequence.BddAbove (a:Sequence) : Prop := ∃ M, a.BddAboveBy M

abbrev Sequence.BddBelowBy (a:Sequence) (M:ℝ) : Prop := ∀ n ≥ a.m, a n ≥ M

abbrev Sequence.BddBelow (a:Sequence) : Prop := ∃ M, a.BddBelowBy M

theorem Sequence.bounded_iff (a:Sequence) : a.IsBounded ↔ a.BddAbove ∧ a.BddBelow := by
  constructor
  · intro hbdd
    obtain ⟨Bd, hBdpos, hBddBy⟩ := hbdd
    rw [BoundedBy] at hBddBy
    constructor
    · use Bd
      intro n hn
      specialize hBddBy n
      grind
    · use -Bd
      intro n hn
      specialize hBddBy n
      grind
  · rintro ⟨habove, hbelow⟩
    obtain ⟨A, hA⟩ := habove
    obtain ⟨B, hB⟩ := hbelow
    use max |A| |B|
    constructor
    · simp_all
    · rw [BoundedBy]
      intro n
      by_cases hvanish : n < a.m
      · rw [a.vanish n hvanish]
        simp
      · push_neg at hvanish
        specialize hA n hvanish
        specialize hB n hvanish
        have hpos : a.seq n ≤ max |A| |B| := by
           calc _ ≤ A           := by exact hA
                _ ≤ |A|         := by apply le_abs_self
                _ ≤ max |A| |B| := by apply le_max_left
        have hneg : -a.seq n ≤ max |A| |B| := by
           calc _ ≤ -B          := by linarith [hB]
                _ ≤ |B|         := by apply neg_le_abs
                _ ≤ max |A| |B| := by apply le_max_right
        exact abs_le.mpr ⟨by linarith [hneg], hpos⟩

theorem Sequence.sup_of_bounded {a:Sequence} (h: a.IsBounded) : a.sup.IsFinite := by
  by_contra h'
  rw [← EReal.infinite_iff_not_finite] at h'
  rcases h' with (htop | hbot)
  · obtain ⟨habove, hbelow⟩ := (Sequence.bounded_iff _).mp h
    obtain ⟨A, hA⟩ := habove
    rw [BddAboveBy] at hA
    rw [Sequence.sup] at htop
    have hA' : ∀ n ≥ a.m, ((a.seq n):EReal) ≤ (A:EReal) := by
      intro n hn
      specialize hA n hn
      exact EReal.coe_le_coe hA
    have hlt : sSup {x:EReal | ∃ n ≥ a.m, x = a n } ≤ (A:EReal) := by
      rw [csSup_le_iff]
      · intro b hb
        obtain ⟨N, hNam, hbseq⟩ := hb
        specialize hA' N hNam
        rwa [hbseq]
      · use A
        intro x hx
        obtain ⟨N, hNam, hbseq⟩ := hx
        specialize hA' N hNam
        rwa [hbseq]
      · use (a:Sequence) a.m
        simp_all
        use a.m
    rw [htop] at hlt
    exact absurd (top_le_iff.mp hlt) (EReal.real_neq_infty _)
  · have hbot' := sSup_eq_bot.mp hbot
    contrapose! hbot'
    use (a:Sequence) a.m
    constructor
    · simp_all; use a.m
    · exact EReal.real_neq_neg_infty (a.seq a.m)

theorem Sequence.inf_of_bounded {a:Sequence} (h: a.IsBounded) : a.inf.IsFinite := by
  by_contra h'
  rw [← EReal.infinite_iff_not_finite] at h'
  rcases h' with (htop | hbot)
  · have htop' := sInf_eq_top.mp htop
    contrapose! htop'
    use (a:Sequence) a.m
    constructor
    · simp_all; use a.m
    · exact EReal.real_neq_infty (a.seq a.m)
  · obtain ⟨habove, hbelow⟩ := (Sequence.bounded_iff _).mp h
    obtain ⟨B, hB⟩ := hbelow
    rw [BddBelowBy] at hB
    rw [Sequence.inf] at hbot
    have hB' : ∀ n ≥ a.m, (B:EReal) ≤ ((a.seq n):EReal) := by
      intro n hn
      specialize hB n hn
      exact EReal.coe_le_coe hB
    have hgt : (B:EReal) ≤ sInf {x:EReal | ∃ n ≥ a.m, x = a n} := by
      rw [le_csInf_iff]
      · intro b hb
        obtain ⟨N, hNam, hbseq⟩ := hb
        specialize hB' N hNam
        rwa [hbseq]
      · use B
        intro x hx
        obtain ⟨N, hNam, hbseq⟩ := hx
        specialize hB' N hNam
        rwa [hbseq]
      · use (a:Sequence) a.m
        simp_all
        use a.m
    rw [hbot] at hgt
    exact absurd (le_bot_iff.mp hgt) (EReal.real_neq_neg_infty _)

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.le_sup {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≤ a.sup := by
  apply EReal.mem_le_sup
  use n

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.sup_le_upper {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≤ M) : a.sup ≤ M := by
  apply EReal.sup_le_upper
  intro x hx
  obtain ⟨N, hNam, hnseq⟩ := hx
  specialize h N hNam
  rwa [hnseq]

/-- Proposition 6.3.6 (Least upper bound property) / Exercise 6.3.2 -/
theorem Sequence.exists_between_lt_sup {a:Sequence} {y:EReal} (h: y < a.sup) :
    ∃ n ≥ a.m, y < a n ∧ a n ≤ a.sup := by
    by_contra! h'
    have hall : ∀ n ≥ a.m, y ≥ a n := by
      intro n hn
      specialize h' n (by linarith)
      replace h' := mt h'; push_neg at h'
      have hlesup := Sequence.le_sup (n:=n) (by linarith)
      exact h' hlesup
    have hyupper : y ∈ upperBounds { (x:EReal) | ∃ n ≥ a.m, x = a n } := by
      intro x hx
      obtain ⟨N, hNam, heq⟩ := hx
      specialize hall N hNam
      rw [heq]
      exact hall
    rw [Sequence.sup] at h
    have hineq := EReal.sup_le_upper _ hyupper
    rcases (EReal.le_iff _ _).mp hineq with (hreal | htop | hbot)
    · obtain ⟨x', y', hx', hy', hxy⟩ := hreal
      rw [hx', hy'] at h
      have hxy' := EReal.coe_lt_coe_iff.mp h
      linarith
    · rw [htop] at h
      exact absurd h not_top_lt
    · rw [hbot] at h
      exact absurd h not_lt_bot

/-- Remark 6.3.7 -/
theorem Sequence.ge_inf {a:Sequence} {n:ℤ} (hn: n ≥ a.m) : a n ≥ a.inf := by
  apply EReal.mem_ge_inf
  use n

/-- Remark 6.3.7 -/
theorem Sequence.inf_ge_lower {a:Sequence} {M:EReal} (h: ∀ n ≥ a.m, a n ≥ M) : a.inf ≥ M := by
  apply EReal.inf_ge_upper
  intro x hx
  obtain ⟨N, hNam, hnseq⟩ := hx
  specialize h N hNam
  rwa [hnseq]

/-- Remark 6.3.7 -/
theorem Sequence.exists_between_gt_inf {a:Sequence} {y:EReal} (h: y > a.inf ) :
    ∃ n ≥ a.m, y > a n ∧ a n ≥ a.inf := by
    by_contra! h'
    have hall : ∀ n ≥ a.m, y ≤ a n := by
      intro n hn
      specialize h' n (by linarith)
      replace h' := mt h'; push_neg at h'
      have hleinf := Sequence.ge_inf (n:=n) (by linarith)
      exact h' hleinf
    have hylower : y ∈ lowerBounds { (x:EReal) | ∃ n ≥ a.m, x = a n } := by
      intro x hx
      obtain ⟨N, hNam, heq⟩ := hx
      specialize hall N hNam
      rw [heq]
      exact hall
    rw [Sequence.inf] at h
    have hineq := EReal.inf_ge_upper _ hylower
    rcases (EReal.le_iff _ _).mp hineq with (hreal | htop | hbot)
    · obtain ⟨x', y', hx', hy', hxy⟩ := hreal
      rw [hx', hy'] at h
      have hxy' := EReal.coe_lt_coe_iff.mp h
      linarith
    · rw [htop] at h
      exact absurd h not_top_lt
    · rw [hbot] at h
      exact not_lt_bot h

abbrev Sequence.IsMonotone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≥ a n

abbrev Sequence.IsAntitone (a:Sequence) : Prop := ∀ n ≥ a.m, a (n+1) ≤ a n

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
lemma Sequence.bddAbove_not_top {a:Sequence} (hbound : a.BddAbove) : a.sup ≠ ⊤ := by
  obtain ⟨A, hA⟩ := hbound
  have hAupper : (A:EReal) ∈ upperBounds {(x:EReal) | ∃ n ≥ a.m, x = a n} := by
    intro x hx
    obtain ⟨N, hNam, heq⟩ := hx
    specialize hA N hNam
    rw [heq]
    exact_mod_cast hA
  have hnon : {(x:EReal) | ∃ n ≥ a.m, x = a n}.Nonempty := by
    use a.seq a.m; simp_all
    use a.m
  by_contra! h'
  have hle := csSup_le hnon hAupper
  rw [Sequence.sup] at h'
  rw [h'] at hle
  exact absurd (top_le_iff.mp hle) (EReal.real_neq_infty A)

theorem Sequence.convergent_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) :
    a.Convergent := by
  rw [Sequence.convergent_def]
  obtain ⟨c', heq⟩ | htop | hbot := EReal.def (a.sup)
  · use c'
    intro ε hε
    have hsubε : c' - ε < c' := by linarith
    have hsubε' := EReal.coe_lt_coe hsubε
    rw [heq] at hsubε'
    obtain ⟨N, hNam, hlt, hub⟩ := Sequence.exists_between_lt_sup hsubε'
    use N
    constructor
    · exact hNam
    · intro n hn
      simp at hn ⊢
      rw [if_pos hn, Real.dist_eq]
      apply abs_sub_le_iff.mpr
      constructor
      · have hlesup := Sequence.le_sup (n:=n) hn.1
        rw [← heq] at hlesup
        have hlesupreal := EReal.coe_le_coe_iff.mp hlesup
        grind
      · have hltreal := EReal.coe_lt_coe_iff.mp hlt
        have hgreater (n : ℤ) (hn : n ≥ N) : c' - ε < a.seq n := by
          induction n, hn using Int.le_induction with
          | base          => exact hltreal
          | succ k hle ih =>
          specialize hmono k (by grind)
          linarith
        specialize hgreater n (by grind)
        grind
  · exact absurd htop (Sequence.bddAbove_not_top hbound)
  · have hbot' := sSup_eq_bot.mp hbot
    contrapose! hbot'
    use (a:Sequence) a.m
    constructor
    · simp_all; use a.m
    · exact EReal.real_neq_neg_infty (a.seq a.m)

/-- Proposition 6.3.8 / Exercise 6.3.3 -/
theorem Sequence.lim_of_monotone {a:Sequence} (hbound: a.BddAbove) (hmono: a.IsMonotone) : lim a = a.sup := by
    obtain ⟨c', heq⟩ | htop | hbot := EReal.def (a.sup)
    · suffices alternatively : a.TendsTo (c') by
        rw [← heq]
        norm_cast
        have := Sequence.lim_eq.mp alternatively
        exact this.2
      intro ε hε
      have hsubε : c' - ε < c' := by linarith
      have hsubε' := EReal.coe_lt_coe hsubε
      rw [heq] at hsubε'
      obtain ⟨N, hNam, hlt, hub⟩ := Sequence.exists_between_lt_sup hsubε'
      use N
      constructor
      · exact hNam
      · intro n hn
        simp at hn ⊢
        rw [if_pos hn, Real.dist_eq]
        apply abs_sub_le_iff.mpr
        constructor
        · have hlesup := Sequence.le_sup (n:=n) hn.1
          rw [← heq] at hlesup
          have hlesupreal := EReal.coe_le_coe_iff.mp hlesup
          grind
        · have hltreal := EReal.coe_lt_coe_iff.mp hlt
          have hgreater (n : ℤ) (hn : n ≥ N) : c' - ε < a.seq n := by
            induction n, hn using Int.le_induction with
            | base          => exact hltreal
            | succ k hle ih =>
            specialize hmono k (by grind)
            linarith
          specialize hgreater n (by grind)
          grind
    · exact absurd htop (Sequence.bddAbove_not_top hbound)
    · have hbot' := sSup_eq_bot.mp hbot
      contrapose! hbot'
      use (a:Sequence) a.m
      constructor
      · simp_all; use a.m
      · exact EReal.real_neq_neg_infty (a.seq a.m)


lemma Sequence.bddBelow_not_bot {a:Sequence} (hbound : a.BddBelow) : a.inf ≠ ⊥ := by
  obtain ⟨B, hB⟩ := hbound
  have hBlower : (B:EReal) ∈ lowerBounds {(x:EReal) | ∃ n ≥ a.m, x = a n} := by
    intro x hx
    obtain ⟨N, hNam, heq⟩ := hx
    specialize hB N hNam
    rw [heq]
    exact_mod_cast hB
  have hnon : {(x:EReal) | ∃ n ≥ a.m, x = a n}.Nonempty := by
    use a.seq a.m; simp_all
    use a.m
  by_contra! h'
  have hge := le_csInf hnon hBlower
  rw [Sequence.inf] at h'
  rw [h'] at hge
  exact absurd (le_bot_iff.mp hge) (EReal.real_neq_neg_infty B)


theorem Sequence.convergent_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    a.Convergent := by
  rw [Sequence.convergent_def]
  obtain ⟨c', heq⟩ | htop | hbot := EReal.def (a.inf)
  · use c'
    intro ε hε
    have haddε : c'  < c' + ε := by linarith
    have haddε' := EReal.coe_lt_coe haddε
    rw [heq] at haddε'
    obtain ⟨N, hNam, hlt, hub⟩ := Sequence.exists_between_gt_inf haddε'
    use N
    constructor
    · exact hNam
    · intro n hn
      simp at hn ⊢
      rw [if_pos hn, Real.dist_eq]
      apply abs_sub_le_iff.mpr
      constructor
      · have hltreal := EReal.coe_lt_coe_iff.mp hlt
        have hgreater (n : ℤ) (hn : n ≥ N) : a.seq n < c' + ε := by
          induction n, hn using Int.le_induction with
          | base          => exact hltreal
          | succ k hle ih =>
          specialize hmono k (by grind)
          linarith
        specialize hgreater n (by grind)
        grind
      · have hgeinf := Sequence.ge_inf (n:=n) hn.1
        rw [← heq] at hgeinf
        have hlesupreal := EReal.coe_le_coe_iff.mp hgeinf
        grind
  · have htop' := sInf_eq_top.mp htop
    contrapose! htop'
    use (a:Sequence) a.m
    constructor
    · simp_all; use a.m
    · exact EReal.real_neq_infty (a.seq a.m)
  · exact absurd hbot (Sequence.bddBelow_not_bot hbound)

theorem Sequence.lim_of_antitone {a:Sequence} (hbound: a.BddBelow) (hmono: a.IsAntitone) :
    lim a = a.inf := by
  obtain ⟨c', heq⟩ | htop | hbot := EReal.def (a.inf)
  · suffices alternatively : a.TendsTo (c') by
      rw [← heq]
      norm_cast
      have := Sequence.lim_eq.mp alternatively
      exact this.2
    intro ε hε
    have haddε : c'  < c' + ε := by linarith
    have haddε' := EReal.coe_lt_coe haddε
    rw [heq] at haddε'
    obtain ⟨N, hNam, hlt, hub⟩ := Sequence.exists_between_gt_inf haddε'
    use N
    constructor
    · exact hNam
    · intro n hn
      simp at hn ⊢
      rw [if_pos hn, Real.dist_eq]
      apply abs_sub_le_iff.mpr
      constructor
      · have hltreal := EReal.coe_lt_coe_iff.mp hlt
        have hgreater (n : ℤ) (hn : n ≥ N) : a.seq n < c' + ε := by
          induction n, hn using Int.le_induction with
          | base          => exact hltreal
          | succ k hle ih =>
          specialize hmono k (by grind)
          linarith
        specialize hgreater n (by grind)
        grind
      · have hgeinf := Sequence.ge_inf (n:=n) hn.1
        rw [← heq] at hgeinf
        have hlesupreal := EReal.coe_le_coe_iff.mp hgeinf
        grind
  · have htop' := sInf_eq_top.mp htop
    contrapose! htop'
    use (a:Sequence) a.m
    constructor
    · simp_all; use a.m
    · exact EReal.real_neq_infty (a.seq a.m)
  · exact absurd hbot (Sequence.bddBelow_not_bot hbound)

theorem Sequence.convergent_iff_bounded_of_monotone {a:Sequence} (ha: a.IsMonotone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · intro hconverge
    exact Sequence.bounded_of_convergent hconverge
  · intro hbounded
    obtain ⟨habove, hbelow⟩ := (Sequence.bounded_iff _).mp hbounded
    exact Sequence.convergent_of_monotone habove ha

theorem Sequence.bounded_iff_convergent_of_antitone {a:Sequence} (ha: a.IsAntitone) :
    a.Convergent ↔ a.IsBounded := by
  constructor
  · intro hconverge
    exact Sequence.bounded_of_convergent hconverge
  · intro hbounded
    obtain ⟨habove, hbelow⟩ := (Sequence.bounded_iff _).mp hbounded
    exact Sequence.convergent_of_antitone hbelow ha

/-- Example 6.3.9 -/
noncomputable abbrev Example_6_3_9 (n:ℕ) := ⌊ Real.pi * 10^n ⌋ / (10:ℝ)^n

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).IsMonotone := by
  intro n hn
  simp_all
  lift n to ℕ using (by omega)
  simp_all
  rw [if_pos (by grind)]
  unfold Example_6_3_9
  rw [le_div_iff₀ (by positivity)]
  rw [pow_succ]
  field_simp
  norm_cast
  rw [Int.le_floor]
  push_cast
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  apply Int.floor_le

/-- Example 6.3.9 -/
lemma Real.rational_approx_le (r:ℝ) (n:ℕ) : ⌊r * 10^n⌋ / (10^n : ℝ) ≤ r := by
  field_simp
  apply Int.floor_le

example : (Example_6_3_9:Sequence).BddAboveBy 4 := by
  have hpilt4 : Real.pi ≤ 4 := Real.pi_lt_four

  sorry

/-- Example 6.3.9 -/
example : (Example_6_3_9:Sequence).Convergent := by sorry

/-- Example 6.3.9 -/
example : lim (Example_6_3_9:Sequence) ≤ 4 := by sorry

/-- Proposition 6.3.1-/
theorem lim_of_exp {x:ℝ} (hpos: 0 < x) (hbound: x < 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Convergent ∧ lim ((fun (n:ℕ) ↦ x^n):Sequence) = 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ x^n):Sequence)
  have why : a.IsAntitone := sorry
  have hbound : a.BddBelowBy 0 := by intro n _; positivity
  have hbound' : a.BddBelow := by use 0
  have hconv := a.convergent_of_antitone hbound' why
  set L := lim a
  have : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = x * L := by
    rw [←(a.lim_smul x hconv).2]; congr; ext n; rfl
    simp [a, pow_succ', HSMul.hSMul, SMul.smul]
  have why2 : lim ((fun (n:ℕ) ↦ x^(n+1)):Sequence) = lim ((fun (n:ℕ) ↦ x^n):Sequence) := by sorry
  convert_to x * L = 1 * L at why2; simp [a,L]
  have hx : x ≠ 1 := by grind
  simp_all [-one_mul]

/-- Exercise 6.3.4 -/
theorem lim_of_exp' {x:ℝ} (hbound: x > 1) : ¬((fun (n:ℕ) ↦ x^n):Sequence).Convergent := by sorry

end Chapter6
