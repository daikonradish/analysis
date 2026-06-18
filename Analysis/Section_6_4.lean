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

/-REINSERT HERE!!!  https://gist.github.com/daikonradish/20c0e097f74ad55d109a2cc2b114cb1c-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/

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


/- REINSERT HERE!!!!!-/
/-https://gist.github.com/daikonradish/b3ba1b4319164d0dbd2f87647e8b5bc8-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/
/- REINSERT HERE!!!!!-/

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
    have ⟨habv, hblw⟩ := (Sequence.bounded_iff a).mp (Sequence.bounded_of_convergent hconv)
    rw [Sequence.tendsTo_iff] at htends
    constructor
    · obtain ⟨x, hreal⟩ | htop | hbot := EReal.def a.liminf 
      · rw [← hreal]
        norm_cast 
        -- have to do some real work here unfortundately
        sorry
      · exact absurd htop (Sequence.liminf_of_bddAbove_ne_top habv)
      · exact absurd hbot (Sequence.liminf_of_bddBelow_ne_bot hblw)
    · obtain ⟨x, hreal⟩ | htop | hbot := EReal.def a.limsup 
      · sorry
      · exact absurd htop (Sequence.limsup_of_bddAbove_ne_top habv) 
      · exact absurd hbot (Sequence.limsup_of_bddBelow_ne_bot hblw) 
  · 
    sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.sup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.sup ≤ b.sup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.inf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.inf ≤ b.inf := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.limsup_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.limsup ≤ b.limsup := by sorry

/-- Lemma 6.4.13 (Comparison principle) / Exercise 6.4.4 -/
theorem Sequence.liminf_mono {a b:Sequence} (hm: a.m = b.m) (hab: ∀ n ≥ a.m, a n ≤ b n) :
    a.liminf ≤ b.liminf := by sorry

/-- Corollary 6.4.14 (Squeeze test) / Exercise 6.4.5 -/
theorem Sequence.lim_of_between {a b c:Sequence} {L:ℝ} (hm: b.m = a.m ∧ c.m = a.m)
  (hab: ∀ n ≥ a.m, a n ≤ b n ∧ b n ≤ c n) (ha: a.TendsTo L) (hb: c.TendsTo L) :
    b.TendsTo L := by sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ 2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ -2/(n+1:ℝ)):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (-1)^n/(n+1:ℝ) + 1 / (n+1)^2):Sequence).TendsTo 0 := by
  sorry

/-- Example 6.4.15 -/
example : ((fun (n:ℕ) ↦ (2:ℝ)^(-(n:ℤ))):Sequence).TendsTo 0 := by
  sorry

abbrev Sequence.abs (a:Sequence) : Sequence where
  m := a.m
  seq n := |a n|
  vanish n hn := by simp [a.vanish n hn]


/-- Corollary 6.4.17 (Zero test for sequences) / Exercise 6.4.7 -/
theorem Sequence.tendsTo_zero_iff (a:Sequence) :
  a.TendsTo (0:ℝ) ↔ a.abs.TendsTo (0:ℝ) := by
  sorry

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
theorem Sequence.sup_not_strict_mono : ∃ (a b:ℕ → ℝ), (∀ n, a n < b n) ∧ ¬ (a:Sequence).sup < (b:Sequence).sup := by
  sorry

/- Exercise 6.4.7 -/
def Sequence.tendsTo_real_iff :
  Decidable (∀ (a:Sequence) (x:ℝ), a.TendsTo x ↔ a.abs.TendsTo x) := by
  -- The first line of this construction should be `apply isTrue` or `apply isFalse`.
  sorry

/-- This definition is needed for Exercises 6.4.8 and 6.4.9. -/
abbrev Sequence.ExtendedLimitPoint (a:Sequence) (x:EReal) : Prop := if x = ⊤ then ¬ a.BddAbove else if x = ⊥ then ¬ a.BddBelow else a.LimitPoint x.toReal

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_limsup (a:Sequence) : a.ExtendedLimitPoint a.limsup := by sorry

/-- Exercise 6.4.8 -/
theorem Sequence.extended_limit_point_of_liminf (a:Sequence) : a.ExtendedLimitPoint a.liminf := by sorry

theorem Sequence.extended_limit_point_le_limsup {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≤ a.limsup := by sorry

theorem Sequence.extended_limit_point_ge_liminf {a:Sequence} {L:EReal} (h:a.ExtendedLimitPoint L): L ≥ a.liminf := by sorry

/-- Exercise 6.4.9 -/
theorem Sequence.exists_three_limit_points : ∃ a:Sequence, ∀ L:EReal, a.ExtendedLimitPoint L ↔ L = ⊥ ∨ L = 0 ∨ L = ⊤ := by sorry

/-- Exercise 6.4.10 -/
theorem Sequence.limit_points_of_limit_points {a b:Sequence} {c:ℝ} (hab: ∀ n ≥ b.m, a.LimitPoint (b n)) (hbc: b.LimitPoint c) : a.LimitPoint c := by sorry


end Chapter6
