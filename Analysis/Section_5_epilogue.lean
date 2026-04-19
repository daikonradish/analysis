import Mathlib.Tactic
import Analysis.Section_5_6

/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers {name}`Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers {lean}`ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers {lean}`ℚ`.

From this point onwards, {name}`Chapter5.Real` will be deprecated, and we will use the standard real
numbers {lean}`ℝ` instead.  In particular, one should use the full Mathlib API for {lean}`ℝ` for all
subsequent chapters, in lieu of the {name}`Chapter5.Real` API.

Filling the {syntax term}`sorry`s here requires both the {name}`Chapter5.Real` API and the Mathlib API for the standard
real numbers {lean}`ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

namespace Chapter5


@[ext]
structure DedekindCut where
  E : Set ℚ
  nonempty : E.Nonempty
  bounded : BddAbove E
  lower: IsLowerSet E
  nomax : ∀ q ∈ E, ∃ r ∈ E, r > q

theorem isLowerSet_iff (E: Set ℚ) : IsLowerSet E ↔ ∀ q r, r < q → q ∈ E → r ∈ E :=
  isLowerSet_iff_forall_lt

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

lemma Real.toSet_Rat_nonempty (x:Real) : x.toSet_Rat.Nonempty := by
  obtain ⟨q, hql, hqr⟩ := @Real.rat_between (x-1) x (by linarith)
  use q
  unfold toSet_Rat; simpa

lemma Real.toSet_Rat_bounded (x:Real) : BddAbove x.toSet_Rat := by
  obtain ⟨q, hql, hqr⟩ := @Real.rat_between x (x+1) (by linarith)
  use q
  unfold toSet_Rat
  intro z hz
  simp at hz
  have : (z:Real) ≤ (q:Real) := by linarith
  exact_mod_cast this

lemma Real.toSet_Rat_lower (x:Real) : IsLowerSet x.toSet_Rat := by
  rw [isLowerSet_iff]
  intro q r hrq hqmem
  unfold toSet_Rat at *
  simp at *
  have : (r : Real) < (q : Real) := by exact_mod_cast hrq
  linarith

lemma Real.toSet_Rat_nomax {x:Real} : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hqmem
  unfold toSet_Rat at *
  simp at hqmem
  obtain ⟨r, hrl, hrr⟩ := @Real.rat_between (q:Real) x hqmem
  use r
  constructor
  · simpa
  · exact_mod_cast hrl

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

lemma DedekindCut.toSet_Real_nonempty (c: DedekindCut) : c.toSet_Real.Nonempty := by
  unfold toSet_Real
  obtain ⟨x, hx⟩ := c.nonempty
  use (x:Real)
  simpa

lemma DedekindCut.toSet_Real_bounded (c: DedekindCut) : BddAbove c.toSet_Real := by
  unfold toSet_Real
  obtain ⟨x, hx⟩ := c.bounded
  use x
  intro a ha
  simp at ha
  obtain ⟨z, hz⟩ := ha
  have := hx hz.1
  rw [← hz.2]
  exact_mod_cast this

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

lemma DedekindCut.toReal_isLUB (c: DedekindCut) : IsLUB c.toSet_Real c.toReal :=
  ExtendedReal.sSup_of_bounded c.toSet_Real_nonempty c.toSet_Real_bounded

noncomputable abbrev Real.equivCut : Real ≃ DedekindCut where
  toFun := toCut
  invFun := DedekindCut.toReal
  left_inv := by
    intro y
    unfold DedekindCut.toReal
    unfold DedekindCut.toSet_Real
    apply le_antisymm
    · rw [csSup_le_iff]
      · intro z hz
        simp at hz
        obtain ⟨x, hx, rfl⟩ := hz
        linarith
      · exact DedekindCut.toSet_Real_bounded y.toCut
      · exact DedekindCut.toSet_Real_nonempty y.toCut
    · rw [le_csSup_iff]
      · intro b hb
        simp at hb
        unfold toSet_Rat at hb
        by_contra! h'
        obtain ⟨r, hrl, hrr⟩ := @Real.rat_between b y h'
        have := hb ⟨r, hrr, rfl⟩; simp at this
        linarith
      · exact DedekindCut.toSet_Real_bounded y.toCut
      · exact DedekindCut.toSet_Real_nonempty y.toCut
  right_inv := by
    intro c
    ext y
    simp only [DedekindCut.toReal, Real.toSet_Rat, DedekindCut.toSet_Real]
    have hlub := c.toReal_isLUB
    simp [DedekindCut.toSet_Real] at hlub
    constructor
    · intro h
      obtain ⟨x, ⟨r, hr, rfl⟩, hyr⟩ := hlub.exists_between h
      simp at hyr
      exact c.lower (le_of_lt (by exact_mod_cast hyr.1)) hr
    · intro h
      simp
      obtain ⟨r, hr, hyr⟩ := c.nomax y h
      have hyr' : (y:Real) < (r:Real) := by exact_mod_cast hyr
      have hssup := hlub.1 ⟨r, hr, rfl⟩
      linarith


end Chapter5

/-- Now to develop analogous results for the Mathlib reals. -/

abbrev Real.toSet_Rat (x:ℝ) : Set ℚ := { q | (q:ℝ) < x }

lemma Real.toSet_Rat_nonempty (x:ℝ) : x.toSet_Rat.Nonempty := by
  unfold Real.toSet_Rat
  have : x - 1 < x := by linarith
  obtain ⟨y, hyl, hyr⟩ := exists_rat_btwn this
  use y
  simp_all

lemma Real.toSet_Rat_bounded (x:ℝ) : BddAbove x.toSet_Rat := by
  unfold Real.toSet_Rat
  have : x < x + 1 := by linarith
  obtain ⟨y, hyl, hyr⟩ := exists_rat_btwn this
  use y
  simp_all
  intro z hz; simp at hz
  have : (z:ℝ) ≤ y := by linarith
  exact_mod_cast this

lemma Real.toSet_Rat_lower (x:ℝ) : IsLowerSet x.toSet_Rat := by
  intro q r hrq hqmem
  unfold toSet_Rat at *
  simp at *
  rify at hrq
  linarith

lemma Real.toSet_Rat_nomax (x:ℝ) : ∀ q ∈ x.toSet_Rat, ∃ r ∈ x.toSet_Rat, r > q := by
  intro q hqmem
  unfold toSet_Rat at *
  simp at hqmem
  obtain ⟨r, hrl, hrr⟩ := exists_rat_btwn hqmem
  use r
  constructor
  · simpa
  · exact_mod_cast hrl

abbrev Real.toCut (x:ℝ) : Chapter5.DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

namespace Chapter5

abbrev DedekindCut.toSet_R (c: DedekindCut) : Set ℝ := (fun (q:ℚ) ↦ (q:ℝ)) '' c.E

lemma DedekindCut.toSet_R_nonempty (c: DedekindCut) : c.toSet_R.Nonempty := by
  unfold DedekindCut.toSet_R
  obtain ⟨x, hx⟩ := c.nonempty
  use x
  simp_all


lemma DedekindCut.toSet_R_bounded (c: DedekindCut) : BddAbove c.toSet_R := by
  unfold DedekindCut.toSet_R
  obtain ⟨x, hx⟩ := c.bounded
  use x
  intro a ha
  simp at ha
  obtain ⟨z, hz⟩ := ha
  have := hx hz.1
  rw [← hz.2]
  exact_mod_cast this

noncomputable abbrev DedekindCut.toR (c: DedekindCut) : ℝ := sSup c.toSet_R

lemma DedekindCut.toR_isLUB (c: DedekindCut) : IsLUB c.toSet_R c.toR :=
  isLUB_csSup c.toSet_R_nonempty c.toSet_R_bounded

end Chapter5


noncomputable abbrev Real.equivCut : ℝ ≃ Chapter5.DedekindCut where
  toFun := _root_.Real.toCut
  invFun := Chapter5.DedekindCut.toR
  left_inv := by
    intro y
    apply le_antisymm
    · rw [csSup_le_iff]
      · intro z hz
        simp at hz
        obtain ⟨x, hx, rfl⟩ := hz
        linarith
      · exact Chapter5.DedekindCut.toSet_R_bounded (_root_.Real.toCut y)
      · exact Chapter5.DedekindCut.toSet_R_nonempty (_root_.Real.toCut y)
    · rw [le_csSup_iff]
      · intro b hb
        unfold Chapter5.DedekindCut.toSet_R at hb
        -- unfold Cha
        by_contra! h'
        obtain ⟨r, hrl, hrr⟩ := exists_rat_btwn h'
        have := hb ⟨r, hrr, rfl⟩; simp at this
        linarith
      · exact Chapter5.DedekindCut.toSet_R_bounded (_root_.Real.toCut y)
      · exact Chapter5.DedekindCut.toSet_R_nonempty (_root_.Real.toCut y)
  right_inv := by
    intro c
    ext y
    simp only [Chapter5.DedekindCut.toR, Real.toSet_Rat, Chapter5.DedekindCut.toSet_R]
    have hlub := Chapter5.DedekindCut.toR_isLUB c
    simp [Chapter5.DedekindCut.toSet_R] at hlub
    constructor
    · intro h
      obtain ⟨x, ⟨r, hr, rfl⟩, hyr⟩ := hlub.exists_between h
      simp at hyr
      exact c.lower (le_of_lt (by exact_mod_cast hyr.1)) hr
    · intro h
      simp
      obtain ⟨r, hr, hyr⟩ := c.nomax y h
      have hyr' : (y:Real) < (r:Real) := by exact_mod_cast hyr
      have hssup := hlub.1 ⟨r, hr, rfl⟩
      linarith


namespace Chapter5

/-- The isomorphism between the {name}`Chapter5.Real` numbers and the Mathlib reals. -/
noncomputable abbrev Real.equivR : Real ≃ ℝ := Real.equivCut.trans _root_.Real.equivCut.symm

lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
  simp only [equivR, Equiv.trans_apply, ←Equiv.apply_eq_iff_eq_symm_apply]
  rfl

-- In order to use this definition, we need some machinery
-----

-- We start by showing it works for ratCasts
theorem Real.equivR_ratCast {q: ℚ} : equivR q = (q: ℝ) := by
  simp
  unfold DedekindCut.toR
  unfold DedekindCut.toSet_R
  apply le_antisymm
  · rw [csSup_le_iff]
    · intro b hb
      simp at hb
      obtain ⟨x, hx, rfl⟩ := hb
      rify at hx
      linarith
    · exact DedekindCut.toSet_R_bounded (q:Real).toCut
    · exact DedekindCut.toSet_R_nonempty (q:Real).toCut
  · rw [le_csSup_iff]
    · intro b hb
      by_contra! h'
      obtain ⟨r, hrl, hrr⟩ := exists_rat_btwn h'
      have hrmem : r ∈ (q:Real).toCut.E := by
        simp
        exact_mod_cast hrr
      have := hb ⟨r, hrmem, rfl⟩; simp at this
      linarith
    · exact DedekindCut.toSet_R_bounded (q:Real).toCut
    · exact DedekindCut.toSet_R_nonempty (q:Real).toCut


lemma Real.equivR_nat {n: ℕ} : equivR n = (n: ℝ) := equivR_ratCast
lemma Real.equivR_int {n: ℤ} : equivR n = (n: ℝ) := equivR_ratCast

----
-- We then want to set up a way to convert from the Real `LIM` to the ℝ `Real.mk`
-- To do this we need a few things:

-- Convertion between the notions of Cauchy Sequences
theorem Sequence.IsCauchy.to_IsCauSeq {a: ℕ → ℚ} (ha: IsCauchy a) : IsCauSeq _root_.abs a := by
  unfold IsCauSeq
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε/2) (by positivity)
  use N
  intro j hj
  specialize hN j hj N (by linarith)
  linarith

-- Convertion of an `IsCauchy` to a `CauSeq`
abbrev Sequence.IsCauchy.CauSeq {a: ℕ → ℚ} : (ha: IsCauchy a) → CauSeq ℚ _root_.abs :=
  (⟨a, ·.to_IsCauSeq⟩)

-- We then set up the conversion from Sequence.Equiv to CauSeq.LimZero because
-- it is the equivalence relation
example {a b: CauSeq ℚ abs} : a ≈ b ↔ CauSeq.LimZero (a - b) := by rfl

theorem Sequence.Equiv.LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b) (h:Equiv a b)
  : CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
  unfold CauSeq.LimZero
  intro ε hε
  rw [Sequence.equiv_iff] at h
  obtain ⟨N, hN⟩ := h (ε/2) (by positivity)
  use N
  intro j hj
  specialize hN j hj
  simp
  linarith

-- We can now use it to convert between different functions in Real.mk
theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
  : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)

--lemma Real.const_seq_to_R (q : ℚ) : =

-- Both directions of the equivalence
theorem Sequence.Equiv_iff_LimZero {a b: ℕ → ℚ} (ha: IsCauchy a) (hb: IsCauchy b)
  : Equiv a b ↔ CauSeq.LimZero (ha.CauSeq - hb.CauSeq) := by
    refine ⟨(·.LimZero ha hb), ?_⟩
    intro hlimzero
    unfold CauSeq.LimZero at hlimzero
    rw [Sequence.equiv_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hlimzero ε hε
    use N
    intro j hj
    specialize hN j hj
    simp at hN
    linarith

----
-- We create some cauchy sequences with useful properties

-- We show that for any sequence, it will eventually be arbitrarily close to its LIM
open Real in
theorem Sequence.difference_approaches_zero {a: ℕ → ℚ} (ha: Sequence.IsCauchy a) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |LIM a - a n| ≤ (ε: ℚ) := by
  intro ε hε
  obtain ⟨b, hb, hbeq⟩ := Real.eq_lim (LIM a)
  rw [hbeq]
  rw [Real.LIM_eq_LIM ha hb, Sequence.equiv_iff] at hbeq
  simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq] at ha
  obtain ⟨N₁, hN₁⟩ := hbeq (ε/2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := ha   (ε/2) (by positivity)
  use max N₁ N₂
  intro n hn
  rw [Real.ratCast_def, Real.LIM_sub hb (Sequence.IsCauchy.const (a n))]
  change |LIM (fun j => b j - a n)| ≤ ε
  have hshrink : ∃ N : ℕ, ∀ j ≥ N, |(fun j => b j - a n) j| ≤ ε := by
      use n+1
      intro j hj
      specialize hN₁ j (by omega)
      specialize hN₂ n (by omega) j (by omega)
      simp
      calc |b j - a n| = |(b j - a j) + (a j - a n)| := by abel_nf
                     _ ≤ |b j - a j| + |a j - a n|   := by exact abs_add_le _ _
                     _ = |a j - b j| + |a n - a j|   := by congr 1; exact Section_4_3.dist_symm (b j) (a j); exact Section_4_3.dist_symm (a j) (a n)
                     _ ≤ ε / 2 + ε / 2               := by linarith
                     _ = ε                           := by norm_num
  apply abs_le.mpr
  constructor
  · have hgt : ∃ N, ∀ j ≥ N, (-ε:Real) ≤ ((b j - a n):ℚ) := by
      obtain ⟨N, hN⟩ := hshrink
      use N
      intro j hj
      specialize hN j hj
      simp at hN
      exact_mod_cast (abs_le.mp hN).1
    exact Real.LIM_of_ge' (Sequence.IsCauchy.sub hb (Sequence.IsCauchy.const (a n))) hgt
  · have hlt : ∃ N, ∀ j ≥ N, ((b j - a n):ℚ) ≤ (ε:Real) := by
      obtain ⟨N, hN⟩ := hshrink
      use N
      intro j hj
      specialize hN j hj
      simp at hN
      exact_mod_cast (abs_le.mp hN).2
    exact Real.LIM_of_le' (Sequence.IsCauchy.sub hb (Sequence.IsCauchy.const (a n))) hlt

-- There exists a Cauchy sequence entirely above the LIM
theorem Real.exists_equiv_above {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, LIM a ≤ b n := by
    have hsqueeze : ∀ N : ℕ, ∃ q : ℚ,  LIM a < q ∧ q < LIM a + 1 / (N + 1) := by
      intro n
      have : n + 1 > 0 := by linarith
      have : ((n+1):Real) > 0 := by exact_mod_cast this
      have : 1 / ((n+1):Real) > 0 := by positivity
      exact @Real.rat_between (LIM a) (LIM a + 1 / (n + 1)) (by grind)
    have hdist (q : ℚ) (x y : Real) (hypos : y > 0) (hxq : x < q) (hxy : q < x + y) :
      |x - q| ≤ y := by
      apply abs_le.mpr; grind
    let b : ℕ → ℚ := fun n => (hsqueeze n).choose
    let hb := fun n => (hsqueeze n).choose_spec
    use b
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
      intro ε hε
      obtain ⟨M, hMpos, hMgt⟩ := @Real.le_mul' 1 (by positivity) (2 / ε)
      simp at hMgt
      have hshrink : ∀ n ≥ M, 1 / (n + 1) < ((ε / 2):Real) := by
        intro n hn
        field_simp at hMgt ⊢
        norm_cast at hMgt ⊢
        have : n + 1 > M := by linarith
        calc 2 < ε * (M:ℚ)     := by exact hMgt
             _ < ε * ((n+1):ℕ) := by gcongr
      use M
      intro j hj k hk
      simp only [b]
      obtain ⟨hjlimgt, hjn⟩ := hb j; set bj := (hsqueeze j).choose
      obtain ⟨hklimgt, hkn⟩ := hb k; set bk := (hsqueeze k).choose
      have hjdist := hdist bj (LIM a) (1 / (j+1)) (by grind) hjlimgt hjn
      have hkdist := hdist bk (LIM a) (1 / (k+1)) (by grind) hklimgt hkn
      have hjshrink := hshrink j (by linarith)
      have hkshrunk := hshrink k (by linarith)
      have hlt :  |(bj:Real) - (bk:Real)| ≤ (ε:Real)  := by calc
              _ = |(bj - LIM a) + (LIM a - bk)|   := by ring_nf!
              _ ≤ |bj - LIM a| + |LIM a - bk|     := by exact abs_add_le _ _
              _ = |LIM a - bj| + |LIM a - bk|     := by congr 1; exact abs_sub_comm (bj:Real) (LIM a)
              _ ≤ 1 / (j + 1) + 1 / (k + 1)       := by linarith
              _ ≤  ε / 2 + ε / 2                  := by linarith
              _ = ε                               := by norm_num
      exact_mod_cast hlt
    · rw [Sequence.equiv_iff]
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := Sequence.difference_approaches_zero ha (ε/2) (by positivity)
      obtain ⟨N₁, hN₁pos, hN₁gt⟩ := @Real.le_mul' 1 (by positivity) ((2 / ε):Real)
      simp at hN₁gt
      have hshrink : ∀ n ≥ N₁, 1 / (n + 1) < ((ε / 2):Real) := by
        intro n hn
        field_simp at hN₁gt ⊢
        have : n + 1 > N₁      := by linarith
        have : (n:Real) + (1:Real) > (N₁:Real)           := by exact_mod_cast this
        calc (2:Real) < (ε:Real) * (N₁:Real)             := by exact hN₁gt
                    _ < (ε:Real) * ((n:Real) + (1:Real)) := by nlinarith
      use max N₀ N₁
      intro n hn
      simp only [b]
      obtain ⟨hnlim, hnn⟩ := hb n; set bn := (hsqueeze n).choose
      have hndist := hdist bn (LIM a) (1 / (n+1)) (by grind) hnlim hnn
      specialize hshrink n (by omega)
      specialize hN₀ n (by omega)
      have : (((ε / 2):ℚ):Real) = (ε:Real) / (2:Real) := by norm_cast
      rw [this] at hN₀
      have hineq : |LIM a - (bn:Real)| < (ε:Real) / 2 := by linarith
      have hlt :   |((a n):Real) - (bn:Real)| ≤ (ε:Real) := by calc
               _ = |(((a n):Real) - LIM a) + (LIM a - (bn:Real))| := by ring_nf
               _ ≤ |((a n):Real) - LIM a| + |LIM a - (bn:Real)|   := by exact abs_add_le _ _
               _ = |LIM a - ((a n):Real)| + |LIM a - (bn:Real)|   := by rw [abs_sub_comm _ _]
               _ ≤ (ε:Real) / 2 + |LIM a - (bn:Real)|             := by grind
               _ ≤ (ε:Real) / 2 + (ε:Real) / 2                    := by linarith only [hineq]
               _ = ε                                              := by norm_num
      exact_mod_cast hlt
    · intro n
      simp only [b]
      obtain ⟨hnlim, hnn⟩ := hb n; set bn := (hsqueeze n).choose
      linarith

-- theorem Real.le_mul {ε:Real} (hε: ε.IsPos) (x:Real) : ∃ M:ℕ, M > 0 ∧ M * ε > x := by
-- There exists a Cauchy sequence entirely below the LIM
set_option maxHeartbeats 800000 in
theorem Real.exists_equiv_below {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : ∃(b: ℕ → ℚ), Sequence.IsCauchy b ∧ Sequence.Equiv a b ∧ ∀n, b n ≤ LIM a := by
    have hsqueeze : ∀ N : ℕ, ∃ q : ℚ,  LIM a - 1 / (N + 1) < q ∧ q < LIM a := by
      intro n
      have : n + 1 > 0 := by linarith
      have : ((n+1):Real) > 0 := by exact_mod_cast this
      have : 1 / ((n+1):Real) > 0 := by positivity
      exact @Real.rat_between (LIM a - 1 / (n + 1)) (LIM a) (by grind)
    have hdist (q : ℚ) (x y : Real) (hypos : y > 0) (hxy : x - y < q) (hxq : q < x)  :
      |x - q| ≤ y := by
      apply abs_le.mpr; grind
    let b : ℕ → ℚ := fun n => (hsqueeze n).choose
    let hb := fun n => (hsqueeze n).choose_spec
    use b
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [Sequence.IsCauchy.coe, Section_4_3.dist_eq]
      intro ε hε
      obtain ⟨M, hMpos, hMgt⟩ := @Real.le_mul' 1 (by positivity) (2 / ε)
      simp at hMgt
      have hshrink : ∀ n ≥ M, 1 / (n + 1) < ((ε / 2):Real) := by
        intro n hn
        field_simp at hMgt ⊢
        norm_cast at hMgt ⊢
        have : n + 1 > M := by linarith
        calc 2 < ε * (M:ℚ)     := by exact hMgt
             _ < ε * ((n+1):ℕ) := by gcongr
      use M
      intro j hj k hk
      simp only [b]
      obtain ⟨hjn, hjlimgt⟩ := hb j; set bj := (hsqueeze j).choose
      obtain ⟨hkn, hklimgt⟩ := hb k; set bk := (hsqueeze k).choose
      have hjdist := hdist bj (LIM a) (1 / (j+1)) (by grind) hjn hjlimgt
      have hkdist := hdist bk (LIM a) (1 / (k+1)) (by grind) hkn hklimgt
      have hjshrink := hshrink j (by linarith)
      have hkshrunk := hshrink k (by linarith)
      have hlt :  |(bj:Real) - (bk:Real)| ≤ (ε:Real)  := by calc
              _ = |(bj - LIM a) + (LIM a - bk)|   := by ring_nf!
              _ ≤ |bj - LIM a| + |LIM a - bk|     := by exact abs_add_le _ _
              _ = |LIM a - bj| + |LIM a - bk|     := by congr 1; exact abs_sub_comm (bj:Real) (LIM a)
              _ ≤ 1 / (j + 1) + 1 / (k + 1)       := by linarith
              _ ≤ 1 / (j + 1) + (ε /2)            := by linarith only [hkshrunk]
              _ ≤ (ε /2) + (ε /2)                 := by linarith only [hjshrink]
              _ = ε                               := by norm_num
      exact_mod_cast hlt
    · rw [Sequence.equiv_iff]
      intro ε hε
      obtain ⟨N₀, hN₀⟩ := Sequence.difference_approaches_zero ha (ε/2) (by positivity)
      obtain ⟨N₁, hN₁pos, hN₁gt⟩ := @Real.le_mul' 1 (by positivity) ((2 / ε):Real)
      simp at hN₁gt
      have hshrink : ∀ n ≥ N₁, 1 / (n + 1) < ((ε / 2):Real) := by
        intro n hn
        field_simp at hN₁gt ⊢
        have : n + 1 > N₁      := by linarith
        have : (n:Real) + (1:Real) > (N₁:Real)           := by exact_mod_cast this
        calc (2:Real) < (ε:Real) * (N₁:Real)             := by exact hN₁gt
                    _ < (ε:Real) * ((n:Real) + (1:Real)) := by nlinarith
      use max N₀ N₁
      intro n hn
      simp only [b]
      obtain ⟨hnlim, hnn⟩ := hb n; set bn := (hsqueeze n).choose
      have hndist := hdist bn (LIM a) (1 / (n+1)) (by grind) hnlim hnn
      specialize hshrink n (by omega)
      specialize hN₀ n (by omega)
      have : (((ε / 2):ℚ):Real) = (ε:Real) / (2:Real) := by norm_cast
      rw [this] at hN₀
      have hineq : |LIM a - (bn:Real)| < (ε:Real) / 2 := by linarith
      have hlt :   |((a n):Real) - (bn:Real)| ≤ (ε:Real) := by calc
               _ = |(((a n):Real) - LIM a) + (LIM a - (bn:Real))| := by ring_nf
               _ ≤ |((a n):Real) - LIM a| + |LIM a - (bn:Real)|   := by exact abs_add_le _ _
               _ = |LIM a - ((a n):Real)| + |LIM a - (bn:Real)|   := by rw [abs_sub_comm _ _]
               _ ≤ (ε:Real) / 2 + |LIM a - (bn:Real)|             := by grind
               _ ≤ (ε:Real) / 2 + (ε:Real) / 2                    := by linarith only [hineq]
               _ = ε                                              := by norm_num
      exact_mod_cast hlt
    · intro n
      simp only [b]
      obtain ⟨hnlim, hnn⟩ := hb n; set bn := (hsqueeze n).choose
      linarith
----

-- useful theorems for the following proof
#check Real.mk_le
#check Real.mk_le_of_forall_le
#check Real.mk_const

-- Transform a `Real` to an `ℝ` by going through Cauchy Sequences
-- we can use the conversion of Real.mk_eq to use different sequences to show different parts
theorem Real.equivR_eq' {a: ℕ → ℚ} (ha: Sequence.IsCauchy a)
  : (LIM a).equivR = Real.mk ha.CauSeq := by
    by_cases hq: ∃(q: ℚ), q = LIM a
    · -- obtain ⟨q, hqlim⟩ := hq
      -- lemma Real.equivR_iff (x : Real) (y : ℝ) : y = Real.equivR x ↔ y.toCut = x.toCut := by
      --rw [Real.equivR_iff]
      --rw [Real.mk_const]
      -- -- We can now use it to convert between different functions in Real.mk-
      -- theorem Real.mk_eq_mk {a b: ℕ → ℚ} (ha : Sequence.IsCauchy a) (hb : Sequence.IsCauchy b) (hab: Sequence.Equiv a b)
      -- : Real.mk ha.CauSeq = Real.mk hb.CauSeq := Real.mk_eq.mpr (hab.LimZero ha hb)
      -- have hqlim' := hqlim
      -- rw [Real.ratCast_def, Real.LIM_eq_LIM (Sequence.IsCauchy.const q) ha] at hqlim
      -- have hqrealmk := Real.mk_eq_mk (Sequence.IsCauchy.const q) ha hqlim
      -- rw [← hqrealmk]
      sorry
    show sSup (Rat.cast '' (LIM a).toSet_Rat) = _
    refine IsLUB.csSup_eq ⟨?_, ?_⟩ (Set.Nonempty.image _ <| Real.toSet_Rat_nonempty _)
    · -- show that `Real.mk ha.CauSeq` is an upper bound
      intro _ hy
      obtain ⟨y, hy, h⟩ := Set.mem_image _ _ _ |>.mp hy
      rw [← h, show (y: ℝ) = Real.mk (CauSeq.const _ y) from rfl]
      sorry
    -- show that for any other upper bound, `Real.mk ha.CauSeq` is smaller
    intro M hM
    sorry
#check CauSeq.const
#check Real.mk
lemma Real.equivR_eq (x: Real) : ∃(a : ℕ → ℚ) (ha: Sequence.IsCauchy a),
  x = LIM a ∧ x.equivR = Real.mk ha.CauSeq := by
    obtain ⟨a, ha, rfl⟩ := x.eq_lim
    exact ⟨a, ha, rfl, equivR_eq' ha⟩

/-- The isomorphism preserves order and ring operations. -/
noncomputable abbrev Real.equivR_ordered_ring : Real ≃+*o ℝ where
  toEquiv := equivR
  map_add' := by sorry
  map_mul' := by sorry
  map_le_map_iff' := by sorry

-- helpers for converting properties between Real and ℝ
lemma Real.equivR_map_mul {x y : Real} : equivR (x * y) = equivR x * equivR y :=
  equivR_ordered_ring.map_mul _ _

lemma Real.equivR_map_inv {x: Real} : equivR (x⁻¹) = (equivR x)⁻¹ :=
  map_inv₀ equivR_ordered_ring _

theorem Real.equivR_map_pos {x: Real} : 0 < x ↔ 0 < equivR x := by sorry

theorem Real.equivR_map_nonneg {x: Real} : 0 ≤ x ↔ 0 ≤ equivR x := by sorry


-- Showing equivalence of the different pows
theorem Real.pow_of_equivR (x:Real) (n:ℕ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.zpow_of_equivR (x:Real) (n:ℤ) : equivR (x^n) = (equivR x)^n := by
  sorry

theorem Real.ratPow_of_equivR (x:Real) (q:ℚ) : equivR (x^q) = (equivR x)^(q:ℝ) := by
  sorry


end Chapter5
