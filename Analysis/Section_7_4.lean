import Mathlib.Tactic
import Analysis.Section_7_3
/-!
# Analysis I, Section 7.4: Rearrangement of series

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- Rearrangement of non-negative or absolutely convergent series.
-/

namespace Chapter7

theorem Series.sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0) : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind

/-- Proposition 7.4.1 -/
theorem Series.converges_of_permute_nonneg {a:ℕ → ℝ} (ha: (a:Series).nonneg) (hconv: (a:Series).converges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n) : Series).converges ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set af : ℕ → ℝ := fun n ↦ a (f n)
  have haf : (af:Series).nonneg := by
    intro n; by_cases h : n ≥ 0 <;> simp [h, af]
    specialize ha (f n.toNat); grind
  set S := (a:Series).partial
  set T := (af:Series).partial
  have hSmono : Monotone S := Series.partial_of_nonneg ha
  have hTmono : Monotone T := Series.partial_of_nonneg haf
  set L := iSup S
  set L' := iSup T
  have hSBound : ∃ Q, ∀ N, S N ≤ Q := (converges_of_nonneg_iff ha).mp hconv
  suffices : (∃ Q, ∀ M, T M ≤ Q) ∧ L = L'
  . have Ssum : L = (a:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L]
      apply tendsto_atTop_isLUB hSmono (isLUB_csSup _ _)
      . use (S 0); aesop
      choose Q hQ using hSBound; use Q; simp [upperBounds, hQ]
    have Tsum : L' = (af:Series).sum := by
      symm; apply sum_of_converges; simp [convergesTo, L']
      apply tendsto_atTop_isLUB hTmono (isLUB_csSup _ _)
      . use (T 0); aesop
      choose Q hQ using this.1; use Q; simp [upperBounds, hQ]
    simp [←Ssum, ←Tsum, this.2, converges_of_nonneg_iff haf]
    convert this.1
  have hTL (M:ℤ) : T M ≤ L := by
    by_cases hM : M ≥ 0
    swap
    . have hM' : M < 0 := by linarith
      simp [T, Series.partial, hM']
      convert le_ciSup (f := S) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
    set Y := Finset.Iic M.toNat
    have hN : ∃ N, ∀ m ∈ Y, f m ≤ N := by
      use (Y.image f).sup id; intro m hm
      apply Finset.le_sup (f := id); grind
    choose N hN using hN
    calc
      _ = ∑ m ∈ Y, af m := by simp [T, Series.partial, af]; exact sum_eq_sum af hM
      _ = ∑ n ∈ f '' Y, a n := by symm; convert Finset.sum_image (by solve_by_elim [hf.injective]); simp
      _ ≤ ∑ n ∈ .Iic N, a n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro _ _; aesop
        intro i _ _; specialize ha i; aesop
      _ = S N := by simp [S, Series.partial]; symm; apply sum_eq_sum (N:=N) a; positivity
      _ ≤ L := by apply le_ciSup _ (N:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hSBound]
  have hTbound : ∃ Q, ∀ M, T M ≤ Q := by use L
  simp [hTbound]
  have hSL' (N:ℤ) : S N ≤ L' := by
    by_cases hN : N ≥ 0
    swap
    . have hN' : N < 0 := by linarith
      simp [S, Series.partial, hN']
      convert le_ciSup (f := T) ?_ (-1)
      simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
    set X := Finset.Iic N.toNat
    have hM : ∃ M, ∀ n ∈ X, ∃ m, f m = n ∧ m ≤ M := by
      use (X.preimage f (Set.injOn_of_injective hf.1)).sup id
      intro n hn; choose m hm using hf.2 n
      refine ⟨ _, hm, ?_ ⟩
      apply Finset.le_sup (f := id)
      simp [Finset.mem_preimage, hm, hn]
    choose M hM using hM
    have sum_eq_sum (b:ℕ → ℝ) {N:ℤ} (hN: N ≥ 0)
      : ∑ n ∈ .Icc 0 N, (if 0 ≤ n then b n.toNat else 0) = ∑ n ∈ .Iic N.toNat, b n := by
      convert Finset.sum_image (g := Int.ofNat) (by simp)
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
    calc
      _ = ∑ n ∈ X, a n := by simp [S, sum_eq_sum, hN, X]
      _ = ∑ n ∈ ((Finset.Iic M).filter (f · ∈ X)).image f, a n := by
        congr; ext; simp; constructor
        . intro h; obtain ⟨ m, rfl, hm' ⟩ := hM _ h; use m
        rintro ⟨ _, ⟨ _, _⟩, rfl ⟩; simp_all
      _ ≤ ∑ m ∈ .Iic M, af m := by
        rw [Finset.sum_image (by solve_by_elim [hf.injective])]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        . aesop
        intro i _ _; specialize haf i; aesop
      _ = T M := by simp [T, Series.partial, af]; symm; apply sum_eq_sum af; positivity
      _ ≤ L' := by apply le_ciSup _ (M:ℤ); simp [BddAbove, Set.Nonempty, upperBounds, hTbound]
  linarith [ciSup_le hSL', ciSup_le hTL]

/-- Example 7.4.2 -/
theorem Series.zeta_2_converges : (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).converges := by
  set ζ₂ := (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series) with hζ₂def
  have hζ₂nonneg : ζ₂.nonneg := by
    intro n; unfold ζ₂; simp
    split_ifs
    · field_simp; grind
    · rfl
  have hζ'conv := (Series.converges_qseries 2 (by norm_num)).mpr (by norm_num)
  set ζ' := (mk' (m := 1) fun n ↦ 1 / (n:ℝ) ^ (2:ℝ) : Series) with hζdef
  have hζ'sum := ζ'.convergesTo_sum hζ'conv
  have hζ'nonneg : ζ'.nonneg := by
    intro n; unfold ζ'; simp
    split_ifs
    · field_simp; grind
    · rfl
  apply (ζ₂.converges_of_nonneg_iff hζ₂nonneg).mpr
  use ζ'.sum + 1
  have hζ'partial := ζ'.partial_le_sum_of_nonneg hζ'nonneg hζ'conv
  suffices ∀ N, ζ₂.partial  N ≤  ζ'.partial N + 1 by grind
  intro N
  unfold Series.partial
  change ∑ n ∈ Finset.Icc 0 N, ζ₂.seq n ≤ ∑ n ∈ Finset.Icc 1 N, ζ'.seq n + 1
  unfold ζ₂ ζ'
  rw [Finset.sum_ite_of_true (by grind)]
  by_cases! hNlt0 : N < 0
  · rw [Finset.Icc_eq_empty (by grind), Finset.Icc_eq_empty (by grind)]
    simp
  · by_cases! hN0 : N = 0
    · rw [hN0]
      simp
    · by_cases! hN1 : N = 1
      · have : N = 0 + 1 := by linarith
        rw [this, sum_of_nonempty (by grind)]; simp; grind
      · have hNgt1 : N > 1 := by grind
        have hinsert : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
          ext n; grind
        rw [hinsert, Finset.sum_insert (by grind)]
        simp
        conv_rhs => rw [add_comm, Finset.sum_ite_of_true (by grind)]
        apply add_le_add
        · rfl
        · apply Finset.sum_le_sum
          intro n hn; simp at hn
          field_simp
          rw [le_div_iff₀ (by norm_cast; nlinarith [hn.1])]
          simp; norm_cast; grind

def τ : ℕ → ℕ := fun n => if Even n then n + 1 else n - 1

lemma τbij : Function.Bijective τ := by
  constructor
  · intro a b hab
    simp only [τ] at hab
    split_ifs at hab with h1 h2 <;> grind
  · intro n
    by_cases! hevodd : Even n
    · use (n+1)
      simp only [τ]; rw [if_neg (by grind)]
      grind
    · use (n-1)
      simp only [τ]; rw [if_pos (by grind)]
      grind

lemma hτperm : (fun n: ℕ => (fun k:ℕ ↦ 1/((k:ℝ)+1)^2) (τ n)) = (fun n:ℕ => if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2) := by
  ext n
  simp only [τ]
  by_cases! hevodd : Even n
  · rw [if_pos hevodd, if_pos hevodd]
    simp; grind
  · rw [if_neg hevodd, if_neg hevodd]
    simp; rw [Nat.cast_sub (by grind)]
    simp

theorem Series.permuted_zeta_2_converges :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).converges := by
  rw [← hτperm]
  set a := (fun k:ℕ ↦ 1/((k:ℝ)+1)^2) with hadef
  have hconv : (a:Series).converges := by exact Series.zeta_2_converges
  have ha : (a:Series).nonneg := by
    intro n; unfold a; simp
    split_ifs
    · field_simp; grind
    · rfl
  have := Series.converges_of_permute_nonneg ha hconv τbij
  exact this.1



theorem Series.permuted_zeta_2_eq_zeta_2 :
  (fun n:ℕ ↦ if Even n then 1/(n+2:ℝ)^2 else 1/(n:ℝ)^2 : Series).sum = (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series).sum := by
  rw [← hτperm]
  set a := (fun k:ℕ ↦ 1/((k:ℝ)+1)^2) with hadef
  have hconv : (a:Series).converges := by exact Series.zeta_2_converges
  have ha : (a:Series).nonneg := by
    intro n; unfold a; simp
    split_ifs
    · field_simp; grind
    · rfl
  have := Series.converges_of_permute_nonneg ha hconv τbij
  exact this.2.symm

/-- Proposition 7.4.3 (Rearrangement of series) -/
theorem Series.absConverges_of_permute {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n) : Series).sum := by
  -- This proof is written to follow the structure of the original text.
  set L := (a:Series).abs.sum
  have hconv := converges_of_absConverges ha
  unfold absConverges at ha
  have habs : (fun n ↦ |a (f n)| : Series).converges ∧ L = (fun n ↦ |a (f n)| : Series).sum := by
    convert converges_of_permute_nonneg (a := fun n ↦ |a n|) _ _ hf using 3
    . simp; ext n; by_cases n ≥ 0 <;> grind
    . intro n; by_cases h: n ≥ 0 <;> simp [h]
    convert ha with n; by_cases n ≥ 0 <;> grind
  set L' := (a:Series).sum
  set af : ℕ → ℝ := fun n ↦ a (f n)
  suffices : (af:Series).convergesTo L'
  . simp [sum_of_converges this, absConverges]
    convert habs.1 with n; by_cases n ≥ 0 <;> grind
  simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds]
  intro ε hε
  rw [converges_iff_tail_decay] at ha
  choose N₁ hN₁ ha using ha _ (half_pos hε); simp at hN₁
  have : ∃ N ≥ N₁, |(a:Series).partial N - L'| < ε/2 := by
    apply convergesTo_sum at hconv
    simp [convergesTo, LinearOrderedAddCommGroup.tendsto_nhds] at hconv
    choose N hN using hconv _ (half_pos hε)
    use max N N₁, (by grind); apply hN; grind
  choose N hN hN2 using this
  have hNpos : N ≥ 0 := by linarith
  let finv : ℕ → ℕ := Function.invFun f
  have : ∃ M, ∀ n ≤ N.toNat, finv n ≤ M := by
    use ((Finset.Iic (N.toNat)).image finv).sup id
    intro n hn
    apply Finset.le_sup (f := id); simp [Finset.mem_image]; use n, hn; rfl
  choose M hM using this; use M; intro M' hM'
  have hM'_pos : M' ≥ 0 := by linarith
  have why : (Finset.Iic M'.toNat).image f ⊇ .Iic N.toNat := by
    intro x hx
    simp at hx ⊢
    specialize hM x hx
    use finv x
    constructor
    · grind
    · unfold finv
      apply Function.invFun_eq
      apply hf.surjective
  set X : Finset ℕ := (Finset.Iic M'.toNat).image f \ .Iic N.toNat
  have claim : ∑ m ∈ .Iic M'.toNat, a (f m) = ∑ n ∈ .Iic N.toNat, a n + ∑ n ∈ X, a n := calc
    _ = ∑ n ∈ (Finset.Iic M'.toNat).image f , a n := by
      symm; apply Finset.sum_image; solve_by_elim [hf.1]
    _ = _ := by
      convert Finset.sum_union _ using 2
      . simp [X, why]
      . infer_instance
      rw [Finset.disjoint_right]; intro n hn; simp only [X, Finset.mem_sdiff] at hn; tauto
  choose q' hq using X.bddAbove
  set q := max q' N.toNat
  have why2 : X ⊆ Finset.Icc (N.toNat+1) q := by
    intro x hx
    have hx' := hx
    unfold X at hx
    simp at hx ⊢
    constructor
    · exact hx.2
    . unfold q
      apply le_max_of_le_left
      exact hq hx'
  have claim2 : |∑ n ∈ X, a n| ≤ ε/2 := calc
    _ ≤ ∑ n ∈ X, |a n| := X.abs_sum_le_sum_abs a
    _ ≤ ∑ n ∈ .Icc (N.toNat+1) q, |a n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg why2; simp
    _ ≤ ε/2 := by
      convert ha (N.toNat+1) _ q _ <;> try omega
      simp [hNpos]; rw [abs_of_nonneg (by positivity)]; symm
      convert Finset.sum_image (g := fun (n:ℕ) ↦ (n:ℤ)) (by simp) using 2
      ext x; simp; constructor
      . intro ⟨ _, _ ⟩; use x.toNat; omega
      grind
  calc
    _ ≤ |(af:Series).partial M' - (a:Series).partial N| + |(a:Series).partial N - L'| := abs_sub_le _ _ _
    _ < |(af:Series).partial M' - (a:Series).partial N| + ε/2 := by gcongr
    _ ≤ ε/2 + ε/2 := by
      gcongr; convert claim2
      simp [Series.partial, sum_eq_sum _ hM'_pos, sum_eq_sum _ hNpos]; grind
    _ = ε := by ring


/-- Example 7.4.4 -/
noncomputable abbrev Series.a_7_4_4 : ℕ → ℝ := fun n ↦ (-1:ℝ)^n / (n+2)

theorem Series.ex_7_4_4_conv : (a_7_4_4 : Series).converges := by
  set m := (0:ℤ)
  set a : {n // n ≥ m} → ℝ := fun n => 1 / (n+2)
  have ha : ∀ n, a n ≥ 0 := by
    intro n; unfold a; simp
    have hnm := n.property
    unfold m at hnm
    norm_cast at hnm ⊢
    grind
  have ha' : Antitone a := by
    intro x y hxy
    unfold a
    norm_cast
    refine (Rat.divInt_le_divInt ?_ ?_).mpr ?_
    · grind
    · grind
    · simpa
  have htt0 : Filter.atTop.Tendsto a (nhds 0) := by
    have hnon : Nonempty { n // n ≥ m } := by use m
    rw [Metric.tendsto_atTop]
    simp_rw [Real.dist_eq, sub_zero]
    intro ε hε
    choose N hN using exists_nat_gt (1/ε)
    use ⟨N, by grind⟩
    intro n hn
    rw [abs_of_nonneg (by grind)]
    unfold a
    rcases n with ⟨k, hk⟩
    have hn' : k ≥ (N : ℤ) := by exact hn
    simp at ⊢
    rw [inv_eq_one_div, div_lt_iff₀ (by positivity)]
    field_simp at hN
    suffices (N:ℝ) ≤ (k:ℝ) + 2 by nlinarith
    suffices (N:ℝ) ≤ (k:ℝ) by linarith
    norm_cast
  convert (Series.converges_of_alternating ha ha').mpr htt0 using 2
  ext n
  unfold m
  split_ifs with hpos
  · unfold Series.a_7_4_4 a
    simp
    rw [div_eq_mul_one_div, inv_eq_one_div]
    lift n to ℕ using (by omega)
    congr
  · rfl

theorem Series.ex_7_4_4_sum : (a_7_4_4 : Series).sum > 0 := by
  have hconv := Series.convergesTo_sum Series.ex_7_4_4_conv
  unfold Series.convergesTo at hconv
  set x := (a_7_4_4 : Series).sum
  set f := (a_7_4_4 : Series).partial
  suffices ∀ᶠ n in Filter.atTop, f n ≥ 1/6 by
    have hge := ge_of_tendsto hconv this
    linarith
  rw [Filter.eventually_atTop]
  use 1
  intro n hn
  lift n to ℕ using (by omega)
  induction' n using Nat.strong_induction_on with k ih
  by_cases! hk1 : k = 1
  · have hk1' : k = (0:ℤ) + 1 := by grind
    unfold f Series.partial; simp
    rw [hk1', sum_of_nonempty (by grind)]; simp
    unfold Series.a_7_4_4; norm_num
  · have hgt1 : k > 1 := by grind
    rcases Nat.even_or_odd k with heven | hodd
    · have hprev := ih (k-1) (by grind) (by grind)
      unfold f Series.partial at hprev ⊢
      simp at hprev ⊢
      have hkeq : k = (k-1) + (1:ℤ) := by grind
      rw [hkeq, sum_of_nonempty (by grind)]
      rw [Finset.sum_ite_of_true (by grind)] at hprev ⊢
      simp at hprev ⊢
      rw [Nat.cast_sub (by grind)] at hprev; simp at hprev
      suffices a_7_4_4 k ≥ 0 by linarith
      unfold Series.a_7_4_4
      field_simp; rw [zero_mul, Even.neg_one_pow heven]
      norm_num
    · have hprev := ih (k - 2) (by grind) (by grind)
      unfold f Series.partial at hprev ⊢
      simp at hprev ⊢
      have hkeq : k = ((k-2) + (1:ℤ)) + (1:ℤ) := by grind
      rw [hkeq, sum_of_nonempty (by grind), sum_of_nonempty (by grind)]
      rw [Finset.sum_ite_of_true (by grind)] at hprev ⊢
      rw [if_pos (by grind), if_pos (by grind)]; simp
      rw [Nat.cast_sub (by grind)] at hprev; simp at hprev
      suffices a_7_4_4 ((k:ℤ) - 2 + 1).toNat + a_7_4_4 ((k:ℤ) - 2 + 1 + 1).toNat ≥ 0 by linarith
      have hkge3 : k ≥ 3 := by grind
      have hidx1 : ((k:ℤ) - 2 + 1).toNat = k - 1 := by omega
      have hidx2 : ((k:ℤ) - 2 + 1 + 1).toNat = k := by omega
      rw [hidx1, hidx2]
      unfold Series.a_7_4_4
      have hsubeven : Even (k - 1) := by grind
      rw [Even.neg_one_pow hsubeven, Odd.neg_one_pow hodd]
      rw [Nat.cast_sub (by grind)]; ring_nf
      field_simp; rw [zero_mul, zero_mul]
      grind

abbrev Series.f_7_4_4 : ℕ → ℕ := fun n ↦ if n % 3 = 0 then 2 * (n/3) else 4 * (n/3) + 2 * (n % 3) - 1

theorem Series.f_7_4_4_bij : Function.Bijective f_7_4_4 := by
  constructor
  · intro a b hab
    unfold Series.f_7_4_4 at hab
    split_ifs at hab with h1 h2 <;> grind
  · intro a
    unfold Series.f_7_4_4
    rcases a.even_or_odd with heven | ⟨k, hk⟩
    · use 3 * (a / 2); grind
    · rcases k.even_or_odd with ⟨m, hm⟩ | ⟨m, hm⟩
      · use 3*m+1
        grind
      · use 3*m+2
        grind

noncomputable abbrev c : ℕ → ℝ := fun k => -1/((2*k+2)*(4*k+3)*(4*k+5))

lemma Series.f_7_4_4.get_triplet (k:ℕ) :
  Series.f_7_4_4 (3*k)   = 2*k   ∧
  Series.f_7_4_4 (3*k+1) = 4*k+1 ∧
  Series.f_7_4_4 (3*k+2) = 4*k+3 := by
  unfold Series.f_7_4_4
  refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> grind

lemma Series.f_7_4_4.triplet_bound (k n :ℕ) (h : 3*k+2 ≤ n) (h' : n ≤ 3*k+4) :
  |(fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).partial n - (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).partial (3*k+2)| ≤ 1 / ((k:ℝ)+2) := by
  have hn : n = 3*k+2 ∨ n = 3*k+3 ∨ n = 3*k+4 := by omega
  rcases hn with rfl | rfl | rfl
  · simp; grind
  · unfold Series.partial; simp
    rw [Finset.sum_ite_of_true (by grind), Finset.sum_ite_of_true (by grind)]
    rw [show (3 * (k:ℤ) + 3) = (3 * (k:ℤ) + 2) + 1 by linarith]
    rw [sum_of_nonempty (by grind)]
    simp; ring_nf
    rw [abs_mul, abs_pow, abs_neg, abs_of_pos (a:=1) (by norm_num), one_pow, mul_one]
    rw [show (3 + (k:ℤ) * 3).toNat = 3 + k * 3 by omega]
    simp; rw [abs_of_pos (by positivity)]
    field_simp; grind
  · unfold Series.partial; simp
    rw [Finset.sum_ite_of_true (by grind), Finset.sum_ite_of_true (by grind)]
    rw [show (3 * (k:ℤ) + 4) = ((3 * (k:ℤ) + 2) + 1) + 1 by linarith]
    rw [sum_of_nonempty (by grind), sum_of_nonempty (by grind)]
    ring_nf
    have h1 : |(2 + (f_7_4_4 (3 + (k:ℤ) * 3).toNat):ℝ)⁻¹ * (-1) ^ f_7_4_4 (3 + (k:ℤ) * 3).toNat| ≤ (2*(2 + (k:ℝ)))⁻¹ := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos (a:=1) (by norm_num), one_pow, mul_one]
      rw [show (3 + (k:ℤ) * 3).toNat = 3 + k * 3 by omega]
      simp; rw [abs_of_pos (by positivity)]
      field_simp; grind
    have h2 : |(2 + (f_7_4_4 (4 + (k:ℤ) * 3).toNat):ℝ)⁻¹ * (-1) ^ f_7_4_4 (4 + (k:ℤ) * 3).toNat| ≤ (2*(2 + (k:ℝ)))⁻¹ := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos (a:=1) (by norm_num), one_pow, mul_one]
      rw [show (4 + (k:ℤ) * 3).toNat = 4 + k * 3 by omega]
      simp; rw [abs_of_pos (by positivity)]
      field_simp
      rw [show (4 + k*3)/3 = k+1 by omega]
      grind
    calc _ ≤ |(2 + (f_7_4_4 (3 + (k:ℤ) * 3).toNat):ℝ)⁻¹ * (-1) ^ f_7_4_4 (3 + (k:ℤ) * 3).toNat| + |(2 + (f_7_4_4 (4 + (k:ℤ) * 3).toNat):ℝ)⁻¹ * (-1) ^ f_7_4_4 (4 + (k:ℤ) * 3).toNat| := by apply abs_add_le
         _ ≤ (2*(2 + (k:ℝ)))⁻¹ + (2*(2 + (k:ℝ)))⁻¹  := by exact add_le_add h1 h2
         _ = (2 + (k:ℝ))⁻¹                          := by grind

lemma Series.f_7_4_4.triplet_sum (k : ℕ) : a_7_4_4 (f_7_4_4 (3*k)) + a_7_4_4 (f_7_4_4 (3*k+1)) + a_7_4_4 (f_7_4_4 (3*k+2)) = c k := by
  obtain ⟨t1, t2, t3⟩ := Series.f_7_4_4.get_triplet k
  rw [t1, t2, t3]
  unfold Series.a_7_4_4
  have ht1even : Even (2*k) := by grind
  have ht2odd : Odd (4*k+1) := by grind
  have ht3odd : Odd (4*k+3) := by grind
  rw [Even.neg_one_pow ht1even, Odd.neg_one_pow ht2odd, Odd.neg_one_pow ht3odd]
  push_cast
  nth_rewrite 2 [add_assoc]; nth_rewrite 2 [add_assoc]
  norm_num
  unfold c
  grind

lemma Series.f_7_4_4.partial_eq (k : ℕ) :
    (fun n ↦ a_7_4_4 (f_7_4_4 n) : Series).partial (3*(k:ℤ)+2) =
    ∑ n ∈ Finset.range (k+1), c n := by
  induction' k with n ih
  · unfold Series.partial c; simp
    have h2 : (2:ℤ) = (0+1) + 1 := by grind
    rw [h2, sum_of_nonempty (by grind), sum_of_nonempty (by grind)]; simp
    have hts := Series.f_7_4_4.triplet_sum 0; simp at hts
    have hts0 : Series.f_7_4_4 0 = 0 := by grind
    rw [hts0] at hts; rw [hts]
    unfold c
    grind
  · unfold Series.partial c at ih ⊢
    simp at ih ⊢
    rw [Finset.sum_ite_of_true (by grind)] at ih ⊢
    have h2 :  (3 * ((n:ℤ) + 1) + 2) = ((3 * (n:ℤ)) + 2) + 1 + 1 + 1 := by grind
    rw [h2, sum_of_nonempty (by grind), sum_of_nonempty (by grind), sum_of_nonempty (by grind)]
    rw [Finset.sum_range_succ, ih]
    suffices a_7_4_4 (f_7_4_4 (3 * (n:ℤ) + 2 + 1).toNat) +
         a_7_4_4 (f_7_4_4 (3 * (n:ℤ) + 2 + 1 + 1).toNat) +
         a_7_4_4 (f_7_4_4 (3 * (n:ℤ) + 2 + 1 + 1 + 1).toNat) =
         -1 / ((2 * ((n+1:ℕ):ℝ) + 2) * (4 * ((n+1:ℕ):ℝ) + 3) * (4 * ((n+1:ℕ):ℝ) + 5)) by linarith
    have h1 : (3 * (n:ℤ) + 2 + 1).toNat = 3 * (n+1) := by omega
    have h2 : (3 * (n:ℤ) + 2 + 1 + 1).toNat = 3 * (n+1) + 1 := by omega
    have h3 : (3 * (n:ℤ) + 2 + 1 + 1 + 1).toNat = 3 * (n+1) + 2 := by omega
    rw [h1, h2, h3]
    exact Series.f_7_4_4.triplet_sum (n+1)

lemma Series.antitone_of_c_sum : Antitone (fun n:ℕ => ∑ k ∈ Finset.range (n+1), c k) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [Finset.sum_range_succ]
  suffices c (n + 1) ≤ 0 by linarith
  unfold c
  field_simp; simp

lemma Series.bounded_below_of_c (n : ℕ) : -((1:ℝ)/ (n+1)^2) ≤ c n := by
  unfold c
  field_simp
  nlinarith

lemma Series.telescoping_bound (n:ℕ) : ∑ x ∈ Finset.range (n + 1), 1 / ((x:ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n:ℝ)+1) := by
  induction' n with k ih
  · simp; grind
  · rw [Finset.sum_range_succ]; simp_all
    rw [show ((k:ℝ) + 1 + 1) = (k:ℝ) + 2 by linarith]
    suffices (((k:ℝ)+2)^2)⁻¹ ≤ ((k:ℝ)+1)⁻¹ - ((k:ℝ)+2)⁻¹ by linarith
    field_simp
    grind

lemma Series.ge_neg_two_c_sum (n : ℕ) : -2 ≤ ∑ k ∈ Finset.range (n+1), c k := by
  have hs : ∑ k ∈ Finset.range (n+1), -((1:ℝ)/ (k+1)^2) ≤ ∑ k ∈ Finset.range (n+1), c k := by
    apply Finset.sum_le_sum
    intro i hi
    exact Series.bounded_below_of_c i
  rw [Finset.sum_neg_distrib] at hs
  suffices ∑ x ∈ Finset.range (n + 1), 1 / ((x:ℝ) + 1) ^ 2 ≤ 2 by linarith
  have htel := Series.telescoping_bound n
  suffices 1 / ((n:ℝ) + 1) ≥ 0 by linarith
  positivity

lemma Series.bounded_below_of_c_sum : BddBelow (Set.range (fun n:ℕ => ∑ k ∈ Finset.range (n+1), c k)) := by
  use -2
  intro n hn
  obtain ⟨a, ha⟩ := hn; simp at ha
  linarith [Series.ge_neg_two_c_sum a]

lemma Series.convergent_of_c_sum : ∃ L:ℝ, Filter.Tendsto (fun n:ℕ => ∑ k ∈ Finset.range (n+1), c k) Filter.atTop (nhds L) := by
  have := tendsto_atTop_ciInf Series.antitone_of_c_sum Series.bounded_below_of_c_sum
  use (⨅ i, ∑ k ∈ Finset.range (i + 1), c k)


theorem Series.ex_7_4_4'_conv : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).converges := by
  unfold Series.converges
  choose L hL using Series.convergent_of_c_sum
  use L
  unfold Series.convergesTo
  rw [Metric.tendsto_atTop] at hL ⊢
  simp_rw [Real.dist_eq] at hL ⊢
  intro ε hε
  choose N₁ hN₁ using hL (ε/3) (by positivity)
  choose N₂ hN₂ using exists_nat_gt (3/ε)
  set N := max N₁ N₂
  have : N ≥ 0 := by positivity
  use 3*N+2
  intro n hn
  lift n to ℕ using (by omega)
  set j := (n - 2) / 3
  have bound := Series.f_7_4_4.triplet_bound j n (by grind) (by grind)
  specialize hN₁ j (by grind)
  rw [← Series.f_7_4_4.partial_eq] at hN₁
  have hN₂' : 1 / (N₂+2) < ε/3  := by field_simp at hN₂ ⊢; grind
  set s := (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).partial
  have hj : j ≥ N₂ := by grind
  have hj' : 1 / (j + 2) ≤ ε / 3 := by
    field_simp at hN₂ ⊢
    suffices ((j+2):ℝ) ≥ N₂ by nlinarith
    norm_cast
    linarith
  calc _ = |s n - s (3 * j + 2) + s (3 * j + 2) - L| := by grind
       _ ≤ |s n - s (3 * j + 2)| + |s (3 * j + 2) - L| := by grind
       _ ≤ ε/3 + |s (3 * j + 2) - L|  := by gcongr; linarith
       _ ≤ ε/3 + ε/3                  := by gcongr
       _ < ε                          := by grind

theorem Series.ex_7_4_4'_sum : (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum < 0 := by
  have hconv := Series.ex_7_4_4'_conv
  have hsum := Series.convergesTo_sum hconv
  unfold Series.convergesTo at hsum
  set φ := (fun n ↦ a_7_4_4 (f_7_4_4 n):Series).partial
  set χ := (fun n ↦ a_7_4_4 (f_7_4_4 n) :Series).sum
  have hsubseq : Filter.Tendsto (fun n => φ ((3 * n)+2)) Filter.atTop (nhds χ) := by
    apply Filter.Tendsto.comp hsum
    apply Filter.tendsto_atTop_atTop.mpr
    intro b; use max 0 b
    intro a hab
    grind
  have hle : χ ≤ -1/30 := by
    apply le_of_tendsto hsubseq
    rw [Filter.eventually_atTop]
    use 0; intro b hb
    lift b to ℕ using (by omega)
    unfold φ
    rw [Series.f_7_4_4.partial_eq]
    induction' b with k ih
    · simp; unfold c; grind
    · rw [Finset.sum_range_succ]
      suffices c (k + 1) ≤ 0 by linarith
      unfold c; field_simp; grind
  linarith

/-- Exercise 7.4.1 -/
theorem Series.absConverges_of_subseries {a:ℕ → ℝ} (ha: (a:Series).absConverges) {f: ℕ → ℕ} (hf: StrictMono f) :
  (fun n ↦ a (f n):Series).absConverges := by
  suffices (fun n ↦ |a (f n)|:Series).converges by
    unfold absConverges
    convert this using 1
    ext n <;> grind
  have hfanonneg : (fun n ↦ |a (f n)|:Series).nonneg := by
    intro n; simp
    split_ifs <;> grind
  have ha' : (fun n => |a n|:Series).converges := by
    unfold absConverges at ha
    convert ha using 1
    ext n <;> grind
  have hanonneg : (fun n => |a n|:Series).nonneg := by
    intro n; simp
    split_ifs <;> grind
  choose M hM using (Series.converges_of_nonneg_iff hanonneg).mp ha'
  have hM0 : 0 ≤ M := by
    have := Series.partial_nonneg hanonneg 1
    specialize hM 1
    linarith
  apply (Series.converges_of_nonneg_iff hfanonneg).mpr
  use M; intro N
  unfold Series.partial at hM ⊢; simp at hM ⊢
  rw [Finset.sum_ite_of_true (by grind)]
  by_cases! hN0 : N < 0
  · rw [sum_of_empty (by grind)]
    linarith
  · lift N to ℕ using by omega
    set N' := ((Finset.Iic N).image f).sup id
    specialize hM N'
    rw [Finset.sum_ite_of_true (by grind)] at hM
    suffices ∑ x ∈ Finset.Icc (0:ℤ) N, |a (f x.toNat)| ≤ ∑ x ∈ Finset.Icc (0:ℤ) N', |a x.toNat| by linarith
    calc ∑ x ∈ Finset.Icc (0:ℤ) N, |a (f x.toNat)|
       = ∑ n ∈ (Finset.Icc (0:ℤ) N).image (f ∘ Int.toNat), |a n| := by
            symm
            apply Finset.sum_image
            intro a ha b hb hab
            have ha0 : a ≥ 0 := by grind
            have hb0 : b ≥ 0 := by grind
            have := hf.injective hab
            grind
      _≤ ∑ n ∈ (Finset.Icc (0:ℤ) N').image Int.toNat, |a n| := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              simp at hx ⊢
              choose a ha using hx
              use x
              constructor
              · constructor
                · grind
                · unfold N'
                  norm_cast
                  apply Finset.le_sup (f := id)
                  simp
                  use a.toNat
                  grind
              · grind
            · intro n hin hnnotin
              grind
      _= ∑ x ∈ Finset.Icc (0:ℤ) N', |a x.toNat| := by
            apply Finset.sum_image
            intro a ha b hb hab
            grind

/--
{given -show}`n : ℕ`
Exercise 7.4.2 : reprove Proposition 7.4.3 using Proposition 7.41, Proposition 7.2.14,
and expressing {lean}`a n` as the difference of {lean}`a n + |a n|` and {lean}`|a n|`.
-/
theorem Series.absConverges_of_permute' {a:ℕ → ℝ} (ha : (a:Series).absConverges)
  {f: ℕ → ℕ} (hf: Function.Bijective f) :
    (fun n ↦ a (f n):Series).absConverges  ∧ (a:Series).sum = (fun n ↦ a (f n):Series).sum := by
  -- set up some stuff first
  set α : ℕ → ℝ := fun n => |a n|
  set β : ℕ → ℝ := fun n => a n + |a n|
  have hαβ : (β:Series) - (α:Series) = (a:Series) := by
    rw [Series.sub_coe]
    congr; ext n
    split_ifs <;> grind
  have hαβ' : (fun n ↦ a (f n):Series) = (fun n ↦ β (f n):Series) - (fun n ↦ α (f n):Series) := by
    congr
    ext n
    split_ifs with h
    · simp; rw [if_pos (by grind), if_pos (by grind)]
      unfold β α; simp
    · simp; rw [if_neg (by grind), if_neg (by grind)]
      simp
  have hαconv : (α:Series).converges := by
    unfold Series.absConverges at ha
    convert ha using 1
    ext n <;> grind
  have haconv : (a:Series).converges := by exact Series.converges_of_absConverges ha
  have hβconv : (β:Series).converges := by
    unfold β
    have : (a:Series) + (α:Series) = (β:Series) := by exact Series.add_coe a α
    rw [← this]
    exact (Series.add haconv hαconv).1
  have hαnonneg : (α:Series).nonneg := by
    intro a; simp
    split_ifs <;> grind
  have hβnonneg : (β:Series).nonneg := by
    intro a; simp
    split_ifs <;> grind
  have hαpermute := Series.converges_of_permute_nonneg hαnonneg hαconv hf
  have hβpermute := Series.converges_of_permute_nonneg hβnonneg hβconv hf
  constructor
  · unfold Series.absConverges
    convert hαpermute.1 using 1
    simp; ext n
    split_ifs <;> grind
  · have hsum : (β:Series).sum - (α:Series).sum = (a:Series).sum := by
      rw [← hαβ]
      have := (Series.sub hβconv hαconv).2
      linarith
    have hsumpermute : (fun n ↦ a (f n):Series).sum = (fun n ↦ β (f n):Series).sum - (fun n ↦ α (f n):Series).sum := by
      rw [hαβ']
      have := (Series.sub hβpermute.1 hαpermute.1).2
      linarith
    grind
end Chapter7
