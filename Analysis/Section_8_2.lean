import Mathlib.Tactic
import Analysis.Section_7_2
import Analysis.Section_7_3
import Analysis.Section_7_4
import Analysis.Section_8_1

/-!
# Analysis I, Section 8.2: Summation on infinite sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Absolute convergence and summation on countably infinite or general sets.
- Connections with Mathlib's {name}`Summable` and {name}`tsum`.
- The Riemann rearrangement theorem.

Some non-trivial API is provided beyond what is given in the textbook in order connect these
notions with existing summation notions.

After this section, the summation notation developed here will be deprecated in favor of Mathlib's API for {name}`Summable` and {name}`tsum`.

-/

namespace Chapter8
open Chapter7 Chapter7.Series Finset Function Filter

/-- Definition 8.2.1 (Series on countable sets).  Note that with this definition, functions defined
on finite sets will not be absolutely convergent; one should use {lit}`AbsConvergent'` instead for such
cases.-/
abbrev AbsConvergent {X:Type} (f: X → ℝ) : Prop := ∃ g: ℕ → X, Bijective g ∧ (f ∘ g: Series).absConverges

theorem AbsConvergent.mk {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : AbsConvergent f := by use g

open Classical in
/-- The definition has been chosen to give a sensible value when {name}`X` is finite, even though
{name}`AbsConvergent` is by definition false in this context. -/
noncomputable abbrev Sum {X:Type} (f: X → ℝ) : ℝ := if h: AbsConvergent f then (f ∘ h.choose:Series).sum else
  if _hX: Finite X then (∑ x ∈ @univ X (Fintype.ofFinite X), f x) else 0

theorem Sum.of_finite {X:Type} [hX:Finite X] (f:X → ℝ) : Sum f = ∑ x ∈ @Finset.univ X (Fintype.ofFinite X), f x := by
  have : ¬ AbsConvergent f := by
    by_contra!; choose g hg _ using this
    rw [←hg.finite_iff, ←not_infinite_iff_finite] at hX; apply hX; infer_instance
  simp [Sum, this, hX]

theorem AbsConvergent.comp {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hf: AbsConvergent f) : (f ∘ g:Series).absConverges := by
  choose g' hbij hconv using hf
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).1 using 4 with n
  simp [hright (g n.toNat)]

theorem Sum.eq {X: Type} {f:X → ℝ} {g:ℕ → X} (h: Bijective g) (hfg: (f ∘ g:Series).absConverges) : (f ∘ g:Series).convergesTo (Sum f) := by
  have : AbsConvergent f := .mk h hfg
  simp [Sum, this]
  choose hbij hconv using this.choose_spec
  set g' := this.choose
  choose g'_inv hleft hright using bijective_iff_has_inverse.mp hbij
  convert convergesTo_sum (converges_of_absConverges hfg) using 1
  have hG : Bijective (g'_inv ∘ g) := .comp ⟨hright.injective, hleft.surjective⟩ h
  convert (absConverges_of_permute hconv hG).2 using 4 with _ n
  by_cases hn : n ≥ 0 <;> simp [hn, hright (g n.toNat)]

theorem Sum.of_comp {X Y:Type} {f:X → ℝ} (h: AbsConvergent f) {g: Y → X} (hbij: Bijective g) : AbsConvergent (f ∘ g) ∧ Sum f = Sum (f ∘ g) := by
  choose g' hbij' hconv' using h
  choose g_inv hleft hright using bijective_iff_has_inverse.mp hbij
  have hbij_g_inv_g' : Bijective (g_inv ∘ g') := .comp ⟨hright.injective, hleft.surjective⟩ hbij'
  have hident : (f ∘ g) ∘ g_inv ∘ g' = f ∘ g' := by ext n; simp [hright (g' n)]
  refine ⟨ ⟨ g_inv ∘ g', ⟨ hbij_g_inv_g', by convert hconv' ⟩ ⟩, ?_ ⟩
  have h := eq (f := f ∘ g) hbij_g_inv_g' (by convert hconv')
  rw [hident] at h
  solve_by_elim [convergesTo_uniq, eq]

@[simp]
theorem Finset.Icc_eq_cast (N:ℕ) : Icc 0 (N:ℤ) = map Nat.castEmbedding (.Icc 0 N) := by
  ext n; simp; constructor
  . intro ⟨ hn, _ ⟩; lift n to ℕ using hn; use n; simp_all
  rintro ⟨ _, ⟨ _, rfl ⟩ ⟩; simp_all

theorem Finset.Icc_empty {N:ℤ} (h: ¬ N ≥ 0) : Icc 0 N = ∅ := by
  ext; simp; intros; contrapose! h; linarith

/-- Theorem 8.2.2, preliminary version.  The arguments here are rearranged slightly from the text. -/
theorem sum_of_sum_of_AbsConvergent_nonneg {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) (hpos: ∀ n m, 0 ≤ f (n, m)) :
  (∀ n, ((fun m ↦ f (n, m)):Series).converges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set L := Sum f
  set a : ℕ → Series := fun n ↦ ((fun m ↦ f (n, m)):Series)
  have hLpos : 0 ≤ L := by
    simp [L, Sum, hf]; apply sum_of_nonneg; intro n; by_cases h: n ≥ 0 <;> simp [h]; grind
  have hfinsum (X: Finset (ℕ × ℕ)) : ∑ p ∈ X, f p ≤ L := by
    choose g' hg habsconv using hf
    set g := (Equiv.ofBijective g' hg).symm
    have hsum := Sum.eq hg habsconv
    have hnonneg : (f ∘ g' : Series).nonneg := by
      intro n; simp
      split_ifs <;> grind
    set N := X.sup g
    have hle : ∑ p ∈ X, f p ≤ ∑ p ∈ (Finset.Icc 0 N).image g', f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp; use g x
        constructor
        · apply le_sup; exact hx
        · unfold g
          exact (Equiv.ofBijective g' hg).right_inv x
      · intro i hi hix
        specialize hpos i.1 i.2; grind
    rw [Finset.sum_image (by intro x _ y _ hxy; exact hg.injective hxy)] at hle
    suffices ∑ x ∈ Icc 0 N, f (g' x) ≤ L by linarith
    have := Series.partial_le_sum_of_nonneg hnonneg (Series.converges_of_absConverges habsconv)
    specialize this N; unfold Series.partial at this; simp at this
    convert this
    exact (Series.sum_of_converges hsum).symm
  have hfinsum' (n M:ℕ) : (a n).partial M ≤ L := by
    simp [a, Series.partial, Finset.Icc_eq_cast]
    convert_to ∑ x ∈ .map (Embedding.sectR n ℕ) (.Icc 0 M), f x ≤ L
    . simp
    solve_by_elim
  have hnon (n:ℕ) : (a n).nonneg := by
    simp [a, nonneg]; intro m; split_ifs <;> simp [hpos]
  have hconv (n:ℕ) : (a n).converges := by
    rw [converges_of_nonneg_iff (hnon n)]
    use L; intro N; by_cases h: N ≥ 0
    . lift N to ℕ using h; solve_by_elim
    rw [partial_of_lt (by simp [a]; linarith)]; simp [hLpos]
  have (N M:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).partial M ≤ L := by
    by_cases hN : N ≥ 0; swap
    . simp [Finset.Icc_empty hN, hLpos]
    lift N to ℕ using hN
    by_cases hM : M ≥ 0; swap
    . convert hLpos; unfold Series.partial
      apply sum_eq_zero; intro n _
      simp [a, Finset.Icc_empty hM]
    lift M to ℕ using hM
    convert_to ∑ x ∈ (Icc 0 N) ×ˢ (.Icc 0 M), f x ≤ L
    . simp [a, sum_product, Series.partial]
    solve_by_elim
  replace (N:ℤ) : ∑ n ∈ Icc 0 N, (a n.toNat).sum ≤ L := by
    apply le_of_tendsto' (x := .atTop) (tendsto_finset_sum _ _) (this N)
    solve_by_elim [convergesTo_sum]
  replace (N:ℤ) : (fun n ↦ (a n).sum:Series).partial N ≤ L := by
    convert this N with n hn; simp_all
  have hnon' : (fun n ↦ (a n).sum:Series).nonneg := by
    intro n; simp; split_ifs
    . exact sum_of_nonneg (hnon n.toNat)
    simp
  have hconv' : (fun n ↦ (a n).sum:Series).converges := by
    rw [converges_of_nonneg_iff hnon']; use L
  replace : (fun n ↦ (a n).sum:Series).sum ≤ L := le_of_tendsto' (convergesTo_sum hconv') this
  replace : (fun n ↦ (a n).sum:Series).sum = L := by
    apply le_antisymm this (le_of_forall_sub_le _); intro ε hε
    replace : ∃ X, ∑ p ∈ X, f p ≥ L - ε := by
      choose g hg habsconv using hf
      have hsum := Sum.eq hg habsconv
      unfold Series.convergesTo at hsum
      rw [Metric.tendsto_atTop] at hsum
      choose N' hN using hsum (ε / 2) (by positivity)
      set N := N'.toNat
      specialize hN N (by grind)
      unfold Series.partial at hN; simp at hN
      rw [Real.dist_eq] at hN
      use (Finset.Icc 0 N).image g
      rw [Finset.sum_image (by intro x _ y _ hxy; exact hg.injective hxy)]
      grind
    choose X hX using this
    have : ∃ N, ∃ M, X ⊆ (Icc 0 N) ×ˢ (Icc 0 M) := by
      use X.sup (Prod.fst)
      use X.sup (Prod.snd)
      intro x hx
      simp; constructor
      · exact le_sup hx
      · exact le_sup hx
    choose N M hX' using this
    calc
      _ ≤ ∑ p ∈ X, f p := hX
      _ ≤ ∑ p ∈ (Icc 0 N) ×ˢ (Icc 0 M), f p := sum_le_sum_of_subset_of_nonneg hX' (by solve_by_elim)
      _ = ∑ n ∈ Icc 0 N, ∑ m ∈ Icc 0 M, f (n, m) := sum_product _ _ _
      _ ≤ ∑ n ∈ Icc 0 N, (a n).sum := by
        apply sum_le_sum; intro n _
        convert partial_le_sum_of_nonneg (hnon n) (hconv n) M
        simp [a, Series.partial]
      _ = (fun n ↦ (a n).sum:Series).partial N := by simp [Series.partial]
      _ ≤ _ := partial_le_sum_of_nonneg hnon' hconv' _
  simp [a, hconv, ← this, Series.convergesTo_sum hconv']

/-- Theorem 8.2.2, second version -/
theorem sum_of_sum_of_AbsConvergent {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ n, ((fun m ↦ f (n, m)):Series).absConverges) ∧
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set fplus := max f 0
  set fminus := max (-f) 0
  have hfplus_nonneg : ∀ n m, 0 ≤ fplus (n, m) := by intro n m; simp [fplus]
  have hfminus_nonneg : ∀ n m, 0 ≤ fminus (n, m) := by intro n m; simp [fminus]
  have hdiff : f = fplus - fminus := by
    ext n
    unfold fplus fminus
    simp
  have hfplus_conv : AbsConvergent fplus := by
    choose g hg hconv using hf
    use g; constructor
    · exact hg
    · refine (Series.converges_of_le ?_ ?_ hconv).1
      · simp
      · intro n hn; simp at hn ⊢
        split_ifs
        unfold fplus
        simp
        grind
  have hfminus_conv : AbsConvergent fminus := by
    choose g hg hconv using hf
    use g; constructor
    · exact hg
    · refine (Series.converges_of_le ?_ ?_ hconv).1
      · simp
      · intro n hn; simp at hn ⊢
        split_ifs
        unfold fminus
        simp
        grind
  choose hfplus_conv' hfplus_sum using sum_of_sum_of_AbsConvergent_nonneg hfplus_conv hfplus_nonneg
  choose hfminus_conv' hfminus_sum using sum_of_sum_of_AbsConvergent_nonneg hfminus_conv hfminus_nonneg
  split_ands
  . intro n
    have hplusc := hfplus_conv' n
    have hminusc := hfminus_conv' n
    have hadd := Series.add hplusc hminusc
    refine (Series.converges_of_le ?_ ?_ hadd.1).1
    · change 0 = 0
      rfl
    · intro m hm
      simp at hm ⊢
      lift m to ℕ using by omega
      simp
      change |f (n, m)| ≤ (fun m:ℤ ↦ if 0 ≤ m then fplus (n, m.toNat) else 0) m +  (fun m:ℤ ↦ if 0 ≤ m then fminus (n, m.toNat) else 0) m
      simp
      unfold fplus fminus; simp
  convert convergesTo.sub hfplus_sum hfminus_sum using 1
  . -- encountered surprising difficulty with definitional equivalence here
    simp [hdiff]
    change (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum:Series)
      - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum:Series)
    convert_to (fun n ↦ ((fun m ↦ (fplus - fminus) (n, m)):Series).sum:Series) =
      (((fun n ↦ ((fun m ↦ fplus (n, m)):Series).sum) - (fun n ↦ ((fun m ↦ (fminus) (n, m)):Series).sum):ℕ → ℝ):Series)
    . convert sub_coe _ _
    rcongr _ n; simp
    convert (sub _ _).2 with m; rfl
    split_ifs with h <;> simp [h, HSub.hSub, Sub.sub]
    . solve_by_elim
    convert hfminus_conv' n.toNat
  have ⟨ g, hg, _ ⟩ := hf
  have h1 := Sum.eq hg (hf.comp hg)
  have hplus := Sum.eq hg (hfplus_conv.comp hg)
  have hminus := Sum.eq hg (hfminus_conv.comp hg)
  apply convergesTo_uniq h1 _
  convert (convergesTo.sub hplus hminus) using 3 with n
  split_ifs with h <;> simp [h, hdiff, HSub.hSub, Sub.sub]

/-- Theorem 8.2.2, third version -/
theorem sum_of_sum_of_AbsConvergent' {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (∀ m, ((fun n ↦ f (n, m)):Series).absConverges) ∧
  (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).convergesTo (Sum f) := by
  set π: ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.2, p.1)
  have hπ: Bijective π := Involutive.bijective (congrFun rfl)
  have ⟨ g, hg, hconv ⟩ := hf
  convert sum_of_sum_of_AbsConvergent (f := f ∘ π) _ using 2
  . exact (Sum.of_comp hf hπ).2
  refine ⟨ _, hπ.comp hg, ?_ ⟩
  convert hconv using 2

/-- Theorem 8.2.2, fourth version -/
theorem sum_comm {f:ℕ × ℕ → ℝ} (hf:AbsConvergent f) :
  (fun n ↦ ((fun m ↦ f (n, m)):Series).sum:Series).sum = (fun m ↦ ((fun n ↦ f (n, m)):Series).sum:Series).sum := by
  simp [sum_of_converges (sum_of_sum_of_AbsConvergent hf).2,
        sum_of_converges (sum_of_sum_of_AbsConvergent' hf).2]

/-- Lemma 8.2.3 / Exercise 8.2.1 -/
theorem AbsConvergent.iff {X:Type} (hX:CountablyInfinite X) (f : X → ℝ) :
  AbsConvergent f ↔ BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ ) := by
    constructor
    · intro hf
      choose g hg hconv using hf
      have hconv' := hconv; unfold Series.absConverges at hconv'
      choose L hL using hconv
      use L
      intro a ha
      simp at ha
      choose Y hY using ha
      let g' := (Equiv.ofBijective g hg).symm
      let N := Y.sup g'
      rw [← hY]
      have hle : ∑ x ∈ Y, |f x| ≤ ∑ n ∈ (Finset.Icc (0:ℕ) N), |f (g n)| := by
        have : ∑ x ∈ Y, |f x| = ∑ n ∈ Y.image g', |f (g n)| := by
          rw [Finset.sum_image (by intro x _ y _ hxy; exact g'.injective hxy)]
          unfold g'
          simp [Equiv.ofBijective_apply_symm_apply]
        suffices ∑ n ∈ Y.image g', |f (g n)| ≤ ∑ n ∈ (Finset.Icc (0:ℕ) N), |f (g n)| by linarith
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp at hx
          choose a ha using hx
          simp
          rw [← ha.2]; unfold N
          exact Finset.le_sup (f := g') ha.1
        · simp
      suffices ∑ n ∈ (Finset.Icc (0:ℕ) N), |f (g n)| ≤ L by linarith
      have := Series.partial_le_sum_of_nonneg (by grind) hconv' N; simp at this
      convert this
      · unfold Series.abs Series.partial; simp
      · exact (sum_of_converges hL).symm
    · intro hbdd
      -- Assume that it is _not_ absolutely convergent.
      by_contra! h
      choose g hg using hX
      set g' := (Equiv.ofBijective g hg).symm
      specialize h g' (by exact Equiv.bijective g')
      -- now, we contrapose h and claim that there has to be some
      -- L to which the series converges. Since this is a sequence of
      -- partial sums of absolute values, it is an increasing sequence.
      -- furthermore, we can bound it above, which means we can use the
      -- monotone convergence theorem to obtain a bound.
      contrapose! h; simp
      unfold Series.convergesTo Series.abs Series.partial; simp
      set γ : ℤ → ℝ := (fun N ↦ ∑ x ∈ Icc 0 N, if 0 ≤ x then |if 0 ≤ x then f (g' x.toNat) else 0| else 0)
      have hmono : Monotone γ := by
        intro a b hab
        unfold γ
        apply Finset.sum_le_sum_of_subset_of_nonneg <;> grind
      -- This is particularly inconvenient and ugly, unfortunately. There is a lot of
      -- ceremony involved in wrapping and unwrapping the types, and the if-then-elses,
      -- even though "on paper" it is obvious that B is an upper bound.
      have hbd : BddAbove (Set.range γ) := by
        choose B hB using hbdd
        use B
        intro x hx; simp at hx
        choose z hz using hx
        unfold γ at hz
        apply hB
        rw [Finset.sum_ite_of_true (by grind)] at hz
        have hz' : ∑ x ∈ Icc 0 z, |f (g' x.toNat)| = x := by
          rw [← hz]
          apply Finset.sum_congr
          · rfl
          · intro x hx; simp at hx
            rw [if_pos (by grind)]
        simp at hz ⊢
        by_cases! hz0 : z < 0
        · use Finset.empty
          rw [← hz', sum_of_empty (by grind)]
          exact Finset.sum_empty
        · use (Finset.Icc 0 z.toNat).map g'.toEmbedding
          rw [← hz']
          simp
          apply @Finset.sum_nbij ℕ ℤ ℝ _ (Finset.Icc 0 z.toNat) (Finset.Icc 0 z)
            (fun x => |f (g' x)|) (fun x => |f (g' x.toNat)|) (fun x => (x : ℤ))
          · simp; intro a ha
            grind
          · intro a ha b hb hab
            grind
          · intro a ha
            simp at ha ⊢
            use a.toNat; grind
          · intro a ha; simp
      have hmonotoneconvergence := tendsto_atTop_ciSup hmono hbd
      use (⨆ i, γ i)

abbrev AbsConvergent' {X:Type} (f: X → ℝ) : Prop := BddAbove ( (fun A ↦ ∑ x ∈ A, |f x|) '' .univ )

theorem AbsConvergent'.of_finite {X:Type} [Finite X] (f:X → ℝ) : AbsConvergent' f := by
  have _ := Fintype.ofFinite X
  simp [bddAbove_def]; use ∑ x, |f x|; intro A; apply Finset.sum_le_univ_sum_of_nonneg; simp

/-- Not in textbook, but should have been included. -/
theorem AbsConvergent'.of_countable {X:Type} (hX:CountablyInfinite X) {f:X → ℝ} :
  AbsConvergent' f ↔ AbsConvergent f := by
  constructor
  . intro hf; simp [bddAbove_def] at hf; choose L hL using hf
    have ⟨ g, hg ⟩ := hX.symm; refine ⟨ g, hg, ?_ ⟩
    unfold absConverges; rw [converges_of_nonneg_iff]
    . use L; intro N; by_cases hN: N ≥ 0
      . lift N to ℕ using hN
        set g':= Embedding.mk g hg.1
        convert hL (map g' (Icc 0 N))
        simp [Series.partial]; rfl
      convert hL ∅
      simp; apply partial_of_lt; grind
    simp [nonneg]
    intro n; by_cases h: n ≥ 0 <;> simp [h]
  intro hf; rwa [AbsConvergent.iff hX f] at hf

/-- Lemma 8.2.5 / Exercise 8.2.2-/
theorem AbsConvergent'.countable_supp {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  AtMostCountable { x | f x ≠ 0 } := by
    choose M hM using hf
    let Ι : ℕ → Set X := fun n => {x | |f x| > 1/(n+1:ℝ)}
    have heq : { x | f x ≠ 0 } = ⋃ n : ℕ, Ι n := by
      ext x;
      simp; constructor
      · intro hfx
        have habs : |f x| > 0 := by grind
        choose N hN using exists_nat_gt (1/|f x|)
        have hinv : 1 / |f x| > 0 := by positivity
        have hpos : (N:ℝ) > 0 := by grind
        have : |f x| > 1 / N := by exact (one_div_lt habs hpos).mp hN
        have : |f x| > 1 / (N+1) := by
          rw [div_lt_iff₀ (by grind)] at hN
          field_simp; grind
        use N; unfold Ι; exact this
      · intro hunion
        choose i hi using hunion
        unfold Ι at hi; simp at hi
        by_contra!
        rw [this] at hi; simp at hi
        grind
    rw [heq]
    have hi (n : ℕ) : (Ι n).Finite := by
      by_contra! hinfinite
      choose A hAsub hAcard using Set.Infinite.exists_subset_card_eq hinfinite (⌈M⌉₊ * (n+1) + 1)
      have hsum : M < ∑ x ∈ A, |f x| := by
        have hbound : ∑ x ∈ A, (1 / (n + 1 : ℝ)) ≤  ∑ x ∈ A, |f x| := by
          apply Finset.sum_le_sum
          intro a ha
          have hain : a ∈ Ι n := by grind
          unfold Ι at hain
          simp at hain ⊢
          grind
        calc M ≤ ⌈M⌉₊                           := by exact Nat.le_ceil _
             _ = (⌈M⌉₊ * (n+1)) * (1/(n+1))     := by field_simp
             _ < (⌈M⌉₊ * (n+1) + 1) * (1/(n+1)) := by gcongr; grind
             _ = #A * (1/(n+1))                 := by congr; exact_mod_cast hAcard.symm
             _ = ∑ x ∈ A, (1 / (n + 1 : ℝ))     := by simp [Finset.sum_const]
             _ ≤ ∑ x ∈ A, |f x|                 := hbound
      contrapose hM
      rw [mem_upperBounds]
      push_neg
      use ∑ x ∈ A, |f x|
      simp; exact hsum
    apply atMostCountable_of_iUnion_atMostCountable
    · left; use id; exact bijective_id
    · intro i; right; specialize hi i; exact hi

#check Set.Infinite.exists_subset_card_eq
/-- Compare with Mathlib's {name}`Summable.subtype`-/
theorem AbsConvergent'.subtype {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (A: Set X) :
  AbsConvergent' (fun x:A ↦ f x) := by
  apply BddAbove.mono _ hf
  intro z hz; simp at *; choose A hA using hz
  use A.map (Embedding.subtype _); simp [hA]

/-- A generalized sum.  Note that this will give junk values if {name}`f` is not {name}`AbsConvergent'`. -/
noncomputable abbrev Sum' {X:Type} (f: X → ℝ) : ℝ := Sum (fun x : { x | f x ≠ 0 } ↦ f x)

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_finsupp {X:Type} {f:X → ℝ} {A: Finset X} (h: ∀ x ∉ A, f x = 0) : Sum' f = ∑ x ∈ A, f x := by
  unfold Sum'
  set E := { x | f x ≠ 0 }
  have hE : E ⊆ A := by intro _; simp [E]; grind
  have hfin : Finite E := Finite.Set.subset _ hE
  set E' := E.toFinite.toFinset
  rw [Sum.of_finite (fun x:E ↦ f x), ←E'.sum_subtype (by simp [E'])]
  replace hE : E' ⊆ A := by aesop
  apply sum_subset hE; aesop

/-- Not in textbook, but should have been included (the series laws are significantly harder
to establish without this) -/
theorem Sum'.of_countable_supp {X:Type} {f:X → ℝ} {A: Set X} (hA: CountablyInfinite A)
  (hfA : ∀ x ∉ A, f x = 0) (hconv: AbsConvergent' f):
  AbsConvergent' (fun x:A ↦ f x) ∧ Sum' f = Sum (fun x:A ↦ f x) := by
  -- We can adapt the proof of `AbsConvergent'.of_countable` to establish absolute convergence on A.
  have hconv' : AbsConvergent (fun x:A ↦ f x) :=
    (AbsConvergent'.of_countable hA).mp (hconv.subtype A)
  rw [AbsConvergent'.of_countable hA]
  refine ⟨ hconv', ?_ ⟩
  set E := { x | f x ≠ 0 }
  -- The main challenge here is to relate a sum on E with a sum on A.  First, we show containment.
  have hE : E ⊆ A := by intro _; simp [E]; by_contra!; aesop
  -- Now, we map A back to the natural numbers, thus identifying E with a subset E' of ℕ.
  choose g hg using hA.symm
  have hsum := Sum.eq hg (hconv'.comp hg)
  set E' := { n | ↑(g n) ∈ E }
  set ι : E' → E := fun ⟨ n, hn ⟩ ↦ ⟨ g n, by aesop ⟩
  have hι: Bijective ι := by
    split_ands
    . intro ⟨ _, _ ⟩ ⟨ _, _ ⟩ h; simp [ι, E', Subtype.val_inj] at *; exact hg.1 h
    . intro ⟨ x, hx ⟩; choose n hn using hg.2 ⟨ _, hE hx ⟩; use ⟨ n, by aesop ⟩; grind
  -- The cases of infinite and finite E' are handled separately.
  obtain hE' | hE' := Nat.atMostCountable_subset E'
  . --   use Nat.monotone_enum_of_infinite to enumerate E'
    --   show the partial sums of E' are a subsequence of the partial sums of A
    set hinf : Infinite E' := hE'.toInfinite
    choose a ha_bij ha_mono using (Nat.monotone_enum_of_infinite E').exists
    have : atTop.Tendsto (Nat.cast ∘ Subtype.val ∘ a: ℕ → ℤ) atTop := by
      apply tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop _)
      intro _ _ hnm; simp [ha_mono hnm]
    apply tendsto_nhds_unique  _ (hsum.comp this)
    have hconv'' : AbsConvergent (fun x:E ↦ f x) := by
      rw [←AbsConvergent'.of_countable]
      . exact hconv.subtype E
      apply (CountablyInfinite.equiv _).mp hE'; use ι
    replace := Sum.eq (hι.comp ha_bij) (hconv''.comp (hι.comp ha_bij))
    convert this.comp tendsto_natCast_atTop_atTop using 1; ext N
    simp [Series.partial, ι]
    calc
      _ = ∑ x ∈ .image (Subtype.val ∘ a) (.Icc 0 N), f ↑(g x) := by
        symm; apply sum_subset
        . intro m hm; simp at hm ⊢; obtain ⟨ n, hn, rfl ⟩ := hm
          simp [ha_mono.monotone hn]
        intro x hx hx'; simp at hx hx'; contrapose! hx'
        choose n hn using (hι.comp ha_bij).2 ⟨ g x, hx' ⟩
        simp [ι, Subtype.val_inj] at hn
        apply hg.1 at hn; subst hn
        use n; simpa [ha_mono.le_iff_le] using hx
      _ = _ := by
        apply sum_image
        intro _ _ _ _ h; simp [Subtype.val_inj] at h; exact ha_bij.1 h
  -- When E' is finite, we show that all sufficiently large partial sums of A are equal to
  -- the sum of E'.
  let hEfin : Finite E := hι.finite_iff.mp hE'
  let hE'fintype : Fintype E' := .ofFinite _
  let hEfintype : Fintype E := .ofFinite _
  apply convergesTo_uniq _ hsum
  simp [Sum.of_finite, Series.convergesTo]
  apply tendsto_nhds_of_eventually_eq
  have hE'bound : BddAbove E' := Set.Finite.bddAbove hE'
  rw [bddAbove_def] at hE'bound; choose N hN using hE'bound
  rw [eventually_atTop]
  use N; intro N' hN'
  lift N' to ℕ using (LE.le.trans (by positivity) hN')
  simp [Series.partial] at hN' ⊢
  calc
    _ = ∑ n ∈ E', f (g n) := by
      symm; apply sum_subset
      . intro x hx; simp at *; linarith [hN _ hx]
      intro _ _ hx'; simpa [E',E] using hx'
    _ = ∑ n:E', f (g n) := by convert (sum_set_coe _).symm
    _ = ∑ n, f (ι n) := sum_congr rfl (by grind)
    _ = _ := hι.sum_comp (g := fun x ↦ f x)

/-- Connection with Mathlib's {name}`Summable` property. Some version of this might be suitable
    for Mathlib? -/
theorem AbsConvergent'.iff_Summable {X:Type} (f:X → ℝ) : AbsConvergent' f ↔ Summable f := by
  simp [←summable_abs_iff, AbsConvergent']
  simp [summable_iff_vanishing_norm]
  classical
  constructor
  . intro h ε hε
    set s := Set.range fun A ↦ ∑ x ∈ A, |f x|
    have hnon : s.Nonempty := by simp [s]; use 0, ∅; simp
    have : (sSup s)-ε < sSup s := by linarith
    simp [lt_csSup_iff h hnon,s] at this; choose S hS using this
    use S; intro T hT
    rw [abs_of_nonneg (by positivity)]
    have : ∑ x ∈ T, |f x| + ∑ x ∈ S, |f x| ≤ sSup s := by
      apply le_csSup h
      simp [s]; exact ⟨ T ∪ S, sum_union hT ⟩
    linarith
  intro h; choose S hS using h 1 (by norm_num)
  rw [bddAbove_def]
  use ∑ x ∈ S, |f x| + 1; simp; intro T
  calc
    _ = ∑ x ∈ (T ∩ S), |f x| + ∑ x ∈ (T \ S), |f x| := (sum_inter_add_sum_diff _ _ _).symm
    _ ≤ _ := by
      gcongr
      . exact inter_subset_right
      apply le_of_lt (lt_of_abs_lt (hS _ disjoint_sdiff_self_left))

/-- Maybe suitable for porting to Mathlib?-/
theorem Filter.Eventually.int_natCast_atTop (p: ℤ → Prop) :
  (∀ᶠ n in .atTop, p n) ↔ ∀ᶠ n:ℕ in .atTop, p ↑n := by
  refine ⟨ Eventually.natCast_atTop, ?_ ⟩
  simp [eventually_atTop]
  intro N hN; use N; intro n hn
  lift n to ℕ using (by omega)
  simp at hn; solve_by_elim

theorem Filter.Tendsto.int_natCast_atTop {R:Type} (f: ℤ → R) (l: Filter R) :
atTop.Tendsto f l ↔ atTop.Tendsto (f ∘ Nat.cast) l := by
  simp [tendsto_iff_eventually]
  peel with p h
  simp [←eventually_atTop]
  convert Eventually.int_natCast_atTop _


/-- Connection with Mathlib's {name}`tsum` (or {kw (of := «termΣ'_,_»)}`Σ'`) operation -/
theorem Sum'.eq_tsum {X:Type} (f:X → ℝ) (h: AbsConvergent' f) :
  Sum' f = ∑' x, f x := by
  set E := {x | f x ≠ 0}
  obtain hE | hE := h.countable_supp
  . simp [Sum']
    choose g hg using hE.symm
    have : ((f ∘ Subtype.val) ∘ g:Series).absConverges := by
      apply AbsConvergent.comp hg
      rw [←AbsConvergent'.of_countable hE]
      exact h.subtype E
    replace this := Sum.eq hg this
    convert convergesTo_uniq this _ using 1
    · replace : ∑' x, f x = ∑' n, f (g n) := calc
        _ = ∑' x:E, f x := by
          exact (tsum_subtype_eq_of_support_subset (fun x hx => hx)).symm
        _ = _ := (Equiv.tsum_eq (Equiv.ofBijective _ hg) _).symm
      rw [this]
      unfold convergesTo; rw [Filter.Tendsto.int_natCast_atTop]
      convert (Summable.tendsto_sum_tsum_nat ?_).comp (tendsto_add_atTop_nat 1) with n
      . ext N; simp [Series.partial, Nat.range_succ_eq_Icc_zero]
      rw [AbsConvergent'.iff_Summable] at h
      exact h.comp_injective (i := Subtype.val ∘ g) (Subtype.val_injective.comp hg.1)
  rw [of_finsupp (A := E.toFinite.toFinset)]; symm; apply tsum_eq_sum
  all_goals simp [E]


/-- Proposition 8.2.6 (a) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.add {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f+g) ∧ Sum' (f + g) = Sum' f + Sum' g := by
  have habsconv : AbsConvergent' (f+g) := by
    choose a ha using hf
    choose b hb using hg
    use a + b
    intro z hz; simp at hz
    choose x hx using hz
    have hale : ∑ p ∈ x, |f p| ≤ a := by apply ha; simp
    have hble : ∑ p ∈ x, |g p| ≤ b := by apply hb; simp
    suffices z ≤ ∑ p ∈ x, |f p| + ∑ p ∈ x, |g p| by linarith
    rw [← hx, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply abs_add_le
  constructor
  · exact habsconv
  · rw [Sum'.eq_tsum _ habsconv, Sum'.eq_tsum f hf, Sum'.eq_tsum g hg]
    simp
    refine Summable.tsum_add ?_ ?_
    · exact (AbsConvergent'.iff_Summable f).mp hf
    · exact (AbsConvergent'.iff_Summable g).mp hg

/-- Proposition 8.2.6 (b) (Absolutely convergent series laws) / Exercise 8.2.3 -/
theorem Sum'.smul {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) (c: ℝ) :
  AbsConvergent' (c • f) ∧ Sum' (c • f) = c * Sum' f := by
  have habsconv : AbsConvergent' (c • f) := by
    choose a ha using hf
    use |c| * a
    intro z hz; simp at hz
    choose x hx using hz
    have hale : ∑ p ∈ x, |f p| ≤ a := by apply ha; simp
    rw [← Finset.mul_sum] at hx
    rw [← hx]
    gcongr
  constructor
  · exact habsconv
  · rw [Sum'.eq_tsum _ habsconv, Sum'.eq_tsum f hf]
    simp
    apply Summable.tsum_mul_left
    exact (AbsConvergent'.iff_Summable f).mp hf

/-- This law is not explicitly stated in Proposition 8.2.6, but follows easily from parts (a) and (b).-/
theorem Sum'.sub {X:Type} {f g:X → ℝ} (hf: AbsConvergent' f) (hg: AbsConvergent' g) :
  AbsConvergent' (f-g) ∧ Sum' (f - g) = Sum' f - Sum' g := by
  convert add hf (smul hg (-1)).1 using 2
  . simp; abel
  . congr; simp; abel
  rw [(smul hg (-1)).2]; ring

/-- Proposition 8.2.6 (c) (Absolutely convergent series laws) / Exercise 8.2.3.  The first
    part of this proposition has been moved to {lean}`AbsConvergent'.subtype`. -/
theorem Sum'.of_disjoint_union {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) {X₁ X₂ : Set X} (hdisj: Disjoint X₁ X₂):
  Sum' (fun x: (X₁ ∪ X₂: Set X) ↦ f x) = Sum' (fun x : X₁ ↦ f x) + Sum' (fun x : X₂ ↦ f x) := by
  have hsum := (AbsConvergent'.iff_Summable _).mp hf
  rw [Sum'.eq_tsum (X:=(X₁ ∪ X₂:Set X)) _ (h:=by exact AbsConvergent'.subtype hf (X₁ ∪ X₂))]
  rw [Sum'.eq_tsum (X:=(X₁:Set X)) _ (h:=by exact AbsConvergent'.subtype hf X₁)]
  rw [Sum'.eq_tsum (X:=(X₂:Set X)) _ (h:=by exact AbsConvergent'.subtype hf X₂)]
  rw [Summable.tsum_union_disjoint hdisj (Summable.subtype hsum X₁) (Summable.subtype hsum X₂)]

/-- This technical claim, the analogue of {name}`tsum_univ`, is required due to the way Mathlib handles
    sets.-/
theorem Sum'.of_univ {X:Type} {f:X → ℝ} (hf: AbsConvergent' f) :
  Sum' (fun x: (.univ : Set X) ↦ f x) = Sum' f := by
  have hsum := (AbsConvergent'.iff_Summable _).mp hf
  rw [Sum'.eq_tsum (X:=(.univ : Set X)) _ (h:=by exact AbsConvergent'.subtype hf Set.univ)]
  rw [Sum'.eq_tsum f hf]
  simp

theorem Sum'.of_comp {X Y:Type} {f:X → ℝ} (hf: AbsConvergent' f) {φ: Y → X}
  (hφ: Function.Bijective φ) :
  AbsConvergent' (f ∘ φ) ∧ Sum' f = Sum' (f ∘ φ) := by
  have habsconv : AbsConvergent' (f ∘ φ) := by
    choose a ha using hf
    use a
    intro x hx
    choose z hzuniv hz using hx
    simp at hz; rw [← hz]
    apply ha; simp
    use z.map ⟨φ, hφ.injective⟩; simp
  constructor
  · exact habsconv
  · rw [Sum'.eq_tsum f hf]
    rw [Sum'.eq_tsum _ habsconv]
    simp
    set e : Y ≃ X := Equiv.ofBijective φ hφ
    rw [← Equiv.tsum_eq e (fun x => f x)]
    apply tsum_congr
    intro b
    rfl

/-- Lemma 8.2.7 / Exercise 8.2.4 -/
lemma absConvergent_of_absConvergent_nonneg {a: ℕ → ℝ}
  (ha: (a:Series).converges)
  (hanonneg : AbsConvergent  (fun n : {n | a n ≥ 0} ↦ a n)):
  (a:Series).absConverges := by
  -- this is the shortest path i could think of without having to grapple with
  -- subtypes, COE etc.
  -- step 1 : show that (fun n : {n | a n ≥ 0} ↦ a n) is AbsConvergent'.
  -- step 2 : use this to show that (fun n : ℕ ↦ max (a n) 0) is AbsConvergent'.
  -- step 3 : strengthen step 2 to AbsConvergent by using the id bijection
  -- step 4 : rewrite absConverges as (fun n => |a n|).converges
  -- step 5 : rewrite (fun n => |a n|) as the difference between a and (fun n => max (a n) 0))
  -- step 6 : reduce the problem to Series.sub
  have habsconv' : AbsConvergent' (fun n : {n | a n ≥ 0} ↦ a n) := by
    by_cases! hfin : {n | a n ≥ 0}.Finite
    · have : Finite {n | a n ≥ 0} := hfin.to_subtype
      exact AbsConvergent'.of_finite _
    · have : Infinite  {n | a n ≥ 0} := hfin.to_subtype
      refine (AbsConvergent'.of_countable ?_).mpr hanonneg
      exact Nat.countable_of_infinite _
  have hmaxconv' : AbsConvergent' (fun n : ℕ ↦ max (a n) 0) := by
    choose M hM using habsconv'
    use M
    intro w hw
    choose A hA using hw; simp at hA
    have :  ∑ x ∈ A, |max (a x) 0| = ∑ x ∈ A, max (a x) 0 := by
      apply Finset.sum_congr rfl
      intro a ha; simp
    rw [← hA, this]
    let Asub := A.subtype (fun n => a n ≥ 0)
    have hsum : ∑ x ∈ A, max (a x) 0 = ∑ x ∈ Asub, |a x.val| := by
      rw [← Finset.sum_filter_add_sum_filter_not A (fun x ↦ a x ≥ 0)]
      have : ∑ x ∈ A with ¬a x ≥ 0, max (a x) 0 = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        simp at ha
        grind
      rw [this, add_zero]
      calc
        ∑ x ∈ A.filter (fun x ↦ a x ≥ 0), max (a x) 0
          = ∑ x ∈ Asub, max (a x.val) 0 := by
            apply Finset.sum_bij (fun x hx ↦ ⟨x, (by simp [Finset.mem_filter] at hx; exact hx.2)⟩)
            · intro x hx; simp at hx
              simp [Asub]; exact hx.1
            · intro x hx y hy hxy
              simp at hxy; exact hxy
            · intro x hx; simp at hx
              use x.val; simp; grind
            · intro a ha
              rfl
        _ = ∑ x ∈ Asub, |a ↑x| := by
            apply Finset.sum_congr rfl
            intro x _
            rw [max_eq_left x.property]
            rw [abs_of_nonneg x.property]
    rw [hsum]
    apply hM
    simp
  have hmaxconv : AbsConvergent (fun n : ℕ ↦ max (a n) 0) := by
    rw [← AbsConvergent'.of_countable]
    · exact hmaxconv'
    · use id; exact bijective_id
  have habsconv : (fun n ↦ max (a n) 0 : Series).absConverges := by
    have := AbsConvergent.comp (g:=id) (h:=by exact bijective_id) hmaxconv
    simp at this
    exact this
  have hnegconv : (fun n ↦ max (-a n) 0 : Series).converges := by
    have hsub : (fun n ↦ max (-a n) 0) = (fun n ↦ max (a n) 0) - a := by
      ext n; simp; grind
    rw [hsub]
    have := Series.sub (converges_of_absConverges habsconv) ha
    convert this.1 using 2
    ext n
    change _ = ((fun n ↦ max (a n) 0):Series).seq n - (a:Series).seq n
    simp
    split_ifs <;> grind
  suffices ((fun n => |a n|):Series).converges by
    unfold Series.absConverges
    convert this
    simp
    split_ifs <;> grind
  have := Series.add (converges_of_absConverges habsconv) hnegconv
  convert this.1 using 2
  ext n
  change _ = ((fun n ↦ max (a n) 0):Series).seq n + (fun n ↦ max (-a n) 0 : Series).seq n
  split_ifs <;> grind

lemma absConvergent_of_absConvergent_neg {a: ℕ → ℝ}
  (ha: (a:Series).converges)
  (hanonneg : AbsConvergent  (fun n : {n | a n < 0} ↦ a n)):
  (a:Series).absConverges := by
  have habsconv' : AbsConvergent' (fun n : {n | a n < 0} ↦ a n) := by
    by_cases! hfin : {n | a n < 0}.Finite
    · have : Finite {n | a n < 0} := hfin.to_subtype
      exact AbsConvergent'.of_finite _
    · have : Infinite  {n | a n < 0} := hfin.to_subtype
      refine (AbsConvergent'.of_countable ?_).mpr hanonneg
      exact Nat.countable_of_infinite _
  have hmaxconv' : AbsConvergent' (fun n ↦ max (-a n) 0) := by
    choose M hM using habsconv'
    use M
    intro w hw
    choose A hA using hw; simp at hA
    have : ∑ x ∈ A, |max (-a x) 0| = ∑ x ∈ A, max (-a x) 0 := by
     apply Finset.sum_congr rfl
     intro x hx
     simp
    rw [← hA, this]
    let Asub := A.subtype (fun n => a n < 0)
    have hsum : ∑ x ∈ A, max (-a x) 0 = ∑ x ∈ Asub, |a x.val| := by
      rw [← Finset.sum_filter_add_sum_filter_not A (fun x ↦ a x < 0)]
      have : ∑ x ∈ A with ¬a x < 0, max (-a x) 0 = 0 := by
        apply Finset.sum_eq_zero
        intro a ha
        simp at ha
        grind
      rw [this, add_zero]
      calc
        ∑ x ∈ A.filter (fun x ↦ a x < 0), max (-a x) 0
          = ∑ x ∈ Asub, max (-a x.val) 0 := by
              apply Finset.sum_bij (fun x hx ↦ ⟨x, (by simp [Finset.mem_filter] at hx; exact hx.2)⟩)
              · intro x hx; simp at hx
                simp [Asub]; exact hx.1
              · intro x hx y hy hxy
                simp at hxy; exact hxy
              · intro x hx; simp at hx
                use x.val; simp; grind
              · intro a ha
                rfl
          _ = ∑ x ∈ Asub, |a ↑x| := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [max_eq_left (by grind)]
            grind
    rw [hsum]
    apply hM
    simp
  have hmaxconv : AbsConvergent (fun n : ℕ ↦ max (-a n) 0) := by
    rw [← AbsConvergent'.of_countable]
    · exact hmaxconv'
    · use id; exact bijective_id
  have habsconv : (fun n ↦ max (-a n) 0 : Series).absConverges := by
    have := AbsConvergent.comp (g:=id) (h:=by exact bijective_id) hmaxconv
    simp at this
    exact this
  have hposconv : (fun n ↦ max (a n) 0 : Series).converges := by
    have hadd : (fun n ↦ max (a n) 0) = a + (fun n ↦ max (-a n) 0) := by
      ext n; simp; grind
    rw [hadd]
    have := Series.add ha (converges_of_absConverges habsconv)
    convert this.1 using 2
    ext n
    change _ = (a:Series).seq n + ((fun n ↦ max (-a n) 0):Series).seq n
    simp
    split_ifs <;> grind
  suffices ((fun n => |a n|):Series).converges by
    unfold Series.absConverges
    convert this
    simp
    split_ifs <;> grind
  have := Series.add hposconv (converges_of_absConverges habsconv)
  convert this.1 using 2
  ext n
  change _ = ((fun n ↦ max (a n) 0):Series).seq n + (fun n ↦ max (-a n) 0 : Series).seq n
  split_ifs <;> grind

theorem divergent_parts_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
    ¬ AbsConvergent (fun n : {n | a n ≥ 0} ↦ a n) ∧ ¬ AbsConvergent (fun n : {n | a n < 0} ↦ a n)
  := by
  by_contra h'
  rw [not_and_or] at h'
  rcases h' with hplus | hminus
  · push_neg at hplus
    exact absurd (absConvergent_of_absConvergent_nonneg ha hplus) ha'
  · push_neg at hminus
    exact absurd (absConvergent_of_absConvergent_neg ha hminus) ha'

theorem infinite_of_conditionally_convergent {a: ℕ → ℝ}
  (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) :
  Infinite { n | a n ≥ 0 } ∧ Infinite { n | a n < 0 } := by
  set A_plus := { n | a n ≥ 0 }
  set A_minus :=  { n | a n < 0 }
  let α : ℕ → ℝ := fun n => max (a n) 0
  let β : ℕ → ℝ := fun n => max (-a n) 0
  constructor
  · by_contra! hfin
    have heqsub : β = α - a := by
      ext n; unfold α β; simp
      grind
    have hαconv : (α:Series).converges := by
      by_cases! hemp : A_plus.Nonempty
      · have hfin' := Set.finite_coe_iff.mp hfin
        have hne : hfin'.toFinset.Nonempty := hfin'.toFinset_nonempty.mpr hemp
        let N₀ := hfin'.toFinset.max' hne
        use ∑ n ∈ Finset.Icc 0 N₀, α n
        unfold Series.convergesTo Series.partial
        rw [Metric.tendsto_atTop]
        intro ε hε
        use N₀; intro n hn
        lift n to ℕ using (by omega)
        simp at hn ⊢
        rw [Real.dist_eq]
        induction' n, hn using Nat.le_induction with k hlt ih
        · simp; grind
        · rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 0 (k + 1))]
          have : α (k+1) = 0 := by
            unfold α
            suffices a (k + 1) < 0 by exact max_eq_right_of_lt this
            have hnotmem : k + 1 ∉ A_plus := by
              intro h
              have := hfin'.toFinset.le_max' (k+1) (by exact (Set.Finite.mem_toFinset hfin').mpr h)
              grind
            unfold A_plus at hnotmem
            simp at hnotmem
            exact hnotmem
          rw [this]; simp; grind
      · have hge0 (n : ℕ) : a n < 0 := by
          by_contra! hlt0
          have hin : n ∈ A_plus := by exact hlt0
          grind
        use 0
        unfold Series.convergesTo Series.partial
        rw [Metric.tendsto_atTop]
        intro ε hε
        use 0; intro n hn
        lift n to ℕ using (by omega)
        simp
        induction' n with k ih
        · simp
          unfold α
          specialize hge0 0; grind
        · rw [Finset.sum_Icc_succ_top (by grind)]
          unfold α
          specialize hge0 (k+1)
          grind
    have hβconv : (β:Series).converges := by
      rw [heqsub]
      have := Series.sub hαconv ha
      convert this.1 using 2
      ext n
      change _ = (α:Series).seq n - (a:Series).seq n
      simp; split_ifs <;> grind
    have habsconv : (a:Series).absConverges := by
      have := Series.add hαconv hβconv
      unfold Series.absConverges Series.abs
      convert this.1 using 2
      ext n
      · change 0 = 0
        rfl
      · change _ = (α:Series).seq n + (β:Series).seq n
        simp; split_ifs
        · lift n to ℕ using by omega
          simp; unfold α β; exact (max_zero_add_max_neg_zero_eq_abs_self _).symm
        · simp
    exact absurd habsconv ha'
  · by_contra! hfin
    have heqadd : α = β + a := by
      ext n; unfold α β; simp
      grind
    have hβconv : (β:Series).converges := by
      by_cases! hemp : A_minus.Nonempty
      · have hfin' := Set.finite_coe_iff.mp hfin
        have hne : hfin'.toFinset.Nonempty := hfin'.toFinset_nonempty.mpr hemp
        let N₀ := hfin'.toFinset.max' hne
        use ∑ n ∈ Finset.Icc 0 N₀, β n
        unfold Series.convergesTo Series.partial
        rw [Metric.tendsto_atTop]
        intro ε hε
        use N₀; intro n hn
        lift n to ℕ using (by omega)
        simp at hn ⊢
        rw [Real.dist_eq]
        induction' n, hn using Nat.le_induction with k hlt ih
        · simp; grind
        · rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 0 (k + 1))]
          have : β (k+1) = 0 := by
            unfold β
            suffices a (k + 1) ≥  0 by grind
            have hnotmem : k + 1 ∉ A_minus := by
              intro h
              have := hfin'.toFinset.le_max' (k+1) (by exact (Set.Finite.mem_toFinset hfin').mpr h)
              grind
            unfold A_minus at hnotmem
            simp at hnotmem
            exact hnotmem
          rw [this]; simp
          exact ih
      · have hge0 (n : ℕ) : a n ≥ 0 := by
          by_contra! hlt0
          have hin : n ∈ A_minus := by exact hlt0
          rw [hemp] at hin
          simp at hin
        have hge0' (n : ℕ) : - a n ≤ 0 := by
          specialize hge0 n
          exact Right.neg_nonpos_iff.mpr hge0
        use 0
        unfold Series.convergesTo Series.partial
        rw [Metric.tendsto_atTop]
        intro ε hε
        use 0; intro n hn
        lift n to ℕ using (by omega)
        simp
        induction' n with k ih
        · simp
          unfold β
          specialize hge0 0; grind
        · rw [Finset.sum_Icc_succ_top (by exact Nat.le_add_left 0 (k + 1))]
          have : β (k+1) = 0 := by
            unfold β; specialize hge0' (k+1)
            apply max_eq_right hge0'
          rw [this]
          simp
          exact ih
    have hαconv : (α:Series).converges := by
      rw [heqadd]
      have := Series.add ha hβconv
      convert this.1 using 2
      ext n
      change _ = (a:Series).seq n + (β:Series).seq n
      simp; split_ifs
      · apply add_comm
      · simp
    have habsconv : (a:Series).absConverges := by
      have := Series.add hαconv hβconv
      unfold Series.absConverges Series.abs
      convert this.1 using 2
      ext n
      · change 0 = 0
        rfl
      · change _ = (α:Series).seq n + (β:Series).seq n
        simp; split_ifs
        · lift n to ℕ using by omega
          simp; unfold α β; exact (max_zero_add_max_neg_zero_eq_abs_self _).symm
        · simp
    exact absurd habsconv ha'

/-- Theorem 8.2.8 (Riemann rearrangement theorem) / Exercise 8.2.5 -/
theorem permute_convergesTo_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges) (L:ℝ) :
  ∃ f : ℕ → ℕ, Bijective f ∧ (a ∘ f:Series).convergesTo L
  := by
  -- This proof is written to follow the structure of the original text.
  choose h1 h2 using divergent_parts_of_divergent ha ha'
  set A_plus := { n | a n ≥ 0 }
  set A_minus := {n | a n < 0 }
  have hdisj : Disjoint A_plus A_minus := by
    rw [Set.disjoint_iff_inter_eq_empty]; ext; simp [A_plus, A_minus]
  have hunion : A_plus ∪ A_minus = .univ := by
    ext; simp [A_plus, A_minus]; grind
  have hA_plus_inf : Infinite A_plus := by exact (infinite_of_conditionally_convergent ha ha').1
  have hA_minus_inf : Infinite A_minus := by exact (infinite_of_conditionally_convergent ha ha').2
  obtain ⟨ a_plus, ha_plus_bij, ha_plus_mono ⟩ := (Nat.monotone_enum_of_infinite A_plus).exists
  obtain ⟨ a_minus, ha_minus_bij, ha_minus_mono ⟩ := (Nat.monotone_enum_of_infinite A_minus).exists
  let F : (n : ℕ) → ((m : ℕ) → m < n → ℕ) → ℕ :=
    fun j n' ↦ if ∑ i:Fin j, a (n' i (by simp)) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i (by simp) }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i (by simp) }
  let n' : ℕ → ℕ := Nat.strongRec F
  have hn' (j:ℕ) : n' j = if ∑ i:Fin j, a (n' i) < L then
      Nat.min { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i }
    else
      Nat.min { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i }
    := Nat.strongRec.eq_def _ j
  have hn'_plus_inf (j:ℕ) : Infinite { n ∈ A_plus | ∀ i:Fin j, n ≠ n' i } := by
    apply Set.infinite_coe_iff.mpr
    have : {n' i | i : Fin j}.Finite := Set.finite_range _
    convert Set.Infinite.diff (Set.infinite_coe_iff.mp hA_plus_inf) this using 1
    ext n; simp
    intro _; tauto
  have hn'_minus_inf (j:ℕ) : Infinite { n ∈ A_minus | ∀ i:Fin j, n ≠ n' i } := by
    apply Set.infinite_coe_iff.mpr
    have : {n' i | i : Fin j}.Finite := Set.finite_range _
    convert Set.Infinite.diff (Set.infinite_coe_iff.mp hA_minus_inf) this using 1
    ext n; simp
    intro _; tauto
  have hn'_inj : Injective n' := by
    have hn'_notclash (j : ℕ) : ∀ i : Fin j, n' j ≠ n' i := by
      have heq := hn' j
      split_ifs at heq with h
      · rw [heq]
        intro i
        have hinf := Set.infinite_coe_iff.mp (hn'_plus_inf j)
        have hne := hinf.nonempty
        have hmem := Nat.sInf_mem hne
        convert hmem.2 i using 1
        exact Nat.min_eq_sInf hne
      · rw [heq]
        intro i
        have hinf := Set.infinite_coe_iff.mp (hn'_minus_inf j)
        have hne := hinf.nonempty
        have hmem := Nat.sInf_mem hne
        convert hmem.2 i using 1
        exact Nat.min_eq_sInf hne
    intro a b hab
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have := (hn'_notclash b ⟨a, hlt⟩); simp at this
      exact absurd hab.symm this
    · exact heq
    · have := (hn'_notclash a ⟨b, hgt⟩); simp at this
      exact absurd hab this
  have h_case_I : Infinite { j | ∑ i:Fin j, a (n' i) < L } := by
    by_contra! hfin
    have hsum_gt: ∃ J : ℕ, ∀ j ≥ J, ∑ i : Fin j, a (n' i) ≥ L := by
      rw [Set.finite_coe_iff] at hfin
      choose J hJ using hfin.bddAbove
      use J+1
      intro j hj
      by_contra! h'
      have := hJ h'
      linarith
    have hpick_minus : ∃ J : ℕ, ∀ j ≥ J, n' j ∈ A_minus := by
      choose J hJ using hsum_gt
      use J
      intro j hj
      rw [hn' j]
      simp [not_lt.mpr (hJ j hj)]
      have hne := (Set.infinite_coe_iff.mp (hn'_minus_inf j)).nonempty
      have hmem := Nat.sInf_mem hne
      convert hmem.1 using 1
      exact Nat.min_eq_sInf hne
    have hcountable : CountablyInfinite A_minus := Nat.countable_of_infinite A_minus
    have habsiff := AbsConvergent.iff hcountable (fun (n : A_minus) => a n)
    have hunbound := (not_iff_not.mpr habsiff).mp h2
    choose J₁ hJ₁ using hsum_gt
    choose J₂ hJ₃ using hpick_minus
    set J := max J₁ J₂
    let L' : ℝ := ∑ i : Fin J, a (n' i)
    let S_used : ℝ := ∑ i : Fin J, |a (n' i)|
    let b : ℝ := (L' - L + 1) + S_used
    rw [not_bddAbove_iff] at hunbound
    choose sum_val hsumimg hgt using hunbound b
    simp at hsumimg
    choose A hA using hsumimg
    let A_nat : Finset ℕ := A.map ⟨Subtype.val, Subtype.val_injective⟩
    have hA_nat : ∑ x ∈ A_nat, |a x| = sum_val := by
      rw [Finset.sum_map]
      exact hA
    let X_max := A_nat.sup id
    let M := J + X_max + 1
    have hM_ge : M ≥ J := by omega
    have hM_contain : ∀ x ∈ A_nat, ∃ i : Fin M, n' i = x := by
      intro x hx
      have hx_le : x ≤ X_max := Finset.le_sup (f:=id) hx
      by_contra h_not_hit
      push_neg at h_not_hit
      let target_set := (Finset.range (X_max + 1)).erase x
      let index_range := Finset.Ico J (J + X_max + 1)
      let image_set := index_range.image n'
      have h_subset : image_set ⊆ target_set := by
        rw [Finset.subset_iff]
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_erase, Finset.mem_range]
        have hi_lt_M : i < M := by omega
        refine ⟨h_not_hit ⟨i, hi_lt_M⟩, ?_⟩
        rw [hn' i]
        split_ifs with h_choice
        · have hi_ge_J₁ : i ≥ J₁ := by omega
          have h_sum_ge := hJ₁ i hi_ge_J₁
          linarith
        · have h_in_set : x ∈ { n ∈ A_minus | ∀ j : Fin i, n ≠ n' j } := by
            dsimp; refine ⟨?_, ?_⟩
            · unfold A_nat at hx
              simp at hx
              tauto
            · intro j
              have hj_lt : (j : ℕ) < M := by omega
              exact (h_not_hit ⟨j, hj_lt⟩).symm
          have h_le_x := Nat.sInf_le h_in_set
          rw [← Nat.min_eq_sInf (by use x)] at h_le_x
          omega
      have h_card_le := Finset.card_le_card h_subset
      have h_image_card : image_set.card = X_max + 1 := by
        rw [Finset.card_image_of_injective _ hn'_inj]
        rw [Nat.card_Ico]
        nth_rewrite 1 [Nat.add_assoc]
        rw [Nat.add_sub_cancel_left]
      have h_target_card : target_set.card = X_max := by
        rw [Finset.card_erase_of_mem]
        · rw [Finset.card_range]; simp
        · rw [Finset.mem_range]; omega
      omega
    have h_split_sum : ∑ i : Fin M, |a (n' i)| = S_used + ∑ i : Fin (M - J), |a (n' (J + i))| := by
      have h_split := @Fin.sum_univ_add ℝ _ J (X_max + 1) (fun i => |a (n' i)|)
      change (∑ i : Fin M, |a (n' i)|) = (∑ i : Fin J, |a (n' i)|) + ∑ i : Fin (X_max + 1), |a (n' (J + ↑i))| at h_split
      rw [h_split]
      unfold S_used
      simp
      dsimp [M]
      have h_dim : J + X_max + 1 - J = X_max + 1 := by
        rw [Nat.add_assoc, Nat.add_sub_cancel_left]
      rw [h_dim]
    have h_tail_mass : ∑ i : Fin (M - J), |a (n' (J + i))| > L' - L + 1 := by
      have h_total_gt : sum_val ≤ ∑ i : Fin M, |a (n' i)| := by
        rw [← hA_nat]
        rw [Fin.sum_univ_eq_sum_range (fun i => |a (n' i)|)]
        let I := (Finset.range M).filter (fun i => n' i ∈ A_nat)
        have h_image : A_nat = I.image n' := by
          ext x
          rw [Finset.mem_image]
          constructor
          · intro hx
            choose i hieq using hM_contain x hx
            use i
            constructor
            · grind only [usr Fin.isLt, = mem_filter, = mem_range]
            · exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd hieq) (n' J₁))
          · intro hi
            choose i hi' using hi
            unfold A_nat
            grind only [= mem_filter]
        rw [h_image]
        rw [Finset.sum_image (fun i1 _ i2 _ h => hn'_inj h)]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.filter_subset
        · intro i _ _; simp
      linarith
    have h_tail_neg : ∑ i : Fin (M - J), a (n' (J + i)) = - ∑ i : Fin (M - J), |a (n' (J + i))| := by
      rw [← Finset.sum_neg_distrib]
      congr 1
      ext i
      have h_in_minus := hJ₃ (J+i) (by omega)
      unfold A_minus at h_in_minus; simp at h_in_minus
      rw [abs_of_neg h_in_minus]
      simp
    have h_sum_M_val : ∑ i : Fin M, a (n' i) < L := by
      have h_split_raw := @Fin.sum_univ_add ℝ _ J (X_max + 1) (fun i => a (n' i))
      change (∑ i : Fin M, a (n' i)) = (∑ i : Fin J, a (n' i)) + ∑ i : Fin (X_max + 1), a (n' (J + ↑i)) at h_split_raw
      rw [h_split_raw]
      have h_dim : M - J = X_max + 1 := by omega
      rw [← h_dim]
      rw [h_tail_neg]
      linarith
    have hmge1 : M ≥ J₁ := by
      have : M ≥ J := hM_ge
      have : J ≥ J₁ := by exact Nat.le_max_left J₁ J₂
      linarith
    have := hJ₁ M hmge1
    linarith
  have h_case_II : Infinite { j | ∑ i:Fin j, a (n' i) ≥ L } := by
    by_contra! hfin
    have hsum_lt: ∃ J : ℕ, ∀ j ≥ J, ∑ i : Fin j, a (n' i) < L := by
      rw [Set.finite_coe_iff] at hfin
      choose J hJ using hfin.bddAbove
      use J+1
      intro j hj
      by_contra! h'
      have := hJ h'
      linarith
    have hpick_plus : ∃ J : ℕ, ∀ j ≥ J, n' j ∈ A_plus := by
      choose J hJ using hsum_lt
      use J
      intro j hj
      rw [hn' j]
      simp [hJ j hj]
      have hne := (Set.infinite_coe_iff.mp (hn'_plus_inf j)).nonempty
      have hmem := Nat.sInf_mem hne
      convert hmem.1 using 1
      exact Nat.min_eq_sInf hne
    have hcountable : CountablyInfinite A_plus := Nat.countable_of_infinite A_plus
    have habsiff := AbsConvergent.iff hcountable (fun (n : A_plus) => a n)
    have hunbound := (not_iff_not.mpr habsiff).mp h1
    choose J₁ hJ₁ using hsum_lt
    choose J₂ hJ₃ using hpick_plus
    set J := max J₁ J₂
    let L' : ℝ := ∑ i : Fin J, a (n' i)
    let S_used : ℝ := ∑ i : Fin J, |a (n' i)|
    let b : ℝ := (L - L' + 1) + S_used
    rw [not_bddAbove_iff] at hunbound
    choose sum_val hsumimg hgt using hunbound b
    simp at hsumimg
    choose A hA using hsumimg
    let A_nat : Finset ℕ := A.map ⟨Subtype.val, Subtype.val_injective⟩
    have hA_nat : ∑ x ∈ A_nat, |a x| = sum_val := by
      rw [Finset.sum_map]
      exact hA
    let X_max := A_nat.sup id
    let M := J + X_max + 1
    have hM_ge : M ≥ J := by omega
    have hM_contain : ∀ x ∈ A_nat, ∃ i : Fin M, n' i = x := by
      intro x hx
      have hx_le : x ≤ X_max := Finset.le_sup (f:=id) hx
      by_contra h_not_hit
      push_neg at h_not_hit
      let target_set := (Finset.range (X_max + 1)).erase x
      let index_range := Finset.Ico J (J + X_max + 1)
      let image_set := index_range.image n'
      have h_subset : image_set ⊆ target_set := by
        rw [Finset.subset_iff]
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        rw [Finset.mem_Ico] at hi
        rw [Finset.mem_erase, Finset.mem_range]
        have hi_lt_M : i < M := by omega
        refine ⟨h_not_hit ⟨i, hi_lt_M⟩, ?_⟩
        rw [hn' i]
        split_ifs with h_choice
        · have h_in_set : x ∈ { n ∈ A_plus | ∀ j : Fin i, n ≠ n' j } := by
            dsimp; refine ⟨?_, ?_⟩
            · unfold A_nat at hx
              simp at hx
              tauto
            · intro j
              have hj_lt : (j : ℕ) < M := by omega
              exact (h_not_hit ⟨j, hj_lt⟩).symm
          have h_le_x := Nat.sInf_le h_in_set
          rw [← Nat.min_eq_sInf (by use x)] at h_le_x
          omega
        · have hi_ge_J₁ : i ≥ J₁ := by omega
          have h_sum_lt := hJ₁ i hi_ge_J₁
          linarith
      have h_card_le := Finset.card_le_card h_subset
      have h_image_card : image_set.card = X_max + 1 := by
        rw [Finset.card_image_of_injective _ hn'_inj]
        rw [Nat.card_Ico]
        nth_rewrite 1 [Nat.add_assoc]
        rw [Nat.add_sub_cancel_left]
      have h_target_card : target_set.card = X_max := by
        rw [Finset.card_erase_of_mem]
        · rw [Finset.card_range]; simp
        · rw [Finset.mem_range]; omega
      omega
    have h_split_sum : ∑ i : Fin M, |a (n' i)| = S_used + ∑ i : Fin (M - J), |a (n' (J + i))| := by
      have h_split := @Fin.sum_univ_add ℝ _ J (X_max + 1) (fun i => |a (n' i)|)
      change (∑ i : Fin M, |a (n' i)|) = (∑ i : Fin J, |a (n' i)|) + ∑ i : Fin (X_max + 1), |a (n' (J + ↑i))| at h_split
      rw [h_split]
      unfold S_used
      simp
      dsimp [M]
      have h_dim : J + X_max + 1 - J = X_max + 1 := by
        rw [Nat.add_assoc, Nat.add_sub_cancel_left]
      rw [h_dim]
    have h_tail_mass : ∑ i : Fin (M - J), |a (n' (J + i))| > L - L' := by
      have h_tail_eq : ∑ i : Fin (M - J), |a (n' (J + i))| = (∑ i : Fin M, |a (n' i)|) - S_used := by
        rw [h_split_sum]
        ring
      have h_total_gt : sum_val ≤ ∑ i : Fin M, |a (n' i)| := by
        rw [← hA_nat]
        rw [Fin.sum_univ_eq_sum_range (fun i => |a (n' i)|)]
        let I := (Finset.range M).filter (fun i => n' i ∈ A_nat)
        have h_image : A_nat = I.image n' := by
          ext x
          rw [Finset.mem_image]
          constructor
          · intro hx
            choose i hieq using hM_contain x hx
            use i
            constructor
            · grind only [usr Fin.isLt, = mem_filter, = mem_range]
            · exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd hieq) (n' J₁))
          · intro hi
            choose i hi' using hi
            unfold A_nat
            grind only [= mem_filter]
        rw [h_image]
        rw [Finset.sum_image (fun i1 _ i2 _ h => hn'_inj h)]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · apply Finset.filter_subset
        · intro i _ _; simp
      rw [h_tail_eq]
      calc
        _ ≥ sum_val - S_used := by linarith [h_total_gt]
        _ > ((L - L' + 1) + S_used) - S_used := by linarith [hgt]
        _ = L - L' + 1 := by ring
        _ > L - L' := by linarith
    have h_tail_pos : ∑ i : Fin (M - J), a (n' (J + i)) = ∑ i : Fin (M - J), |a (n' (J + i))| := by
      congr 1
      ext i
      have h_in_plus := hJ₃ (J+i) (by omega)
      unfold A_plus at h_in_plus; simp at h_in_plus
      rw [abs_of_nonneg h_in_plus]
    have h_sum_M_val : ∑ i : Fin M, a (n' i) ≥ L := by
      have h_split_raw := @Fin.sum_univ_add ℝ _ J (X_max + 1) (fun i => a (n' i))
      change (∑ i : Fin M, a (n' i)) = (∑ i : Fin J, a (n' i)) + ∑ i : Fin (X_max + 1), a (n' (J + ↑i)) at h_split_raw
      rw [h_split_raw]
      have h_dim : M - J = X_max + 1 := by omega
      rw [← h_dim]
      rw [h_tail_pos]
      linarith
    have hmge1 : M ≥ J₁ := by
      have : M ≥ J := hM_ge
      have : J ≥ J₁ := by exact Nat.le_max_left J₁ J₂
      linarith
    have := hJ₁ M hmge1
    linarith
  have hn'_surj : Surjective n' := by
    intro j
    by_contra! hnotsurj
    let S := { x : ℕ | ∀ j, n' j ≠ x }
    have hnonempty : S.Nonempty := by
      use j
      exact hnotsurj
    have hsinfinS := Nat.sInf_mem hnonempty
    set m := sInf S
    have hm : ∀ j, n' j ≠ m := by
      unfold S at hsinfinS
      exact hsinfinS
    have h_below_picked (k : ℕ) (hk : k < m) : ∃ j, n' j = k := by
    -- Since m = sInf S, any k < m cannot be in S (the set of missing elements).
      have hk_not_in_S : k ∉ S := by
        intro h_in_S
        exact absurd (Nat.sInf_le h_in_S) (by omega)
      unfold S at hk_not_in_S; simp at hk_not_in_S
      exact hk_not_in_S
    have hmem : m ∈ A_plus ∪ A_minus := by
      rw [hunion]
      tauto
    have hfin : Set.Finite { j | n' j < m } := by
      have : { j | n' j < m } = n' ⁻¹' (Set.Iio m) := by ext; simp
      rw [this]
      apply Set.Finite.preimage (by exact Injective.injOn hn'_inj)
      exact Set.finite_Iio m
    choose N hN using hfin.bddAbove
    have hN' : ∀ j > N, m ≤ n' j := by
      intro j hj
      by_contra! h'
      have := hN h'
      omega
    rcases hmem with hplus | hminus
    · choose j hj_case hj_gt using Set.Infinite.exists_gt (Set.infinite_coe_iff.mp h_case_I) N
      have hn'j : n' j = sInf { n ∈ A_plus | ∀ i : Fin j, n ≠ n' i } := by
        rw [hn' j, if_pos (by grind), Nat.min_eq_sInf (by exact Set.Nonempty.of_subtype)]
      have hm_candidate : m ∈ { n ∈ A_plus | ∀ i : Fin j, n ≠ n' i } := by
        refine ⟨hplus, ?_⟩
        intro i
        exact (hm i).symm
      have hle : n' j ≤ m := by
        rw [hn'j]
        exact Nat.sInf_le hm_candidate
      have heq : n' j = m := by grind
      exact hm j heq
    · choose j hj_case hj_gt using Set.Infinite.exists_gt (Set.infinite_coe_iff.mp h_case_II) N
      have hn'j : n' j = sInf { n ∈ A_minus | ∀ i : Fin j, n ≠ n' i } := by
        rw [hn' j, if_neg (by grind), Nat.min_eq_sInf (by exact Set.Nonempty.of_subtype)]
      have hm_candidate : m ∈ { n ∈ A_minus | ∀ i : Fin j, n ≠ n' i } := by
        refine ⟨hminus, ?_⟩
        intro i
        exact (hm i).symm
      have hle : n' j ≤ m := by
        rw [hn'j]
        exact Nat.sInf_le hm_candidate
      have heq : n' j = m := by grind
      exact hm j heq
  have hconv : atTop.Tendsto (a ∘ n') (nhds 0) := by
    have hatt0 : atTop.Tendsto a (nhds 0) := by
      have htt := Series.decay_of_converges ha
      rw [Metric.tendsto_atTop] at htt ⊢
      intro ε hε
      choose N hN using htt ε hε
      use N.toNat
      intro n hn
      specialize hN n (by omega)
      simp at hN ⊢
      exact hN
    have hn'_tendsto : Tendsto n' atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      have hfin : { j | n' j < b }.Finite := by
        apply (Set.finite_Iio b).preimage
        intro x _ y _ hxy
        exact hn'_inj hxy
      obtain ⟨N, hN⟩ := hfin.bddAbove
      use N+1
      by_contra! h'
      choose N' hN' using h'
      have := hN hN'.2
      linarith
    exact hatt0.comp hn'_tendsto
  have hsum : (a ∘ n':Series).convergesTo L := by
    unfold Series.convergesTo Series.partial
    simp
    suffices alternatively : Tendsto (fun N:ℕ ↦ ∑ x ∈ range N, a (n' x)) atTop (nhds L) by
      rw [Metric.tendsto_atTop] at alternatively ⊢
      simp_rw [Real.dist_eq] at alternatively ⊢
      intro ε hε
      choose N hN using alternatively ε hε
      use max 0 N
      intro n hn
      lift n to ℕ using by omega
      specialize hN (n+1) (by omega)
      simp
      rwa [Nat.range_succ_eq_Icc_zero] at hN
    suffices alternatively : Tendsto (fun N:ℕ ↦ ∑ i:Fin N, a (n' i)) atTop (nhds L) by
      convert alternatively using 2 with N
      rw [← Fin.sum_univ_eq_sum_range]
    have h_crossing : ∀ N, ∃ k ≥ N,
      (∑ i : Fin k, a (n' i) < L ∧ ∑ i : Fin (k+1), a (n' i) ≥ L) ∨
      (∑ i : Fin k, a (n' i) ≥ L ∧ ∑ i : Fin (k+1), a (n' i) < L) := by
      by_contra! h'
      choose N hN using h'
      by_cases! hSN : ∑ i : Fin N, a (n' i) < L
      · have hstay : ∀ j ≥ N, ∑ i : Fin j, a (n' i) < L := by
          intro j hj
          induction' j, hj using Nat.le_induction with k hk ih
          · exact hSN
          · specialize hN k hk
            exact hN.1 ih
        have hfin : Finite { j | ∑ i : Fin j, a (n' i) ≥ L } := by
          apply Set.Finite.subset (Set.finite_Iio N)
          intro j hj
          simp at hj ⊢
          by_contra! h'
          specialize hstay j h'
          linarith only [hstay, hj]
        exact h_case_II.not_finite hfin
      · have hstay : ∀ j ≥ N, ∑ i : Fin j, a (n' i) ≥ L := by
          intro j hj
          induction' j, hj using Nat.le_induction with k hk ih
          · exact hSN
          · specialize hN k hk
            exact hN.2 ih
        have hfin : Finite { j | ∑ i : Fin j, a (n' i) < L } := by
          apply Set.Finite.subset (Set.finite_Iio N)
          intro j hj
          simp at hj ⊢
          by_contra! h'
          specialize hstay j h'
          linarith only [hstay, hj]
        exact h_case_I.not_finite hfin
    rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε hε
    choose N hN using hconv ε hε
    simp_rw [Real.dist_eq] at hN ⊢
    simp_rw [sub_zero] at hN
    choose k hk hcross using h_crossing N
    have hstep (k:ℕ) : ∑ i : Fin (k+1), a (n' i) = (∑ i : Fin k, a (n' i)) + a (n' k) := by
      rw [Fin.sum_univ_castSucc]; simp
    use k+1
    intro n hn
    induction' n, hn using Nat.le_induction with m hm ih
    · rcases hcross with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hstep] at hr ⊢
        specialize hN k hk
        have := (abs_lt.mp hN).2; simp at this
        rw [abs_lt]
        constructor <;> linarith
      · rw [hstep] at hr ⊢
        specialize hN k hk
        have := (abs_lt.mp hN).1; simp at this
        rw [abs_lt]
        constructor <;> linarith
    · by_cases! h1 : ∑ i : Fin m, a (n' i) < L <;> by_cases! h2 : ∑ i : Fin (m+1), a (n' i) < L
      · have hn'm_plus : n' m ∈ A_plus := by
          have heq : n' m = sInf { n ∈ A_plus | ∀ i : Fin m, n ≠ n' i } := by
            rw [hn' m, if_pos h1]
            rw [Nat.min_eq_sInf (by exact Set.Nonempty.of_subtype)]
          have hmem : sInf { n ∈ A_plus | ∀ i : Fin m, n ≠ n' i } ∈
              { n ∈ A_plus | ∀ i : Fin m, n ≠ n' i } := by
              apply Nat.sInf_mem
              exact Set.Nonempty.of_subtype
          rw [← heq] at hmem
          exact hmem.1
        have hpos : a (n' m) ≥ 0 := by exact hn'm_plus
        rw [hstep] at h2 ⊢
        rw [abs_lt] at ih ⊢
        constructor <;> linarith
      · specialize hN m (by omega); simp at hN
        rw [hstep] at h2 ⊢
        rw [abs_lt] at ih hN ⊢
        constructor <;> linarith
      · specialize hN m (by omega); simp at hN
        rw [hstep] at h2 ⊢
        rw [abs_lt] at ih hN ⊢
        constructor <;> linarith
      · have hn'm_minus : n' m ∈ A_minus := by
          have heq : n' m = sInf { n ∈ A_minus | ∀ i : Fin m, n ≠ n' i } := by
            rw [hn' m, if_neg (by linarith)]
            rw [Nat.min_eq_sInf (by exact Set.Nonempty.of_subtype)]
          have hmem : sInf { n ∈ A_minus | ∀ i : Fin m, n ≠ n' i } ∈
              { n ∈ A_minus | ∀ i : Fin m, n ≠ n' i } := by
              apply Nat.sInf_mem
              exact Set.Nonempty.of_subtype
          rw [← heq] at hmem
          exact hmem.1
        have hpos : a (n' m) < 0 := by exact hn'm_minus
        rw [hstep] at h2 ⊢
        rw [abs_lt] at ih ⊢
        constructor <;> linarith
  use n'
  refine ⟨ ⟨ hn'_inj, hn'_surj ⟩, ?_ ⟩; convert hsum

/-- Exercise 8.2.6 -/
theorem permute_diverges_of_divergent {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊤) := by
  sorry

theorem permute_diverges_of_divergent' {a: ℕ → ℝ} (ha: (a:Series).converges)
  (ha': ¬ (a:Series).absConverges)  :
  ∃ f : ℕ → ℕ,  Bijective f ∧ atTop.Tendsto (fun N ↦ ((a ∘ f:Series).partial N : EReal)) (nhds ⊥) := by
  sorry


end Chapter8
