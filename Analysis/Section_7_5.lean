import Mathlib.Tactic
import Analysis.Section_6_4
import Analysis.Section_7_4
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics



/-!
# Analysis I, Section 7.5: The root and ratio tests

I have attempted to make the translation as faithful a paraphrasing as possible of the original text.  When there is a choice between a more idiomatic Lean solution and a more faithful translation, I have generally chosen the latter.  In particular, there will be places where the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing so.

Main constructions and results of this section:

- The root and ratio tests/

A point that is only implicitly stated in the text is that for the root and ratio tests, the lim inf and lim sup should be interpreted within the extended reals.  The Lean formalizations below make this point more explicit.

-/

namespace Chapter7

open Filter Real EReal

/-- Theorem 7.5.1(a) (Root test).  A technical condition is needed to ensure the limsup is finite. -/
theorem Series.root_test_pos {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) < 1) : s.absConverges := by
    -- This proof is written to follow the structure of the original text.
    set α':EReal := atTop.limsup (fun n ↦ ↑(|s.seq n|^(1/(n:ℝ)):ℝ))
    have hpos : 0 ≤ α' := by
      apply le_limsup_of_frequently_le (Frequently.of_forall _) (by isBoundedDefault)
      intros; positivity
    set α := α'.toReal
    have hαα' : α' = α := by
      symm; apply coe_toReal
      . contrapose! h; simp [h]; exact le_top
      contrapose! hpos; simp [hpos]
    rw [hαα'] at h hpos; norm_cast at h hpos
    set ε := (1-α)/2
    have hε : 0 < ε := by simp [ε]; linarith
    have hε' : α' < (α+ε:ℝ) := by rw [hαα', EReal.coe_lt_coe_iff]; linarith
    have hα : α + ε < 1 := by simp [ε]; linarith
    have hα' : 0 < α + ε := by linarith
    have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
    rw [eventually_atTop] at this
    choose N' hN using this; set N := max N' (max s.m 1)
    have (n:ℤ) (hn: n ≥ N) : |s.seq n| ≤ (α + ε)^n := by
      have : n ≥ N' := by omega
      have npos : 0 < n := by omega
      specialize hN n this
      rw [EReal.coe_lt_coe_iff] at hN
      calc
        _ = (|s.seq n|^(1/(n:ℝ)))^n := by
          rw [←rpow_intCast, ←rpow_mul (by positivity)]
          symm; convert rpow_one _; field_simp
        _ ≤ _ := by
          convert pow_le_pow_left₀ (by positivity) (le_of_lt hN) n.toNat
          all_goals convert zpow_natCast _ _; omega
    set k := (N - s.m).toNat
    have hNk : N = s.m + k := by omega
    have hgeom : (fun n ↦ (α+ε) ^ n : Series).converges := by
      simp [converges_geom_iff, abs_of_pos hα', hα]
    rw [converges_from _ N.toNat] at hgeom
    have : (s.from N).absConverges := by
      apply (converges_of_le _ _ hgeom).1
      . simp; omega
      intro n hn; simp at hn
      have hn' : n ≥ 0 := by omega
      simp [hn.1, hn.2, hn']
      convert this n hn.2; symm; convert zpow_natCast _ _; omega
    unfold absConverges at this ⊢
    rw [converges_from _ k]; convert this; simp; refine ⟨ by omega, ?_ ⟩
    ext n
    by_cases hnm : n ≥ s.m <;> simp [hnm]
    by_cases hn: n ≥ N <;> simp [hn] <;> grind


/-- Theorem 7.5.1(b) (Root test) -/
theorem Series.root_test_neg {s : Series}
  (h : atTop.limsup (fun n ↦ ((|s.seq n|^(1/(n:ℝ)):ℝ):EReal)) > 1) : s.diverges := by
    -- This proof is written to follow the structure of the original text.
    apply frequently_lt_of_lt_limsup (by isBoundedDefault) at h
    apply diverges_of_nodecay
    by_contra this; rw [LinearOrderedAddCommGroup.tendsto_nhds] at this; specialize this 1 (by positivity)
    choose n hn hs hs' using (h.and_eventually this).forall_exists_of_atTop 1
    simp at hs'; replace hs' := rpow_lt_one ?_ hs' (?_:0 < 1/(n:ℝ)) <;> try positivity
    rw [show (1:EReal) = (1:ℝ) by simp, EReal.coe_lt_coe_iff] at hs
    linarith

/-- Theorem 7.5.1(c) (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive: ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.diverges := by
  set a : ℕ → ℝ := fun _ => 1
  use (a:Series)
  constructor
  · simp; rw [Metric.tendsto_atTop]
    intro ε hε
    use 0; intro n hn
    lift n to ℕ using by omega
    rw [Real.dist_eq, if_pos (by grind)]
    unfold a; simp
    exact hε
  · have hsum (n:ℕ) : (a:Series).partial n = (n + 1:ℝ) := by
      induction' n with k ih
      · unfold Series.partial; simp
        unfold a; simp
      · unfold Series.partial at ih ⊢; simp at ih ⊢
        rw [sum_of_nonempty (by grind), ih]
        rw [if_pos (by grind)]
    have hdiv : Filter.Tendsto (a:Series).partial Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      use max 0 ⌈b⌉
      intro n hn
      lift n to ℕ using by omega
      specialize hsum n
      rw [hsum]
      have hleceil := Int.le_ceil b
      have h' : ⌈b⌉ ≤ n := by grind
      rify at h'
      grind
    intro hconv
    unfold Series.converges at hconv
    choose L hL using hconv
    unfold Series.convergesTo at hL
    exact not_tendsto_nhds_of_tendsto_atTop hdiv L hL


lemma Series.root_test_seq : Filter.Tendsto (fun n:ℕ ↦ ((n:ℝ)+1)^(1/(n:ℝ))) Filter.atTop (nhds 1) := by
  -- some ugliness here becase we have tendsto_rpow_div : Tendsto (fun x ↦ x ^ (1 / x)) atTop (nhds 1)
  -- but actually we are using the definition of zeta in Section 7 2, which
  -- means that we need to compare (x+1) ^ (1/x) instead.
  have h2 : Filter.Tendsto (fun n:ℕ ↦ (2:ℝ)^(1/(n:ℝ))) Filter.atTop (nhds 1) := by
    have hcont := Real.continuous_const_rpow (a:=2) (by norm_num)
    convert hcont.continuousAt.tendsto.comp tendsto_one_div_atTop_nhds_zero_nat
    simp
  have hlt : Filter.Tendsto (fun n:ℕ ↦ ((2:ℝ)*n)^(1/(n:ℝ))) Filter.atTop (nhds 1) := by
    convert h2.mul (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop) using 1
    · ext n; simp
      rw [mul_rpow (by grind) (by grind)]
    · simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'       -- squeeze theorem
    (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop)  -- lower bound
    hlt                                                  -- upper bound
  · rw [Filter.eventually_atTop]
    use 0; intro n hn
    simp; gcongr; linarith
  · rw [Filter.eventually_atTop]
    use 1; intro n hn
    simp; gcongr; norm_cast; grind

lemma Series.root_test_seq' : Filter.Tendsto (fun n:ℤ ↦ ((n:ℝ)+1)^(1/(n:ℝ))) Filter.atTop (nhds 1) := by
  have hnat := Series.root_test_seq
  rw [Metric.tendsto_atTop] at hnat ⊢
  intro ε hε
  choose N hN using hnat ε hε
  use N; intro n hn
  lift n to ℕ using by omega
  specialize hN n (by grind)
  rw [Real.dist_eq] at hN ⊢
  push_cast; exact hN

/-- Theorem 7.5.1 (Root test) / Exercise 7.5.3 -/
theorem Series.root_test_inconclusive' : ∃ s:Series,
  atTop.Tendsto (fun n ↦ |s.seq n|^(1/(n:ℝ))) (nhds 1) ∧ s.absConverges := by
  use (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  constructor
  · simp
    have hinv := Series.root_test_seq'.inv₀ (a:=1) (by norm_num)
    have hpow := hinv.pow 2; simp at hpow
    apply (Filter.tendsto_congr' _).mpr hpow
    filter_upwards [Filter.eventually_ge_atTop 0]
    intro n hn
    lift n to ℕ using by omega
    rw [if_pos (by grind)]
    simp; norm_cast
    rw [inv_rpow (by positivity)]
    congr 1
    conv_rhs => rw [← rpow_natCast]
    conv_lhs => rw [Nat.cast_pow, ← rpow_natCast]
    rw [← rpow_mul (by positivity), ← rpow_mul (by positivity)]
    congr 1
    grind
  · unfold Series.absConverges
    convert Series.zeta_2_converges with n
    simp_all

#check Filter.liminf_le_liminf_of_le

/-- Lemma 7.5.2 / Exercise 7.5.1 -/
theorem Series.ratio_ineq {c:ℤ → ℝ} (m:ℤ) (hpos: ∀ n ≥ m, c n > 0) :
  atTop.liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) ≤
    atTop.liminf (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.liminf (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑((c n)^(1/(n:ℝ)):ℝ))
  ∧ atTop.limsup (fun n ↦ (((c n)^(1/(n:ℝ)):ℝ):EReal)) ≤
    atTop.limsup (fun n ↦ ↑(c (n+1) / c n:ℝ))
    := by
  -- This proof is written to follow the structure of the original text.
  refine ⟨ ?_, liminf_le_limsup ?_ ?_, ?_ ⟩ <;> try isBoundedDefault
  · set L' := liminf (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
    set L'' := liminf (fun n ↦ (((c n) ^ (1 / (n:ℝ)):ℝ):EReal)) atTop
    have hL'pos : 0 ≤ L' := by
        unfold L'
        apply Filter.le_liminf_of_le (by isBoundedDefault)
        filter_upwards [Filter.eventually_ge_atTop m]
        intro n hn
        have hposn := hpos n (by grind)
        have hposn1 := hpos (n+1) (by grind)
        positivity
    have hL''pos : 0 ≤ L'' := by
        apply le_liminf_of_le (by isBoundedDefault)
        filter_upwards [Filter.eventually_ge_atTop m]
        intro a ha
        specialize hpos a (by grind)
        positivity
    have hL'notbot : L' ≠ ⊥ := by intro hbot; rw [hbot] at hL'pos; simp at hL'pos
    have hL''notbot : L'' ≠ ⊥ := by intro hbot; rw [hbot] at hL''pos; simp at hL''pos
    apply le_of_forall_lt_imp_le_of_dense
    intro y hy
    by_cases! hybot : y = ⊥
    · rw [hybot]; apply bot_le
    by_cases! hytop : y = ⊤
    · rw [hytop] at hy
      exact absurd hy not_top_lt
    by_cases! hL''top : L'' = ⊤
    · rw [hL''top]; apply le_top
    lift y to ℝ using ⟨hytop, hybot⟩
    by_cases! hy0 : y ≤ 0
    · have := EReal.coe_le_coe hy0
      exact le_trans this hL''pos
    have hcratio : ∃ N:ℤ, ∀ n ≥ N, y < c (n+1) / c n := by
      have := eventually_lt_of_lt_liminf hy (by isBoundedDefault)
      rw [eventually_atTop] at this
      choose N hN using this
      use N; intro n hn
      specialize hN n hn; simp at hN
      exact hN
    choose M hM using hcratio
    set N := max 1 (max m M)
    have hNgt1 : (N:ℝ) ≥ 1 := by
      norm_cast; grind
    set κ : ℝ := c N / y ^ (N:ℝ)
    have hκpos : 0 < κ := by
      specialize hpos N (by grind)
      positivity
    set φ : ℤ → ℝ := fun n => (κ ^ (1 / (n:ℝ))) * y
    have hle : ∀ᶠ (n:ℤ) in Filter.atTop, φ n ≤ (c n ^ (1 / (n:ℝ))) := by
      rw [eventually_atTop]
      use N; intro n hn
      induction' n, hn using Int.le_induction with k hnn ih
      · unfold φ κ
        specialize hpos N (by omega)
        conv_lhs =>
          rw [div_rpow (by positivity) (by positivity)]
          rw [← rpow_mul (by positivity)]
          rw [mul_one_div_cancel (by grind), rpow_one]
        field_simp
        rfl
      · have hckpos := hpos k (by omega)
        have hck1pos := hpos (k+1) (by omega)
        have hkt1 : (k:ℝ) ≥ 1 := by norm_cast; omega
        have ih' := (Real.rpow_le_rpow_iff (z:=(k:ℝ)) (hx:=by positivity) (hy:=by positivity) (hz:=by positivity)).mpr ih
        rw [mul_rpow (by positivity) (by positivity)] at ih'
        rw [← rpow_mul (by positivity), ← rpow_mul (by positivity)] at ih'
        field_simp at ih'
        unfold κ at ih'
        rw [rpow_one, rpow_one] at ih'
        suffices φ (k+1) ^ ((k:ℝ)+1) ≤ c (k+1) by
          have halt := (Real.rpow_le_rpow_iff (z:=(1/((k:ℝ)+1))) (hx:=by positivity) (hy:=by positivity) (hz:=by positivity)).mpr this
          rw [← rpow_mul (by positivity)] at halt
          rw [mul_one_div_cancel (by grind), rpow_one] at halt
          exact_mod_cast halt
        unfold φ κ
        rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity)]
        push_cast; field_simp
        rw [rpow_one, rpow_add (by positivity), rpow_one, ← mul_assoc]
        specialize hM k (by omega)
        field_simp at hM
        nlinarith
    have hle' :  ∀ᶠ (n:ℤ) in Filter.atTop, ((φ n):EReal) ≤ (((c n)^(1/(n:ℝ)):ℝ):EReal) := by
      rw [eventually_atTop] at hle ⊢
      choose N hN using hle
      use N; intro n hn
      specialize hN n hn
      exact_mod_cast hN
    have htt : Filter.Tendsto φ Filter.atTop (nhds y) := by
      unfold φ
      have hdivtt : Filter.Tendsto (fun n:ℤ => 1/(n:ℝ)) Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]
        simp_rw [Real.dist_eq, sub_zero]
        intro ε hε
        choose N hN using exists_nat_gt (1/ε)
        have hN0 : 0 < N := by
          rify
          have : 0 < 1 / ε := by positivity
          grind
        field_simp at hN
        use N
        intro n hn
        have hn0 : 0 < n := by omega
        rw [abs_of_pos (by positivity)]
        field_simp
        rify at hN hn ⊢
        nlinarith
      have hpow := (Real.continuousAt_const_rpow (a:=κ) (by grind)).tendsto.comp hdivtt
      simp at hpow
      convert hpow.const_mul y using 1
      · ext n
        simp; grind
      · simp
    have htt' := EReal.tendsto_coe.mpr htt
    have hyliminf := htt'.liminf_eq.symm
    rw [hyliminf]
    unfold L''
    exact Filter.liminf_le_liminf hle'
  set L' := limsup (fun n ↦ ((c (n+1) / c n:ℝ):EReal)) .atTop
  by_cases hL : L' = ⊤; · rw [hL]; exact le_top
  have hL'pos : 0 ≤ L' := by
    apply le_limsup_of_frequently_le'
    rw [frequently_atTop]
    intro N; use max N m, by omega
    have hpos1 := hpos (max N m) (by omega)
    have hpos2 := hpos ((max N m)+1) (by omega)
    positivity
  have why : L' ≠ ⊥ := by
     intro hbot
     rw [hbot] at hL'pos
     simp at hL'pos
  set L := L'.toReal
  have hL' : L' = L := (coe_toReal hL why).symm
  have hLpos : 0 ≤ L := by rw [hL'] at hL'pos; norm_cast at hL'pos
  apply le_of_forall_gt_imp_ge_of_dense
  intro y hy
  by_cases hy' : y = ⊤; · simp [hy']; exact le_top
  have : y = y.toReal := by symm; apply coe_toReal hy'; contrapose! hy; simp [hy]
  rw [this, hL', EReal.coe_lt_coe_iff] at hy
  set ε := y.toReal - L
  have hε : 0 < ε := by grind
  replace this : y = (L+ε:ℝ) := by convert this; simp [ε]
  rw [this]
  have hε' : L' < (L+ε:ℝ) := by rw [hL', EReal.coe_lt_coe_iff]; linarith
  have := eventually_lt_of_limsup_lt hε' (by isBoundedDefault)
  rw [eventually_atTop] at this; choose N' hN using this
  set N := max N' (max m 1)
  have (n:ℤ) (hn: n ≥ N) : c (n+1) / c n ≤ (L + ε) := by
    have : n ≥ N' := by omega
    have npos : 0 < n := by omega
    specialize hN n this; norm_cast at hN; order
  set A := c N * (L+ε)^(-N)
  have hA : 0 < A := by specialize hpos N (by omega); positivity
  have why2 (n:ℤ) (hn: n ≥ N) : c n ≤ A * (L+ε)^n := by
    induction' n, hn using Int.le_induction with k hn' ih
    · specialize hN N (by grind); norm_cast at hN
      unfold A
      rw [mul_assoc]; simp
      rw [inv_mul_cancel₀ (by positivity)]; simp
    · specialize hN k (by omega)
      norm_cast at hN
      field_simp at hN
      rw [div_lt_iff₀ (hpos _ (by omega))] at hN
      conv_rhs => rw [zpow_add₀ (by grind), zpow_one]
      nlinarith
  have why2_root (n:ℤ) (hn: n ≥ N) : (((c n)^(1/(n:ℝ)):ℝ):EReal) ≤ (A^(1/(n:ℝ)) * (L+ε):ℝ) := by
    rw [EReal.coe_le_coe_iff]
    have hn' : n > 0 := by omega
    calc
      _ ≤ (A * (L+ε)^n)^(1/(n:ℝ)) := by
        apply_rules [rpow_le_rpow, le_of_lt (hpos n _)]; omega; positivity
      _ = A^(1/(n:ℝ)) * ((L+ε)^n)^(1/(n:ℝ)) := mul_rpow (by positivity) (by positivity)
      _ = _ := by
        congr
        rw [←rpow_intCast, ←rpow_mul (by positivity)]
        convert rpow_one _
        field_simp
  calc
    _ ≤ atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)) * (L+ε):ℝ):EReal)) := by
      apply limsup_le_limsup <;> try isBoundedDefault
      unfold EventuallyLE; rw [eventually_atTop]
      use N
    _ ≤ (atTop.limsup (fun n:ℤ ↦ ((A^(1/(n:ℝ)):ℝ):EReal))) * (atTop.limsup (fun n:ℤ ↦ ((L+ε:ℝ):EReal))) := by
      convert EReal.limsup_mul_le _ _ _ _ with n
      . rfl
      . apply Frequently.of_forall; intros; positivity
      . apply Eventually.of_forall; simp; positivity
      . simp [-coe_add]
      simp [-coe_add]; grind
    _ = (L+ε:ℝ) := by
      simp; convert one_mul _
      apply Tendsto.limsup_eq
      convert Tendsto.comp (f := fun n:ℤ ↦ (A ^ (n:ℝ)⁻¹)) (g := fun x:ℝ ↦ (x:EReal)) (y := nhds 1) _ _
      . apply continuous_coe_real_ereal.tendsto'; norm_num
      convert Tendsto.comp (f := fun n:ℤ ↦ (n:ℝ)⁻¹) (g := fun x:ℝ ↦ A^x) (y := nhds 0) _ _
      . apply (continuous_const_rpow (by positivity)).tendsto'; simp
      exact tendsto_inv_atTop_zero.comp tendsto_intCast_atTop_atTop

/-- Corollary 7.5.3 (Ratio test, convergence). -/
theorem Series.ratio_test_pos {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.limsup (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) < 1) : s.absConverges := by
    apply Series.root_test_pos (lt_of_le_of_lt _ h)
    convert (ratio_ineq s.m _).2.2
    convert hnon using 1 with n
    simp

/-- Corollary 7.5.3 (Ratio test, divergence). -/
theorem Series.ratio_test_neg {s : Series} (hnon: ∀ n ≥ s.m, s.seq n ≠ 0)
  (h : atTop.liminf (fun n ↦ ((|s.seq (n+1)| / |s.seq n|:ℝ):EReal)) > 1) : s.diverges := by
    apply Series.root_test_neg (lt_of_lt_of_le h _)
    convert (ratio_ineq s.m _).1.trans (ratio_ineq s.m _).2.1 with n; rfl
    all_goals convert hnon using 1 with n; simp

/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive: ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.diverges := by
  set a : ℕ → ℝ := fun _ => 1
  use (a:Series)
  refine ⟨?_, ?_, ?_⟩
  · simp
    intro n hn
    constructor <;> grind
  · simp
    rw [Metric.tendsto_atTop]
    intro ε hε
    use 0; intro n hn
    rw [Real.dist_eq, if_pos hn, if_pos (by grind)]
    unfold a; simp
    exact hε
  · have hsum (n:ℕ) : (a:Series).partial n = (n + 1:ℝ) := by
      induction' n with k ih
      · unfold Series.partial; simp
        unfold a; simp
      · unfold Series.partial at ih ⊢; simp at ih ⊢
        rw [sum_of_nonempty (by grind), ih]
        rw [if_pos (by grind)]
    have hdiv : Filter.Tendsto (a:Series).partial Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      use max 0 ⌈b⌉
      intro n hn
      lift n to ℕ using by omega
      specialize hsum n
      rw [hsum]
      have hleceil := Int.le_ceil b
      have h' : ⌈b⌉ ≤ n := by grind
      rify at h'
      grind
    intro hconv
    unfold Series.converges at hconv
    choose L hL using hconv
    unfold Series.convergesTo at hL
    exact not_tendsto_nhds_of_tendsto_atTop hdiv L hL


/-- Corollary 7.5.3 (Ratio test) / Exercise 7.5.3 -/
theorem Series.ratio_test_inconclusive' : ∃ s:Series, (∀ n ≥ s.m, s.seq n ≠ 0) ∧
  atTop.Tendsto (fun n ↦ |s.seq (n+1)| / |s.seq n|) (nhds 1) ∧ s.absConverges := by
  use (fun n:ℕ ↦ 1/(n+1:ℝ)^2 : Series)
  refine ⟨?_, ?_, ?_⟩
  · simp
    intro n hn
    constructor <;> grind
  · simp
    rw [Metric.tendsto_atTop]
    intro ε hε
    choose N hN using exists_nat_gt (3/ε)
    use max (N+1) 3
    intro n hn
    lift n to ℕ using by omega
    simp at hn
    rw [Real.dist_eq, if_pos (by grind), if_pos (by grind)]
    simp
    rw [show (n:ℝ) + 1 + 1 = n + 2 by linarith]
    field_simp
    rw [sq_sub_sq]
    simp; norm_num
    rw [show (-2 + -(n:ℝ) + (-1 + -(n:ℝ))) = -(2*(n:ℝ)+3) by linarith]
    rw [abs_div, abs_neg, abs_of_pos (by grind), abs_of_nonneg (by apply sq_nonneg)]
    rw [div_lt_iff₀ (by positivity)]
    field_simp at hN
    calc _ ≤ (2 * n:ℝ) + (n:ℝ)       := by gcongr; norm_cast; exact hn.2
         _ = 3 * n                   := by ring_nf
         _ < (ε * n) * n             := by
                        gcongr
                        · norm_cast; linarith
                        · suffices (N:ℝ) < (n:ℝ) by nlinarith
                          norm_cast
                          exact hn.1
         _ = ε * n^2                 := by nlinarith
         _ < ε * (n^2 + 4 * n + 4)   := by
                        suffices 0 < (n:ℝ) by nlinarith
                        norm_cast
                        linarith
         _ = ε * (n+2)^2             := by grind
  · unfold Series.absConverges
    convert Series.zeta_2_converges with n
    simp_all

/-- Proposition 7.5.4 -/
theorem Series.root_self_converges : atTop.Tendsto (fun (n:ℕ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) := by
  set c : ℤ → ℝ := fun n => n
  set m : ℤ := 1
  have hpos : ∀ n ≥ m, c n > 0 := by intro n hn; unfold c; rify at hn; grind
  obtain ⟨hl, he, hs⟩ := Series.ratio_ineq (c:=c) (m:=m) hpos
  have htt : Filter.Tendsto (fun n:ℤ => c (n+1) / c n) Filter.atTop (nhds 1) := by
    have hdivtt : Filter.Tendsto (fun n:ℤ => 1/(n:ℝ)) Filter.atTop (nhds 0) := by
        rw [Metric.tendsto_atTop]
        simp_rw [Real.dist_eq, sub_zero]
        intro ε hε
        choose N hN using exists_nat_gt (1/ε)
        have hN0 : 0 < N := by
          rify
          have : 0 < 1 / ε := by positivity
          grind
        field_simp at hN
        use N
        intro n hn
        have hn0 : 0 < n := by omega
        rw [abs_of_pos (by positivity)]
        field_simp
        rify at hN hn ⊢
        nlinarith
    have hconstadd := (hdivtt.const_add 1); simp at hconstadd
    refine Filter.Tendsto.congr' ?_ hconstadd
    filter_upwards [eventually_ge_atTop 1]
    intro a ha
    unfold c
    grind
  have htt' := EReal.tendsto_coe.mpr htt
  have hinf := htt'.liminf_eq
  have hsup := htt'.limsup_eq
  rw [hinf] at hl; unfold c at hl; push_cast at hl
  rw [hsup] at hs; unfold c at hs; push_cast at hs
  unfold c at he
  -- we weaken it to Z first.
  suffices atTop.Tendsto (fun (n:ℤ) ↦ (n:ℝ)^(1 / (n:ℝ))) (nhds 1) by
    rw [Metric.tendsto_atTop] at this ⊢
    intro ε hε
    choose N hN using this ε hε
    use max 0 N.toNat
    intro n hn
    specialize hN n (by grind)
    rw [Real.dist_eq] at hN ⊢
    norm_cast
  have := tendsto_of_le_liminf_of_limsup_le hl hs
  exact EReal.tendsto_coe.mp this

/-- Exercise 7.5.2 -/
theorem Series.poly_mul_geom_converges {x:ℝ} (hx: |x|<1) (q:ℝ) : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).converges
  ∧ atTop.Tendsto (fun n:ℕ ↦ (n:ℝ)^q * x^n) (nhds 0) := by
  have habsconv : (fun n:ℕ ↦ (n:ℝ)^q * x^n : Series).absConverges := by
    apply Series.root_test_pos
    simp
    have hrootconv := Series.root_self_converges
    have hpow := hrootconv.rpow_const (p:=q) (by left; grind); simp at hpow
    have hpowmul := hpow.mul_const |x|; simp at hpowmul
    have hpowmul' : Tendsto (fun (n:ℤ) ↦ (n ^ (n:ℝ)⁻¹) ^ q * |x|) atTop (nhds |x|) := by
      rw [Metric.tendsto_atTop] at hpowmul ⊢
      intro ε hε
      choose N hN using hpowmul ε hε
      use N; intro n hn
      lift n to ℕ using by omega
      specialize hN n (by omega)
      rw [Real.dist_eq] at hN ⊢
      exact_mod_cast hN
    have hpowmuler := EReal.tendsto_coe.mpr hpowmul'
    have hsup := hpowmuler.limsup_eq
    suffices limsup (fun (n : ℤ) ↦ (((((n : ℝ) ^ (n : ℝ)⁻¹) ^ q * |x| : ℝ) : EReal))) atTop =
               limsup (fun (n : ℤ) ↦ (((|(if 0 ≤ n then (n.toNat : ℝ) ^ q * x ^ n.toNat else 0)| ^ (n : ℝ)⁻¹ : ℝ) : EReal))) atTop by
                  rw [← this]
                  rw [hsup]
                  exact_mod_cast hx
    apply limsup_congr
    · filter_upwards [eventually_ge_atTop 1]
      intro a ha
      lift a to ℕ using by omega
      simp; norm_cast
      nth_rewrite 2 [abs_of_nonneg (by positivity)]
      conv_lhs =>
        rw [← rpow_mul (by positivity), mul_comm _ q]
      conv_rhs =>
        rw [mul_rpow (by positivity) (by positivity)]
        rw [← rpow_mul (by positivity), ← Real.rpow_natCast,  ← rpow_mul (by positivity)]
        rw [mul_inv_cancel₀ (by norm_cast; linarith), rpow_one]
  have hconv := Series.converges_of_absConverges habsconv
  constructor
  · exact hconv
  · suffices atTop.Tendsto (fun n:ℤ ↦ (n:ℝ)^q * x^n) (nhds 0) by
      rw [Metric.tendsto_atTop] at this ⊢
      intro ε hε
      choose N hN using this ε hε
      use N.toNat; intro n hn
      specialize hN n (by grind)
      rw [Real.dist_eq] at hN ⊢
      simp at hN ⊢
      exact_mod_cast hN
    have hdecay := Series.decay_of_converges hconv
    refine (Filter.tendsto_congr' ?_).mpr hdecay
    filter_upwards [eventually_ge_atTop 1]
    intro a ha
    lift a to ℕ using (by omega)
    simp

end Chapter7
