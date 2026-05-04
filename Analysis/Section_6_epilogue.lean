import Mathlib.Tactic
import Analysis.Section_6_7

/-!
# Analysis I, Chapter 6 epilogue: Connections with Mathlib limits

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences {name}`Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/

open Filter

/-- Identification with the Cauchy sequence support in Mathlib/Algebra/Order/CauSeq/Basic -/
theorem Chapter6.Sequence.isCauchy_iff_isCauSeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ IsCauSeq _root_.abs a := by
  simp_rw [IsCauchy.coe, Real.dist_eq, IsCauSeq]
  constructor <;> intro h ε hε <;> have ⟨ N, h ⟩ := h _ (half_pos hε) <;> use N
  . intro n hn; linarith [h n hn N (by rfl)]
  intro n hn m hm
  calc
    _ ≤ |a n - a N| + |a m - a N| := by grind [abs_sub_comm, abs_sub_le]
    _ ≤ ε/2 + ε/2 := by grind
    _ = _ := by linarith

/-- Identification with the Cauchy sequence support in Mathlib/Topology/UniformSpace/Cauchy -/
theorem Chapter6.Sequence.Cauchy_iff_CauchySeq (a: ℕ → ℝ) :
    (a:Sequence).IsCauchy ↔ CauchySeq a := by
  rw [isCauchy_iff_isCauSeq]
  convert isCauSeq_iff_cauchySeq

/-- Identification with {name}`Filter.Tendsto` -/
theorem Chapter6.Sequence.tendsto_iff_Tendsto (a: ℕ → ℝ) (L:ℝ) :
    (a:Sequence).TendsTo L ↔ atTop.Tendsto a (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N.toNat; intro n hn
    specialize hN n (Int.toNat_le.mp hn); simp at hN
    rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h ε hε; use N; intro n hn
  have hpos : n ≥ 0 := by grind
  rw [ge_iff_le, ←Int.le_toNat hpos] at hn
  simp [hpos, ←Real.dist_eq, le_of_lt (hN n.toNat hn)]

theorem Chapter6.Sequence.tendsto_iff_Tendsto' (a: Sequence) (L:ℝ) : a.TendsTo L ↔ atTop.Tendsto a.seq (nhds L) := by
  rw [Metric.tendsto_atTop, tendsTo_iff]
  constructor <;> intro h ε hε
  . have ⟨ N, hN ⟩ := h _ (half_pos hε); use N; peel 2 hN; rw [Real.dist_eq]; linarith
  have ⟨ N, hN ⟩ := h _ hε; use N; peel 2 hN; rw [←Real.dist_eq]; linarith

theorem Chapter6.Sequence.converges_iff_Tendsto (a: ℕ → ℝ) :
    (a:Sequence).Convergent ↔ ∃ L, atTop.Tendsto a (nhds L) := by simp_rw [←tendsto_iff_Tendsto]

theorem Chapter6.Sequence.converges_iff_Tendsto' (a: Sequence) :
    a.Convergent ↔ ∃ L, atTop.Tendsto a.seq (nhds L) := by simp_rw [←tendsto_iff_Tendsto']

/-- A technicality: {name}`CauSeq.IsComplete` {lean}`ℝ` was established for {name}`_root_.abs` but not for {name}`norm`. -/
instance inst_real_complete : CauSeq.IsComplete ℝ norm := by convert Real.instIsCompleteAbs

/-- Identification with {name}`CauSeq.lim` -/
theorem Chapter6.Sequence.lim_eq_CauSeq_lim (a:ℕ → ℝ) (ha: (a:Sequence).IsCauchy) :
    Chapter6.lim (a:Sequence) = CauSeq.lim  ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩ := by
  have h1 := CauSeq.tendsto_limit ⟨ a, (isCauchy_iff_isCauSeq a).mp ha⟩
  have h2 := lim_def ((a:Sequence).Cauchy_iff_convergent.mp ha)
  rw [←tendsto_iff_Tendsto] at h1
  by_contra! h; apply (a:Sequence).tendsTo_unique at h; tauto

/-- Identification with {name}`limUnder` -/
theorem Chapter6.Sequence.lim_eq_limUnder (a:ℕ → ℝ) (ha: (a:Sequence).Convergent) :
    Chapter6.lim (a:Sequence) = limUnder Filter.atTop a := by
    have htt := Sequence.lim_def ha
    set L := Chapter6.lim (a:Sequence) with Ldef
    have hattop := (Chapter6.Sequence.tendsto_iff_Tendsto a L).mp htt
    exact (Tendsto.limUnder_eq hattop).symm

/-- Identification with {name}`Bornology.IsBounded` -/
theorem Chapter6.Sequence.isBounded_iff_isBounded_range (a:ℕ → ℝ):
    (a:Sequence).IsBounded ↔ Bornology.IsBounded (Set.range a) := by
  simp [isBounded_def, boundedBy_def, Metric.isBounded_iff]
  constructor
  . intro ⟨ M, hM, h ⟩; use 2*M; intro n m
    calc
      _ = |a n - a m| := Real.dist_eq _ _
      _ ≤ |a n| + |a m| := abs_sub _ _
      _ ≤ M + M := by gcongr; convert h n; convert h m
      _ = _ := by ring
  intro ⟨ C, h ⟩
  have : C ≥ 0 := by specialize h 0 0; simpa using h
  refine ⟨ C + |a 0|, by positivity, ?_ ⟩
  intro n; by_cases hn: n ≥ 0 <;> simp [hn]
  . calc
      _ ≤ |a n.toNat - a 0| + |a 0| := by convert abs_add_le _ _; abel; infer_instance
      _ ≤ C + |a 0| := by gcongr; rw [←Real.dist_eq]; convert h n.toNat 0
  positivity

theorem Chapter6.Sequence.sup_eq_sSup (a:ℕ → ℝ):
    (a:Sequence).sup = sSup (Set.range (fun n ↦ (a n:EReal))) := by
  unfold Sequence.sup
  rcongr x
  constructor
  · rintro ⟨n, hnam, rfl⟩
    use n.toNat; simp_all
  · rintro ⟨n, rfl⟩
    use n; simp_all


theorem Chapter6.Sequence.inf_eq_sInf (a:ℕ → ℝ):
    (a:Sequence).inf = sInf (Set.range (fun n ↦ (a n:EReal))) := by
  unfold Sequence.inf
  rcongr x
  constructor
  · rintro ⟨n, hnam, rfl⟩
    use n.toNat; simp_all
  · rintro ⟨n, rfl⟩
    use n; simp_all

theorem Chapter6.Sequence.bddAbove_iff (a:ℕ → ℝ):
    (a:Sequence).BddAbove ↔ _root_.BddAbove (Set.range a) := by
  unfold Sequence.BddAbove Sequence.BddAboveBy
  unfold _root_.BddAbove
  constructor
  · rintro ⟨M, hM⟩
    use M
    apply mem_upperBounds.mpr
    intro x hx
    obtain ⟨n, hn⟩ := hx
    specialize hM n (by grind); simp at hM
    rwa [hn] at hM
  · rintro ⟨B, hB⟩
    use B
    intro n hnam; simp at hnam; lift n to ℕ using (by omega)
    simp
    exact hB (Set.mem_range_self n)

theorem Chapter6.Sequence.bddBelow_iff (a:ℕ → ℝ):
    (a:Sequence).BddBelow ↔ _root_.BddBelow (Set.range a) := by
  unfold Sequence.BddBelow Sequence.BddBelowBy
  unfold _root_.BddBelow
  constructor
  · rintro ⟨M, hM⟩
    use M
    apply mem_lowerBounds.mpr
    intro x hx
    obtain ⟨n, hn⟩ := hx
    specialize hM n (by grind); simp at hM
    rwa [hn] at hM
  · rintro ⟨B, hB⟩
    use B
    intro n hnam; simp at hnam; lift n to ℕ using (by omega)
    simp
    exact hB (Set.mem_range_self n)

lemma Chapter6.Sequence.IsMonotone_nat (a:ℕ → ℝ) (n N:ℕ) (hmono: (a:Sequence).IsMonotone) :
  a n ≤ a (n + N) := by
  induction' N with k ih
  · simp
  · rw [← Nat.add_assoc]
    calc a n ≤ a (n + k)      := by exact ih
           _ ≤ a (n + k + 1)  := by exact hmono (n+k) (by grind)

theorem Chapter6.Sequence.Monotone_iff (a:ℕ → ℝ): (a:Sequence).IsMonotone ↔ Monotone a := by
  constructor
  · intro hismono n₁ n₂ hn
    obtain ⟨d, hd⟩ := Nat.le.dest hn
    rw [← hd]
    apply Chapter6.Sequence.IsMonotone_nat
    exact hismono
  · intro hmono n hn; simp at hn; lift n to ℕ using (by omega)
    simp; rw [if_pos (by grind)]
    have : n ≤ n+1 := by linarith
    exact hmono this

lemma Chapter6.Sequence.IsAntitone_nat (a:ℕ → ℝ) (n N:ℕ) (hanti: (a:Sequence).IsAntitone) :
  a n ≥ a (n + N) := by
  induction' N with k ih
  · simp
  · rw [← Nat.add_assoc]
    calc a n ≥ a (n + k)      := by exact ih
           _ ≥ a (n + k + 1)  := by exact hanti (n+k) (by grind)

theorem Chapter6.Sequence.Antitone_iff (a:ℕ → ℝ): (a:Sequence).IsAntitone ↔ Antitone a := by
  constructor
  · intro hisanti n₁ n₂ hn
    obtain ⟨d, hd⟩ := Nat.le.dest hn
    rw [← hd]
    apply Chapter6.Sequence.IsAntitone_nat
    exact hisanti
  · intro hanti n hn; simp at hn; lift n to ℕ using (by omega)
    simp; rw [if_pos (by grind)]
    have : n ≤ n+1 := by linarith
    exact hanti this

/-- Identification with {name}`MapClusterPt` -/
theorem Chapter6.Sequence.limit_point_iff (a:ℕ → ℝ) (L:ℝ) :
    (a:Sequence).LimitPoint L ↔ MapClusterPt L .atTop a := by
  simp_rw [limit_point_def, mapClusterPt_iff_frequently, frequently_atTop, Metric.mem_nhds_iff]
  constructor
  . intro h s ⟨ ε, hε, hεs ⟩ N
    have ⟨ n, hn1, hn2 ⟩ := h _ (half_pos hε) N (by positivity)
    have hn : n ≥ 0 := by grind
    refine ⟨ n.toNat, by rwa [ge_iff_le, Int.le_toNat hn], ?_ ⟩
    apply hεs; simp [Real.dist_eq, hn] at *; linarith
  intro h ε hε N _
  have ⟨ n, hn1, hn2 ⟩ := h (Metric.ball L ε) ⟨ _, hε, by aesop ⟩ N.toNat
  have hn : n ≥ 0 := by positivity
  refine ⟨ n, by rwa [ge_iff_le, ←Int.toNat_le], ?_ ⟩
  simp [Real.dist_eq, hn] at *; linarith

/-- Identification with {name}`Filter.limsup` -/
theorem Chapter6.Sequence.limsup_eq (a:ℕ → ℝ) :
    (a:Sequence).limsup = atTop.limsup (fun n ↦ (a n:EReal)) := by
  simp_rw [Filter.limsup_eq, eventually_atTop]
  apply le_antisymm
  · apply le_sInf
    intro x hx
    obtain ⟨N, hN⟩ := hx
    unfold Sequence.limsup
    apply sInf_le_of_le
    · use N
      constructor
      · simp
      · rfl
    · apply sSup_le
      intro y hy
      rcases hy with ⟨n, hn, rfl⟩
      simp at hn
      lift n to ℕ using by omega
      simp at hn
      simp_all
  · apply sInf_le_sInf
    intro x hx
    rcases hx with ⟨N, hNam, rfl⟩
    simp at hNam
    lift N to ℕ using (by omega)
    use N
    intro n hn
    unfold Sequence.upperseq Sequence.sup
    apply le_sSup
    use n; simp_all

/-- Identification with {name}`Filter.liminf` -/
theorem Chapter6.Sequence.liminf_eq (a:ℕ → ℝ) :
    (a:Sequence).liminf = atTop.liminf (fun n ↦ (a n:EReal)) := by
  simp_rw [Filter.liminf_eq, eventually_atTop]
  apply le_antisymm
  · apply sSup_le_sSup
    intro x hx
    rcases hx with ⟨N, hNam, rfl⟩
    simp at hNam
    lift N to ℕ using (by omega)
    use N
    intro n hn
    unfold Sequence.lowerseq Sequence.inf
    apply sInf_le
    use n; simp_all
  · apply sSup_le
    intro x hx
    obtain ⟨N, hN⟩ := hx
    unfold Sequence.liminf
    apply le_sSup_of_le
    · use N
      constructor
      · simp
      · rfl
    · apply le_sInf
      intro y hy
      rcases hy with ⟨n, hn, rfl⟩
      simp at hn
      lift n to ℕ using by omega
      simp at hn
      simp_all

/-- Identification of {name}`Chapter6.Real.rpow` and Mathlib exponentiation -/
theorem Chapter6.Real.rpow_eq_rpow {x:ℝ} (hx: x > 0) (α:ℝ) : rpow x α = x^α := by
  choose q hq using Real.eq_lim_of_rat α
  have hq' := hq
  rw [Sequence.tendsto_iff_Tendsto] at hq'
  have hrat := Real.ratPow_tendsto_rpow hx hq
  have halt : (fun n ↦ x ^ (q n:ℝ):Sequence).TendsTo (x ^ α) := by
    rw [Sequence.tendsto_iff_Tendsto]
    have hcont : ContinuousAt (fun y ↦ x ^ y) α := Real.continuousAt_const_rpow (a:=x) (by linarith)
    exact hcont.tendsto.comp hq'
  have h1 := (Sequence.lim_eq.mp hrat).2
  have h2 := (Sequence.lim_eq.mp halt).2
  rwa [h1] at h2
