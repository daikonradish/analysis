import Mathlib.Tactic
import Analysis.Section_6_4

/-!
# Analysis I, Section 6.5: Some standard limits

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Some standard limits, including limits of sequences of the form 1/n^α, x^n, and x^(1/n).

-/

namespace Chapter6

theorem Sequence.lim_of_const (c:ℝ) :  ((fun (_:ℕ) ↦ c):Sequence).TendsTo c := by
  rw [Sequence.tendsTo_iff]
  intro ε hε
  use ((fun (_:ℕ) ↦ c):Sequence).m
  intro n hn
  simp at hn
  lift n to ℕ using (by omega)
  simp; grind

instance Sequence.inst_pow: Pow Sequence ℕ where
  pow a k := {
    m := a.m
    seq n := if n ≥ a.m then a n ^ k else 0
    vanish := by grind
  }

@[simp]
lemma Sequence.pow_eval {a:Sequence} {k: ℕ} {n: ℤ} (hn : n ≥ a.m): (a ^ k) n = a n ^ k := by
  rw [HPow.hPow, instHPow, Pow.pow, inst_pow]
  grind

@[simp]
lemma Sequence.pow_one (a:Sequence) : a^1 = a := by
  ext n; rfl; simp only [HPow.hPow, Pow.pow]; split_ifs with h; simp; simp [a.vanish n (by grind)]

lemma Sequence.pow_succ (a:Sequence) (k:ℕ): a^(k+1) = a^k * a := by
  ext x
  . symm; exact Int.min_self a.m
  . simp only [mul_eval]
    by_cases h: x ≥ a.m
    · simp [pow_eval h]
      rfl
    · rw [a.vanish x (by grind), mul_zero]
      exact vanish _ _ (by simp at h; exact h)

/-- Corollary 6.5.1 -/
theorem Sequence.lim_of_power_decay {k:ℕ} :
    ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence).TendsTo 0 := by
  -- This proof is written to follow the structure of the original text.
  set a := ((fun (n:ℕ) ↦ 1/((n:ℝ)+1)^(1/(k+1:ℝ))):Sequence)
  have ha : a.BddBelow := by use 0; intro n _; simp [a]; positivity
  have ha' : a.IsAntitone := by
    intro n hn; observe hn' : 0 ≤ n+1; simp [a,hn,hn']
    rw [inv_le_inv₀, Real.rpow_le_rpow_iff] <;> try positivity
    simp
  apply convergent_of_antitone ha at ha'
  have hpow (n:ℕ): (a^(n+1)).Convergent ∧ lim (a^(n+1)) = (lim a)^(n+1) := by
    induction' n with n ih
    . simp [ha', -dite_pow]
    rw [pow_succ]; convert lim_mul ih.1 ha' using 1; rw [ih.2]; grind
  have hlim : (lim a)^(k+1) = 0 := by
    rw [←(hpow k).2]; convert lim_harmonic.2; ext; rfl
    simp only [HPow.hPow, Pow.pow, a]; split_ifs with h
    · simp
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
      convert Real.rpow_one _; field_simp; push_cast; ring
    · simp
  simp [lim_eq, ha', eq_zero_of_pow_eq_zero hlim]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
lemma Sequence.lim_of_lag {a : ℕ → ℝ} (N:ℕ) (h: (a:Sequence).Convergent) :
  lim a = lim (fun n => a (n+N)) := by
  have hlim := Sequence.lim_def h
  set L := lim a
  have hlagconv : (fun n => a (n+N):Sequence).TendsTo L := by
    rw [Sequence.tendsTo_iff] at hlim ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hlim ε hε
    use max (a:Sequence).m (N + N₁)
    intro n hn
    specialize hN₁ (n + N) (by grind)
    simp at hN₁ ⊢
    rw [if_pos (by grind)] at hN₁ ⊢
    grind
  have := Sequence.lim_eq.mp hlagconv
  exact this.2.symm

lemma Sequence.lim_of_lag' {a : ℕ → ℝ} (N:ℕ) (h: (fun n => a (n+N):Sequence).Convergent) :
  lim (fun n => a (n+N)) = lim a := by
  have hlim := Sequence.lim_def h
  set L := lim (fun n => a (n+N))
  have hconv' : (a:Sequence).TendsTo L := by
    rw [Sequence.tendsTo_iff] at hlim ⊢
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := hlim ε hε
    use max (fun n => a (n+N):Sequence).m ((max N₁ 0) + N)
    intro n hn
    specialize hN₁ (n-N) (by grind)
    simp at hN₁ ⊢
    rw [if_pos (by grind)] at hN₁ ⊢
    rwa [Nat.sub_add_cancel (by grind)] at hN₁
  have := Sequence.lim_eq.mp hconv'
  exact this.2.symm

lemma Sequence.lim_pow {x:ℝ} (hx : x > 0 ∧ x < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  set α : ℕ → ℝ := fun n => x^n
  obtain ⟨hx0, hx1⟩ := hx
  have hbelow : (α:Sequence).BddBelow := by
    use 0
    intro n hn; simp at hn
    unfold α; simp_all
    positivity
  have hantitone : (α:Sequence).IsAntitone := by
    intro n hn; simp at hn
    unfold α; simp_all
    by_cases hn : (n+1) ≥ 0
    · simp_all
      rw [← zpow_natCast x n.toNat, ← zpow_natCast x (n+1).toNat]
      rw [Int.toNat_of_nonneg (by grind), Int.toNat_of_nonneg (by grind)]
      rw [zpow_add₀, zpow_one]
      have : x^n > 0 := by positivity
      nlinarith
      grind
    · by_cases h' : (n+1) = 0
      · simp_all
      · push_neg at h' hn
        simp_all
        rw [if_neg (by grind)]
        positivity
  have hαconv := Sequence.convergent_of_antitone hbelow hantitone
  have hαlim := Sequence.lim_def hαconv
  set β : ℕ → ℝ := fun n => x ^ (n+1)
  observe hlag : β = fun n => α (n+1)
  have hβlim := Sequence.lim_of_lag 1 hαconv
  rw [← hlag] at hβlim
  have hsmul : (β:Sequence) = x • (α:Sequence) := by
    refine Sequence.ext rfl ?_
    unfold α β
    ext n
    by_cases hn : n ≥ 0
    · simp_all
      rw [pow_add];
      ring_nf
    · simp_all
      rw [if_neg (by grind), if_neg (by grind)]
  have hlimmul := Sequence.tendsTo_smul x hαlim
  rw [← hsmul] at hlimmul; observe hβconv : (β:Sequence).Convergent
  have hβlim' := Sequence.lim_def hβconv
  have hlimeq : lim β = x * lim α := by
    by_contra!
    exact Sequence.tendsTo_unique β this ⟨hβlim', hlimmul⟩
  rw [← hβlim] at hlimeq
  set L := lim α
  have hL0 : L = 0 := by
    observe : L - x * L = 0
    have hltimes : L * (1 - x) = 0 := by linarith only [this]
    have hminus : (1 - x) ≠ 0 := by linarith
    grind
  rwa [hL0] at hαlim

lemma Sequence.lim_pow_of_abs {x:ℝ} (hx : x > 0 ∧ x < 1) : (fun (n:ℕ) ↦ |x|^n:Sequence).TendsTo 0 := by
  have hseq : (fun (n:ℕ) ↦ x^n:Sequence) = (fun (n:ℕ) ↦ |x|^n:Sequence) := by
    refine Sequence.ext rfl ?_
    ext n
    by_cases hn : n ≥ 0
    · simp_all
      rw [abs_of_pos (by grind)]
    · simp_all
      rw [if_neg (by grind), if_neg (by grind)]
  have hpow := Sequence.lim_pow hx
  rwa [← hseq]

lemma Sequence.lim_abs_of_pow {x:ℝ} (hx : x > 0 ∧ x < 1) : (fun (n:ℕ) ↦ |x^n|:Sequence).TendsTo 0 := by
  have hseq : (fun (n:ℕ) ↦ x^n:Sequence) = (fun (n:ℕ) ↦ |x^n|:Sequence) := by
    refine Sequence.ext rfl ?_
    ext n
    by_cases hn : n ≥ 0
    · simp_all
      rw [abs_of_pos (by grind)]
    · simp_all
      rw [if_neg (by grind), if_neg (by grind)]
  have hpow := Sequence.lim_pow hx
  rwa [← hseq]




theorem Sequence.lim_of_geometric {x:ℝ} (hx: |x| < 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 0 := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hx0 : |x| > 0 := by grind
    have hx1 : |x| < 1 := by grind
    have habstt := Sequence.lim_pow ⟨hx0, hx1⟩
    have ⟨habsconv, habslim⟩ := Sequence.lim_eq.mp habstt
    have ⟨hnegconv, hneglim⟩ := Sequence.lim_smul (-1:ℝ) habsconv
    rw [habslim, mul_zero] at hneglim
    have hnegtt := Sequence.lim_eq.mpr ⟨hnegconv, hneglim⟩
    have hnegabs : (fun (n:ℕ) => -|x|^n:Sequence) = (-1:ℝ) • (fun (n:ℕ) => |x|^n:Sequence) := by
      refine Sequence.ext rfl ?_
      ext n
      by_cases hn : n ≥ 0 <;> simp_all
    rw [← hnegabs] at hnegtt
    refine Sequence.lim_of_between (by grind) ?_ hnegtt habstt
    intro n hn; simp at hn
    lift n to ℕ using (by omega)
    constructor
    · simp_all
      have := neg_abs_le (x ^ n)
      rw [abs_pow] at this
      exact this
    · simp_all
      rw [← abs_pow]
      exact le_abs_self _
  · rw [hzero, Sequence.tendsTo_iff]
    intro ε hε
    use 1; intro n hn; simp_all; rw [if_pos (by grind)]
    rw [zero_pow (by grind)]
    simp; linarith
  · have hx0 : x > 0 := by grind
    have hx1 : x < 1 := by grind
    exact Sequence.lim_pow ⟨hx0, hx1⟩


/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric' {x:ℝ} (hx: x = 1) : ((fun (n:ℕ) ↦ x^n):Sequence).TendsTo 1 := by
  have hlim1 := Sequence.lim_of_const (1:ℝ)
  have heq : ((fun (n:ℕ) ↦ x^n):Sequence) = ((fun (n:ℕ) ↦ (1:ℝ)):Sequence) := by
    refine Sequence.ext rfl ?_
    ext n
    simp_all
  rwa [heq]

/-- Lemma 6.5.2 / Exercise 6.5.2 -/
theorem Sequence.lim_of_geometric'' {x:ℝ} (hx: x = -1 ∨ |x| > 1) :
    ((fun (n:ℕ) ↦ x^n):Sequence).Divergent := by
  rw [Sequence.divergent_def]
  intro hconv
  rcases hx with hneg1 | hmod1
  · have hcauchy := (Sequence.Cauchy_iff_convergent _).mpr hconv
    rw [Sequence.IsCauchy.coe] at hcauchy
    obtain ⟨N, hN⟩ := hcauchy (1/2) (by grind)
    specialize hN (2*N) (by grind) (2*N+1) (by grind)
    rw [Real.dist_eq] at hN
    rw [hneg1] at hN
    have heven : Even (2*N) := by grind
    have hodd : Odd (2*N+1) := by grind
    simp_all
    norm_num at hN
  · have hbdd := Sequence.bounded_of_convergent hconv
    obtain ⟨B, hBpos, hB⟩ := hbdd
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B hmod1
    specialize hB N; simp at hB
    grind

/-- Lemma 6.5.3 / Exercise 6.5.3 -/
theorem Sequence.lim_of_roots {x:ℝ} (hx: x > 0) :
    ((fun (n:ℕ) ↦ x^(1/(n+1:ℝ))):Sequence).TendsTo 1 := by
  have taohint {ε M : ℝ} (hε : ε > 0) (hM : M > 0): ∃ N : ℕ, ∀ n ≥ N, M^(1/(n+1:ℝ)) ≤ 1 + ε := by
    by_cases hM' : M ≤ 1
    · use 0
      intro n hn
      suffices M ^ (1 / (n+1:ℝ)) ≤ 1 by linarith
      apply Real.rpow_le_one (by linarith) hM'
      positivity
    · let α : ℕ → ℝ := fun n => (1+ε)^n
      have habs1 : |(1+ε)| > 1 := by grind
      have hnotconv := Sequence.lim_of_geometric'' (Or.inr habs1)
      have hαabove : ¬ (α:Sequence).BddAbove := by
        intro h'
        have hmono : (α:Sequence).IsMonotone := by
          intro n hn; simp at hn
          lift n to ℕ using (by omega)
          simp
          rw [if_pos (by grind)]
          unfold α
          gcongr <;> grind
        exact hnotconv (Sequence.convergent_of_monotone h' hmono)
      have hunbound : ∀ M : ℝ, ∃ n : ℕ, α n > M := by
        intro M
        by_contra! h'
        contrapose hαabove
        use M
        intro n hn; simp at hn
        lift n to ℕ using (by omega)
        simp
        specialize h' n
        exact h'
      obtain ⟨N, hN⟩ := hunbound M
      unfold α at hN
      have hpowlt :  (1+ε)^N < (1+ε)^(N+1) := by
        apply pow_lt_pow_right₀ <;> grind
      have hpowM : M ≤ (1+ε)^(N+1) := by grind
      use N
      intro n hn
      have : M ^ (1 / (n+1:ℝ)) ≤ M ^ (1 / (N+1:ℝ)) := by
          gcongr; linarith
      suffices M ^ (1 / (N+1:ℝ)) ≤ 1 + ε by linarith
      apply (Real.rpow_le_rpow_iff (y:=1+ε) (z:=N+1) (by positivity) (by grind) (by grind)).mp
      rw [← Real.rpow_mul (by grind), one_div_mul_cancel (by grind), Real.rpow_one]
      exact_mod_cast hpowM
  rw [Sequence.tendsTo_iff]
  intro ε hε
  by_cases hx1 : x ≤ 1
  · obtain ⟨N, hN⟩ := taohint (M:=1/x) hε (by positivity)
    use max 0 N; intro n hn; simp at hn
    lift n to ℕ using (by omega); norm_cast at hn
    specialize hN n hn
    simp at hN ⊢
    rw [Real.inv_rpow (by grind), inv_le_comm₀ (by positivity) (by grind)] at hN
    have : x ^ (n+1:ℝ)⁻¹ ≤ 1 := by
      apply Real.rpow_le_one
      · grind
      · grind
      · positivity
    rw [abs_of_nonpos (by grind)]
    suffices x^(n+1:ℝ)⁻¹ ≥ 1 - ε by linarith
    suffices 1 - ε ≤ (1+ε)⁻¹ by linarith
    field_simp
    rw [mul_comm, ← sq_sub_sq]
    simp; positivity
  · push_neg at hx1
    obtain ⟨N, hN⟩ := taohint (M:=x) hε (by linarith)
    use max 0 N; intro n hn; simp at hn
    lift n to ℕ using (by omega); norm_cast at hn
    simp at hN ⊢
    specialize hN n (by grind)
    have : 1 ≤ x ^ (1 / (n+1:ℝ)) := by
      apply Real.one_le_rpow
      · linarith
      · positivity
    rw [abs_of_nonneg (by grind)]
    grind



lemma Sequence.pow_zero' {a:ℕ → ℝ} {k:ℕ} (hk: k ≥ 1) (h : (a:Sequence).TendsTo 0) :
  ((fun (n:ℕ) => (a n)^k):Sequence).TendsTo 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp
    have : (a:Sequence) = ((fun n => a n):Sequence) := by
      refine Sequence.ext rfl ?_
      ext n
      simp_all
    rwa [← this]
  | succ k' hk ih =>
    have : ((fun n => a n ^ (k'+1)):Sequence) = (a:Sequence) * ((fun n => a n ^ k'):Sequence) := by
      refine Sequence.ext rfl ?_
      ext n
      by_cases hN0 : n ≥ 0
      · simp_all
        rw [pow_add]
        grind
      · simp_all; rw [if_neg (by grind), if_neg (by grind)]
    rw [this]
    have ha := Sequence.lim_eq.mp h
    have hpow := Sequence.lim_eq.mp ih
    have ⟨hlimconv, hlimmul⟩ := Sequence.lim_mul ha.1 hpow.1
    rw [ha.2, hpow.2] at hlimmul; rw [mul_zero] at hlimmul
    exact Sequence.lim_eq.mpr ⟨hlimconv, hlimmul⟩


/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_decay {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ)):Sequence).TendsTo 0 := by
  have hnum : q.num > 0 := by positivity
  have hfun : (fun (n:ℕ) ↦ 1/((n+1:ℝ)^(q:ℝ))) = (fun (n:ℕ) ↦ (((1/((n+1:ℝ)))^(1/(q.den:ℝ)))^(q.num:ℝ))) := by
    ext n
    rw [← Real.rpow_mul (by positivity)]
    have : (q : ℝ) = (1 / q.den) * q.num := by
      rw [Rat.cast_def]
      ring
    rw [← this, Real.div_rpow (by grind) (by grind), Real.one_rpow]
  rw [hfun]
  have hlimdecay := Sequence.lim_of_power_decay (k:=q.den-1); norm_cast at hlimdecay
  rw [Nat.sub_add_cancel (n:=q.den) (m:=1) (by exact q.den_pos)] at hlimdecay
  norm_cast
  rw [← Int.toNat_of_nonneg (a:=q.num) (by grind)]
  simp_rw [zpow_natCast]
  have : q.num.toNat > 0 := by grind
  have : q.num.toNat ≥ 1 := by grind
  have := Sequence.pow_zero' (k:=q.num.toNat) this hlimdecay
  convert this using 1
  refine Sequence.ext rfl ?_
  ext n
  by_cases hn0 : n ≥ 0
  · simp; rw [if_pos (by grind), if_pos (by grind)]
    field_simp
    rw [← mul_pow, ← Real.mul_rpow (by positivity) (by grind)]
    field_simp
    simp
  · simp
    rw [if_neg (by grind), if_neg (by grind)]

/-- Exercise 6.5.1 -/
theorem Sequence.lim_of_rat_power_growth {q:ℚ} (hq: q > 0) :
    (fun (n:ℕ) ↦ ((n+1:ℝ)^(q:ℝ)):Sequence).Divergent := by
  rw [Sequence.divergent_def]
  intro hconv
  have hbdd := Sequence.bounded_of_convergent hconv
  obtain ⟨B, hBpo, hB⟩ := hbdd
  unfold Sequence.BoundedBy at hB
  specialize hB (Nat.ceil (B ^ (1/q:ℝ)))
  simp_all
  rw [abs_of_nonneg (by positivity)] at hB
  rw [← Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity)] at hB
  linarith [Nat.le_ceil (B ^ (q : ℝ)⁻¹)]



end Chapter6
