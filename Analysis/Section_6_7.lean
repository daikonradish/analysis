import Mathlib.Tactic
import Analysis.Section_5_epilogue
import Analysis.Section_6_6

/-!
# Analysis I, Section 6.7: Real exponentiation, part II

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Real exponentiation.

Because the Chapter 5 reals have been deprecated in favor of the Mathlib reals, and Mathlib real
exponentiation is defined without first going through rational exponentiation, we will adopt a
somewhat awkward compromise, in that we will initially accept the Mathlib exponentiation operation
(with all its API) when the exponent is a rational, and use this to define a notion of real
exponentiation which in the epilogue to this chapter we will show is identical to the Mathlib operation.
-/

namespace Chapter6

open Sequence Real

/-- Lemma 6.7.1 (Continuity of exponentiation) -/
lemma ratPow_continuous {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).Convergent := by
  -- This proof is rearranged slightly from the original text.
  choose M hM hbound using bounded_of_convergent ⟨ α, hq ⟩
  obtain h | rfl | h := lt_trichotomy x 1
  . have h' : x ≤ 1 := by linarith
    rw [← Sequence.Cauchy_iff_convergent]
    intro ε hε
    choose K hK hclose using Sequence.lim_of_roots hx (ε * x^M) (by positivity)
    choose N hN hq using Sequence.IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
    simp [Real.CloseSeq, Real.dist_eq] at hclose hK hN
    lift N to ℕ using hN
    lift K to ℕ using hK
    specialize hclose K (by simp) (by simp); simp at hclose
    use N, by simp
    intro n hn m hm; simp at hn hm
    specialize hq n (by simp [hn]) m (by simp [hm])
    simp [Real.Close, hn, hm, Real.dist_eq] at hq ⊢
    have : 0 ≤ (N:ℤ) := by simp
    lift n to ℕ using by linarith
    lift m to ℕ using by linarith
    simp at hn hm hq ⊢
    obtain hqq | hqq := le_or_gt (q m) (q n)
    · replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hx h]; norm_cast
      rw [abs_of_nonpos (by linarith)]
      calc
          _ = x^(q m:ℝ) * (1 - x^(q n - q m:ℝ)) := by ring_nf; rw [←Real.rpow_add (by grind)]; ring_nf
          _ ≤ x^(-M) * (1 - x^((K:ℝ) + 1)⁻¹)    := by
            apply mul_le_mul
            · apply Real.rpow_le_rpow_of_exponent_ge hx h'
              specialize hbound m; simp at hbound; grind
            · have := Real.rpow_le_rpow_of_exponent_ge hx h' (abs_le.mp hq).2
              linarith
            · suffices x ^ (q n - q m:ℝ) ≤ 1 by linarith
              apply Real.rpow_le_one
              · grind
              · grind
              · norm_cast; grind
            · positivity
          _ ≤ x^(-M) * (ε * x^M) := by gcongr; grind
          _ = ε                  := by rw [mul_comm, mul_assoc, ← Real.rpow_add]; simp; grind
    replace :  x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hx h]; norm_cast; grind
    rw [abs_of_nonneg (by linarith)]
    calc
        _ = x^(q n:ℝ) * (1 - x^(q m - q n:ℝ)) := by ring_nf; rw [←Real.rpow_add]; ring_nf; exact hx
        _ ≤ x^(-M) * (1 - x^((K:ℝ) + 1)⁻¹)    := by
          apply mul_le_mul
          · apply Real.rpow_le_rpow_of_exponent_ge hx h'
            specialize hbound n; simp at hbound; grind
          · have := (abs_le'.mp hq).2; rw [neg_sub] at this
            have := Real.rpow_le_rpow_of_exponent_ge hx h' this
            grind
          · suffices x ^ (q m - q n:ℝ) ≤ 1 by linarith
            apply Real.rpow_le_one
            · grind
            · grind
            · norm_cast; grind
          · positivity
        _ ≤ x^(-M) * (ε * x^M) := by gcongr; grind
        _ = ε                  := by rw [mul_comm, mul_assoc, ← Real.rpow_add]; simp; grind
  . simp; exact ⟨ 1, lim_of_const 1 ⟩
  have h': 1 ≤ x := by linarith
  rw [←Sequence.Cauchy_iff_convergent]
  intro ε hε
  choose K hK hclose using Sequence.lim_of_roots hx (ε*x^(-M)) (by positivity)
  choose N hN hq using Sequence.IsCauchy.convergent ⟨ α, hq ⟩ (1/(K+1:ℝ)) (by positivity)
  simp [Real.CloseSeq, Real.dist_eq] at hclose hK hN
  lift N to ℕ using hN
  lift K to ℕ using hK
  specialize hclose K (by simp) (by simp); simp at hclose
  use N, by simp
  intro n hn m hm; simp at hn hm
  specialize hq n (by simp [hn]) m (by simp [hm])
  simp [Real.Close, hn, hm, Real.dist_eq] at hq ⊢
  have : 0 ≤ (N:ℤ) := by simp
  lift n to ℕ using by linarith
  lift m to ℕ using by linarith
  simp at hn hm hq ⊢
  obtain hqq | hqq := le_or_gt (q m) (q n)
  . replace : x^(q m:ℝ) ≤ x^(q n:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast
    rw [abs_of_nonneg (by linarith)]
    calc
      _ = x^(q m:ℝ) * (x^(q n - q m:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add (by linarith)]; ring_nf
      _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
        gcongr <;> try exact h'
        . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
        . specialize hbound m; simp_all [abs_le']
        grind [abs_le']
      _ ≤ x^M * (ε * x^(-M)) := by gcongr; grind [abs_le']
      _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; linarith
  replace : x^(q n:ℝ) ≤ x^(q m:ℝ) := by rw [Real.rpow_le_rpow_left_iff h]; norm_cast; linarith
  rw [abs_of_nonpos (by linarith)]
  calc
    _ = x^(q n:ℝ) * (x^(q m - q n:ℝ) - 1) := by ring_nf; rw [←Real.rpow_add]; ring_nf; positivity
    _ ≤ x^M * (x^(1/(K+1:ℝ)) - 1) := by
      gcongr <;> try exact h'
      . rw [sub_nonneg]; apply Real.one_le_rpow h'; norm_cast; linarith
      . specialize hbound n; simp_all [abs_le']
      grind [abs_le']
    _ ≤ x^M * (ε * x^(-M)) := by gcongr; simp_all [abs_le']
    _ = ε := by rw [mul_comm, mul_assoc, ←Real.rpow_add]; simp; positivity


lemma ratPow_lim_uniq {x α:ℝ} (hx: x > 0) {q q': ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α)
 (hq': ((fun n ↦ (q' n:ℝ)):Sequence).TendsTo α) :
 lim ((fun n ↦ x^(q n:ℝ)):Sequence) = lim ((fun n ↦ x^(q' n:ℝ)):Sequence) := by
 -- This proof is written to follow the structure of the original text.
  set r := q - q'
  suffices : (fun n ↦ x^(r n:ℝ):Sequence).TendsTo 1
  . rw [←mul_one (lim ((fun n ↦ x^(q' n:ℝ)):Sequence))]
    rw [lim_eq] at this
    convert (lim_mul (b := (fun n ↦ x^(r n:ℝ):Sequence)) (ratPow_continuous hx hq') this.1).2
    . rw [mul_coe]
      rcongr _ n
      rw [←Real.rpow_add (by linarith)]
      simp [r]
    exact this.2.symm
  intro ε hε
  have h1 := lim_of_roots hx
  have h2 := tendsTo_inv h1 (by norm_num)
  choose K1 hK1 h3 using h1 ε hε
  choose K2 hK2 h4 using h2 ε hε
  simp [Inv.inv] at hK1 hK2
  lift K1 to ℕ using hK1; lift K2 to ℕ using hK2
  simp [inv_coe] at h4
  set K := max K1 K2
  have hr := tendsTo_sub hq hq'
  rw [sub_coe] at hr
  choose N hN hr using hr (1 / (K + 1:ℝ)) (by positivity)
  refine ⟨ N, by simp_all, ?_ ⟩
  intro n hn; simp at hn
  specialize h3 K (by simp [K]); specialize h4 K (by simp [K])
  simp [hn, Real.dist_eq, abs_le', K, -Nat.cast_max] at h3 h4 ⊢
  specialize hr n (by simp [hn])
  simp [Real.Close, hn, abs_le'] at hr
  obtain h | rfl | h := lt_trichotomy x 1
  . -- have hle1 : x ≤ 1 := by linarith
    have h5 : x ^ (K + 1:ℝ)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      · exact hx
      · linarith
      · simp_all [r]
    have h6 : x ^ (r n.toNat:ℝ) ≤ (x^(K + 1:ℝ)⁻¹)⁻¹ := by
      rw [← Real.rpow_neg (by grind)]
      apply Real.rpow_le_rpow_of_exponent_ge
      · exact hx
      · linarith
      · simp_all [r]
        linarith
    split_ands <;> grind
  . simp; linarith
  have h5 : x ^ (r n.toNat:ℝ) ≤ x^(K + 1:ℝ)⁻¹ := by gcongr; linarith; simp_all [r]
  have h6 : (x^(K + 1:ℝ)⁻¹)⁻¹ ≤ x ^ (r n.toNat:ℝ) := by
    rw [←Real.rpow_neg (by linarith)]
    gcongr; linarith
    simp [r]; linarith
  split_ands <;> linarith

theorem Real.eq_lim_of_rat (α:ℝ) : ∃ q: ℕ → ℚ, ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α := by
  choose q hcauchy hLIM using (Chapter5.Real.equivR.symm α).eq_lim; use q
  apply lim_eq_LIM at hcauchy
  simp only [←hLIM, Equiv.apply_symm_apply] at hcauchy
  convert hcauchy; aesop

/-- Definition 6.7.2 (Exponentiation to a real exponent) -/
noncomputable abbrev Real.rpow (x:ℝ) (α:ℝ) :ℝ := lim ((fun n ↦ x^((eq_lim_of_rat α).choose n:ℝ)):Sequence)

lemma Real.rpow_eq_lim_ratPow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 rpow x α = lim ((fun n ↦ x^(q n:ℝ)):Sequence) :=
   ratPow_lim_uniq hx (eq_lim_of_rat α).choose_spec hq

lemma Real.ratPow_tendsto_rpow {x α:ℝ} (hx: x > 0) {q: ℕ → ℚ}
 (hq: ((fun n ↦ (q n:ℝ)):Sequence).TendsTo α) :
 ((fun n ↦ x^(q n:ℝ)):Sequence).TendsTo (rpow x α) := by
  rw [lim_eq]
  exact ⟨ ratPow_continuous hx hq, (rpow_eq_lim_ratPow hx hq).symm ⟩

lemma Real.rpow_of_rat_eq_ratPow {x:ℝ} (hx: x > 0) {q: ℚ} :
  rpow x (q:ℝ) = x^(q:ℝ) := by
  convert rpow_eq_lim_ratPow hx (α := q) (lim_of_const _)
  exact (lim_eq.mp (lim_of_const _)).2.symm

/-- Proposition 6.7.3(a) / Exercise 6.7.1 -/
theorem Real.ratPow_nonneg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q ≥ 0 := by
  choose q' hq' using eq_lim_of_rat q
  rw [rpow_eq_lim_ratPow hx hq']
  by_contra! h'
  have htt := ratPow_tendsto_rpow hx hq'
  rw [rpow_eq_lim_ratPow hx hq'] at htt
  rw [Sequence.tendsTo_iff] at htt
  have h'' := neg_pos.mpr h'
  specialize htt _ h''
  obtain ⟨N, hN⟩ := htt
  specialize hN (max 0 N) (by grind)
  simp at hN
  rw [abs_le] at hN
  obtain ⟨hub, hlb⟩ := hN
  simp at hlb
  have hlb' : x ^ (q' (max 0 N).toNat : ℝ) > 0 := by positivity
  linarith only [hlb, hlb']

theorem Real.ratPow_pos {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x q > 0 := by
  have hnneg := Real.ratPow_nonneg hx q
  suffices rpow x q ≠ 0 by exact lt_of_le_of_ne hnneg this.symm
  clear hnneg
  by_contra! h'
  choose q' hq' using eq_lim_of_rat q
  have hpowbdd : ∃ M > 0, ((fun n ↦ x^(q' n:ℝ)):Sequence).BddBelowBy M := by
    choose B hB hbound using bounded_of_convergent ⟨ q, hq' ⟩
    rcases lt_trichotomy x 1 with hlt1 | heq1 | hgt1
    · use x ^ B; constructor
      · positivity
      · intro n hn; simp at hn; lift n to ℕ using (by omega)
        simp_all
        specialize hbound n; simp at hbound
        grind
    · use 0.5; constructor
      · norm_num
      · intro n hn; simp at hn; lift n to ℕ using (by omega)
        simp_all; norm_num
    · use x^(-B); constructor
      · positivity
      · intro n hn; simp at hn; lift n to ℕ using (by omega)
        simp_all
        specialize hbound n; simp at hbound
        grind
  rw [rpow_eq_lim_ratPow hx hq'] at h'
  have htt := ratPow_tendsto_rpow hx hq'
  rw [rpow_eq_lim_ratPow hx hq'] at htt
  rw [h'] at htt
  rw [Sequence.tendsTo_iff] at htt
  obtain ⟨M, hMpos, hMbd⟩ := hpowbdd
  specialize htt (M/2) (by positivity)
  obtain ⟨N, hN⟩ := htt
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 N)
  specialize hN n (by grind)
  specialize hMbd n (by grind)
  simp_all
  grind

/-- Proposition 6.7.3(b) -/
theorem Real.ratPow_add {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow x (q+r) = rpow x q * rpow x r := by
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hq'r' := tendsTo_add hq' hr'
  rw [add_coe] at hq'r'
  convert_to ((fun n ↦ ((q' n + r' n:ℚ):ℝ)):Sequence).TendsTo (q + r) at hq'r'
  . aesop
  have h1 := ratPow_continuous hx hq'
  have h2 := ratPow_continuous hx hr'
  rw [rpow_eq_lim_ratPow hx hq', rpow_eq_lim_ratPow hx hr', rpow_eq_lim_ratPow hx hq'r', ←(lim_mul h1 h2).2, mul_coe]
  rcongr n; rw [←Real.rpow_add]; simp; linarith

/-- Proposition 6.7.3(b) / Exercise 6.7.1 -/
lemma Sequence.eventually_positive {a : ℕ → ℝ} {L:ℝ} (h: (a:Sequence).TendsTo L) (hL : L > 0) :
  ∃ N : ℕ, ∀ n ≥ N, a n > 0 := by
  rw [Sequence.tendsTo_iff] at h
  obtain ⟨N, hN⟩ := h (L/2) (by positivity)
  use N.toNat
  intro n hn
  specialize hN n (by omega)
  simp at hN; grind

lemma Real.natPow_unit_tendsTo' {a : ℕ → ℝ} (h : (a : Sequence).TendsTo 1) (k : ℕ) :
  ((fun n ↦ a n ^ k): Sequence).TendsTo 1 := by
  induction' k with k ih
  · rw [Sequence.tendsTo_iff]; intro ε hε; use 0
    intro n hn; lift n to ℕ using (by omega)
    simp_all
    linarith
  · have : ((fun n => a n ^ (k+1)):Sequence) = (a:Sequence) * ((fun n ↦ a n ^ k): Sequence) := by
      refine Sequence.ext rfl ?_
      ext n
      simp_all
      split_ifs <;> grind
    rw [this]
    have := Sequence.tendsTo_mul h ih; simp at this; exact this

lemma Real.natPow_unit_tendsTo {a : ℕ → ℝ} (h : (a : Sequence).TendsTo 1) (k : ℕ) :
  ((fun n ↦ a n ^ (k:ℝ)): Sequence).TendsTo 1 := by
  have hunit := Real.natPow_unit_tendsTo' h k
  have hseqeq : ((fun n ↦ a n ^ k): Sequence) =  ((fun n ↦ a n ^ (k:ℝ)): Sequence) := by
    refine Sequence.ext rfl ?_
    ext n
    simp_all
  rwa [hseqeq] at hunit

lemma Sequence.from_N_iff {L:ℝ} {a : ℕ → ℝ} (N : ℕ) :
  (a : Sequence).TendsTo L ↔ ((a:Sequence).from N).TendsTo L := by
  constructor
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    choose M hM using h ε hε
    use max M N; intro n hn; lift n to ℕ using (by omega); simp at hn
    specialize hM n (by omega)
    simp_all
  · intro h
    rw [Sequence.tendsTo_iff] at h ⊢
    intro ε hε
    choose M hM using h ε hε
    use max M N; intro n hn; lift n to ℕ using (by omega); simp at hn
    specialize hM n (by omega)
    simp_all

lemma Real.ratPow_unit_tendsTo_pos {a : ℕ → ℝ} (q:ℚ) (hq : q > 0) (h : (a : Sequence).TendsTo 1) :
  ((fun (n:ℕ) ↦ a n ^ (q:ℝ)): Sequence).TendsTo 1 := by
  obtain ⟨k, hk⟩ := exists_nat_ge q
  obtain ⟨N, hN⟩ := Sequence.eventually_positive (h : (a : Sequence).TendsTo 1) (by linarith)
  suffices alternatively : (((fun n ↦ a n ^ (q:ℝ)): Sequence).from N).TendsTo 1 by
    exact (Sequence.from_N_iff N).mpr alternatively
  -- let ones : Sequence := ((fun (n:ℕ) ↦ (1:ℝ)):Sequence)
  let down : ℕ → ℝ := fun n => if a n ≥ 1 then 1 else a n ^ (k:ℝ)
  let up   : ℕ → ℝ := fun n => if a n ≥ 1 then a n ^ (k:ℝ) else 1
  apply Sequence.lim_of_between (a:=((down:Sequence).from N)) (c:=((up:Sequence).from N)) (by grind)
  · intro n hn; simp at hn;
    lift n to ℕ using (by omega)
    simp_all
    constructor
    · unfold down
      split_ifs with hif
      · apply Real.one_le_rpow
        · exact hif
        · norm_cast; linarith
      · push_neg at hif
        refine (Real.rpow_le_rpow_left_iff_of_base_lt_one ?_ ?_).mpr ?_
        · exact hN n hn
        · exact hif
        · exact_mod_cast hk
    · unfold up
      split_ifs with hif
      · gcongr
        · exact hif
        · exact_mod_cast hk
      · push_neg at hif
        apply Real.rpow_le_one
        · linarith only [hN n hn]
        · linarith only [hif]
        · norm_cast; linarith only [hq]
  · suffices alternatively : (down:Sequence).TendsTo 1 by exact (Sequence.from_N_iff N).mp alternatively
    have hunit := Real.natPow_unit_tendsTo h k
    rw [Sequence.tendsTo_iff] at hunit ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hunit ε hε
    use M; intro m hm
    specialize hM m (by grind)
    unfold down
    grind
  · suffices alternatively : (up:Sequence).TendsTo 1 by exact (Sequence.from_N_iff N).mp alternatively
    have hunit := Real.natPow_unit_tendsTo h k
    rw [Sequence.tendsTo_iff] at hunit ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hunit ε hε
    use M; intro m hm
    specialize hM m (by grind)
    unfold up
    grind

lemma Real.ratPow_unit_tendsTo {a : ℕ → ℝ} (q:ℚ) (h : (a : Sequence).TendsTo 1) :
  ((fun (n:ℕ) ↦ a n ^ (q:ℝ)): Sequence).TendsTo 1 := by
  rcases lt_trichotomy q 0 with hlt0 | heq0 | hgt0
  · obtain ⟨N, hN⟩ := Sequence.eventually_positive h (by linarith)
    suffices alternatively :  (((fun (n:ℕ) ↦ a n ^ (q:ℝ)): Sequence).from N).TendsTo 1
      by exact (Sequence.from_N_iff N).mpr alternatively
    set s := -q with hs
    have hspos : s > 0 := by grind
    have hstt :=(Sequence.from_N_iff N).mp (Real.ratPow_unit_tendsTo_pos s hspos h)
    have hsinv := Sequence.tendsTo_inv hstt (by linarith); simp at hsinv
    have hseqeq :  (((fun (n:ℕ) ↦ a n ^ (s:ℝ)): Sequence).from N)⁻¹ = (((fun (n:ℕ) ↦ a n ^ (q:ℝ)): Sequence).from N) := by
      refine Sequence.ext rfl ?_
      ext n
      simp_all
      split_ifs with hif
      · lift n to ℕ using (by omega); simp at hif
        have hanpos := hN n hif
        simp_all
        rw [Real.rpow_neg]
        field_simp
        grind
      · grind
      · grind
    rwa [hseqeq] at hsinv
  · rw [heq0, Sequence.tendsTo_iff]
    intro ε hε
    use 0
    intro n hn; lift n to ℕ using (by omega)
    simp_all; grind
  · exact Real.ratPow_unit_tendsTo_pos q hgt0 h



theorem Real.ratPow_ratPow {x:ℝ} (hx: x > 0) (q r:ℝ) : rpow (rpow x q) r = rpow x (q*r) := by
  set L := rpow x q with hLdef
  have hL : L > 0 := by unfold L; exact Real.ratPow_pos hx q
  choose q' hq' using eq_lim_of_rat q
  choose r' hr' using eq_lim_of_rat r
  have hmul := Sequence.tendsTo_mul hq' hr'; rw [Sequence.mul_coe] at hmul
  convert_to (fun n => (((q' n * r' n):ℚ):ℝ):Sequence).TendsTo (q * r) at hmul
  · aesop
  -- handle RHS
  have hpowmul : ((fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ)) : Sequence).TendsTo (rpow x (q*r)) := by
    have :  ((fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ)) : Sequence) = (fun n => x^(((q' n * r' n):ℚ):ℝ):Sequence) := by
      refine Sequence.ext rfl ?_
      ext n
      simp_all
      split_ifs
      · lift n to ℕ using (by omega)
        rw [← Real.rpow_mul (by linarith)]
      · rfl
    rw [this]
    exact Real.ratPow_tendsto_rpow hx hmul
  have hL' := Real.ratPow_tendsto_rpow hL hr'
  have hupper : ((fun n => x ^ (q' n:ℝ) / L):Sequence).TendsTo 1 := by
    have := Sequence.tendsTo_mul (ratPow_tendsto_rpow hx hq') (lim_of_const (1/L))
    rw [Sequence.mul_coe, ← hLdef, mul_one_div_cancel (by grind)] at this
    simp_rw [mul_one_div] at this
    exact this
  suffices alternatively :
    ((fun n ↦ (x ^ (q' n : ℝ) / L) ^ (r' n : ℝ)) : Sequence).TendsTo 1 by
    have httmul := Sequence.tendsTo_mul alternatively hL'
    rw [Sequence.mul_coe, one_mul] at httmul
    have hfuneq :
      (fun n : ℕ ↦ (x ^ (q' n : ℝ) / L) ^ (r' n : ℝ) * L ^ (r' n : ℝ)) =
      fun n ↦ (x ^ (q' n : ℝ)) ^ (r' n : ℝ) := by
      ext n
      rw [Real.div_rpow (y:=L) (by positivity) (by linarith only [hL])]; field_simp
    rw [hfuneq] at httmul
    unfold L at httmul ⊢
    have h1 := (Sequence.lim_eq.mp hpowmul).2
    have h2 := (Sequence.lim_eq.mp httmul).2
    rwa [h2] at h1
  obtain ⟨B, hBn, hB⟩ := Sequence.bounded_of_convergent ⟨r, hr'⟩
  set B' := ⌈B⌉₊ + 1
  have : B < B' := by
    unfold B'
    have := Nat.le_ceil B
    rify; linarith
  have hB' : ((fun n => (r' n:ℝ)):Sequence).BoundedBy B' := by
    intro n
    specialize hB n
    simp_all
    split_ifs
    · rw [if_pos (by grind)] at hB
      grind
    · simp
  have hpowunit := Real.natPow_unit_tendsTo hupper B'
  rw [Sequence.tendsTo_iff] at hpowunit ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hpowunit (min (ε/2) (1/2)) (by positivity)
  use max 0 N
  intro n hn
  simp at hn
  lift n to ℕ using (by omega)
  simp at hn
  specialize hN n (by grind)
  simp at hN
  set U := x ^ (q' n : ℝ) / L with hUdef
  have hUpos : U > 0 := by positivity
  obtain ⟨hN0, hN1⟩ := hN
  rw [abs_le] at hN1
  have hubhalf : U ^ B' ≥ 1/2 := by linarith [hN1.1]
  have hrnleb : |(r' n:ℝ)| ≤ B' := by
    specialize hB' n
    simp at hB'
    exact hB'
  rw [abs_le] at hrnleb
  rw [abs_le]
  by_cases hU1 : U < 1
  · have hlb : U ^ (B':ℝ) ≤ U ^ (r' n:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      · exact hUpos
      · linarith only [hU1]
      · exact hrnleb.2
    have hub : U ^ (r' n:ℝ) ≤ U ^(-(B':ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      · exact hUpos
      · linarith only [hU1]
      · exact hrnleb.1
    have hinvleε : (U ^ B')⁻¹ - 1 ≤ ε := by
      conv => lhs; field_simp
      have : U ^ B' > 0 := by positivity
      rw [div_le_iff₀ this]
      calc 1 - U ^ B' ≤ ε / 2      := by rw [abs_sub_comm] at hN0; exact le_of_abs_le hN0
                    _ ≤ ε * U ^ B' := by nlinarith
    rw [abs_le] at hN0
    simp
    constructor
    · have :=
        calc
          1 = (1 - (ε / 2)) + ε / 2    := by ring_nf
          _ ≤ (U ^ B') + ε / 2         := by gcongr; linarith [hN0.1]
          _ ≤ (U ^ (r' n :ℝ)) +  ε / 2 := by gcongr; exact_mod_cast hlb
          _ ≤ (U ^ (r' n :ℝ)) +  ε     := by gcongr; linarith
      unfold U at this
      exact this
    · have :=
        calc
          U ^ (r' n :ℝ) ≤ U ^ (-(B':ℝ))        := by exact hub
                      _ = (U ^ B')⁻¹           := by norm_cast
                      _ = ((U ^ B')⁻¹ - 1) + 1 := by ring
                      _ ≤ ε + 1                := by gcongr
      unfold U at this
      exact this
  · push_neg at hU1
    have hlb : U ^ (-(B':ℝ)) ≤ U ^ (r' n:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hU1
      · exact hrnleb.1
    have hub : U ^ (r' n:ℝ) ≤  U ^ (B':ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact hU1
      · exact hrnleb.2
    have hge1 : 1 ≤ U ^ B' := by exact one_le_pow₀ hU1
    have hinvleε : 1 - (U ^ B')⁻¹ ≤ ε / 2 := by
      calc 1 - (U ^ B')⁻¹ = (U ^ B' - 1) / U ^ B' := by field_simp
                        _ ≤ U ^ B' - 1            := by apply div_le_self; linarith only [hge1]; exact hge1
                        _ ≤ ε / 2                 := by exact le_of_abs_le hN0
    simp
    constructor
    · have :=
        calc 1 = (1 - ε) + ε       := by ring_nf
             _ ≤ (1 - ε/2) + ε     := by linarith
             _ ≤ (U ^ B')⁻¹ + ε    := by gcongr; linarith only [hinvleε]
             _ = (U ^ (-B':ℝ)) + ε := by congr 1; norm_cast
      unfold U at this
      grind
    · rw [← hUdef]
      calc  _ ≤ U ^ B'           := by exact_mod_cast hub
            _ = (U ^ B' - 1) + 1 := by ring_nf
            _ ≤ ε / 2 + 1        := by linarith only [le_of_abs_le hN0]
            _ ≤ ε + 1            := by linarith


/-- Proposition 6.7.3(c) / Exercise 6.7.1 -/
lemma Real.ratPow_zero {x:ℝ} (hx: x > 0) : rpow x 0 = 1 := by
  let q' : ℕ → ℚ := fun _ => 0
  have hq' : (fun n => (q' n:ℝ):Sequence).TendsTo 0 := by
    rw [Sequence.tendsTo_iff]; intro ε hε; use 0; intro n hn
    simp_all
    unfold q'
    simp_all; linarith
  have this := Real.ratPow_tendsto_rpow hx hq'
  have that : (fun n ↦ x ^ (q' n:ℝ):Sequence).TendsTo 1 := by
    have heq : (fun n ↦ x ^ (q' n:ℝ)) = (fun _ ↦ 1) := by
      ext n
      unfold q'
      simp
    rw [heq]
    exact lim_of_const 1
  have h1 := (Sequence.lim_eq.mp this).2
  have h2 := (Sequence.lim_eq.mp that).2
  rwa [h1] at h2


theorem Real.ratPow_neg {x:ℝ} (hx: x > 0) (q:ℝ) : rpow x (-q) = 1 / rpow x q := by
  have := Real.ratPow_add hx (q) (-q); ring_nf at this; rw [mul_comm] at this
  rw [Real.ratPow_zero hx] at this
  apply eq_one_div_of_mul_eq_one_left
  exact this.symm

/-- Proposition 6.7.3(d) / Exercise 6.7.1 -/
lemma Sequence.eventually_gt {q' : ℕ → ℝ} {p q : ℝ}
  (hq' : (q':Sequence).TendsTo q) (hpq : q > p) :
  ∃ N:ℕ , ∀ n ≥ N, q' n > p := by
  let ε := q - p
  have hpos : ε > 0 := by linarith
  rw [Sequence.tendsTo_iff] at hq'
  obtain ⟨N, hN⟩ := hq' (ε/2) (by positivity)
  use N.toNat + 1
  intro n hn
  specialize hN n (by omega); simp at hN
  grind


lemma Real.rpow_gt_one {x : ℝ} (hx : x > 1) {q : ℝ} (hq : q > 0) :
  rpow x q > 1 := by
  -- 1. Find a rational p between 0 and q
  obtain ⟨p, hp0, hpq⟩ := exists_rat_btwn hq
  have hrat : rpow x p > 1 := by
    rw [Real.rpow_of_rat_eq_ratPow (by linarith)]
    apply Real.one_lt_rpow
    · exact hx
    · exact hp0
  have hge : rpow x q ≥ rpow x p := by
    rw [Real.rpow_of_rat_eq_ratPow (x:=x) (q:=p) (by linarith)]
    obtain ⟨q', hq'⟩ := Real.eq_lim_of_rat q
    have htt := Real.ratPow_tendsto_rpow (x:=x) (by linarith) hq'
    have htt' := htt
    rw [Sequence.tendsTo_iff] at htt
    by_contra! h'
    specialize htt (x^ (p:ℝ) - rpow x q) (by linarith [h'])
    obtain ⟨N₁, hN₁⟩ := htt
    obtain ⟨N₂, hN₂⟩ := Sequence.eventually_gt hq' hpq
    let N' := max N₁.toNat N₂
    specialize hN₁ N' (by grind); simp at hN₁
    specialize hN₂ N' (by omega)
    rw [abs_le] at hN₁; simp at hN₁
    have := (Real.rpow_lt_rpow_left_iff hx).mpr hN₂
    grind
  linarith

lemma  Real.ratPow_mul' {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  obtain ⟨q', hq'⟩ := Real.eq_lim_of_rat q
  have hxy := Real.ratPow_tendsto_rpow (x:=x*y) (by nlinarith) hq'
  have hx  := Real.ratPow_tendsto_rpow (x:=x)   (by  linarith) hq'
  have hy  := Real.ratPow_tendsto_rpow (x:=y)   (by  linarith) hq'
  have hmul := Sequence.tendsTo_mul hx hy
  rw [Sequence.mul_coe] at hmul
  convert_to  (fun n ↦ (x * y) ^ (q' n:ℝ):Sequence).TendsTo (rpow x q * rpow y q) at hmul
  · refine Sequence.ext rfl ?_
    ext n
    simp
    split_ifs
    · lift n to ℕ using (by omega)
      simp
      rw [← Real.mul_rpow (by linarith) (by linarith)]
    · rfl
  have h1 := (Sequence.lim_eq.mp hxy).2
  have h2 := (Sequence.lim_eq.mp hmul).2
  rwa [h1] at h2


lemma Real.ratPow_mono' {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) (hxy: x > y) : rpow x q > rpow y q := by
  let u := x / y
  have hgt1 : u > 1 := by unfold u; field_simp; exact hxy
  have hequ : u * y = x := by unfold u; field_simp
  suffices alternatively : rpow u q > 1 by
    have hmul := Real.ratPow_mul' (x:=u) (y:=y) (by linarith) hy q
    conv at hmul =>
      lhs
      rw [hequ]
    rw [hmul]
    apply lt_mul_of_one_lt_left
    · exact Real.ratPow_pos hy q
    · exact alternatively
  exact Real.rpow_gt_one hgt1 h

theorem Real.ratPow_mono {x y:ℝ} (hx: x > 0) (hy: y > 0) {q:ℝ} (h: q > 0) : x > y ↔ rpow x q > rpow y q := by
  constructor
  · intro hxy
    exact Real.ratPow_mono' hx hy h hxy
  · intro hrpow
    by_contra! h'
    rcases lt_or_eq_of_le h' with hle | heq
    · have := Real.ratPow_mono' hy hx h hle
      linarith
    · rw [heq] at hrpow
      linarith

/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
lemma Real.ratPow_mono_of_gt_one' {x:ℝ} (hx: x > 1) {q r:ℝ} (hqr : q > r) : rpow x q > rpow x r := by
  have hadd := Real.ratPow_add (q:=r) (r:=(q-r)) (x:=x) (by linarith); ring_nf at hadd
  rw [hadd]
  suffices alternatively : rpow x (-r + q) > 1 by
    apply lt_mul_of_one_lt_right
    · exact Real.ratPow_pos (x:=x) (q:=r) (by linarith)
    · exact alternatively
  exact Real.rpow_gt_one hx (by linarith)

theorem Real.ratPow_mono_of_gt_one {x:ℝ} (hx: x > 1) {q r:ℝ} : rpow x q > rpow x r ↔ q > r := by
  constructor
  · intro hpow
    by_contra! h'
    rcases lt_or_eq_of_le h' with hle | heq
    · have := Real.ratPow_mono_of_gt_one' hx hle
      linarith
    · rw [heq] at hpow
      linarith
  · intro hqr
    exact Real.ratPow_mono_of_gt_one' hx hqr


/-- Proposition 6.7.3(e) / Exercise 6.7.1 -/
lemma Real.ratPow_one {q:ℝ} : rpow 1 q = 1 := by
  obtain ⟨q', hq'⟩ := Real.eq_lim_of_rat q
  have hpow := Real.ratPow_tendsto_rpow (x:=1) (by linarith) hq'
  have hone : (fun (n:ℕ) ↦ (1:ℝ) ^ (q' n:ℝ):Sequence).TendsTo 1 := by
    have hconst := lim_of_const 1
    convert hconst with n
    · rw [Real.one_rpow]
  have h1 := (Sequence.lim_eq.mp hpow).2
  have h2 := (Sequence.lim_eq.mp hone).2
  rwa [h1] at h2

lemma Real.ratPow_inv {x:ℝ} (hx : x > 0) (q:ℝ) : rpow (1 / x) q = 1 / rpow x q := by
  have hmul := Real.ratPow_mul' (x:=(1/x)) (y:=x) (by exact one_div_pos.mpr hx) (hx) q
  field_simp at hmul
  rw [Real.ratPow_one] at hmul
  symm
  rwa [div_eq_iff (a:=1) (b:=(rpow x q)) (by linarith only [Real.ratPow_pos hx q])]

theorem Real.ratPow_mono_of_lt_one {x:ℝ} (hx0: 0 < x) (hx: x < 1) {q r:ℝ} : rpow x q > rpow x r ↔ q < r := by
  set y := 1/x with ydef
  have hgt1 : y > 1 := by exact one_lt_one_div hx0 hx
  have hgt0 : y > 0 := by linarith
  have heq : x = 1 / y := by rw [one_div_one_div]
  rw [heq, Real.ratPow_inv (x:=y) (by linarith), Real.ratPow_inv (x:=y) (by linarith)]
  conv =>
    lhs
    rw [gt_iff_lt]
    rw [one_div_lt_one_div (by exact Real.ratPow_pos hgt0 r) (by exact Real.ratPow_pos hgt0 q)]
    rw [← gt_iff_lt]
  exact Real.ratPow_mono_of_gt_one hgt1

/-- Proposition 6.7.3(f) / Exercise 6.7.1 -/
theorem Real.ratPow_mul {x y:ℝ} (hx: x > 0) (hy: y > 0) (q:ℝ) : rpow (x*y) q = rpow x q * rpow y q := by
  apply Real.ratPow_mul' hx hy

end Chapter6
