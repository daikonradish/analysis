import Mathlib.Tactic
import Mathlib.Data.Real.Sign
import Analysis.Section_9_1

set_option doc.verso.suggestions false

/-!
# Analysis I, Section 9.3: Limiting values of functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Limits of continuous functions
- Connection with Mathlib's filter convergence concepts
- Limit laws for functions

Technical point: in the text, the functions `f` studied are defined only on subsets `X` of {lean}`ℝ`, and
left undefined elsewhere.  However, in Lean, this then creates some fiddly conversions when trying
to restrict `f` to various subsets of `X` (which, technically, are not precisely subsets of {lean}`ℝ`,
though they can be coerced to such).  To avoid this issue we will deviate from the text by having
our functions defined on all of {lean}`ℝ` (with the understanding that they are assigned "junk" values
outside of the domain `X` of interest).
-/

/-- Definition 9.3.1
Note the books uses ≤ instead of <, but < matches mathlib's definition of neighborhood.
-/
abbrev Real.CloseFn (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) : Prop :=
  ∀ x ∈ X, |f x - L| < ε

/-- Definition 9.3.3 -/
abbrev Real.CloseNear (ε:ℝ) (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop :=
  ∃ δ > 0, ε.CloseFn (X ∩ .Ioo (x₀-δ) (x₀+δ)) f L

namespace Chapter9

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (5.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by 
  intro x hx; simp at hx ⊢ 
  rw [show (4:ℝ) = 2^2 by norm_num, sq_sub_sq, abs_mul]
  have h1 : 3 ≤ x + 2 := by linarith 
  have h2 : x + 2 ≤ 5 := by linarith 
  have h3 : |x + 2| ≤ 5 := by grind 
  have h4 : |x - 2| ≤ 1 := by grind 
  calc _ ≤ 5 * 1 := by gcongr 
       _ = (5:ℝ) := by norm_num 
       _ < 5.1   := by norm_num  

/-- Example 9.3.2
Slight change from the book to accomodate the change to {lean}`Real.CloseFn`
-/
example : (0.42:ℝ).CloseFn (.Icc 1.9 2.1) (fun x ↦ x^2) 4 := by 
  intro x hx; simp at hx ⊢ 
  rw [show (4:ℝ) = 2^2 by norm_num, sq_sub_sq]
  rw [abs_lt]
  constructor <;> nlinarith 

/-- Example 9.3.4 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 4 := by
  intro h 
  specialize h 3 (by norm_num); simp at h
  rw [show 3^2=(9:ℝ) by norm_num] at h 
  ring_nf at h 
  norm_num at h

/-- Example 9.3.4 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  unfold Real.CloseNear
  use 0.01; simp; constructor 
  · norm_num 
  · intro x hx 
    simp at hx; norm_num at hx 
    simp 
    rw [abs_lt]
    constructor <;> nlinarith 

/-- Example 9.3.5 -/
example: ¬(0.1:ℝ).CloseFn (.Icc 1 3) (fun x ↦ x^2) 9 := by
  unfold Real.CloseFn
  by_contra! h 
  specialize h 1 (by norm_num)
  norm_num at h  


/-- Example 9.3.5 -/
example: (0.1:ℝ).CloseNear (.Icc 1 3) (fun x ↦ x^2) 9 3 := by
  unfold Real.CloseNear 
  use 0.01; constructor 
  · norm_num 
  · intro x hx; simp at hx ⊢ 
    rw [abs_lt]
    constructor <;> nlinarith

/-- Definition 9.3.6 (Convergence of functions at a point). -/
abbrev Convergesto (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) : Prop := ∀ ε > (0:ℝ), ε.CloseNear X f L x₀

/-- Connection with Mathlib filter convergence concepts -/
theorem Convergesto.iff (X:Set ℝ) (f: ℝ → ℝ) (L:ℝ) (x₀:ℝ) :
  Convergesto X f L x₀ ↔ (nhdsWithin x₀ X).Tendsto f (nhds L) := by
  unfold Convergesto Real.CloseNear Real.CloseFn nhdsWithin
  rw [LinearOrderedAddCommGroup.tendsto_nhds]
  peel with ε hε
  rw [Filter.eventually_inf_principal]
  simp [Filter.Eventually, mem_nhds_iff_exists_Ioo_subset]
  constructor
  . intro ⟨ δ, _, _ ⟩; use x₀-δ, x₀+δ, by grind
    intro _; simp; grind
  intro ⟨ l, u, ⟨ _, _ ⟩, h ⟩
  have h1 : 0 < x₀ - l := by linarith
  have h2 : 0 < u - x₀ := by linarith
  set δ := min (x₀ - l) (u - x₀)
  observe hδ1 : δ ≤ x₀ - l
  observe hδ2 : δ ≤ u - x₀
  use δ, (by positivity); intro x hxX _ _
  specialize h (show x ∈ .Ioo l u by simp; grind)
  simpa [hxX] using h

/-- Example 9.3.8 -/
example: Convergesto (.Icc 1 3) (fun x ↦ x^2) 4 2 := by
  intro ε hε 
  use (ε/5); constructor 
  · positivity 
  · intro x hx; simp at hx ⊢ 
    rw [abs_lt]
    constructor <;> nlinarith  
  

/-- Proposition 9.3.9 / Exercise 9.3.1 -/
theorem Convergesto.iff_conv {E:Set ℝ} (f: ℝ → ℝ) (L:ℝ) {x₀:ℝ} :
  Convergesto E f L x₀ ↔ ∀ a:ℕ → ℝ, (∀ n:ℕ, a n ∈ E) →
  Filter.atTop.Tendsto a (nhds x₀) →
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  constructor 
  · intro hconv a haE htt 
    simp_rw [Metric.tendsto_atTop, Real.dist_eq] at htt ⊢ 
    unfold Convergesto Real.CloseNear Real.CloseFn at hconv
    intro ε hε 
    choose δ hδpos hδ using hconv ε hε 
    choose N hN using htt δ hδpos 
    use N; intro n hn 
    specialize hN n (by linarith)
    specialize hδ (a n)
    apply hδ; constructor 
    · exact haE n 
    · simp; rw [abs_lt] at hN
      constructor <;> linarith 
  · intro h 
    by_contra! h' 
    unfold Convergesto Real.CloseNear Real.CloseFn at h'
    push_neg at h' 
    choose ε hεpos hε using h'
    have key : ∀ n : ℕ, ∃ x ∈ E ∩ Set.Ioo (x₀ - (1/(n+1:ℝ))) (x₀ + (1/(n+1:ℝ))), ε ≤ |f x - L| := by 
      intro n 
      exact hε (1 / (n+1:ℝ)) (by positivity)
    choose a haN haε using key 
    have haE : ∀ n, a n ∈ E := by 
      intro n 
      specialize haN n 
      exact haN.1
    have httx₀ : Filter.Tendsto a Filter.atTop (nhds x₀) := by 
      have haN' : ∀ n : ℕ, a n ∈ Set.Ioo (x₀ - (1/(n+1:ℝ))) (x₀ + (1/(n+1:ℝ))) := by 
        intro n 
        exact (haN n).2
      rw [tendsto_iff_dist_tendsto_zero]
      simp_rw [Real.dist_eq]
      apply squeeze_zero (g0:=tendsto_one_div_add_atTop_nhds_zero_nat)
      · intro n; positivity 
      · intro n
        specialize haN' n; simp at haN' 
        rw [abs_le]
        constructor <;> grind 
    specialize h a haE httx₀ 
    rw [Metric.tendsto_atTop] at h 
    choose N hN using h ε hεpos 
    specialize hN N (by rfl)
    specialize haε N 
    rw [Real.dist_eq] at hN; grind


theorem Convergesto.comp {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto E f L x₀) {a:ℕ → ℝ}
  (ha: ∀ n:ℕ, a n ∈ E) (hconv: Filter.atTop.Tendsto a (nhds x₀)) :
  Filter.atTop.Tendsto (fun n ↦ f (a n)) (nhds L) := by
  rw [iff_conv f L] at hf; solve_by_elim

-- Remark 9.3.11 is not quite true in Lean: the hypothesis `AdherentPt x₀ E` is safely removed
-- from most theorems (with the exception of Convergesto.uniq).

/-- Corollary 9.3.13 -/
theorem Convergesto.uniq {E:Set ℝ} {f: ℝ → ℝ} {L L':ℝ} {x₀:ℝ} (h: AdherentPt x₀ E)
  (hf: Convergesto E f L x₀) (hf': Convergesto E f L' x₀) : L = L' := by
  -- This proof is written to follow the structure of the original text.
  let ⟨ a, ha, hconv ⟩ := (limit_of_AdherentPt _ _).mp h
  exact tendsto_nhds_unique (hf.comp ha hconv) (hf'.comp ha hconv)

/-- Proposition 9.3.14 (Limit laws for functions) -/
theorem Convergesto.add {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f + g) (L + M) x₀ := by
    -- This proof is written to follow the structure of the original text.
    rw [iff_conv _ _] at hf hg ⊢
    intro a ha hconv; specialize hf a ha hconv; specialize hg a ha hconv
    convert hf.add hg using 1

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.sub {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f - g) (L - M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢ 
    intro a ha hconv
    specialize hf a ha hconv 
    specialize hg a ha hconv 
    apply hf.sub hg 

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.max {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (max f g) (max L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢ 
    intro a ha hconv
    specialize hf a ha hconv 
    specialize hg a ha hconv
    apply hf.max hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.min {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (min f g) (min L M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢ 
    intro a ha hconv
    specialize hf a ha hconv 
    specialize hg a ha hconv
    apply hf.min hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.smul {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (c:ℝ) :
  Convergesto E (c • f) (c * L) x₀ := by
    rw [iff_conv _ _] at hf ⊢
    intro a ha hconv
    specialize hf a ha hconv  
    exact hf.const_smul c



/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2 -/
theorem Convergesto.mul {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ}
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f * g) (L * M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢ 
    intro a ha hconv
    specialize hf a ha hconv 
    specialize hg a ha hconv
    apply hf.mul hg

/-- Proposition 9.3.14 (Limit laws for functions) / Exercise 9.3.2.  The hypothesis in the book that g is non-vanishing on E can be dropped. -/
theorem Convergesto.div {E:Set ℝ} {f g: ℝ → ℝ} {L M:ℝ} {x₀:ℝ} (hM: M ≠ 0)
  (hf: Convergesto E f L x₀) (hg: Convergesto E g M x₀) :
  Convergesto E (f / g) (L / M) x₀ := by
    rw [iff_conv _ _] at hf hg ⊢ 
    intro a ha hconv
    specialize hf a ha hconv 
    specialize hg a ha hconv
    apply hf.div hg 
    exact hM 

theorem Convergesto.const (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun _ ↦ c) c x₀ := by
  rw [iff_conv _ _]
  intro a ha hconv 
  simp  

theorem Convergesto.id (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x) x₀ x₀ := by
  rw [iff_conv _ _]
  intro a ha hconv 
  exact hconv 

theorem Convergesto.sq (E:Set ℝ) (x₀:ℝ)
  : Convergesto E (fun x ↦ x^2) (x₀^2) x₀ := by
  rw [iff_conv _ _]
  intro a ha hconv 
  exact hconv.pow 2 

theorem Convergesto.linear (E:Set ℝ) (x₀:ℝ) (c:ℝ)
  : Convergesto E (fun x ↦ c * x) (c * x₀) x₀ := by
  rw [iff_conv _ _]
  intro a ha hconv 
  exact hconv.const_mul c

theorem Convergesto.quadratic (E:Set ℝ) (x₀:ℝ) (c d:ℝ)
  : Convergesto E (fun x ↦ x^2 + c * x + d) (x₀^2 + c * x₀ + d) x₀ := by
  rw [iff_conv _ _]
  intro a ha hconv
  have hsq := hconv.pow 2 
  have hc := hconv.const_mul c 
  exact (hsq.add hc).add_const d 

theorem Convergesto.restrict {X Y:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} (hf: Convergesto X f L x₀) (hY: Y ⊆ X) : Convergesto Y f L x₀ := by
  rw [iff_conv _ _] at hf ⊢ 
  intro a ha hconv
  exact hf a (by intro n; apply hY; exact ha n) hconv 


theorem Real.sign_def (x:ℝ) : Real.sign x = if x < 0 then -1 else if x > 0 then 1 else 0 := rfl

/-- Example 9.3.16 -/
theorem Convergesto.sign_right : Convergesto (.Ioi 0) Real.sign 1 0 := by 
  rw [iff_conv _ _]
  intro a ha hconv 
  have hfun : (fun n => if a n < 0 then (-1 : ℝ) else if a n > 0 then 1 else 0)
      = (fun _ => (1 : ℝ)) := by
    funext n
    have hn : 0 < a n := by simpa using ha n
    rw [if_neg (not_lt.mpr hn.le), if_pos hn]
  simp_rw [Real.sign_def, hfun]
  simp 


/-- Example 9.3.16 -/
theorem Convergesto.sign_left : Convergesto (.Iio 0) Real.sign (-1) 0 := by
  rw [iff_conv _ _]
  intro a ha hconv 
  have hfun : (fun n => if a n < 0 then (-1 : ℝ) else if a n > 0 then 1 else 0)
      = (fun _ => (-1 : ℝ)) := by
    funext n
    have hn : a n < 0 := by simpa using ha n 
    rw [if_neg (not_lt.mpr hn.le), if_pos hn]
  simp_rw [Real.sign_def, hfun]
  simp 

/-- Example 9.3.16 -/
theorem Convergesto.sign_all : ¬ ∃ L, Convergesto (.univ) Real.sign L 0 := by 
  push_neg 
  intro L h 
  specialize h 1 (by positivity)
  choose δ hδpos hδ using h 
  have h1 := hδ (-δ/2) (by simp; grind) 
  have h2 := hδ (δ/2) (by simp; grind)
  rw [Real.sign_def] at h1 h2 
  rw [if_pos (by grind)] at h1 
  rw [if_neg (by grind), if_pos (by grind)] at h2
  grind

noncomputable abbrev f_9_3_17 : ℝ → ℝ := fun x ↦ if x = 0 then 1 else 0

theorem Convergesto.f_9_3_17_remove : Convergesto (.univ \ {0}) f_9_3_17 0 0 := by 
  unfold f_9_3_17
  intro ε hε 
  use 1, by positivity 
  simp 
  intro a ha; simp at ha 
  simp 
  rw [if_neg (by exact ha.1)]
  simp; exact hε 

theorem Convergesto.f_9_3_17_all : ¬ ∃ L, Convergesto .univ f_9_3_17 L 0 := by 
  unfold f_9_3_17
  push_neg 
  intro L h 
  specialize h 0.5 (by positivity)
  choose δ hδpos hδ using h 
  have h1 := hδ 0 (by simp; grind) 
  have h2 := hδ (-δ/2) (by simp; grind)
  simp at h1 h2 
  rw [if_neg (by linarith)] at h2 
  simp at h2
  rw [abs_lt] at h1 h2
  linarith 
  
  
/-- Proposition 9.3.18 / Exercise 9.3.3 -/
theorem Convergesto.local {E:Set ℝ} {f: ℝ → ℝ} {L:ℝ} {x₀:ℝ} {δ:ℝ} (hδ: δ > 0) :
  Convergesto E f L x₀ ↔ Convergesto (E ∩ .Ioo (x₀-δ) (x₀+δ)) f L x₀ := by
  constructor 
  · intro h 
    apply restrict h 
    simp  
  · intro h ε hε
    choose δ' hδpos' hδ' using h ε hε 
    use Min.min δ δ'; constructor 
    · positivity
    · convert hδ' using 1 
      grind 


/-- Example 9.3.19.  The point of this example is somewhat blunted by the ability to remove the hypothesis that {lit}`g` is non-zero from the relevant part of Proposition 9.3.14 -/
example : Convergesto .univ (fun x ↦ (x+2)/(x+1)) (4/3:ℝ) 2 := by 
  apply Convergesto.div (by linarith)
  · rw [show (4:ℝ) = 2 + 2 by linarith]
    apply Convergesto.add
    · apply Convergesto.id  
    · apply Convergesto.const
  · rw [show (3:ℝ) = 2 + 1 by linarith]
    apply Convergesto.add 
    · apply Convergesto.id  
    · apply Convergesto.const

/-- Example 9.3.20 -/
example : Convergesto (.univ \ {1}) (fun x ↦ (x^2-1)/(x-1)) 2 1 := by 
  rw [show (2:ℝ) = 2 / 1 by linarith]
  nth_rewrite 2 [show (1:ℝ) = (1:ℝ) ^ (2:ℕ) by linarith]
  simp_rw [sq_sub_sq, mul_div_assoc]
  apply Convergesto.mul
  · rw [show (2:ℝ) = 1 + 1 by linarith]
    apply Convergesto.add
    · apply Convergesto.id
    · apply Convergesto.const 
  · simp 
    intro ε hε 
    use ε; constructor 
    · exact hε 
    · intro x hx; simp at hx 
      simp 
      rw [div_self (by grind)]
      simp; exact hε 


open Classical in
/-- Example 9.3.21 -/
noncomputable abbrev f_9_3_21 : ℝ → ℝ := fun x ↦ if x ∈ (fun q:ℚ ↦ (q:ℝ)) '' .univ then 1 else 0


lemma f_9_3_21_rational_to_one : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by 
  unfold f_9_3_21
  rw [Metric.tendsto_atTop]
  intro ε hε 
  simp_rw [Real.dist_eq]
  choose N hN using exists_nat_gt (1/ε) 
  use N 
  intro n hn 
  rw [if_pos]
  · simp; exact hε
  . simp; use (n)⁻¹; simp 

example : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 (1/n:ℝ)) (nhds 1) := by 
  apply f_9_3_21_rational_to_one


lemma f_9_3_21_irrational_to_zero : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by 
  unfold f_9_3_21
  rw [Metric.tendsto_atTop]
  intro ε hε 
  simp_rw [Real.dist_eq]
  choose N hN using exists_nat_gt (1/ε) 
  use N 
  intro n hn 
  rw [if_neg]
  · simp; exact hε
  · simp 
    intro q hq 
    have : 0 < 1/ε  := by positivity 
    have : 0 < (N:ℝ) := by linarith 
    have : (N:ℝ) ≤ (n:ℝ) := by norm_cast
    have : 0 < (n:ℝ) := by linarith 
    have : (n:ℝ) ≠ 0 := by linarith 
    norm_cast at this 
    have h := irrational_sqrt_two.div_natCast this
    refine absurd ?_ h 
    simp; use q

example : Filter.atTop.Tendsto (fun (n:ℕ) ↦ f_9_3_21 ((Real.sqrt 2)/n:ℝ)) (nhds 0) := by 
  apply f_9_3_21_irrational_to_zero 

example : ¬ ∃ L, Convergesto .univ f_9_3_21 L 0 := by 
  by_contra h 
  choose L hL using h 
  rw [Convergesto.iff_conv] at hL 
  have hrational : Filter.Tendsto (fun (n:ℕ) => (1:ℝ)/n) Filter.atTop (nhds 0) := by 
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hirrational : Filter.Tendsto (fun (n:ℕ) => (Real.sqrt 2)/(n:ℝ)) Filter.atTop (nhds 0) := by 
    exact tendsto_const_div_atTop_nhds_zero_nat √2
  have hrational' := hL _ (by tauto) hrational 
  have hirrational' := hL _ (by tauto) hirrational 
  have h1 := tendsto_nhds_unique hrational' f_9_3_21_rational_to_one
  have h0 := tendsto_nhds_unique hirrational' f_9_3_21_irrational_to_zero
  grind

/- Exercise 9.3.4: State a definition of limit superior and limit inferior for functions, and prove an analogue of Proposition 9.3.9 for those definitions. -/

/-- Exercise 9.3.5 (Continuous version of squeeze test) -/
theorem Convergesto.squeeze {E:Set ℝ} {f g h: ℝ → ℝ} {L:ℝ} {x₀:ℝ}
  (hfg: ∀ x ∈ E, f x ≤ g x) (hgh: ∀ x ∈ E, g x ≤ h x)
  (hf: Convergesto E f L x₀) (hh: Convergesto E h L x₀) :
  Convergesto E g L x₀ := by
  rw [iff_conv _ _] at hf hh ⊢
  intro a ha haconv 
  specialize hf a ha haconv 
  specialize hh a ha haconv 
  apply hf.squeeze hh 
  · intro n; simp
    exact hfg (a n) (by exact ha n) 
  · intro n; simp 
    exact hgh (a n) (by exact ha n)


end Chapter9
