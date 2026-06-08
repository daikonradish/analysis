import Mathlib.Tactic

/-!
# Analysis I, Section 8.1: Countability

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Custom notions for "equal cardinality", "countable", and "at most countable".  Note that Mathlib's
{name}`Countable` typeclass corresponds to what we call "at most countable" in this text.
- Countability of the integers and rationals.

Note that as the Chapter 3 set theory has been deprecated, we will not re-use relevant constructions from that theory here, replacing them with Mathlib counterparts instead.

-/

namespace Chapter8

/-- The definition of equal cardinality. For simplicity we restrict attention to the Type 0 universe.
This is analogous to `Chapter3.SetTheory.Set.EqualCard`, but we are not using the latter since
the Chapter 3 set theory is deprecated. -/
abbrev EqualCard (X Y : Type) : Prop := ∃ f : X → Y, Function.Bijective f

/-- Relation with Mathlib's {name}`Equiv` concept -/
theorem EqualCard.iff {X Y : Type} : EqualCard X Y ↔ Nonempty (X ≃ Y) := by
  simp [EqualCard]; constructor
  . intro ⟨ f, hf ⟩; exact ⟨ .ofBijective f hf ⟩
  intro ⟨ e ⟩; exact ⟨ e.toFun, e.bijective ⟩

/-- Equivalence with Mathlib's {name}`Cardinal.mk` concept -/
theorem EqualCard.iff' {X Y : Type} : EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y := by
  simp [Cardinal.eq, iff]

theorem EqualCard.refl (X : Type) : EqualCard X X := by
  have : Cardinal.mk X = Cardinal.mk X := by rfl
  exact EqualCard.iff'.mpr this

theorem EqualCard.symm {X Y : Type} (hXY : EqualCard X Y) : EqualCard Y X := by
  have := EqualCard.iff'.mp hXY
  exact EqualCard.iff'.mpr this.symm

theorem EqualCard.trans {X Y Z : Type} (hXY : EqualCard X Y) (hYZ : EqualCard Y Z) :
  EqualCard X Z := by
    have hcXY := EqualCard.iff'.mp hXY
    have hcYZ := EqualCard.iff'.mp hYZ
    have hcXZ : Cardinal.mk X = Cardinal.mk Z := by grind
    exact EqualCard.iff'.mpr hcXZ

instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩

theorem EqualCard.univ (X : Type) : EqualCard (.univ : Set X) X :=
  ⟨ Subtype.val, Subtype.val_injective, by intro _; aesop ⟩

abbrev CountablyInfinite (X : Type) : Prop := EqualCard X ℕ

abbrev AtMostCountable (X : Type) : Prop := CountablyInfinite X ∨ Finite X

theorem CountablyInfinite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  CountablyInfinite X ↔ CountablyInfinite Y := ⟨ hXY.symm.trans, hXY.trans ⟩

theorem Finite.equiv {X Y: Type} (hXY : EqualCard X Y) :
  Finite X ↔ Finite Y := by obtain ⟨ f, hf ⟩ := hXY; exact (Equiv.ofBijective f hf).finite_iff

theorem AtMostCountable.equiv {X Y: Type} (hXY : EqualCard X Y) :
  AtMostCountable X ↔ AtMostCountable Y := by
  simp [AtMostCountable, CountablyInfinite.equiv hXY, Finite.equiv hXY]

/-- Equivalence with Mathlib's {name}`Denumerable` concept (cf. Remark 8.1.2) -/
theorem CountablyInfinite.iff (X : Type) : CountablyInfinite X ↔ Nonempty (Denumerable X) := by
  simp [CountablyInfinite, EqualCard.iff]; constructor
  . intro ⟨ e ⟩; exact ⟨ Denumerable.mk' e ⟩
  intro ⟨ h ⟩; exact ⟨ h.eqv X ⟩

/-- Equivalence with Mathlib's {name}`Countable` typeclass -/
theorem CountablyInfinite.iff' (X : Type) : CountablyInfinite X ↔ Countable X ∧ Infinite X := by
  rw [iff, nonempty_denumerable_iff]

theorem CountablyInfinite.toCountable {X : Type} (hX: CountablyInfinite X) : Countable X := by
  simp_all [iff']

theorem CountablyInfinite.toInfinite {X : Type} (hX: CountablyInfinite X) : Infinite X := by
  simp_all [iff']

theorem AtMostCountable.iff (X : Type) : AtMostCountable X ↔ Countable X := by
  observe h1 : CountablyInfinite X ↔ Countable X ∧ Infinite X
  observe h2 : Finite X ∨ Infinite X
  observe h3 : Finite X → Countable X
  tauto

theorem CountablyInfinite.iff_image_inj {A:Type} (X: Set A) : CountablyInfinite X ↔ ∃ f : ℕ ↪ A, X = f '' .univ := by
  constructor
  . intro ⟨ g, hg ⟩
    choose f hleft hright using Function.bijective_iff_has_inverse.mp hg
    refine ⟨ ⟨ Subtype.val ∘ f, ?_ ⟩, ?_ ⟩
    . intro x y hxy; apply hright.injective; simp_all [Subtype.val_inj]
    ext; simp; constructor
    . intro hx; use g ⟨ _, hx ⟩; simp [hleft _]
    rintro ⟨ _, rfl ⟩; aesop
  intro ⟨ f, hf ⟩
  have := Function.leftInverse_invFun (Function.Embedding.injective f)
  use (Function.invFun f) ∘ Subtype.val; split_ands
  . rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ h; grind
  intro n; use ⟨ f n, by aesop ⟩; grind

/-- Examples 8.1.3 -/
example : CountablyInfinite ℕ := by
  rw [CountablyInfinite.iff']
  constructor
  · exact instCountableNat
  · exact instInfiniteNat

example : CountablyInfinite (.univ \ {0}: Set ℕ) := by
  rw [CountablyInfinite.iff']
  constructor
  · use (fun n => n + 1)
    intro a b hab; simp at hab
    ext; exact hab
  · set f : ℕ → (.univ \ {0}: Set ℕ) := fun n => ⟨n + 1, by grind⟩
    apply Infinite.of_injective f
    intro a b hab; unfold f at hab
    simp at hab; exact hab

example : CountablyInfinite ((fun n:ℕ ↦ 2*n) '' .univ) := by
  rw [CountablyInfinite.iff']
  set f : ((fun n:ℕ ↦ 2*n) '' .univ) → ℕ := fun n => n / 2
  set g : ℕ → ((fun n:ℕ ↦ 2*n) '' .univ) := fun n => ⟨2 * n, by grind⟩
  constructor
  · use f
    intro a b hab
    grind
  · apply Infinite.of_injective g
    intro a b hab
    grind

/-- Proposition 8.1.4 (Well ordering principle) / Exercise 8.1.2 -/
theorem Nat.exists_min {X: Set ℕ} (hX : X.Nonempty) : ∃ m ∈ X, ∀ n ∈ X, m ≤ n := by
  by_contra! h
  suffices ∀ n:ℕ, n ∉ X by
    choose k hk using hX
    specialize h k hk
    choose m hmX hmlt using h
    specialize this m
    exact this hmX
  intro n hn
  induction' n using Nat.strong_induction_on with k ih
  specialize h k hn
  choose m hm using h
  specialize ih m hm.2 hm.1
  exact ih

theorem Nat.exists_unique_min {X : Set ℕ} (hX : X.Nonempty) :
  ∃! m ∈ X, ∀ n ∈ X, m ≤ n := by
  choose m hm using Nat.exists_min hX
  use m; constructor
  · simp; exact hm
  · intro m' hm'
    have hle := hm.2 m' hm'.1
    have hge := hm'.2 m hm.1
    linarith


def Int.exists_unique_min : Decidable (∀ (X : Set ℤ) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use Set.Iio 0
  constructor
  · use -1; grind
  · intro hm
    obtain ⟨m, ⟨hmem, hmin⟩, hunique⟩ := hm
    have : m - 1 ∈ Set.Iio 0 := by grind
    specialize hmin (m - 1) this
    linarith


def NNRat.exists_unique_min : Decidable (∀ (X : Set NNRat) (hX : X.Nonempty), ∃! m ∈ X, ∀ n ∈ X, m ≤ n) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  apply isFalse
  push_neg
  use Set.Ioi 0
  constructor
  · use (1/2); simp
  · intro hm
    obtain ⟨m, ⟨hmem, hmin⟩, hunique⟩ := hm
    have : (m/2) ∈ Set.Ioi 0 := by
      simp at hmem
      have : 0 < m / 2 := by positivity
      exact this
    specialize hmin (m/2) this
    field_simp at hmin
    have : m > 0 := by exact hmem
    have h : m < m * 2 := by
      nth_rw 1 [← mul_one m]
      apply mul_lt_mul_of_pos_left _ this
      norm_num
    push_cast at h hmin
    exact absurd hmin (not_le.mpr h)

open Classical in
noncomputable abbrev Nat.min (X : Set ℕ) : ℕ := if hX : X.Nonempty then (exists_unique_min hX).exists.choose else 0

theorem Nat.min_spec {X : Set ℕ} (hX : X.Nonempty) : min X ∈ X ∧ ∀ n ∈ X, min X ≤ n := by
  simp [hX, min]; exact (exists_unique_min hX).exists.choose_spec

theorem Nat.min_eq {X : Set ℕ} (hX : X.Nonempty) {a:ℕ} (ha : a ∈ X ∧ ∀ n ∈ X, a ≤ n) : min X = a :=
  (exists_unique_min hX).unique (min_spec hX) ha

@[simp]
theorem Nat.min_empty : min ∅ = 0 := by simp [Nat.min]

example : Nat.min ((fun n ↦ 2*n) '' (.Ici 1)) = 2 := by
  rw [Nat.min_eq]
  · use 2; simp
  · constructor
    · simp
    · intro n hn
      simp at hn
      choose n' hn' using hn
      nlinarith

theorem Nat.min_eq_sInf {X : Set ℕ} (hX : X.Nonempty) : min X = sInf X := by
  have hspec := Nat.min_spec hX
  apply le_antisymm
  · apply le_csInf hX hspec.2
  · apply Nat.sInf_le hspec.1

open Classical in
/-- Equivalence with Mathlib's {name}`Nat.find` method -/
theorem Nat.min_eq_find {X : Set ℕ} (hX : X.Nonempty) : min X = Nat.find hX := by
  symm; rw [Nat.find_eq_iff]; have := min_spec hX; grind

/-- Proposition 8.1.5 -/
theorem Nat.monotone_enum_of_infinite (X : Set ℕ) [Infinite X] : ∃! f : ℕ → X, Function.Bijective f ∧ StrictMono f := by
  -- This proof is written to follow the structure of the original text.
  let a : ℕ → ℕ := Nat.strongRec (fun n a ↦ min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m h })
  have ha : ∀ n, a n = min { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := Nat.strongRec.eq_def _
  have ha_infinite (n:ℕ) : Infinite { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
    have hXinf : X.Infinite := Set.infinite_coe_iff.mp (inferInstance)
    have hX' :  { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } = X \ Finset.image a (Finset.range n) := by
      ext k
      simp; tauto
    rw [hX']
    apply Set.infinite_coe_iff.mpr
    apply hXinf.diff (t:=Finset.image a (Finset.range n))
    apply Finset.finite_toSet
  have ha_nonempty (n:ℕ) : { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m }.Nonempty := Set.Nonempty.of_subtype
  have ha_mono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hle : a n ≤ a (n+1) := by
      rw [ha n, ha (n+1), Nat.min_eq_sInf (ha_nonempty n), Nat.min_eq_sInf (ha_nonempty (n+1))]
      apply csInf_le_csInf
      · use 0
        intro x hx; simp
      · exact ha_nonempty (n+1)
      · intro x hx; simp at hx ⊢
        constructor
        · exact hx.1
        · intro m hm
          exact hx.2 m (by linarith)
    have hneq : a n ≠ a (n+1) := by
      rw [ha (n+1), Nat.min_eq_sInf (ha_nonempty (n+1))]
      have hinfmem := Nat.sInf_mem (ha_nonempty (n+1))
      have hneq := hinfmem.2 n (by linarith)
      exact hneq.symm
    grind
  have ha_injective : Function.Injective a := by
    exact ha_mono.injective
  have haX (n:ℕ) : a n ∈ X := by
    have hnmem (n : ℕ): a n ∈ {x | x ∈ X ∧ ∀ m < n, x ≠ a m} := by
      rw [ha n, Nat.min_eq_sInf (ha_nonempty n)]
      exact Nat.sInf_mem (ha_nonempty n)
    specialize hnmem n
    exact hnmem.1
  set f : ℕ → X := fun n ↦ ⟨ a n, haX n ⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy; simp [f] at hxy; solve_by_elim
  have hf_surjective : Function.Surjective f := by
    intro ⟨ x, hx ⟩; simp [f]; by_contra
    have h1 (n:ℕ) : x ∈ { x ∈ X | ∀ (m:ℕ) (h:m < n), x ≠ a m } := by
      constructor
      · exact hx
      · by_contra! hexist
        contrapose! this
        choose m hm using hexist
        use m
        exact hm.2.symm
    have h2 (n:ℕ) : x ≥ a n := by
      rw [ha n]; exact ge_iff_le.mpr ((min_spec (ha_nonempty n)).2 _ (h1 n))
    have h3 (n:ℕ) : a n ≥ n := by
      exact ha_mono.le_apply
    have h4 (n:ℕ) : x ≥ n := (h3 n).trans (h2 n)
    linarith [h4 (x+1)]
  apply ExistsUnique.intro f ⟨ ⟨ hf_injective, hf_surjective ⟩, ha_mono ⟩
  intro g ⟨ hg_bijective, hg_mono ⟩; by_contra!
  replace : { n | g n ≠ f n }.Nonempty := by
    contrapose! this
    apply funext; simpa [Set.eq_empty_iff_forall_notMem] using this
  set m := min { n | g n ≠ f n }
  have hm : g m ≠ f m := (min_spec this).1
  have hm' {n:ℕ} (hn: n < m) : g n = f n := by by_contra hgfn; linarith [(min_spec this).2 n (by simp [hgfn])]
  have hgm : g m = min { x ∈ X | ∀ (n:ℕ) (h:n < m), x ≠ a n } := by
    have hga {k : ℕ} (hk : k < m) : g k = a k := by
      have := hm' (n:=k) (by grind)
      unfold f at this
      grind
    symm; apply Nat.min_eq (ha_nonempty m)
    constructor
    · constructor
      · simp
      · intro n hn
        specialize hga (k:=n) (by grind)
        rw [← hga]
        suffices g n < g m by grind
        exact hg_mono hn
    · rintro n ⟨hnX, hltn⟩
      by_contra! hlt
      obtain ⟨k, hk⟩ := hg_bijective.surjective ⟨n, hnX⟩
      have hgkn := congrArg Subtype.val hk; simp at hgkn
      have hkm : m ≤ k := by
        by_contra! h'
        have heq : a k = n := by rw [← hgkn, hga h']
        have hneq := hltn k h'
        exact hneq.symm heq
      have hgkm := hg_mono.monotone hkm
      rw [← hgkn] at hlt
      norm_cast at hlt
      grind
  rw [←ha m] at hgm; contrapose! hm; exact Subtype.val_injective hgm

theorem Nat.countable_of_infinite (X : Set ℕ) [Infinite X] : CountablyInfinite X := by
  have := (monotone_enum_of_infinite X).exists
  exact EqualCard.symm ⟨ this.choose, this.choose_spec.1 ⟩

/-- Corollary 8.1.6 -/
theorem Nat.atMostCountable_subset (X: Set ℕ) : AtMostCountable X := by
  obtain _ | _ := finite_or_infinite X
  . tauto
  simp [AtMostCountable, countable_of_infinite]

/-- Corollary 8.1.7 -/
theorem AtMostCountable.subset {X: Type} (hX : AtMostCountable X) (Y: Set X) : AtMostCountable Y := by
  -- This proof is written to follow the structure of the original text.
  obtain ⟨ f, hf ⟩ | hX := hX
  . let f' : Y → f '' Y := fun y ↦ ⟨ f y, by aesop ⟩
    have hf' : Function.Bijective f' := by
      constructor
      · intro a b hab
        unfold f' at hab; simp at hab
        have hab' := hf.injective hab
        exact Subtype.val_injective hab'
      · intro y
        obtain ⟨x, hx, heq⟩ := y.property
        use ⟨x, hx⟩
        unfold f'; simp
        ext; exact heq
    rw [equiv ⟨ _, hf' ⟩ ]; apply Nat.atMostCountable_subset
  simp [AtMostCountable, show Finite Y by infer_instance]

theorem AtMostCountable.subset' {A: Type} {X Y: Set A} (hX: AtMostCountable X) (hY: Y ⊆ X) : AtMostCountable Y := by
  refine' (equiv ⟨ fun y ↦ ⟨ ↑↑y, y.property ⟩, _, _ ⟩).mp (subset hX { x : X | ↑x ∈ Y })
  . intro ⟨ ⟨ _, _ ⟩, _ ⟩ ⟨ ⟨ _, _ ⟩, _ ⟩ _; simp_all
  intro ⟨ y, hy ⟩; use ⟨ ⟨ y, hY hy ⟩, by aesop ⟩

/-- Proposition 8.1.8 / Exercise 8.1.4 -/
theorem AtMostCountable.image_nat (Y: Type) (f: ℕ → Y) : AtMostCountable (f '' .univ) := by
  set Τ := {n : ℕ | ∀ m < n, f m ≠ f n}
  set f' : Τ → f '' Set.univ := fun ⟨n, hn⟩ => ⟨f n, by simp⟩
  have hinjf' : Function.Injective f' := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    unfold f' at hab
    simp at hab ⊢
    rcases lt_trichotomy a b with hlt | heq | hgt
    · unfold Τ at hb; simp at hb
      specialize hb a hlt
      exact absurd hab hb
    · exact heq
    · unfold Τ at ha; simp at ha
      specialize ha b hgt
      exact absurd hab.symm ha
  have hsurjf' : Function.Surjective f' := by
    rintro ⟨y, ⟨x, hx, hxeq⟩⟩
    have hnonempty : {k:ℕ | f k = y}.Nonempty := by use x; simp; exact hxeq
    choose k hkmin using Nat.exists_min hnonempty
    use ⟨k, ?_⟩
    · unfold f'; simp
      exact hkmin.1
    · unfold Τ
      intro m hlt
      by_contra! heq
      have : k ≤ m := by exact hkmin.2 m (by grind)
      linarith
  have hΤatmost := Nat.atMostCountable_subset Τ
  refine (AtMostCountable.equiv ?equalcard).mp hΤatmost
  use f'
  exact ⟨hinjf', hsurjf'⟩


/-- Corollary 8.1.9 / Exercise 8.1.5 -/
theorem AtMostCountable.image {X:Type} (hX: CountablyInfinite X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  choose g hg using hX
  set geq := Equiv.ofBijective g hg
  set g' := geq.symm
  have huniv : f '' Set.univ = (f ∘ g') '' Set.univ := by
    ext y
    simp; constructor
    · intro hexist; choose x hx using hexist
      use g x; unfold g' geq
      simp; exact hx
    · intro hexist; choose x hx using hexist
      use g' x
  rw [huniv]
  apply AtMostCountable.image_nat

theorem AtMostCountable.image' {X:Type} (hX: AtMostCountable X) {Y: Type} (f: X → Y) : AtMostCountable (f '' .univ) := by
  rcases hX with hcountable | hfinite
  · apply AtMostCountable.image hcountable
  · right
    exact Finite.Set.finite_image Set.univ f


/-- Proposition 8.1.10 / Exercise 8.1.7 -/
theorem CountablyInfinite.union {A:Type} {X Y: Set A} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X ∪ Y: Set A) := by
  have hunion : (X ∪ Y:Set A) = (X:Set A) ∪ ((Y \ X):Set A) := by
    ext n; simp
  rw [hunion]
  have hsubset : ((Y \ X):Set A) ⊆ (Y:Set A) := by
    intro y hy; simp at hy; exact hy.1
  rcases AtMostCountable.subset' (by left; exact hY) hsubset with hinfinite | hfinite
  · choose f hf using hX
    set f' := (Equiv.ofBijective f hf).symm
    choose g hg using hinfinite
    set g' := (Equiv.ofBijective g hg).symm
    set l : ℕ → (X ∪ Y \ X:Set A) := fun n => if Even n then ⟨f' (n / 2), by grind⟩ else ⟨g' (n/2), by grind⟩
    have hlinj : Function.Injective l := by
      intro a b hab
      by_cases! haeo : Even a <;> by_cases! hbeo : Even b
      · unfold l at hab; rw [if_pos haeo, if_pos hbeo] at hab
        simp at hab
        have hsub := Subtype.val_injective hab
        have hal := f'.injective hsub
        grind
      · unfold l at hab; rw [if_pos haeo, if_neg hbeo] at hab
        simp at hab
        have hin  : (f' (a / 2):A) ∈ (X:Set A) := by simp
        have hnotin : (g' (b / 2):A) ∉ (X:Set A) := by grind
        rw [hab] at hin
        exact absurd hin hnotin
      · unfold l at hab; rw [if_neg haeo, if_pos hbeo] at hab
        simp at hab
        have hin  : (f' (b / 2):A) ∈ (X:Set A) := by grind
        have hnotin : (g' (a / 2):A) ∉ (X:Set A) := by grind
        rw [← hab] at hin
        exact absurd hin hnotin
      · unfold l at hab; rw [if_neg haeo, if_neg hbeo] at hab
        simp at hab
        have hsub := Subtype.val_injective hab
        have hal := g'.injective hsub
        grind
    have hlsurj : Function.Surjective l := by
      intro ⟨b, hb⟩ ; rcases hb with hx | hyx
      · set N := 2 * f'.symm ⟨b, hx⟩
        have heven : Even N := by grind
        use N
        unfold l; rw [if_pos heven]
        unfold N; simp
      · set N := 2 * g'.symm ⟨b, hyx⟩ + 1
        have hodd : ¬ Even N := by grind
        use N
        unfold l; rw [if_neg hodd]
        simp
        unfold N
        have hdiv : (2 * g'.symm ⟨b, hyx⟩ + 1) / 2 = g'.symm ⟨b, hyx⟩ := by omega
        rw [hdiv]
        grind
    set l' := (Equiv.ofBijective l ⟨hlinj, hlsurj⟩).symm
    use l'; exact Equiv.bijective l'
  · choose f hf using hX
    set f' := (Equiv.ofBijective f hf).symm
    haveI hfinty : Fintype (Y \ X:Set A) := Fintype.ofFinite (Y \ X:Set A)
    set g := Fintype.equivFin (Y \ X:Set A)
    set N := Fintype.card (Y \ X:Set A)
    set l : ℕ → (X ∪ Y \ X:Set A) := fun n =>
      if hN : n < N then ⟨g.symm ⟨n, hN⟩, by right; simp⟩
      else  ⟨f' (n - N), by left; simp⟩
    have hlinj : Function.Injective l := by
      intro a b hab
      by_cases haN : a < N <;> by_cases! hbN : b < N
      · unfold l at hab; rw [dif_pos haN, dif_pos hbN] at hab
        simp at hab
        have hsub := Subtype.val_injective hab
        simp at hsub; exact hsub
      · unfold l at hab; rw [dif_pos haN, dif_neg (by grind)] at hab
        simp at hab
        have hin : (g.symm ⟨a, haN⟩:A) ∈ (Y \ X:Set A) := by simp
        have hnotin : (f' (b - N):A) ∉ (Y \ X:Set A) := by simp
        rw [hab] at hin
        exact absurd hin hnotin
      · unfold l at hab; rw [dif_neg (by grind), dif_pos hbN] at hab
        simp at hab
        have hin : (g.symm ⟨b, hbN⟩:A) ∈ (Y \ X:Set A) := by simp
        have hnotin : (f' (a - N):A) ∉ (Y \ X:Set A) := by simp
        rw [← hab] at hin
        exact absurd hin hnotin
      · unfold l at hab; rw [dif_neg (by grind), dif_neg (by grind)] at hab
        simp at hab
        have hsub := Subtype.val_injective hab
        simp at hsub; grind
    have hlsurj : Function.Surjective l := by
      intro ⟨b, hb⟩
      rcases hb with hX | hXY
      · use f ⟨b, hX⟩ + N
        unfold l f'; simp
      · use g ⟨b, hXY⟩
        unfold l; simp
    set l' := (Equiv.ofBijective l ⟨hlinj, hlsurj⟩).symm
    use l'; exact Equiv.bijective l'

/-- Corollary 8.1.11 --/
theorem Int.countablyInfinite : CountablyInfinite ℤ := by
  -- This proof is written to follow the structure of the original text.
  have h1 : CountablyInfinite {n:ℤ | n ≥ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    . intro h; use n.toNat; simp [h]
  have h2 : CountablyInfinite {n:ℤ | n ≤ 0} := by
    rw [CountablyInfinite.iff_image_inj]
    use ⟨ (-↑·:ℕ → ℤ), by intro _ _ _; simp_all ⟩
    ext n; simp; refine ⟨ ?_, by aesop ⟩
    intro h; use (-n).toNat; simp [h]
  have : CountablyInfinite (.univ : Set ℤ) := by
    convert h1.union h2; ext; simp; omega
  rwa [←CountablyInfinite.equiv (.univ _)]

/-- Lemma 8.1.12 -/
theorem CountablyInfinite.lower_diag : CountablyInfinite { n : ℕ × ℕ | n.2 ≤ n.1 } := by
  -- This proof is written to follow the structure of the original text.
  let A := { n : ℕ × ℕ | n.2 ≤ n.1 }
  let a : ℕ → ℕ := fun n ↦ ∑ m ∈ .range (n+1), m
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    induction' n with k ih
    · unfold a; simp
      rw [Finset.sum_range_succ]; grind
    · unfold a at ih ⊢
      conv_lhs => rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      grind
  let f : A → ℕ := fun ⟨ (n, m), _ ⟩ ↦ a n + m
  have hf : Function.Injective f := by
    rintro ⟨ ⟨ n, m ⟩, hnm ⟩ ⟨ ⟨ n',m'⟩, hnm' ⟩ h
    simp [A,f] at hnm hnm' ⊢ h
    obtain hnn' | rfl | hnn' := lt_trichotomy n n'
    . have : a n' + m' > a n + m := by calc
        _ ≥ a n' := by linarith
        _ ≥ a (n+1) := ha.monotone (by linarith)
        _ = a n + (n + 1) := Finset.sum_range_succ id _
        _ > a n + m := by linarith
      linarith
    . simpa using h
    have : a n + m > a n' + m' := by calc
        _ ≥ a n := by linarith
        _ ≥ a (n'+1) := ha.monotone (by linarith)
        _ = a n' + (n' + 1) := Finset.sum_range_succ id _
        _ > a n' + m' := by linarith
    linarith
  let f' : A → f '' .univ := fun p ↦ ⟨ f p, by aesop ⟩
  have hf' : Function.Bijective f' := by
    constructor
    . intro p q hpq; simp [f'] at hpq; solve_by_elim
    intro ⟨ l, hl ⟩; simp at hl
    obtain ⟨ n, m, q, rfl ⟩ := hl; use ⟨ (n, m), q ⟩
  have : AtMostCountable A := by rw [AtMostCountable.equiv ⟨ _, hf' ⟩]; apply Nat.atMostCountable_subset
  have hfin : ¬ Finite A := by
    intro hfin
    have hinfin : Infinite A := by
      apply Set.infinite_coe_iff.mpr
      apply Set.Infinite.mono (s:= Set.range fun n => (n, 0))
      · intro y hy
        unfold A
        simp; grind
      · refine (Set.infinite_range_iff ?_).mpr ?_
        · intro a b hab
          simp at hab; exact hab
        · exact instInfiniteNat
    exact not_finite A
  simp [AtMostCountable] at this; tauto

/-- Corollary 8.1.13 -/
theorem CountablyInfinite.prod_nat : CountablyInfinite (ℕ × ℕ) := by
  have upper_diag : CountablyInfinite { n : ℕ × ℕ | n.1 ≤ n.2 } := by
    refine (equiv ⟨ fun ⟨ (n, m), _ ⟩ ↦ ⟨ (m, n), by aesop ⟩, ?_, ?_ ⟩).mp lower_diag
    . intro ⟨ (_, _), _ ⟩ ⟨ (_, _), _ ⟩ _; aesop
    intro ⟨ (n, m), _ ⟩; use ⟨ (m, n), by aesop ⟩
  have : CountablyInfinite (.univ : Set (ℕ × ℕ)) := by
    convert union lower_diag upper_diag; ext ⟨ n, m ⟩; simp; omega
  exact (equiv (.univ _)).mp this


#check CountablyInfinite.equiv
#check EqualCard -- ∃ f : X → Y, Function.Bijective f
/-- Corollary 8.1.14 / Exercise 8.1.8 -/
theorem CountablyInfinite.prod {X Y:Type} (hX: CountablyInfinite X) (hY: CountablyInfinite Y) :
  CountablyInfinite (X × Y) := by
  suffices hcard : EqualCard (X × Y) (ℕ × ℕ) by
    have hprod := CountablyInfinite.prod_nat
    exact (equiv hcard).mpr hprod
  choose g hg using hX
  choose f hf using hY
  use fun (x, y) => (g x, f y)
  simp
  constructor
  · intro (x₁, y₁) (x₂, y₂) hxy; simp at hxy ⊢
    constructor
    · exact hg.injective hxy.1
    · exact hf.injective hxy.2
  · intro (x, y)
    choose x' hx' using hg.surjective x
    choose y' hy' using hf.surjective y
    use (x', y'); simp; grind


/-- Corollary 8.1.15 -/
theorem Rat.countablyInfinite : CountablyInfinite ℚ := by
  -- This proof is written to follow the structure of the original text.
  have : CountablyInfinite { n:ℤ | n ≠ 0 } := by
    have hatmost : AtMostCountable  { n:ℤ | n ≠ 0 } := by
      apply AtMostCountable.subset (by left; exact Int.countablyInfinite)
    rcases hatmost with hcountable | hfinite
    · exact hcountable
    · exfalso
      have hnonempty : { n:ℤ | n ≠ 0 }.Nonempty := by use 1; simp
      have hbounded := Set.exists_max_image _ id hfinite hnonempty
      choose B hB0 hbdd using hbounded
      contrapose! hbdd
      by_cases! hB : B ≤ 0
      · use 1; constructor <;> grind
      · use (B+1); constructor <;> grind
  apply Int.countablyInfinite.prod at this
  let f : ℤ × { n:ℤ | n ≠ 0 } → ℚ := fun (a,b) ↦ (a/b:ℚ)
  replace := AtMostCountable.image this f
  have h : f '' .univ = .univ := by
    ext x
    simp
    use x.num, x.den
    unfold f; simp
    exact Rat.num_div_den x
  rcases this with h1 | h2
  · have h1' : CountablyInfinite (Set.univ : Set ℚ) := h ▸ h1
    rwa [CountablyInfinite.equiv (EqualCard.univ _)] at h1'
  · have h2' : Finite (Set.univ : Set ℚ) := h ▸ h2
    rw [Set.finite_coe_iff, Set.finite_univ_iff] at h2'
    exact absurd h2' (not_finite_iff_infinite.mpr inferInstance)

open Classical in
/-- Exercise 8.1.1 -/
example (X: Type) : Infinite X ↔ ∃ Y : Set X, Y ≠ .univ ∧ EqualCard Y X := by
  constructor
  · intro hinfinite
    set g := Infinite.natEmbedding X
    use Set.univ \ {g 0}
    constructor
    · simp
    · set f : (Set.univ \ {g 0} : Set X) → X := fun ⟨x, _⟩ => if h : ∃ n, g (n + 1) = x then g h.choose else x
      use f; constructor
      · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
        unfold f at hab; simp at hab
        split_ifs at hab with hl hr hm
        · have := g.injective hab
          have := hl.choose_spec
          have := hr.choose_spec
          grind
        · simp; exfalso
          rcases Nat.eq_zero_or_pos hl.choose with h0 | hpos
          · grind
          · rw [← hab] at hr
            contrapose hr
            use hl.choose - 1
            simp; grind
        · simp; exfalso
          rcases Nat.eq_zero_or_pos hm.choose with h0 | hpos
          · grind
          · rw [hab] at hl
            contrapose hl
            use hm.choose - 1
            simp; grind
        · simp; exact hab
      · intro a
        by_cases! hexist : ∃ n, g n = a
        · choose n hn using hexist
          rw [← hn]
          use ⟨g (n+1), ?deferredMembershipProof⟩
          · unfold f; simp
          · constructor
            · simp
            · grind
        · use ⟨a, by simp; grind⟩
          unfold f
          simp only []
          rw [dif_neg (by grind)]
  · intro hexist
    choose Y hYnotuniv hequiv using hexist
    choose g hg using hequiv
    by_contra! hfinite
    haveI hfinX : Fintype X := Fintype.ofFinite X
    haveI hfinY : Fintype Y := Fintype.ofFinite Y
    have heq := Fintype.card_of_bijective hg
    have hlt : Fintype.card Y < Fintype.card X := by
      rw [← Set.toFinset_card Y, ← Finset.card_univ]
      apply Finset.card_lt_card
      rw [Finset.ssubset_univ_iff]
      intro h'
      apply hYnotuniv
      exact Set.toFinset_eq_univ.mp h'
    grind

/-- Exercise 8.1.6 -/
theorem atMostCountable_iff_injective (A: Type) : AtMostCountable A ↔ ∃ f : A → ℕ, Function.Injective f := by
  constructor
  · intro hatmost
    rcases hatmost with hinfinite | hfinite
    · choose g hg using hinfinite
      use g
      exact hg.injective
    · have hequiv : A ≃ Fin (Nat.card A) := by exact Finite.equivFin A
      set f : A → ℕ := fun a => (hequiv a).val
      use f
      intro a b hab
      unfold f at hab
      have := Fin.val_injective hab
      simp at this; exact this
  · intro hexist
    choose f hf using hexist
    have hbij : A ≃ Set.range f := Equiv.ofInjective f hf
    have hXY : EqualCard A (Set.range f) := by
      use hbij.toFun
      exact hbij.bijective
    suffices AtMostCountable (Set.range f) by
      exact (AtMostCountable.equiv hXY).mpr this
    apply Nat.atMostCountable_subset

/-- Exercise 8.1.9 -/
theorem atMostCountable_of_iUnion_atMostCountable {I X:Type} (hI: AtMostCountable I) (A: I → Set X) (hA: ∀ i, AtMostCountable (A i)) :
  AtMostCountable (⋃ i, A i) := by
  -- choosing the i-th set.
  choose ι hι using (atMostCountable_iff_injective _).mp hI
  choose γ hγ using fun i => (atMostCountable_iff_injective _).mp (hA i)
  let F : (Σ i, ((A i):Set X)) → ℕ × ℕ := fun s  => (ι s.1, γ s.1 s.2)
  have hFinj : Function.Injective F := by
    intro ⟨i, x⟩ ⟨j, y⟩ h
    unfold F at h
    simp at h
    obtain ⟨hij, hxy⟩ := h
    have hi : i = j := hι hij
    subst hi
    have hx := hγ i hxy
    subst hx
    rfl
  choose G hG using CountablyInfinite.prod_nat
  set K :  (Σ i, ((A i):Set X)) → ℕ := fun s => (G ∘ F) s
  have hKinj : Function.Injective K := by
    exact Function.Injective.comp hG.injective hFinj
  have hatmost := (atMostCountable_iff_injective _).mpr ⟨K, hKinj⟩
  convert AtMostCountable.image' hatmost (fun s => s.2.val)
  ext x; simp


/-- Exercise 8.1.10.  Note the lack of the `noncomputable` keyword in the {lit}`abbrev`. -/

def fusc : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | (n+2) => if (n + 2) % 2 = 0
    then fusc ((n + 2) / 2)
    else fusc ((n + 2) / 2) + fusc ((n + 2) / 2 + 1)

@[simp] lemma fusc_zero : fusc 0 = 0 := by unfold fusc; grind
@[simp] lemma fusc_one : fusc 1 = 1 := by unfold fusc; grind
@[simp] lemma fusc_two : fusc 2 = 1 := by
  unfold fusc
  rw [if_pos (by grind)]
  norm_num

lemma fusc_even {n:ℕ} : fusc (2 * n) = fusc n := by
  by_cases! hn0 : n = 0
  · rw [hn0]
  · have heq : 2 * n = (2 * n - 2) + 2 := by grind
    have heven : ((2 * n - 2) + 2) % 2 = 0 := by grind
    rw [heq]
    conv_lhs => unfold fusc
    rw [if_pos heven]
    congr 1
    grind

lemma fusc_odd {n:ℕ} : fusc (2 * n + 1) = fusc n + fusc (n + 1) := by
  by_cases! hn0 : n = 0
  · rw [hn0]
    simp
  · have heq : 2 * n + 1 = (2 * n - 1) + 2 := by grind
    have hodd : (2 * n - 1) + 2 ≠ 0 := by grind
    rw [heq]
    conv_lhs => unfold fusc
    rw [if_neg (by grind)]
    congr <;> grind

lemma fusc_pos {n:ℕ} (hn : n ≥ 1) : fusc n > 0 := by
  induction' n using Nat.strong_induction_on with k ih
  rcases eq_or_lt_of_le hn with heq | hlt
  · rw [← heq]
    unfold fusc; simp
  · rcases Nat.even_or_odd k with ⟨d, hd⟩ | ⟨d, hd⟩
    · rw [hd, ← two_mul, fusc_even]
      have hdltk : d < k := by grind
      have hdgt1 : d ≥ 1 := by grind
      specialize ih (m:=d) hdltk hdgt1
      exact ih
    · rw [hd, fusc_odd]
      have ihd := ih (m:=d) (by grind) (by grind)
      have ihd1 := ih (m:=(d+1)) (by grind) (by grind)
      linarith

lemma fusc_coprime {n:ℕ} : Nat.Coprime (fusc n) (fusc (n+1)) := by
  induction' n using Nat.strong_induction_on with k ih
  · rcases Nat.even_or_odd k with ⟨d, hd⟩ | ⟨d, hd⟩
    · rcases eq_zero_or_pos k with rfl | hk
      · simp
      · rw [hd, ← two_mul, fusc_even, fusc_odd]
        specialize ih (m:=d) (by grind)
        exact Nat.coprime_self_add_right.mpr ih
    · rw [hd, fusc_odd]
      have : (2 * d + 1 + 1) = 2 * (d + 1) := by grind
      rw [this, fusc_even]
      specialize ih (m:=d) (by grind)
      exact Nat.coprime_add_self_left.mpr ih

lemma fusc_even_lt {n:ℕ} (hn : n ≥ 1) : fusc (2 * n) < fusc (2 * n + 1) := by
  rw [fusc_even, fusc_odd]
  suffices fusc (n + 1) > 0 by linarith
  exact fusc_pos (n:=n+1) (by linarith)

lemma fusc_odd_gt {n:ℕ} (hn : n ≥ 1) : fusc (2 * n + 1) > fusc (2 * (n+1)) := by
  rw [fusc_even, fusc_odd]
  suffices fusc n > 0 by linarith
  exact fusc_pos hn

lemma exists_even_of_lt {n:ℕ} (hn : n ≥ 2) (hlt : fusc n < fusc (n+1)) :
  ∃ k ≥ 1, n = 2 * k := by
  rcases Nat.even_or_odd n with ⟨d, hd⟩ | ⟨d, hd⟩
  · use d; grind
  · have hgt := fusc_odd_gt (n:=d) (by grind)
    have heq : 2 * (d + 1) = n + 1 := by grind
    rw [← hd, heq] at hgt
    linarith

lemma exists_odd_of_gt {n:ℕ} (hn : n ≥ 2) (hgt : fusc n > fusc (n+1)) :
  ∃ k ≥ 1, n = 2 * k + 1 := by
  rcases Nat.even_or_odd n with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hlt := fusc_even_lt (n:=d) (by grind)
    rw [← two_mul] at hd
    rw [← hd] at hlt
    linarith
  · use d; grind

lemma fusc_succ_ne {n:ℕ} (hn : n ≥ 2) : fusc n ≠ fusc (n+1) := by
  rcases Nat.even_or_odd n with ⟨d, hd⟩ | ⟨d, hd⟩
  · have hlt := fusc_even_lt (n:=d) (by grind)
    grind
  · have hgt := fusc_odd_gt (n:=d) (by grind)
    grind


lemma fusc_pair_one {n:ℕ} (h : fusc n = 1) (hsucc : fusc (n+1) = 1) : n = 1 := by
  rcases eq_zero_or_pos n with h0 | hpos
  · rw [h0, fusc_zero] at h
    simp at h
  · have hn : n ≥ 1 := by grind
    rcases eq_or_lt_of_le hn with heq | hlt
    · exact heq.symm
    · have hneq := fusc_succ_ne (n:=n) (by grind)
      rw [h] at hneq
      exact absurd hsucc hneq.symm

lemma fusc_zero_eq {n:ℕ} (h : fusc n = 0) : n = 0 := by
  rcases eq_zero_or_pos n with h0 | hpos
  · exact h0
  · have hn : n ≥ 1 := by grind
    have h' := fusc_pos hn
    linarith

lemma fusc_pair_injective {m n : ℕ} (h : fusc n = fusc m) (hsucc : fusc (n+1) = fusc (m+1)) :
  m = n := by
  induction' m using Nat.strong_induction_on with k ih generalizing n
  rcases eq_zero_or_pos k with rfl | hkpos <;>
  rcases eq_zero_or_pos n with rfl | hnpos
  · rfl
  · simp at h hsucc
    exact (fusc_zero_eq h).symm
  · simp at h hsucc
    exact fusc_zero_eq h.symm
  · have hn : n ≥ 1 := by grind
    have hk : k ≥ 1 := by grind
    rcases eq_or_lt_of_le hn with hneq | hnlt <;> rcases eq_or_lt_of_le hk with hkeq | hklt
    · linarith
    · grind
    · rw [← hkeq] at h hsucc; simp at h hsucc
      have := fusc_pair_one h hsucc
      linarith
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rcases Nat.even_or_odd n with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [← two_mul] at hj hi
        rw [hj, hi] at h hsucc
        rw [fusc_even, fusc_even] at h
        rw [fusc_odd, fusc_odd] at hsucc
        have hsucc' : fusc (i+1) = fusc (j+1) := by linarith
        specialize ih (m:=j) (by grind) h hsucc'
        grind
      · rw [← two_mul] at hj
        rw [hj, hi] at h hsucc
        rw [fusc_even, fusc_odd] at h
        have hieq : 2 * i + 1 + 1 = 2 * (i + 1) := by grind
        rw [hieq, fusc_even, fusc_odd] at hsucc
        have hj0 : fusc (j+1) = 0 := by grind
        have hj0' := fusc_pos (n:=j+1) (by grind)
        linarith
      · rw [← two_mul] at hi
        rw [hj, hi] at h hsucc
        rw [fusc_even, fusc_odd] at h
        have hjeq : 2 * j + 1 + 1 = 2 * (j + 1) := by grind
        rw [hjeq, fusc_even, fusc_odd] at hsucc
        have hj0 : fusc (i+1) = 0 := by grind
        have hj0' := fusc_pos (n:=i+1) (by grind)
        linarith
      · rw [hj, hi] at h hsucc
        rw [fusc_odd, fusc_odd] at h
        have hjeq : 2 * j + 1 + 1 = 2 * (j + 1) := by grind
        have hieq : 2 * i + 1 + 1 = 2 * (i + 1) := by grind
        rw [hjeq, hieq, fusc_even, fusc_even] at hsucc
        have h' : fusc i = fusc j := by linarith
        specialize ih (m:=j) (by grind) h' hsucc
        grind

theorem fusc_pair_surjective {q r : ℕ} (hr : r > 0) (h : Nat.Coprime q r) :
  ∃ n, fusc n = q ∧ fusc (n+1) = r := by
  induction' hsum : (q + r) using Nat.strong_induction_on with s ih generalizing q r
  rcases lt_trichotomy q r with hlt | heq | hgt
  · rcases eq_zero_or_pos q with rfl | hqpos
    · have hr : r = 1 := by exact (Nat.coprime_zero_left r).mp h
      subst hr
      use 0; simp
    · have hrs : r < s := by grind
      have hrq : r - q ≥ 1 := by grind
      have h' : Nat.Coprime q (r-q) := by exact (Nat.coprime_sub_self_right (by grind)).mpr h
      specialize ih r hrs hrq h' (by grind)
      choose k hk hk' using ih
      use 2 * k; constructor
      · rw [fusc_even]; exact hk
      · rw [fusc_odd]; grind
  · have hq1 : q = 1 := by grind
    have hr1 : r = 1 := by grind
    rw [hq1, hr1]
    use 1; simp
  · rcases eq_zero_or_pos r with rfl | hqpos
    · linarith
    · have hqs : q < s := by grind
      have h' : (q - r).Coprime r := by
        refine Nat.coprime_comm.mp ?_
        refine (Nat.coprime_sub_self_right ?_).mpr ?_
        · grind
        · exact Nat.coprime_comm.mp h
      specialize ih q (q:=q-r) (r:=r) hqs hr h' (by grind)
      choose k hk hk' using ih
      use 2 * k + 1; constructor
      · rw [fusc_odd]; grind
      · have : 2 * k + 1 + 1 = 2 * (k+1) := by grind
        rw [this, fusc_even]; grind

-- this only covers POSITIVE rationals
def calkinwilf : ℕ → ℚ := fun n => fusc n / fusc (n+1)

lemma calkinwilf_pos {n:ℕ} (hn : n > 0): calkinwilf n > 0 := by
  unfold calkinwilf
  have hnp := fusc_pos (n:=n) (by grind)
  have hnp' := fusc_pos (n:=n+1) (by grind)
  apply div_pos
  · exact_mod_cast hnp
  · exact_mod_cast hnp'

lemma calkinwilf_injective {m n :ℕ} (h: calkinwilf m = calkinwilf n) : m = n := by
  unfold calkinwilf at h
  have hcross : (fusc m : ℚ) * (fusc (n + 1) : ℚ) = (fusc n : ℚ) * (fusc (m + 1) : ℚ) := by
    rw [div_eq_div_iff] at h
    · grind
    · have := fusc_pos (n:=m+1) (by grind)
      norm_cast; grind
    · have := fusc_pos (n:=n+1) (by grind)
      norm_cast; grind
  norm_cast at hcross
  have hcopm := fusc_coprime (n:=m)
  have hcopn := fusc_coprime (n:=n)
  have h_dvd_prod1 : fusc m ∣ fusc n * fusc (m + 1) := by
    rw [← hcross]
    exact dvd_mul_right (fusc m) (fusc (n + 1))
  have h_dvd1 : fusc m ∣ fusc n :=
    Nat.Coprime.dvd_of_dvd_mul_right hcopm h_dvd_prod1
  have h_dvd_prod2 : fusc n ∣ fusc m * fusc (n + 1) := by
    rw [hcross]; exact dvd_mul_right (fusc n) (fusc (m + 1))
  have h_dvd2 : fusc n ∣ fusc m :=
    Nat.Coprime.dvd_of_dvd_mul_right hcopn h_dvd_prod2
  have h_num : fusc m = fusc n := Nat.dvd_antisymm h_dvd1 h_dvd2
  rcases eq_zero_or_pos (fusc n) with hfnzero | hfnpos
  · rw [hfnzero] at h_num
    have h1 := fusc_zero_eq hfnzero
    have h2 := fusc_zero_eq h_num
    grind
  · have h_denom : fusc (m+1) = fusc (n+1) := by
      rw [h_num] at hcross
      simp at hcross
      rcases hcross with heq | h0
      · exact heq.symm
      · linarith
    exact fusc_pair_injective h_num.symm h_denom.symm

lemma calkinwilf_surjective (q : ℚ) (hq : q > 0) : ∃ n ≥ 1, calkinwilf n = q := by
  have hqdenpos : q.den ≥ 1 := by exact Rat.den_pos q
  have hqnumpos : q.num > 0 := by exact Rat.num_pos.mpr hq
  let n := q.num.natAbs
  have h_num_nat_eq : (n : ℤ) = q.num := Int.natAbs_of_nonneg (by grind)
  have h_num_pos : n ≥ 1 := by omega
  have hcoprime := q.reduced
  choose k hk1 hk2 using fusc_pair_surjective hqdenpos hcoprime
  use k; constructor
  · by_contra! h'
    have hk0 : k = 0 := by grind
    rw [hk0, fusc_zero] at hk1
    grind
  · unfold calkinwilf
    rw [hk1, hk2]
    simp
    have h_nonneg : q.num ≥ 0 := by
      have h_num_pos : q.num > 0 := by exact Rat.num_pos.mpr hq
      omega
    rw [abs_of_nonneg (by exact_mod_cast h_nonneg)]
    exact Rat.num_div_den q


abbrev explicit_bijection : ℕ → ℚ :=
  -- wow this took so damn long to write
  fun n =>
    if n == 0 then 0
    else if n % 2 == 0 then calkinwilf (n / 2)
    else -calkinwilf ((n + 1) / 2)

lemma explicit_bijection_zero : explicit_bijection 0 = 0:= by simp

lemma explicit_bijection_ne_zero {n:ℕ} (hn : n > 0) : explicit_bijection n ≠ 0 := by
  unfold explicit_bijection
  split_ifs with h1 h2
  · simp at h1; linarith
  · have : n / 2 > 0 := by grind
    linarith [calkinwilf_pos this]
  · have : ((n + 1) / 2) > 0 := by grind
    linarith [calkinwilf_pos this]

theorem explicit_bijection_spec : Function.Bijective explicit_bijection := by
  constructor
  · intro a b hab
    rcases eq_zero_or_pos a with ha0 | hapos <;> rcases eq_zero_or_pos b with hb0 | hbpos
    · grind
    · rw [ha0, explicit_bijection_zero] at hab
      have hneq := explicit_bijection_ne_zero hbpos
      exact absurd hab.symm hneq
    · rw [hb0, explicit_bijection_zero] at hab
      have hneq := explicit_bijection_ne_zero hapos
      exact absurd hab hneq
    · rcases Nat.even_or_odd a with ⟨d, hd⟩ | ⟨d, hd⟩ <;> rcases Nat.even_or_odd b with ⟨k, hk⟩ | ⟨k, hk⟩
      · have haeven : a % 2 == 0 := by grind
        have hbeven : b % 2 == 0 := by grind
        unfold explicit_bijection at hab
        conv_lhs at hab => rw [if_neg (by grind), if_pos haeven]
        conv_rhs at hab => rw [if_neg (by grind), if_pos hbeven]
        have := calkinwilf_injective hab
        grind
      · have haeven : a % 2 == 0 := by grind
        have hbodd : b % 2 != 0 := by grind
        unfold explicit_bijection at hab
        conv_lhs at hab => rw [if_neg (by grind), if_pos haeven]
        conv_rhs at hab => rw [if_neg (by grind), if_neg (by grind)]
        have hlpos := calkinwilf_pos (n:=a/2) (by grind)
        have hrpos := calkinwilf_pos (n:=((b + 1) / 2)) (by grind)
        linarith
      · have haodd : a % 2 != 0 := by grind
        have hbeven : b % 2 == 0 := by grind
        unfold explicit_bijection at hab
        conv_lhs at hab => rw [if_neg (by grind), if_neg (by grind)]
        conv_rhs at hab => rw [if_neg (by grind), if_pos hbeven]
        have hlpos := calkinwilf_pos (n:=((a + 1) / 2)) (by grind)
        have hrpos := calkinwilf_pos (n:=(b/2)) (by grind)
        linarith
      · have haodd : a % 2 != 0 := by grind
        have hbodd : b % 2 != 0 := by grind
        unfold explicit_bijection at hab
        conv_lhs at hab => rw [if_neg (by grind), if_neg (by grind)]
        conv_rhs at hab => rw [if_neg (by grind), if_neg (by grind)]
        simp at hab
        have := calkinwilf_injective hab
        grind
  · intro q
    rcases lt_trichotomy q 0 with hneg | h0 | hpos
    · choose n hnpos hncw using calkinwilf_surjective (q:=-q) (by grind)
      use (2 * n - 1)
      have hodd : (2 * n - 1) % 2 != 0 := by grind
      unfold explicit_bijection
      rw [if_neg (by grind), if_neg (by grind)]
      have : (2 * n - 1 + 1) / 2 = n := by omega
      rw [this, hncw]
      simp
    · use 0; rw [explicit_bijection_zero]
      exact h0.symm
    · choose n hnpos hncw using calkinwilf_surjective (q:=q) hpos
      use 2 * n
      unfold explicit_bijection
      rw [if_neg (by grind), if_pos (by grind)]
      simp; exact hncw

end Chapter8
