import Mathlib.Tactic
import Analysis.Section_2_3

/-!
# Analysis I, Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers

In this (technical) epilogue, we show that the "Chapter 2" natural numbers {name}`Chapter2.Nat` are
isomorphic in various senses to the standard natural numbers {lean}`ℕ`.

After this epilogue, {name}`Chapter2.Nat` will be deprecated, and we will instead use the standard
natural numbers {lean}`ℕ` throughout.  In particular, one should use the full Mathlib API for {lean}`ℕ` for
all subsequent chapters, in lieu of the {name}`Chapter2.Nat` API.

Filling the sorries here requires both the {name}`Chapter2.Nat` API and the Mathlib API for the standard
natural numbers {lean}`ℕ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

In second half of this section we also give a fully axiomatic treatment of the natural numbers
via the Peano axioms. The treatment in the preceding three sections was only partially axiomatic,
because we used a specific construction {name}`Chapter2.Nat` of the natural numbers that was an inductive
type, and used that inductive type to construct a recursor.  Here, we give some exercises to show
how one can accomplish the same tasks directly from the Peano axioms, without knowing the specific
implementation of the natural numbers.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

/-- Converting a Chapter 2 natural number to a Mathlib natural number. -/
abbrev Chapter2.Nat.toNat (n : Chapter2.Nat) : ℕ := match n with
  | zero => 0
  | succ n' => n'.toNat + 1

lemma Chapter2.Nat.zero_toNat : (0 : Chapter2.Nat).toNat = 0 := rfl

lemma Chapter2.Nat.succ_toNat (n : Chapter2.Nat) : (n++).toNat = n.toNat + 1 := rfl

/-- The conversion is a bijection. Here we use the existing capability (from Section 2.1) to map
the Mathlib natural numbers to the Chapter 2 natural numbers. -/
abbrev Chapter2.Nat.equivNat : Chapter2.Nat ≃ ℕ where
  toFun := toNat
  invFun n := (n:Chapter2.Nat)
  left_inv n := by
    induction' n with n hn; rfl
    simp [hn]
    rw [succ_eq_add_one]
  right_inv n := by
    induction' n with n hn; rfl
    simp [←succ_eq_add_one, hn]

/-- The conversion preserves addition. -/
abbrev Chapter2.Nat.map_add : ∀ (n m : Nat), (n + m).toNat = n.toNat + m.toNat := by
  intro n m
  induction' n with n hn
  · rw [show zero = 0 from rfl, zero_add, _root_.Nat.zero_add]
  · rw [add_comm (n++) m]
    rw [add_succ]
    rw [add_comm m n]
    rw [Chapter2.Nat.succ_toNat]
    rw [hn]
    have : n.toNat + m.toNat + 1 = (n.toNat + 1) + m.toNat := by abel 
    rw [this]

/-- The conversion preserves multiplication. -/
abbrev Chapter2.Nat.map_mul : ∀ (n m : Nat), (n * m).toNat = n.toNat * m.toNat := by
  intro n m
  induction' n with n hn
  · change (0 * m).toNat = 0 * m.toNat
    rw [zero_mul, _root_.Nat.zero_mul]
  · rw [succ_mul]
    rw [Chapter2.Nat.map_add]
    rw [hn]
    rw [Chapter2.Nat.succ_toNat]
    rw [_root_.Nat.add_mul (n.toNat) 1 (m.toNat)]
    rw [_root_.Nat.one_mul]

/-- The conversion preserves order. -/
abbrev Chapter2.Nat.map_le_map_iff : ∀ {n m : Nat}, n.toNat ≤ m.toNat ↔ n ≤ m := by
  intro n m
  rw [le_iff_exists_add]
  -- Bridge Chapter2's ≤ to its additive definition (the ∃ a, m = n + a)
  rw [Chapter2.Nat.le_iff]
  constructor 
  · intro h 
    obtain ⟨dmath, hdmath⟩ := h 
    let a := equivNat.symm dmath 
    use a 
    apply equivNat.injective 
    change m.toNat = (n + a).toNat
    rw [Chapter2.Nat.map_add]
    have ha_eq : a.toNat = dmath := by
      exact equivNat.right_inv dmath
    rw [ha_eq]
    exact hdmath
  · intro hchpt2
    obtain ⟨a, ha⟩ := hchpt2
    use a.toNat 
    rw [← Chapter2.Nat.map_add]
    rw [ha]

abbrev Chapter2.Nat.equivNat_ordered_ring : Chapter2.Nat ≃+*o ℕ where
  toEquiv := equivNat
  map_add' := map_add
  map_mul' := map_mul
  map_le_map_iff' := map_le_map_iff

/-- The conversion preserves exponentiation. -/
lemma Chapter2.Nat.pow_eq_pow (n m : Chapter2.Nat) :
    n.toNat ^ m.toNat = (n^m).toNat := by
  induction' m with m ih
  · rw [Chapter2.Nat.zero_toNat]
    change n.toNat ^ 0 = (n ^ 0).toNat
    rw [pow_zero, _root_.Nat.pow_zero]
  · rw [Chapter2.Nat.succ_toNat]
    rw [_root_.Nat.pow_succ]
    rw [ih]
    rw [Chapter2.Nat.pow_succ]
    rw [Chapter2.Nat.map_mul]

/-- The Peano axioms for an abstract type {name}`Nat` -/
@[ext]
structure PeanoAxioms where
  Nat : Type
  zero : Nat -- Axiom 2.1
  succ : Nat → Nat -- Axiom 2.2
  succ_ne : ∀ n : Nat, succ n ≠ zero -- Axiom 2.3
  succ_cancel : ∀ {n m : Nat}, succ n = succ m → n = m -- Axiom 2.4
  induction : ∀ (P : Nat → Prop),
    P zero → (∀ n : Nat, P n → P (succ n)) → ∀ n : Nat, P n -- Axiom 2.5

namespace PeanoAxioms

/-- The Chapter 2 natural numbers obey the Peano axioms. -/
def Chapter2_Nat : PeanoAxioms where
  Nat := Chapter2.Nat
  zero := Chapter2.Nat.zero
  succ := Chapter2.Nat.succ
  succ_ne := Chapter2.Nat.succ_ne
  succ_cancel := Chapter2.Nat.succ_cancel
  induction := Chapter2.Nat.induction

/-- The Mathlib natural numbers obey the Peano axioms. -/
def Mathlib_Nat : PeanoAxioms where
  Nat := ℕ
  zero := 0
  succ := Nat.succ
  succ_ne := Nat.succ_ne_zero
  succ_cancel := Nat.succ_inj.mp
  induction _ := Nat.rec

/-- One can map the Mathlib natural numbers into any other structure obeying the Peano axioms. -/
abbrev natCast (P : PeanoAxioms) : ℕ → P.Nat := fun n ↦ match n with
  | Nat.zero => P.zero
  | Nat.succ n => P.succ (natCast P n)

/-- One can start the proof here with {syntax tactic}`unfold Function.Injective`, although it is not strictly necessary. -/
theorem natCast_injective (P : PeanoAxioms) : Function.Injective P.natCast := by
  intro x y hxy
  revert y hxy
  induction x with
  | zero => 
    intro y h
    cases y with
    | zero => rfl
    | succ y' => exact (P.succ_ne _ h.symm).elim
  | succ x' ih => 
    intro y h
    cases y with
    | zero => exact (P.succ_ne _ h).elim
    | succ y' => 
      have hin : P.natCast x' = P.natCast y' := P.succ_cancel h
      have heq : x' = y' := ih hin
      rw [heq]
      

/-- One can start the proof here with {syntax tactic}`unfold Function.Surjective`, although it is not strictly necessary. -/
theorem natCast_surjective (P : PeanoAxioms) : Function.Surjective P.natCast := by
  unfold Function.Surjective
  intro b
  apply P.induction (n := b)
  · use 0
  · intro n hn 
    obtain ⟨z, hz⟩ := hn 
    use Nat.succ z
    dsimp only [natCast]
    rw [hz]

/-- The notion of an equivalence between two structures obeying the Peano axioms.
    The symbol {kw (of := «term_≃_»)}`≃` is an alias for Mathlib's {name}`Equiv` class; for instance {lean}`P.Nat ≃ Q.Nat` is
    an alias for {lean}`_root_.Equiv P.Nat Q.Nat`. -/
class Equiv (P Q : PeanoAxioms) where
  equiv : P.Nat ≃ Q.Nat
  equiv_zero : equiv P.zero = Q.zero
  equiv_succ : ∀ n : P.Nat, equiv (P.succ n) = Q.succ (equiv n)

/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.symm {P Q: PeanoAxioms} (e : Equiv P Q) : Equiv Q P where
  equiv := e.equiv.symm
  equiv_zero := by
    rw [← e.equiv_zero]
    exact e.equiv.left_inv P.zero    
  equiv_succ n := by 
    apply e.equiv.injective 
    rw [e.equiv.apply_symm_apply]
    rw [e.equiv_succ]
    rw [e.equiv.apply_symm_apply]


/-- This exercise will require application of Mathlib's API for the {name}`Equiv` class.
    Some of this API can be invoked automatically via the {tactic}`simp` tactic. -/
abbrev Equiv.trans {P Q R: PeanoAxioms} (equiv1 : Equiv P Q) (equiv2 : Equiv Q R) : Equiv P R where
  equiv := equiv1.equiv.trans equiv2.equiv
  equiv_zero := by 
    change equiv2.equiv (equiv1.equiv P.zero) = R.zero
    rw [equiv1.equiv_zero]
    rw [equiv2.equiv_zero]
  equiv_succ n := by 
    change equiv2.equiv (equiv1.equiv (P.succ n)) = R.succ (equiv2.equiv (equiv1.equiv n))
    rw [equiv1.equiv_succ]
    rw [equiv2.equiv_succ]
    

/-- Useful Mathlib tools for inverting bijections include {name}`Function.surjInv` and {name}`Function.invFun`. -/
noncomputable abbrev Equiv.fromNat (P : PeanoAxioms) : Equiv Mathlib_Nat P where
  equiv := {
    toFun := P.natCast
    invFun := Function.surjInv (natCast_surjective P)
    left_inv := by 
      intro n 
      apply natCast_injective P
      exact Function.surjInv_eq (natCast_surjective P) (P.natCast n)
    right_inv := by 
      intro n
      exact Function.surjInv_eq (natCast_surjective P) n
  }
  equiv_zero := rfl
  equiv_succ n := rfl

/-- The task here is to establish that any two structures obeying the Peano axioms are equivalent. -/
noncomputable abbrev Equiv.mk' (P Q : PeanoAxioms) : Equiv P Q := 
  Equiv.trans (Equiv.symm (Equiv.fromNat P)) (Equiv.fromNat Q)

/-- There is only one equivalence between any two structures obeying the Peano axioms. -/
theorem Equiv.uniq {P Q : PeanoAxioms} (equiv1 equiv2 : PeanoAxioms.Equiv P Q) :
    equiv1 = equiv2 := by
  obtain ⟨equiv1, equiv_zero1, equiv_succ1⟩ := equiv1
  obtain ⟨equiv2, equiv_zero2, equiv_succ2⟩ := equiv2
  congr
  ext n
  apply P.induction (n := n)
  · rw [equiv_zero1, equiv_zero2]
  · intro n' heq
    specialize equiv_succ1 n'
    specialize equiv_succ2 n'
    rw [equiv_succ1, equiv_succ2, heq]


/-- A sample result: recursion is well-defined on any structure obeying the Peano axioms-/
theorem Nat.recurse_uniq {P : PeanoAxioms} (f: P.Nat → P.Nat → P.Nat) (c: P.Nat) :
    ∃! (a: P.Nat → P.Nat), a P.zero = c ∧ ∀ n, a (P.succ n) = f n (a n) := by
  sorry
        

end PeanoAxioms
