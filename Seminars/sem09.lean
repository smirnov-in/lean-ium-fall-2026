import Mathlib

/-!
# Seminar 9
Mathlib: additive and multiplicative APIs. Morphisms.
-/

namespace Translation

/- Hierarchy -/

#print Mul
#print Semigroup
#print One
#print MulOneClass
#print NPow
#print Monoid
#print Inv
#print Div
#print ZPow
#print Group

/- to_additive -/

#print AddGroup

example {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ * a = b⁻¹ := by
  group

example {G : Type*} [AddGroup G] (a b : G) : -(a + b) + a = -b := by
  add_group

@[to_additive]
theorem inv_mul_cancel_left_demo {G : Type*} [Group G] (a b : G) :
    (a * b)⁻¹ * a = b⁻¹ := by
  group

#print neg_add_cancel_left_demo
#print axioms neg_add_cancel_left_demo

@[to_additive]
def twiceMul {M : Type*} [Mul M] (x : M) : M := x * x

@[to_additive (attr := simp)]
theorem twiceMul_one {M : Type*} [MulOneClass M] : twiceMul (1 : M) = 1 := by
  simp [twiceMul]

#print twiceAdd
#print twiceAdd_zero
example : twiceAdd (0 : ℤ) = 0 := by simp

/- Exponents -/

@[to_additive]
theorem pow_add_demo {M : Type*} [Monoid M] (x : M) (n m : ℕ) :
    x ^ (n + m) = x ^ n * x ^ m := by
  exact pow_add x n m

#print nsmul_add_demo

@[to_additive]
theorem iterated_pow {M : Type*} [Monoid M] (x : M) (n m : ℕ) :
    x ^ (n * m) = (x ^ n) ^ m := pow_mul x n m

#print iterated_nsmul

-- Dependencies need their own entries in the translation dictionary.
def rawSquare {M : Type*} [Mul M] (x : M) := x * x

theorem rawSquare_eq {M : Type*} [Mul M] (x : M) : rawSquare x = x * x := rfl

-- attribute [to_additive rawDouble_eq] rawSquare_eq
attribute [to_additive rawDouble] rawSquare
attribute [to_additive rawDouble_eq] rawSquare_eq

#print rawDouble_eq

/- Reuse a multiplicative theorem through a type synonym. -/

#synth Group (Multiplicative ℤ)
#synth AddMonoid (Additive ℕ)

example (x y : ℤ) :
    Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl

example {A : Type*} [AddMonoid A] (x : A) (n : ℕ) :
    (n + 1) • x = n • x + x :=
  pow_succ (Multiplicative.ofAdd x) n

end Translation

/- Bundled morphisms -/

namespace Morphisms

#print MonoidHom
#print AddMonoidHom
#print OneHom
#print MulHom
#check (ℕ →* ℕ)
#check (ℤ →+ ℤ)

#check_failure GroupHom

@[to_additive doubleHom]
def squareHom (M : Type*) [CommMonoid M] : M →* M where
  toFun x := x ^ 2
  map_one' := by simp
  map_mul' x y := mul_pow x y 2

#print doubleHom
#eval doubleHom ℤ 7

example (n : ℤ) : doubleHom ℤ n = n + n := by
  change 2 • n = n + n
  exact two_nsmul n

section
  variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

  example (f : M →* N) (x : M) : (f : M → N) x = f x := rfl

  example (f : M →* N) (x y : M) : f (x * y) = f x * f y := by
    simp

  #check MonoidHom.comp
  example (f : M →* N) (g : N →* P) (x : M) : (g.comp f) x = g (f x) := rfl

  example (f : M →* N) : f.comp (MonoidHom.id M) = f := by
    ext x
    rfl

  example (f g : M →* N) (h : ∀ x, f x = g x) : f = g := by
    ext x
    exact h x
end

section
  variable {G H : Type*} [Group G] [Group H]

  example (f : G →* H) (x : G) : f x⁻¹ = (f x)⁻¹ := map_inv f x

  example (f : G → H) (hf : ∀ x y, f (x * y) = f x * f y) : G →* H :=
    MonoidHom.mk' f hf
end


/- More structure -/

#check (ℤ →+* ℤ)
#check (ℤ ≃* ℤ)
#print RingHom
#print MulEquiv

section
  variable {R S : Type*} [Semiring R] [Semiring S]

  example (f : R →+* S) : ⇑f.toMonoidHom = (f : R → S) := rfl
  example (f : R →+* S) : ⇑f.toAddMonoidHom = (f : R → S) := rfl

  example (f : R →+* S) (x y : R) :
      f (x * y + 1) = f x * f y + 1 := by
    simp
end

example {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (x : M) :
    e.symm (e x) = x := e.symm_apply_apply x


/- One API for several types of morphisms -/

#print FunLike
#print DFunLike
#print MonoidHom.instFunLike

#print MulHomClass
#print MonoidHomClass
#print RingHomClass

#synth FunLike (ℤ →+* ℤ) ℤ ℤ
#synth MonoidHomClass (ℤ →+* ℤ) ℤ ℤ
#synth MonoidHomClass (ℤ ≃* ℤ) ℤ ℤ

#check @map_mul
#check @map_pow

@[to_additive map_repeated_add]
theorem map_powers_demo {F M N : Type*} [Monoid M] [Monoid N]
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (x : M) (n : ℕ) :
    f (x ^ n) = f x ^ n := by
  induction n with
  | zero => simp only [pow_zero, map_one]
  | succ n ih => simp only [pow_succ, map_mul, ih]

#print map_repeated_add

example {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (x : M) (n : ℕ) :
    f (x ^ n) = f x ^ n := map_powers_demo f x n

example {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (x : R) (n : ℕ) :
    f (x ^ n) = f x ^ n := map_powers_demo f x n

example {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N) (x : M) (n : ℕ) :
    e (x ^ n) = e x ^ n := map_powers_demo e x n

example {A B : Type*} [AddMonoid A] [AddMonoid B] (f : A →+ B) (x : A) (n : ℕ) :
    f (n • x) = n • f x := map_repeated_add f x n

example {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (x : R) (n : ℕ) :
    f (n • x) = n • f x := map_repeated_add f x n


/- Why injectivity is part of FunLike -/

example {F M N : Type*} [FunLike F M N] (f g : F) (h : ∀ x, f x = g x) :
    f = g := DFunLike.ext f g h

structure TaggedHom (M N : Type*) [Monoid M] [Monoid N] where
  hom : M →* N
  tag : Bool

def taggedId (b : Bool) : TaggedHom ℕ ℕ := ⟨MonoidHom.id ℕ, b⟩

example : (taggedId true).hom = (taggedId false).hom := rfl

example : taggedId true ≠ taggedId false := by
  intro h
  have := congrArg TaggedHom.tag h
  contradiction

end Morphisms

/- Quotients -/

namespace Quotients

#print Subgroup
#check MonoidHom.ker
#check MonoidHom.range

section
  variable {G H : Type*} [Group G] [Group H] (N : Subgroup G) [N.Normal]

  #synth Group (G ⧸ N)
  #check QuotientGroup.mk' N

  example (x y : G) :
      QuotientGroup.mk' N (x * y) = QuotientGroup.mk' N x * QuotientGroup.mk' N y := rfl

  example (x : G) : QuotientGroup.mk' N x = 1 ↔ x ∈ N :=
    QuotientGroup.eq_one_iff x

  variable (f : G →* H) (hN : N ≤ f.ker)
  #check QuotientGroup.lift N f hN

  example (x : G) : QuotientGroup.lift N f hN (QuotientGroup.mk' N x) = f x := rfl

  example (g : G ⧸ N →* H) (hg : g.comp (QuotientGroup.mk' N) = f) :
      g = QuotientGroup.lift N f hN := by
    ext x
    exact congrArg (λ k : G →* H ↦ k x) hg
end

section
  variable {G H : Type*} [Group G] [Group H] (f : G →* H)

  #synth f.ker.Normal

  noncomputable def firstIso : G ⧸ f.ker ≃* f.range :=
    QuotientGroup.quotientKerEquivRange f

  example (x : G) : (firstIso f (QuotientGroup.mk' f.ker x) : H) = f x := rfl

  #check QuotientGroup.quotientKerEquivOfSurjective
  #check QuotientAddGroup.quotientKerEquivRange
end

end Quotients

/-!
# Exercises
-/

section hw
  variable {G : Type*} [Group G]

  -- ⊤ denotes G as a subgroup of G
  #check (⊤ : Subgroup G)

  lemma two_cover (A B : Subgroup G) (h : ∀ x : G, x ∈ A ∨ x ∈ B) :
      A = ⊤ ∨ B = ⊤ := by
    sorry

  lemma three_cover_index_two (A B C : Subgroup G)
      (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤)
      (h : ∀ x : G, x ∈ A ∨ x ∈ B ∨ x ∈ C) : A.index = 2 := by
    sorry

  abbrev C₂ := Multiplicative (ZMod 2)

  lemma klein_three_cover :
      ∃ A B C : Subgroup (C₂ × C₂),
      A ≠ ⊤ ∧ B ≠ ⊤ ∧ C ≠ ⊤ ∧ ∀ x : C₂ × C₂, x ∈ A ∨ x ∈ B ∨ x ∈ C := by
    sorry

  theorem klein_quot_three_cover (N : Subgroup G) [N.Normal] (f : G ⧸ N ≃* C₂ × C₂) :
      ∃ A B C : Subgroup G,
      A ≠ ⊤ ∧ B ≠ ⊤ ∧ C ≠ ⊤ ∧ ∀ x : G, x ∈ A ∨ x ∈ B ∨ x ∈ C := by
    sorry

  -- It may help to first prove A ⊓ B ≤ C
  theorem three_cover_klein_quot (A B C : Subgroup G)
      (hA : A ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤) (h : ∀ x : G, x ∈ A ∨ x ∈ B ∨ x ∈ C) :
      ∃ (hN : (A ⊓ B ⊓ C).Normal),
      Nonempty (G ⧸ (A ⊓ B ⊓ C) ≃* C₂ × C₂) := by
    sorry
end hw
