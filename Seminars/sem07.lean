/-!
# Seminar 7
Axioms and computation. Quotients.
-/


/- Propositional extensionality -/

#check_failure (rfl : True = (True ∧ True))

example : True ↔ (True ∧ True) :=
  ⟨λ _ ↦ ⟨trivial, trivial⟩, λ _ ↦ trivial⟩

#print propext

theorem thm₁ {P : Prop → Prop} (h : a ↔ b) : P a ↔ P b := by
  replace h := propext h
  rw [h]

#print axioms thm₁
#print thm₁

theorem thm₂ {P : Prop → Prop} (h : a ↔ b) : P a ↔ P b := by
  rw [h]

#print axioms thm₂
#print thm₂


/- Functional extensionality -/

def f  (n : Nat) := n
def g  (n : Nat) := 0 + n
def g' (n : Nat) := n + 0

#check_failure (rfl : f = g)
#check (rfl : f = g')

theorem f_eq_g_ext (n : Nat) : f n = g n := by
  induction n <;> simp [f, g]

#check funext

theorem f_eq_g : f = g :=
  funext f_eq_g_ext

#print axioms f_eq_g

theorem f_eq_g' : f = g := by
  funext
  apply f_eq_g_ext

-- The type of all subsets of a type A
def Set (α : Type) : Type := α → Prop
def mem (a : α) (x : Set α) : Prop := x a
infix:50 (priority := high) "∈" => mem

theorem set_ext (h : ∀ a : α, a ∈ x ↔ a ∈ y) : x = y :=
  funext (λ a ↦ propext (h a))


/- Quotients -/

#print Quot

def mod7Rel (x y : Nat) : Prop := x % 7 = y % 7

#check Quot mod7Rel
#check (Quot.mk mod7Rel 4)

#print Quot.ind
#print Quot.lift

def decide_mod7Rel (x : Nat) : Bool := x % 7 = 0

theorem decide_mod7Rel_respects (a b : Nat) (h : mod7Rel a b) : decide_mod7Rel a = decide_mod7Rel b := by
  simp only [mod7Rel, decide_mod7Rel] at *
  rw [h]

#check (Quot.lift decide_mod7Rel decide_mod7Rel_respects)

example (a : Nat) :
  Quot.lift decide_mod7Rel decide_mod7Rel_respects (Quot.mk mod7Rel a) =
  decide_mod7Rel a :=
  rfl

#check (rfl : mod7Rel 4 11)
#check_failure (rfl : Quot.mk mod7Rel 4 = Quot.mk mod7Rel 11)

#print Quot.sound

theorem eq_4_11_mod7 : Quot.mk mod7Rel 4 = Quot.mk mod7Rel 11 := by
  apply Quot.sound
  rfl

#print axioms eq_4_11_mod7
#print funext

#print Setoid

instance NatMod7 : Setoid Nat where
  r := mod7Rel
  iseqv := {
    refl := by intro; rfl
    symm := by simp only [mod7Rel]; intro x y h; symm; apply h
    trans := by simp only [mod7Rel]; intro x y z h₁ h₂; apply Eq.trans h₁ h₂
  }

#check (rfl : 4 ≈ 11)

#print Quotient
#check Quotient.mk NatMod7 4


/- Choice -/

#print Nonempty

example (α : Type) : Nonempty α ↔ ∃ _ : α, True :=
  ⟨λ ⟨x⟩ ↦ ⟨x, trivial⟩, λ ⟨x, _⟩ ↦ ⟨x⟩⟩

#print Classical.choice

noncomputable def indefiniteDescription
  {p : α → Prop} (h : ∃ x : α, p x) : {x : α // p x} :=
  Classical.choice (let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩)

#print axioms indefiniteDescription

noncomputable def choose {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription h).val

theorem choose_spec {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription h).property


/- Diaconescu's theorem -/

theorem em (p : Prop) : p ∨ ¬ p :=
  let U (x : Prop) := (x =  True) ∨ p
  let V (x : Prop) := (x = False) ∨ p
  have exU : ∃ x : Prop, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x : Prop, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_spec : U u := choose_spec exU
  have v_spec : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    sorry
  have p_to_uv : p → u = v := by
    sorry
  sorry

#print axioms em
#check Classical.em
#print Classical.em
#print axioms Classical.em

theorem propComplete (p : Prop) : p = True ∨ p = False :=
  match em p with
  | .inl hp =>
    Or.inl (propext (Iff.intro (λ _ ↦ True.intro) (λ _ ↦ hp)))
  | .inr hn =>
    Or.inr (propext (Iff.intro hn False.elim))


/- Decidable -/

#print Decidable
#print Decidable.em

example : 2 + 2 ≠ 5 := by decide

#print DecidableEq

example (n m : Nat) : n = m ∨ n ≠ m := by apply Decidable.em

#print ite

def foo (n m : Nat) : Nat :=
  if n = m then 0 else n + m


/- Native evaluation -/

-- set_option maxRecDepth 5000

theorem big_list_sum : (List.range 1_001).sum = 500_500 := by
  -- decide
  decide +native

#print axioms big_list_sum
#print big_list_sum._native.decide.ax_1_1


/- sorry -/

#check sorryAx

theorem bad : False := sorry

#print axioms bad


/- Summary

Kernel primitive type constructions:
- Universes: Sort u : Sort (u + 1)
- Dependent functions: (x : α) → β x
- Inductive types and families
- Quotient types: Quot r

Import kernel principles:
- Non-cumulativity of Sorts
- Definitional proof irrelevance
- Impredicativity of Prop
- Restricted elimination from Prop

Standrad library logical axioms are:
- propext {a b : Prop} : (a ↔ b) → a = b
- Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} :
    r a b → Quot.mk r a = Quot.mk r b
- Classical.choice.{u} {α : Sort u} : Nonempty α → α

Derived principles:
- funext.{u, v} {α : Sort u} {β : α → Sort v}
    {f g : (x : α) → β x} (h : ∀ (x : α), f x = g x) : f = g
  follows from Quot.sound
- Classical.em (p : Prop) : p ∨ ¬p
  follows from propext, Quot.sound and Classical.choice

Additional axioms:
- sorryAx.{u} (α : Sort u) (synthetic : Bool) : α
- Native evaluation axioms
-/


/-!
# Exercises
-/

section hw
  noncomputable example {f : α → β} (hf : Function.Surjective f) :
      {g : β → α // Function.RightInverse g f} := by
    sorry

  def choice_from_surjective_right_inverse {α : Type}
      (h : ∀ {α β : Type}  {f : α → β}, Function.Surjective f →
          {g : β → α // Function.RightInverse g f}) :
      Nonempty α → α := by
    sorry

  /--
  info: 'choice_from_surjective_right_inverse' does not depend on any axioms
  -/
  #guard_msgs in
  #print axioms choice_from_surjective_right_inverse


  inductive step : List Bool → List Bool → Prop where
  | cancel (u v : List Bool) : step (u ++ false :: true :: v) (u ++ v)

  def B : Type := Quot step

  -- Equivalence class of empty list is 1
  instance : OfNat B 1 where
    ofNat := Quot.mk step []

  -- Lift list contactenation to B
  instance : Mul B where
    mul := sorry

  example (x y z : B) : x * y * z = x * (y * z) := by
    sorry

  example (x : B) : x * 1 = x := by
    sorry

  example (x : B) : 1 * x = x := by
    sorry

  def L : B := Quot.mk step [false]
  def R : B := Quot.mk step [true]

  example : L * R = 1 := by
    sorry

  example : R * L ≠ 1 := by
    sorry

  instance : Pow B Nat where
    pow :=
      let rec pow' b
        | 0     => 1
        | n + 1 => (pow' b n) * b
      pow'

  example (x : B) : ∃ m n : Nat, x = R ^ m * L ^ n := by
    sorry

  example (m n m' n' : Nat) :
      R ^ m * L ^ n = R ^ m' * L ^ n' →
      m = m' ∧ n = n' := by
    sorry
end hw
