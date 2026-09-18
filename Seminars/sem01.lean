/-!
# Seminar 1
Terms, types, functions and definitions
-/

/- Check types. -/

#check 0
#check (0 : Nat)
#check (0 : Int)
#check -1
#check_failure (-1 : Nat)
#check 2 + 2

-- Lean inserts a coercion Nat → Int.
#check (2 : Nat) + (2 : Int)


/- Eval terms. -/

#eval 2 + 2
#eval 1 - 3
#eval (1 : Int) - 3


/- Anonymous functions. -/

#check fun x : Nat ↦ x
#check λ x : Nat ↦ x + 2
#check (λ x : Nat ↦ x) 2
#check fun x y : Nat ↦ x + y
#check (fun x y : Nat ↦ x + y) 2
#check_failure (λ x : Nat ↦ x) (2 : Int)
#check_failure (λ x : Nat ↦ x) (λ x : Nat ↦ x)


/- Beta reduction. -/

#eval (λ x : Nat ↦ x) 2
#eval (fun x y : Nat ↦ x + y) 2 3

-- Why doesn't this make sense for #eval?
-- #eval (fun x y : Nat ↦ x + y) 2


/- Type of types. -/

#check Nat
#check Nat → Nat
#check Nat -> Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat

/- Type of types: how deep can we go? -/

#check Nat
#check Nat → Nat

#check Type
#check Type 0
#check Type 1
#check Type 2
#check (Type 2 : Type 3)
#check_failure (Type 2 : Type 4)
#check_failure Type -1

-- Can the universe level depend on an ordinary Nat?
#check_failure (fun n : Nat ↦ Type n)


/- Sorts. -/

#check Sort 1
#check Sort 0
#check Prop
#check True
#check False

#check Nat → Nat
#check Nat → Type
#check Type → Nat
#check Nat → Prop
#check Prop → Nat
#check True → True -- what?


/- Definitions. -/

def n : Nat := 42

#check n
#eval n

def m := 43
def next : Nat → Nat := λ n ↦ n + 1
def double (n : Nat) := n + n
def add (n m : Nat) := n + m
def mul (n : Nat) m := n * m

#check add
#check add 2
#eval add 2 3
#eval double n


/- Higher-order functions. -/

def doTwice (f : Nat → Nat) := λ n ↦ f (f n)

#check doTwice
#eval doTwice (add 5) m

def compose (f g : Nat → Nat) := λ n ↦ f (g n)

#check compose
#eval compose (add 5) (mul 2) n


/- Definitions and definitional equality. -/

def MyNat := Nat

-- Why doesn't this work?
-- def five? : MyNat := 5

def five : MyNat := (5 : Nat)

#check five
#eval five


/- Sections and variables. -/

section foo
  variable (x y : Nat)

  def add? := x + y

  #check add?
  #eval add? 2 3

end foo

#check add?


/- Namespaces. -/

namespace Foo
  def a := 5
  def f x := x + 7

  #check a
  #check f
end Foo

#check_failure a
#check Foo.a

open Foo

#check a
#check Foo.a

namespace Foo
  def fa := f a

  #check fa

  namespace Bar
    def ffa := f (f a)

    #check ffa
  end Bar

  #check_failure ffa
  #check Bar.ffa
end Foo

#check Bar.ffa


/- Dot notation. -/

def Nat.add' (x y : Nat) : Nat := x + y

#eval Nat.add' n m
#eval n.add' m


/- Polymorphism. -/

def idNat (x : Nat) := x
def idProp (x : Prop) := x
def idType (x : Type) := x

-- Can we write all three at once?

-- def id' x := x  -- Why not?

def id1 (x : α) := x

#check id1 5
#check id1 True
#check id1 Nat
#check id1

-- Let's make the type argument explicit.

def id2 (α : Type) (x : α) : α := x

#check id2 Nat 5
#check id2 Prop True

-- But:
#check_failure id2 Type Nat


/- Universe polymorphism. -/

def id3.{u} :
  (α : Type u) → α → α :=
  λ _ x ↦ x

#check id3 Nat 5
#check id3 Type Nat


/- Implicit arguments. -/

def id4.{u} {α : Type u} (x : α) : α := x

#check id4
#check id4 5
#check id4 Nat

#check_failure id4 Nat 5
#check @id4 Nat 5

/-!
# Exercises
-/

#check sorry

section hw
  variable (α β γ δ : Type)

  -- Define any functions with the following types.
  -- If you can't, explain why

  def ex1 : α → β → α := sorry
  def ex2 : (α → β → γ) → β → α → γ := sorry
  def ex3 : (α → (β → γ)) → (α → β) → α → γ := sorry
  def ex4 : ((α → β) → γ) → (β → γ → δ) → (α → β) → α → δ := sorry
  def ex5 : (α → β) → β → α := sorry

end hw
