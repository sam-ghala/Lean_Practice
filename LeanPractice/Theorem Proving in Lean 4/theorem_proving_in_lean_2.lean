-- chapter 2 dependent type theory
-- calculus of constructions, a countable hiearchy of non-cumulative universes and inductive types
-- lets find out what that means
-- 2.1
-- type theory : every expresssion has an associated type
-- a lean natural number is an arbitrary-precision unsigned integer
def b1 : Bool := true
def b2 : Bool := false

#check b1 && b2
#check b1 || b2
#eval b1 && b2
/-  Comment Block -/
-- def declares new constants in the working envionment
-- #check asks lean to report their types
-- #eval evaluates the given expression

-- we can build new types out of others, powerful
#check (0, 1.0)
#check Nat.succ 2
#eval Nat.succ 2
#check (5,9).1
#eval (5,9).2

-- \ to => → or \ r, or \ ->
-- \ times => × or \ x
-- α β γ , \ a, \ b, \ g

-- Nat.add => Nat -> Nat -> Nat => Nat -> (Nat -> Nat) => A function that takes in a natural number and another function that itself takes in a natural number that returns a natual natumber

#eval Nat.add 3 2

#check Prod Nat Nat
#check Nat × Nat

def α : Type := Nat
def β : Type := Bool
-- def F : Type → Type := List
def G : Type → Type → Type := Prod

-- #check α#check F α#check F Nat#check G α#check G α β#check G α Nat

#check List α
#check List Nat

#check Type
-- everything is a type
#check Type
#check Type 1
#check Type 4
#check Type 32 -- max
-- Book says to think of type 0 as a universe of "small" or "ordinary" types
-- Each succesive type universe n is a larger universe that contains type n-1
-- Type is an abbreviation for Type 0
-- The list is apparently infinite : "there is a Type n for every natural number"
#check Type
#check Type 0
--
universe u

def F (α : Type u) : Type u := Prod α α

#check F
-- 2.3
-- λ and fun mean the same thing
-- Creating a function from another expression is a process known as lambda abstraction.Suppose you have the variable x : α and you can construct an expression t : β, then the expression fun (x : α) => t, or, equivalently, λ (x : α) => t, is an object of type α → β. Think of this as the function from α to β which maps any value x to the value t.
