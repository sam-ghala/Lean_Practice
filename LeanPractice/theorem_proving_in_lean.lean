#check 4


#check Nat → Bool
#check Nat × Bool

#check (Nat → Bool) → Bool


-- def α : Type := Nat
-- def β : Type := Nat
-- #check Prod α β


#check Type 32

#check Type 0

#check Prop
#check Type
#check Type 0

#check List
#check Prod

-- universe u

-- def F (α : Type u) : Type := Prod α α
-- #check F

-- or

def G.{v} (α : Type v) : Type v := Prod α α

#check fun (x : Nat) => x + 5
#eval (fun x : Nat => x + 5) 20

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n
#eval f 3

def g (s : String) : Bool := s.length > 0
#eval g ""

#check fun z : Nat => g (f z)

#check λ x => g (f x) -- space matters between g and (

def double (x : Nat) := x + x
#eval double 54

def double2 : Nat -> Nat :=
  λ x => x + x
#eval double2 2

def doTwice (f : Nat -> Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 3
-- def assigns a name to a definition
-- fun assigns an anonymous function "usually used immediately or passed to another function"

-- : (colon) - "has type"
-- := (colon-equals) - "is defined as"
-- => (fat arrow) - "maps to" / "gives"
-- -> (thin arrow) - "function type"

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) := x * x

#eval compose Nat Nat Nat double square 3

-- local defintions uses "let" keyword
-- The expression let a := t1; t2 is definitionally equal to
-- the result of replacing every occurrence of a in t2 by t1.
#check let y := 2 + 2; y * y
-- replace every occurrence of y in y * y with 2 + 2
#eval let y := 3 * 3; y * y

def twice_double (x : Nat) :=
  let y := x + x; y * y

#eval twice_double 2

def foo := let a := Nat; fun x : a => x + 2

-- def bar := (fun a => fun x : a => x + 2) Nat
-- def fun (a : Nat) => fun x : a => x + 2

#check let y := 2 + 2; let z := y + y; z * z -- (2+2 + 2+2) * (2+2 + 2+2)
#eval let y := 2 + 2; let z := y + y; z * z

variable (β γ α: Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose3 := g (f x)
def doTwice3 := h (h x)
def doThrice3 := h (h (h x))

#print compose3

section useful
  variable (ρ β γ : Type) -- scope hidden by section
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose_hidden := g (f x)
  def doTwice_hidden := h (h x)
  def doThrice_hidden := h (h (h x))
end useful

-- #check ρ -- scope hidden by section


-- namespaces

namespace Foo
  def a : Nat := 5
  def ff (x : Nat) : Nat := x + 7

  def fa : Nat := ff a
  def ffa : Nat := ff (ff a)

  #check a
  #check ff
  #check fa
  #check ffa
  #check Foo.fa
  end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.ff
#check Foo.fa
#check Foo.ffa
open Foo

#check a
#check ff
#check fa
#check Foo.fa

namespace a
  def m : Nat := 5
  namespace b
    def n : Nat := 4
  end b
end a

-- #check m
#check a.b.n
open a
#check m
#check b.n



inductive Vector2 (α : Type) : Nat → Type where
  | nil : Vector2 α 0
  | cons : α → Vector2 α n → Vector2 α (n + 1)

#check Vector2

namespace one
  universe u v

  def f_one (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
    ⟨a, b⟩
  #check f_one
end one


-- {} means that argument should be left implicitly for its type to be inferred
