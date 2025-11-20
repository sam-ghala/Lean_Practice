-- Chapter 4

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

-- -- -- -- -- Exercises -- -- -- -- --
-- Prove these equivalences:

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h1 : ∀ x, p x ∧ q x =>
      And.intro
        (fun x => (h1 x).left )
        (fun x => (h1 x).right))
    (fun h2 : (∀ x, p x) ∧ (∀ x, q x) =>
      (fun x => ⟨h2.left x, h2.right x⟩))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (fun h1 : (∀ x, p x → q x) =>
    (fun h2 : (∀ x, p x) =>
      fun x : α => h1 x (h2 x))) -- could be explicit in x : α

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (fun h1 : (∀ x, p x) ∨ (∀ x, q x) =>
    (fun x : α =>
      Or.elim h1
        (fun hp : ∀ x, p x => Or.inl (hp x))
        (fun hq : ∀ x, q x => Or.inr (hq x))))

-- You should also try to understand why the reverse implication is not derivable in the last example.

-- It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  (fun h1 : α =>
    Iff.intro
      (fun h2 : (∀ x : α, r) => h2 h1)
      (fun h3 : r => (fun x : α => h3)))

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h1 : (∀ x, p x ∨ r) =>
        Or.elim (em r)
        (fun hr : r => Or.inr hr)
          (fun nhr : ¬r =>
            Or.inl (fun x =>
              Or.elim (h1 x)
                (fun hpx => hpx)
                (fun hr => absurd hr nhr))))
    (fun h2 : (∀ x, p x) ∨ r =>
      (fun x =>
      Or.elim h2
        (fun hp : ∀ x, p x => Or.inl (hp x))
        (fun hr : r => Or.inr hr)))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h1 : ∀ x, r → p x =>
      (fun hr : r =>
        (fun x : α =>
          h1 x hr)))
    (fun h2 : r → ∀ x, p x =>
      (fun x : α =>
        (fun hr : r => h2 hr x)))

-- Consider the “barber paradox,” that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  Or.elim (em (shaves barber barber))
    (fun h1 : shaves barber barber => absurd h1 ((h barber).mp h1))
    (fun h2 : ¬ shaves barber barber => absurd ((h barber).mpr h2) h2)

-- Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.

def even (n : Nat) : Prop := ∃ b , n = 2 * b
def odd (n : Nat) : Prop := ∃ b , n = 2 * b + 1

def prime (n : Nat) : Prop := n > 1 ∧ ∀ x, (x ∣ n → x = 1 ∨ x = n)

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, (prime p) ∧ p > n -- for all n : Nat, there exists p : prime greater than n

def Fermat_prime (n : Nat) : Prop := (prime ((2 ^ (2 ^ n)) + 1)) -- a prime in the form of 2^(2^n) - 1

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, (Fermat_prime p) ∧ p > n
def goldbach_conjecture : Prop := ∀ n : Nat, n > 2 ∧ even n -> ∃ a : Nat, ∃ b : Nat, (prime a ∧ prime b ∧ a + b = n) -- every even integer greater than 2 is the sum of two prime numbers

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, n > 5 ∧ odd n -> ∃ a : Nat, ∃ b : Nat, ∃ c : Nat, (prime a ∧ prime b ∧ prime c ∧ a + b + c = n) -- every odd number greater than 5 is the sum of three primes

def Fermat's_last_theorem : Prop := -- no three positive integers a, b, and c satisfy the equation aⁿ + bⁿ = cⁿ for any integer value of n greater than 2
  ∀ n : Nat, n > 2 ->
    ∀ a : Nat, ∀ b : Nat, ∀ c : Nat,
      (a < 0 ∧ b < 0 ∧ c < 0) →
        (a ^ n + b ^ n ≠ c ^ n)

-- Prove as many of the identities listed in the Existential Quantifier section as you can.

-- -- -- -- -- -- -- -- --
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  (fun hr : r => ⟨a, hr⟩)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨a, hpa_and_r⟩ =>
      ⟨⟨a, hpa_and_r.left⟩, hpa_and_r.right⟩)
    (fun ⟨⟨a, hpa⟩, hr⟩ =>
      ⟨a, ⟨hpa, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, hpq⟩ =>
      Or.elim hpq
        (fun hpa : p a =>
          Or.inl ⟨a, hpa⟩)
        (fun hqa : q a =>
          Or.inr ⟨a, hqa⟩))
    (fun h_outer_or =>
      Or.elim h_outer_or
        (fun ⟨a, hpa⟩ =>
          ⟨a, Or.inl hpa⟩)
        (fun ⟨a, hqa⟩ =>
          ⟨a, Or.inr hqa⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h1 : (∀ x, p x) =>
      (fun ⟨a, hna⟩ =>
        absurd (h1 a) (hna)))
    (fun h2 : ¬ (∃ x, ¬ p x) =>
      fun x =>
        byContradiction (fun hnpx =>
          h2 ⟨x, hnpx⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨w, hw⟩ =>
      (fun h_all_not =>
        absurd hw (h_all_not w)))
    (fun h1 : ¬ (∀ x, ¬ p x) =>
      byContradiction
        (fun h2 : ¬ (∃ x, p x) =>
          have h3 : ∀ x, ¬ p x :=
            (fun x =>
              (fun hp : p x =>
                absurd ⟨x, hp⟩ h2))
          absurd h3 h1))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry -- solved below
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry


-- -- -->
-- Notice that the second example and the last two examples require the assumption that there is at least one element a of type α.

-- Here are solutions to two of the more difficult ones:

open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
