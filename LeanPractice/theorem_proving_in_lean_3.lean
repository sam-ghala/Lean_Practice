def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
-- def Implies (p q : Prop) : Prop := p → q
-- structure Proof (p : Prop) : Type where
  -- proof : p
#check Proof axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q

--------------------

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun (hpq : p ∧ q) => ⟨hpq.right, hpq.left⟩)
    --
    (fun (hqp : q ∧ p) => ⟨hqp.right, hqp.left⟩)
  -- another way to prove it ->
  -- Iff.intro
  --   (fun h : p ∧ q =>
  --    show q ∧ p from And.intro (And.right h) (And.left h))
  --   (fun h : q ∧ p =>
  --    show p ∧ q from And.intro (And.right h) (And.left h))


-- Or.elim {a b c : Prop} (h : a ∨ b) (left : a → c) (right : b → c) : c
-- Proof by cases on an Or. If a ∨ b, and both a and b imply proposition c, then c is true.
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun (hpq : p ∨ q) =>
      Or.elim hpq
        (fun p => Or.inr p)
        (fun q => Or.inl q))
    --
    (fun (hqp : q ∨ p) =>
      Or.elim hqp
        (fun q => Or.inr q)
        (fun p => Or.inl p))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (hpqr : (p ∧ q) ∧ r) => ⟨hpqr.left.left, ⟨hpqr.left.right, hpqr.right⟩⟩)
    --
    (fun (hpqr : p ∧ (q ∧ r)) => ⟨⟨hpqr.left, hpqr.right.left⟩, hpqr.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun (hpqr: (p ∨ q) ∨ r) =>
      Or.elim hpqr
        (fun (h2 : p ∨ q) =>
          Or.elim h2
            (fun hp => Or.inl hp)
            (fun hq => Or.inr (Or.inl hq)))
        (fun hr => Or.inr (Or.inr hr)))
    --
    (fun (h3 : p ∨ (q ∨ r)) =>
      Or.elim h3
        (fun hp => Or.inl (Or.inl hp))
        (fun (h4: q ∨ r) =>
          Or.elim h4
            (fun hq => Or.inl (Or.inr hq))
            (fun hr => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (fun h1 : p ∧ (q ∨ r) =>
    have hp : p := h1.left
    Or.elim (h1.right)
        (fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
  --
  (fun (h2 : (p ∧ q) ∨ (p ∧ r)) =>
    Or.elim h2
      (fun h3 : p ∧ q =>
        have hp : p := h3.left
        have hq : q := h3.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
      (fun h4 : p ∧ r =>
        have hp : p := h4.left
        have hr : r := h4.right
        show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
 Iff.intro
  (fun h1 : p ∨ (q ∧ r) =>
    Or.elim h1
      (fun hp : p => ⟨Or.inl hp, Or.inl hp⟩)
      (fun h2 : q ∧ r => show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr h2.left, Or.inr h2.right⟩))
  --
  (fun h3 : (p ∨ q) ∧ (p ∨ r) =>
    Or.elim h3.left
      (fun hp: p => Or.inl hp)
      (fun hq : q =>
        Or.elim h3.right
          (fun hp : p => Or.inl hp)
          (fun hr : r => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h1 : p → (q → r) =>
      (fun hpq : p ∧ q => h1 hpq.left hpq.right))
    --
    (fun h2 : p ∧ q → r =>
      (fun hp: p =>
        (fun hq: q => h2 ⟨hp, hq⟩)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h1 : (p ∨ q) → r =>
      ⟨(fun hp : p => h1 (Or.inl hp)), (fun hq : q => h1 (Or.inr hq))⟩)
    --
    (fun h2 : (p → r) ∧ (q → r) =>
      (fun h_or : p ∨ q =>
        Or.elim h_or
          (fun hp : p => h2.left hp)
          (fun hq : q => h2.right hq)))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h1 : ¬(p ∨ q) =>
    And.intro
      (fun hp : p => h1 (Or.inl hp))
      (fun hq : q => h1 (Or.inr hq)))
    (fun h2 : ¬p ∧ ¬q =>
      (fun hpq : p ∨ q =>
      Or.elim hpq
        (fun hp : p => h2.left hp)
        (fun hq : q => h2.right hq)))



example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
