-- focused on the finding aspect of proofs
-- SMT ("satisfiability modulo theories”)
-- automated reasoning strive for power and efficiency often at the expense of guaranteed soundness
-- in contrast, interactive theorem proving focuses on the "verification" aspect of theorem proving, requiring that every claim is supported by a proof in a suitable axiomatic foundation

-- lean is based on a version of dependent type theory
-- based on the Calculus of Constructions with inductive types, whatever that means

theorem and_commutative (p q: Prop) : p ∧ q -> q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp
