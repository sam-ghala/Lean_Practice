-- File to understand how to use different basis for understanding a problem
/-
1. A residual stream in a transformer is a vector in ℝ^d. What does it mean to "pick a basis" for this space, and why is the standard basis (e₁, e₂, ..., e_d) not special?

2. If a feature is a "direction in activation space," why does that implicitly involve a basis? Could you describe the same feature in a different basis?

3. Two researchers analyze the same model. One says neuron 47 is important. The other says "neuron 47 doesn't exist, it's an artifact of your basis choice." Who's right?

4. When you read out activation values like [0.3, -0.7, 0.2, ...], what are you actually looking at? What had to be chosen for those numbers to exist?

5. A feature has activation 0.8 in one basis and activation 0.0 in another basis. Is the feature "present" or not? What's actually invariant here?

6. Why is "the activations at layer 5" not the same thing as "the list of numbers at layer 5"?

7. PCA on activations gives you "principal components." In basis language, what did PCA just do?

8. If you rotate all the weights and activations in a network consistently, the network computes the same function. Why? What does this say about what's "real" versus what's basis-dependent?

9. What does it mean that the residual stream basis is "arbitrary" but the computation the network performs is not?

10. "The model stores more features than it has dimensions." Explain why this sentence only makes sense once you understand bases.

11. In superposition, features are not aligned with basis directions. What would it mean for them to be aligned? Why might a model choose not to do that?

12. If you found a basis where every feature aligned with exactly one basis vector, what would that tell you about the model?

13. "Finding interpretable directions" is a core goal of mechanistic interpretability. Translate this into basis language.

14. Why might the basis that makes *one* layer interpretable be different from the basis that makes *another* layer interpretable?

15. An attention head "reads from" and "writes to" the residual stream. What does change of basis have to do with understanding what it reads and writes?
-/

-- 3.

-- 2.
-- A feature is a direction (a vector defining an axis)
-- An activation is a point (a vector representing the current state)
-- A feature activation is a number (how much of that direction is present)
-- a feature w.r.t the origin stays the same vector

-- activation space V = ℝ^d where d = d_model, the vector where the residual stream lives
-- activation a ∈ ℝ^d representing the model's state at some layer, vecotr/point : exists indepentaly of any basis

-- feature direction (direction in space)
-- f ∈ ℝ^d, usually normalized ‖f‖ = 1
-- represents a concept; the direction itself exists indepentely of basis

-- feature activation (a number)
-- ⟨a, f⟩ = dot prod of activation with feature direction
-- similarity of how much feature f is present in activation a
-- basis independent

-- invariants:
-- activation vector a (as geometric object)
-- feature direction f (as geometric object)
-- feature activation ⟨a, f⟩ as a scalar
-- angles between vectors
-- lengths of vectors

-- changes with basis:
-- numbers used to write down a
-- numbers used to write down f
-- which index corresponds to which direction



import Mathlib.Data.Real.Basic
-- 1
def RealVec (d : Nat) := Fin d → ℝ

-- residual stream is a vector in an abstract space
-- a basis is linearly independent, span(base) = ℝ^d
-- given a basis every vector has exactly one set of coefficients, unique

-- standard basis vector
-- e_i = (0, 0, ..., 1, ..., 0) with 1 in position i
-- points along each axis
def std_basis_vec (d : Nat) (i : Fin d) : RealVec d :=
  fun j => if i = j then 1 else 0

-- standard basis
-- E = {e_1, ..., e_d}

def std_basis (d : Nat) : Fin d → RealVec d :=
  fun i => std_basis_vec d i

-- there are infineitely many valid bases
-- any linearly independent vector forms a basis

-- example: Rotated Basis in ℝ^2
-- B = {(1/√2, 1/√2), (1/√2, -1/√2)} is a valid basis
-- Same space, different "axes"

-- standard basis is convenient
-- v[i] = coefficient of e_i

-- real : the vector v, angles between vactores, lengths, subspaces
-- arbitrary : which direction is "e_1", what numbers appear in the array

-- printed activations are coordinates in standard basis
-- a different basis would gve different numbers for the same vector

-- the idea that "this neuron x turn on for cat images" means
-- "the coefficient of e_x is high for cat images"
-- model doesn't know basis, the weights implictly define meaningful directions
-- the learned meaningful directions arent probably alinged with e_1, e_2

-- superposition
-- "features" = meaningful directions the model uses
-- "neurons" = standard basis directions
-- features ≠ neurons in general

-- 1. "Pick a basis" means: choose d linearly independent vectors to serve
-- as reference directions, this determines how any vector gets described as a list of numbers
-- model computation is invariant to basis choice
-- looking at activations values are like looking at the coordinates in an arbitrary basis
-- more structure might be rotated away from that basis

-- linear independence - can I build this vector from the others
-- orthogonal - perpendicular

-- R^2
-- b_1 = (1, 0)
-- b_2 = (1, 1)
-- cannot build b_2 from b_1
-- geometric test for independence in R^2 = do they point in different directions
-- (1,0) and (2,0) = dependent
-- (1,0) and (-3,0) = dependent

-- if I have d + 1 vectors in ℝ_d, then at least one of them must be writable
-- as a combination of the others

-- < d vectors: can be independent, but won't span (not a basis)
-- = d vectors: can be independent AND span (basis)
-- > d vectors: cannot all be independent (never a basis)

-- activations = model.get_activations(input) [768]
-- print(activations[42]) print neuron 42 coords
-- this uses the standard basis

-- to explicitly find a new basis: (3 ways)
/-
pca = PCA(n_components=768)
pca.fit(activations_dataset)
new_basis = pca.components_  # shape: [768, 768]
-/
-- each row of components is a new basis vector. pca found directions of max variance
-- a basis where the first coords capture the most "spread" in the data

-- SVD of a weight matrix
/-
U, S, Vt = torch.svd(W)
-/
-- U and V are orthonormal bases, the weight matrix is a diagonal in these bases

-- SAE
/-
SAE learns a dictionary of directions
learned_directions = sae.decoder.weight  # shape: [d_model, n_features]
-/
-- trying to find a basis where coefficients are sparse

-- finding the right base reveals structure
-- standard basi: convinent for indexing
-- pca basis: captures variance, good for compression
-- eigenbasis of attention: reveals what info flows where
-- SAE directions: might capture interpretable features

-- creating a basis -> finding a rotation of space where coords mean something

-- pca finds orthonormal basis that capture maximum variance and each subsequent one is
-- perpendicular. PC@ is perpendicular to PC1, PC3 is perpendicular to PC1 and PC2

-- linear probe finds a single direction
-- direction in activation space related to a label, high score predicts yes no score predcits no
-- linear probe finds one meaningul direction, not just one vector
-- "this could be a one basis vector that has some meaning"
