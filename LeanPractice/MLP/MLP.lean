import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
set_option linter.style.longLine false

/-
LEAN DEFINITIONS FOR NEURAL NETWORK FUNDAMENTALS
Author: Sam Ghalayini
-/

-- ═══════════════════════════════════════════════════════════════════════════
-- FUNCTION PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════

-- Additivity
-- f(a + b) = f(a) + f(b)
-- Preserves addition; one of two conditions for linearity.
def additive {α β : Type} [Add α] [Add β] (f : α → β) : Prop :=
  ∀ x y, f (x + y) = f x + f y

-- Homogeneity
-- f(c · x) = c · f(x)
-- Preserves scalar multiplication; the other condition for linearity.
def homogeneity {α β : Type} [SMul ℝ α] [SMul ℝ β] (f : α → β) : Prop :=
  ∀ (a: α) (c : ℝ), f (c • a) = c • f a

-- Zero-Preserving
-- f(0) = 0
-- Linear functions must map zero to zero.
def zero_maps {α β : Type} [Zero α] [Zero β] (f : α → β) : Prop :=
  f 0 = 0

-- Linear Function
-- additive(f) ∧ homogeneous(f)
-- The transformation performed by weight matrices (Wx).
def linear_func {α β : Type} [Add α] [Add β] [SMul ℝ α] [SMul ℝ β] (f : α → β) : Prop :=
  additive f ∧ homogeneity f

-- Affine Function
-- f(x) = L(x) + b where L is linear
-- A linear map plus translation; the complete layer transformation.
def affine_func {α β : Type} [Add α] [Add β] [SMul ℝ α] [SMul ℝ β] (f : α → β) : Prop :=
  ∃ (g : α → β) (b : β), linear_func g ∧ ∀ x, f x = g x + b

-- Non-Linear Function
-- ¬(additive(f) ∧ homogeneous(f))
-- Violates superposition; essential for network expressivity.
def non_linear_func {α β : Type} [Add α] [Add β] [SMul ℝ α] [SMul ℝ β] (f : α → β) : Prop :=
  ¬ linear_func f

-- Odd Function
-- f(-x) = -f(x)
-- Zero-centered output; examples: tanh, identity.
def odd_func {α β : Type} [Neg α] [Neg β] (f : α → β) : Prop :=
  ∀ x, f (-x) = -(f x)

-- Even Function
-- f(-x) = f(x)
-- Symmetric about y-axis; examples: x², cosine.
def even_func {α β : Type} [Neg α] (f : α → β) : Prop :=
  ∀ x, f (-x) = f x

-- Monotonic Increasing
-- x ≤ y → f(x) ≤ f(y)
-- Order-preserving; ensures larger inputs don't decrease activation.
def monotonic_inc {α β : Type} [LE α] [LE β] (f : α → β) : Prop :=
  ∀ x, ∀ y, x ≤ y → f x ≤ f y

-- Bounded Function
-- ∃M, ∀x, ‖f(x)‖ ≤ M
-- Range-constrained; prevents activations from exploding.
def bounded_func {α β : Type} [NormedAddCommGroup β] (f : α → β) : Prop :=
  ∃ M, ∀ x, ‖f x‖ ≤ M

-- Idempotent
-- f(f(x)) = f(x)
-- Applying twice equals applying once; ReLU is idempotent on ℝ⁺.
def idempotent {α : Type} (f : α → α) : Prop :=
  ∀ x, f (f x) = f x

-- Lipschitz Continuity
-- ‖f(x) - f(y)‖ ≤ K · ‖x - y‖
-- Bounds rate of change; K=1 for ReLU, prevents exploding gradients.
def lipschitz {α β : Type} [NormedAddCommGroup α] [NormedAddCommGroup β] (K : ℝ) (f : α → β) : Prop :=
  ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖

-- Composition
-- h(x) = g(f(x))
-- Connecting layers; network is composition of layer functions.
def composition {α β γ : Type} (f : α → β) : Prop :=
  ∃ (g : β → γ) (h : α → γ), ∀ x, h x = g (f x)

-- Non-Negative Function
-- ∀x, f(x) ≥ 0
-- Required for loss functions and ReLU output.
def non_neg {α β : Type} [Preorder β] [Zero β] (f : α → β) : Prop :=
  ∀ x, f x ≥ 0

-- ═══════════════════════════════════════════════════════════════════════════
-- LINEAR ALGEBRA
-- ═══════════════════════════════════════════════════════════════════════════

-- Real Vector
-- v : Fin n → ℝ
-- n-dimensional vector; core data structure for activations.
def real_vector (n : ℕ) : Type :=
  Fin n → ℝ

variable {v : real_vector 4}
#check v 7
#eval (7 : Fin 4)

-- Dot Product
-- ⟨u, v⟩ = Σᵢ uᵢvᵢ
-- Inner product implementation; core of matrix multiplication.
def dot_prod {n : ℕ} (u v : real_vector n) : ℝ :=
  ∑ i, (u i) * (v i)

-- Dot Product Symmetry
-- ⟨u, v⟩ = ⟨v, u⟩
-- Follows from commutativity of real multiplication.
def dot_sym {n : ℕ} (u v : real_vector n) : Prop :=
  dot_prod u v = dot_prod v u

-- Dot Product Linearity
-- ⟨cu + v, w⟩ = c⟨u, w⟩ + ⟨v, w⟩
-- Bilinear in both arguments.
def dot_lin {n : ℕ} (u v w : real_vector n) (c : ℝ) : Prop :=
  dot_prod (fun i => c * u i + v i) w = c * (dot_prod u w) + (dot_prod v w)

-- Dot Product Positive Definiteness
-- ⟨u, u⟩ ≥ 0 and ⟨u, u⟩ = 0 ↔ u = 0
-- Defines norm; basis for distance metrics.
def dot_pos {n : ℕ} (u : real_vector n) : Prop :=
  (dot_prod u u ≥ 0) ∧ (dot_prod u u = 0 ↔ u = (fun _ => 0))

theorem dot_prod_is_sym {n : ℕ} (u v : real_vector n) : dot_sym u v := by
  unfold dot_sym
  unfold dot_prod
  congr
  funext i
  rw [mul_comm]

theorem dot_prod_is_lin {n : ℕ} (u v w : real_vector n) (c : ℝ) : dot_lin u v w c := by
  unfold dot_lin
  unfold dot_prod
  congr
  sorry

theorem dot_prod_is_pos {n : ℕ} (u : real_vector n) : dot_pos u := sorry

-- Real Matrix
-- A : Fin m × Fin n → ℝ
-- m×n matrix; weight matrices define layer transformations.
def real_matrix (n m : ℕ) : Type :=
 (Fin n × Fin m) → ℝ

-- Matrix-Vector Multiplication
-- (Av)ᵢ = Σⱼ Aᵢⱼvⱼ
-- Core forward pass operation.
def m_v_mul {n m : ℕ} (A : real_matrix n m) (v : real_vector m) : real_vector n :=
  fun (i : Fin n) =>
    ∑ j : Fin m, A (i, j) * v j

-- Element-wise Application
-- (f ∘ v)ᵢ = f(vᵢ)
-- How activations are applied to layer outputs.
def el_wise {n : ℕ} (f : ℝ → ℝ) (v : real_vector n) : real_vector n :=
  fun (i : Fin n) => f (v i)

-- ═══════════════════════════════════════════════════════════════════════════
-- ACTIVATION FUNCTIONS
-- ═══════════════════════════════════════════════════════════════════════════

-- ReLU
-- f(x) = max(0, x)
-- Most common activation; cheap, avoids vanishing gradients.
def relu (x : ℝ) : ℝ :=
  max 0 x

theorem relu_is_monotonic : monotonic_inc relu := sorry
theorem relu_is_non_neg : non_neg relu := sorry
theorem relu_is_idempotent : idempotent relu := sorry
theorem relu_is_lipschitz : lipschitz 1 relu := sorry

-- Sigmoid
-- σ(x) = 1 / (1 + e⁻ˣ)
-- Squashes to (0,1); used for binary classification output.
noncomputable def sigmoid (x : ℝ) : ℝ :=
  1 / (1 + Real.exp (-x))

theorem sigmoid_is_monotonic : monotonic_inc sigmoid := sorry
theorem sigmoid_is_bounded : bounded_func sigmoid := sorry

-- Tanh
-- tanh(x) = (eˣ - e⁻ˣ) / (eˣ + e⁻ˣ)
-- Squashes to (-1,1); zero-centered sigmoid.
noncomputable def my_tanh {x : ℝ} : ℝ :=
  Real.tanh x

-- ═══════════════════════════════════════════════════════════════════════════
-- NETWORK ARCHITECTURE
-- ═══════════════════════════════════════════════════════════════════════════

-- Dense Layer
-- (W, b) where W : ℝᵐˣⁿ, b : ℝᵐ
-- Fully-connected layer; represents x ↦ Wx + b.
structure dense_layer (n m : ℕ) where
  weights : real_matrix m n
  bias : real_vector m

-- Layer Forward Pass
-- forward(x) = Wx + b
-- Affine transformation before activation.
def layer_pass {n m : ℕ} (layer : dense_layer n m) (x : real_vector n) : real_vector m :=
  fun i : Fin m =>
  (∑ j : Fin n, layer.weights (i, j) * x j) + layer.bias i

-- Activation Layer
-- a = σ(z) applied element-wise
-- Introduces non-linearity after affine transformation.
def activation_layer {n : ℕ} (σ : ℝ → ℝ) (z : real_vector n) : real_vector n :=
  el_wise σ z

-- Dimension Compatibility
-- dₒᵤₜ = dᵢₙ
-- Layer output must match next layer input.
def dim_constraint {d_out d_in : ℕ} : Prop :=
  d_out = d_in

-- MLP (Multi-Layer Perceptron)
-- Sequence of dense layers with compatible dimensions.
-- Inductive structure enables arbitrary depth.
inductive MLP : ℕ → ℕ → Type where
  | output_layer {i o : ℕ} (l : dense_layer i o) : MLP i o
  | hidden_layer {i h o : ℕ} (l : dense_layer i h) (next : MLP h o) : MLP i o

-- MLP Forward Pass
-- Recursive evaluation through all layers.
-- Composes affine transforms with activations.
noncomputable def mlp_forward {i o : ℕ} (net : MLP i o) (x : real_vector i) : real_vector o :=
  match net with
  | MLP.output_layer l => layer_pass l x
  | MLP.hidden_layer l next =>
    let z := layer_pass l x
    let a := el_wise sigmoid z
    mlp_forward next a

-- ═══════════════════════════════════════════════════════════════════════════
-- LOSS FUNCTIONS & OPTIMIZATION
-- ═══════════════════════════════════════════════════════════════════════════

-- Dataset
-- D = {(xᵢ, yᵢ)}ᵢ₌₁ᴺ
-- Training data as input-output pairs.
structure dataset {N m : ℕ} where
  data : real_matrix N m

-- Mean Squared Error
-- L(y, ŷ) = (1/n) Σᵢ (yᵢ - ŷᵢ)²
-- Regression loss; non-negative, convex, differentiable.
noncomputable def mse {n : ℕ} (y_true y_hat : real_vector n) : real_vector n :=
  fun j => (1 / n) * (fun i => y_true i - y_hat i) j

-- ═══════════════════════════════════════════════════════════════════════════
-- DERIVATIVES & CALCULUS
-- ═══════════════════════════════════════════════════════════════════════════

-- Derivative (Fréchet)
-- f(x + h) = f(x) + L(h) + o(‖h‖)
-- L is the linear approximation; enables gradient computation.
def is_derivative_at {n m : ℕ}
  (f : real_vector n → real_vector m)
  (x : real_vector n)
  (L : real_matrix m n) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → ‖f (x + h) - f x - m_v_mul L h‖ ≤ ε * ‖h‖

-- Sigmoid Derivative
-- σ'(x) = σ(x)(1 - σ(x))
-- Used in backpropagation through sigmoid layers.
noncomputable def sigmoid_grad (x : ℝ) : ℝ :=
  sigmoid x * (1 - sigmoid x)

-- ReLU Derivative (Subgradient)
-- ReLU'(x) = 1 if x > 0, else 0
-- Piecewise; undefined at x=0, typically set to 0.
noncomputable def relu_grad (x : ℝ) : ℝ :=
  (if x > 0 then 1 else 0 : ℝ)

-- ═══════════════════════════════════════════════════════════════════════════
-- TO-DO: ADDITIONAL PROPERTIES NEEDED FOR MLP
-- ═══════════════════════════════════════════════════════════════════════════
-- Convexity
-- f(tx + (1-t)y) ≤ tf(x) + (1-t)f(y) for t ∈ [0,1]
-- Guarantees gradient descent finds global minimum for loss functions.

-- Strict Convexity
-- f(tx + (1-t)y) < tf(x) + (1-t)f(y) for t ∈ (0,1), x ≠ y
-- Guarantees unique global minimum.

-- Softmax
-- softmax(x)ᵢ = eˣⁱ / Σⱼ eˣʲ
-- Normalizes to probability distribution; Σᵢ softmax(x)ᵢ = 1.

-- Softmax Properties
-- ∀i, softmax(x)ᵢ ∈ (0,1) and Σᵢ softmax(x)ᵢ = 1
-- Output is valid probability distribution over classes.

-- Log-Sum-Exp
-- LSE(x) = log(Σᵢ eˣⁱ)
-- Numerically stable softmax computation; convex function.

-- Cross-Entropy Loss
-- L(y, ŷ) = -Σᵢ yᵢ log(ŷᵢ)
-- Multi-class classification loss; y is one-hot encoded.

-- Binary Cross-Entropy Loss
-- L(y, ŷ) = -[y log(ŷ) + (1-y) log(1-ŷ)]
-- Binary classification loss with sigmoid output.

-- KL Divergence
-- D_KL(P‖Q) = Σᵢ pᵢ log(pᵢ/qᵢ)
-- Measures distribution difference; cross-entropy = entropy + KL.

-- Chain Rule (Univariate)
-- (g ∘ f)'(x) = g'(f(x)) · f'(x)
-- Foundation of backpropagation.

-- Chain Rule (Multivariate)
-- D(g ∘ f)(x) = Dg(f(x)) · Df(x)
-- Jacobian composition; matrix multiplication of derivatives.

-- Jacobian Matrix
-- Jᵢⱼ = ∂fᵢ/∂xⱼ
-- Matrix of all partial derivatives; generalizes gradient to vector outputs.

-- Gradient
-- ∇f = [∂f/∂x₁, ..., ∂f/∂xₙ]ᵀ
-- Direction of steepest ascent; Jacobian transpose for scalar output.

-- Hessian Matrix
-- Hᵢⱼ = ∂²f/∂xᵢ∂xⱼ
-- Second derivatives; positive semi-definite implies convexity.

-- Gradient Descent Update
-- θₜ₊₁ = θₜ - η∇L(θₜ)
-- Parameter update rule; η is learning rate.

-- Learning Rate Constraint
-- η > 0
-- Must be positive; too large causes divergence, too small slows convergence.

-- Backpropagation (Layer Gradient)
-- ∂L/∂Wˡ = δˡ(aˡ⁻¹)ᵀ where δˡ = (∂L/∂zˡ)
-- Efficient gradient computation via dynamic programming.

-- Error Signal Propagation
-- δˡ = ((Wˡ⁺¹)ᵀδˡ⁺¹) ⊙ σ'(zˡ)
-- Backward pass; ⊙ is element-wise multiplication.

-- Bias Gradient
-- ∂L/∂bˡ = δˡ
-- Bias gradient equals error signal directly.

-- Parameter Vector
-- θ = [vec(W¹), b¹, ..., vec(Wᴸ), bᴸ]
-- Flattened parameters for optimization.

-- Loss Surface
-- L : Θ → ℝ
-- Maps parameters to scalar loss; gradient descent navigates this surface.

-- Critical Point
-- ∇L(θ*) = 0
-- Stationary point; could be minimum, maximum, or saddle.

-- Saddle Point
-- ∇L(θ*) = 0 with indefinite Hessian
-- Neither min nor max; common in high-dimensional loss surfaces.

-- Local Minimum
-- ∇L(θ*) = 0 with positive semi-definite Hessian
-- Gradient descent converges here; may not be global minimum.

-- Vanishing Gradient Condition
-- ‖∂L/∂Wˡ‖ → 0 as l → 1
-- Early layers stop learning; caused by saturating activations.

-- Exploding Gradient Condition
-- ‖∂L/∂Wˡ‖ → ∞ as l → 1
-- Training becomes unstable; bounded by Lipschitz constants.

-- Gradient Clipping
-- g' = g · min(1, c/‖g‖)
-- Prevents exploding gradients by capping norm.

-- L2 Regularization
-- L_reg(θ) = L(θ) + (λ/2)‖θ‖²
-- Weight decay; encourages small weights, improves generalization.

-- L1 Regularization
-- L_reg(θ) = L(θ) + λ‖θ‖₁
-- Encourages sparsity; some weights become exactly zero.

-- Xavier Initialization
-- W ~ N(0, 2/(nᵢₙ + nₒᵤₜ))
-- Variance scaling; maintains activation variance across layers.

-- He Initialization
-- W ~ N(0, 2/nᵢₙ)
-- For ReLU networks; accounts for ReLU killing half the variance.

-- Batch
-- B ⊂ D with |B| = batch_size
-- Subset for mini-batch gradient descent.

-- Mini-Batch Gradient
-- ∇L_B = (1/|B|) Σ_{(x,y)∈B} ∇L(x,y)
-- Unbiased estimate of full gradient.

-- Epoch
-- One complete pass through training dataset.
-- Model sees each example once per epoch.

-- Momentum
-- vₜ = βvₜ₋₁ + ∇L(θₜ), θₜ₊₁ = θₜ - ηvₜ
-- Accumulates gradient direction; accelerates convergence.

-- Adam Update
-- Combines momentum with adaptive learning rates.
-- mₜ = β₁mₜ₋₁ + (1-β₁)gₜ, vₜ = β₂vₜ₋₁ + (1-β₂)gₜ²

-- Universal Approximation Theorem
-- ∀ε>0, ∀f∈C(K), ∃MLP with one hidden layer s.t. ‖MLP - f‖_∞ < ε
-- MLPs can approximate any continuous function on compact domains.

-- Depth vs Width Trade-off
-- Deep networks can be exponentially more efficient than wide shallow ones.
-- Some functions require exponential width or polynomial depth.

-- Network Composition Theorem
-- MLP = σᴸ ∘ Aᴸ ∘ σᴸ⁻¹ ∘ ... ∘ σ¹ ∘ A¹
-- Network is alternating composition of affine and activation maps.

-- Lipschitz Composition
-- If f is K₁-Lipschitz and g is K₂-Lipschitz, then g∘f is K₁K₂-Lipschitz.
-- Network Lipschitz constant is product of layer constants.

-- Affine Layer is Lipschitz
-- ‖Wx + b - (Wy + b)‖ ≤ ‖W‖_op · ‖x - y‖
-- Lipschitz constant is operator norm of weight matrix.

-- Dropout (Training)
-- Randomly zero out activations with probability p.
-- Regularization technique; approximates ensemble.

-- Batch Normalization
-- Normalize activations to zero mean, unit variance per batch.
-- Stabilizes training; allows higher learning rates.

-- Skip Connection / Residual
-- h(x) = f(x) + x
-- Identity shortcut; enables training very deep networks.

-- Leaky ReLU
-- f(x) = max(αx, x) where α ∈ (0,1)
-- Prevents dead neurons; small gradient for x < 0.

-- ELU (Exponential Linear Unit)
-- f(x) = x if x > 0, else α(eˣ - 1)
-- Smooth approximation to ReLU; negative values allowed.

-- GELU
-- f(x) = x · Φ(x) where Φ is standard normal CDF
-- Smooth approximation used in transformers.

-- Swish
-- f(x) = x · σ(x)
-- Self-gated activation; smooth, non-monotonic.

-- Output Layer Activation
-- Regression: identity, Classification: softmax, Binary: sigmoid
-- Determined by task and loss function.

-- Differentiable Almost Everywhere
-- f is differentiable except on a set of measure zero.
-- Sufficient for gradient-based optimization (e.g., ReLU at 0).
