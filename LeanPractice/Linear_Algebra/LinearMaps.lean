/-
-- Some Notes from this lecture:
-- https://www.youtube.com/watch?v=GkPhwnvRe-8
-- Linear Algebra Talk 1/2
-/

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.DivisionRing

open Module

set_option linter.style.longLine false


-- basis
-- set of coord axis
-- finite set of things
-- lens with what you look at the space through
-- different lens/different basis
-- abstract lens
-- how to choose the right basis for my problem


-- First set of notes below ->
/-!
# Linear Map Properties: Injective, Surjective, and Isomorphisms

Key theorem: For linear maps between finite-dimensional spaces,
any 2 of these 3 properties imply the third:
1. Injective (ker f = {0})
2. Surjective (im f = W)
3. dim V = dim W
-/

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [AddCommGroup W]
variable [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

-- ═══════════════════════════════════════════════════════════════════════════
-- DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════

-- Injective
-- ∀ x y, f(x) = f(y) → x = y
-- A function that maps distinct inputs to distinct outputs
def injective {α β : Type} (f : α → β) : Prop :=
  ∀ x y, f x = f y → x = y
  -- or
  -- ∀ x y, x ≠ y → f x ≠ f y

-- Surjective
-- ∀ w ∈ W, ∃ v ∈ V, f(v) = w
-- A function whose image covers the entire codomain
def surjective {α β : Type} (f : α → β) : Prop :=
  ∀ (y : β), ∃ (x : α), f x = y

-- Bijective
-- Injective f ∧ Surjective f
-- A function that is both injective and surjective
def bijective {α β : Type} (f : α → β) : Prop :=
  injective f ∧ surjective f

-- Kernel (ker)
-- ker(f) = {v ∈ V | f(v) = 0}
-- The set of all vectors that map to zero
def kernel {α β : Type} (f : α → β) [Zero β] : Set α :=
  {x : α | f x = 0}
-- or
def kernel_2 {α β : Type} (f : α → β) [Zero β] : α → Prop :=
  fun x => f x = 0

-- Image (range)
-- im(f) = {f(v) | v ∈ V}
-- The set of all vectors that are outputs of f
def image {α β : Type} (f : α → β) : Set β :=
  {y : β | ∃ x, f x = y}

-- Linear Isomorphism
-- A bijective linear map between vector spaces
-- An invertible structure-preserving map
def is_linear {α β γ : Type} [Add β] [Add γ] [SMul α β] [SMul α γ] (f : β → γ) : Prop :=
  (∀ x y, f (x + y) = f x + f y) ∧ (∀ (c : α) (x : β), f (c • x) = c • f x)

def is_linear_isomorphism {α β γ : Type} [Add β] [Add γ] [SMul α β] [SMul α γ] (f : β → γ) : Prop :=
    (∀ x y, f (x + y) = f x + f y) ∧ (∀ (c : α) (x : β), f (c • x) = c • f x) ∧ bijective f
-- error for "is_linear f ∧ bijective f", just inlined it

-- ═══════════════════════════════════════════════════════════════════════════
-- THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════

-- Rank-Nullity Theorem (foundation)
-- dim(V) = dim(ker f) + dim(im f)
omit [FiniteDimensional K W] in
theorem rank_nullity (f : V →ₗ[K] W) :
    finrank K V = finrank K (LinearMap.ker f) + finrank K (LinearMap.range f) := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  omega

-- Injective ↔ trivial kernel
omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem injective_iff_ker_eq_bot (f : V →ₗ[K] W) :
    Function.Injective f ↔ LinearMap.ker f = ⊥ :=
  LinearMap.ker_eq_bot.symm

-- Surjective ↔ image is everything
omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem surjective_iff_range_eq_top (f : V →ₗ[K] W) :
    Function.Surjective f ↔ LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top.symm

-- (1) Injective + Equal dimensions → Surjective
theorem surjective_of_injective_of_finrank_eq' (f : V →ₗ[K] W)
    (hinj : Function.Injective f) (hdim : finrank K V = finrank K W) :
    Function.Surjective f :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj

-- (2) Surjective + Equal dimensions → Injective
theorem injective_of_surjective_of_finrank_eq' (f : V →ₗ[K] W)
    (hsurj : Function.Surjective f) (hdim : finrank K V = finrank K W) :
    Function.Injective f :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj

-- (3) Injective + Surjective → Equal dimensions
omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem finrank_eq_of_bijective (f : V →ₗ[K] W)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    finrank K V = finrank K W :=
  LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

-- Isomorphism ↔ Bijective linear map
omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem isomorphism_iff_bijective (f : V →ₗ[K] W) :
    Function.Bijective f ↔ ∃ (e : V ≃ₗ[K] W), (e : V →ₗ[K] W) = f :=
  ⟨fun hbij => ⟨LinearEquiv.ofBijective f hbij, rfl⟩,
   fun ⟨e, he⟩ => he ▸ e.bijective⟩
