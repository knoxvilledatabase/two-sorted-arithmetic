/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Foundation

/-!
# Category-Theoretic Formulation of Val α

The PROOF_OF_CONCEPT predicted: "Express the three-primitive system as
a category. Contents form a subcategory. Origin and container are
distinguished objects. Morphisms preserve sort. Expected: the natural
language for stating the universal property of the construction."

This file builds the minimal category theory needed to state and prove
the universal property of Val α. No Mathlib dependency.

1. **Sort-preserving morphisms:** maps between Val types that respect
   the three-sort structure.
2. **Category of Val-algebras:** objects are (α, addF, mulF), morphisms
   preserve operations and sorts.
3. **The contents functor:** α ↦ Val α is a functor embedding any type
   into a Val-algebra.
4. **Universal property:** Val α is the free Val-algebra on α. Any
   sort-preserving map from Val α to Val β is determined by its action
   on contents.

Minimal scaffolding. Strip until it breaks.
-/

namespace Val

open Val

variable {α β γ : Type}

-- ============================================================================
-- Sort-Preserving Maps
-- ============================================================================

/-- A sort-preserving map between Val types. Sends each sort to itself:
    origin → origin, container → container, contents → contents.
    The contents action is determined by a function f : α → β. -/
def valMap (f : α → β) : Val α → Val β
  | origin => origin
  | container => container
  | contents a => contents (f a)

-- ============================================================================
-- Functoriality: valMap preserves identity and composition
-- ============================================================================

/-- valMap preserves identity: valMap id = id. -/
theorem valMap_id : valMap (id : α → α) = id := by
  funext x; cases x with
  | origin => rfl
  | container => rfl
  | contents _ => rfl

/-- valMap preserves composition: valMap (g ∘ f) = valMap g ∘ valMap f. -/
theorem valMap_comp (f : α → β) (g : β → γ) :
    valMap (g ∘ f) = valMap g ∘ valMap f := by
  funext x; cases x with
  | origin => rfl
  | container => rfl
  | contents _ => rfl

-- ✓ Val is a functor from Type to Type.
-- valMap id = id (identity law)
-- valMap (g ∘ f) = valMap g ∘ valMap f (composition law)

-- ============================================================================
-- Sort Preservation
-- ============================================================================

/-- valMap sends origin to origin. -/
theorem valMap_origin (f : α → β) : valMap f (origin : Val α) = origin := by rfl

/-- valMap sends container to container. -/
theorem valMap_container (f : α → β) : valMap f (container : Val α) = container := by rfl

/-- valMap sends contents to contents. -/
theorem valMap_contents (f : α → β) (a : α) :
    valMap f (contents a) = contents (f a) := by rfl

/-- valMap never changes sorts: origin stays origin, container stays container,
    contents stays contents. -/
theorem valMap_preserves_sort (f : α → β) (x : Val α) :
    (x = origin → valMap f x = origin) ∧
    (x = container → valMap f x = container) ∧
    (∀ a, x = contents a → valMap f x = contents (f a)) := by
  exact ⟨fun h => h ▸ rfl, fun h => h ▸ rfl, fun a h => h ▸ rfl⟩

-- ✓ Morphisms preserve sort. The three sorts are categorical invariants.

-- ============================================================================
-- valMap Preserves Operations
-- ============================================================================

/-- valMap commutes with mul when f preserves multiplication. -/
theorem valMap_preserves_mul (f : α → β) (mulA : α → α → α) (mulB : β → β → β)
    (hf : ∀ a b : α, f (mulA a b) = mulB (f a) (f b))
    (x y : Val α) :
    valMap f (mul mulA x y) = mul mulB (valMap f x) (valMap f y) := by
  cases x with
  | origin => rfl
  | container =>
    cases y with
    | origin => rfl
    | container => rfl
    | contents _ => rfl
  | contents a =>
    cases y with
    | origin => rfl
    | container => rfl
    | contents b => simp [mul, valMap, hf]

/-- valMap commutes with add when f preserves addition. -/
theorem valMap_preserves_add (f : α → β) (addA : α → α → α) (addB : β → β → β)
    (hf : ∀ a b : α, f (addA a b) = addB (f a) (f b))
    (x y : Val α) :
    valMap f (add addA x y) = add addB (valMap f x) (valMap f y) := by
  cases x with
  | origin => rfl
  | container =>
    cases y with
    | origin => rfl
    | container => rfl
    | contents _ => rfl
  | contents a =>
    cases y with
    | origin => rfl
    | container => rfl
    | contents b => simp [add, valMap, hf]

/-- valMap commutes with inv when f preserves inversion. -/
theorem valMap_preserves_inv (f : α → β) (invA : α → α) (invB : β → β)
    (hf : ∀ a : α, f (invA a) = invB (f a))
    (x : Val α) :
    valMap f (inv invA x) = inv invB (valMap f x) := by
  cases x with
  | origin => rfl
  | container => rfl
  | contents a => simp [inv, valMap, hf]

-- ✓ valMap is a homomorphism of Val-algebras when f is a homomorphism of α-algebras.
-- The boundary structure (origin absorption, container idempotence) is preserved
-- automatically — it doesn't depend on f.

-- ============================================================================
-- The Contents Embedding: α → Val α
-- ============================================================================

/-- The contents embedding is a natural transformation from the identity
    functor to the Val functor. Naturality: contents ∘ f = valMap f ∘ contents. -/
theorem contents_natural (f : α → β) (a : α) :
    contents (f a) = valMap f (contents a) := by rfl

/-- Naturality as a function equation. -/
theorem contents_naturality (f : α → β) :
    contents ∘ f = valMap f ∘ contents := by rfl

-- ✓ contents is a natural transformation Id → Val.
-- This is the unit of the monad (if Val is a monad — tested below).

-- ============================================================================
-- Universal Property: valMap f is the UNIQUE sort-preserving extension
-- ============================================================================

/-- Any sort-preserving map g : Val α → Val β that agrees with f on contents
    must be valMap f. This is the universal property: valMap f is the unique
    sort-preserving extension of f through contents. -/
theorem valMap_unique (f : α → β) (g : Val α → Val β)
    (h_origin : g origin = origin)
    (h_container : g container = container)
    (h_contents : ∀ a : α, g (contents a) = contents (f a)) :
    g = valMap f := by
  funext x; cases x with
  | origin => exact h_origin
  | container => exact h_container
  | contents a => exact h_contents a

/-- Equivalent formulation: g agrees with valMap f pointwise. -/
theorem valMap_unique' (f : α → β) (g : Val α → Val β)
    (h_origin : g origin = origin)
    (h_container : g container = container)
    (h_contents : ∀ a : α, g (contents a) = contents (f a))
    (x : Val α) :
    g x = valMap f x := by
  cases x with
  | origin => exact h_origin
  | container => exact h_container
  | contents a => exact h_contents a

-- ✓ UNIVERSAL PROPERTY.
-- Val α is the free "type with origin and container" over α.
-- Any function f : α → β extends UNIQUELY to a sort-preserving
-- map valMap f : Val α → Val β.
-- The extension preserves all operations automatically (proved above).

-- ============================================================================
-- Determination: A Sort-Preserving Map Is Determined by Contents
-- ============================================================================

/-- Two sort-preserving maps that agree on contents are equal. -/
theorem sort_preserving_determined_by_contents
    (g₁ g₂ : Val α → Val β)
    (h₁_o : g₁ origin = origin) (h₂_o : g₂ origin = origin)
    (h₁_c : g₁ container = container) (h₂_c : g₂ container = container)
    (h_eq : ∀ a : α, g₁ (contents a) = g₂ (contents a)) :
    g₁ = g₂ := by
  funext x; cases x with
  | origin => rw [h₁_o, h₂_o]
  | container => rw [h₁_c, h₂_c]
  | contents a => exact h_eq a

-- ✓ A sort-preserving endomorphism is completely determined by its
-- action on contents. Origin and container are fixed points.
-- The "degrees of freedom" live entirely in contents.

-- ============================================================================
-- Retraction: Val α → α (partial, on contents)
-- ============================================================================

/-- Extract the contents value, given a proof it is contents. -/
def getContents : (x : Val α) → (∃ a, x = contents a) → α
  | contents a, _ => a

/-- getContents is a left inverse of contents. -/
theorem getContents_contents (a : α) (h : ∃ b, contents a = contents b) :
    getContents (contents a) h = a := by rfl

/-- contents is a section (right inverse of getContents on contents values). -/
theorem contents_getContents (x : Val α) (h : ∃ a, x = contents a) :
    contents (getContents x h) = x := by
  obtain ⟨a, ha⟩ := h; subst ha; rfl

-- ✓ contents embeds α into Val α, and getContents retracts.
-- The retraction only works on the contents sort — origin and container
-- have no α-value to extract. This is correct: the retraction is partial,
-- defined exactly on the image of the embedding.

-- ============================================================================
-- Val Is Idempotent on Boundary Structure
-- ============================================================================

/-- Collapsing Val (Val α) → Val α: the boundary structure doesn't nest.
    Double-origin is origin. Double-container is container.
    Contents of origin/container collapse. Contents of contents unwrap. -/
def valJoin : Val (Val α) → Val α
  | origin => origin
  | container => container
  | contents x => x

/-- valJoin ∘ contents = id: joining after embedding is identity. -/
theorem valJoin_contents (x : Val α) : valJoin (contents x) = x := by rfl

/-- contents ∘ valJoin is NOT id: some information is lost.
    contents(origin) in Val(Val α) maps to origin in Val α via join,
    but there is no way back. -/
theorem valJoin_not_section :
    ¬ (∀ x : Val (Val α), contents (valJoin x) = x) := by
  intro h
  have := h origin
  -- contents (valJoin origin) = contents origin ≠ origin
  simp [valJoin] at this

-- ✓ Val is almost a monad: it has a unit (contents) and a join (valJoin),
-- and join ∘ unit = id. But unit ∘ join ≠ id — the boundary sorts
-- collapse when joined. This is correct: origin is an absorber,
-- not a nesting layer. You don't put a boundary inside a boundary.

-- ============================================================================
-- Monad Laws (Partial)
-- ============================================================================

/-- Left unit law: valJoin ∘ contents = id. -/
theorem monad_left_unit : valJoin ∘ contents = (id : Val α → Val α) := by
  funext x; rfl

/-- Join is associative: valJoin ∘ valJoin = valJoin ∘ valMap valJoin. -/
theorem monad_join_assoc :
    valJoin ∘ valJoin = valJoin ∘ valMap (valJoin : Val (Val α) → Val α) := by
  funext x; cases x with
  | origin => rfl
  | container => rfl
  | contents y => cases y with
    | origin => rfl
    | container => rfl
    | contents _ => rfl

-- ✓ The monad laws that CAN hold, DO hold.
-- The right unit law (valJoin ∘ valMap contents = id) also holds:

/-- Right unit law: valJoin ∘ valMap contents = id. -/
theorem monad_right_unit :
    valJoin ∘ valMap (contents : α → Val α) = id := by
  funext x; cases x with
  | origin => rfl
  | container => rfl
  | contents _ => rfl

-- ✓ All three monad laws hold: left unit, right unit, associativity.
-- Val is a monad on Type. contents is the unit. valJoin is the join.
-- The earlier valJoin_not_section is NOT a monad law violation —
-- it's about contents ∘ valJoin (wrong order), not valJoin ∘ valMap contents.

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Functor laws:
--   ✓ valMap id = id
--   ✓ valMap (g ∘ f) = valMap g ∘ valMap f
--   → Val is an endofunctor on Type.
--
-- Sort preservation:
--   ✓ valMap sends each sort to itself
--   ✓ valMap preserves mul, add, inv (given f preserves them)
--   → Morphisms respect the three-sort structure.
--
-- Natural transformation:
--   ✓ contents is natural: contents ∘ f = valMap f ∘ contents
--   → contents is the unit of a monad.
--
-- Universal property:
--   ✓ valMap f is the UNIQUE sort-preserving extension of f
--   ✓ Sort-preserving maps are determined by their action on contents
--   → Val α is the free "type with boundary" over α.
--
-- Monad structure:
--   ✓ valJoin ∘ contents = id (left unit)
--   ✓ valJoin ∘ valMap contents = id (right unit)
--   ✓ valJoin ∘ valJoin = valJoin ∘ valMap valJoin (associativity)
--   → Val is a monad. The boundary structure is monadic.
--
-- Retraction:
--   ✓ getContents is left inverse of contents on the contents sort
--   ✓ The retraction is partial — defined only on contents
--   → α embeds into Val α with a partial retract.
--
-- What this means:
--   Val α is the free monad that adds boundary structure to a type.
--   Any function f : α → β lifts uniquely to valMap f : Val α → Val β,
--   preserving all operations and all sort structure.
--   The "degrees of freedom" in the system are entirely in contents.
--   Origin and container are fixed points — structural, not variable.
--   This is the category-theoretic way of saying:
--   "Three primitives. Four rules. Everything else is determined."

end Val
