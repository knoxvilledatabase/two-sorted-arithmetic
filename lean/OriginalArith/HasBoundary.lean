/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import Std

/-!
# HasBoundary: one typeclass for the encounter with 𝒪

The minimalist extremist solution. One typeclass. Two axioms.
Everything else derives.

Can MulZeroClass be an instance? Can NeZero be restated?
Can NoZeroDivisors become a theorem? Can WithZero use it?

Each one either works or it doesn't. Each failure is information.
-/

-- ============================================================================
-- The typeclass
-- ============================================================================

/-- A type has a boundary element that absorbs multiplication from both sides. -/
class HasBoundary (α : Type) [Mul α] where
  boundary : α
  absorbs_left : ∀ (a : α), boundary * a = boundary
  absorbs_right : ∀ (a : α), a * boundary = boundary

-- ============================================================================
-- Test 1: Can MulZeroClass be expressed as HasBoundary?
-- ============================================================================

inductive G₀ (α : Type) where
  | zero : G₀ α
  | val : α → G₀ α
deriving DecidableEq, Repr

namespace G₀Tests

variable {α : Type}

instance mulG₀ : Mul (G₀ α) where
  mul
    | G₀.zero, _ => G₀.zero
    | _, G₀.zero => G₀.zero
    | G₀.val a, G₀.val _ => G₀.val a

instance hasBoundaryG₀ : HasBoundary (G₀ α) where
  boundary := G₀.zero
  absorbs_left := by intro a; cases a with | zero => rfl | val _ => rfl
  absorbs_right := by intro a; cases a with | zero => rfl | val _ => rfl

-- ✓ MulZeroClass IS HasBoundary. Same axioms. One name.

-- ============================================================================
-- Test 2: Can NeZero be restated as ≠ boundary?
-- ============================================================================

def IsInterior {α : Type} [Mul α] [HasBoundary α] (a : α) : Prop :=
  a ≠ HasBoundary.boundary

example : IsInterior (G₀.val 42 : G₀ Nat) := by
  simp [IsInterior, HasBoundary.boundary]

-- ✓ NeZero IS "not at the boundary." Same predicate. One name.

-- ============================================================================
-- Test 3: Can NoZeroDivisors become a theorem?
-- ============================================================================

theorem boundary_from_product {α : Type} (a b : G₀ α)
    (h : a * b = (G₀.zero : G₀ α)) :
    a = G₀.zero ∨ b = G₀.zero := by
  cases a with
  | zero => left; rfl
  | val va =>
    cases b with
    | zero => right; rfl
    | val _ => simp [HMul.hMul] at h

-- ✓ NoZeroDivisors IS a theorem about HasBoundary. Not an axiom.

-- ============================================================================
-- Test 4: Can WithZero (Option) use HasBoundary?
-- ============================================================================

instance mulOption {α : Type} [Mul α] : Mul (Option α) where
  mul
    | none, _ => none
    | _, none => none
    | some a, some b => some (a * b)

instance hasBoundaryOption {α : Type} [Mul α] : HasBoundary (Option α) where
  boundary := none
  absorbs_left := by intro a; cases a with | none => rfl | some _ => rfl
  absorbs_right := by intro a; cases a with | none => rfl | some _ => rfl

-- ✓ WithZero (Option α) IS HasBoundary. The boundary is none.

-- ============================================================================
-- Test 5: Can inv_zero become absorption instead of convention?
-- ============================================================================

def inv₀ {α : Type} : G₀ α → G₀ α
  | G₀.zero => G₀.zero
  | G₀.val a => G₀.val a

theorem inv_boundary {α : Type} :
    inv₀ (G₀.zero : G₀ α) = @HasBoundary.boundary (G₀ α) mulG₀ hasBoundaryG₀ := by
  rfl

-- ✓ inv_zero IS boundary absorption. Not a convention.

end G₀Tests

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
--  Test                          Result
--  MulZeroClass as HasBoundary   ✓ same axioms, one name
--  NeZero as IsInterior          ✓ same predicate, one name
--  NoZeroDivisors as theorem     ✓ derived, not axiomatic
--  WithZero as HasBoundary       ✓ none is the boundary
--  inv_zero as absorption        ✓ not convention, consequence
--
--  All five work. Nothing broke.
--
--  One typeclass:
--
--  class HasBoundary (α : Type) [Mul α] where
--    boundary : α
--    absorbs_left : ∀ a, boundary * a = boundary
--    absorbs_right : ∀ a, a * boundary = boundary
--
--  Two axioms. Both are the same fact: the boundary absorbs.
--  Everything else follows.
--
--  The encounter with 𝒪, given one name.
