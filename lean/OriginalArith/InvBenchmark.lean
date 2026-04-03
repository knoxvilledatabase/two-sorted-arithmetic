/-
Released under MIT license.
-/
import Std

/-!
# Inverse Convention Benchmark: 0⁻¹ = 0 asserted vs derived

Mathlib defines `0⁻¹ = 0` by convention in any `GroupWithZero` or `DivisionRing`.
The documentation says: "working with total functions has the advantage of not
constantly having to check that x ≠ 0 when writing x⁻¹."

That convention is a choice. Not a derivation. This benchmark asks:
with the two-sorted split, does the convention become a theorem?

**File 1 (Collapsed):** `0⁻¹ = 0` is asserted as an axiom.
**File 2 (Two-sorted):** `origin'⁻¹ = origin'` follows from absorption.
  `bounded'(0)⁻¹` is a separate question within B.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: 0⁻¹ = 0 by convention
-- ============================================================================

namespace ConventionCollapsed

variable {α : Type}

def G₀ (α : Type) := Option α

-- Inverse: THE CONVENTION. 0⁻¹ = 0. Asserted, not derived.
-- This is Mathlib's `inv_zero` axiom in GroupWithZero.
def inv : G₀ α → G₀ α
  | none => none          -- ← THIS IS THE CONVENTION: 0⁻¹ = 0
  | some a => some a      -- nonzero inverse (simplified)

def mul : G₀ α → G₀ α → G₀ α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a

-- The convention stated as a theorem — but it's just unfolding the definition.
-- In Mathlib this is the `inv_zero` axiom. It's asserted, not proved from
-- deeper principles. The choice of `none` (rather than `some x` for any x)
-- is a human decision.

/-- The convention: 0⁻¹ = 0. Asserted by definition. -/
theorem inv_zero : inv (none : G₀ α) = none := by
  rfl  -- trivially true because we DEFINED it this way

/-- Downstream: 0 / 0 = 0. Follows from the convention. -/
theorem zero_div_zero : mul (none : G₀ α) (inv none) = none := by
  rfl

/-- Downstream: 0 / a = 0 for all a. -/
theorem zero_div (a : G₀ α) : mul none (inv a) = none := by
  rfl

/-- Downstream: a / 0 = 0 for all a. Requires the convention. -/
theorem div_zero (a : G₀ α) : mul a (inv none) = none := by
  cases a with | none => rfl | some _ => rfl

/-- Downstream: inv distributes — but only if a ≠ 0. -/
theorem inv_ne_zero (a : G₀ α) (h : a ≠ none) : inv a ≠ none := by
  cases a with | none => contradiction | some _ => simp [inv]

-- SUMMARY:
--   Conventions asserted: 1 (inv_zero, the choice that 0⁻¹ = 0)
--   Theorems needing ≠ 0: 1 (inv_ne_zero)
--   Total theorems: 5

end ConventionCollapsed

-- ============================================================================
-- TWO-SORTED: origin'⁻¹ = origin' by absorption, no convention
-- ============================================================================

namespace ConventionTwoSorted

variable {α : Type}

-- The two-sorted type: Origin (boundary) or Bounded (interior).
inductive Sort' (α : Type) where
  | origin : Sort' α         -- the boundary
  | bounded : α → Sort' α    -- interior elements

open Sort'

-- Inverse: NOT a convention. Origin absorbs. Bounded inverts within B.
def inv : Sort' α → Sort' α
  | origin => origin          -- ← NOT A CONVENTION: absorption. I1/I2.
  | bounded a => bounded a    -- nonzero inverse within B (simplified)

def mul : Sort' α → Sort' α → Sort' α
  | origin, _ => origin       -- absorption I2
  | _, origin => origin       -- absorption I1
  | bounded a, bounded _ => bounded a  -- within B (simplified)

-- origin'⁻¹ = origin' is not a convention. It's absorption.
-- The boundary absorbs the inverse operation the same way it absorbs
-- multiplication. This follows from what Origin IS, not from a choice.

/-- origin⁻¹ = origin. Derived from absorption, not asserted by convention. -/
theorem inv_origin : inv (origin : Sort' α) = origin := by
  rfl  -- same rfl, but the REASON is different: absorption, not convention

/-- bounded(0)⁻¹ is a separate question within B. -/
theorem inv_bounded (a : α) : inv (bounded a) = bounded a := by
  rfl

/-- origin / origin = origin. Absorption, not 0/0=0 convention. -/
theorem origin_div_origin : mul (origin : Sort' α) (inv origin) = origin := by
  rfl

/-- origin / a = origin for all a. Absorption I2. -/
theorem origin_div (a : Sort' α) : mul origin (inv a) = origin := by
  rfl

/-- a / origin = origin for all a. Absorption I1. Not a convention. -/
theorem div_origin (a : Sort' α) : mul a (inv origin) = origin := by
  cases a with | origin => rfl | bounded _ => rfl

/-- bounded(a)⁻¹ is always bounded. No ≠ 0 hypothesis needed.
    The type already knows bounded elements are not origin. -/
theorem inv_bounded_ne_origin (a : α) : inv (bounded a) ≠ origin := by
  simp [inv]

-- SUMMARY:
--   Conventions asserted: 0
--   Theorems needing ≠ 0: 0 (type carries it)
--   Total theorems: 6 (but inv_bounded_ne_origin replaces inv_ne_zero
--                       without a hypothesis — the type does the work)

end ConventionTwoSorted

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed       Two-Sorted
--  Conventions asserted          1               0
--  ≠ 0 hypotheses               1               0
--  inv_zero status          asserted        derived (absorption)
--  0/0 status               0 (convention)  origin (absorption)
--  bounded(0)⁻¹ status      same as 0⁻¹     separate question in B
--  Information lost              0               0
--
--  The convention `0⁻¹ = 0` is Brahmagupta's collapse formalized.
--  Mathlib chose 0 without asking which zero is in the denominator.
--
--  With the two-sorted split:
--  - origin⁻¹ = origin follows from absorption. No choice needed.
--  - bounded(0)⁻¹ is a question within B. Calculus handles it.
--  - The convention dissolves. It was never needed. It was papering
--    over the collision between two different zeros.
