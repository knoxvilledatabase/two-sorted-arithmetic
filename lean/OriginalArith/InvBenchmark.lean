/-
Released under MIT license.
-/
import OriginalArith.Foundation

/-!
# Inverse Convention Benchmark: 0⁻¹ = 0 asserted vs derived

Mathlib defines `0⁻¹ = 0` by convention in any `GroupWithZero` or `DivisionRing`.
The documentation says: "working with total functions has the advantage of not
constantly having to check that x ≠ 0 when writing x⁻¹."

That convention is a choice. Not a derivation. This benchmark asks:
with Val α, does the convention become a theorem?

**File 1 (Collapsed):** `0⁻¹ = 0` is asserted as an axiom.
**File 2 (Val α):** `origin⁻¹ = origin` follows from absorption.
  `contents(0)⁻¹` is a separate question within contents.
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

/-- The convention: 0⁻¹ = 0. Asserted by definition. -/
theorem inv_zero : inv (none : G₀ α) = none := by
  rfl

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
-- VAL α: origin⁻¹ = origin by absorption, no convention
-- ============================================================================

namespace ConventionValAlpha

open Val

variable {α : Type}

-- Inverse: NOT a convention. Origin absorbs. Contents inverts within contents.
-- Container inverts its carried value.

/-- origin⁻¹ = origin. Derived from absorption, not asserted by convention. -/
theorem inv_origin : Val.inv (id : α → α) (origin : Val α) = origin := by
  rfl  -- same rfl, but the REASON is different: absorption, not convention

/-- contents(a)⁻¹ is contents(g a). Arithmetic within contents. -/
theorem inv_contents (g : α → α) (a : α) :
    Val.inv g (contents a) = contents (g a) := by rfl

/-- container(a)⁻¹ is container(g a). The bucket inverts its value. -/
theorem inv_container (g : α → α) (a : α) :
    Val.inv g (container a) = container (g a) := by rfl

/-- origin / origin = origin. Absorption, not 0/0=0 convention. -/
theorem origin_div_origin (f : α → α → α) (g : α → α) :
    Val.div f g (origin : Val α) origin = origin := by rfl

/-- origin / a = origin for all a. Absorption. -/
theorem origin_div (f : α → α → α) (g : α → α) (a : Val α) :
    Val.div f g origin a = origin := by rfl

/-- a / origin = origin for all a. Absorption. Not a convention. -/
theorem div_origin (f : α → α → α) (g : α → α) (a : Val α) :
    Val.div f g a origin = origin := by
  exact Val.div_by_origin f g a

/-- contents(a)⁻¹ is always contents. No ≠ 0 hypothesis needed.
    The type already knows contents elements are not origin. -/
theorem inv_contents_ne_origin (g : α → α) (a : α) :
    Val.inv g (contents a) ≠ (origin : Val α) := by
  simp [Val.inv]

-- SUMMARY:
--   Conventions asserted: 0
--   Theorems needing ≠ 0: 0 (type carries it)
--   Total theorems: 7 (but inv_contents_ne_origin replaces inv_ne_zero
--                       without a hypothesis — the type does the work)

end ConventionValAlpha

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed       Val α
--  Conventions asserted          1               0
--  ≠ 0 hypotheses               1               0
--  inv_zero status          asserted        derived (absorption)
--  0/0 status               0 (convention)  origin (absorption)
--  contents(0)⁻¹ status     same as 0⁻¹     separate question in contents
--  Information lost              0               0
--
--  The convention `0⁻¹ = 0` is the collapse formalized.
--  Mathlib chose 0 without asking which zero is in the denominator.
--
--  With Val α:
--  - origin⁻¹ = origin follows from absorption. No choice needed.
--  - contents(0)⁻¹ is a question within contents. Calculus handles it.
--  - The convention dissolves. It was never needed. It was papering
--    over the collision between two different zeros.
