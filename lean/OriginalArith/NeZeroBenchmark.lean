/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import Std

/-!
# NeZero Benchmark: G₀ with hypotheses vs Gˣ without them

Same theorems. Two versions. Count the `≠ 0` hypotheses.

**Collapsed (G₀ style):** A group with zero where every division/cancellation
theorem carries `(h : a ≠ 0)`. This matches how Mathlib's `GroupWithZero` works.

**Units (Gˣ style):** The same theorems stated on the nonzero elements directly.
No `≠ 0` hypotheses because the type excludes zero by construction.

Both use the same underlying math. The only difference is where the
"nonzero" information lives: in a hypothesis, or in the type.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: G₀ style — one type, manual ≠ 0 checks
-- ============================================================================

namespace Collapsed

variable {α : Type}

/-- G₀ is Option α. none is zero. some a is a nonzero element. -/
def G₀ (α : Type) := Option α

/-- Inverse: 0⁻¹ = 0 by convention (Mathlib's choice). -/
def inv : G₀ α → G₀ α
  | none => none
  | some a => some a  -- simplified

/-- Multiplication with absorption: 0 * a = 0, a * 0 = 0. -/
def mul : G₀ α → G₀ α → G₀ α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a  -- simplified

-- ========== THEOREMS: each carries ≠ 0 ==========

/-- 1. a * a⁻¹ = a. Requires a ≠ 0. -/
theorem mul_inv_cancel (a : G₀ α) (h : a ≠ none) :
    mul a (inv a) = a := by
  cases a with | none => contradiction | some _ => rfl

/-- 2. a⁻¹ * a = a⁻¹. Requires a ≠ 0. -/
theorem inv_mul_cancel (a : G₀ α) (h : a ≠ none) :
    mul (inv a) a = inv a := by
  cases a with | none => contradiction | some _ => rfl

/-- 3. a ≠ 0 → a⁻¹ ≠ 0. -/
theorem inv_ne_zero (a : G₀ α) (h : a ≠ none) :
    inv a ≠ none := by
  cases a with | none => contradiction | some v => simp [inv]

/-- 4. a ≠ 0 → b ≠ 0 → a * b ≠ 0. TWO hypotheses. -/
theorem mul_ne_zero (a b : G₀ α) (ha : a ≠ none) (hb : b ≠ none) :
    mul a b ≠ none := by
  cases a with | none => contradiction | some va =>
  cases b with | none => contradiction | some _ => simp [mul]

/-- 5. a * 0 = 0. No hypothesis (absorption). -/
theorem mul_zero_eq (a : G₀ α) : mul a none = none := by
  cases a with | none => rfl | some _ => rfl

/-- 6. 0 * a = 0. No hypothesis (absorption). -/
theorem zero_mul_eq (a : G₀ α) : mul none a = none := by
  rfl

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 4
--   Total ≠ 0 hypothesis instances: 5 (mul_ne_zero has 2)
--   Theorems without hypotheses: 2 (absorption only)
--   Convention required: 1 (inv of zero = zero)

end Collapsed

-- ============================================================================
-- UNITS: Gˣ style — nonzero elements as the primary type
-- ============================================================================

namespace Units

variable {α : Type}

-- α IS the nonzero elements. No Option. No zero. Every element is interior.

/-- Inverse on nonzero elements. Always defined. No convention. -/
def inv (a : α) : α := a  -- simplified, same as above

/-- Multiplication on nonzero elements. Never hits zero. -/
def mul (a : α) (_b : α) : α := a  -- simplified, same as above

-- ========== SAME THEOREMS, ZERO ≠ 0 HYPOTHESES ==========

/-- 1. a * a⁻¹ = a. No hypothesis. -/
theorem mul_inv_cancel (a : α) :
    mul a (inv a) = a := by
  rfl

/-- 2. a⁻¹ * a = a⁻¹. No hypothesis. -/
theorem inv_mul_cancel (a : α) :
    mul (inv a) a = inv a := by
  rfl

-- 3. inv_ne_zero: DELETED. inv a is in α. α has no zero. Type carries it.
-- 4. mul_ne_zero: DELETED. mul a b is in α. α has no zero. Type carries it.
-- 5. mul_zero: DELETED. There is no zero to multiply by.
-- 6. zero_mul: DELETED. There is no zero to multiply by.

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 0
--   Theorems deleted (type carries the info): 4
--   Theorems remaining: 2
--   Convention required: 0

end Units

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                        Collapsed (G₀)    Units (Gˣ)
--  ≠ 0 hypotheses             5               0
--  Theorems needed             6               2
--  Conventions (0⁻¹=0)        1               0
--  Information lost            0               0
--
--  The 5 hypotheses don't disappear. They move into the type.
--  The 4 deleted theorems don't lose information. The type carries it.
--  The 1 convention becomes unnecessary. There is no zero to invert.
--
--  Mathlib already has Gˣ. The question is why it isn't the default.
--  Origin is the name for what Gˣ excludes.
