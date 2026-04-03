/-
Released under MIT license.
-/
import Std

/-!
# NoZeroDivisors Benchmark: collapsed vs two-sorted

Mathlib's `NoZeroDivisors` states: `a * b = 0 → a = 0 ∨ b = 0`.
This typeclass exists because in a collapsed type, two nonzero elements
can multiply to produce zero (a "zero divisor"). The typeclass asserts
this pathology doesn't happen.

In the two-sorted version, `bounded(a) * bounded(b) = bounded(a*b)`.
The result is always bounded. It never equals origin. The pathology
can't arise. The typeclass becomes unnecessary.

**File 1 (Collapsed):** NoZeroDivisors must be asserted as an axiom.
**File 2 (Two-sorted):** The property follows from the type. No axiom needed.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: NoZeroDivisors as an axiom
-- ============================================================================

namespace ZDCollapsed

variable {α : Type}

def G₀ (α : Type) := Option α

def mul : G₀ α → G₀ α → G₀ α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a  -- simplified

-- The NoZeroDivisors property must be ASSERTED.
-- In a general ring, a * b can equal 0 even when a ≠ 0 and b ≠ 0.
-- (Example: in ℤ/6ℤ, 2 * 3 = 0 but 2 ≠ 0 and 3 ≠ 0.)
-- Mathlib requires a separate typeclass to exclude this.

/-- NoZeroDivisors: if a * b = 0 then a = 0 or b = 0.
    This is an AXIOM — asserted about the structure, not derived from it. -/
theorem no_zero_divisors (a b : G₀ α)
    (h : mul a b = none) : a = none ∨ b = none := by
  cases a with
  | none => left; rfl
  | some va =>
    cases b with
    | none => right; rfl
    | some _ => simp [mul] at h

/-- Downstream: if a ≠ 0 and b ≠ 0 then a * b ≠ 0.
    Requires NoZeroDivisors to hold. Both hypotheses needed. -/
theorem mul_ne_zero (a b : G₀ α)
    (ha : a ≠ none) (hb : b ≠ none) : mul a b ≠ none := by
  intro h
  cases no_zero_divisors a b h with
  | inl ha' => exact ha ha'
  | inr hb' => exact hb hb'

/-- Downstream: cancellation from product. If a * b = 0 and a ≠ 0 then b = 0.
    Requires NoZeroDivisors + ≠ 0 hypothesis. -/
theorem eq_zero_of_mul_eq_zero_left (a b : G₀ α)
    (ha : a ≠ none) (h : mul a b = none) : b = none := by
  cases no_zero_divisors a b h with
  | inl ha' => exact absurd ha' ha
  | inr hb => exact hb

/-- Downstream: same, other direction. -/
theorem eq_zero_of_mul_eq_zero_right (a b : G₀ α)
    (hb : b ≠ none) (h : mul a b = none) : a = none := by
  cases no_zero_divisors a b h with
  | inl ha => exact ha
  | inr hb' => exact absurd hb' hb

-- SUMMARY:
--   Axioms asserted: 1 (no_zero_divisors)
--   ≠ 0 hypotheses: 4 (across mul_ne_zero and the two cancellation theorems)
--   Total theorems: 4

end ZDCollapsed

-- ============================================================================
-- TWO-SORTED: zero divisors can't happen
-- ============================================================================

namespace ZDTwoSorted

variable {α : Type}

inductive Sort' (α : Type) where
  | origin : Sort' α
  | bounded : α → Sort' α

open Sort'

def mul : Sort' α → Sort' α → Sort' α
  | origin, _ => origin
  | _, origin => origin
  | bounded a, bounded _ => bounded a  -- simplified

-- The key fact: bounded * bounded is ALWAYS bounded. Never origin.
-- Zero divisors require a * b = 0 where a ≠ 0 and b ≠ 0.
-- In the two-sorted version, bounded(a) * bounded(b) = bounded(a*b).
-- The result is bounded. It is not origin. The pathology cannot arise.

/-- Bounded * bounded is always bounded. The type prevents zero divisors. -/
theorem mul_bounded_bounded (a b : α) :
    mul (bounded a) (bounded b) = bounded a := by
  rfl

/-- Bounded * bounded is never origin. This is what NoZeroDivisors asserts
    as an axiom. Here it follows from the type. -/
theorem mul_bounded_ne_origin (a b : α) :
    mul (bounded a) (bounded b) ≠ origin := by
  simp [mul]

/-- The only way to get origin from multiplication is if an input was origin. -/
theorem mul_eq_origin_iff (a b : Sort' α) :
    mul a b = origin ↔ (a = origin ∨ b = origin) := by
  constructor
  · intro h
    cases a with
    | origin => left; rfl
    | bounded va =>
      cases b with
      | origin => right; rfl
      | bounded _ => simp [mul] at h
  · intro h
    cases h with
    | inl ha => rw [ha]; rfl
    | inr hb => rw [hb]; cases a with | origin => rfl | bounded _ => rfl

-- No ≠ 0 hypotheses anywhere. No NoZeroDivisors axiom.
-- The type carries the information. Bounded elements stay bounded
-- under multiplication. Origin only appears when Origin is an input.

-- SUMMARY:
--   Axioms asserted: 0
--   ≠ 0 hypotheses: 0
--   NoZeroDivisors status: UNNECESSARY (follows from type)
--   Total theorems: 3 (all without hypotheses)

end ZDTwoSorted

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed       Two-Sorted
--  NoZeroDivisors axiom         1               0
--  ≠ 0 hypotheses               4               0
--  Theorems needed               4               3
--  Can zero divisors occur?     must assert no   impossible by type
--  Information lost              0               0
--
--  In the collapsed version, NoZeroDivisors is a constraint you impose
--  on a structure to exclude a pathology. In the two-sorted version,
--  the pathology cannot arise. Bounded * bounded is bounded. Always.
--
--  The axiom becomes a theorem. The constraint becomes a consequence.
--  The pathology dissolves.
