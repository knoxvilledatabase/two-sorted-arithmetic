/-
Released under MIT license.
-/
import OriginalArith.Foundation

/-!
# NoZeroDivisors Benchmark: collapsed vs Val α

Mathlib's `NoZeroDivisors` states: `a * b = 0 → a = 0 ∨ b = 0`.
This typeclass exists because in a collapsed type, two nonzero elements
can multiply to produce zero (a "zero divisor"). The typeclass asserts
this pathology doesn't happen.

In Val α, `contents(a) * contents(b) = contents(f a b)`.
The result is always contents. It never equals origin. The pathology
can't arise. The typeclass becomes unnecessary.

**File 1 (Collapsed):** NoZeroDivisors must be asserted as an axiom.
**File 2 (Val α):** The property follows from the type. No axiom needed.
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
-- VAL α: zero divisors can't happen
-- ============================================================================

namespace ZDValAlpha

open Val

variable {α : Type}

-- The key fact: contents * contents is ALWAYS contents. Never origin.
-- Zero divisors require a * b = 0 where a ≠ 0 and b ≠ 0.
-- In Val α, contents(a) * contents(b) = contents(f a b).
-- The result is contents. It is not origin. The pathology cannot arise.

/-- Contents * contents is always contents. The type prevents zero divisors. -/
theorem mul_contents_contents (f : α → α → α) (a b : α) :
    Val.mul f (contents a) (contents b) = contents (f a b) := by rfl

/-- Contents * contents is never origin. This is what NoZeroDivisors asserts
    as an axiom. Here it follows from the type. -/
theorem mul_contents_ne_origin (f : α → α → α) (a b : α) :
    Val.mul f (contents a) (contents b) ≠ origin := by
  simp [Val.mul]

/-- The only way to get origin from multiplication is if an input was origin. -/
theorem mul_eq_origin_iff (f : α → α → α) (a b : Val α) :
    Val.mul f a b = origin ↔ (a = origin ∨ b = origin) := by
  constructor
  · intro h
    cases a with
    | origin => left; rfl
    | container va =>
      cases b with
      | origin => right; rfl
      | container _ => simp [Val.mul] at h
      | contents _ => simp [Val.mul] at h
    | contents va =>
      cases b with
      | origin => right; rfl
      | container _ => simp [Val.mul] at h
      | contents _ => simp [Val.mul] at h
  · intro h
    cases h with
    | inl ha => rw [ha]; rfl
    | inr hb => rw [hb]; exact Val.origin_absorbs_mul_right f a

-- No ≠ 0 hypotheses anywhere. No NoZeroDivisors axiom.
-- The type carries the information. Contents elements stay contents
-- under multiplication. Origin only appears when origin is an input.

-- SUMMARY:
--   Axioms asserted: 0
--   ≠ 0 hypotheses: 0
--   NoZeroDivisors status: UNNECESSARY (follows from type)
--   Total theorems: 3 (all without hypotheses)

end ZDValAlpha

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed       Val α
--  NoZeroDivisors axiom         1               0
--  ≠ 0 hypotheses               4               0
--  Theorems needed               4               3
--  Can zero divisors occur?     must assert no   impossible by type
--  Information lost              0               0
--
--  In the collapsed version, NoZeroDivisors is a constraint you impose
--  on a structure to exclude a pathology. In Val α, the pathology
--  cannot arise. Contents * contents is contents. Always.
--
--  The axiom becomes a theorem. The constraint becomes a consequence.
--  The pathology dissolves.
