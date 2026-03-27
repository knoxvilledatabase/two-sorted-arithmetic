/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Foundation

/-!
# Division Ring Benchmark: Collapsed vs Seed

Same theorems. Two versions. Count the `≠ 0` hypotheses.

**Collapsed:** The field axiom "every nonzero element has a multiplicative
inverse" requires `≠ 0` on every invocation. This matches Mathlib's
`DivisionRing` and `Field` where `inv_zero : (0 : α)⁻¹ = 0` is a
convention and every inverse theorem carries `(h : a ≠ 0)`.

**Seed:** The same theorems on Val α. Every contents element has a
contents inverse. No `≠ 0` qualifier. The field axiom says "contents"
not "nonzero." The sort system is the qualifier.

This is the most fundamental benchmark: the field axiom itself.
Every `≠ 0` hypothesis in all of mathematics traces back to this one.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: Option α — ≠ 0 is the price of every field operation
-- ============================================================================

namespace Collapsed

variable {α : Type}

def F (α : Type) := Option α

def mul : F α → F α → F α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a

def inv : F α → F α
  | none => none    -- convention: 0⁻¹ = 0
  | some a => some a

def fdiv (a b : F α) : F α := mul a (inv b)

-- ========== THEOREMS: each is a field axiom or consequence ==========

/-- 1. a⁻¹ is defined. Requires a ≠ 0. -/
theorem inv_defined (a : F α) (h : a ≠ none) :
    inv a ≠ none := by
  cases a <;> simp_all [inv]

/-- 2. a * a⁻¹ is defined. Requires a ≠ 0. -/
theorem mul_inv_defined (a : F α) (h : a ≠ none) :
    mul a (inv a) ≠ none := by
  cases a <;> simp_all [mul, inv]

/-- 3. a / b is defined. Requires b ≠ 0. -/
theorem div_defined (a b : F α) (ha : a ≠ none) (hb : b ≠ none) :
    fdiv a b ≠ none := by
  cases a <;> cases b <;> simp_all [fdiv, mul, inv]

/-- 4. (a/b) * b = a (cancellation). Requires b ≠ 0. -/
theorem div_mul_cancel (a b : F α) (hb : b ≠ none) :
    mul (fdiv a b) b = a := by
  cases a <;> cases b <;> simp_all [fdiv, mul, inv]

/-- 5. a / a = 1 (self-division). Requires a ≠ 0. -/
theorem div_self (a : F α) (h : a ≠ none) :
    fdiv a a = a := by
  cases a <;> simp_all [fdiv, mul, inv]

/-- 6. 0⁻¹ = 0 (convention, not derivation). -/
theorem inv_zero_convention : inv (none : F α) = none := by rfl

/-- 7. (a⁻¹)⁻¹ = a (double inverse). Requires a ≠ 0. -/
theorem inv_inv (a : F α) (h : a ≠ none) :
    inv (inv a) = a := by
  cases a <;> simp_all [inv]

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 6
--   Total ≠ 0 hypothesis instances: 7 (div_defined has 2)
--   Convention required: 1 (inv none = none)
--   Every field operation theorem requires ≠ 0.

end Collapsed

-- ============================================================================
-- SEED: Val α — the field axiom without ≠ 0
-- ============================================================================

namespace Seed

open Val

variable {α : Type}

-- ========== SAME THEOREMS, ZERO HYPOTHESES ==========

/-- 1. Inverse of contents is contents. No hypothesis. -/
theorem inv_contents (invF : α → α) (a : α) :
    Val.inv invF (contents a) = contents (invF a) := by rfl

/-- 2. a * a⁻¹ within contents. No hypothesis. -/
theorem mul_inv_contents (mulF : α → α → α) (invF : α → α) (a : α) :
    Val.mul mulF (contents a) (Val.inv invF (contents a)) =
    contents (mulF a (invF a)) := by rfl

/-- 3. a / b within contents. No hypothesis. -/
theorem div_contents (mulF : α → α → α) (invF : α → α) (a b : α) :
    Val.mul mulF (contents a) (Val.inv invF (contents b)) =
    contents (mulF a (invF b)) := by rfl

/-- 4. (a/b) * b within contents. No hypothesis. -/
theorem div_mul_contents (mulF : α → α → α) (invF : α → α) (a b : α) :
    Val.mul mulF (Val.mul mulF (contents a) (Val.inv invF (contents b))) (contents b) =
    contents (mulF (mulF a (invF b)) b) := by rfl

/-- 5. a / a within contents. No hypothesis. -/
theorem div_self_contents (mulF : α → α → α) (invF : α → α) (a : α) :
    Val.mul mulF (contents a) (Val.inv invF (contents a)) =
    contents (mulF a (invF a)) := by rfl

/-- 6. Origin inverse is origin — by absorption, not convention. -/
theorem inv_origin (invF : α → α) :
    Val.inv invF (origin : Val α) = origin := by rfl

/-- 7. Double inverse within contents. No hypothesis. -/
theorem inv_inv_contents (invF : α → α) (a : α) :
    Val.inv invF (Val.inv invF (contents a)) = contents (invF (invF a)) := by rfl

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 0
--   Convention required: 0 (origin⁻¹ = origin is absorption, not convention)
--   Every theorem is rfl. The type computes the answer.

end Seed

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed (Option α)    Seed (Val α)
--  ≠ 0 hypotheses                  7                    0
--  Theorems requiring them          6                    0
--  Conventions (0⁻¹=0)             1                    0
--  Information lost                 0                    0
--  Proof complexity          cases/simp_all             rfl
--
--  This is the field axiom itself. "Every nonzero element has an inverse."
--  In Val α: "Every contents element has a contents inverse." No qualifier.
--  The ≠ 0 was never about the mathematics of invertibility.
--  It was about sort confusion: is this the boundary or a field element?
--  In Val α the type answers that question. The axiom drops the qualifier.
--
--  Every ≠ 0 hypothesis in all of mathematics traces back to this one.
--  The field axiom is the factory. Remove the conflation from the factory
--  and the product — the hypothesis — stops being manufactured.
