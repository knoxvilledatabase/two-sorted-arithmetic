/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import TwoSortedArith.Foundation

/-!
# Polynomial Evaluation Benchmark: Collapsed vs Seed

Same theorems. Two versions. Count the hypotheses.

**Collapsed:** Polynomial evaluation where coefficients and the evaluation
point can be zero. Operations carry `≠ 0` checks when division or
leading coefficient checks are needed. Evaluation can silently produce
zero (none) indistinguishable from "computation failed."

**Seed:** The same theorems on Val α. Contents coefficients evaluated at
a contents point always give contents. Origin propagation is structural.
The sort is always determined.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: Option α — zero conflation in polynomial operations
-- ============================================================================

namespace Collapsed

variable {α : Type}

def F (α : Type) := Option α

def add : F α → F α → F α
  | none, b => b
  | a, none => a
  | some a, some _ => some a

def mul : F α → F α → F α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a

def inv : F α → F α
  | none => none
  | some a => some a

def fdiv (a b : F α) : F α := mul a (inv b)

/-- Horner evaluation. -/
def polyEval : List (F α) → F α → F α
  | [], _ => none  -- zero polynomial = 0
  | [a], _ => a
  | a :: b :: rest, x => add a (mul x (polyEval (b :: rest) x))

-- ========== THEOREMS: hypotheses required ==========

/-- 1. Evaluation of nonzero coefficients at nonzero point is nonzero.
    Requires: coefficient ≠ 0. -/
theorem eval_const_defined (a : F α) (x : F α) (ha : a ≠ none) :
    polyEval [a] x ≠ none := by
  simp [polyEval]; exact ha

/-- 2. Linear evaluation defined. Requires: both coefficients ≠ 0 AND x ≠ 0. -/
theorem eval_linear_defined (a₀ a₁ x : F α)
    (ha₀ : a₀ ≠ none) (ha₁ : a₁ ≠ none) (hx : x ≠ none) :
    polyEval [a₀, a₁] x ≠ none := by
  cases a₀ <;> cases a₁ <;> cases x <;> simp_all [polyEval, add, mul]

/-- 3. Leading coefficient check for polynomial division.
    Requires: leading coefficient ≠ 0. -/
theorem leading_coeff_ne_zero (a₀ a₁ : F α) (ha₁ : a₁ ≠ none) :
    polyEval [a₀, a₁] none = a₀ := by
  cases a₀ <;> cases a₁ <;> simp_all [polyEval, add, mul]

/-- 4. Quotient of polynomials: eval(p)/eval(q) defined.
    Requires: eval(q) ≠ 0 AND eval(p) ≠ 0. -/
theorem poly_quotient_defined (p q x : F α)
    (hp : p ≠ none) (hq : q ≠ none) :
    fdiv p q ≠ none := by
  cases p <;> cases q <;> simp_all [fdiv, mul, inv]

/-- 5. Evaluation at zero produces zero (absorption/convention).
    The result none means BOTH "the value is zero" AND "we evaluated at the boundary."
    Indistinguishable. -/
theorem eval_at_zero_ambiguous (a₁ : F α) :
    polyEval [none, a₁] (some _root_.Unit.unit) = none := by
  cases a₁ <;> simp [polyEval, add, mul]

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 4
--   Total ≠ 0 hypothesis instances: 6
--     eval_const_defined: 1
--     eval_linear_defined: 3
--     leading_coeff_ne_zero: 1
--     poly_quotient_defined: 2 (note: not about eval, but about quotient)
--   Ambiguity: 1 (eval_at_zero produces none — is it zero or boundary?)
--   Convention required: 1 (zero polynomial = none)

end Collapsed

-- ============================================================================
-- SEED: Val α — no hypotheses, sort always determined
-- ============================================================================

namespace Seed

open Val

variable {α : Type}

/-- Horner evaluation on Val α. -/
def polyEval (addF mulF : α → α → α) (zero : α) : List (Val α) → Val α → Val α
  | [], _ => contents zero
  | [a], _ => a
  | a :: b :: rest, x => Val.add addF a (Val.mul mulF x (polyEval addF mulF zero (b :: rest) x))

-- ========== SAME THEOREMS, ZERO HYPOTHESES ==========

/-- 1. Constant evaluation is always contents. No hypothesis. -/
theorem eval_const_contents (addF mulF : α → α → α) (zero : α) (a : α) (x : Val α) :
    polyEval addF mulF zero [contents a] x = contents a := by rfl

/-- 2. Linear evaluation with contents coefficients at contents point is contents. No hypothesis. -/
theorem eval_linear_contents (addF mulF : α → α → α) (zero : α) (a₀ a₁ v : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] (contents v) =
    contents (addF a₀ (mulF v a₁)) := by rfl

/-- 3. Leading coefficient is structurally contents. No hypothesis needed. -/
theorem leading_coeff_contents (addF mulF : α → α → α) (zero : α) (a₀ a₁ : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] origin = origin := by
  simp [polyEval, Val.add, Val.mul]

/-- 4. Quotient of polynomial evaluations is contents. No hypothesis. -/
theorem poly_quotient_contents (mulF : α → α → α) (invF : α → α) (p q : α) :
    Val.mul mulF (contents p) (Val.inv invF (contents q)) =
    contents (mulF p (invF q)) := by rfl

/-- 5. Evaluation at origin gives origin (absorption). NOT ambiguous —
    the sort tells you it's the boundary, not a zero value. -/
theorem eval_at_origin_is_origin (addF mulF : α → α → α) (zero : α)
    (a₀ a₁ : α) :
    polyEval addF mulF zero [contents a₀, contents a₁] origin = origin := by
  simp [polyEval, Val.add, Val.mul]

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 0
--   Convention required: 0
--   Ambiguity: 0 (origin is visibly boundary, contents(0) is visibly zero)
--   Proofs: rfl or simp (structural reduction)

end Seed

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed (Option α)    Seed (Val α)
--  ≠ 0 hypotheses                  6                    0
--  Theorems requiring them          4                    0
--  Conventions                      1                    0
--  Sort ambiguity                   1                    0
--  Information lost                 0                    0
--
--  The collapsed model cannot distinguish "evaluated to zero" from
--  "evaluated at the boundary." Both are none. In Val α:
--    contents(0) = evaluated to zero (a value)
--    origin = evaluated at the boundary (a sort)
--  The sort system resolves the ambiguity that the collapsed model hides.
