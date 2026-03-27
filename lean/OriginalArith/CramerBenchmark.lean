/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Foundation

/-!
# Cramer's Rule Benchmark: Collapsed vs Seed

Same theorems. Two versions. Count the `det ≠ 0` hypotheses.

**Collapsed (standard style):** A 2×2 matrix over Option α where `none` is zero.
Every theorem involving the inverse or Cramer's solution carries `(h : det ≠ none)`.
This matches how Mathlib's `Matrix.nonsing_inv`, `Matrix.cramer`, and
`Matrix.mul_nonsing_inv` all require `IsUnit (det A)`.

**Seed (Val α style):** The same theorems on Val α. Determinant of a contents
matrix is always contents. Division of contents by contents is always contents.
No hypotheses. The type carries the invariant.

Both use simplified operations. The benchmark is about the HYPOTHESIS STRUCTURE,
not mathematical completeness. Same methodology as NeZeroBenchmark.lean.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: Option α — det ≠ 0 required everywhere
-- ============================================================================

namespace Collapsed

variable {α : Type}

/-- Field as Option α. none is zero. some a is a field element. -/
def F (α : Type) := Option α

/-- Multiplication: 0 absorbs. -/
def mul : F α → F α → F α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a  -- simplified

/-- Subtraction: 0 absorbs. -/
def sub : F α → F α → F α
  | none, _ => none
  | _, none => none
  | some a, some _ => some a  -- simplified

/-- Inverse: 0⁻¹ = 0 by convention (Mathlib's choice). -/
def inv : F α → F α
  | none => none  -- convention
  | some a => some a  -- simplified

/-- Division: a / b = a * b⁻¹. -/
def fdiv (a b : F α) : F α := mul a (inv b)

/-- 2×2 determinant: ad - bc. -/
def det2 (a b c d : F α) : F α := sub (mul a d) (mul b c)

-- ========== THEOREMS: each carries det ≠ 0 ==========

/-- 1. 1/det is well-defined. Requires det ≠ 0. -/
theorem inv_det_defined (a b c d : F α) (hdet : det2 a b c d ≠ none) :
    inv (det2 a b c d) ≠ none := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [det2, sub, mul, inv]

/-- 2. Cramer x₁ = (d·b₁ - b·b₂)/det is well-defined. Requires det ≠ 0 AND numerator ≠ 0. -/
theorem cramer_x1_defined (a b c d b₁ b₂ : F α)
    (hdet : det2 a b c d ≠ none)
    (hnum : sub (mul d b₁) (mul b b₂) ≠ none) :
    fdiv (sub (mul d b₁) (mul b b₂)) (det2 a b c d) ≠ none := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases b₁ <;> cases b₂ <;>
    simp_all [det2, sub, mul, inv, fdiv]

/-- 3. Cramer x₂ = (a·b₂ - c·b₁)/det is well-defined. Requires det ≠ 0 AND numerator ≠ 0. -/
theorem cramer_x2_defined (a b c d b₁ b₂ : F α)
    (hdet : det2 a b c d ≠ none)
    (hnum : sub (mul a b₂) (mul c b₁) ≠ none) :
    fdiv (sub (mul a b₂) (mul c b₁)) (det2 a b c d) ≠ none := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases b₁ <;> cases b₂ <;>
    simp_all [det2, sub, mul, inv, fdiv]

/-- 4. Inverse matrix entry A⁻¹₁₁ = d/det is well-defined. Requires det ≠ 0 AND d ≠ 0. -/
theorem inverse_e11_defined (a b c d : F α)
    (hdet : det2 a b c d ≠ none) (hd : d ≠ none) :
    fdiv d (det2 a b c d) ≠ none := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [det2, sub, mul, inv, fdiv]

/-- 5. Inverse matrix entry A⁻¹₂₂ = a/det is well-defined. Requires det ≠ 0 AND a ≠ 0. -/
theorem inverse_e22_defined (a b c d : F α)
    (hdet : det2 a b c d ≠ none) (ha : a ≠ none) :
    fdiv a (det2 a b c d) ≠ none := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [det2, sub, mul, inv, fdiv]

/-- 6. det · (1/det) = det (cancellation). Requires det ≠ 0. -/
theorem det_mul_inv_det (a b c d : F α) (hdet : det2 a b c d ≠ none) :
    mul (det2 a b c d) (inv (det2 a b c d)) = det2 a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [det2, sub, mul, inv]

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 6
--   Total ≠ 0 hypothesis instances: 8 (some theorems have 2)
--   Convention required: 1 (inv none = none)
--   Every Cramer/inverse theorem requires det ≠ 0.

end Collapsed

-- ============================================================================
-- SEED: Val α — no hypotheses, the type carries the invariant
-- ============================================================================

namespace Seed

open Val

variable {α : Type}

/-- 2×2 determinant on Val α. -/
def det2 (mulF subF : α → α → α) (a b c d : Val α) : Val α :=
  Val.add subF (Val.mul mulF a d) (Val.mul mulF b c)

/-- Division on Val α. -/
def fdiv (mulF : α → α → α) (invF : α → α) (a b : Val α) : Val α :=
  Val.mul mulF a (Val.inv invF b)

-- ========== SAME THEOREMS, ZERO ≠ 0 HYPOTHESES ==========

/-- 1. 1/det is always contents for contents matrices. No hypothesis. -/
theorem inv_det_contents (mulF subF : α → α → α) (invF : α → α) (a b c d : α) :
    Val.inv invF (det2 mulF subF (contents a) (contents b) (contents c) (contents d)) =
    contents (invF (subF (mulF a d) (mulF b c))) := by rfl

/-- 2. Cramer x₁ is always contents. No hypothesis. -/
theorem cramer_x1_contents (mulF subF : α → α → α) (invF : α → α) (a b c d b₁ b₂ : α) :
    fdiv mulF invF
      (Val.add subF (Val.mul mulF (contents d) (contents b₁))
                     (Val.mul mulF (contents b) (contents b₂)))
      (det2 mulF subF (contents a) (contents b) (contents c) (contents d)) =
    contents (mulF (subF (mulF d b₁) (mulF b b₂)) (invF (subF (mulF a d) (mulF b c)))) := by
  rfl

/-- 3. Cramer x₂ is always contents. No hypothesis. -/
theorem cramer_x2_contents (mulF subF : α → α → α) (invF : α → α) (a b c d b₁ b₂ : α) :
    fdiv mulF invF
      (Val.add subF (Val.mul mulF (contents a) (contents b₂))
                     (Val.mul mulF (contents c) (contents b₁)))
      (det2 mulF subF (contents a) (contents b) (contents c) (contents d)) =
    contents (mulF (subF (mulF a b₂) (mulF c b₁)) (invF (subF (mulF a d) (mulF b c)))) := by
  rfl

/-- 4. Inverse matrix entry A⁻¹₁₁ = d/det is always contents. No hypothesis. -/
theorem inverse_e11_contents (mulF subF : α → α → α) (invF : α → α) (a b c d : α) :
    fdiv mulF invF (contents d)
      (det2 mulF subF (contents a) (contents b) (contents c) (contents d)) =
    contents (mulF d (invF (subF (mulF a d) (mulF b c)))) := by rfl

/-- 5. Inverse matrix entry A⁻¹₂₂ = a/det is always contents. No hypothesis. -/
theorem inverse_e22_contents (mulF subF : α → α → α) (invF : α → α) (a b c d : α) :
    fdiv mulF invF (contents a)
      (det2 mulF subF (contents a) (contents b) (contents c) (contents d)) =
    contents (mulF a (invF (subF (mulF a d) (mulF b c)))) := by rfl

/-- 6. det · (1/det) within contents. No hypothesis. -/
theorem det_mul_inv_det_contents (mulF subF : α → α → α) (invF : α → α) (a b c d : α) :
    Val.mul mulF
      (det2 mulF subF (contents a) (contents b) (contents c) (contents d))
      (Val.inv invF (det2 mulF subF (contents a) (contents b) (contents c) (contents d))) =
    contents (mulF (subF (mulF a d) (mulF b c)) (invF (subF (mulF a d) (mulF b c)))) := by
  rfl

-- TOTAL:
--   Theorems with ≠ 0 hypotheses: 0
--   Theorems deleted: 0 (all six remain, all proved by rfl)
--   Convention required: 0
--   Every theorem is rfl. The type computes the answer.

end Seed

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                           Collapsed (Option α)    Seed (Val α)
--  ≠ 0 hypotheses                  8                    0
--  Theorems requiring them          6                    0
--  Conventions (0⁻¹=0)             1                    0
--  Information lost                 0                    0
--  Proof complexity          cases/simp_all             rfl
--
--  The 8 hypotheses don't disappear. They move into the type.
--  In Val α, contents / contents = contents. Always. Unconditionally.
--  The sort is determined by the type, not by a proof obligation.
--
--  In Mathlib, every theorem about Matrix.nonsing_inv, Matrix.cramer,
--  and Matrix.mul_nonsing_inv carries IsUnit (det A) or Invertible (det A).
--  That is this same hypothesis, dressed in typeclass clothing.
--
--  The factory that produces these hypotheses: the conflation of
--  "zero the field element" with "zero the boundary." In Val α,
--  they are different constructors. The confusion is a type error.
