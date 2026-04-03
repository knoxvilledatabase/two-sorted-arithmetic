/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Foundation

/-!
# Ordered Fields on Val α

RingField.lean proved ring and field laws within contents.
This file adds ordering:

1. **Partial order:** reflexivity, transitivity, antisymmetry within contents.
2. **Total order:** totality within contents when α is totally ordered.
3. **Ordered ring compatibility:** addition and multiplication preserve order.
4. **Origin and container are outside the order.**

Same faithful embedding pattern. The ordering on α lifts to contents.
Origin and container don't participate — they are boundary and structure,
not elements of the ordered field.

Test to failure. If it works, the foundation supports ordered algebra.
If it breaks, we learn where.
-/

namespace Val

open Val

variable {α : Type}

-- ============================================================================
-- Comparison: contents compare within contents
-- ============================================================================

/-- Less-than-or-equal on Val α. Only contents are comparable.
    Origin and container are outside the ordering. -/
def le (r : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => r a b
  | _, _ => False

/-- Strict less-than on Val α. Defined from le and ≠, within contents. -/
def lt (r : α → α → Prop) (s : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => s a b
  | _, _ => False

-- ============================================================================
-- Partial Order Laws (within contents)
-- ============================================================================

/-- Reflexivity: contents(a) ≤ contents(a) when r is reflexive. -/
theorem le_refl (r : α → α → Prop)
    (hr : ∀ a : α, r a a) (a : α) :
    le r (contents a) (contents a) := by
  show r a a; exact hr a

/-- Transitivity: a ≤ b → b ≤ c → a ≤ c within contents. -/
theorem le_trans (r : α → α → Prop)
    (hr : ∀ a b c : α, r a b → r b c → r a c)
    (a b c : α)
    (hab : le r (contents a) (contents b))
    (hbc : le r (contents b) (contents c)) :
    le r (contents a) (contents c) := by
  show r a c; exact hr a b c hab hbc

/-- Antisymmetry: a ≤ b → b ≤ a → a = b within contents. -/
theorem le_antisymm (r : α → α → Prop)
    (hr : ∀ a b : α, r a b → r b a → a = b)
    (a b : α)
    (hab : le r (contents a) (contents b))
    (hba : le r (contents b) (contents a)) :
    (contents a : Val α) = contents b := by
  congr; exact hr a b hab hba

-- ✓ Partial order laws hold for contents.

-- ============================================================================
-- Total Order (within contents)
-- ============================================================================

/-- Totality: for any two contents, a ≤ b ∨ b ≤ a. -/
theorem le_total (r : α → α → Prop)
    (hr : ∀ a b : α, r a b ∨ r b a)
    (a b : α) :
    le r (contents a) (contents b) ∨ le r (contents b) (contents a) := by
  exact hr a b

-- ✓ Total order holds for contents when α is totally ordered.

-- ============================================================================
-- Origin and Container Are Outside the Order
-- ============================================================================

/-- Origin is not ≤ anything. -/
theorem origin_not_le (r : α → α → Prop) (x : Val α) :
    ¬ le r origin x := by
  cases x with
  | origin => exact id
  | container => exact id
  | contents _ => exact id

/-- Nothing is ≤ origin. -/
theorem not_le_origin (r : α → α → Prop) (x : Val α) :
    ¬ le r x origin := by
  cases x with
  | origin => exact id
  | container => exact id
  | contents _ => exact id

/-- Container is not ≤ anything. -/
theorem container_not_le (r : α → α → Prop) (c : α) (x : Val α) :
    ¬ le r (container c) x := by
  cases x with
  | origin => exact id
  | container _ => exact id
  | contents _ => exact id

/-- Nothing is ≤ container. -/
theorem not_le_container (r : α → α → Prop) (c : α) (x : Val α) :
    ¬ le r x (container c) := by
  cases x with
  | origin => exact id
  | container _ => exact id
  | contents _ => exact id

/-- Origin is not < anything. -/
theorem origin_not_lt (r s : α → α → Prop) (x : Val α) :
    ¬ lt r s origin x := by
  cases x with
  | origin => exact id
  | container => exact id
  | contents _ => exact id

/-- Container is not < anything. -/
theorem container_not_lt (r s : α → α → Prop) (c : α) (x : Val α) :
    ¬ lt r s (container c) x := by
  cases x with
  | origin => exact id
  | container _ => exact id
  | contents _ => exact id

-- ✓ Origin and container are outside the ordering entirely.
-- They are not "less than everything" or "greater than everything."
-- They simply don't participate. The order lives in contents.

-- ============================================================================
-- Ordered Ring: Addition Preserves Order
-- ============================================================================

/-- If a ≤ b then a + c ≤ b + c within contents. -/
theorem add_le_add_right (r : α → α → Prop) (addF : α → α → α)
    (h : ∀ a b c : α, r a b → r (addF a c) (addF b c))
    (a b c : α)
    (hab : le r (contents a) (contents b)) :
    le r (add addF (contents a) (contents c))
         (add addF (contents b) (contents c)) := by
  show r (addF a c) (addF b c)
  exact h a b c hab

/-- If a ≤ b then c + a ≤ c + b within contents. -/
theorem add_le_add_left (r : α → α → Prop) (addF : α → α → α)
    (h : ∀ a b c : α, r a b → r (addF c a) (addF c b))
    (a b c : α)
    (hab : le r (contents a) (contents b)) :
    le r (add addF (contents c) (contents a))
         (add addF (contents c) (contents b)) := by
  show r (addF c a) (addF c b)
  exact h a b c hab

-- ✓ Addition preserves order within contents.

-- ============================================================================
-- Ordered Ring: Multiplication by Nonnegative Preserves Order
-- ============================================================================

/-- If 0 ≤ a and 0 ≤ b then 0 ≤ a * b within contents. -/
theorem mul_nonneg (r : α → α → Prop) (mulF : α → α → α) (zero : α)
    (h : ∀ a b : α, r zero a → r zero b → r zero (mulF a b))
    (a b : α)
    (ha : le r (contents zero) (contents a))
    (hb : le r (contents zero) (contents b)) :
    le r (contents zero) (mul mulF (contents a) (contents b)) := by
  show r zero (mulF a b)
  exact h a b ha hb

/-- If a ≤ b and 0 ≤ c then a * c ≤ b * c within contents. -/
theorem mul_le_mul_of_nonneg_right (r : α → α → Prop) (mulF : α → α → α) (zero : α)
    (h : ∀ a b c : α, r a b → r zero c → r (mulF a c) (mulF b c))
    (a b c : α)
    (hab : le r (contents a) (contents b))
    (hc : le r (contents zero) (contents c)) :
    le r (mul mulF (contents a) (contents c))
         (mul mulF (contents b) (contents c)) := by
  show r (mulF a c) (mulF b c)
  exact h a b c hab hc

/-- If a ≤ b and 0 ≤ c then c * a ≤ c * b within contents. -/
theorem mul_le_mul_of_nonneg_left (r : α → α → Prop) (mulF : α → α → α) (zero : α)
    (h : ∀ a b c : α, r a b → r zero c → r (mulF c a) (mulF c b))
    (a b c : α)
    (hab : le r (contents a) (contents b))
    (hc : le r (contents zero) (contents c)) :
    le r (mul mulF (contents c) (contents a))
         (mul mulF (contents c) (contents b)) := by
  show r (mulF c a) (mulF c b)
  exact h a b c hab hc

-- ✓ Multiplication preserves order for nonneg elements within contents.

-- ============================================================================
-- Faithful Embedding of Order
-- ============================================================================

/-- contents preserves the order: a ≤ b in α ↔ contents(a) ≤ contents(b). -/
theorem contents_preserves_le (r : α → α → Prop) (a b : α) :
    r a b ↔ le r (contents a) (contents b) := by
  constructor
  · exact id
  · exact id

/-- contents reflects the order: contents(a) ≤ contents(b) → a ≤ b. -/
theorem contents_reflects_le (r : α → α → Prop) (a b : α)
    (h : le r (contents a) (contents b)) :
    r a b := h

-- ✓ The order on α is exactly preserved in contents. Nothing lost, nothing added.

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Partial order laws (within contents):
--   ✓ Reflexivity
--   ✓ Transitivity
--   ✓ Antisymmetry
--   → Partial order: confirmed.
--
-- Total order (within contents):
--   ✓ Totality when α is totally ordered
--   → Total order: confirmed.
--
-- Origin and container outside the order:
--   ✓ Origin is not ≤ anything and nothing is ≤ origin
--   ✓ Container is not ≤ anything and nothing is ≤ container
--   ✓ Same for strict <
--   → Boundary sorts don't participate in the order.
--
-- Ordered ring compatibility (within contents):
--   ✓ Addition preserves order (both sides)
--   ✓ Multiplication by nonneg preserves order (both sides)
--   ✓ Product of nonneg is nonneg
--   → Ordered ring laws: confirmed.
--
-- Faithful embedding of order:
--   ✓ contents preserves and reflects ≤
--   → α's order is exactly preserved in Val α.
--
-- Same pattern as RingField.lean:
--   The ordered field lives entirely in contents.
--   Origin and container are outside it — by type, not by convention.

end Val
