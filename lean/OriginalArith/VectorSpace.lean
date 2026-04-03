/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Foundation

/-!
# Vector Spaces and Modules on Val α

RingField.lean proved the field lives in contents.
OrderedField.lean proved the order lives in contents.
This file proves scalar multiplication works with Val α scalars.

1. **Scalar multiplication:** `Val α` scalars act on `Val β` vectors.
   Same absorption pattern. Origin absorbs. Container absorbs.
   Contents scale within contents.

2. **Module laws:** distributivity, associativity, identity — all within
   contents when the underlying operations satisfy them.

The field lives in contents. So scalar multiplication works within contents.
Expected: clean, same faithful embedding pattern.

Test to failure.
-/

namespace Val

open Val

variable {α β : Type}

-- ============================================================================
-- Scalar Multiplication: Val α scalars acting on Val β vectors
-- ============================================================================

/-- Scalar multiplication on Val. Scalars from Val α, vectors from Val β.
    Same absorption pattern as mul:
    - origin scalar or origin vector → origin (absorption)
    - container scalar or container vector → container (structural)
    - contents scalar × contents vector → contents (actual scaling) -/
def smul (f : α → β → β) : Val α → Val β → Val β
  | origin, _                  => origin
  | _, origin                  => origin
  | container a, container b   => container (f a b)
  | container a, contents b    => container (f a b)
  | contents a, container b    => container (f a b)
  | contents a, contents v     => contents (f a v)

-- ============================================================================
-- Absorption: origin absorbs scalar multiplication
-- ============================================================================

/-- Origin scalar absorbs: 𝒪 • v = 𝒪 -/
theorem origin_smul {β : Type} (f : α → β → β) (v : Val β) :
    smul f (origin : Val α) v = origin := by rfl

/-- Origin vector absorbs: a • 𝒪 = 𝒪 -/
theorem smul_origin {β : Type} (f : α → β → β) (a : Val α) :
    smul f a (origin : Val β) = origin := by
  cases a with | origin => rfl | container _ => rfl | contents _ => rfl

-- ✓ Origin absorbs from both sides. Same as mul.

-- ============================================================================
-- Container: structural under scalar multiplication
-- ============================================================================

/-- Container scalar × container vector = container (values combine). -/
theorem container_smul_container {β : Type} (f : α → β → β) (a : α) (b : β) :
    smul f (container a) (container b) = container (f a b) := by rfl

/-- Container scalar × contents vector = container (values combine). -/
theorem container_smul_contents {β : Type} (f : α → β → β) (a : α) (v : β) :
    smul f (container a) (contents v) = container (f a v) := by rfl

/-- Contents scalar × container vector = container (values combine). -/
theorem contents_smul_container {β : Type} (f : α → β → β) (a : α) (b : β) :
    smul f (contents a) (container b) = container (f a b) := by rfl

-- ✓ Container is structural under smul. Same pattern.

-- ============================================================================
-- Contents closure: scalar multiplication stays in contents
-- ============================================================================

/-- Contents scalar × contents vector = contents (actual scaling). -/
theorem contents_smul_contents {β : Type} (f : α → β → β) (a : α) (v : β) :
    smul f (contents a) (contents v) = contents (f a v) := by rfl

/-- Scalar multiplication of contents never produces origin. -/
theorem contents_smul_ne_origin {β : Type} (f : α → β → β) (a : α) (v : β) :
    smul f (contents a) (contents v) ≠ (origin : Val β) := by simp [smul]

/-- Scalar multiplication of contents never produces container. -/
theorem contents_smul_ne_container {β : Type} (f : α → β → β) (a : α) (v : β) (c : β) :
    smul f (contents a) (contents v) ≠ (container c : Val β) := by simp [smul]

-- ✓ Contents are closed under scalar multiplication. Never leave contents.

-- ============================================================================
-- Module Law 1: Scalar multiplication distributes over vector addition
-- a • (v + w) = a • v + a • w
-- ============================================================================

/-- Scalar distributes over vector addition within contents. -/
theorem smul_add {β : Type} (scaleF : α → β → β) (addF : β → β → β)
    (h : ∀ (a : α) (v w : β), scaleF a (addF v w) = addF (scaleF a v) (scaleF a w))
    (a : α) (v w : β) :
    smul scaleF (contents a) (add addF (contents v) (contents w)) =
    add addF (smul scaleF (contents a) (contents v))
             (smul scaleF (contents a) (contents w)) := by
  simp [smul, add, h]

-- ✓ Scalar distributes over vector addition.

-- ============================================================================
-- Module Law 2: Scalar addition distributes over scalar multiplication
-- (a + b) • v = a • v + b • v
-- ============================================================================

/-- Scalar addition distributes over scalar multiplication within contents. -/
theorem add_smul {β : Type} (scaleF : α → β → β) (addA : α → α → α) (addB : β → β → β)
    (h : ∀ (a b : α) (v : β), scaleF (addA a b) v = addB (scaleF a v) (scaleF b v))
    (a b : α) (v : β) :
    smul scaleF (add addA (contents a) (contents b)) (contents v) =
    add addB (smul scaleF (contents a) (contents v))
             (smul scaleF (contents b) (contents v)) := by
  simp [smul, add, h]

-- ✓ Scalar addition distributes over scalar multiplication.

-- ============================================================================
-- Module Law 3: Associativity of scalar multiplication
-- (a * b) • v = a • (b • v)
-- ============================================================================

/-- Scalar multiplication is associative within contents. -/
theorem smul_assoc {β : Type} (scaleF : α → β → β) (mulF : α → α → α)
    (h : ∀ (a b : α) (v : β), scaleF (mulF a b) v = scaleF a (scaleF b v))
    (a b : α) (v : β) :
    smul scaleF (mul mulF (contents a) (contents b)) (contents v) =
    smul scaleF (contents a) (smul scaleF (contents b) (contents v)) := by
  simp [smul, mul, h]

-- ✓ Scalar multiplication is associative.

-- ============================================================================
-- Module Law 4: Identity scalar
-- 1 • v = v
-- ============================================================================

/-- The scalar identity acts as identity on contents vectors. -/
theorem one_smul {β : Type} (scaleF : α → β → β) (one : α)
    (h : ∀ v : β, scaleF one v = v) (v : β) :
    smul scaleF (contents one) (contents v) = contents v := by
  simp [smul, h]

-- ✓ Identity scalar works. Same pattern as multiplicative identity.

-- ============================================================================
-- Faithful Embedding of Scalar Multiplication
-- ============================================================================

/-- contents preserves scalar multiplication. -/
theorem contents_preserves_smul {β : Type} (f : α → β → β) (a : α) (v : β) :
    contents (f a v) = smul f (contents a) (contents v) := by rfl

-- ✓ α's scalar multiplication on β is exactly preserved inside Val.

-- ============================================================================
-- Full Val-level smul associativity (all 27 cases)
-- ============================================================================

/-- smul is associative at the Val level when the underlying operations
    satisfy the associativity law. -/
theorem val_smul_assoc {β : Type} (scaleF : α → β → β) (mulF : α → α → α)
    (h : ∀ (a b : α) (v : β), scaleF (mulF a b) v = scaleF a (scaleF b v))
    (a b : Val α) (v : Val β) :
    smul scaleF (mul mulF a b) v = smul scaleF a (smul scaleF b v) := by
  cases a with
  | origin => simp [mul, smul]
  | container _ =>
    cases b with
    | origin => simp [mul, smul]
    | container _ =>
      cases v with
      | origin => rfl
      | container _ => simp [mul, smul, h]
      | contents _ => simp [mul, smul, h]
    | contents _ =>
      cases v with
      | origin => rfl
      | container _ => simp [mul, smul, h]
      | contents _ => simp [mul, smul, h]
  | contents va =>
    cases b with
    | origin =>
      cases v with
      | origin => rfl
      | container _ => rfl
      | contents _ => rfl
    | container _ =>
      cases v with
      | origin => simp [mul, smul]
      | container _ => simp [mul, smul, h]
      | contents _ => simp [mul, smul, h]
    | contents vb =>
      cases v with
      | origin => simp [mul, smul]
      | container _ => simp [mul, smul, h]
      | contents vv => simp [mul, smul, h]

-- ✓ Full Val-level associativity. All 27 cases resolve.

-- ============================================================================
-- Full Val-level identity (all 3 cases)
-- ============================================================================

/-- contents(one) is the scalar identity at the Val level. -/
theorem val_one_smul {β : Type} (scaleF : α → β → β) (one : α)
    (h : ∀ v : β, scaleF one v = v) (v : Val β) :
    smul scaleF (contents one) v = v := by
  cases v with
  | origin => simp [smul]
  | container _ => simp [smul, h]
  | contents vv => simp [smul, h]

-- ✓ contents(1) is the scalar identity. origin and container absorb as expected.

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Scalar multiplication:
--   ✓ Same absorption pattern as mul (origin absorbs, container structural)
--   ✓ Contents closed under smul
--   ✓ Faithful embedding of α's scalar multiplication
--
-- Module laws (within contents):
--   ✓ Scalar distributes over vector addition
--   ✓ Scalar addition distributes over smul
--   ✓ Associativity of scalar multiplication
--   ✓ Identity scalar
--   → Module laws: confirmed within contents.
--
-- Full Val-level laws:
--   ✓ Associativity across all 27 sort combinations
--   ✓ Identity across all 3 sort cases
--   → Val-level module structure: confirmed.
--
-- Same pattern as RingField.lean and OrderedField.lean:
--   The module lives entirely in contents.
--   Origin and container are outside it — by type, not by convention.
--   No extra axioms. No patches. No NeZero. No conventions.

end Val
