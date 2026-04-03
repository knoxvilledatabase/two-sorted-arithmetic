/-
Released under MIT license.
-/
import OriginalArith.Foundation

/-!
# Faithful Embedding and Algebraic Laws

Two results that strengthen Foundation.lean:

1. **Faithful embedding:** The contents constructor is injective and
   preserves all operations. The original arithmetic on α is completely
   preserved inside Val α. Nothing is lost.

2. **Algebraic laws hold on Val α:** Semigroup, monoid, and zero-absorption
   laws all hold when the underlying α satisfies them. Proved directly
   without typeclass machinery (to avoid elaboration friction with Lean's
   instance resolution on a three-constructor type).
-/

namespace Val

open Val

-- ============================================================================
-- Part 1: Faithful Embedding
-- ============================================================================

/-- contents is injective: different values produce different contents. -/
theorem contents_injective {α : Type} : Function.Injective (contents : α → Val α) := by
  intros a b h; cases h; rfl

/-- contents preserves multiplication. -/
theorem contents_preserves_mul {α : Type} (f : α → α → α) (a b : α) :
    contents (f a b) = mul f (contents a) (contents b) := by rfl

/-- contents preserves addition. -/
theorem contents_preserves_add {α : Type} (f : α → α → α) (a b : α) :
    contents (f a b) = add f (contents a) (contents b) := by rfl

/-- contents preserves left identity. -/
theorem contents_preserves_id_left {α : Type}
    (f : α → α → α) (z : α) (h : ∀ a : α, f z a = a) (a : α) :
    add f (contents z) (contents a) = contents a := by simp [add, h]

/-- contents preserves right identity. -/
theorem contents_preserves_id_right {α : Type}
    (f : α → α → α) (z : α) (h : ∀ a : α, f a z = a) (a : α) :
    add f (contents a) (contents z) = contents a := by simp [add, h]

/-- contents reflects equality: equal contents means equal values. -/
theorem contents_reflects_eq {α : Type} (a b : α)
    (h : (contents a : Val α) = contents b) : a = b := by cases h; rfl

-- ✓ contents is a faithful, operation-preserving, equality-reflecting embedding.
-- The arithmetic of α is exactly preserved inside Val α.

-- ============================================================================
-- Part 2: Algebraic Laws on Val α
-- ============================================================================
-- Proved directly using Foundation.lean's operations.
-- No typeclass instances — just the laws stated as theorems.

-- ---------- Semigroup law: associativity ----------

/-- Multiplication on Val α is associative when f is associative.
    This is the semigroup law. -/
theorem val_mul_assoc {α : Type} (f : α → α → α)
    (hf : ∀ x y z : α, f (f x y) z = f x (f y z))
    (a b c : Val α) :
    mul f (mul f a b) c = mul f a (mul f b c) := by
  cases a with
  | origin => rfl
  | container va =>
    cases b with
    | origin => rfl
    | container vb =>
      cases c with
      | origin => rfl
      | container vc => simp [mul, hf]
      | contents vc => simp [mul, hf]
    | contents vb =>
      cases c with
      | origin => rfl
      | container vc => simp [mul, hf]
      | contents vc => simp [mul, hf]
  | contents va =>
    cases b with
    | origin => rfl
    | container vb =>
      cases c with
      | origin => rfl
      | container vc => simp [mul, hf]
      | contents vc => simp [mul, hf]
    | contents vb =>
      cases c with
      | origin => simp [mul]
      | container vc => simp [mul, hf]
      | contents vc => simp [mul]; exact hf va vb vc

-- ✓ Semigroup law holds.

-- ---------- Monoid laws: identity ----------

/-- contents(one) is a left identity for mul when one is a left identity for f. -/
theorem val_one_mul {α : Type} (f : α → α → α) (one : α)
    (h : ∀ a : α, f one a = a) (a : Val α) :
    mul f (contents one) a = a := by
  cases a with
  | origin => simp [mul]
  | container v => simp [mul, h]
  | contents v => simp [mul, h]

/-- contents(one) is a right identity for mul when one is a right identity for f. -/
theorem val_mul_one {α : Type} (f : α → α → α) (one : α)
    (h : ∀ a : α, f a one = a) (a : Val α) :
    mul f a (contents one) = a := by
  cases a with
  | origin => rfl
  | container v => simp [mul, h]
  | contents v => simp [mul, h]

-- ✓ Monoid laws hold. contents(1) is the identity.
-- origin * 1 = origin (absorption). container(a) * 1 = container(a) (computes, f a 1 = a).

-- ---------- Arithmetic zero: contents(0) is the zero of α, not an absorber ----------

/-- contents(zero) is the arithmetic zero within contents.
    This is α's own zero property, not absorption. -/
theorem val_zero_mul_contents {α : Type} (f : α → α → α) (zero : α)
    (h : ∀ a : α, f zero a = zero) (a : α) :
    mul f (contents zero) (contents a) = contents zero := by
  simp [mul, h]

/-- Same from the right. -/
theorem val_mul_zero_contents {α : Type} (f : α → α → α) (zero : α)
    (h : ∀ a : α, f a zero = zero) (a : α) :
    mul f (contents a) (contents zero) = contents zero := by
  simp [mul, h]

/-- contents(0) does NOT absorb origin — origin absorbs IT. -/
theorem zero_contents_does_not_absorb_origin {α : Type} (f : α → α → α) (zero : α) :
    mul f (contents zero) origin = origin := by rfl

/-- contents(0) meets container — result is container, values combine. -/
theorem zero_contents_meets_container {α : Type} (f : α → α → α) (zero a : α) :
    mul f (contents zero) (container a) = container (f zero a) := by rfl

-- CRITICAL OBSERVATION (from a build failure that caught an overclaim):
--
-- These are three DIFFERENT behaviors, not three levels of "absorption":
--
--   𝒪: ABSORPTION — the ocean eats the fish. Forced by the first principle.
--   container: COMPUTATION AT BOUNDARY — values combine, boundary persists.
--   contents(0): ARITHMETIC ZERO — empty times anything is empty, within α.
--
-- Mathlib's zero_mul says 0 * a = 0 as if there is one behavior.
-- There are three. Each at a different level. Each for a different reason.
-- The collapsed symbol 0 hid this. The three-primitive type made it visible.
-- The build failure made it undeniable.

-- ---------- Distributivity ----------

/-- Left distributivity at the contents level. -/
theorem val_left_distrib {α : Type}
    (mulF addF : α → α → α)
    (h : ∀ a b c : α, mulF a (addF b c) = addF (mulF a b) (mulF a c))
    (a b c : α) :
    mul mulF (contents a) (add addF (contents b) (contents c)) =
    add addF (mul mulF (contents a) (contents b))
             (mul mulF (contents a) (contents c)) := by
  simp [mul, add, h]

-- ✓ Distributivity holds for contents.

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Faithful embedding:
--   ✓ contents is injective
--   ✓ contents preserves mul, add, identities
--   ✓ contents reflects equality
--   ✓ α's arithmetic is exactly preserved inside Val α
--
-- Algebraic laws (proved directly, no typeclass machinery):
--   ✓ Associativity (semigroup law, all sort combinations)
--   ✓ Identity (monoid law, contents(1) as identity)
--   ✓ Arithmetic zero (contents(0) is zero within contents)
--   ✓ Distributivity (contents level)
--
-- Critical finding (from a build failure):
--   Three different behaviors, not three levels of absorption:
--     𝒪: absorption — forced by the first principle
--     container: computation at boundary — values combine, boundary persists
--     contents(0): arithmetic zero — α's own zero property
--   Mathlib's zero_mul conflates all three into one axiom.
--   The three-primitive system makes them visibly different.
--
-- No extra axioms. No patches. No conventions.
-- Val α inherits α's algebra and adds boundary structure on top.

end Val
