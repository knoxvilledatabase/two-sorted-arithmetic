/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import Std

/-!
# Container Benchmark: 𝒪, B, and Contents as three primitives

Previous benchmarks used two sorts: Origin and Bounded (which mixed
container and contents into one wrapper).

This benchmark tests three primitives:
- 𝒪 (Origin) — the whole. Absorbs everything.
- B (Container) — the bucket. B × B = B. Not a number.
- Contents — 0, 1, 2, 3... Just quantities. 0 is empty contents.

The four rules:
  𝒪 × anything = 𝒪            — the whole absorbs
  B × B = B                     — container of containers is container
  B × contents = B(contents)    — bucket holding something
  contents × contents = contents — actual arithmetic
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- The three-primitive system
-- ============================================================================

namespace ThreePrimitive

variable {α : Type} [DecidableEq α]

/-- The three sorts. Not two. Three. -/
inductive Val (α : Type) where
  | origin : Val α                -- 𝒪 — the whole
  | container : Val α             -- B — the bucket, not a number
  | contents : α → Val α          -- 0, 1, 2... just quantities
deriving Repr

open Val

-- ============================================================================
-- The four rules
-- ============================================================================

/-- Multiplication under three primitives. Four rules, no exceptions. -/
def mul (f : α → α → α) : Val α → Val α → Val α
  | origin, _               => origin              -- Rule 1: 𝒪 × anything = 𝒪
  | _, origin               => origin              -- Rule 1: anything × 𝒪 = 𝒪
  | container, container    => container            -- Rule 2: B × B = B
  | container, contents _   => container            -- Rule 3: B × contents = B
  | contents _, container   => container            -- Rule 3: contents × B = B
  | contents a, contents b  => contents (f a b)     -- Rule 4: contents × contents = contents

-- ============================================================================
-- Rule 1: 𝒪 absorbs everything
-- ============================================================================

theorem origin_absorbs_left (f : α → α → α) (x : Val α) :
    mul f origin x = origin := by
  rfl

theorem origin_absorbs_right (f : α → α → α) (x : Val α) :
    mul f x origin = origin := by
  cases x with
  | origin => rfl
  | container => rfl
  | contents _ => rfl

-- ============================================================================
-- Rule 2: B × B = B
-- ============================================================================

theorem container_times_container (f : α → α → α) :
    mul f (container : Val α) container = container := by
  rfl

-- ============================================================================
-- Rule 3: B × contents = B (and contents × B = B)
-- ============================================================================

theorem container_times_contents (f : α → α → α) (a : α) :
    mul f (container : Val α) (contents a) = container := by
  rfl

theorem contents_times_container (f : α → α → α) (a : α) :
    mul f (contents a) (container : Val α) = container := by
  rfl

-- ============================================================================
-- Rule 4: contents × contents = contents (actual arithmetic)
-- ============================================================================

theorem contents_times_contents (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) = contents (f a b) := by
  rfl

-- ============================================================================
-- What dissolves with three primitives
-- ============================================================================

/-- Contents never produce origin. (NoZeroDivisors — gone.) -/
theorem contents_never_origin (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ origin := by
  simp [mul]

/-- Contents never produce bare container. -/
theorem contents_never_container (f : α → α → α) (a b : α) :
    mul f (contents a) (contents b) ≠ container := by
  simp [mul]

/-- Container is never origin. -/
theorem container_ne_origin : (container : Val α) ≠ origin := by
  simp

/-- Contents are never origin. (NeZero — gone.) -/
theorem contents_ne_origin (a : α) : (contents a : Val α) ≠ origin := by
  simp

/-- Contents are never bare container. -/
theorem contents_ne_container (a : α) : (contents a : Val α) ≠ container := by
  simp

/-- Origin is unique: if something absorbs everything, it's origin. -/
theorem absorber_is_origin (f : α → α → α) [Nonempty α] (x : Val α)
    (h : ∀ y : Val α, mul f x y = origin) : x = origin := by
  cases x with
  | origin => rfl
  | container => have := h container; simp [mul] at this
  | contents a => have := h container; simp [mul] at this

-- ============================================================================
-- The inv question: three different answers for three different sorts
-- ============================================================================

/-- Inverse on three sorts. Each sort gets its own answer. No convention. -/
def inv (g : α → α) : Val α → Val α
  | origin => origin              -- 𝒪⁻¹ = 𝒪 (absorption, not convention)
  | container => container        -- B⁻¹ = B (a bucket inverted is still a bucket)
  | contents a => contents (g a)  -- contents⁻¹ = inverse contents (arithmetic)

/-- Origin inverse is origin. Absorption. -/
theorem inv_origin (g : α → α) : inv g (origin : Val α) = origin := by rfl

/-- Container inverse is container. Structure. -/
theorem inv_container (g : α → α) : inv g (container : Val α) = container := by rfl

/-- Contents inverse is contents. Arithmetic within contents. -/
theorem inv_contents (g : α → α) (a : α) :
    inv g (contents a : Val α) = contents (g a) := by rfl

-- No convention needed anywhere. Each sort answers for itself.

-- ============================================================================
-- Comparison: what does adding B as a separate symbol buy?
-- ============================================================================

-- In the two-sorted version (Origin + Bounded):
--   Bounded wraps contents AND is the container.
--   bounded'(0) is both "empty contents" and "one bucket."
--   That's still a two-job collapse, just at a smaller scale.
--
-- In the three-primitive version:
--   container is ONLY the container. Not a number. Not contents.
--   contents 0 is ONLY empty contents. Not a container.
--   Each symbol has exactly one job.
--
-- The MulZeroClass question:
--   Two-sorted: 0 * a = 0 because bounded'(0) absorbs? No —
--     bounded'(0) * bounded'(a) = bounded'(0*a) = bounded'(0).
--     It's contents-level arithmetic, not absorption.
--   Three-primitive: contents(0) * contents(a) = contents(0*a) = contents(0).
--     Same. Still contents-level. Still Rule 4.
--     But now B × anything = B is Rule 2/3, a SEPARATE fact.
--     The container behavior and the zero-contents behavior are
--     visibly different operations, not collapsed into one.
--
-- What this reveals:
--   MulZeroClass conflates TWO different reasons something "becomes zero":
--   1. Contents-level: 0 * a = 0 (empty contents times anything is empty)
--   2. Container-level: B absorbs contents (bucket eats the number)
--   These are different operations. Mathlib treats them as one axiom.
--   The three-primitive split makes the difference visible.

end ThreePrimitive

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                    Two-sorted    Three-primitive
--  Sorts                 2              3
--  Rules                 2 (I1,I2)      4 (clean, no overlap)
--  0 has jobs            2              1 (just empty contents)
--  1 has jobs            2              1 (just unit contents)
--  B is explicit         no             yes
--  NeZero needed         no             no
--  NoZeroDivisors        no             no
--  inv convention        no             no
--  MulZeroClass split    no             yes (contents-zero vs container-absorb)
--
--  The three-primitive version reveals something the two-sorted
--  version hides: MulZeroClass is two facts wearing one axiom.
--  Contents-level zero (0*a=0) and container-level absorption (B*a=B)
--  are different operations collapsed into zero_mul/mul_zero.
--
--  Three symbols. Four rules. Every symbol has one job.
