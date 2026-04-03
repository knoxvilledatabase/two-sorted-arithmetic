/-
Released under MIT license.
-/
import OriginalArith.Foundation

/-!
# Container Benchmark: 𝒪, container, and contents as three primitives

This benchmark demonstrates that with `Val α` from Foundation.lean,
all three sorts have clean, distinct behavior:

- 𝒪 (origin) — the whole. Absorbs everything.
- container(a) — the bucket carrying value a. Not a number.
- contents(a) — 0, 1, 2, 3... Just quantities. 0 is empty contents.

The four rules:
  𝒪 × anything = 𝒪              — the whole absorbs
  container(a) × container(b) = container(f a b) — values combine, boundary persists
  container(a) × contents(b) = container(f a b)  — combine, keep boundary
  contents(a) × contents(b) = contents(f a b)    — actual arithmetic
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- Using Val α from Foundation.lean directly
-- ============================================================================

namespace ContainerBenchmark

open Val

variable {α : Type} [DecidableEq α]

-- ============================================================================
-- Rule 1: 𝒪 absorbs everything
-- ============================================================================

theorem origin_absorbs_left (f : α → α → α) (x : Val α) :
    Val.mul f origin x = origin :=
  Val.origin_absorbs_mul_left f x

theorem origin_absorbs_right (f : α → α → α) (x : Val α) :
    Val.mul f x origin = origin :=
  Val.origin_absorbs_mul_right f x

-- ============================================================================
-- Rule 2: container × container = container
-- ============================================================================

theorem container_times_container (f : α → α → α) (a b : α) :
    Val.mul f (container a : Val α) (container b) = container (f a b) := by rfl

-- ============================================================================
-- Rule 3: container × contents = container (and contents × container = container)
-- ============================================================================

theorem container_times_contents (f : α → α → α) (a b : α) :
    Val.mul f (container a : Val α) (contents b) = container (f a b) := by rfl

theorem contents_times_container (f : α → α → α) (a b : α) :
    Val.mul f (contents a) (container b : Val α) = container (f a b) := by rfl

-- ============================================================================
-- Rule 4: contents × contents = contents (actual arithmetic)
-- ============================================================================

theorem contents_times_contents (f : α → α → α) (a b : α) :
    Val.mul f (contents a) (contents b) = contents (f a b) := by rfl

-- ============================================================================
-- What dissolves with three primitives
-- ============================================================================

/-- Contents never produce origin. (NoZeroDivisors — gone.) -/
theorem contents_never_origin (f : α → α → α) (a b : α) :
    Val.mul f (contents a) (contents b) ≠ origin := by
  simp [Val.mul]

/-- Contents never produce container. -/
theorem contents_never_container (f : α → α → α) (a b c : α) :
    Val.mul f (contents a) (contents b) ≠ container c := by
  simp [Val.mul]

/-- Container is never origin. -/
theorem container_ne_origin (a : α) : (container a : Val α) ≠ origin := by
  simp

/-- Contents are never origin. (NeZero — gone.) -/
theorem contents_ne_origin (a : α) : (contents a : Val α) ≠ origin := by
  simp

/-- Contents are never container. -/
theorem contents_ne_container (a b : α) : (contents a : Val α) ≠ container b := by
  simp

/-- Origin is unique: if something absorbs everything, it's origin. -/
theorem absorber_is_origin (f : α → α → α) [Nonempty α] (x : Val α)
    (h : ∀ y : Val α, Val.mul f x y = origin) : x = origin := by
  cases x with
  | origin => rfl
  | container a => have := h (container a); simp [Val.mul] at this
  | contents a => have := h (container a); simp [Val.mul] at this

-- ============================================================================
-- The inv question: three different answers for three different sorts
-- ============================================================================

/-- Origin inverse is origin. Absorption. -/
theorem inv_origin (g : α → α) : Val.inv g (origin : Val α) = origin := by rfl

/-- Container inverse is container with inverted value. -/
theorem inv_container (g : α → α) (a : α) :
    Val.inv g (container a : Val α) = container (g a) := by rfl

/-- Contents inverse is contents. Arithmetic within contents. -/
theorem inv_contents (g : α → α) (a : α) :
    Val.inv g (contents a : Val α) = contents (g a) := by rfl

-- No convention needed anywhere. Each sort answers for itself.

-- ============================================================================
-- Comparison: what does the three-sort split buy?
-- ============================================================================

-- In a collapsed system (one zero for everything):
--   0 is both "empty contents" and "boundary."
--   0 * a = 0 could mean "empty contents times something" or "boundary absorbs."
--   MulZeroClass conflates two different reasons something "becomes zero."

-- In Val α (three sorts):
--   container(a) × anything = container(f a ...) — container computes
--   contents(0) × contents(a) = contents(0*a) = contents(0) — zero iterations
--   origin × anything = origin — absorption
--   These are three visibly different operations.

-- The three-sort split makes the difference visible.

end ContainerBenchmark

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                    Collapsed       Val α (three sorts)
--  Sorts                 1              3
--  Rules                 patched        4 (clean, no overlap)
--  0 has jobs            2+             1 (just empty contents)
--  1 has jobs            2+             1 (just unit contents)
--  container explicit    no             yes
--  NeZero needed         yes            no
--  NoZeroDivisors        yes            no
--  inv convention        yes            no
--  MulZeroClass split    no             yes (contents-zero vs container vs origin)
--
--  Val α reveals something the collapsed version hides: MulZeroClass
--  is multiple facts wearing one axiom. Contents-level zero (0*a=0),
--  container-level computation, and origin absorption are different
--  operations collapsed into zero_mul/mul_zero.
--
--  Three symbols. Four rules. Every symbol has one job.
