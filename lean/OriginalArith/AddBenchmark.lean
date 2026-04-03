/-
Released under MIT license.
-/
import Std

/-!
# Addition Benchmark: the other side of the trade-off

The four previous benchmarks measured the cost of the collapsed default
for multiplication: 18 hypotheses, 2 axioms, 1 convention.

This benchmark measures the cost of the separated default for addition.
If separating origin from bounded makes addition harder, the trade-off
goes the other way.

Ground floor only. 0 + 1 = 1. Two files. Count the work.
-/

set_option linter.unusedSectionVars false

-- ============================================================================
-- COLLAPSED: 0 + 1 = 1 in Option α (today's default)
-- ============================================================================

namespace AddCollapsed

variable {α : Type}

def G₀ (α : Type) := Option α

def zero : G₀ α := none
def one (a : α) : G₀ α := some a

-- Addition: 0 + a = a, a + 0 = a, a + b = a + b within α
-- We need a binary operation on α for the bounded case
def add (f : α → α → α) : G₀ α → G₀ α → G₀ α
  | none, b => b             -- 0 + b = b (additive identity)
  | a, none => a             -- a + 0 = a (additive identity)
  | some a, some b => some (f a b)  -- a + b within α

/-- 0 + 1 = 1. Clean. No hypotheses. -/
theorem zero_add (a : α) (f : α → α → α) :
    add f none (some a) = some a := by
  rfl

/-- 1 + 0 = 1. Clean. No hypotheses. -/
theorem add_zero (a : α) (f : α → α → α) :
    add f (some a) none = some a := by
  rfl

/-- 0 + 0 = 0. Clean. -/
theorem zero_add_zero (f : α → α → α) :
    add f (none : G₀ α) none = none := by
  rfl

-- SUMMARY:
--   Lines of setup: ~10
--   Hypotheses: 0
--   Wrapping: 0
--   Complexity: minimal. Addition with zero just works.

end AddCollapsed

-- ============================================================================
-- SEPARATED: 0 + 1 = 1 with WithZero (the proposed default)
-- ============================================================================

namespace AddSeparated

variable {α : Type}

-- α is the interior. WithZero α is α + boundary.
-- But for addition, zero is the ADDITIVE IDENTITY — it's the placeholder
-- job, not the origin job. Zero belongs in the additive structure.

-- Option 1: Work in WithZero α (Option α) for addition.
-- This is IDENTICAL to the collapsed version. No difference.

def WithZero (α : Type) := Option α

def add (f : α → α → α) : WithZero α → WithZero α → WithZero α
  | none, b => b
  | a, none => a
  | some a, some b => some (f a b)

/-- 0 + 1 = 1. Identical to collapsed. -/
theorem zero_add (a : α) (f : α → α → α) :
    add f none (some a) = some a := by
  rfl

/-- 1 + 0 = 1. Identical to collapsed. -/
theorem add_zero (a : α) (f : α → α → α) :
    add f (some a) none = some a := by
  rfl

/-- 0 + 0 = 0. Identical to collapsed. -/
theorem zero_add_zero (f : α → α → α) :
    add f (none : WithZero α) none = none := by
  rfl

-- SUMMARY:
--   Lines of setup: ~10
--   Hypotheses: 0
--   Wrapping: 0
--   Complexity: IDENTICAL to collapsed.

-- This is the same code. Exactly the same.
--
-- Because additive zero IS the none in WithZero α.
-- The additive identity IS the adjoined element.
-- WithZero α is Option α. The addition is the same function.
--
-- CORRECTION: This does NOT prove "the trade-off doesn't exist."
-- It proves one theorem costs the same. That's all.
--
-- The honest finding: addition genuinely needs zero in the type.
-- You can't do 0 + a = a in Gˣ because Gˣ has no zero.
-- So the "separated" version for addition IS WithZero α.
-- Which IS Option α. Which IS the collapsed type.
--
-- The two jobs zero does are not symmetric:
-- - The absorbing element job IS separable. Work in Gˣ.
--   Encounter none at the boundary. 18 hypotheses dissolve.
-- - The additive identity job is NOT separable. Zero must be
--   in the type for addition to work.
--
-- WithZero Gˣ serves both: Gˣ is the interior for multiplication.
-- none is the additive identity for addition AND the absorbing
-- boundary for multiplication. Same value. Different jobs.

end AddSeparated

-- ============================================================================
-- THE DIFF
-- ============================================================================
--
--                        Collapsed       Separated
--  0 + 1 = 1             rfl             rfl
--  Lines of code          ~10             ~10
--  Hypotheses             0               0
--  Wrapping/lifting       0               0
--  Complexity             minimal         IDENTICAL
--
--  What this proves: 0 + 1 = 1 costs the same in both versions.
--  What this does NOT prove: "the trade-off doesn't exist."
--
--  Addition needs zero in the type. The additive identity is not
--  separable. The absorbing element is.
--
--  WithZero Gˣ is the correct type:
--  - Gˣ for the interior (multiplication without ≠ 0 hypotheses)
--  - none for the boundary (absorbing element) AND the additive
--    identity (0 + a = a). Same value. Two jobs. But now the jobs
--    are understood, not conflated.
--
--  The separation saves 18 multiplicative hypotheses.
--  The separation costs nothing for addition.
--  But the reason it costs nothing is that addition still uses
--  the collapsed type. The separation is partial, not total.
--
--  That's the honest result.
