/-
Released under MIT license.
-/
import OriginalArith.Basic

/-!
# Consolidation: Four Benchmarks, One Principle

The four benchmarks all dissolved patches for the same reason:
computation inside the interior never crosses into Origin.

- **NeZeroBenchmark:** `Gˣ × Gˣ` never produces zero. Hypotheses vanish.
- **InvBenchmark:** `origin⁻¹ = origin` by absorption. Convention vanishes.
- **ZeroDivBenchmark:** `bounded × bounded` never produces origin. Axiom vanishes.
- **ZModBenchmark:** `PosNat` is never zero. `[NeZero n]` vanishes.

Each benchmark stated this in a different vocabulary. This file states it once.

## The principle

For any two-sorted operation on `Zero' D`:
- `Interior × Interior → Interior` (never touches Origin)
- `Interior × Origin → Origin` (absorption I1)
- `Origin × Interior → Origin` (absorption I2)
- `Origin × Origin → Origin` (absorption I3)

Every dissolved hypothesis, axiom, and convention was a guard against a
crossing from Interior to Origin that the type makes impossible.
-/

namespace OriginalArith

open OriginalArith

-- ============================================================================
-- The principle: bounded operations stay bounded
-- ============================================================================

/-- The core fact all four benchmarks rely on:
    bounded × bounded is always bounded. Never origin.
    This is why ≠ 0 hypotheses, NoZeroDivisors, and NeZero dissolve. -/
theorem bounded_closed_under_twoSortedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    twoSortedOp f (bounded' a) (bounded' b) = bounded' (f a b) := by
  rfl

/-- Bounded operations never produce origin. -/
theorem bounded_op_ne_origin {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    twoSortedOp f (bounded' a) (bounded' b) ≠ origin' := by
  simp [twoSortedOp, origin', bounded']

/-- Origin only appears in the output when origin appears in the input. -/
theorem origin_in_output_requires_origin_in_input {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : Zero' D)
    (h : twoSortedOp f a b = origin') :
    a = origin' ∨ b = origin' := by
  cases a with
  | inl _ => left; cases ‹Origin›; rfl
  | inr va =>
    cases b with
    | inl _ => right; cases ‹Origin›; rfl
    | inr vb => simp [twoSortedOp, origin', bounded'] at h

-- ============================================================================
-- Why each benchmark's patches dissolve
-- ============================================================================

/-- NeZero dissolves because: bounded elements operating on bounded elements
    produce bounded elements. The result is never origin. The type knows. -/
theorem neZero_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    ∃ c : D, twoSortedOp f (bounded' a) (bounded' b) = bounded' c :=
  ⟨f a b, rfl⟩

/-- NoZeroDivisors dissolves because: if the result is origin, at least one
    input was origin. Bounded inputs cannot produce origin output. -/
theorem noZeroDivisors_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D)
    (h : twoSortedOp f (bounded' a) (bounded' b) = origin') : False := by
  simp [twoSortedOp, origin', bounded'] at h

/-- The inv convention dissolves because: origin absorbs inversion the same
    way it absorbs multiplication. Not a choice. A consequence. -/
theorem inv_convention_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) :
    twoSortedOp f origin' origin' = origin' := by
  simp [twoSortedOp, origin']

/-- NeZero on moduli dissolves because: a positive natural (bounded) used
    as a modulus is never origin. The type carries the positivity. -/
theorem neZero_modulus_unnecessary {D : Type} (n : D) :
    (bounded' n : Zero' D) ≠ origin' := by
  simp [bounded', origin']

-- ============================================================================
-- The consolidation theorem
-- ============================================================================

/-- All four benchmarks reduce to one fact:
    the interior is closed under operations.
    Bounded in, bounded out. Origin only appears when origin goes in.

    Every ≠ 0 hypothesis is checking: "is this bounded or origin?"
    Every NoZeroDivisors axiom is asserting: "bounded × bounded ≠ origin."
    Every NeZero is requiring: "this parameter is bounded."
    Every inv_zero convention is choosing: "origin⁻¹ = origin."

    In the two-sorted system, all four are consequences of the type.
    Not axioms. Not conventions. Not hypotheses. Consequences. -/
theorem consolidation {D : Type} [DecidableEq D] (f : D → D → D) (a b : D) :
    -- Interior is closed (NeZero, ≠ 0 hypotheses dissolve)
    (∃ c : D, twoSortedOp f (bounded' a) (bounded' b) = bounded' c) ∧
    -- Interior never produces origin (NoZeroDivisors dissolves)
    (twoSortedOp f (bounded' a) (bounded' b) ≠ origin') ∧
    -- Origin absorbs (inv_zero convention dissolves)
    (twoSortedOp f origin' origin' = origin') ∧
    -- Bounded is never origin (NeZero on moduli dissolves)
    ((bounded' a : Zero' D) ≠ origin') := by
  refine ⟨⟨f a b, rfl⟩, ?_, ?_, ?_⟩
  · simp [twoSortedOp, origin', bounded']
  · simp [twoSortedOp, origin']
  · simp [bounded', origin']

end OriginalArith
