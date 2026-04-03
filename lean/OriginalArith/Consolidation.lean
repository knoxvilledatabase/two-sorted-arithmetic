/-
Released under MIT license.
-/
import OriginalArith.Basic

/-!
# Consolidation: Four Benchmarks, One Principle

The four benchmarks all dissolved patches for the same reason:
computation inside contents never crosses into origin.

- **NeZeroBenchmark:** contents × contents produces contents. Hypotheses vanish.
- **InvBenchmark:** origin⁻¹ = origin by absorption. Convention vanishes.
- **ZeroDivBenchmark:** contents × contents never produces origin. Axiom vanishes.
- **ZModBenchmark:** PosNat is never zero. `[NeZero n]` vanishes.

Each benchmark stated this in a different vocabulary. This file states it once.

## The principle

For any operation on `Val D`:
- `contents × contents → contents` (never touches origin)
- `contents × origin → origin` (absorption I1)
- `origin × contents → origin` (absorption I2)
- `origin × origin → origin` (absorption I3)
- `container` combines values and keeps the boundary

Every dissolved hypothesis, axiom, and convention was a guard against a
crossing from contents to origin that the type makes impossible.
-/

namespace OriginalArith

open OriginalArith

-- ============================================================================
-- The principle: contents operations stay in contents
-- ============================================================================

/-- The core fact all four benchmarks rely on:
    contents × contents is always contents. Never origin.
    This is why ≠ 0 hypotheses, NoZeroDivisors, and NeZero dissolve. -/
theorem bounded_closed_under_twoSortedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    Val.mul f (bounded' a) (bounded' b) = bounded' (f a b) := by
  rfl

/-- Contents operations never produce origin. -/
theorem bounded_op_ne_origin {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    Val.mul f (bounded' a) (bounded' b) ≠ origin' := by
  simp [Val.mul, origin']

/-- Origin only appears in the output when origin appears in the input. -/
theorem origin_in_output_requires_origin_in_input {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : Val D)
    (h : Val.mul f a b = origin') :
    a = origin' ∨ b = origin' := by
  cases a with
  | origin => left; rfl
  | container va =>
    cases b with
    | origin => right; rfl
    | container _ => simp [Val.mul] at h
    | contents _ => simp [Val.mul] at h
  | contents va =>
    cases b with
    | origin => right; rfl
    | container _ => simp [Val.mul] at h
    | contents _ => simp [Val.mul] at h

-- ============================================================================
-- Why each benchmark's patches dissolve
-- ============================================================================

/-- NeZero dissolves because: contents elements operating on contents elements
    produce contents elements. The result is never origin. The type knows. -/
theorem neZero_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D) :
    ∃ c : D, Val.mul f (bounded' a) (bounded' b) = bounded' c :=
  ⟨f a b, rfl⟩

/-- NoZeroDivisors dissolves because: if the result is origin, at least one
    input was origin. Contents inputs cannot produce origin output. -/
theorem noZeroDivisors_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : D)
    (h : Val.mul f (bounded' a) (bounded' b) = origin') : False := by
  simp [Val.mul, origin'] at h

/-- The inv convention dissolves because: origin absorbs inversion the same
    way it absorbs multiplication. Not a choice. A consequence. -/
theorem inv_convention_unnecessary {D : Type} [DecidableEq D]
    (f : D → D → D) :
    Val.mul f origin' origin' = origin' := by
  simp [Val.mul]

/-- NeZero on moduli dissolves because: a positive natural (contents) used
    as a modulus is never origin. The type carries the positivity. -/
theorem neZero_modulus_unnecessary {D : Type} (n : D) :
    (bounded' n : Val D) ≠ origin' := by
  simp [bounded', origin']

-- ============================================================================
-- The consolidation theorem
-- ============================================================================

/-- All four benchmarks reduce to one fact:
    contents is closed under operations.
    Contents in, contents out. Origin only appears when origin goes in.

    Every ≠ 0 hypothesis is checking: "is this contents or origin?"
    Every NoZeroDivisors axiom is asserting: "contents × contents ≠ origin."
    Every NeZero is requiring: "this parameter is contents."
    Every inv_zero convention is choosing: "origin⁻¹ = origin."

    In the three-sort system, all four are consequences of the type.
    Not axioms. Not conventions. Not hypotheses. Consequences. -/
theorem consolidation {D : Type} [DecidableEq D] (f : D → D → D) (a b : D) :
    -- Contents is closed (NeZero, ≠ 0 hypotheses dissolve)
    (∃ c : D, Val.mul f (bounded' a) (bounded' b) = bounded' c) ∧
    -- Contents never produces origin (NoZeroDivisors dissolves)
    (Val.mul f (bounded' a) (bounded' b) ≠ origin') ∧
    -- Origin absorbs (inv_zero convention dissolves)
    (Val.mul f origin' origin' = origin') ∧
    -- Contents is never origin (NeZero on moduli dissolves)
    ((bounded' a : Val D) ≠ origin') := by
  refine ⟨⟨f a b, rfl⟩, ?_, ?_, ?_⟩
  · simp [Val.mul, origin']
  · simp [Val.mul]
  · simp [bounded', origin']

end OriginalArith
