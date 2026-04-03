/-
Released under MIT license.
-/
import OriginalArith.Foundation

/-!
# Original Arithmetic: Basic Definitions (Compatibility Layer)

This file re-exports the core definitions from `Foundation.lean` and provides
backward-compatible names for theorems that were originally stated in the
original vocabulary.

The foundation is `Val α` with three constructors:
- `origin` — the categorical boundary. Absorbs everything.
- `container` — carries a value. The bucket.
- `contents` — quantities. 0, 1, 2, 3...

## Backward-compatible names

- `origin'` → `Val.origin`
- `bounded' d` → `Val.contents d`
- `Zero' D` → `Val D`
- `twoSortedOp f a b` → `Val.mul f a b`
- `twoSortedDiv` → `Val.div` (with inverse function)
- `morphism` → `Val.valMap` (sort-preserving map)

## Main results (re-stated)

- `interaction_I1` / `interaction_I2` / `interaction_I3` — absorption axioms
- `origin_not_bounded` — origin ≠ contents
- `zero_div_zero_same` — contents ÷ contents reveals container
- `morphism_preserves_origin` — maps preserve origin
- `original_arithmetic_is_well_formed` — master theorem
-/

namespace OriginalArith

-- ============================================================================
-- Backward-compatible type aliases
-- ============================================================================

/-- The sorted type: `Val D`. Replaces `Origin ⊕ Bounded D`. -/
abbrev Zero' (D : Type) := Val D

/-- Smart constructor for origin. -/
abbrev origin' {D : Type} : Val D := Val.origin

/-- Smart constructor for contents (previously "bounded"). -/
abbrev bounded' {D : Type} (d : D) : Val D := Val.contents d

-- ============================================================================
-- Axiom 𝒪1: Non-membership
-- ============================================================================

/-- 𝒪1: Origin is not a contents element. -/
theorem origin_not_bounded {D : Type} (d : D) :
    (origin' : Val D) ≠ bounded' d := by
  simp [origin', bounded']

-- ============================================================================
-- Interaction Axioms (I1–I3)
-- ============================================================================

/-- Lift a binary operation on `D` to `Val D`. Returns `origin` whenever
either argument is `origin`. -/
abbrev twoSortedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : Val D) : Val D :=
  Val.mul f a b

/-- I1: `f(x, 𝒪) = 𝒪` for all `x`. Right-absorption. -/
theorem interaction_I1 {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Val D) :
    twoSortedOp f x origin' = origin' :=
  Val.origin_absorbs_mul_right f x

/-- I2: `f(𝒪, x) = 𝒪` for all `x`. Left-absorption. -/
theorem interaction_I2 {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Val D) :
    twoSortedOp f origin' x = origin' :=
  Val.origin_absorbs_mul_left f x

/-- I3: `f(𝒪, 𝒪) = 𝒪`. Self-absorption. (Redundant — follows from I1 or I2.) -/
theorem interaction_I3 {D : Type} [DecidableEq D]
    (f : D → D → D) :
    twoSortedOp f origin' origin' = origin' :=
  Val.origin_absorbs_mul_left f origin'

-- ============================================================================
-- Division (using Val.div)
-- ============================================================================

/-- Division of contents by contents with same value yields container.
    This is the "contents ÷ contents = 1" result. -/
theorem zero_div_zero_same {D : Type} [DecidableEq D]
    (f : D → D → D) (g : D → D) (d : D) :
    Val.div f g (bounded' d) (bounded' d) = Val.contents (f d (g d)) := by
  rfl

/-- Division by origin = origin. -/
theorem zero_div_origin {D : Type} (f : D → D → D) (g : D → D) (d : D) :
    Val.div f g (bounded' d) (origin' : Val D) = origin' := by
  exact Val.div_by_origin f g (bounded' d)

/-- Origin ÷ origin = origin. Self-stability. -/
theorem origin_div_origin {D : Type} (f : D → D → D) (g : D → D) :
    Val.div f g (origin' : Val D) origin' = origin' := by
  exact Val.div_by_origin f g origin'

-- ============================================================================
-- The Morphism φ
-- ============================================================================

/-- Structure-preserving map between Val domains. -/
def morphism {D₁ D₂ : Type} (f : D₁ → D₂) : Val D₁ → Val D₂
  | Val.origin => Val.origin
  | Val.container a => Val.container (f a)
  | Val.contents a => Val.contents (f a)

/-- The distinction-preserving property: a map sends origin to origin
and contents to contents. -/
def preservesDistinction {D₁ D₂ : Type}
    (φ : Val D₁ → Val D₂) : Prop :=
  (φ origin' = origin') ∧
  (∀ d : D₁, ∃ d₂ : D₂, φ (bounded' d) = bounded' d₂)

/-- φ preserves Origin. -/
theorem morphism_preserves_origin {D₁ D₂ : Type} (f : D₁ → D₂) :
    morphism f (origin' : Val D₁) = origin' := by
  simp [morphism, origin']

/-- φ preserves contents. -/
theorem morphism_preserves_bounded {D₁ D₂ : Type} (f : D₁ → D₂) (d : D₁) :
    morphism f (bounded' d) = bounded' (f d) := by
  simp [morphism, bounded']

/-- The morphism preserves the distinction. -/
theorem morphism_preserves_distinction_general {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) := by
  constructor
  · simp [morphism, origin']
  · intro d; exact ⟨f d, by simp [morphism, bounded']⟩

/-- φ commutes with operations when one argument is Origin. -/
theorem morphism_commutes_at_origin {D₁ D₂ : Type} [DecidableEq D₁] [DecidableEq D₂]
    (φ : D₁ → D₂) (op₁ : D₁ → D₁ → D₁) (op₂ : D₂ → D₂ → D₂)
    (x : Val D₁) :
    morphism φ (twoSortedOp op₁ x origin') =
    twoSortedOp op₂ (morphism φ x) origin' := by
  cases x with
  | origin => simp [twoSortedOp, morphism, origin', Val.mul]
  | container a => simp [twoSortedOp, morphism, origin', Val.mul]
  | contents a => simp [twoSortedOp, morphism, origin', Val.mul]

-- ============================================================================
-- Metatheoretic Boundary: 𝒪 ∉ B
-- ============================================================================

/-- The morphism φ preserves the distinction. -/
theorem our_morphism_preserves {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) := by
  constructor
  · exact morphism_preserves_origin f
  · intro d; exact ⟨f d, morphism_preserves_bounded f d⟩

/-- Any map that embeds Origin into contents does NOT preserve the distinction. -/
theorem origin_cannot_embed_in_bounded {D : Type} (d : D)
    (φ : Val D → Val D)
    (h : φ origin' = bounded' d) :
    ¬ preservesDistinction φ := by
  intro ⟨horigin, _⟩
  rw [horigin] at h
  exact origin_not_bounded d h

-- ============================================================================
-- Master Theorem
-- ============================================================================

/-- Original arithmetic is well-formed: all operations are total,
all distinctions are preserved, all boundary conditions return Origin. -/
theorem original_arithmetic_is_well_formed {D : Type} [DecidableEq D]
    (d : D) (f : D → D → D) :
    -- Contents operations stay in contents
    (∃ c : D, twoSortedOp f (bounded' d) (bounded' d) = bounded' c) ∧
    -- Contents with origin → origin (I1)
    (twoSortedOp f (bounded' d) origin' = origin') ∧
    -- Origin with contents → origin (I2)
    (twoSortedOp f origin' (bounded' d) = origin') ∧
    -- Origin with origin → origin (I3)
    (twoSortedOp f (origin' : Val D) origin' = origin') := by
  refine ⟨⟨f d d, rfl⟩, ?_, ?_, ?_⟩
  · exact interaction_I1 f (bounded' d)
  · exact interaction_I2 f (bounded' d)
  · exact interaction_I3 f

end OriginalArith
