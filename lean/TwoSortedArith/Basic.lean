/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import Std

/-!
# Two-Sorted Arithmetic: Basic Definitions and Core Theorems

A formalization of two-sorted arithmetic where zero decomposes into two
distinct sorts: **Origin** (the categorical boundary, 𝒪) and **Bounded**
(values inside a domain, 0_B).

The key result: given the Origin|Bounded split, the interaction axioms —
Origin absorbs every operation — follow by construction. The axioms I1 and I2
are independent (neither implies the other), and any absorbing classification
must match the Origin|Bounded split (`uniqueness_of_split` in Structure.lean).

Note: the Lean code proves properties of the two-sorted model. The claim
that real-world domains (division by zero, NaN, Russell's paradox) share
this structure is empirical — each domain is modeled as `Zero' D` and
verified to satisfy I1-I3 within that model.

## Main definitions

* `Origin` — the categorical boundary. Not a number. One inhabitant.
* `Bounded D` — a value inside domain `D`, carrying a distinction tag.
* `Zero' D` — the two-sorted zero: `Origin ⊕ Bounded D`.
* `twoSortedOp` — lifts a binary operation on `D` to `Zero' D`,
  returning `Origin` whenever either argument is `Origin`.
* `twoSortedDiv` — total division on `Zero' D`.
* `morphism` — structure-preserving map between two-sorted domains.
* `preservesDistinction` — the property that a map sends `Origin` to `Origin`
  and `Bounded` to `Bounded`.

## Main results

* `interaction_I1` / `interaction_I2` / `interaction_I3` — the interaction axioms.
* `zero_div_zero_same` — `0_B ÷ 0_B = 1` when distinctions match.
* `origin_cannot_embed_in_bounded` — `𝒪` cannot be mapped into `Bounded`
  without collapsing the distinction.
* `morphism_commutes_at_boundary` — the morphism φ is structure-preserving.
* `two_sorted_arithmetic_is_well_formed` — the master theorem.

## References

* [two-sorted arithmetic](https://github.com/knoxvilledatabase/two-sorted-arithmetic)
-/

namespace TwoSortedArith

-- ============================================================================
-- Core Types
-- ============================================================================

/-- The categorical origin. Not a number. The boundary condition of the
bounded domain. Has exactly one inhabitant. -/
inductive Origin : Type where
  | mk : Origin
deriving Repr, DecidableEq

/-- A value inside a bounded domain, carrying a distinction tag of type `D`. -/
structure Bounded (D : Type) where
  distinction : D
deriving Repr

/-- The two-sorted zero: either Origin (boundary) or Bounded (interior). -/
def Zero' (D : Type) := Origin ⊕ Bounded D

/-- Smart constructor for the Origin sort. -/
def origin' {D : Type} : Zero' D := Sum.inl Origin.mk

/-- Smart constructor for the Bounded sort. -/
def bounded' {D : Type} (d : D) : Zero' D := Sum.inr ⟨d⟩

-- ============================================================================
-- Axiom 𝒪1: Non-membership
-- ============================================================================

/-- 𝒪1: Origin is not a Bounded element. Proved by disjointness of `Sum`. -/
theorem origin_not_bounded {D : Type} (b : Bounded D) :
    (origin' : Zero' D) ≠ bounded' b.distinction := by
  simp [origin', bounded']

-- ============================================================================
-- Interaction Axioms (I1–I3)
-- ============================================================================

/-- Lift a binary operation on `D` to `Zero' D`. Returns `Origin` whenever
either argument is `Origin`. This is the two-sorted operation. -/
def twoSortedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (a b : Zero' D) : Zero' D :=
  match a, b with
  | Sum.inl _, _         => origin'
  | _, Sum.inl _         => origin'
  | Sum.inr x, Sum.inr y => bounded' (f x.distinction y.distinction)

/-- I1: `f(x, 𝒪) = 𝒪` for all `x`. Right-absorption. -/
theorem interaction_I1 {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Zero' D) :
    twoSortedOp f x origin' = origin' := by
  simp [twoSortedOp, origin']
  cases x with
  | inl _ => rfl
  | inr _ => rfl

/-- I2: `f(𝒪, x) = 𝒪` for all `x`. Left-absorption. -/
theorem interaction_I2 {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Zero' D) :
    twoSortedOp f origin' x = origin' := by
  simp [twoSortedOp, origin']

/-- I3: `f(𝒪, 𝒪) = 𝒪`. Self-absorption. (Redundant — follows from I1 or I2.) -/
theorem interaction_I3 {D : Type} [DecidableEq D]
    (f : D → D → D) :
    twoSortedOp f origin' origin' = origin' := by
  simp [twoSortedOp, origin']

-- ============================================================================
-- Two-Sorted Division
-- ============================================================================

/-- Result of two-sorted division. Total — every case is handled. -/
inductive DivResult where
  | IsOrigin : DivResult
  | IsOne    : DivResult
deriving Repr, DecidableEq

/-- Two-sorted division. Contents divided by contents reveals the container. -/
def twoSortedDiv {D : Type} [DecidableEq D] (a b : Zero' D) : DivResult :=
  match a, b with
  | Sum.inl _, _         => DivResult.IsOrigin
  | _, Sum.inl _         => DivResult.IsOrigin
  | Sum.inr x, Sum.inr y =>
      if x.distinction = y.distinction
      then DivResult.IsOne
      else DivResult.IsOrigin

/-- `0_B ÷ 0_B = 1` when distinctions match. -/
theorem zero_div_zero_same {D : Type} [DecidableEq D] (d : D) :
    twoSortedDiv (bounded' d) (bounded' d) = DivResult.IsOne := by
  simp [twoSortedDiv, bounded']

/-- `0_B ÷ 𝒪 = 𝒪`. -/
theorem zero_div_origin {D : Type} [DecidableEq D] (d : D) :
    twoSortedDiv (bounded' d) (origin' : Zero' D) = DivResult.IsOrigin := by
  simp [twoSortedDiv, origin', bounded']

/-- `𝒪 ÷ 𝒪 = 𝒪`. Self-stability (axiom 𝒪3). -/
theorem origin_div_origin {D : Type} [DecidableEq D] :
    twoSortedDiv (origin' : Zero' D) origin' = DivResult.IsOrigin := by
  simp [twoSortedDiv, origin']

-- ============================================================================
-- The Morphism φ
-- ============================================================================

/-- Structure-preserving map between two-sorted domains.
Maps bounded elements via `f`, preserves Origin. -/
def morphism {D₁ D₂ : Type} (f : D₁ → D₂) : Zero' D₁ → Zero' D₂
  | Sum.inl _ => origin'
  | Sum.inr x => bounded' (f x.distinction)

/-- The distinction-preserving property: a map sends Origin to Origin
and Bounded to Bounded. -/
def preservesDistinction {D₁ D₂ : Type}
    (φ : Zero' D₁ → Zero' D₂) : Prop :=
  (φ origin' = origin') ∧
  (∀ d : D₁, ∃ d₂ : D₂, φ (bounded' d) = bounded' d₂)

/-- φ preserves Origin. -/
theorem morphism_preserves_origin {D₁ D₂ : Type} (f : D₁ → D₂) :
    morphism f (origin' : Zero' D₁) = origin' := by
  simp [morphism, origin']

/-- φ preserves Bounded. -/
theorem morphism_preserves_bounded {D₁ D₂ : Type} (f : D₁ → D₂) (d : D₁) :
    morphism f (bounded' d) = bounded' (f d) := by
  simp [morphism, bounded']

/-- The morphism preserves the distinction. -/
theorem morphism_preserves_distinction_general {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) := by
  constructor
  · simp [morphism, origin']
  · intro d; exact ⟨f d, by simp [morphism, bounded']⟩

/-- φ commutes with operations at the boundary. -/
theorem morphism_commutes_at_boundary {D₁ D₂ : Type} [DecidableEq D₁] [DecidableEq D₂]
    (φ : D₁ → D₂) (op₁ : D₁ → D₁ → D₁) (op₂ : D₂ → D₂ → D₂)
    (x : Zero' D₁) :
    morphism φ (twoSortedOp op₁ x origin') =
    twoSortedOp op₂ (morphism φ x) origin' := by
  simp [twoSortedOp, morphism, origin']
  cases x with
  | inl _ => rfl
  | inr _ => rfl

-- ============================================================================
-- Metatheoretic Boundary: 𝒪 ∉ B
-- ============================================================================

/-- The morphism φ preserves the distinction. -/
theorem our_morphism_preserves {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) := by
  constructor
  · exact morphism_preserves_origin f
  · intro d; exact ⟨f d, morphism_preserves_bounded f d⟩

/-- Any map that embeds Origin into Bounded does NOT preserve the distinction.
𝒪 is necessarily outside B. -/
theorem origin_cannot_embed_in_bounded {D : Type} (d : D)
    (φ : Zero' D → Zero' D)
    (h : φ origin' = bounded' d) :
    ¬ preservesDistinction φ := by
  intro ⟨horigin, _⟩
  rw [horigin] at h
  exact origin_not_bounded ⟨d⟩ h

-- ============================================================================
-- Master Theorem
-- ============================================================================

/-- Two-sorted arithmetic is well-formed: all operations are total,
all distinctions are preserved, all boundary conditions return Origin. -/
theorem two_sorted_arithmetic_is_well_formed {D : Type} [DecidableEq D]
    (d : D) (f : D → D → D) :
    (∃ r : DivResult, twoSortedDiv (bounded' d) (bounded' d) = r) ∧
    (twoSortedDiv (bounded' d) (bounded' d) = DivResult.IsOne) ∧
    (twoSortedDiv (bounded' d) origin' = DivResult.IsOrigin) ∧
    (twoSortedOp f (bounded' d) origin' = origin') ∧
    (twoSortedOp f origin' (bounded' d) = origin') ∧
    (twoSortedDiv (origin' : Zero' D) origin' = DivResult.IsOrigin) := by
  refine ⟨⟨DivResult.IsOne, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact zero_div_zero_same d
  · exact zero_div_zero_same d
  · exact zero_div_origin d
  · exact interaction_I1 f (bounded' d)
  · exact interaction_I2 f (bounded' d)
  · exact origin_div_origin

end TwoSortedArith
