/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import TwoSortedArith.Basic

/-!
# Two-Sorted Arithmetic: Domain Isomorphisms

Each of 17 domains is modeled as `Zero' D` with a domain-specific operation.
The modeling claim is that each domain's boundary behavior fits the two-sorted
envelope. The Lean code verifies that, given this modeling, I1-I3 hold and
the distinction is preserved across morphisms.

The connection between the model and the real domain (e.g., "SQL NULL behaves
like Origin") is empirical, not proved here. What is proved: if you model it
this way, the structure is consistent and composes.

## Domains

1. Arithmetic (division by zero)
2. Set Theory (Russell's paradox / ∈ at the boundary)
3. Computability (halting problem)
4. Formal Logic (Gödel / provability at the boundary)
5. IEEE 754 (NaN propagation)
6. Truth Theory (liar's paradox)
7. Category Theory (initial object / empty hom-set)
8. Projective Geometry (points at infinity)
9. Filter Theory (ultrafilter at the boundary)
10. Order Theory (bottom element absorption)
11. Ring Theory (zero divisors)
12. SQL (NULL propagation)
13. Lambda Calculus (Ω divergence)
14. Measure Theory (null sets)
15. Game Theory (losing positions)
16. Topology (boundary of open sets)
17. Proof Theory (cut elimination at the boundary)

## Main result

* `morphism_always_preserves` — for any two types `D₁` and `D₂` and any function
  `f : D₁ → D₂`, the induced morphism preserves the distinction. This is a
  property of `morphism` itself, not a claim about specific domain pairings.
-/

namespace TwoSortedArith

open TwoSortedArith

-- ============================================================================
-- Domain template
-- ============================================================================
-- Each domain is modeled as Zero' D with a domain-specific name and operation.
-- This is a modeling choice: we claim the domain's boundary behavior fits the
-- two-sorted envelope. The Lean code verifies internal consistency of that model.
-- It does not prove the modeling is the only correct one.
--
-- Pattern per domain:
--   1. Type alias (abbrev) — models the domain as Zero' D
--   2. Domain operation — returns Origin when either argument is Origin
--   3. I1, I2, I3 — verified for this domain's operation
--   4. Morphism to arithmetic — identity on the underlying type
--   5. Three-part isomorphism theorem

-- ============================================================================
-- Domain 7: Category Theory
-- ============================================================================

section CategoryTheory

abbrev CatObj (D : Type) := Zero' D

def homOp {D : Type} [DecidableEq D] (a b : CatObj D) : CatObj D :=
  match a, b with
  | Sum.inl _, _         => origin'
  | _, Sum.inl _         => origin'
  | Sum.inr x, Sum.inr _ => bounded' x.distinction

theorem cat_I1 {D : Type} [DecidableEq D] (x : CatObj D) :
    homOp x (origin' : CatObj D) = origin' := by
  simp [homOp, origin']; cases x with | inl _ => rfl | inr _ => rfl

theorem cat_I2 {D : Type} [DecidableEq D] (x : CatObj D) :
    homOp (origin' : CatObj D) x = origin' := by
  simp [homOp, origin']

theorem cat_I3 {D : Type} [DecidableEq D] :
    homOp (origin' : CatObj D) origin' = origin' := by
  simp [homOp, origin']

def catToArith {D : Type} : CatObj D → Zero' D := id

theorem cat_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    (catToArith (origin' : CatObj D) = (origin' : Zero' D)) ∧
    (preservesDistinction (catToArith : CatObj D → Zero' D)) ∧
    (∀ x : CatObj D, catToArith (homOp x origin') =
      twoSortedOp f (catToArith x) origin') := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [catToArith, homOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end CategoryTheory

-- ============================================================================
-- Domains 8–11: Projective Geometry, Filter Theory, Order Theory, Ring Theory
-- ============================================================================
-- Each follows the same pattern. The domain operation is a type alias for
-- Zero' D with a domain-specific name, and the morphism is identity.

section ProjectiveGeometry

abbrev ProjPoint (D : Type) := Zero' D

def projOp {D : Type} [DecidableEq D] (a b : ProjPoint D) : ProjPoint D :=
  twoSortedOp (fun x _ => x) a b

theorem proj_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : ProjPoint D → Zero' D) ∧
    (∀ x : ProjPoint D, id (projOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [projOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end ProjectiveGeometry

section FilterTheory

abbrev FilterSet (D : Type) := Zero' D

def filterOp {D : Type} [DecidableEq D] (a b : FilterSet D) : FilterSet D :=
  twoSortedOp (fun x _ => x) a b

theorem filter_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : FilterSet D → Zero' D) ∧
    (∀ x : FilterSet D, id (filterOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [filterOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end FilterTheory

section OrderTheory

abbrev OrdElem (D : Type) := Zero' D

def ordOp {D : Type} [DecidableEq D] (a b : OrdElem D) : OrdElem D :=
  twoSortedOp (fun x _ => x) a b

theorem order_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : OrdElem D → Zero' D) ∧
    (∀ x : OrdElem D, id (ordOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [ordOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end OrderTheory

section RingTheory

abbrev RingElem (D : Type) := Zero' D

def ringOp {D : Type} [DecidableEq D] (a b : RingElem D) : RingElem D :=
  twoSortedOp (fun x _ => x) a b

theorem ring_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : RingElem D → Zero' D) ∧
    (∀ x : RingElem D, id (ringOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [ringOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end RingTheory

-- ============================================================================
-- Domains 12–17: SQL, Lambda Calculus, Measure Theory, Game Theory,
--                Topology, Proof Theory
-- ============================================================================

section SQL

abbrev SqlValue (D : Type) := Zero' D

def sqlOp {D : Type} [DecidableEq D] (a b : SqlValue D) : SqlValue D :=
  twoSortedOp (fun x _ => x) a b

theorem sql_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : SqlValue D → Zero' D) ∧
    (∀ x : SqlValue D, id (sqlOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [sqlOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end SQL

section LambdaCalculus

abbrev LambdaTerm (D : Type) := Zero' D

def lambdaOp {D : Type} [DecidableEq D] (a b : LambdaTerm D) : LambdaTerm D :=
  twoSortedOp (fun x _ => x) a b

theorem lambda_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : LambdaTerm D → Zero' D) ∧
    (∀ x : LambdaTerm D, id (lambdaOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [lambdaOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end LambdaCalculus

section MeasureTheory

abbrev MeasureSet (D : Type) := Zero' D

def measureOp {D : Type} [DecidableEq D] (a b : MeasureSet D) : MeasureSet D :=
  twoSortedOp (fun x _ => x) a b

theorem measure_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : MeasureSet D → Zero' D) ∧
    (∀ x : MeasureSet D, id (measureOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [measureOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end MeasureTheory

section GameTheory

abbrev GameState (D : Type) := Zero' D

def gameOp {D : Type} [DecidableEq D] (a b : GameState D) : GameState D :=
  twoSortedOp (fun x _ => x) a b

theorem game_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : GameState D → Zero' D) ∧
    (∀ x : GameState D, id (gameOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [gameOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end GameTheory

section Topology

abbrev TopoSpace (D : Type) := Zero' D

def topoOp {D : Type} [DecidableEq D] (a b : TopoSpace D) : TopoSpace D :=
  twoSortedOp (fun x _ => x) a b

theorem topo_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : TopoSpace D → Zero' D) ∧
    (∀ x : TopoSpace D, id (topoOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [topoOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end Topology

section ProofTheory

abbrev ProofState (D : Type) := Zero' D

def proofOp {D : Type} [DecidableEq D] (a b : ProofState D) : ProofState D :=
  twoSortedOp (fun x _ => x) a b

theorem proof_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : ProofState D → Zero' D) ∧
    (∀ x : ProofState D, id (proofOp x origin') =
      twoSortedOp f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [proofOp, twoSortedOp, origin']
    cases x with | inl _ => rfl | inr _ => rfl

end ProofTheory

-- ============================================================================
-- The General Principle
-- ============================================================================
-- This is a single universally-quantified theorem, not 136 separate proofs.
-- It says: for any two types and any function between them, the induced
-- morphism preserves the distinction. The 17-domain claim is that each
-- domain fits this model. The theorem verifies the model is consistent.

/-- For any two types and any function between them, the induced morphism
preserves the distinction. This is a property of `morphism` itself, not
of any specific domain pairing. -/
theorem morphism_always_preserves {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) :=
  morphism_preserves_distinction_general f

end TwoSortedArith
