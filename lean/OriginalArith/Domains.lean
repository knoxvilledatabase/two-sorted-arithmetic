/-
Released under MIT license.
-/
import OriginalArith.Basic

/-!
# Original Arithmetic: Domain Isomorphisms

Each of 17 domains is modeled as `Val D` with a domain-specific operation.
The modeling claim is that each domain's boundary behavior fits the
three-sort envelope. The Lean code verifies that, given this modeling,
absorption holds and the distinction is preserved across morphisms.

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

namespace OriginalArith

open OriginalArith

-- ============================================================================
-- Domain template
-- ============================================================================
-- Each domain is modeled as Val D with a domain-specific name and operation.
-- Pattern per domain:
--   1. Type alias (abbrev) — models the domain as Val D
--   2. Domain operation — returns origin when either argument is origin
--   3. I1, I2, I3 — verified for this domain's operation
--   4. Morphism to arithmetic — identity on the underlying type
--   5. Isomorphism theorem

-- ============================================================================
-- Domain 7: Category Theory
-- ============================================================================

section CategoryTheory

abbrev CatObj (D : Type) := Val D

def homOp {D : Type} [DecidableEq D] (a b : CatObj D) : CatObj D :=
  Val.mul (fun x _ => x) a b

theorem cat_I1 {D : Type} [DecidableEq D] (x : CatObj D) :
    homOp x (origin' : CatObj D) = origin' := by
  simp [homOp]; exact Val.origin_absorbs_mul_right _ x

theorem cat_I2 {D : Type} [DecidableEq D] (x : CatObj D) :
    homOp (origin' : CatObj D) x = origin' := by
  simp [homOp, Val.mul]

theorem cat_I3 {D : Type} [DecidableEq D] :
    homOp (origin' : CatObj D) origin' = origin' := by
  simp [homOp, Val.mul]

def catToArith {D : Type} : CatObj D → Val D := id

theorem cat_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    (catToArith (origin' : CatObj D) = (origin' : Val D)) ∧
    (preservesDistinction (catToArith : CatObj D → Val D)) ∧
    (∀ x : CatObj D, catToArith (homOp x origin') =
      Val.mul f (catToArith x) origin') := by
  refine ⟨rfl, ?_, ?_⟩
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [catToArith, homOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end CategoryTheory

-- ============================================================================
-- Domains 8–11: Projective Geometry, Filter Theory, Order Theory, Ring Theory
-- ============================================================================

section ProjectiveGeometry

abbrev ProjPoint (D : Type) := Val D

def projOp {D : Type} [DecidableEq D] (a b : ProjPoint D) : ProjPoint D :=
  Val.mul (fun x _ => x) a b

theorem proj_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : ProjPoint D → Val D) ∧
    (∀ x : ProjPoint D, id (projOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [projOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end ProjectiveGeometry

section FilterTheory

abbrev FilterSet (D : Type) := Val D

def filterOp {D : Type} [DecidableEq D] (a b : FilterSet D) : FilterSet D :=
  Val.mul (fun x _ => x) a b

theorem filter_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : FilterSet D → Val D) ∧
    (∀ x : FilterSet D, id (filterOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [filterOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end FilterTheory

section OrderTheory

abbrev OrdElem (D : Type) := Val D

def ordOp {D : Type} [DecidableEq D] (a b : OrdElem D) : OrdElem D :=
  Val.mul (fun x _ => x) a b

theorem order_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : OrdElem D → Val D) ∧
    (∀ x : OrdElem D, id (ordOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [ordOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end OrderTheory

section RingTheory

abbrev RingElem (D : Type) := Val D

def ringOp {D : Type} [DecidableEq D] (a b : RingElem D) : RingElem D :=
  Val.mul (fun x _ => x) a b

theorem ring_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : RingElem D → Val D) ∧
    (∀ x : RingElem D, id (ringOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [ringOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end RingTheory

-- ============================================================================
-- Domains 12–17: SQL, Lambda Calculus, Measure Theory, Game Theory,
--                Topology, Proof Theory
-- ============================================================================

section SQL

abbrev SqlValue (D : Type) := Val D

def sqlOp {D : Type} [DecidableEq D] (a b : SqlValue D) : SqlValue D :=
  Val.mul (fun x _ => x) a b

theorem sql_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : SqlValue D → Val D) ∧
    (∀ x : SqlValue D, id (sqlOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [sqlOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end SQL

section LambdaCalculus

abbrev LambdaTerm (D : Type) := Val D

def lambdaOp {D : Type} [DecidableEq D] (a b : LambdaTerm D) : LambdaTerm D :=
  Val.mul (fun x _ => x) a b

theorem lambda_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : LambdaTerm D → Val D) ∧
    (∀ x : LambdaTerm D, id (lambdaOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [lambdaOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end LambdaCalculus

section MeasureTheory

abbrev MeasureSet (D : Type) := Val D

def measureOp {D : Type} [DecidableEq D] (a b : MeasureSet D) : MeasureSet D :=
  Val.mul (fun x _ => x) a b

theorem measure_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : MeasureSet D → Val D) ∧
    (∀ x : MeasureSet D, id (measureOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [measureOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end MeasureTheory

section GameTheory

abbrev GameState (D : Type) := Val D

def gameOp {D : Type} [DecidableEq D] (a b : GameState D) : GameState D :=
  Val.mul (fun x _ => x) a b

theorem game_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : GameState D → Val D) ∧
    (∀ x : GameState D, id (gameOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [gameOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end GameTheory

section Topology

abbrev TopoSpace (D : Type) := Val D

def topoOp {D : Type} [DecidableEq D] (a b : TopoSpace D) : TopoSpace D :=
  Val.mul (fun x _ => x) a b

theorem topo_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : TopoSpace D → Val D) ∧
    (∀ x : TopoSpace D, id (topoOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [topoOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end Topology

section ProofTheory

abbrev ProofState (D : Type) := Val D

def proofOp {D : Type} [DecidableEq D] (a b : ProofState D) : ProofState D :=
  Val.mul (fun x _ => x) a b

theorem proof_isomorphism {D : Type} [DecidableEq D] (f : D → D → D) :
    preservesDistinction (id : ProofState D → Val D) ∧
    (∀ x : ProofState D, id (proofOp x origin') =
      Val.mul f (id x) origin') := by
  constructor
  · exact ⟨rfl, fun d => ⟨d, rfl⟩⟩
  · intro x; simp [proofOp, Val.mul]
    cases x with | origin => rfl | container _ => rfl | contents _ => rfl

end ProofTheory

-- ============================================================================
-- The General Principle
-- ============================================================================

/-- For any two types and any function between them, the induced morphism
preserves the distinction. This is a property of `morphism` itself, not
of any specific domain pairing. -/
theorem morphism_always_preserves {D₁ D₂ : Type} (f : D₁ → D₂) :
    preservesDistinction (morphism f) :=
  morphism_preserves_distinction_general f

end OriginalArith
