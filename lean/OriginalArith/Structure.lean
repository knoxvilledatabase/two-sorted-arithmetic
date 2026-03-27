/-
Copyright (c) 2024-2026 Knox Database. All rights reserved.
Released under MIT license.
Authors: Knox Database
-/
import OriginalArith.Basic

/-!
# Two-Sorted Arithmetic: Structural Properties

Algebraic and categorical properties of the two-sorted system.
These theorems establish consistency, rigidity, and standard algebraic structure.
`Zero' D` with `zBind` is the Option/Maybe monad; this is not a novel claim but
confirms the two-sorted system sits in a well-understood algebraic framework.

## Main results

### Characterization
* `sort_dichotomy` — every element is Origin or Bounded, no third form.
* `origin_uniqueness` — Origin has exactly one inhabitant.
* `absorber_is_origin` — any element absorbing everything must be Origin.
* `morphism_uniqueness` — morphisms are unique given the bounded map.

### Algebraic structure
* `twoSortedOp_associative` — sort-level associativity.
* `origin_propagation_commutative` — commutativity of Origin propagation.
* `origin_universal_absorber` — Origin absorbs every operation simultaneously.
* `contents_div_contents_eq_container` — `0_B ÷ 0_B = 1` (contents reveal container).

### Functoriality
* `morphism_composition_transitivity` — morphisms compose.
* `functor_identity` — `morphism id = id`.
* `functor_composition` — `morphism (g ∘ f) = morphism g ∘ morphism f`.

### Monad laws (Option/Maybe)
* `monad_left_identity` / `monad_right_identity` / `monad_associativity`.
* `monad_origin_absorbs` — `None >>= f = None`, standard Option behavior.

### Axiom analysis
* `three_axioms_reduce_to_two` — I3 is redundant; {I1, I2} suffices.
* `axiom_independence` — I1 and I2 are genuinely independent.

### Propagation
* `origin_propagates_depth` — Origin propagates through arbitrary nesting depth.

### Decidability
* `sort_membership_exclusive` — every element is in exactly one sort (XOR).
* `classifySort` — computable sort classification.

### Negative tests
* `leaky_violates_I2` — an operation violating absorption fails the isomorphism.
* `bad_map_fails_distinction` — mapping Origin to Bounded breaks the distinction.
-/

namespace OriginalArith

open OriginalArith

-- ============================================================================
-- Morphism Composition / Transitivity
-- ============================================================================

/-- Morphism composition equals direct morphism. -/
theorem morphism_composition_transitivity {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    ∀ x : Zero' D₁, morphism g (morphism f x) = morphism (g ∘ f) x := by
  intro x
  cases x with
  | inl _ => simp [morphism, origin']
  | inr v => simp [morphism, bounded', Function.comp]

/-- Composition preserves distinction. -/
theorem composition_preserves_distinction {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    preservesDistinction (morphism (g ∘ f) : Zero' D₁ → Zero' D₃) :=
  morphism_preserves_distinction_general (g ∘ f)

-- ============================================================================
-- Contents ÷ Contents = Container
-- ============================================================================

-- Contents ÷ Contents uses twoSortedDiv from Basic.lean directly.
-- No separate type needed — DivResult.IsOne is the container revealed.

/-- Self-division of bounded elements with matching distinction reveals the container.
This is a restatement of `zero_div_zero_same` from Basic.lean for clarity. -/
theorem contents_reveal_container {D : Type} [DecidableEq D] (d : D) :
    twoSortedDiv (bounded' d) (bounded' d) = DivResult.IsOne :=
  zero_div_zero_same d

-- ============================================================================
-- Absorber Characterization
-- ============================================================================
-- The real uniqueness result is `absorber_is_origin` below: if an element
-- absorbs everything under every operation, it must be origin'.
-- That theorem does the actual work. We do not claim a stronger uniqueness
-- result than what the code proves.

-- ============================================================================
-- Sort Dichotomy
-- ============================================================================

/-- Every element is either Origin or Bounded. No third form. -/
theorem sort_dichotomy {D : Type} (x : Zero' D) :
    (x = origin') ∨ (∃ d : D, x = bounded' d) := by
  cases x with
  | inl u => left; cases u; rfl
  | inr v => right; exact ⟨v.distinction, rfl⟩

-- (no_intermediate_sort was removed: it was P ∨ ¬P, i.e. excluded middle,
-- not a structural result. The real content is in absorber_is_origin below,
-- which proves that any element absorbing everything must be origin'.)

-- ============================================================================
-- Associativity
-- ============================================================================

/-- Sort-level associativity when the underlying operation is associative. -/
theorem twoSortedOp_associative {D : Type} [DecidableEq D]
    (f : D → D → D)
    (f_assoc : ∀ x y z : D, f (f x y) z = f x (f y z))
    (a b c : Zero' D) :
    twoSortedOp f (twoSortedOp f a b) c = twoSortedOp f a (twoSortedOp f b c) := by
  cases a with
  | inl _ => simp [twoSortedOp, origin']
  | inr va =>
    cases b with
    | inl _ => simp [twoSortedOp, origin']
    | inr vb =>
      cases c with
      | inl _ => simp [twoSortedOp, origin', bounded']
      | inr vc =>
        simp [twoSortedOp, bounded']
        exact congrArg (fun x => Sum.inr (Bounded.mk x))
          (f_assoc va.distinction vb.distinction vc.distinction)

-- ============================================================================
-- Origin Uniqueness
-- ============================================================================

/-- Origin has exactly one inhabitant. -/
theorem origin_uniqueness (x y : Origin) : x = y := by
  cases x; cases y; rfl

-- ============================================================================
-- Morphism Uniqueness
-- ============================================================================

/-- Two distinction-preserving morphisms that agree on bounded elements
agree on all elements. -/
theorem morphism_uniqueness {D₁ D₂ : Type}
    (φ ψ : Zero' D₁ → Zero' D₂)
    (hφ : preservesDistinction φ) (hψ : preservesDistinction ψ)
    (h_agree : ∀ d : D₁, φ (bounded' d) = ψ (bounded' d)) :
    ∀ x : Zero' D₁, φ x = ψ x := by
  intro x
  cases x with
  | inl u =>
    have h1 : (Sum.inl u : Zero' D₁) = origin' := by cases u; rfl
    rw [h1, hφ.1, hψ.1]
  | inr v => exact h_agree v.distinction

-- ============================================================================
-- Functoriality
-- ============================================================================

/-- `morphism id = id`. -/
theorem functor_identity {D : Type} :
    ∀ x : Zero' D, morphism id x = x := by
  intro x; cases x with
  | inl u => cases u; rfl
  | inr v => simp [morphism, bounded']

/-- `morphism (g ∘ f) = morphism g ∘ morphism f`. -/
theorem functor_composition {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    ∀ x : Zero' D₁, morphism (g ∘ f) x = (morphism g ∘ morphism f) x := by
  intro x; simp [Function.comp]
  exact (morphism_composition_transitivity f g x).symm

-- ============================================================================
-- Monad Laws
-- ============================================================================

def zReturn {D : Type} (d : D) : Zero' D := bounded' d

def zBind {D : Type} (m : Zero' D) (f : D → Zero' D) : Zero' D :=
  match m with
  | Sum.inl _ => origin'
  | Sum.inr v => f v.distinction

/-- Left identity: `return a >>= f = f a`. -/
theorem monad_left_identity {D : Type} (a : D) (f : D → Zero' D) :
    zBind (zReturn a) f = f a := by
  simp [zBind, zReturn, bounded']

/-- Right identity: `m >>= return = m`. -/
theorem monad_right_identity {D : Type} (m : Zero' D) :
    zBind m zReturn = m := by
  cases m with
  | inl u => cases u; rfl
  | inr v => simp [zBind, zReturn, bounded']

/-- Associativity: `(m >>= f) >>= g = m >>= (λx. f x >>= g)`. -/
theorem monad_associativity {D : Type} (m : Zero' D)
    (f : D → Zero' D) (g : D → Zero' D) :
    zBind (zBind m f) g = zBind m (fun x => zBind (f x) g) := by
  cases m with
  | inl u => cases u; simp [zBind, origin']
  | inr v => simp [zBind]

/-- Origin absorbs bind, the standard Option/Maybe behavior: `None >>= f = None`. -/
theorem monad_origin_absorbs {D : Type} (f : D → Zero' D) :
    zBind (origin' : Zero' D) f = origin' := by
  simp [zBind, origin']

-- ============================================================================
-- Axiom Reduction: {I1, I2, I3} → {I1, I2}
-- ============================================================================

/-- I3 follows from I1 alone. The three-axiom system reduces to two. -/
theorem three_axioms_reduce_to_two {D : Type} [DecidableEq D]
    (op : Zero' D → Zero' D → Zero' D)
    (h_I1 : ∀ x : Zero' D, op x origin' = origin')
    (_h_I2 : ∀ x : Zero' D, op origin' x = origin') :
    op origin' origin' = origin' := by
  exact h_I1 origin'

-- ============================================================================
-- Axiom Independence: I1 ⊬ I2 and I2 ⊬ I1
-- ============================================================================

/-- Operation satisfying I1 but not I2. -/
def opSatI1NotI2 {D : Type} (a b : Zero' D) : Zero' D :=
  match a, b with
  | _, Sum.inl _         => origin'
  | Sum.inl _, Sum.inr v => bounded' v.distinction
  | Sum.inr x, Sum.inr _ => bounded' x.distinction

theorem opI1NotI2_satisfies_I1 {D : Type} (x : Zero' D) :
    opSatI1NotI2 x (origin' : Zero' D) = origin' := by
  cases x with | inl _ => rfl | inr _ => rfl

theorem opI1NotI2_violates_I2 {D : Type} (d : D) :
    opSatI1NotI2 (origin' : Zero' D) (bounded' d) ≠ origin' := by
  simp [opSatI1NotI2, origin', bounded']

/-- Operation satisfying I2 but not I1. -/
def opSatI2NotI1 {D : Type} (a b : Zero' D) : Zero' D :=
  match a, b with
  | Sum.inl _, _         => origin'    -- I2: left-Origin absorbs
  | Sum.inr x, Sum.inl _ => bounded' x.distinction  -- I1 violation: right-Origin passes through
  | Sum.inr x, Sum.inr _ => bounded' x.distinction

theorem opI2NotI1_satisfies_I2 {D : Type} (x : Zero' D) :
    opSatI2NotI1 (origin' : Zero' D) x = origin' := by
  simp [opSatI2NotI1, origin']

theorem opI2NotI1_violates_I1 {D : Type} (d : D) :
    opSatI2NotI1 (bounded' d) (origin' : Zero' D) ≠ origin' := by
  simp [opSatI2NotI1, origin', bounded']

-- ============================================================================
-- Origin Propagation at Arbitrary Depth
-- ============================================================================

def iteratedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (base : Zero' D) (arg : Zero' D) : Nat → Zero' D
  | 0     => base
  | n + 1 => twoSortedOp f (iteratedOp f base arg n) arg

/-- Origin propagates through any depth of iteration. -/
theorem origin_propagates_depth {D : Type} [DecidableEq D]
    (f : D → D → D) (arg : Zero' D) (n : Nat) :
    iteratedOp f origin' arg n = origin' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [iteratedOp]; rw [ih]; simp [twoSortedOp, origin']

-- ============================================================================
-- Commutativity of Origin Propagation
-- ============================================================================

/-- Origin propagation is commutative even when the underlying operation is not. -/
theorem origin_propagation_commutative {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Zero' D) :
    twoSortedOp f origin' x = twoSortedOp f x origin' := by
  cases x with
  | inl _ => rfl
  | inr _ => simp [twoSortedOp, origin']

-- ============================================================================
-- Universal Absorber / Fixed Point
-- ============================================================================

/-- Origin absorbs every operation simultaneously. -/
theorem origin_universal_absorber {D : Type} [DecidableEq D] (x : Zero' D) :
    ∀ f : D → D → D,
      twoSortedOp f origin' x = origin' ∧ twoSortedOp f x origin' = origin' := by
  intro f; exact ⟨interaction_I2 f x, interaction_I1 f x⟩

/-- The absorber is unique: if an element absorbs everything, it must be Origin. -/
theorem absorber_is_origin {D : Type} [DecidableEq D] [Nonempty D]
    (z : Zero' D)
    (h : ∀ (f : D → D → D) (y : Zero' D), twoSortedOp f z y = origin') :
    z = origin' := by
  cases z with
  | inl u => cases u; rfl
  | inr v =>
    exfalso
    have d := Classical.choice ‹Nonempty D›
    have := h (fun a _ => a) (bounded' d)
    simp [twoSortedOp, origin', bounded'] at this

-- ============================================================================
-- Sort Membership Decidability
-- ============================================================================

/-- Computable sort classification. -/
def classifySort {D : Type} (x : Zero' D) : Bool :=
  match x with
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- Every element is in exactly one sort (XOR). -/
theorem sort_membership_exclusive {D : Type} (x : Zero' D) :
    (x = origin' ∧ ¬ ∃ d : D, x = bounded' d) ∨
    (x ≠ origin' ∧ ∃ d : D, x = bounded' d) := by
  cases x with
  | inl u =>
    left; constructor
    · cases u; rfl
    · intro ⟨_, h⟩; simp [bounded'] at h
  | inr v =>
    right; constructor
    · simp [origin']
    · exact ⟨v.distinction, rfl⟩

-- ============================================================================
-- Bounded Injectivity
-- ============================================================================
-- These theorems prove that bounded elements are uniquely determined by their
-- distinction tag. The Bounded constructor is injective.
--
-- (The deeper claim — that 0 and 1 are inseparable, that you cannot have the
-- mark without the sheet — lives in PROOF_OF_CONCEPT.md as questions, not here
-- as theorems. The philosophy is ahead of the formalization. That's the point.)

/-- Bounded elements are uniquely determined by their distinction. -/
theorem bounded_determined_by_distinction {D : Type} (d₁ d₂ : D) :
    (bounded' d₁ : Zero' D) = bounded' d₂ ↔ d₁ = d₂ := by
  constructor
  · intro h
    have : Sum.inr (⟨d₁⟩ : Bounded D) = Sum.inr (⟨d₂⟩ : Bounded D) := h
    cases this; rfl
  · intro h; rw [h]

/-- The Bounded constructor is injective. -/
theorem bounded_injective {D : Type} :
    Function.Injective (Bounded.mk : D → Bounded D) := by
  intros d₁ d₂ h; cases h; rfl

-- ============================================================================
-- Negative Tests
-- ============================================================================

/-- A leaky operation where Origin does NOT absorb. -/
def leakyOp {D : Type} [DecidableEq D] (a b : Zero' D) : Zero' D :=
  match a, b with
  | Sum.inl _, x         => x
  | x, Sum.inl _         => x
  | Sum.inr x, Sum.inr _ => bounded' x.distinction

/-- The leaky operation violates I2. -/
theorem leaky_violates_I2 {D : Type} [DecidableEq D] (d : D) :
    leakyOp (origin' : Zero' D) (bounded' d) ≠ origin' := by
  simp [leakyOp, origin', bounded']

/-- A morphism from the leaky domain fails commutativity with arithmetic. -/
theorem leaky_morphism_fails {D : Type} [DecidableEq D]
    (f : D → D → D) (d : D) :
    leakyOp (origin' : Zero' D) (bounded' d) ≠
    twoSortedOp f (origin' : Zero' D) (bounded' d) := by
  simp [leakyOp, twoSortedOp, origin', bounded']

/-- A map that sends Origin to Bounded fails to preserve the distinction. -/
def badMap {D : Type} (d₀ : D) : Zero' D → Zero' D
  | Sum.inl _ => bounded' d₀
  | Sum.inr x => bounded' x.distinction

theorem bad_map_fails_distinction {D : Type} [DecidableEq D] (d₀ : D) :
    ¬ preservesDistinction (badMap d₀ : Zero' D → Zero' D) := by
  intro ⟨h, _⟩
  simp [badMap, origin', bounded'] at h

end OriginalArith
