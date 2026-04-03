/-
Released under MIT license.
-/
import OriginalArith.Basic

/-!
# Original Arithmetic: Structural Properties

Algebraic and categorical properties of the Val α system.
These theorems establish consistency, rigidity, and standard algebraic structure.

## Main results

### Characterization
* `sort_trichotomy` — every element is origin, container, or contents.
* `absorber_is_origin` — any element absorbing everything must be origin.
* `morphism_uniqueness` — morphisms are unique given the contents map.

### Algebraic structure
* `twoSortedOp_associative` — sort-level associativity.
* `origin_propagation_commutative` — commutativity of origin propagation.
* `origin_universal_absorber` — origin absorbs every operation simultaneously.

### Functoriality
* `morphism_composition_transitivity` — morphisms compose.
* `functor_identity` — `morphism id = id`.
* `functor_composition` — `morphism (g ∘ f) = morphism g ∘ morphism f`.

### Monad laws
* `monad_left_identity` / `monad_right_identity` / `monad_associativity`.
* `monad_origin_absorbs` — `None >>= f = None`, standard Option behavior.

### Axiom analysis
* `three_axioms_reduce_to_two` — I3 is redundant; {I1, I2} suffices.
* `axiom_independence` — I1 and I2 are genuinely independent.

### Propagation
* `origin_propagates_depth` — origin propagates through arbitrary nesting depth.

### Decidability
* `sort_membership_exclusive` — every element is in exactly one sort.
* `classifySort` — computable sort classification.

### Negative tests
* `leaky_violates_I2` — an operation violating absorption fails the isomorphism.
* `bad_map_fails_distinction` — mapping origin to contents breaks the distinction.
-/

namespace OriginalArith

open OriginalArith

-- ============================================================================
-- Morphism Composition / Transitivity
-- ============================================================================

/-- Morphism composition equals direct morphism. -/
theorem morphism_composition_transitivity {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    ∀ x : Val D₁, morphism g (morphism f x) = morphism (g ∘ f) x := by
  intro x
  cases x with
  | origin => simp [morphism]
  | container a => simp [morphism, Function.comp]
  | contents a => simp [morphism, Function.comp]

/-- Composition preserves distinction. -/
theorem composition_preserves_distinction {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    preservesDistinction (morphism (g ∘ f) : Val D₁ → Val D₃) :=
  morphism_preserves_distinction_general (g ∘ f)

-- ============================================================================
-- Contents ÷ Contents = Container
-- ============================================================================

/-- Self-division of contents elements reveals the structure.
This restates the Foundation.lean theorem for clarity. -/
theorem contents_reveal_container {D : Type} [DecidableEq D]
    (f : D → D → D) (g : D → D) (d : D) :
    Val.div f g (bounded' d) (bounded' d) = Val.contents (f d (g d)) :=
  zero_div_zero_same f g d

-- ============================================================================
-- Sort Trichotomy
-- ============================================================================

/-- Every element is origin, container, or contents. -/
theorem sort_dichotomy {D : Type} (x : Val D) :
    (x = origin') ∨ (∃ a : D, x = Val.container a) ∨ (∃ d : D, x = bounded' d) :=
  Val.sort_trichotomy x

-- ============================================================================
-- Associativity
-- ============================================================================

/-- Sort-level associativity for all Val constructors. -/
theorem twoSortedOp_associative {D : Type} [DecidableEq D]
    (f : D → D → D)
    (f_assoc : ∀ x y z : D, f (f x y) z = f x (f y z))
    (a b c : Val D) :
    Val.mul f (Val.mul f a b) c = Val.mul f a (Val.mul f b c) := by
  cases a with
  | origin => simp [Val.mul]
  | container va =>
    cases b with
    | origin => simp [Val.mul]
    | container vb =>
      cases c with
      | origin => simp [Val.mul]
      | container vc => simp [Val.mul, f_assoc]
      | contents vc => simp [Val.mul, f_assoc]
    | contents vb =>
      cases c with
      | origin => simp [Val.mul]
      | container vc => simp [Val.mul, f_assoc]
      | contents vc => simp [Val.mul, f_assoc]
  | contents va =>
    cases b with
    | origin => simp [Val.mul]
    | container vb =>
      cases c with
      | origin => simp [Val.mul]
      | container vc => simp [Val.mul, f_assoc]
      | contents vc => simp [Val.mul, f_assoc]
    | contents vb =>
      cases c with
      | origin => simp [Val.mul]
      | container vc => simp [Val.mul, f_assoc]
      | contents vc => simp [Val.mul, f_assoc]

-- ============================================================================
-- Morphism Uniqueness
-- ============================================================================

/-- Two distinction-preserving morphisms that agree on contents and container elements
agree on all elements. With three sorts, both contents and container agreement
are required. -/
theorem morphism_uniqueness {D₁ D₂ : Type}
    (φ ψ : Val D₁ → Val D₂)
    (hφ : preservesDistinction φ) (hψ : preservesDistinction ψ)
    (h_agree_contents : ∀ d : D₁, φ (bounded' d) = ψ (bounded' d))
    (h_agree_container : ∀ a : D₁, φ (Val.container a) = ψ (Val.container a)) :
    ∀ x : Val D₁, φ x = ψ x := by
  intro x
  cases x with
  | origin => rw [hφ.1, hψ.1]
  | container a => exact h_agree_container a
  | contents a => exact h_agree_contents a

-- ============================================================================
-- Functoriality
-- ============================================================================

/-- `morphism id = id`. -/
theorem functor_identity {D : Type} :
    ∀ x : Val D, morphism id x = x := by
  intro x; cases x with
  | origin => rfl
  | container a => simp [morphism]
  | contents a => simp [morphism]

/-- `morphism (g ∘ f) = morphism g ∘ morphism f`. -/
theorem functor_composition {D₁ D₂ D₃ : Type}
    (f : D₁ → D₂) (g : D₂ → D₃) :
    ∀ x : Val D₁, morphism (g ∘ f) x = (morphism g ∘ morphism f) x := by
  intro x; simp [Function.comp]
  exact (morphism_composition_transitivity f g x).symm

-- ============================================================================
-- Monad Laws
-- ============================================================================

def zReturn {D : Type} (d : D) : Val D := bounded' d

def zBind {D : Type} (m : Val D) (f : D → Val D) : Val D :=
  match m with
  | Val.origin => origin'
  | Val.container a => Val.container a  -- container preserves itself
  | Val.contents a => f a

/-- Left identity: `return a >>= f = f a`. -/
theorem monad_left_identity {D : Type} (a : D) (f : D → Val D) :
    zBind (zReturn a) f = f a := by
  simp [zBind, zReturn, bounded']

/-- Right identity: `m >>= return = m`. -/
theorem monad_right_identity {D : Type} (m : Val D) :
    zBind m zReturn = m := by
  cases m with
  | origin => rfl
  | container a => rfl
  | contents a => simp [zBind, zReturn, bounded']

/-- Associativity: `(m >>= f) >>= g = m >>= (λx. f x >>= g)`. -/
theorem monad_associativity {D : Type} (m : Val D)
    (f : D → Val D) (g : D → Val D) :
    zBind (zBind m f) g = zBind m (fun x => zBind (f x) g) := by
  cases m with
  | origin => simp [zBind]
  | container a => simp [zBind]
  | contents a => simp [zBind]

/-- Origin absorbs bind, the standard Option/Maybe behavior: `None >>= f = None`. -/
theorem monad_origin_absorbs {D : Type} (f : D → Val D) :
    zBind (origin' : Val D) f = origin' := by
  simp [zBind, origin']

-- ============================================================================
-- Axiom Reduction: {I1, I2, I3} → {I1, I2}
-- ============================================================================

/-- I3 follows from I1 alone. The three-axiom system reduces to two. -/
theorem three_axioms_reduce_to_two {D : Type} [DecidableEq D]
    (op : Val D → Val D → Val D)
    (h_I1 : ∀ x : Val D, op x origin' = origin')
    (_h_I2 : ∀ x : Val D, op origin' x = origin') :
    op origin' origin' = origin' := by
  exact h_I1 origin'

-- ============================================================================
-- Axiom Independence: I1 ⊬ I2 and I2 ⊬ I1
-- ============================================================================

/-- Operation satisfying I1 but not I2. -/
def opSatI1NotI2 {D : Type} (a b : Val D) : Val D :=
  match a, b with
  | _, Val.origin         => origin'
  | Val.origin, Val.contents d => bounded' d
  | Val.origin, Val.container d => Val.container d
  | Val.contents a, _    => bounded' a
  | Val.container a, _   => Val.container a

theorem opI1NotI2_satisfies_I1 {D : Type} (x : Val D) :
    opSatI1NotI2 x (origin' : Val D) = origin' := by
  cases x with | origin => rfl | container _ => rfl | contents _ => rfl

theorem opI1NotI2_violates_I2 {D : Type} (d : D) :
    opSatI1NotI2 (origin' : Val D) (bounded' d) ≠ origin' := by
  simp [opSatI1NotI2, origin', bounded']

/-- Operation satisfying I2 but not I1. -/
def opSatI2NotI1 {D : Type} (a b : Val D) : Val D :=
  match a, b with
  | Val.origin, _              => origin'
  | Val.contents a, Val.origin => bounded' a  -- I1 violation
  | Val.contents a, _          => bounded' a
  | Val.container a, Val.origin => Val.container a  -- I1 violation
  | Val.container a, _         => Val.container a

theorem opI2NotI1_satisfies_I2 {D : Type} (x : Val D) :
    opSatI2NotI1 (origin' : Val D) x = origin' := by
  simp [opSatI2NotI1, origin']

theorem opI2NotI1_violates_I1 {D : Type} (d : D) :
    opSatI2NotI1 (bounded' d) (origin' : Val D) ≠ origin' := by
  simp [opSatI2NotI1, origin', bounded']

-- ============================================================================
-- Origin Propagation at Arbitrary Depth
-- ============================================================================

def iteratedOp {D : Type} [DecidableEq D]
    (f : D → D → D) (base : Val D) (arg : Val D) : Nat → Val D
  | 0     => base
  | n + 1 => Val.mul f (iteratedOp f base arg n) arg

/-- Origin propagates through any depth of iteration. -/
theorem origin_propagates_depth {D : Type} [DecidableEq D]
    (f : D → D → D) (arg : Val D) (n : Nat) :
    iteratedOp f origin' arg n = origin' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [iteratedOp]; rw [ih]; simp [Val.mul]

-- ============================================================================
-- Commutativity of Origin Propagation
-- ============================================================================

/-- Origin propagation is commutative even when the underlying operation is not. -/
theorem origin_propagation_commutative {D : Type} [DecidableEq D]
    (f : D → D → D) (x : Val D) :
    Val.mul f origin' x = Val.mul f x origin' := by
  cases x with
  | origin => rfl
  | container _ => simp [Val.mul]
  | contents _ => simp [Val.mul]

-- ============================================================================
-- Universal Absorber / Fixed Point
-- ============================================================================

/-- Origin absorbs every operation simultaneously. -/
theorem origin_universal_absorber {D : Type} [DecidableEq D] (x : Val D) :
    ∀ f : D → D → D,
      Val.mul f origin' x = origin' ∧ Val.mul f x origin' = origin' := by
  intro f; exact ⟨interaction_I2 f x, interaction_I1 f x⟩

/-- The absorber is unique: if an element absorbs everything, it must be origin. -/
theorem absorber_is_origin {D : Type} [DecidableEq D] [Nonempty D]
    (z : Val D)
    (h : ∀ (f : D → D → D) (y : Val D), Val.mul f z y = origin') :
    z = origin' := by
  cases z with
  | origin => rfl
  | container a =>
    exfalso
    have d := Classical.choice ‹Nonempty D›
    have := h (fun a _ => a) (Val.contents d)
    simp [Val.mul] at this
  | contents a =>
    exfalso
    have d := Classical.choice ‹Nonempty D›
    have := h (fun a _ => a) (Val.contents d)
    simp [Val.mul] at this

-- ============================================================================
-- Sort Membership Decidability
-- ============================================================================

/-- Computable sort classification. Returns 0 for origin, 1 for container, 2 for contents. -/
def classifySort {D : Type} (x : Val D) : Nat :=
  match x with
  | Val.origin => 0
  | Val.container _ => 1
  | Val.contents _ => 2

/-- Every element is in exactly one sort. -/
theorem sort_membership_exclusive {D : Type} (x : Val D) :
    (x = origin' ∧ ¬ ∃ d : D, x = bounded' d) ∨
    (x ≠ origin' ∧ ∃ d : D, x = bounded' d) ∨
    (x ≠ origin' ∧ ∃ a : D, x = Val.container a) := by
  cases x with
  | origin =>
    left; constructor
    · rfl
    · intro ⟨_, h⟩; simp [bounded'] at h
  | container a =>
    right; right; constructor
    · simp [origin']
    · exact ⟨a, rfl⟩
  | contents a =>
    right; left; constructor
    · simp [origin']
    · exact ⟨a, rfl⟩

-- ============================================================================
-- Contents Injectivity
-- ============================================================================

/-- Contents elements are uniquely determined by their value. -/
theorem bounded_determined_by_distinction {D : Type} (d₁ d₂ : D) :
    (bounded' d₁ : Val D) = bounded' d₂ ↔ d₁ = d₂ := by
  constructor
  · intro h; simp [bounded'] at h; exact h
  · intro h; rw [h]

-- ============================================================================
-- Negative Tests
-- ============================================================================

/-- A leaky operation where Origin does NOT absorb. -/
def leakyOp {D : Type} [DecidableEq D] (a b : Val D) : Val D :=
  match a, b with
  | Val.origin, x     => x
  | x, Val.origin     => x
  | Val.contents a, _ => bounded' a
  | Val.container a, _ => Val.container a

/-- The leaky operation violates I2. -/
theorem leaky_violates_I2 {D : Type} [DecidableEq D] (d : D) :
    leakyOp (origin' : Val D) (bounded' d) ≠ origin' := by
  simp [leakyOp, origin', bounded']

/-- A morphism from the leaky domain fails commutativity with arithmetic. -/
theorem leaky_morphism_fails {D : Type} [DecidableEq D]
    (f : D → D → D) (d : D) :
    leakyOp (origin' : Val D) (bounded' d) ≠
    Val.mul f (origin' : Val D) (bounded' d) := by
  simp [leakyOp, Val.mul, bounded']

/-- A map that sends origin to contents fails to preserve the distinction. -/
def badMap {D : Type} (d₀ : D) : Val D → Val D
  | Val.origin => bounded' d₀
  | Val.container a => Val.container a
  | Val.contents a => bounded' a

theorem bad_map_fails_distinction {D : Type} [DecidableEq D] (d₀ : D) :
    ¬ preservesDistinction (badMap d₀ : Val D → Val D) := by
  intro ⟨h, _⟩
  simp [badMap, origin', bounded'] at h

end OriginalArith
